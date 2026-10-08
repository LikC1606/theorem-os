/** Linux-only immutable dependency custodian. Kept as a bundled literal, not an external asset. */
export const MATH_SEALED_ENVIRONMENT_HELPER = String.raw`
import argparse
import ctypes
import hashlib
import json
import os
from pathlib import Path
import select
import secrets
import shutil
import signal
import socket
import stat
import subprocess
import sys
import tempfile
import time


class Cancelled(Exception):
    pass


shutdown_requested = False


def emit(value):
    print(json.dumps(value), flush=True)


def cancelled():
    if shutdown_requested:
        raise Cancelled('custodian terminated')
    if select.select([sys.stdin.buffer], [], [], 0)[0]:
        if not os.read(sys.stdin.fileno(), 4096):
            raise Cancelled('custodian input closed')


def terminate(signum, frame):
    global shutdown_requested
    shutdown_requested = True


def stop(process):
    if process is not None and process.poll() is None:
        process.terminate()
        try:
            process.wait(timeout=3)
        except subprocess.TimeoutExpired:
            process.kill()
            process.wait()


def require_disk(directory, size):
    capacity = os.statvfs(directory)
    if size + 64 * 1024 * 1024 > capacity.f_bavail * capacity.f_frsize:
        raise RuntimeError('insufficient available disk for dependency image')


def main():
    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--source')
    group.add_argument('--image')
    parser.add_argument('--export-image')
    parser.add_argument('--expected-image-sha256')
    args = parser.parse_args()
    workspace = None
    mountpoint = None
    image_fd = None
    root_fd = None
    compressor = None
    server = None
    listener = None
    clients = {}
    mounted = False
    try:
        if sys.platform != 'linux':
            raise RuntimeError('dependency environment requires Linux')
        # Record the host setting. Scope 0 permits same-UID debugging; only scopes
        # >= 1 protect this custodian and its FUSE server from sibling injection.
        ptrace_scope = int(Path('/proc/sys/kernel/yama/ptrace_scope').read_text().strip())
        libc = ctypes.CDLL(None, use_errno=True)
        # Explicitly revoke an inherited PR_SET_PTRACER exception, if any.
        if libc.prctl(0x59616d61, 0, 0, 0, 0) != 0:
            raise OSError(ctypes.get_errno(), 'could not revoke ptrace exception')
        snapfuse = shutil.which('snapfuse') or shutil.which('squashfuse')
        unmount = shutil.which('fusermount3') or shutil.which('fusermount')
        compressor_bin = shutil.which('mksquashfs')
        if not snapfuse or not unmount or (args.source and not compressor_bin):
            raise RuntimeError('sealed dependency environment requires squashfuse, fusermount, and mksquashfs')
        signal.signal(signal.SIGTERM, terminate)
        signal.signal(signal.SIGINT, terminate)
        cancelled()
        workspace = Path(tempfile.mkdtemp(prefix='math-sealed-environment-', dir='/var/tmp'))
        mountpoint = workspace / 'mount'
        mountpoint.mkdir()
        image_path = workspace / 'dependencies.squashfs'
        with tempfile.TemporaryFile(dir=workspace) as diagnostics:
            if args.source:
                source = Path(args.source)
                if not source.is_dir() or source.is_symlink():
                    raise RuntimeError('sealed source must be a materialized directory')
                total_bytes = 0
                for directory, _, files in os.walk(source):
                    cancelled()
                    for filename in files:
                        metadata = os.lstat(os.path.join(directory, filename))
                        if stat.S_ISREG(metadata.st_mode):
                            total_bytes += metadata.st_size
                require_disk(workspace, total_bytes)
                compressor = subprocess.Popen(
                    [compressor_bin, str(source), str(image_path),
                     '-noappend', '-quiet', '-no-progress', '-processors', '2',
                     '-mem', '128M', '-noD', '-noF', '-noI'],
                    stdin=subprocess.DEVNULL,
                    stdout=subprocess.DEVNULL, stderr=diagnostics)
                while compressor.poll() is None:
                    cancelled()
                    time.sleep(0.05)
                if compressor.returncode != 0:
                    diagnostics.seek(0)
                    raise RuntimeError('mksquashfs failed: ' + diagnostics.read(8192).decode(errors='replace'))
            else:
                input_fd = os.open(args.image, os.O_RDONLY | os.O_NOFOLLOW)
                try:
                    if not stat.S_ISREG(os.fstat(input_fd).st_mode):
                        raise RuntimeError('squashfs image must be a regular file')
                    require_disk(workspace, os.fstat(input_fd).st_size)
                    with image_path.open('xb') as output:
                        while True:
                            cancelled()
                            chunk = os.read(input_fd, 1024 * 1024)
                            if not chunk:
                                break
                            output.write(chunk)
                finally:
                    os.close(input_fd)
            # Keep the image on disk through a read-only descriptor, without a
            # writable pathname. The image is reclaimed when its last FD closes.
            image_path.chmod(0o400)
            image_fd = os.open(image_path, os.O_RDONLY | os.O_NOFOLLOW)
            image_path.unlink()
            seals = 0
            digest = hashlib.sha256()
            os.lseek(image_fd, 0, os.SEEK_SET)
            while True:
                cancelled()
                chunk = os.read(image_fd, 1024 * 1024)
                if not chunk:
                    break
                digest.update(chunk)
            if os.pread(image_fd, 4, 0) != b'hsqs':
                raise RuntimeError('image is not squashfs')
            if args.expected_image_sha256 and digest.hexdigest() != args.expected_image_sha256:
                raise RuntimeError('cached image digest changed')
            if args.export_image:
                # Publish an independent disk copy; never expose a writable alias
                # to the image backing an active immutable mount.
                os.lseek(image_fd, 0, os.SEEK_SET)
                output_fd = os.open(args.export_image, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600)
                with os.fdopen(output_fd, 'wb') as output:
                    while True:
                        cancelled()
                        chunk = os.read(image_fd, 1024 * 1024)
                        if not chunk:
                            break
                        output.write(chunk)
                    output.flush()
                    os.fsync(output.fileno())
                    os.fchmod(output.fileno(), 0o400)
            server = subprocess.Popen(
                [snapfuse, '-f', '-o', 'ro', '/proc/self/fd/' + str(image_fd), str(mountpoint)],
                pass_fds=[image_fd], stdin=subprocess.DEVNULL,
                stdout=subprocess.DEVNULL, stderr=diagnostics)
            while not os.path.ismount(mountpoint):
                cancelled()
                if server.poll() is not None:
                    diagnostics.seek(0)
                    raise RuntimeError('squashfuse failed: ' + diagnostics.read(8192).decode(errors='replace'))
                time.sleep(0.025)
            mounted = True
            root_fd = os.open(mountpoint, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
            root_stat = os.fstat(root_fd)
            # Keep the mount attached so sandbox backends can bind the pinned FD.
            # Only the FD is published as authority: mountpoint replacement never
            # redirects it. Detachment may block a new bind, which fails closed.
            cancelled()
            lease_socket = str(workspace / 'lease.sock')
            lease_token = secrets.token_hex(32)
            listener = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
            listener.bind(lease_socket)
            listener.listen(64)
            listener.setblocking(False)
            emit({'state': 'ready', 'pid': os.getpid(), 'rootFd': root_fd,
                  'rootPath': '/proc/' + str(os.getpid()) + '/fd/' + str(root_fd),
                  'device': root_stat.st_dev, 'inode': root_stat.st_ino,
                  'imageFd': image_fd, 'imageBytes': os.fstat(image_fd).st_size,
                  'imageSha256': digest.hexdigest(), 'seals': seals,
                  'serverPid': server.pid, 'ptraceScope': ptrace_scope,
                  'leaseSocket': lease_socket, 'leaseToken': lease_token})
            owner_released = False
            lease_count = 0
            maximum_leases = 0
            lease_starts = 0
            lease_ends = 0
            overlap_started = None
            overlap_seconds = 0.0
            while server.poll() is None:
                readers = list(clients)
                if not owner_released:
                    readers.extend([sys.stdin.buffer, listener])
                readable = select.select(readers, [], [], 0.1)[0]
                if not owner_released and (shutdown_requested or
                        (sys.stdin.buffer in readable and not os.read(sys.stdin.fileno(), 4096))):
                    owner_released = True
                    listener.close()
                    listener = None
                if listener is not None and listener in readable:
                    client, _ = listener.accept()
                    client.setblocking(False)
                    clients[client] = {'active': False, 'data': b'', 'started': time.monotonic()}
                for client, state in list(clients.items()):
                    close = owner_released and not state['active']
                    if client in readable:
                        try:
                            data = client.recv(4096)
                            if not data:
                                close = True
                            elif not state['active']:
                                state['data'] += data
                                if len(state['data']) > 4096:
                                    close = True
                                elif b'\n' in state['data']:
                                    message = json.loads(state['data'].split(b'\n', 1)[0])
                                    if message.get('token') == lease_token and not owner_released:
                                        if message.get('action') == 'status':
                                            elapsed_overlap = overlap_seconds
                                            if overlap_started is not None:
                                                elapsed_overlap += time.monotonic() - overlap_started
                                            client.sendall((json.dumps({
                                                'ok': True, 'publications': 1,
                                                'activeLeaseCount': lease_count,
                                                'maxLeaseCount': maximum_leases,
                                                'leaseStarts': lease_starts, 'leaseEnds': lease_ends,
                                                'overlapMilliseconds': elapsed_overlap * 1000,
                                                'ownerReleased': owner_released,
                                                'seals': seals,
                                                'imageBytes': os.fstat(image_fd).st_size,
                                                'serverPid': server.pid,
                                            }) + '\n').encode())
                                            close = True
                                        elif message.get('action') in (None, 'acquire'):
                                            client.sendall(b'{"ok":true}\n')
                                            state['active'] = True
                                            lease_count += 1
                                            lease_starts += 1
                                            maximum_leases = max(maximum_leases, lease_count)
                                            if lease_count == 2:
                                                overlap_started = time.monotonic()
                                        else:
                                            close = True
                                    else:
                                        close = True
                        except (OSError, ValueError, AttributeError):
                            close = True
                    if not state['active'] and time.monotonic() - state['started'] > 5:
                        close = True
                    if close:
                        if state['active']:
                            if lease_count == 2 and overlap_started is not None:
                                overlap_seconds += time.monotonic() - overlap_started
                                overlap_started = None
                            lease_count -= 1
                            lease_ends += 1
                        client.close()
                        del clients[client]
                if owner_released and not clients:
                    return 0
            raise RuntimeError('immutable filesystem server exited while its lease was active')
    except Cancelled:
        return 0
    except Exception as error:
        emit({'state': 'blocked', 'error': str(error)})
        return 1
    finally:
        # Ignore repeated cancellation while reclaiming resources owned here.
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        signal.signal(signal.SIGINT, signal.SIG_IGN)
        stop(compressor)
        for client in clients:
            client.close()
        if listener is not None:
            listener.close()
        if root_fd is not None:
            os.close(root_fd)
        if mounted and mountpoint is not None:
            subprocess.run([unmount, '-uz', str(mountpoint)],
                           stdin=subprocess.DEVNULL, capture_output=True)
        stop(server)
        if image_fd is not None:
            os.close(image_fd)
        if workspace is not None:
            shutil.rmtree(workspace, ignore_errors=True)


sys.exit(main())
`;
