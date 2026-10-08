// Linux-only helper. Python is launched with isolated imports (-I).
export const LEAN_SHARED_ENVIRONMENT_NATIVE = String.raw`import ctypes
import errno
import fcntl
import hashlib
import json
import os
import re
import selectors
import signal
import stat
import struct
import sys
import time

# This process never execs after acquiring its FUSE or namespace authority.
LIBC = ctypes.CDLL(None, use_errno=True)
SENTINEL = '__DEEPSCIENTIST_SHARED_PACKAGES__'
BROKER_ROOT = '/mnt'
LEASE_ROOT = '/run/lean-shared'
MAX_FRAME = 64 * 1024 * 1024
MAX_CAPTURE = 1024 * 1024
MAX_STDIN = 4 * 1024 * 1024
MAX_RUN_MS = 15 * 60 * 1000
MS_BIND = 4096
MS_PRIVATE = 1 << 18
MS_REC = 16384
CLONE_NEWUSER = 0x10000000
CLONE_NEWNS = 0x20000
SEALS = fcntl.F_SEAL_WRITE | fcntl.F_SEAL_GROW | fcntl.F_SEAL_SHRINK | fcntl.F_SEAL_SEAL
CLOSING = False
PREPARATION_PHASE = 'capability'


def checked(result):
    if result < 0:
        code = ctypes.get_errno()
        raise OSError(code, os.strerror(code))
    return result


def mount(source, target, kind=None, flags=0, options=None):
    checked(LIBC.mount(os.fsencode(source) if source else None, os.fsencode(target),
                       os.fsencode(kind) if kind else None, ctypes.c_ulong(flags),
                       os.fsencode(options) if options else None))


def protect():
    checked(LIBC.prctl(4, 0, 0, 0, 0))
    if LIBC.prctl(3, 0, 0, 0, 0) != 0:
        raise RuntimeError('Unable to protect helper process')


def parent_death(parent):
    checked(LIBC.prctl(1, signal.SIGKILL, 0, 0, 0))
    if os.getppid() != parent:
        os._exit(125)


def emit(value):
    data = (json.dumps(value, separators=(',', ':'), ensure_ascii=True) + '\n').encode()
    while data:
        written = os.write(1, data)
        data = data[written:]


def integer(value, minimum, maximum, label):
    if isinstance(value, bool) or not isinstance(value, int) or not minimum <= value <= maximum:
        raise ValueError('Invalid ' + label)
    return value


def stable_root(path):
    info = os.lstat(path)
    if not stat.S_ISDIR(info.st_mode) or info.st_uid != 0 or info.st_mode & 0o022:
        raise RuntimeError('Shared helper requires a root-owned, non-writable ' + path)


def setup_namespace():
    stable_root('/')
    stable_root(BROKER_ROOT)
    stable_root('/run')
    uid, gid = os.getuid(), os.getgid()
    if uid == 0:
        raise RuntimeError('Shared dependency helper requires an unprivileged host user')
    checked(LIBC.unshare(CLONE_NEWUSER))
    with open('/proc/self/setgroups', 'w') as stream:
        stream.write('deny')
    with open('/proc/self/uid_map', 'w') as stream:
        stream.write('0 %d 1' % uid)
    with open('/proc/self/gid_map', 'w') as stream:
        stream.write('0 %d 1' % gid)
    protect()
    checked(LIBC.unshare(CLONE_NEWNS))
    mount(None, '/', flags=MS_PRIVATE | MS_REC)


def safe_relative(value):
    if not isinstance(value, str) or not value or len(value.encode('utf-8')) > 4096 or '\x00' in value or '\\' in value:
        raise ValueError('Unsafe manifest relative path')
    parts = value.split('/')
    if any(not part or part in ('.', '..', '.git', 'Solution.lean') or len(part.encode('utf-8')) > 255 for part in parts):
        raise ValueError('Unsafe manifest relative path')
    return parts


def capture_manifest(request):
    if not isinstance(request, dict) or request.get('op') != 'prepare':
        raise ValueError('First request must prepare a shared environment')
    entries = request.get('files')
    if not isinstance(entries, list) or not entries or len(entries) > 500000:
        raise ValueError('Invalid manifest file count')
    max_bytes = integer(request.get('maxBytes'), 1, 128 * 1024 ** 3, 'maxBytes')
    timeout = integer(request.get('timeoutMs'), 1, 30 * 60 * 1000, 'prepare timeout')
    deadline = time.monotonic() + timeout / 1000
    pack = os.memfd_create('deepscientist-lean-dependencies', os.MFD_CLOEXEC | os.MFD_ALLOW_SEALING)
    nodes = {1: {'mode': stat.S_IFDIR | 0o555, 'size': 0, 'offset': 0, 'mtime': 0, 'children': {}, 'parent': 1}}
    paths = {'': 1}
    records = []
    total = 0

    def ensure_directory(parts):
        parent = 1
        for index, part in enumerate(parts):
            relative = '/'.join(parts[:index + 1])
            existing = paths.get(relative)
            if existing is not None:
                if not stat.S_ISDIR(nodes[existing]['mode']):
                    raise ValueError('Manifest file and directory conflict')
                parent = existing
                continue
            inode = len(nodes) + 1
            nodes[inode] = {'mode': stat.S_IFDIR | 0o555, 'size': 0, 'offset': 0, 'mtime': 0, 'children': {}, 'parent': parent}
            nodes[parent]['children'][part.encode('utf-8')] = inode
            paths[relative] = inode
            parent = inode
        return parent

    try:
        for entry in entries:
            if time.monotonic() >= deadline:
                raise TimeoutError('Shared environment preparation timed out')
            if not isinstance(entry, dict):
                raise ValueError('Invalid manifest entry')
            relative = entry.get('relative')
            parts = safe_relative(relative)
            if relative in paths:
                raise ValueError('Duplicate or conflicting manifest path')
            source = entry.get('source')
            digest = entry.get('digest')
            size = integer(entry.get('bytes'), 0, max_bytes, 'file size')
            mode = integer(entry.get('mode'), 0, 0xffffffff, 'file mode')
            if not isinstance(source, str) or not os.path.isabs(source) or '\x00' in source:
                raise ValueError('Invalid manifest source')
            if not isinstance(digest, str) or re.fullmatch('[0-9a-f]{64}', digest) is None:
                raise ValueError('Invalid manifest digest')
            if total + size > max_bytes:
                raise ValueError('Shared dependency byte limit exceeded')
            parent = ensure_directory(parts[:-1])
            descriptor = os.open(source, os.O_RDONLY | os.O_NOFOLLOW | os.O_CLOEXEC | os.O_NONBLOCK)
            try:
                before = os.fstat(descriptor)
                if not stat.S_ISREG(before.st_mode) or before.st_size != size:
                    raise ValueError('Manifest source type or size changed')
                hashed = hashlib.sha256()
                remaining = size
                while remaining:
                    if time.monotonic() >= deadline:
                        raise TimeoutError('Shared environment preparation timed out')
                    chunk = os.read(descriptor, min(1024 * 1024, remaining))
                    if not chunk:
                        raise ValueError('Manifest source was truncated')
                    hashed.update(chunk)
                    data = memoryview(chunk)
                    while data:
                        written = os.write(pack, data)
                        data = data[written:]
                    remaining -= len(chunk)
                after = os.fstat(descriptor)
                if os.read(descriptor, 1) or (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns, before.st_ctime_ns) != (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns, after.st_ctime_ns):
                    raise ValueError('Manifest source changed during capture')
                if hashed.hexdigest() != digest:
                    raise ValueError('Manifest source digest changed')
            finally:
                os.close(descriptor)
            inode = len(nodes) + 1
            nodes[inode] = {'mode': stat.S_IFREG | (0o555 if mode & 0o111 else 0o444), 'size': size, 'offset': total, 'mtime': before.st_mtime_ns, 'parent': parent}
            nodes[parent]['children'][parts[-1].encode('utf-8')] = inode
            paths[relative] = inode
            records.append((total, size, digest))
            total += size
        fcntl.fcntl(pack, fcntl.F_ADD_SEALS, SEALS)
        if fcntl.fcntl(pack, fcntl.F_GET_SEALS) & SEALS != SEALS:
            raise RuntimeError('Shared dependency memfd is not sealed')
        for offset, size, digest in records:
            hashed = hashlib.sha256()
            remaining = size
            while remaining:
                if time.monotonic() >= deadline:
                    raise TimeoutError('Sealed dependency verification timed out')
                chunk = os.pread(pack, min(1024 * 1024, remaining), offset)
                if not chunk:
                    raise ValueError('Sealed dependency data is truncated')
                hashed.update(chunk)
                offset += len(chunk)
                remaining -= len(chunk)
            if hashed.hexdigest() != digest:
                raise ValueError('Sealed dependency digest mismatch')
        for node in nodes.values():
            if 'children' in node:
                node['listing'] = [(b'.', paths.get('', 1), 4), (b'..', node['parent'], 4)]
        for inode, node in nodes.items():
            if 'children' in node:
                node['listing'][0] = (b'.', inode, 4)
                node['listing'].extend((name, child, 4 if stat.S_ISDIR(nodes[child]['mode']) else 8) for name, child in sorted(node['children'].items()))
        return pack, nodes, len(entries), total
    except BaseException:
        os.close(pack)
        raise


def fuse_loop(descriptor, pack, nodes, total):
    def attr(inode):
        node = nodes[inode]
        seconds, nanos = divmod(node['mtime'], 1000000000)
        return struct.pack('=6Q10I', inode, node['size'], (node['size'] + 511) // 512,
                           seconds, seconds, seconds, nanos, nanos, nanos, node['mode'],
                           2 if 'children' in node else 1, 0, 0, 0, 4096, 0)

    def reply(unique, data=b'', error=0):
        packet = struct.pack('=IiQ', 16 + len(data), -error, unique) + data
        if os.write(descriptor, packet) != len(packet):
            raise RuntimeError('Short FUSE response')

    while True:
        try:
            packet = os.read(descriptor, 1024 * 1024)
        except OSError as error:
            if error.errno == errno.EINTR:
                continue
            return
        if len(packet) < 40:
            return
        length, opcode, unique, inode, uid, gid, pid, padding = struct.unpack_from('=IIQQIIII', packet)
        if length != len(packet):
            return
        body = packet[40:]
        try:
            if opcode == 26:
                major, minor, readahead, flags = struct.unpack_from('=IIII', body)
                if major != 7 or minor < 23:
                    return
                reply(unique, struct.pack('=IIIIHHIIHHI7I', 7, min(minor, 31), readahead,
                                          flags & (1 | 32), 16, 12, 131072, 1, 32, 0, 0, *([0] * 7)))
            elif opcode in (2, 42):
                continue
            elif opcode == 38:
                return
            elif opcode == 1:
                node = nodes.get(inode)
                child = node.get('children', {}).get(body.rstrip(b'\0')) if node else None
                if child is None:
                    reply(unique, error=errno.ENOENT)
                else:
                    reply(unique, struct.pack('=QQQQII', child, 1, 3600, 3600, 0, 0) + attr(child))
            elif inode not in nodes:
                reply(unique, error=errno.ENOENT)
            elif opcode == 3:
                reply(unique, struct.pack('=QII', 3600, 0, 0) + attr(inode))
            elif opcode in (14, 27):
                flags = struct.unpack_from('=I', body)[0]
                directory = 'children' in nodes[inode]
                if opcode == 14 and directory:
                    reply(unique, error=errno.EISDIR)
                elif opcode == 27 and not directory:
                    reply(unique, error=errno.ENOTDIR)
                elif flags & (os.O_WRONLY | os.O_RDWR | os.O_TRUNC | os.O_APPEND):
                    reply(unique, error=errno.EROFS)
                else:
                    reply(unique, struct.pack('=QII', inode, 0, 0))
            elif opcode == 15:
                handle, offset, size = struct.unpack_from('=QQI', body)
                node = nodes[inode]
                if 'children' in node or handle != inode:
                    reply(unique, error=errno.EBADF)
                else:
                    reply(unique, os.pread(pack, min(size, 131072, max(0, node['size'] - offset)), node['offset'] + min(offset, node['size'])))
            elif opcode == 28:
                handle, offset, size = struct.unpack_from('=QQI', body)
                node = nodes[inode]
                if 'children' not in node or handle != inode:
                    reply(unique, error=errno.ENOTDIR)
                    continue
                output = bytearray()
                for index in range(min(offset, len(node['listing'])), len(node['listing'])):
                    name, child, kind = node['listing'][index]
                    entry = struct.pack('=QQII', child, index + 1, len(name), kind) + name
                    entry += b'\0' * (-len(entry) % 8)
                    if len(output) + len(entry) > size:
                        break
                    output.extend(entry)
                reply(unique, output)
            elif opcode == 17:
                reply(unique, struct.pack('=5Q10I', (total + 4095) // 4096, 0, 0, len(nodes), 0, 4096, 255, 4096, 0, *([0] * 6)))
            elif opcode in (18, 20, 25, 29, 30):
                reply(unique)
            elif opcode == 34:
                mask = struct.unpack_from('=I', body)[0]
                reply(unique, error=errno.EROFS if mask & os.W_OK else errno.EACCES if mask & os.X_OK and not nodes[inode]['mode'] & 0o111 else 0)
            elif opcode == 22:
                reply(unique, error=errno.ENODATA)
            elif opcode == 23:
                reply(unique, struct.pack('=II', 0, 0) if struct.unpack_from('=I', body)[0] == 0 else b'')
            elif opcode in (4, 6, 8, 9, 10, 11, 12, 13, 16, 21, 24, 35, 43, 45, 47, 51):
                reply(unique, error=errno.EROFS)
            else:
                reply(unique, error=errno.ENOSYS)
        except (KeyError, ValueError, OverflowError, struct.error):
            reply(unique, error=errno.EIO)


def start_fuse(pack, nodes, total):
    mount('tmpfs', BROKER_ROOT, 'tmpfs', 2 | 4, 'size=1m,mode=0700')
    os.mkdir(BROKER_ROOT + '/base', 0o700)
    descriptor = os.open('/dev/fuse', os.O_RDWR | os.O_CLOEXEC)
    try:
        mount('deepscientist-sealed-dependencies', BROKER_ROOT + '/base', 'fuse', 1 | 2 | 4,
              'fd=%d,rootmode=40000,user_id=0,group_id=0,max_read=131072,default_permissions' % descriptor)
        parent = os.getpid()
        worker = os.fork()
        if worker == 0:
            try:
                parent_death(parent)
                protect()
                for stream in (0, 1, 2):
                    try:
                        os.close(stream)
                    except OSError:
                        pass
                fuse_loop(descriptor, pack, nodes, total)
            finally:
                os._exit(0)
        os.close(descriptor)
        # Require a live daemon and a completed FUSE_INIT before advertising ready.
        if not stat.S_ISDIR(os.stat(BROKER_ROOT + '/base').st_mode):
            raise RuntimeError('Shared dependency mount is unavailable')
        return worker
    except BaseException:
        try:
            os.close(descriptor)
        except OSError:
            pass
        raise


def empty_result(code, message):
    digest = hashlib.sha256(b'').hexdigest()
    return {'started': False, 'exitCode': None, 'signal': None, 'stdout': '', 'stderr': '',
            'stdoutSha256': digest, 'stderrSha256': digest, 'timedOut': False, 'aborted': False,
            'durationMs': 0, 'errorCode': code, 'errorMessage': message}


def validate_run(request):
    identifier = request.get('id')
    if not isinstance(identifier, str) or not identifier or len(identifier) > 200:
        raise ValueError('Invalid run id')
    argv = request.get('argv')
    if not isinstance(argv, list) or not argv or len(argv) > 10000 or any(not isinstance(arg, str) or '\x00' in arg for arg in argv):
        raise ValueError('Invalid sandbox arguments')
    if argv[0] != '/usr/bin/bwrap' or SENTINEL not in argv:
        raise ValueError('Shared commands require /usr/bin/bwrap and the package sentinel')
    binary = os.stat(argv[0])
    if not stat.S_ISREG(binary.st_mode) or binary.st_uid != 65534 or binary.st_mode & 0o022:
        # Host root maps to the overflow uid in this single-user namespace.
        raise ValueError('Sandbox executable must be owned by host root')
    for required in ('--unshare-user', '--unshare-net', '--unshare-pid', '--die-with-parent'):
        if required not in argv:
            raise ValueError('Sandbox namespace protections are missing')
    cwd = request.get('cwd')
    if not isinstance(cwd, str) or not os.path.isabs(cwd) or '\x00' in cwd:
        raise ValueError('Invalid sandbox working directory')
    timeout = integer(request.get('timeoutMs'), 1, MAX_RUN_MS, 'run timeout')
    environment = request.get('env')
    if not isinstance(environment, dict) or len(environment) > 1000 or any(not isinstance(key, str) or not isinstance(value, str) or not key or '=' in key or '\x00' in key or '\x00' in value for key, value in environment.items()):
        raise ValueError('Invalid sandbox environment')
    environment = {key: value for key, value in environment.items() if not key.startswith(('LD_', 'PYTHON')) and key not in ('BASH_ENV', 'ENV')}
    stdin = request.get('stdin', '')
    if not isinstance(stdin, str) or len(stdin.encode('utf-8')) > MAX_STDIN:
        raise ValueError('Invalid sandbox input')
    if request.get('outputCapture', 'tail') not in ('head', 'tail'):
        raise ValueError('Invalid output capture mode')
    return identifier, argv, cwd, environment, timeout, stdin.encode('utf-8')


def verify_generated_outputs():
    # Source/configuration changes in a lease must never become accepted observations.
    # Lake owns only these generated paths in the existing private snapshot contract.
    upper = LEASE_ROOT + '/upper'

    def verify_ancestor_metadata(absolute, relative):
        # A remove/recreate operation can hide a complete lower directory with
        # an opaque upper ancestor, without leaving any forbidden child entry.
        # Redirect/metacopy markers can also change which lower bytes are read.
        # Inspect the private upper tree, where overlay control xattrs remain
        # visible. Only identity/readdir bookkeeping is harmless: opaque=x
        # requests whiteout scanning; opaque=y hides the lower directory.
        markers = [name for name in os.listxattr(absolute, follow_symlinks=False)
                   if name.startswith(('trusted.overlay.', 'user.overlay.'))]
        for name in markers:
            value = os.getxattr(absolute, name, follow_symlinks=False)
            marker = name.split('.', 2)[2]
            if ((marker == 'uuid' and len(value) == 16) or
                    (marker == 'impure' and value == b'y') or
                    (marker == 'opaque' and value == b'x') or
                    # ovl_get_fh treats only an empty origin as unknown; it
                    # carries no file handle capable of selecting lower data.
                    (marker == 'origin' and value == b'')):
                continue
            raise ValueError('Shared Lean lease modified protected dependency metadata: ' + relative + ' (' + name + ')')

    verify_ancestor_metadata(upper, '.')
    for directory, directories, files in os.walk(upper, followlinks=False):
        for name in directories + files:
            absolute = directory + '/' + name
            relative = os.path.relpath(absolute, upper)
            parts = relative.split('/')
            generated = len(parts) >= 3 and parts[1] == '.lake' and (
                parts[2] == 'build' or (len(parts) == 3 and re.fullmatch(r'lakefile\.[^/]+', parts[2])))
            info = os.lstat(absolute)
            ancestor = stat.S_ISDIR(info.st_mode) and (len(parts) == 1 or (len(parts) == 2 and parts[1] == '.lake'))
            if ancestor:
                verify_ancestor_metadata(absolute, relative)
            if not generated and not ancestor:
                raise ValueError('Shared Lean lease modified a protected dependency: ' + relative)


def run_child(argv, cwd, environment, parent, input_fd, stdout_fd, stderr_fd, error_fd):
    try:
        os.setsid()
        parent_death(parent)
        protect()
        checked(LIBC.prctl(38, 1, 0, 0, 0))
        checked(LIBC.unshare(CLONE_NEWNS))
        mount(None, '/', flags=MS_PRIVATE | MS_REC)
        mount('tmpfs', '/run', 'tmpfs', 2 | 4, 'size=512m,nr_inodes=262144,mode=0700')
        os.mkdir(LEASE_ROOT, 0o700)
        for name in ('lower', 'upper', 'work', 'merged'):
            os.mkdir(LEASE_ROOT + '/' + name, 0o700)
        mount(BROKER_ROOT + '/base', LEASE_ROOT + '/lower', flags=MS_BIND)
        # No broker tmpfs path survives into the execed child's namespace.
        mount('tmpfs', BROKER_ROOT, 'tmpfs', 2 | 4, 'size=1m,mode=0700')
        mount('overlay', LEASE_ROOT + '/merged', 'overlay', 2 | 4,
              'lowerdir=%s/lower,upperdir=%s/upper,workdir=%s/work' % (LEASE_ROOT, LEASE_ROOT, LEASE_ROOT))
        arguments = [LEASE_ROOT + '/merged' if arg == SENTINEL else arg for arg in argv]
        os.chdir(cwd)
        os.dup2(input_fd, 0)
        os.dup2(stdout_fd, 1)
        os.dup2(stderr_fd, 2)
        # Retain a protected supervisor in this lease namespace to validate the
        # overlay after the sandbox exits, before releasing any successful result.
        supervisor = os.getpid()
        sandbox = os.fork()
        if sandbox == 0:
            parent_death(supervisor)
            # All inherited pack/control/other lease descriptors are close-on-exec.
            os.execve(arguments[0], arguments, environment)
        _, status = os.waitpid(sandbox, 0)
        verify_generated_outputs()
        if os.WIFEXITED(status):
            os._exit(os.WEXITSTATUS(status))
        termination = os.WTERMSIG(status)
        if termination not in (signal.SIGKILL, signal.SIGSTOP):
            signal.signal(termination, signal.SIG_DFL)
        os.kill(os.getpid(), termination)
        os._exit(128 + termination)
    except BaseException as error:
        try:
            os.write(error_fd, str(error).encode('utf-8', 'replace')[:8192])
        finally:
            os._exit(125)


def stop_lease(lease, reason):
    if lease.get('stopped'):
        return
    lease['stopped'] = time.monotonic()
    if reason == 'timeout':
        lease['timedOut'] = True
    elif reason in ('cancel', 'close'):
        lease['aborted'] = True
    else:
        lease['errorCode'] = 'SHARED_ENVIRONMENT_UNAVAILABLE'
        lease['errorMessage'] = reason
    try:
        os.killpg(lease['pid'], signal.SIGKILL)
    except ProcessLookupError:
        try:
            os.kill(lease['pid'], signal.SIGKILL)
        except ProcessLookupError:
            pass


def broker_loop(worker, initial_buffer):
    selector = selectors.DefaultSelector()
    os.set_blocking(0, False)
    selector.register(0, selectors.EVENT_READ, ('control', None))
    leases = {}
    active_ids = set()
    completed_ids = set()
    buffer = initial_buffer
    closing = False
    worker_alive = True

    def unregister(descriptor):
        try:
            selector.unregister(descriptor)
        except KeyError:
            pass
        try:
            os.close(descriptor)
        except OSError:
            pass

    def start(request):
        identifier = request.get('id')
        try:
            identifier, argv, cwd, environment, timeout, stdin = validate_run(request)
            if identifier in active_ids or identifier in completed_ids:
                raise ValueError('Run id was already used')
            if len(leases) >= 4:
                emit({'id': identifier, 'result': empty_result('SHARED_CAPACITY', 'At most four shared leases may run concurrently')})
                return
            input_fd = os.memfd_create('deepscientist-lean-stdin', os.MFD_CLOEXEC)
            pending_input = memoryview(stdin)
            while pending_input:
                pending_input = pending_input[os.write(input_fd, pending_input):]
            os.lseek(input_fd, 0, os.SEEK_SET)
            stdout_read, stdout_write = os.pipe2(os.O_CLOEXEC)
            stderr_read, stderr_write = os.pipe2(os.O_CLOEXEC)
            error_read, error_write = os.pipe2(os.O_CLOEXEC)
            parent = os.getpid()
            started = time.monotonic()
            pid = os.fork()
            if pid == 0:
                run_child(argv, cwd, environment, parent, input_fd, stdout_write, stderr_write, error_write)
                os._exit(125)
            for descriptor in (input_fd, stdout_write, stderr_write, error_write):
                os.close(descriptor)
            lease = {'id': identifier, 'pid': pid, 'startedAt': started, 'deadline': started + timeout / 1000,
                     'capture': request.get('outputCapture', 'tail'), 'stdout': bytearray(), 'stderr': bytearray(),
                     'stdoutHash': hashlib.sha256(), 'stderrHash': hashlib.sha256(), 'error': bytearray(),
                     'fds': {stdout_read, stderr_read, error_read}, 'status': None, 'timedOut': False, 'aborted': False}
            leases[pid] = lease
            active_ids.add(identifier)
            for descriptor, channel in ((stdout_read, 'stdout'), (stderr_read, 'stderr'), (error_read, 'error')):
                os.set_blocking(descriptor, False)
                selector.register(descriptor, selectors.EVENT_READ, (channel, pid))
        except BaseException as error:
            emit({'id': identifier, 'result': empty_result('SHARED_RUN_REJECTED', str(error))})

    try:
        while True:
            if CLOSING:
                closing = True
            if worker_alive:
                finished, status = os.waitpid(worker, os.WNOHANG)
                if finished:
                    worker_alive = False
                    closing = True
                    for lease in leases.values():
                        stop_lease(lease, 'Shared dependency filesystem worker exited')
            while b'\n' in buffer and not closing:
                line, buffer = buffer.split(b'\n', 1)
                try:
                    request = json.loads(line)
                    if not isinstance(request, dict):
                        raise ValueError('Expected protocol object')
                    operation = request.get('op')
                    if operation == 'run':
                        start(request)
                    elif operation == 'cancel':
                        for lease in leases.values():
                            if lease['id'] == request.get('id'):
                                stop_lease(lease, 'cancel')
                    elif operation == 'close':
                        closing = True
                    else:
                        raise ValueError('Unknown shared helper operation')
                except (ValueError, TypeError, UnicodeError) as error:
                    emit({'errorCode': 'SHARED_PROTOCOL_ERROR', 'errorMessage': str(error)})
                    closing = True
            if closing:
                for lease in leases.values():
                    stop_lease(lease, 'close')
                if not leases:
                    break
            for lease in list(leases.values()):
                if lease['status'] is None:
                    finished, status = os.waitpid(lease['pid'], os.WNOHANG)
                    if finished:
                        lease['status'] = status
                if time.monotonic() >= lease['deadline'] and lease['status'] is None:
                    stop_lease(lease, 'timeout')
                if lease.get('stopped') and time.monotonic() - lease['stopped'] > 2:
                    for descriptor in list(lease['fds']):
                        unregister(descriptor)
                        lease['fds'].remove(descriptor)
                if lease['status'] is not None and not lease['fds']:
                    status = lease['status']
                    result = {'started': not bool(lease['error']),
                              'exitCode': os.WEXITSTATUS(status) if os.WIFEXITED(status) else None,
                              'signal': signal.Signals(os.WTERMSIG(status)).name if os.WIFSIGNALED(status) else None,
                              'stdout': lease['stdout'].decode('utf-8', 'replace'), 'stderr': lease['stderr'].decode('utf-8', 'replace'),
                              'stdoutSha256': lease['stdoutHash'].hexdigest(), 'stderrSha256': lease['stderrHash'].hexdigest(),
                              'timedOut': lease['timedOut'], 'aborted': lease['aborted'],
                              'durationMs': round((time.monotonic() - lease['startedAt']) * 1000)}
                    if lease['error']:
                        result['errorCode'] = 'SHARED_RUN_SETUP_FAILED'
                        result['errorMessage'] = lease['error'].decode('utf-8', 'replace')
                    if 'errorCode' in lease:
                        result['errorCode'] = lease['errorCode']
                        result['errorMessage'] = lease['errorMessage']
                        result['exitCode'] = None
                    emit({'id': lease['id'], 'result': result})
                    active_ids.remove(lease['id'])
                    completed_ids.add(lease['id'])
                    del leases[lease['pid']]
            for key, mask in selector.select(0.05):
                channel, pid = key.data
                try:
                    chunk = os.read(key.fd, 65536)
                except BlockingIOError:
                    continue
                if channel == 'control':
                    if not chunk:
                        closing = True
                        selector.unregister(0)
                    else:
                        buffer += chunk
                        if len(buffer) > MAX_FRAME:
                            emit({'errorCode': 'SHARED_PROTOCOL_ERROR', 'errorMessage': 'Protocol frame exceeds limit'})
                            closing = True
                    continue
                lease = leases.get(pid)
                if lease is None:
                    unregister(key.fd)
                    continue
                if not chunk:
                    unregister(key.fd)
                    lease['fds'].discard(key.fd)
                    continue
                if channel == 'error':
                    lease['error'].extend(chunk[:max(0, 8192 - len(lease['error']))])
                else:
                    lease[channel + 'Hash'].update(chunk)
                    if lease['capture'] == 'head':
                        lease[channel].extend(chunk[:max(0, MAX_CAPTURE - len(lease[channel]))])
                    else:
                        lease[channel].extend(chunk)
                        if len(lease[channel]) > MAX_CAPTURE:
                            del lease[channel][:-MAX_CAPTURE]
        emit({'closed': True, 'healthy': worker_alive})
    finally:
        for lease in leases.values():
            stop_lease(lease, 'close')
            for descriptor in list(lease['fds']):
                unregister(descriptor)
        selector.close()
        if worker_alive:
            try:
                os.kill(worker, signal.SIGKILL)
            except ProcessLookupError:
                pass
            try:
                os.waitpid(worker, 0)
            except ChildProcessError:
                pass


def closing_signal(signum, frame):
    global CLOSING
    CLOSING = True


def main():
    global PREPARATION_PHASE
    parent_death(os.getppid())
    setup_namespace()
    signal.signal(signal.SIGTERM, closing_signal)
    signal.signal(signal.SIGINT, closing_signal)
    buffer = b''
    while b'\n' not in buffer:
        chunk = os.read(0, 65536)
        if not chunk:
            raise ValueError('Missing shared environment manifest')
        buffer += chunk
        if len(buffer) > MAX_FRAME:
            raise ValueError('Shared manifest exceeds protocol limit')
    line, remainder = buffer.split(b'\n', 1)
    PREPARATION_PHASE = 'integrity'
    pack, nodes, files, total = capture_manifest(json.loads(line))
    PREPARATION_PHASE = 'capability'
    worker = start_fuse(pack, nodes, total)
    os.close(pack)
    PREPARATION_PHASE = 'ready'
    del nodes
    emit({'ready': True, 'files': files, 'bytes': total})
    broker_loop(worker, remainder)


try:
    main()
except BaseException as error:
    try:
        emit({'ready': False, 'errorCode': 'SHARED_ENVIRONMENT_UNAVAILABLE', 'errorMessage': str(error), 'failureKind': PREPARATION_PHASE})
    except BaseException:
        pass
    sys.exit(1)
`;
