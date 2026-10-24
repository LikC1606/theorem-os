#!/usr/bin/python3
"""Run one isolated full-source Lean check without a time or heartbeat budget."""
import hashlib
import argparse
import json
import os
from pathlib import Path
import resource
import subprocess
import time
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--candidate-dir", default="character-sync-def-candidate")
options = parser.parse_args()
WORK = ROOT / options.candidate_dir
assert WORK.parent == ROOT and WORK.is_dir()
CAMPAIGN = ROOT.parent.parent
LEAN = Path("/home/lzh/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean")


def now():
    return datetime.now(timezone.utc).isoformat()


def write_json(name, value):
    destination = WORK / name
    temporary = destination.with_suffix(destination.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(destination)


def limits():
    resource.setrlimit(resource.RLIMIT_AS, (32 * 1024**3, 32 * 1024**3))


def main():
    source = WORK / "Submission.lean"
    source_sha = hashlib.sha256(source.read_bytes()).hexdigest()
    preparation = json.loads((WORK / "preparation.json").read_text())
    assert source_sha == preparation["sourceSHA256"]
    assert not (WORK / "build-started.json").exists(), "Check already started"
    package_root = CAMPAIGN / "environment/project/.lake/packages"
    package_names = ("plausible", "aesop", "batteries", "importGraph", "Qq", "mathlib", "LeanSearchClient", "proofwidgets")
    paths = [WORK, WORK / "dependencies"]
    for name in package_names:
        path = package_root / name / ".lake/build/lib/lean"
        assert path.is_dir(), str(path)
        paths.append(path)
    assert (paths[1] / "OAI/AlgebraicGeometry/CharacterVarieties/Seams/ProducedEquations.olean").is_file()
    env = os.environ.copy()
    env.pop("LEAN_SYSROOT", None)
    env["LEAN_PATH"] = ":".join(map(str, paths))
    env["LEAN_NUM_THREADS"] = "1"
    command = [str(LEAN), "-j1", "-R", ".", "-o", "Submission.olean", "Submission.lean"]
    started = time.monotonic()
    with (WORK / "build.log").open("wb") as log:
        process = subprocess.Popen(command, cwd=WORK, env=env, stdin=subprocess.DEVNULL,
                                   stdout=log, stderr=subprocess.STDOUT, preexec_fn=limits)
        receipt = {"startedAt": now(), "supervisorPid": os.getpid(), "leanPid": process.pid,
                   "sourceSHA256": source_sha, "command": command, "leanPath": paths and env["LEAN_PATH"],
                   "addressSpaceLimitBytes": 32 * 1024**3, "timeLimitSeconds": 0,
                   "nativeAcceptance": False}
        write_json("build-started.json", receipt)
        code = process.wait()
    output = WORK / "Submission.olean"
    receipt.update({"finishedAt": now(), "elapsedSeconds": time.monotonic() - started,
                    "exitCode": code, "oleanExists": output.is_file(),
                    "oleanSHA256": hashlib.sha256(output.read_bytes()).hexdigest() if output.is_file() else None})
    write_json("build-receipt.json", receipt)


if __name__ == "__main__":
    main()
