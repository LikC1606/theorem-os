#!/usr/bin/python3
"""Compare the completed standalone Character artifact with the original target."""
from datetime import datetime, timezone
import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import shutil
import subprocess
import time


stage = Path(__file__).resolve().parent
campaign = stage.parent.parent
candidate = stage / "character-sync-def-v2-candidate"
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--prebuilt-project", action="store_true")
parser.add_argument("--output-dir")
options = parser.parse_args()
output = stage / (options.output_dir or ("character-sync-def-v2-comparator-prebuilt"
                  if options.prebuilt_project else "character-sync-def-v2-comparator"))
assert output.parent == stage
output.mkdir(exist_ok=False)


def digest(file):
    return hashlib.sha256(file.read_bytes()).hexdigest()


def limits():
    resource.setrlimit(resource.RLIMIT_AS, (32 * 1024**3, 32 * 1024**3))


build = json.loads((candidate / "build-receipt.json").read_text())
audit = json.loads((candidate / "audit-receipt.json").read_text())
assert build["exitCode"] == 0 and audit["passed"]
assert digest(candidate / "Submission.lean") == build["sourceSHA256"] == audit["sourceSHA256"]
assert digest(candidate / "Submission.olean") == build["oleanSHA256"]
for name in ("Submission.lean", "Submission.olean"):
    shutil.copyfile(candidate / name, output / name)
challenge = campaign / "metadata/challenges/CharacterVarietiesAllSeamsSupport.lean"
configuration = campaign / "metadata/challenges/CharacterVarietiesAllSeamsSupport.json"
shutil.copyfile(challenge, output / "Challenge.lean")
config = json.loads(configuration.read_text())
config.update(challenge_module="Challenge", solution_module="Submission")
(output / "comparator.json").write_text(json.dumps(config, indent=2) + "\n")
if options.prebuilt_project:
    # Lake registers the two already compiled modules. The unchanged comparator
    # still exports, compares and replays their proof terms in the Lean kernel.
    # No cache trace or native evaluator configuration is written or altered.
    (output / "lakefile.toml").write_text(
        'name = "character_prebuilt_audit"\nversion = "0.1.0"\n\n'
        '[[lean_lib]]\nname = "Challenge"\ndefaultFacets = []\n\n'
        '[[lean_lib]]\nname = "Submission"\ndefaultFacets = []\n')
    (output / "lean-toolchain").write_text("leanprover/lean4:v4.34.1\n")
tool_root = campaign / "environment/tools-v4.34.1"
manifest = json.loads((tool_root / "manifest.json").read_text())
for name in ("comparator", "lean4export"):
    assert digest(tool_root / name) == manifest["tools"][name]["sha256"]
lean = Path("/home/lzh/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean")
environment = os.environ.copy()
environment.pop("LEAN_SYSROOT", None)
environment["LEAN_NUM_THREADS"] = "1"
environment["LEAN_PATH"] = str(output) + ":" + build["leanPath"].split(":", 1)[1]
environment["PATH"] = str(lean.parent) + ":" + str(tool_root) + ":" + environment["PATH"]
record = {
    "startedAt": datetime.now(timezone.utc).isoformat(),
    "sourceSHA256": build["sourceSHA256"],
    "oleanSHA256": build["oleanSHA256"],
    "originalChallengeSHA256": digest(challenge),
    "originalComparatorSHA256": digest(configuration),
    "adaptedComparatorSHA256": digest(output / "comparator.json"),
    "comparatorBinarySHA256": digest(tool_root / "comparator"),
    "submissionRecompiled": False,
    "prebuiltLakeProject": options.prebuilt_project,
    "nativeEvaluatorChanged": False,
    "nativeAccepted": False,
    "addressSpaceLimitBytes": 32 * 1024**3,
    "timeLimitSeconds": 0,
    "attribution": "Standalone original-comparator check of a genuine completed artifact; native pipeline acceptance remains separate.",
    "commands": [],
}


def save(name):
    (output / name).write_text(json.dumps(record, indent=2) + "\n")


save("started.json")
commands = [
    ("challenge", [str(lean), "-j1", "-R", ".", "-o", "Challenge.olean", "Challenge.lean"]),
    ("comparator", [str(tool_root / "comparator"), "comparator.json"]),
]
if options.prebuilt_project:
    commands.insert(0, ("lake-manifest", [str(lean.parent / "lake"), "update"]))
for label, command in commands:
    started = time.monotonic()
    with (output / (label + ".log")).open("wb") as log:
        process = subprocess.Popen(command, cwd=output, env=environment,
                                   stdin=subprocess.DEVNULL, stdout=log,
                                   stderr=subprocess.STDOUT, preexec_fn=limits)
        code = process.wait()
    record["commands"].append({"label": label, "command": command, "exitCode": code,
                               "elapsedSeconds": time.monotonic() - started})
    if code:
        break
record.update(finishedAt=datetime.now(timezone.utc).isoformat(),
              passed=len(record["commands"]) == len(commands) and all(x["exitCode"] == 0 for x in record["commands"])
              and "Your solution is okay!" in (output / "comparator.log").read_text())
save("receipt.json")
print(json.dumps(record), flush=True)
raise SystemExit(0 if record["passed"] else 1)
