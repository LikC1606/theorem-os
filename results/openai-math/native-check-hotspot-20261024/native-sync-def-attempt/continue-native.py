#!/usr/bin/python3
"""Continue this prepared attempt and submit its verified candidate normally."""
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
import time


stage = Path(__file__).resolve().parent
receipt_file = stage / "continuation-receipt.json"
with receipt_file.open("x") as output:
    output.write("{}\n")
record = {"phase": "waiting_for_startup", "startedAt": datetime.now(timezone.utc).isoformat(),
          "nativeAccepted": False, "sourceQueued": False, "timeLimitSeconds": 0}


def save(**updates):
    record.update(updates, observedAt=datetime.now(timezone.utc).isoformat())
    temporary = receipt_file.with_suffix(".tmp")
    temporary.write_text(json.dumps(record, indent=2) + "\n")
    temporary.replace(receipt_file)


def read(file):
    return json.loads(file.read_text())


save()
try:
    build = read(stage.parent / "character-sync-def-v2-candidate/build-receipt.json")
    audit = read(stage.parent / "character-sync-def-v2-candidate/audit-receipt.json")
    guard = read(stage.parent / "guard-preflight-v2/receipt.json")
    assert build["exitCode"] == 0 and audit["passed"] and guard["passed"]
    assert build["sourceSHA256"] == audit["sourceSHA256"] == guard["sourceSHA256"]
    save(sourceSHA256=build["sourceSHA256"])
    while True:
        startup = read(stage / "startup-receipt.json")
        if startup["phase"] == "startup_finished":
            assert startup["exitCode"] == 0, "Native startup failed; inspect startup.log."
            break
        time.sleep(2)

    with (stage / "continuation-resume.log").open("wb") as log:
        process = subprocess.Popen(["/usr/bin/python3", str(stage / "run-native.py"), "resume"],
                                   cwd=stage, stdin=subprocess.DEVNULL,
                                   stdout=log, stderr=subprocess.STDOUT)
        save(phase="waiting_for_native_plan", resumeSupervisorPid=process.pid)
        info = read(stage / "preparation.json")
        state_file = Path(info["output"] + ".runtime/state.json")
        while True:
            if state_file.exists():
                state = read(state_file)
                if state.get("cooperation", {}).get("planVersion"):
                    assert state["phase"] != "finished", "Native attempt finished before delivery."
                    break
            assert process.poll() is None, "Native resume exited before its plan was available."
            time.sleep(2)
        save(phase="submitting_through_native_queue", runId=state["runId"])
        bun = "/home/lzh/.venvs/deepscientist-finance/.bun/bin/bun"
        for suffix, flags in (("dry-run", []), ("queue", ["--queue"])):
            with (stage / ("continuation-" + suffix + ".log")).open("wb") as queue_log:
                result = subprocess.run([bun, str(stage / "queue-candidate.ts"), *flags],
                                        cwd=stage, stdin=subprocess.DEVNULL,
                                        stdout=queue_log, stderr=subprocess.STDOUT)
            assert result.returncode == 0, "Native queue command failed; inspect its log before retrying."
        queued = read(stage / "queue-receipt.json")
        assert queued["candidateQueued"] and queued["sourceSHA256"] == build["sourceSHA256"]
        save(phase="native_running", sourceQueued=True, queueResult=queued["result"])
        code = process.wait()
    final = read(stage / "resume-receipt.json")
    save(phase="native_finished", resumeExitCode=code, nativeAccepted=final["nativeAccepted"],
         resultStatus=final.get("resultStatus"), resultReason=final.get("resultReason"))
except Exception as error:
    save(phase="continuation_failed", error=str(error))
    raise
