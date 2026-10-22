from pathlib import Path
import shutil, json, hashlib
root = Path(__file__).resolve().parent
source = root / "support"
target = root / ".lake/packages/cartier_support"
manifest = json.loads((root / "support-manifest.json").read_text())
for entry in manifest["files"]:
    p = root / entry["path"]
    assert hashlib.sha256(p.read_bytes()).hexdigest() == entry["sha256"], str(p)
if target.exists():
    raise SystemExit("Existing .lake/packages/cartier_support: use a fresh standalone copy.")
target.parent.mkdir(parents=True, exist_ok=True)
shutil.copytree(source, target)
print(json.dumps({"staged": "cartier_support", "modules": len(manifest["files"])}))
