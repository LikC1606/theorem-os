set -eu
publisher_source=$PWD
mkdir -p -- "$publisher_source/.lake"
publisher_eval=$(mktemp -d "$publisher_source/.lake/publisher-eval.XXXXXXXX")
trap 'publisher_status=$?; rm -rf -- "$publisher_eval" || publisher_status=1; exit "$publisher_status"' 0
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM
for publisher_entry in ./* ./.[!.]* ./..?*; do
    [ -e "$publisher_entry" ] || [ -L "$publisher_entry" ] || continue
    case "$publisher_entry" in ./.lake|./.git) continue ;; esac
    cp -a -- "$publisher_entry" "$publisher_eval/"
done
mkdir -p -- "$publisher_eval/.lake/packages"
cp -a --reflink=auto -- "$publisher_source/.lake/packages/." "$publisher_eval/.lake/packages/"
chmod -R u+w -- "$publisher_eval/.lake/packages"
/usr/bin/python3 - "$publisher_eval" <<'OAI_PACKAGE_OVERRIDES'
import json
from pathlib import Path
import sys
project = Path(sys.argv[1])
manifest = json.loads((project / 'lake-manifest.json').read_text())
packages = []
for entry in manifest['packages']:
    name = entry['name']
    if not isinstance(name, str) or not name or any(c in name for c in ('/', chr(92), chr(0))) or name in ('.', '..'):
        raise ValueError('invalid copied package name')
    unquoted = name[1:-1] if name.startswith(chr(171)) and name.endswith(chr(187)) else name
    directory = next((project / '.lake/packages' / candidate for candidate in (name, unquoted)
                      if (project / '.lake/packages' / candidate).is_dir()), None)
    if directory is None:
        raise ValueError('copied manifest package is missing: ' + name)
    packages.append({**entry, 'type': 'path', 'dir': str(directory)})
(project / '.lake/package-overrides.json').write_text(json.dumps({'schemaVersion': '1.2.0', 'packages': packages}) + chr(10))
OAI_PACKAGE_OVERRIDES
cat > "$publisher_eval/comparator.json" <<'OAI_COMPARATOR_JSON'
{
  "challenge_module": "Challenge",
  "solution_module": "Submission",
  "theorem_names": [
    "OAI.CartierSections.isCompact_closedChartFieldRetraction_cone"
  ],
  "definition_names": [],
  "permitted_axioms": [
    "propext",
    "Quot.sound",
    "Classical.choice"
  ],
  "enable_nanoda": false
}
OAI_COMPARATOR_JSON
cd -- "$publisher_eval"
export LEAN_NUM_THREADS=1
lake build Challenge Submission
lake env /bin/sh -c 'if [ -x /runtime/pinned-lean/bin/lean ]; then PATH=/runtime/pinned-lean/bin:$PATH; export PATH; fi; exec comparator comparator.json'
