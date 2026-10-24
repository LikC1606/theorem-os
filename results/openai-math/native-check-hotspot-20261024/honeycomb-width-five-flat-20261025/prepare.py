"""Prepare isolated source candidates from frozen public evidence only."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

stage = Path(__file__).resolve().parent
hotspot = stage.parent
old = hotspot / 'honeycomb-width-five-20261025'
base_path = hotspot / 'honeycomb-native-width-three-20261025/proof-source/Submission.lean'
constraints_path = hotspot / 'honeycomb-width-five-source-constraints-20261025.json'
sha = lambda b: hashlib.sha256(b).hexdigest()
assert sha(constraints_path.read_bytes()) == '65f367e1b022234aefa1f3121fb319326de53d294ebfb9a208739f783d3986d5'
snapshot = json.loads(constraints_path.read_text())
(stage / 'fixed-source-constraints.json').write_bytes(constraints_path.read_bytes())
original = (old / 'WidthFive.lean.inc').read_text()
assert sha(original.encode()) == 'a33eef19ac38782883227589dc48e125ff7e3d4379da9f6cf4ebc20e9c8760ca'
assert original.startswith('namespace WidthFive\n')
inner, outer = original[len('namespace WidthFive\n'):].split('\nend WidthFive\n', 1)
helper_names = re.findall(r'(?m)^(?:@\[[^\n]+\]\s*)?(?:noncomputable\s+)?(?:def|lemma|theorem)\s+([A-Za-z_][A-Za-z0-9_\']*)', inner)
mapping = {name: 'widthFive' + name[0].upper() + name[1:] for name in helper_names}
assert len(mapping) == len(helper_names)
body = inner + '\n' + outer
body = body.replace('WidthFive.', '')
token = re.compile(r'\b(' + '|'.join(re.escape(n) for n in sorted(mapping, key=len, reverse=True)) + r')\b')
flat_anonymous = token.sub(lambda m: mapping[m[0]], body)
flat_named = flat_anonymous.replace('instance (v : Vertex)',
    'instance widthFiveDecidableInside (v : Vertex)').replace('instance (w : List Vertex)',
    'instance widthFiveDecidableRowOK (w : List Vertex)')
assert flat_named.count('instance widthFiveDecidable') == 2
flat = flat_named.replace('@[simp] lemma ', 'lemma ')
assert len(re.findall(r'(?m)^\]$', flat)) == 31
flat = re.sub(r'(?m)^\]$', '  ]', flat)
flat = flat.replace('/-- Unconditional height-five summability, using a checked six-vertex memory. -/\n', '')
assert not re.search(r'(?m)^\s*(namespace|end|section|open|set_option|attribute)\b', flat)
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b', flat)
assert 'WidthFive.' not in flat
base = base_path.read_text()
anchor = 'theorem finite_bridge_sums : FiniteBridgeSums := by\n'
assert base.count(anchor) == 1
assert 'widthFive' not in base
assert 'width_five_summability_diagnostic' not in base

variants = {
    'baseline': '',
    'namespaced': original,
    'flat-anonymous': flat_anonymous,
    'flat-named-simp': flat_named,
    'project': flat,
}
workspace = Path('/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/tasks/HoneycombBridgeFiniteness/workspace')
trusted = {}
for filename, digest in snapshot['constraints']['trustedFiles'].items():
    git_path = snapshot['provenance']['projectRelative'] + '/' + filename
    data = subprocess.run(['git', '--no-optional-locks', 'show',
        snapshot['provenance']['baseCommit'] + ':' + git_path], cwd=workspace,
        check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE).stdout
    assert sha(data) == digest, filename
    trusted[filename] = data

for name, inc in variants.items():
    root = stage / name
    root.mkdir(exist_ok=True)
    (root / 'Submission.lean').write_text(base.replace(anchor, inc + '\n' + anchor) if inc else base)
    for filename, data in trusted.items():
        (root / filename).write_bytes(data)

(stage / 'OriginalWidthFive.lean.inc').write_text(original)
(stage / 'BaseSubmission.lean').write_text(base)
(stage / 'WidthFiveFlat.lean.inc').write_text(flat)
(stage / 'rename-map.json').write_text(json.dumps({
    'helpers': mapping,
    'instances': {'anonymous inside': 'widthFiveDecidableInside',
                  'anonymous rowOK': 'widthFiveDecidableRowOK'},
    'removedContext': ['namespace WidthFive', 'end WidthFive', 'final new doc comment'],
    'tableCloseBracketsIndented': 31,
    'optionalSimpAttributeRemoved': True,
}, indent=2) + '\n')
provenance = json.loads((old / 'provenance.json').read_text())
provenance.update({
    'scope': 'Height-five source-structure compatibility repair; mathematics unchanged',
    'originalFrozenPackage': str(old), 'originalIncrementSHA256': sha(original.encode()),
    'basePublicSource': str(base_path), 'basePublicSourceSHA256': sha(base.encode()),
    'fixedConstraintsSnapshotSHA256': sha(constraints_path.read_bytes()),
    'guardModule': '/home/lzh/theorem-os-runs/openai-math-d-to-s-20261022/validation/honeycomb-new-build-continuation-20261024/runtime/src/solver/problem.ts',
    'preparedCandidateSHA256': sha((stage/'project/Submission.lean').read_bytes()),
    'preparedIncrementSHA256': sha(flat.encode()),
    'oldSuccessfulSourceRerun': False,
})
for key in ['archivedAt', 'sourceSHA256', 'incrementSHA256', 'diagnosticSource',
            'diagnosticSourceSHA256', 'noLeanRerunDuringArchival']:
    provenance.pop(key, None)
(stage / 'provenance.json').write_text(json.dumps(provenance, indent=2) + '\n')
print(json.dumps({'helperCount': len(mapping), 'instanceCount': 2,
                  'candidateSHA256': provenance['preparedCandidateSHA256'],
                  'incrementSHA256': provenance['preparedIncrementSHA256']}))
