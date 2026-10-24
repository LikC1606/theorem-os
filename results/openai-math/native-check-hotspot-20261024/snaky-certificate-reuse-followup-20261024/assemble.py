from pathlib import Path
import datetime
import hashlib
import json
import re

stage = Path(__file__).resolve().parent
base = stage.parent.parent / 'snaky-ordinary-bridge-20261023'
static = stage.parent / 'snaky-integration-cost-20261024/static-reuse-followup'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
sources = {
    'canonical': ('SnakyConditionalCanonicalV8.lean', '712ecd4ee1a6cf29e5dc08a07510910addc1870b4039327836646b7a0f16daab'),
    'merged': ('SnakyConditionalCanonicalV8IntegrationMerged.lean', 'dc40df160330f9058ff0af4e85adac6ed1be8be0b2d54c7fba5f10f71450eaae'),
}
for label, (filename, expected) in sources.items():
    assert sha(base / filename) == expected
    assert sha(stage / (label + '-source.lean')) == expected

original = (stage / 'canonical-source.lean').read_text()
pattern = re.compile(r"(?m)^(?:(?:private|protected|noncomputable)\s+)*(?:def|abbrev|lemma|theorem|structure|inductive|instance)\s+([\w'.]+)")


def decl(text, name):
    matches = list(pattern.finditer(text))
    found = [(i, m) for i, m in enumerate(matches) if m.group(1) == name]
    assert len(found) == 1, (name, len(found))
    i, match = found[0]
    end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
    return re.split(r'(?m)^(?:end\b|#print\b)', text[match.start():end])[0].rstrip() + '\n'


namesets = [
    ('CandidateLargestRowSmallCommon', ['qsmall10', 'qsmall11', 'qsmall_step11']),
    ('CandidateLargestRowChunkListData', [*(f'ql614b{i}' for i in range(28)), 'ql614', 'qm614']),
    ('CandidateSemanticsCoreProbe', ['qinverseRotation', 'qorientEquiv', 'qplacementEquiv', 'qmoveRow']),
    ('CandidateDataProbe', ['qCell', 'qR', 'qR.A', 'qR.H', 'qR.height', 'qT', 'qorient', 'qplaceRow']),
]
identity = []
dependencies = []
for module, names in namesets:
    source = base / (module + '.lean')
    content = source.read_text()
    receipt = json.loads((base / (module + '.receipt.json')).read_text())
    assert receipt['exitCode'] == 0
    assert sha(source) == receipt['sourceSha256']
    assert (base / (module + '.olean')).is_file()
    dependencies.append({'module': module, 'sourceSHA256': sha(source),
                         'oleanSHA256': sha(base / (module + '.olean')),
                         'receiptSHA256': sha(base / (module + '.receipt.json'))})
    for name in names:
        a = re.sub(r'\s+', ' ', decl(original, name)).strip()
        b = re.sub(r'\s+', ' ', decl(content, name)).strip()
        identity.append({'declaration': name, 'compiledModule': module,
                         'normalizedSourceEqual': a == b,
                         'canonicalNormalizedSHA256': hashlib.sha256(a.encode()).hexdigest(),
                         'compiledNormalizedSHA256': hashlib.sha256(b.encode()).hexdigest()})
        if a != b:
            (stage / (name + '-canonical.txt')).write_text(a + '\n')
            (stage / (name + '-compiled.txt')).write_text(b + '\n')

context = ['import CandidateLargestRowSmallCommon', '', 'set_option Elab.async false',
           'set_option stderrAsMessages false', '', 'namespace OAI.SnakyConditional',
           'open OrdinaryStrategy', '',
           'run_cmd do IO.eprintln "certificate context: compiled qsmall_step11 imported"', '']
for name in ['qo614', 'qmem_moveRow_H_iff', 'qescapeI_10', 'qescapeI_11']:
    context.append(decl(original, name))
context += ['run_cmd do IO.eprintln "certificate context: exact canonical adapters added"', '',
            '#print axioms qsmall_step11', '#print axioms qmem_moveRow_H_iff', '',
            'end OAI.SnakyConditional', '']
(stage / 'CertificateContext.lean').write_text('\n'.join(context))
replacement = (static / 'qescapestep_11.replacement.lean.txt').read_text()
old = decl(original, 'qescapestep_11')
assert replacement.split(':= by')[0] == old.split(':= by')[0]
(stage / 'qescapestep_11.original.lean.txt').write_text(old)
(stage / 'qescapestep_11.replacement.lean.txt').write_text(replacement)
for kind, body in [('Baseline', old), ('Reuse', replacement)]:
    header = ('import CertificateContext\n\nset_option Elab.async false\n'
              'set_option stderrAsMessages false\n\nnamespace OAI.SnakyConditional\n'
              'open OrdinaryStrategy\n\n')
    text = (header + 'run_cmd do IO.eprintln s!"' + kind + ': proof started monoMs={← IO.monoMsNow}"\n\n' + body +
            '\nrun_cmd do IO.eprintln s!"' + kind + ': proof elaborated and kernel checked monoMs={← IO.monoMsNow}"\n\n'
            '#print axioms qescapestep_11\n\nend OAI.SnakyConditional\n')
    (stage / (kind + 'Certificate.lean')).write_text(text)
(stage / 'compiled-source-correspondence.json').write_text(json.dumps(identity, indent=2) + '\n')
provenance = {
    'createdAt': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'stage': str(stage), 'sourceRoot': str(base),
    'canonicalSourceSHA256': sha(stage / 'canonical-source.lean'),
    'mergedSourceSHA256': sha(stage / 'merged-source.lean'),
    'candidateCount': 1, 'replacedDeclaration': 'OAI.SnakyConditional.qescapestep_11',
    'reusedCertificate': 'OAI.SnakyConditional.qsmall_step11',
    'compiledDependencies': dependencies,
    'leanToolchain': 'leanprover/lean4:v4.34.1',
    'mathlibCommit': 'd13f23b723b8a846827a245b89c10fc7d3f11612',
    'sealedPackagesRoot': '/proc/1250131/fd/5',
    'sealedEnvironmentIdentity': '2d808da67c8ab8ad74458d8a53ecc2ee8da9c63a825e0429439ebf56a9a78c87',
    'activeProcessesTouched': False, 'activeSourceModified': False,
    'existingCacheModified': False, 'existingReceiptsModified': False,
    'mainRepositoryModified': False, 'queueModified': False,
    'publisherSolutionsRead': False, 'fullOriginalTargetCompiled': False,
}
(stage / 'provenance.json').write_text(json.dumps(provenance, indent=2) + '\n')
print(json.dumps({'declarationsCompared': len(identity),
                  'exactNormalizedMatches': sum(d['normalizedSourceEqual'] for d in identity),
                  'differences': [d['declaration'] for d in identity if not d['normalizedSourceEqual']]}))
