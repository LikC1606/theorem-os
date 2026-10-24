from pathlib import Path
stage = Path(__file__).resolve().parent
names = ['bridgeBoxColumn_eq_twice_position', 'bridgeBoundedVertices_finite',
         'bridgeConfinedVertex_finite', 'bridgeConfinedVertexList_map_val',
         'bridgeConfinedVertexList_nodup', 'bridgeConfinedVertexList_injective',
         'bridgeConfinedPath_finite', 'bridgeConfined_summable_weight',
         'bridgeConfined_summable_firstLengthWeight',
         'bridgeConfined_summable_normalizedFirstLengthWeight', 'bridgeConfined_sums']
source = 'import Mathlib\n\nset_option Elab.async false\nset_option stderrAsMessages false\n\nnamespace OAI.PolynomialVacuumBridge.Corridor\n\n'
for f in ['CanonicalDefinitions.lean.inc','ExistingColumnCode.lean.inc','ConfinedFiniteness.lean.inc']:
    source += (stage / f).read_text() + '\n'
source += '\n'.join('#print axioms ' + n for n in names)
source += '\n\nend OAI.PolynomialVacuumBridge.Corridor\n'
(stage / 'ConfinedFiniteness.lean').write_text(source)
