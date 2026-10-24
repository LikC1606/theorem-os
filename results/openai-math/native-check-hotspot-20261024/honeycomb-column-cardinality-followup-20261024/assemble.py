from pathlib import Path

stage = Path(__file__).resolve().parent
header = '''import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Chain

set_option Elab.async false
set_option stderrAsMessages false

namespace OAI.PolynomialVacuumBridge.Corridor

'''
theorems = [
    'bridgeLayerColumnCode_injective',
    'bridgeVertexList_length_le_columnSet',
    'bridgeLength_le_columnSet',
    'bridgeLength_le_columnInterval',
    'bridgeLength_le_columnBox',
    'bridgeLength_le_slabSet',
    'bridgeLength_le_occupiedSlabs',
    'bridgeColumn_natAbs_le_radius',
    'bridgeLength_le_columnRadius',
]
footer = '\n' + '\n'.join('#print axioms ' + name for name in theorems)
footer += '\n\nend OAI.PolynomialVacuumBridge.Corridor\n'
source = header + (stage / 'CanonicalGeometry.lean.inc').read_text()
source += '\n' + (stage / 'ColumnCardinality.lean.inc').read_text() + footer
(stage / 'ColumnCardinality.lean').write_text(source)
