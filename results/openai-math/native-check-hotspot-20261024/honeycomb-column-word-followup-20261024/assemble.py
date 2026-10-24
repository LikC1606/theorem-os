from pathlib import Path

stage = Path(__file__).resolve().parent
header = '''import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Chain

set_option Elab.async false
set_option stderrAsMessages false

namespace OAI.PolynomialVacuumBridge.Corridor

'''
names = [
    'bridgeAdjacent_unique_of_column',
    'bridgeChain_tail_eq_of_columnWord',
    'bridgeVertices_eq_of_columnWord',
    'bridgeColumnWord_injective',
]
footer = '\n' + '\n'.join('#print axioms ' + name for name in names)
footer += '\n\nend OAI.PolynomialVacuumBridge.Corridor\n'
source = header + (stage / 'CanonicalGeometry.lean.inc').read_text()
source += '\n' + (stage / 'ColumnWordInjection.lean.inc').read_text() + footer
(stage / 'ColumnWordInjection.lean').write_text(source)
