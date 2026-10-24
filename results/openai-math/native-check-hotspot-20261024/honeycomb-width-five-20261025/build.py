from pathlib import Path
import sys

stage = Path(__file__).resolve().parent
pieces = ['CurrentPrefix.lean.inc', 'Basic.lean.inc', 'PotentialTable.lean.inc',
          'FiniteCertificate.lean.inc', 'CertificateChecks.lean.inc']
if '--proof' in sys.argv:
    pieces += ['Proof.lean.inc']
text = '\n'.join((stage / p).read_text() for p in pieces)
text += '\nend WidthFive\n'
if '--proof' in sys.argv:
    text += (stage / 'Final.lean.inc').read_text()
else:
    text += '\n#check @WidthFive.table_checked\n#print axioms WidthFive.table_checked\n'
text += '\nend PolynomialVacuumBridge.Corridor\nend OAI\n'
(stage / 'WidthFive.lean').write_text(text)
