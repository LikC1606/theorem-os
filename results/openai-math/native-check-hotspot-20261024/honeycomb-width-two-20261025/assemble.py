from pathlib import Path
s = Path(__file__).resolve().parent
names = ['WidthTwo.nextPairs_card', 'WidthTwo.continuations_card', 'WidthTwo.path_mem_allPaths', 'WidthTwo.path_card', 'WidthTwo.stripGrowthAtTwo', 'width_two_summability_diagnostic']
source = (s / 'CurrentPrefix.lean.inc').read_text() + '\n' + (s / 'WidthTwo.lean.inc').read_text() + '\n' + '\n'.join('#check @' + n + '\n#print axioms ' + n for n in names) + '\nend PolynomialVacuumBridge.Corridor\nend OAI\n'
(s / 'WidthTwo.lean').write_text(source)
