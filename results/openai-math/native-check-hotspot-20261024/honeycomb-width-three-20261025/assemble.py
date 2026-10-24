from pathlib import Path
s = Path(__file__).resolve().parent
names = ['WidthThree.count_five', 'WidthThree.count_block_bound', 'WidthThree.path_mem_allPaths', 'WidthThree.path_card', 'WidthThree.stripGrowthAtThree', 'width_three_summability_diagnostic']
source = (s / 'CurrentPrefix.lean.inc').read_text() + '\n' + (s / 'WidthThree.lean.inc').read_text() + '\n' + '\n'.join('#check @' + n + '\n#print axioms ' + n for n in names) + '\nend PolynomialVacuumBridge.Corridor\nend OAI\n'
(s / 'WidthThree.lean').write_text(source)
