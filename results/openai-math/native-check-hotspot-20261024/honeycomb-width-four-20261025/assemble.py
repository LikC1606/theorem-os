from pathlib import Path
s=Path(__file__).resolve().parent
names=['WidthFour.mem_neighbors','WidthFour.edgeWeight_ge_one','WidthFour.edgeWeight_le_sixtyFour','WidthFour.potential_step','WidthFour.continuations_card','WidthFour.mem_continuations','WidthFour.allPaths_card','WidthFour.path_mem_allPaths','WidthFour.path_card_real','WidthFour.beta_lt_mu','WidthFour.stripGrowthAtFour','width_four_summability_diagnostic']
source=(s/'CurrentPrefix.lean.inc').read_text()+'\n'+(s/'WidthFour.lean.inc').read_text()+'\n'+'\n'.join('#check @'+n+'\n#print axioms '+n for n in names)+'\nend PolynomialVacuumBridge.Corridor\nend OAI\n'
(s/'WidthFour.lean').write_text(source)
