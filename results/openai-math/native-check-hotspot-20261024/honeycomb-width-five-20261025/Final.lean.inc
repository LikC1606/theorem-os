/-- Unconditional height-five summability, using a checked six-vertex memory. -/
theorem width_five_summability_diagnostic :
    Summable (weight (h := 5)) ∧ Summable (firstLengthWeight (h := 5)) := by
  obtain ⟨C, β, hC, hβ, hlt, hcount⟩ := WidthFive.stripGrowthAtFive
  have hL : Summable (firstLengthWeight (h := 5)) :=
    bridgeSummable_firstLengthWeight_of_mu_bound hC hβ hlt hcount
  exact ⟨bridgeSummable_weight_of_summable_firstLengthWeight hL, hL⟩

#check @WidthFive.table_checked
#print axioms WidthFive.table_checked
#check @WidthFive.count_weighted
#print axioms WidthFive.count_weighted
#check @WidthFive.path_mem_allPaths
#print axioms WidthFive.path_mem_allPaths
#check @WidthFive.path_card_real
#print axioms WidthFive.path_card_real
#check @WidthFive.stripGrowthAtFive
#print axioms WidthFive.stripGrowthAtFive
#check @width_five_summability_diagnostic
#print axioms width_five_summability_diagnostic
