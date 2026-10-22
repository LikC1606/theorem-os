import CleanOpeningDefinitionsProbe
namespace OAI.SnakyCertificate.StrategyBridge
lemma initial_probe : (moveRow 4 (0,1) openingRow_406).H ⊆ escapeI_0 := by
  have h : ∀ a ∈ openingRow_406.H, placement 4 (0,1) a ∈ escapeI_0 := by decide +kernel
  intro b hb
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
  exact h a ha
end OAI.SnakyCertificate.StrategyBridge
