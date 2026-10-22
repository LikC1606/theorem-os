import CleanLastGeometryProbe
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace OAI.SnakyCertificate.StrategyBridge
open OAI.SnakyConditional.OrdinaryStrategy
lemma goal_translation_cancel (S : Finset Cell) :
    (S.image (placement 0 (0,-1))).image (placement 0 (0,1)) = S := by
  rw [Finset.image_image]
  have hf : placement 0 (0,1) ∘ placement 0 (0,-1) = id := by
    funext p; ext <;> simp [placement, orient]
  rw [hf, Finset.image_id]
theorem empty_winning_of_opening_rows
    (h406 : Threat Goal openingRow_406.A openingRow_406.H openingRow_406.height)
    (h533 : Threat Goal openingRow_533.A openingRow_533.H openingRow_533.height)
    (h557 : Threat Goal openingRow_557.A openingRow_557.H openingRow_557.height)
    (h584 : Threat Goal openingRow_584.A openingRow_584.H openingRow_584.height)
    (h586 : Threat Goal openingRow_586.A openingRow_586.H openingRow_586.height)
    (h587 : Threat Goal openingRow_587.A openingRow_587.H openingRow_587.height)
    (h590 : Threat Goal openingRow_590.A openingRow_590.H openingRow_590.height)
    (h591 : Threat Goal openingRow_591.A openingRow_591.H openingRow_591.height)
    (h595 : Threat Goal openingRow_595.A openingRow_595.H openingRow_595.height)
    (h601 : Threat Goal openingRow_601.A openingRow_601.H openingRow_601.height)
    (h602 : Threat Goal openingRow_602.A openingRow_602.H openingRow_602.height)
    (h603 : Threat Goal openingRow_603.A openingRow_603.H openingRow_603.height)
    (h611 : Threat Goal openingRow_611.A openingRow_611.H openingRow_611.height)
    (h614 : Threat Goal openingRow_614.A openingRow_614.H openingRow_614.height)
    (h615 : Threat Goal openingRow_615.A openingRow_615.H openingRow_615.height)
    : Winning Goal 35 ∅ ∅ := by
  have hec : ∀ d ∈ escapeChildren, Threat Goal d.A d.H d.height := by
    intro d hd
    simp only [escapeChildren, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact moveRow_threat _ _ _ h406
    · exact moveRow_threat _ _ _ h406
    · exact moveRow_threat _ _ _ h533
    · exact moveRow_threat _ _ _ h584
    · exact moveRow_threat _ _ _ h586
    · exact moveRow_threat _ _ _ h587
    · exact moveRow_threat _ _ _ h590
    · exact moveRow_threat _ _ _ h591
    · exact moveRow_threat _ _ _ h601
    · exact moveRow_threat _ _ _ h602
    · exact moveRow_threat _ _ _ h611
    · exact moveRow_threat _ _ _ h614
  have heraw : Threat Goal {(0,-1)} escapeRawH 34 := by
    refine threat_fork Goal (fun h hG => goal_mono h hG) origin
      (escapeChildren.map (fun d => (⟨d.A,d.H,d.height⟩ : ThreatData Cell)))
      (by simp [escapeChildren]) 33 ?_ ?_ _ _ ?_ ?_ ?_ ?_
    · intro d hd; obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
      exact hec e he
    · intro d hd; obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
      exact escape_child_height e he
    · intro d hd; obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
      simpa only [Finset.pair_comm origin (0,-1)] using escape_A_bound e he
    · intro d hd; obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
      intro x hx
      exact Finset.mem_insert_of_mem (mem_unionH escapeChildren e he hx)
    · exact Finset.mem_insert_self _ _
    · intro b hb
      simpa only [Finset.pair_comm origin (0,-1)] using escape_common_bound b (by
        intro e he; exact hb ⟨e.A,e.H,e.height⟩ (List.mem_map.mpr ⟨e,he,rfl⟩))
  let raw : RowData := ⟨{(0,-1)}, escapeRawH,34⟩
  have he := moveRow_threat 0 (0,1) raw heraw
  have hmove : moveRow 0 (0,1) raw = escapeMemo := by
    apply openingRow_ext
    · decide +kernel
    · rfl
    · rfl
  rw [hmove] at he
  have hrc : ∀ d ∈ rootChildren, Threat Goal d.A d.H d.height := by
    intro d hd
    simp only [rootChildren, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact moveRow_threat _ _ _ h557
    · exact moveRow_threat _ _ _ h557
    · exact moveRow_threat _ _ _ h595
    · exact moveRow_threat _ _ _ h595
    · exact moveRow_threat _ _ _ h595
    · exact moveRow_threat _ _ _ h595
    · exact moveRow_threat _ _ _ h595
    · exact moveRow_threat _ _ _ h595
    · exact moveRow_threat _ _ _ h595
    · exact moveRow_threat _ _ _ h595
    · exact moveRow_threat _ _ _ h603
    · exact moveRow_threat _ _ _ h603
    · exact moveRow_threat _ _ _ h603
    · exact moveRow_threat _ _ _ h603
    · exact moveRow_threat _ _ _ h557
    · exact moveRow_threat _ _ _ h557
    · exact moveRow_threat _ _ _ h615
    · exact moveRow_threat _ _ _ h615
    · exact moveRow_threat _ _ _ h615
    · exact moveRow_threat _ _ _ h615
    · exact moveRow_threat _ _ _ he
    · exact moveRow_threat _ _ _ he
    · exact moveRow_threat _ _ _ he
    · exact moveRow_threat _ _ _ he
  have hr : Threat Goal ∅ (insert origin (unionH rootChildren)) 35 := by
    refine threat_fork Goal (fun h hG => goal_mono h hG) origin
      (rootChildren.map (fun d => (⟨d.A,d.H,d.height⟩ : ThreatData Cell)))
      (by simp [rootChildren]) 34 ?_ ?_ _ _ ?_ ?_ ?_ ?_
    · intro d hd; obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
      exact hrc e he
    · intro d hd; obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd; exact root_child_height e he
    · intro d hd; obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd; exact root_A_bound e he
    · intro d hd x hx; obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
      exact Finset.mem_insert_of_mem (mem_unionH rootChildren e he hx)
    · exact Finset.mem_insert_self _ _
    · intro b hb
      exact root_common_bound b (by
        intro e he; exact hb ⟨e.A,e.H,e.height⟩ (List.mem_map.mpr ⟨e,he,rfl⟩))
  exact hr ∅ ∅ (Finset.Subset.refl _) (Finset.disjoint_empty_right _)
end OAI.SnakyCertificate.StrategyBridge
