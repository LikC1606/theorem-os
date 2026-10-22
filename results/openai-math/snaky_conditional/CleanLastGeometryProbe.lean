import CleanCommonBoundsProbe
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace OAI.SnakyCertificate.StrategyBridge
lemma escape_A_bound : ∀ d ∈ escapeChildren, d.A ⊆ {(0,-1),origin} := by decide +kernel
lemma escape_common_bound (b : Cell) (hb : ∀ d ∈ escapeChildren, b ∈ d.H) : b ∈ ({(0,-1),origin} : Finset Cell) := escape_small_common b hb
lemma escape_child_height : ∀ d ∈ escapeChildren, d.height ≤ 33 := by decide +kernel
lemma escape_missing_0 : (placementEquiv 4 (0, 1)).symm (1,0) ∉ openingRow_406.H := by decide +kernel
lemma escape_missing_1 : (placementEquiv 6 (0, -2)).symm (1,0) ∉ openingRow_406.H := by decide +kernel
lemma escape_missing_2 : (placementEquiv 0 (0, 1)).symm (1,0) ∉ openingRow_533.H := by decide +kernel
lemma escape_missing_3 : (placementEquiv 0 (0, 1)).symm (1,0) ∉ openingRow_584.H := by decide +kernel
lemma escape_missing_4 : (placementEquiv 6 (0, -2)).symm (1,0) ∉ openingRow_586.H := by decide +kernel
lemma escape_missing_5 : (placementEquiv 6 (0, -2)).symm (1,0) ∉ openingRow_587.H := by decide +kernel
lemma escape_missing_6 : (placementEquiv 2 (0, 1)).symm (1,0) ∉ openingRow_590.H := by decide +kernel
lemma escape_missing_7 : (placementEquiv 2 (0, -2)).symm (1,0) ∉ openingRow_591.H := by decide +kernel
lemma escape_missing_8 : (placementEquiv 0 (0, 1)).symm (1,0) ∉ openingRow_601.H := by decide +kernel
lemma escape_missing_9 : (placementEquiv 2 (0, 1)).symm (1,0) ∉ openingRow_602.H := by decide +kernel
lemma escape_missing_10 : (placementEquiv 5 (0, -2)).symm (1,0) ∉ openingRow_611.H := by decide +kernel
lemma escape_missing_11 : (placementEquiv 4 (1, -1)).symm (1,0) ∉ openingRow_614.H := by decide +kernel
lemma escape_child_missing : ∀ d ∈ escapeChildren, (1,0) ∉ d.H := by
  intro d hd
  simp only [escapeChildren, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun h => escape_missing_0 ((mem_moveRow_H_iff 4 (0, 1) openingRow_406 (1,0)).mp h)
  · exact fun h => escape_missing_1 ((mem_moveRow_H_iff 6 (0, -2) openingRow_406 (1,0)).mp h)
  · exact fun h => escape_missing_2 ((mem_moveRow_H_iff 0 (0, 1) openingRow_533 (1,0)).mp h)
  · exact fun h => escape_missing_3 ((mem_moveRow_H_iff 0 (0, 1) openingRow_584 (1,0)).mp h)
  · exact fun h => escape_missing_4 ((mem_moveRow_H_iff 6 (0, -2) openingRow_586 (1,0)).mp h)
  · exact fun h => escape_missing_5 ((mem_moveRow_H_iff 6 (0, -2) openingRow_587 (1,0)).mp h)
  · exact fun h => escape_missing_6 ((mem_moveRow_H_iff 2 (0, 1) openingRow_590 (1,0)).mp h)
  · exact fun h => escape_missing_7 ((mem_moveRow_H_iff 2 (0, -2) openingRow_591 (1,0)).mp h)
  · exact fun h => escape_missing_8 ((mem_moveRow_H_iff 0 (0, 1) openingRow_601 (1,0)).mp h)
  · exact fun h => escape_missing_9 ((mem_moveRow_H_iff 2 (0, 1) openingRow_602 (1,0)).mp h)
  · exact fun h => escape_missing_10 ((mem_moveRow_H_iff 5 (0, -2) openingRow_611 (1,0)).mp h)
  · exact fun h => escape_missing_11 ((mem_moveRow_H_iff 4 (1, -1) openingRow_614 (1,0)).mp h)
lemma escape_diag_missing : (1,1) ∉ escapeMemo.H := by
  intro h
  obtain ⟨a,ha,he⟩ := Finset.mem_image.mp h
  have hae : a = (1,0) := by
    apply (placementEquiv 0 (0,1)).injective
    exact he.trans (by rfl)
  subst a
  have hn := not_mem_unionH escapeChildren (1,0) escape_child_missing
  exact (Finset.mem_insert.mp ha).elim (by decide) hn
lemma escape_rotation_missing (r : Fin 8) (b : Cell) (hr : placement r (0,0) (1,1) = b) :
    b ∉ (moveRow r (0,0) escapeMemo).H := by
  intro h
  have hm := (mem_moveRow_H_iff r (0,0) escapeMemo b).mp h
  have he : (placementEquiv r (0,0)).symm b = (1,1) := by
    rw [← hr]
    exact (placementEquiv r (0,0)).symm_apply_apply (1,1)
  exact escape_diag_missing (he ▸ hm)
lemma root_A_bound : ∀ d ∈ rootChildren, d.A ⊆ {origin} := by decide +kernel
lemma root_child_height : ∀ d ∈ rootChildren, d.height ≤ 34 := by decide +kernel
lemma root_common_bound (b : Cell) (hb : ∀ d ∈ rootChildren, b ∈ d.H) : b ∈ ({origin} : Finset Cell) := by
  have hs := root_small_common b hb
  simp only [rootI_19, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact False.elim (escape_rotation_missing 6 (-1,-1) (by rfl) (hb (moveRow 6 (0,0) escapeMemo) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))
  · exact False.elim (escape_rotation_missing 3 (-1,1) (by rfl) (hb (moveRow 3 (0,0) escapeMemo) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))
  · exact Finset.mem_singleton_self _
  · exact False.elim (escape_rotation_missing 2 (1,-1) (by rfl) (hb (moveRow 2 (0,0) escapeMemo) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))
  · exact False.elim (escape_rotation_missing 0 (1,1) (by rfl) (hb (moveRow 0 (0,0) escapeMemo) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))
end OAI.SnakyCertificate.StrategyBridge
