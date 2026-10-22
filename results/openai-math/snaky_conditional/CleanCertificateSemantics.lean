import CleanGenericThreat
import CertificateData

namespace OAI.SnakyCertificate

namespace StrategyBridge

open OAI.SnakyConditional.OrdinaryStrategy

def Goal (M : Finset Cell) : Prop :=
  ∃ (r : Fin 8) (t : Cell), snaky.image (placement r t) ⊆ M

lemma goal_mono {M M' : Finset Cell} (h : M ⊆ M') (hG : Goal M) : Goal M' := by
  obtain ⟨r, t, ht⟩ := hG
  exact ⟨r, t, ht.trans h⟩

def inverseRotation (r : Fin 8) : Fin 8 :=
  if r = 3 then 5 else if r = 5 then 3 else r

lemma orient_inverse (r : Fin 8) (p : Cell) : orient (inverseRotation r) (orient r p) = p := by
  fin_cases r <;> ext <;> simp [orient, inverseRotation]

lemma orient_inverse' (r : Fin 8) (p : Cell) : orient r (orient (inverseRotation r) p) = p := by
  fin_cases r <;> ext <;> simp [orient, inverseRotation]

def orientEquiv (r : Fin 8) : Cell ≃ Cell where
  toFun := orient r
  invFun := orient (inverseRotation r)
  left_inv := orient_inverse r
  right_inv := orient_inverse' r

def placementEquiv (r : Fin 8) (t : Cell) : Cell ≃ Cell :=
  (orientEquiv r).trans (Equiv.addRight t)

lemma placementEquiv_apply (r : Fin 8) (t p : Cell) :
    placementEquiv r t p = placement r t p := rfl

lemma orient_add (r : Fin 8) (p q : Cell) : orient r (p + q) = orient r p + orient r q := by
  fin_cases r <;> ext <;> simp [orient] <;> ring

def composeRotation (r s : Fin 8) : Fin 8 :=
  ![![0,1,2,3,4,5,6,7], ![1,0,3,2,5,4,7,6],
    ![2,5,0,7,6,1,4,3], ![3,4,1,6,7,0,5,2],
    ![4,3,6,1,0,7,2,5], ![5,2,7,0,1,6,3,4],
    ![6,7,4,5,2,3,0,1], ![7,6,5,4,3,2,1,0]] r s

lemma orient_compose (r s : Fin 8) (p : Cell) :
    orient r (orient s p) = orient (composeRotation r s) p := by
  fin_cases r <;> fin_cases s <;> ext <;> simp [orient, composeRotation]

lemma goal_map (r : Fin 8) (t : Cell) (M : Finset Cell) (hG : Goal M) :
    Goal (M.image (placementEquiv r t)) := by
  obtain ⟨s, u, hu⟩ := hG
  refine ⟨composeRotation r s, orient r u + t, ?_⟩
  intro x hx
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  have hm := hu (Finset.mem_image_of_mem (placement s u) hp)
  have hh := Finset.mem_image_of_mem (placementEquiv r t) hm
  simpa only [placementEquiv_apply, placement, orient_add, orient_compose, add_assoc] using hh

lemma baseRow_threat (i : Fin 6) :
    Threat Goal (baseRow i).A (baseRow i).H (baseRow i).height := by
  apply threat_leaf Goal (fun h hG => goal_mono h hG) origin (baseEnvelope i)
  exact ⟨0, -basePoint i, Finset.Subset.refl _⟩

lemma placeRow_threat (t : Term) (d : RowData)
    (hd : Threat Goal d.A d.H d.height) :
    Threat Goal (placeRow t d).A (placeRow t d).H (placeRow t d).height := by
  exact threat_map Goal (placementEquiv t.rotation t.shift) (goal_map t.rotation t.shift)
    d.A d.H d.height hd

lemma mem_unionA (ds : List RowData) (d : RowData) (hd : d ∈ ds) :
    d.A ⊆ unionA ds := by
  induction ds with
  | nil => simp at hd
  | cons e ds ih =>
      simp only [List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact Finset.subset_union_left
      · exact (ih hd).trans Finset.subset_union_right

lemma mem_unionH (ds : List RowData) (d : RowData) (hd : d ∈ ds) :
    d.H ⊆ unionH ds := by
  induction ds with
  | nil => simp at hd
  | cons e ds ih =>
      simp only [List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact Finset.subset_union_left
      · exact (ih hd).trans Finset.subset_union_right

lemma mem_foldInter (ds : List RowData) (S : Finset Cell) (b : Cell)
    (hS : b ∈ S) (hb : ∀ d ∈ ds, b ∈ d.H) :
    b ∈ (ds.map RowData.H).foldr (· ∩ ·) S := by
  induction ds with
  | nil => exact hS
  | cons d ds ih =>
      apply Finset.mem_inter.mpr
      exact ⟨hb d (by simp), ih (by intro e he; exact hb e (by simp [he]))⟩

lemma mem_commonH_of_all (ds : List RowData) (hne : ds ≠ []) (b : Cell)
    (hb : ∀ d ∈ ds, b ∈ d.H) : b ∈ commonH ds := by
  cases ds with
  | nil => exact False.elim (hne rfl)
  | cons e ds =>
      exact mem_foldInter ds e.H b (hb e (by simp)) (by
        intro d hd; exact hb d (by simp [hd]))

lemma height_le_foldMax (ds : List RowData) (d : RowData) (hd : d ∈ ds) :
    d.height ≤ (ds.map RowData.height).foldr max 0 := by
  induction ds with
  | nil => simp at hd
  | cons e ds ih =>
      simp only [List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact le_max_left _ _
      · exact (ih hd).trans (le_max_right _ _)

lemma forkRow_threat (ds : List RowData) (hne : ds ≠ [])
    (hs : ∀ d ∈ ds, Threat Goal d.A d.H d.height) :
    Threat Goal (forkRow ds).A (forkRow ds).H (forkRow ds).height := by
  change Threat Goal _ _ (1 + (ds.map RowData.height).foldr max 0)
  rw [Nat.add_comm 1]
  let td : RowData → ThreatData Cell := fun d => ⟨d.A, d.H, d.height⟩
  apply threat_fork Goal (fun h hG => goal_mono h hG) origin (ds.map td)
    (by intro h; exact hne (List.map_eq_nil_iff.mp h)) _
  · intro d hd
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
    exact hs e he
  · intro d hd
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
    exact height_le_foldMax ds e he
  · intro d hd x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
    have hm : x ∈ unionA ds ∪ commonH ds :=
      Finset.mem_union_left _ (mem_unionA ds e he hx)
    by_cases hx0 : x = origin
    · exact Finset.mem_insert.mpr (Or.inl hx0)
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hx0, hm⟩)
  · intro d hd x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
    exact Finset.mem_insert_of_mem (mem_unionH ds e he hx)
  · exact Finset.mem_insert_self _ _
  · intro b hb
    have hc : b ∈ commonH ds := mem_commonH_of_all ds hne b (by
      intro e he
      exact hb (td e) (List.mem_map.mpr ⟨e, he, rfl⟩))
    have hm : b ∈ unionA ds ∪ commonH ds := Finset.mem_union_right _ hc
    by_cases hb0 : b = origin
    · exact Finset.mem_insert.mpr (Or.inl hb0)
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hb0, hm⟩)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma entryAt_valid_of_TableValid (hv : TableValid) (i : ℕ) (hi : i < 616) (hil : 6 ≤ i) :
    (entryAt i).terms ≠ [] ∧ ∀ t ∈ (entryAt i).terms, t.child < i := by
  have hsize := hv.1
  have hk : i - 6 < table.size := by omega
  have hh := hv.2 (i - 6) hk
  have he : entryAt i = table[i - 6]?.getD emptyEntry := rfl
  rw [he]
  have hhidx := hh.1
  have hhne := hh.2.1
  have hhchild := hh.2.2
  refine ⟨hhne, ?_⟩
  intro t ht
  have hc := hhchild t ht
  rw [hhidx] at hc
  omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem rowAt_threat
    (hvalid : ∀ i, i < 616 → 6 ≤ i →
      (entryAt i).terms ≠ [] ∧ ∀ t ∈ (entryAt i).terms, t.child < i)
    (i : ℕ) (hib : i < 616) :
    Threat Goal (rowAt i).A (rowAt i).H (rowAt i).height := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      by_cases hi : i < 6
      · have he : rowAt i = baseRow ⟨i, hi⟩ := by
          rw [rowAt]
          exact dif_pos hi
        simp only [he]
        exact baseRow_threat ⟨i, hi⟩
      · have hv := hvalid i hib (by omega)
        let f : Term → RowData := fun t =>
          placeRow t (if _ : t.child < i then rowAt t.child else emptyRow)
        have he : rowAt i = forkRow ((entryAt i).terms.map f) := by
          rw [rowAt]
          exact dif_neg hi
        have hne : (entryAt i).terms.map f ≠ [] := by
          intro hempty
          exact hv.1 (List.map_eq_nil_iff.mp hempty)
        have hs : ∀ d ∈ (entryAt i).terms.map f,
            Threat Goal d.A d.H d.height := by
          intro d hd
          obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hd
          change Threat Goal (placeRow t _).A (placeRow t _).H (placeRow t _).height
          apply placeRow_threat
          have hti := hv.2 t ht
          simp only [dif_pos hti]
          exact ih t.child hti (by omega)
        generalize hds : (entryAt i).terms.map f = ds at he hne hs
        have hf := forkRow_threat ds hne hs
        rw [← he] at hf
        exact hf

end StrategyBridge

end OAI.SnakyCertificate
