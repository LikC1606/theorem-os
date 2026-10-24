import Mathlib
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace LiuBangXiangYu

/-- The multiset of piece lengths obtained by cutting `[0,1]` at the points of a
finite set `S ⊆ (0,1)`.  We sort `S` ascending, prepend `0` and append `1`, and
take consecutive differences.  The result is a list of `|S| + 1` positive reals
summing to `1` (when `S ⊆ (0,1)`). -/
noncomputable def pieceLengths (S : Finset ℝ) : List ℝ :=
  let l : List ℝ := (0 : ℝ) :: (S.sort (· ≤ ·)) ++ [1]
  List.zipWith (fun a b => b - a) l l.tail

/-- The sum of the entries of a list `L` at the (0-indexed) even positions, after
sorting `L` in non-increasing order.  These are the entries in the `1`st, `3`rd,
`5`th, … positions of the sorted (decreasing) list, i.e. the pieces claimed by
the first mover under the greedy claiming rule. -/
noncomputable def firstPlayerShare (L : List ℝ) : ℝ :=
  let sorted := L.mergeSort (· ≥ ·)
  ((sorted.zipIdx.filter (fun p => p.2 % 2 = 0)).map (fun p => p.1)).sum

/-- `L(A,B)`: Liu Bang's total length, given Liu Bang's marks `A` and Xiang Yu's
marks `B`. -/
noncomputable def L (A B : Finset ℝ) : ℝ :=
  firstPlayerShare (pieceLengths (A ∪ B))

/-- The set of admissible markings for a player: a finite subset of `(0,1)` of
size at most `n`.  We encode it as a `Finset ℝ` subject to the side conditions. -/
def AdmissibleMark (n : ℕ) (X : Finset ℝ) : Prop :=
  (↑X ⊆ Set.Ioo (0 : ℝ) 1) ∧ X.card ≤ n

/-- The value Liu Bang can guarantee.

`V n` is the supremum over Liu Bang's admissible markings `A` of the infimum,
over Xiang Yu's admissible markings `B` disjoint from `A`, of `L A B`. -/
noncomputable def V (n : ℕ) : ℝ :=
  ⨆ A : {A : Finset ℝ // AdmissibleMark n A},
    ⨅ B : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B}, L A.1 B.1

/-- The claimed answer value `V(n) = 2^n / (2^(n+1) - 1)`. -/
noncomputable def answer (n : ℕ) : ℝ := (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1)

/-! ## Correctness statements for the definitions

These pin down that the encoded definitions behave as intended. -/

lemma sparseEdgeSigning
    (n : ℕ) (edges : List (Fin (n + 1) × Fin (n + 1)))
    (hlen : edges.length ≤ n) :
    ∃ s : Fin (n + 1) → ℤ,
      (∃ i, s i ≠ 0) ∧
      (∀ i, s i = -1 ∨ s i = 0 ∨ s i = 1) ∧
      ∀ e ∈ edges, s e.1 + s e.2 = 0 := by
  let T : (Fin (n + 1) → ℚ) →ₗ[ℚ] (Fin edges.length → ℚ) :=
    { toFun := fun f j => f (edges.get j).1 + f (edges.get j).2
      map_add' := by
        intro f g
        funext j
        dsimp
        ring
      map_smul' := by
        intro q f
        funext j
        dsimp
        ring }
  have hdim :
      Module.finrank ℚ (Fin edges.length → ℚ) <
        Module.finrank ℚ (Fin (n + 1) → ℚ) := by
    simp only [Module.finrank_pi, Fintype.card_fin]
    omega
  have hker : LinearMap.ker T ≠ ⊥ :=
    T.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨f, hfker, hfne⟩ := (LinearMap.ker T).ne_bot_iff.mp hker
  have hfzero : T f = 0 := LinearMap.mem_ker.mp hfker
  have hcoordinate : ∃ i, f i ≠ 0 := by
    by_contra h
    apply hfne
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  let s : Fin (n + 1) → ℤ := fun i =>
    if 0 < f i then 1 else if f i < 0 then -1 else 0
  refine ⟨s, ?_, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hcoordinate
    refine ⟨i, ?_⟩
    by_cases hpos : 0 < f i
    · simp [s, hpos]
    · have hneg : f i < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hi
      simp [s, hpos, hneg]
  · intro i
    dsimp [s]
    split_ifs <;> simp
  · have hpair (j : Fin edges.length) :
        f (edges.get j).1 + f (edges.get j).2 = 0 := by
      simpa [T] using congrFun hfzero j
    have sign_cancel (a b : ℚ) (hab : a + b = 0) :
        (if 0 < a then (1 : ℤ) else if a < 0 then -1 else 0) +
          (if 0 < b then (1 : ℤ) else if b < 0 then -1 else 0) = 0 := by
      have hb : b = -a := by linarith
      subst b
      rcases lt_trichotomy a 0 with ha | rfl | ha
      · have hnotpos : ¬ 0 < a := not_lt_of_ge ha.le
        have hnegpos : 0 < -a := neg_pos.mpr ha
        simp [hnotpos, ha, hnegpos]
      · norm_num
      · have hnegnotpos : ¬ 0 < -a := not_lt_of_ge (neg_nonpos.mpr ha.le)
        have hnegneg : -a < 0 := neg_lt_zero.mpr ha
        simp [ha, hnegnotpos, hnegneg]
    intro e he
    obtain ⟨j, rfl⟩ := List.get_of_mem he
    exact sign_cancel _ _ (hpair j)
theorem pieceLengths_nonneg (S : Finset ℝ)
    (hS : (↑S : Set ℝ) ⊆ Set.Ioo (0 : ℝ) 1) (x : ℝ)
    (hx : x ∈ pieceLengths S) : 0 ≤ x := by
  have adjacent_nonneg :
      ∀ (l : List ℝ), l.Pairwise (· ≤ ·) →
        ∀ y ∈ List.zipWith (fun a b => b - a) l l.tail, 0 ≤ y := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
        intro hl y hy
        cases l with
        | nil => simp at hy
        | cons b l =>
            simp only [List.tail_cons, List.zipWith_cons_cons, List.mem_cons] at hy
            rcases hy with rfl | hy
            · exact sub_nonneg.mpr
                ((List.pairwise_cons_cons_iff_of_trans.mp hl).1)
            · exact ih (List.pairwise_cons_cons_iff_of_trans.mp hl).2 y hy
  have hl : ((0 : ℝ) :: S.sort (· ≤ ·) ++ [1]).Pairwise (· ≤ ·) := by
    rw [List.pairwise_append]
    refine ⟨?_, List.pairwise_singleton _ _, ?_⟩
    · rw [List.pairwise_cons]
      refine ⟨?_, S.pairwise_sort (· ≤ ·)⟩
      intro a ha
      exact (hS (by simpa using ha)).1.le
    · intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst b
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · norm_num
      · exact (hS (by simpa using ha)).2.le
  exact adjacent_nonneg _ hl x (by simpa [pieceLengths] using hx)
theorem pieceLengths_pos
    (S : Finset ℝ) (hS : (↑S : Set ℝ) ⊆ Set.Ioo (0 : ℝ) 1) (x : ℝ)
    (hx : x ∈ pieceLengths S) : 0 < x := by
  have adjacent_pos :
      ∀ (l : List ℝ), l.Pairwise (· ≤ ·) → l.Nodup →
        ∀ y ∈ List.zipWith (fun a b => b - a) l l.tail, 0 < y := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
        intro hl hnodup y hy
        cases l with
        | nil => simp at hy
        | cons b l =>
            simp only [List.tail_cons, List.zipWith_cons_cons, List.mem_cons] at hy
            rcases hy with rfl | hy
            · apply sub_pos.mpr
              have hab := (List.pairwise_cons_cons_iff_of_trans.mp hl).1
              exact lt_of_le_of_ne hab (by
                intro heq
                apply (List.nodup_cons.mp hnodup).1
                simp [heq])
            · exact ih (List.pairwise_cons_cons_iff_of_trans.mp hl).2
                (List.nodup_cons.mp hnodup).2 y hy
  have hl : ((0 : ℝ) :: S.sort (· ≤ ·) ++ [1]).Pairwise (· ≤ ·) := by
    rw [List.pairwise_append]
    refine ⟨?_, List.pairwise_singleton _ _, ?_⟩
    · rw [List.pairwise_cons]
      refine ⟨?_, S.pairwise_sort (· ≤ ·)⟩
      intro a ha
      exact (hS (by simpa using ha)).1.le
    · intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst b
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · norm_num
      · exact (hS (by simpa using ha)).2.le
  have hzero : (0 : ℝ) ∉ S.sort (· ≤ ·) := by
    intro h
    exact (hS (by simpa using h)).1.ne' rfl
  have hone : (1 : ℝ) ∉ S.sort (· ≤ ·) := by
    intro h
    exact (hS (by simpa using h)).2.ne rfl
  have hnodup : ((0 : ℝ) :: S.sort (· ≤ ·) ++ [1]).Nodup := by
    rw [List.nodup_append]
    refine ⟨?_, List.nodup_singleton 1, ?_⟩
    · rw [List.nodup_cons]
      exact ⟨hzero, S.sort_nodup (· ≤ ·)⟩
    · intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst b
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · norm_num
      · exact fun h => hone (h ▸ ha)
  exact adjacent_pos _ hl hnodup x (by simpa [pieceLengths] using hx)
theorem firstPlayerShare_mem_Icc (xs : List ℝ)
    (hxs : ∀ x : ℝ, x ∈ xs → 0 ≤ x) (hsum : xs.sum = 1) :
    firstPlayerShare xs ∈ Set.Icc (0 : ℝ) 1 := by
  let sorted := xs.mergeSort (· ≥ ·)
  let chosen :=
    ((sorted.zipIdx.filter (fun p => p.2 % 2 = 0)).map (fun p => p.1))
  have hperm : sorted.Perm xs := by
    exact List.mergeSort_perm xs (· ≥ ·)
  have hsorted_nonneg : ∀ x ∈ sorted, 0 ≤ x := by
    intro x hx
    exact hxs x (hperm.mem_iff.mp hx)
  have hchosen_sub : chosen.Sublist sorted := by
    have hfilter :
        (sorted.zipIdx.filter (fun p => p.2 % 2 = 0)).Sublist sorted.zipIdx :=
      List.filter_sublist
    have hmap := hfilter.map (fun p => p.1)
    simpa only [chosen, List.zipIdx_map_fst] using hmap
  change 0 ≤ chosen.sum ∧ chosen.sum ≤ 1
  constructor
  · exact List.sum_nonneg fun x hx => hsorted_nonneg x (hchosen_sub.subset hx)
  · have hle := hchosen_sub.sum_le_sum hsorted_nonneg
    rw [hperm.sum_eq, hsum] at hle
    exact hle
theorem firstPlayerShare_eq_of_perm (xs ys : List ℝ) (h : xs.Perm ys) :
    firstPlayerShare xs = firstPlayerShare ys := by
  unfold firstPlayerShare
  have hsorted : xs.mergeSort (· ≥ ·) = ys.mergeSort (· ≥ ·) :=
    ((List.mergeSort_perm xs (· ≥ ·)).trans
      (h.trans (List.mergeSort_perm ys (· ≥ ·)).symm)).eq_of_pairwise'
        (List.pairwise_mergeSort' (· ≥ ·) xs)
        (List.pairwise_mergeSort' (· ≥ ·) ys)
  rw [hsorted]
lemma refinementBlocks_split
    (blocks : List (List ℝ))
    (hne : ∀ block ∈ blocks, block ≠ [])
    (pre post : List ℝ) (x u v : ℝ)
    (hflat : blocks.flatten = pre ++ x :: post)
    (hsum : u + v = x) :
    ∃ blocks' : List (List ℝ),
      blocks'.map List.sum = blocks.map List.sum ∧
      blocks'.flatten = pre ++ u :: v :: post ∧
      blocks'.length = blocks.length ∧
      (∀ block ∈ blocks', block ≠ []) := by
  induction blocks generalizing pre post x u v with
  | nil => simp at hflat
  | cons block blocks ih =>
      have hblock : block ≠ [] := hne block (by simp)
      have htail : ∀ tail ∈ blocks, tail ≠ [] := by
        intro tail hmem
        exact hne tail (by simp [hmem])
      change block ++ blocks.flatten = pre ++ x :: post at hflat
      rcases (List.append_eq_append_iff.mp hflat) with
        ⟨more, hpre, hrest⟩ | ⟨more, hblockeq, hrest⟩
      · rcases ih htail more post x u v hrest hsum with
          ⟨blocks', hmaps, hflats, hlens, hnes⟩
        refine ⟨block :: blocks', ?_, ?_, ?_, ?_⟩
        · simp [hmaps]
        · simp only [List.flatten_cons, hflats, hpre, List.cons_append]
          simp [List.append_assoc]
        · simp [hlens]
        · intro tail hmem
          rcases List.mem_cons.mp hmem with rfl | hmem
          · exact hblock
          · exact hnes tail hmem
      · cases more with
        | nil =>
            simp only [List.append_nil] at hblockeq
            subst block
            rcases ih htail [] post x u v (by simpa using hrest.symm) hsum with
              ⟨blocks', hmaps, hflats, hlens, hnes⟩
            refine ⟨pre :: blocks', ?_, ?_, ?_, ?_⟩
            · simp [hmaps]
            · simpa using congrArg (pre ++ ·) hflats
            · simp [hlens]
            · intro tail hmem
              rcases List.mem_cons.mp hmem with rfl | hmem
              · exact hblock
              · exact hnes tail hmem
        | cons y ys =>
            simp only [List.cons_append, List.cons.injEq] at hrest
            rcases hrest with ⟨rfl, rfl⟩
            let block' : List ℝ := pre ++ u :: v :: ys
            refine ⟨block' :: blocks, ?_, ?_, ?_, ?_⟩
            · simp only [List.map_cons, List.cons.injEq]
              constructor
              · simp only [block', List.sum_append, List.sum_cons]
                rw [hblockeq, List.sum_append, List.sum_cons]
                linarith
              · trivial
            · simp only [List.flatten_cons, block']
              simp [List.append_assoc]
            · rfl
            · intro tail hmem
              rcases List.mem_cons.mp hmem with rfl | hmem
              · simp [block']
              · exact htail tail hmem
def cutDiffs (a b : ℝ) (xs : List ℝ) : List ℝ :=
  List.zipWith (fun x y => y - x) (a :: xs ++ [b]) (a :: xs ++ [b]).tail
lemma cutDiffs_nil (a b : ℝ) :
    cutDiffs a b [] = [b - a] := by
  simp [cutDiffs]
lemma cutDiffs_cons (a b x : ℝ) (xs : List ℝ) :
    cutDiffs a b (x :: xs) = (x - a) :: cutDiffs x b xs := by
  simp [cutDiffs]
lemma cutDiffs_orderedInsert_split (a z b : ℝ) (xs : List ℝ) :
    ∃ pre post : List ℝ, ∃ x u v : ℝ,
      cutDiffs a z xs = pre ++ x :: post ∧
      cutDiffs a z (xs.orderedInsert (· ≤ ·) b) =
        pre ++ u :: v :: post ∧
      u + v = x := by
  induction xs generalizing a with
  | nil =>
      refine ⟨[], [], z - a, b - a, z - b, ?_, ?_, ?_⟩
      · simp [cutDiffs]
      · simp [cutDiffs]
      · linarith
  | cons y ys ih =>
      by_cases hby : b ≤ y
      · refine ⟨[], cutDiffs y z ys, y - a, b - a, y - b, ?_, ?_, ?_⟩
        · simp [cutDiffs_cons]
        · rw [List.orderedInsert_cons_of_le _ ys hby]
          simp [cutDiffs_cons]
        · linarith
      · rcases ih y with ⟨pre, post, x, u, v, hold, hnew, huv⟩
        refine ⟨(y - a) :: pre, post, x, u, v, ?_, ?_, huv⟩
        · rw [cutDiffs_cons, hold]
          rfl
        · rw [List.orderedInsert_of_not_le _ ys hby, cutDiffs_cons, hnew]
          rfl
lemma pieceLengths_insert_split
    (S : Finset ℝ) (b : ℝ)
    (hS : (↑S : Set ℝ) ⊆ Set.Ioo (0 : ℝ) 1)
    (hb : b ∈ Set.Ioo (0 : ℝ) 1) (hnot : b ∉ S) :
    ∃ pre post : List ℝ, ∃ x u v : ℝ,
      pieceLengths S = pre ++ x :: post ∧
      pieceLengths (insert b S) = pre ++ u :: v :: post ∧
      u + v = x := by
  let xs := S.sort (· ≤ ·)
  have hbxs : b ∉ xs := by
    simpa only [xs, Finset.mem_sort] using hnot
  have hconsNodup : (b :: xs).Nodup := by
    exact List.nodup_cons.mpr ⟨hbxs, S.sort_nodup (· ≤ ·)⟩
  have horderedNodup : (xs.orderedInsert (· ≤ ·) b).Nodup := by
    exact ((List.perm_orderedInsert (· ≤ ·) b xs).nodup_iff).2 hconsNodup
  have horderedPairwise :
      (xs.orderedInsert (· ≤ ·) b).Pairwise (· ≤ ·) := by
    exact (S.pairwise_sort (· ≤ ·)).orderedInsert b xs
  have htoFinset :
      (xs.orderedInsert (· ≤ ·) b).toFinset = insert b S := by
    ext y
    simp [xs, List.mem_orderedInsert]
  have hsort :
      (insert b S).sort (· ≤ ·) = xs.orderedInsert (· ≤ ·) b := by
    rw [← htoFinset]
    exact (List.toFinset_sort (· ≤ ·) horderedNodup).2 horderedPairwise
  change ∃ pre post : List ℝ, ∃ x u v : ℝ,
    cutDiffs 0 1 (S.sort (· ≤ ·)) = pre ++ x :: post ∧
    cutDiffs 0 1 ((insert b S).sort (· ≤ ·)) =
      pre ++ u :: v :: post ∧
    u + v = x
  rw [hsort]
  exact cutDiffs_orderedInsert_split 0 1 b xs
lemma pieceLengths_union_refines
    (A B : Finset ℝ)
    (hA : (↑A : Set ℝ) ⊆ Set.Ioo (0 : ℝ) 1)
    (hB : (↑B : Set ℝ) ⊆ Set.Ioo (0 : ℝ) 1)
    (hdisj : Disjoint A B) :
    ∃ blocks : List (List ℝ),
      blocks.map List.sum = pieceLengths A ∧
      blocks.flatten.Perm (pieceLengths (A ∪ B)) ∧
      blocks.flatten.length ≤ blocks.length + B.card ∧
      ∀ x : ℝ, x ∈ blocks.flatten → 0 ≤ x := by
  have hsingleton_sums : ∀ xs : List ℝ,
      (xs.map (fun x => [x])).map List.sum = xs := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
        simp only [List.map_cons]
        rw [show [x].sum = x by simp, ih]
  have hsingleton_flatten : ∀ xs : List ℝ,
      (xs.map (fun x => [x])).flatten = xs := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
        rw [List.map_cons, List.flatten_cons, ih]
        rfl
  have hordered :
      ∃ blocks : List (List ℝ),
        blocks.map List.sum = pieceLengths A ∧
        blocks.flatten = pieceLengths (A ∪ B) ∧
        blocks.length = (pieceLengths A).length ∧
        ∀ block ∈ blocks, block ≠ [] := by
    induction B using Finset.induction_on with
    | empty =>
        refine ⟨(pieceLengths A).map (fun x => [x]), ?_, ?_, ?_, ?_⟩
        · exact hsingleton_sums (pieceLengths A)
        · simpa only [Finset.union_empty] using
            hsingleton_flatten (pieceLengths A)
        · simp
        · simp
    | @insert b B hb ih =>
        have hbIoo : b ∈ Set.Ioo (0 : ℝ) 1 := hB (by simp)
        have hB' : (↑B : Set ℝ) ⊆ Set.Ioo (0 : ℝ) 1 := by
          intro y hy
          exact hB (by simp [hy])
        have hdisj' : Disjoint A B := by
          rw [Finset.disjoint_left] at hdisj ⊢
          intro a haA haB
          exact hdisj haA (by simp [haB])
        have hbA : b ∉ A := by
          intro hbA
          exact (Finset.disjoint_left.mp hdisj) hbA (by simp)
        have hbAB : b ∉ A ∪ B := by simp [hbA, hb]
        have hAB : (↑(A ∪ B) : Set ℝ) ⊆ Set.Ioo (0 : ℝ) 1 := by
          intro y hy
          rcases Finset.mem_union.mp hy with hy | hy
          · exact hA (by simpa using hy)
          · exact hB' (by simpa using hy)
        rcases ih hB' hdisj' with ⟨blocks, hmap, hflat, hlen, hne⟩
        rcases pieceLengths_insert_split (A ∪ B) b hAB hbIoo hbAB with
          ⟨pre, post, x, u, v, hold, hnew, huv⟩
        rcases refinementBlocks_split blocks hne pre post x u v
            (hflat.trans hold) huv with
          ⟨blocks', hmap', hflat', hlen', hne'⟩
        refine ⟨blocks', hmap'.trans hmap, ?_, hlen'.trans hlen, hne'⟩
        calc
          blocks'.flatten = pre ++ u :: v :: post := hflat'
          _ = pieceLengths (insert b (A ∪ B)) := hnew.symm
          _ = pieceLengths (A ∪ insert b B) := by
            rw [Finset.union_insert]
  rcases hordered with ⟨blocks, hmap, hflat, hlen, hne⟩
  have hAB : (↑(A ∪ B) : Set ℝ) ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact hA (by simpa using hy)
    · exact hB (by simpa using hy)
  refine ⟨blocks, hmap, ?_, ?_, ?_⟩
  · rw [hflat]
  · rw [hflat, hlen]
    simp [pieceLengths, Finset.card_union_of_disjoint hdisj, Nat.add_comm,
      Nat.add_left_comm]
  · intro x hx
    apply pieceLengths_nonneg (A ∪ B) hAB x
    rw [← hflat]
    exact hx
lemma cutDiffs_append_last (a b z : ℝ) (xs : List ℝ) :
    cutDiffs a b (xs ++ [z]) = cutDiffs a z xs ++ [b - z] := by
  induction xs generalizing a with
  | nil => simp [cutDiffs]
  | cons x xs ih => simp [cutDiffs_cons, ih]
lemma cutDiffs_map_range (g : ℕ → ℝ) (n : ℕ) :
    cutDiffs (g 0) (g (n + 1))
        ((List.range n).map (fun i => g (i + 1))) =
      (List.range (n + 1)).map (fun i => g (i + 1) - g i) := by
  induction n generalizing g with
  | zero => simp [cutDiffs]
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.map_singleton,
        cutDiffs_append_last, ih]
      rw [List.range_succ, List.map_append, List.map_singleton]
      rw [show List.range (n + 2) = List.range n ++ [n, n + 1] by
        simp [List.range_succ]]
      simp [Nat.add_assoc]
noncomputable def geometricEndpoint (n k : ℕ) : ℝ :=
  1 - (((2 : ℝ) ^ (n + 1 - k) - 1) / ((2 : ℝ) ^ (n + 1) - 1))
noncomputable def geometricMarkList (n : ℕ) : List ℝ :=
  (List.range n).map (fun i => geometricEndpoint n (i + 1))
noncomputable def geometricMarkSet (n : ℕ) : Finset ℝ :=
  (geometricMarkList n).toFinset
lemma geometricDen_pos (n : ℕ) : 0 < (2 : ℝ) ^ (n + 1) - 1 := by
  have hpow : (1 : ℝ) < (2 : ℝ) ^ (n + 1) := by
    simpa using
      (pow_lt_pow_right₀ (a := (2 : ℝ)) (by norm_num) (Nat.zero_lt_succ n))
  linarith
lemma geometricEndpoint_zero (n : ℕ) : geometricEndpoint n 0 = 0 := by
  unfold geometricEndpoint
  simp only [Nat.sub_zero]
  rw [div_self (ne_of_gt (geometricDen_pos n))]
  ring
lemma geometricEndpoint_last (n : ℕ) : geometricEndpoint n (n + 1) = 1 := by
  simp [geometricEndpoint]
lemma geometricEndpoint_diff (n i : ℕ) (hi : i < n + 1) :
    geometricEndpoint n (i + 1) - geometricEndpoint n i =
      (2 : ℝ) ^ (n - i) / ((2 : ℝ) ^ (n + 1) - 1) := by
  have hnext : n + 1 - (i + 1) = n - i := by omega
  have hcur : n + 1 - i = (n - i) + 1 := by omega
  unfold geometricEndpoint
  rw [hnext, hcur, pow_succ]
  ring
lemma geometricEndpoint_strict (n i j : ℕ) (hij : i < j) (hj : j < n) :
    geometricEndpoint n (i + 1) < geometricEndpoint n (j + 1) := by
  have hi : i < n := hij.trans hj
  have hiExp : n + 1 - (i + 1) = n - i := by omega
  have hjExp : n + 1 - (j + 1) = n - j := by omega
  have hpow : (2 : ℝ) ^ (n - j) < (2 : ℝ) ^ (n - i) := by
    apply pow_lt_pow_right₀ (by norm_num)
    omega
  have hquot :
      ((2 : ℝ) ^ (n - j) - 1) / ((2 : ℝ) ^ (n + 1) - 1) <
        ((2 : ℝ) ^ (n - i) - 1) / ((2 : ℝ) ^ (n + 1) - 1) := by
    apply (div_lt_div_iff_of_pos_right (geometricDen_pos n)).2
    linarith
  unfold geometricEndpoint
  rw [hiExp, hjExp]
  linarith
lemma geometricMarkList_pairwise (n : ℕ) :
    (geometricMarkList n).Pairwise (· < ·) := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  simp only [geometricMarkList, List.length_map, List.length_range] at hi hj
  simp only [geometricMarkList, List.getElem_map, List.getElem_range]
  exact geometricEndpoint_strict n i j hij hj
lemma geometricMarkSet_spec (n : ℕ) :
    AdmissibleMark n (geometricMarkSet n) ∧
      pieceLengths (geometricMarkSet n) =
        (List.range (n + 1)).map (fun i =>
          (1 / ((2 : ℝ) ^ (n + 1) - 1)) * (2 : ℝ) ^ (n - i)) := by
  have hpair := geometricMarkList_pairwise n
  have hsort : (geometricMarkSet n).sort (· ≤ ·) = geometricMarkList n := by
    exact (List.toFinset_sort (· ≤ ·) hpair.nodup).2
      (hpair.imp fun h => h.le)
  constructor
  · constructor
    · intro x hx
      have hxlist : x ∈ geometricMarkList n := by
        simpa [geometricMarkSet] using hx
      simp only [geometricMarkList, List.mem_map] at hxlist
      rcases hxlist with ⟨i, hi, rfl⟩
      have hi : i < n := by simpa using hi
      have hiExp : 0 < n - i := by omega
      have hsmallExp : n - i < n + 1 := by omega
      have hsmall : (2 : ℝ) ^ (n - i) < (2 : ℝ) ^ (n + 1) :=
        pow_lt_pow_right₀ (by norm_num) hsmallExp
      have hlarge : (1 : ℝ) < (2 : ℝ) ^ (n - i) := by
        simpa using (pow_lt_pow_right₀ (a := (2 : ℝ)) (by norm_num) hiExp)
      have hindex : n + 1 - (i + 1) = n - i := by omega
      unfold geometricEndpoint
      rw [hindex]
      constructor
      · apply sub_pos.mpr
        apply (div_lt_one (geometricDen_pos n)).2
        linarith
      · exact sub_lt_self 1
          (div_pos (sub_pos.mpr hlarge) (geometricDen_pos n))
    · exact (List.toFinset_card_le (geometricMarkList n)).trans_eq (by
        simp [geometricMarkList])
  · change cutDiffs 0 1 ((geometricMarkSet n).sort (· ≤ ·)) = _
    rw [hsort, geometricMarkList]
    have hdiffs := cutDiffs_map_range (geometricEndpoint n) n
    rw [geometricEndpoint_zero, geometricEndpoint_last] at hdiffs
    rw [hdiffs]
    apply List.map_congr_left
    intro i hi
    rw [geometricEndpoint_diff n i (by simpa using hi)]
    ring
lemma geometricPrefixSum_formula (n k : ℕ) (hk : k < n) :
    (∑ j ∈ Finset.range (k + 1), (2 : ℝ) ^ (n - j)) =
      (2 : ℝ) ^ (n + 1) - (2 : ℝ) ^ (n - k) := by
  induction k with
  | zero =>
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        Nat.sub_zero]
      rw [pow_succ]
      ring
  | succ k ih =>
      rw [Finset.sum_range_succ, ih (by omega)]
      rw [show n - k = (n - (k + 1)) + 1 by omega, pow_succ]
      ring
lemma geometricPrefixSum_eq_endpoint (n k : ℕ) (hk : k < n) :
    (∑ j ∈ Finset.range (k + 1), (2 : ℝ) ^ (n - j)) /
        ((2 : ℝ) ^ (n + 1) - 1) =
      geometricEndpoint n (k + 1) := by
  rw [geometricPrefixSum_formula n k hk]
  unfold geometricEndpoint
  rw [show n + 1 - (k + 1) = n - k by omega]
  field_simp [ne_of_gt (geometricDen_pos n)]
  ring
lemma geometricPrefixMarkSet_eq (n : ℕ) :
    (Finset.range n).image (fun k =>
        (∑ j ∈ Finset.range (k + 1), (2 : ℝ) ^ (n - j)) /
          ((2 : ℝ) ^ (n + 1) - 1)) =
      geometricMarkSet n := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨k, hk, hkx⟩
    rw [geometricMarkSet, List.mem_toFinset]
    simp only [geometricMarkList, List.mem_map]
    refine ⟨k, by simpa using hk, ?_⟩
    exact (geometricPrefixSum_eq_endpoint n k (by simpa using hk)).symm.trans hkx
  · intro hx
    rw [geometricMarkSet, List.mem_toFinset] at hx
    simp only [geometricMarkList, List.mem_map] at hx
    rcases hx with ⟨k, hk, hkx⟩
    have hkn : k < n := by simpa using hk
    apply Finset.mem_image.mpr
    refine ⟨k, Finset.mem_range.mpr hkn, ?_⟩
    exact (geometricPrefixSum_eq_endpoint n k hkn).trans hkx
lemma geometricMarks_spec (n : ℕ) (hn : 0 < n) :
    let d : ℝ := (2 : ℝ) ^ (n + 1) - 1
    let A : Finset ℝ := (Finset.range n).image (fun k =>
      (∑ j ∈ Finset.range (k + 1), (2 : ℝ) ^ (n - j)) / d)
    AdmissibleMark n A ∧
      pieceLengths A = (List.range (n + 1)).map
        (fun i => (1 / d) * (2 : ℝ) ^ (n - i)) := by
  dsimp only
  rw [geometricPrefixMarkSet_eq n]
  exact geometricMarkSet_spec n
lemma closeSubsetSums :
    ∀ (m : ℕ), 0 < m → ∀ (x : Fin m → ℝ),
      (∀ i, 0 ≤ x i) → (∑ i, x i) = 1 →
      ∃ U V : Finset (Fin m), U ≠ V ∧
        |(∑ i ∈ U, x i) - ∑ i ∈ V, x i| ≤
          1 / ((2 : ℝ) ^ m - 1) := by
  intro m hm x hx hsum
  let N : ℕ := 2 ^ m - 1
  have hpow : 1 < 2 ^ m := one_lt_pow₀ (by omega) hm.ne'
  have hN : 0 < N := by
    dsimp [N]
    omega
  let subsetSum : Finset (Fin m) → ℝ := fun U => ∑ i ∈ U, x i
  have hsubset (U : Finset (Fin m)) :
      0 ≤ subsetSum U ∧ subsetSum U ≤ 1 := by
    constructor
    · exact Finset.sum_nonneg fun i _ => hx i
    · rw [← hsum]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U)
        (fun i _ _ => hx i)
  let bin : Finset (Fin m) → Fin N := fun U =>
    ⟨min ⌊(N : ℝ) * subsetSum U⌋₊ (N - 1), by
      exact lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hN (by omega))⟩
  have hcard : Fintype.card (Fin N) < Fintype.card (Finset (Fin m)) := by
    simp only [Fintype.card_fin, Fintype.card_finset]
    dsimp [N]
    omega
  obtain ⟨U, V, hUV, hbin⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt bin hcard
  refine ⟨U, V, hUV, ?_⟩
  have hU := hsubset U
  have hV := hsubset V
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  change |subsetSum U - subsetSum V| ≤ 1 / ((2 : ℝ) ^ m - 1)
  have hNcast : (N : ℝ) = (2 : ℝ) ^ m - 1 := by
    dsimp [N]
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [← hNcast]
  have hbinval :
      min ⌊(N : ℝ) * subsetSum U⌋₊ (N - 1) =
        min ⌊(N : ℝ) * subsetSum V⌋₊ (N - 1) := by
    exact congrArg Fin.val hbin
  by_cases hUone : subsetSum U = 1
  · by_cases hVone : subsetSum V = 1
    · simp [hUone, hVone]
    · have hcodeU :
          min ⌊(N : ℝ) * subsetSum U⌋₊ (N - 1) = N - 1 := by
        simp [hUone, Nat.floor_natCast]
      have hfloorV : N - 1 ≤ ⌊(N : ℝ) * subsetSum V⌋₊ := by
        rw [hcodeU] at hbinval
        rw [hbinval]
        exact min_le_left _ _
      have hscaledV_nonneg : 0 ≤ (N : ℝ) * subsetSum V :=
        mul_nonneg hNr.le hV.1
      have hscaledV : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) * subsetSum V :=
        (Nat.le_floor_iff hscaledV_nonneg).mp hfloorV
      have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      rw [hUone, abs_of_nonneg (sub_nonneg.mpr hV.2)]
      apply (le_div_iff₀ hNr).2
      rw [hcast] at hscaledV
      nlinarith
  · by_cases hVone : subsetSum V = 1
    · have hcodeV :
          min ⌊(N : ℝ) * subsetSum V⌋₊ (N - 1) = N - 1 := by
        simp [hVone, Nat.floor_natCast]
      have hfloorU : N - 1 ≤ ⌊(N : ℝ) * subsetSum U⌋₊ := by
        rw [hcodeV] at hbinval
        rw [← hbinval]
        exact min_le_left _ _
      have hscaledU_nonneg : 0 ≤ (N : ℝ) * subsetSum U :=
        mul_nonneg hNr.le hU.1
      have hscaledU : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) * subsetSum U :=
        (Nat.le_floor_iff hscaledU_nonneg).mp hfloorU
      have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      rw [hVone, abs_of_nonpos (sub_nonpos.mpr hU.2)]
      apply (le_div_iff₀ hNr).2
      rw [hcast] at hscaledU
      nlinarith
    · have hUlt : subsetSum U < 1 := lt_of_le_of_ne hU.2 hUone
      have hVlt : subsetSum V < 1 := lt_of_le_of_ne hV.2 hVone
      have hscaledU_nonneg : 0 ≤ (N : ℝ) * subsetSum U :=
        mul_nonneg hNr.le hU.1
      have hscaledV_nonneg : 0 ≤ (N : ℝ) * subsetSum V :=
        mul_nonneg hNr.le hV.1
      have hfloorUlt : ⌊(N : ℝ) * subsetSum U⌋₊ < N := by
        rw [Nat.floor_lt hscaledU_nonneg]
        nlinarith
      have hfloorVlt : ⌊(N : ℝ) * subsetSum V⌋₊ < N := by
        rw [Nat.floor_lt hscaledV_nonneg]
        nlinarith
      have hfloors :
          ⌊(N : ℝ) * subsetSum U⌋₊ =
            ⌊(N : ℝ) * subsetSum V⌋₊ := by
        rw [min_eq_left (by omega), min_eq_left (by omega)] at hbinval
        exact hbinval
      have hUlower :
          (⌊(N : ℝ) * subsetSum U⌋₊ : ℝ) ≤
            (N : ℝ) * subsetSum U := Nat.floor_le hscaledU_nonneg
      have hUupper :
          (N : ℝ) * subsetSum U <
            (⌊(N : ℝ) * subsetSum U⌋₊ : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      have hVlower :
          (⌊(N : ℝ) * subsetSum V⌋₊ : ℝ) ≤
            (N : ℝ) * subsetSum V := Nat.floor_le hscaledV_nonneg
      have hVupper :
          (N : ℝ) * subsetSum V <
            (⌊(N : ℝ) * subsetSum V⌋₊ : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      have hscaled :
          |(N : ℝ) * subsetSum U - (N : ℝ) * subsetSum V| ≤ 1 := by
        rw [abs_le]
        constructor <;> rw [hfloors] at hUlower hUupper <;> linarith
      have hscaled' :
          (N : ℝ) * |subsetSum U - subsetSum V| ≤ 1 := by
        rw [← abs_of_nonneg hNr.le, ← abs_mul]
        convert hscaled using 1 <;> ring
      exact (le_div_iff₀ hNr).2 (by simpa [mul_comm] using hscaled')
lemma signedPowersOfTwo_sum_succ (n : ℕ) (s : Fin (n + 2) → ℤ) :
    (∑ i : Fin (n + 2), s i * (2 : ℤ) ^ ((n + 1) - (i : ℕ))) =
      2 * (∑ i : Fin (n + 1), s i.castSucc * (2 : ℤ) ^ (n - (i : ℕ))) +
        s (Fin.last (n + 1)) := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, Nat.sub_self, pow_zero, mul_one]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi : (i : ℕ) ≤ n := Nat.le_of_lt_succ i.isLt
  rw [Nat.succ_sub hi, pow_succ]
  ring
lemma signedPowersOfTwo_int_ne_zero :
    ∀ (n : ℕ) (s : Fin (n + 1) → ℤ),
      (∀ i, s i = -1 ∨ s i = 0 ∨ s i = 1) →
      (∃ i, s i ≠ 0) →
      (∑ i : Fin (n + 1), s i * (2 : ℤ) ^ (n - (i : ℕ))) ≠ 0 := by
  intro n
  induction n with
  | zero =>
      intro s _ hnz
      rcases hnz with ⟨i, hi⟩
      have hi0 : i = 0 := Fin.eq_zero i
      subst i
      simpa using hi
  | succ n ih =>
      intro s hs hnz hzero
      let last : Fin (n + 2) := Fin.last (n + 1)
      have hsplit := signedPowersOfTwo_sum_succ n s
      have hlast : s last = 0 := by
        rcases hs last with hneg | hzero' | hone
        · rw [hneg] at hsplit
          rw [hsplit] at hzero
          omega
        · exact hzero'
        · rw [hone] at hsplit
          rw [hsplit] at hzero
          omega
      have hprefix : ∃ i : Fin (n + 1), s i.castSucc ≠ 0 := by
        rcases hnz with ⟨i, hi⟩
        exact Fin.lastCases (fun h => (h hlast).elim)
          (fun j h => ⟨j, h⟩) i hi
      have hprefix_ne := ih (fun i => s i.castSucc)
        (fun i => hs i.castSucc) hprefix
      rw [hsplit, hlast, add_zero] at hzero
      apply hprefix_ne
      omega
theorem signedPowersOfTwo_abs_one_le
    (n : ℕ) (s : Fin (n + 1) → ℤ)
    (hs : ∀ i, s i = -1 ∨ s i = 0 ∨ s i = 1)
    (hnz : ∃ i, s i ≠ 0) :
    (1 : ℝ) ≤
      |∑ i : Fin (n + 1), (s i : ℝ) * (2 : ℝ) ^ (n - (i : ℕ))| := by
  let z : ℤ := ∑ i : Fin (n + 1), s i * (2 : ℤ) ^ (n - (i : ℕ))
  have hz : z ≠ 0 := signedPowersOfTwo_int_ne_zero n s hs hnz
  have hcast :
      (∑ i : Fin (n + 1), (s i : ℝ) * (2 : ℝ) ^ (n - (i : ℕ))) =
        (z : ℝ) := by
    simp [z]
  rw [hcast, ← Int.cast_abs]
  exact_mod_cast Int.one_le_abs hz
def pairedAlternatingSum : List ℝ → ℝ
  | [] => 0
  | [x] => x
  | x :: y :: xs => x - y + pairedAlternatingSum xs
def taggedPairEdges {m : ℕ} : List (Fin m × ℝ) → List (Fin m × Fin m)
  | x :: y :: xs => (x.1, y.1) :: taggedPairEdges xs
  | _ => []
lemma taggedPairEdges_length {m : ℕ} (tags : List (Fin m × ℝ)) :
    2 * (taggedPairEdges tags).length ≤ tags.length := by
  induction tags using List.twoStepInduction with
  | nil => simp [taggedPairEdges]
  | singleton x => simp [taggedPairEdges]
  | cons_cons x y xs ih _ =>
      simp only [taggedPairEdges, List.length_cons]
      omega
lemma int_sign_abs_le_one {m : ℕ} (s : Fin m → ℤ)
    (hs : ∀ i, s i = -1 ∨ s i = 0 ∨ s i = 1) (i : Fin m) :
    |(s i : ℝ)| ≤ 1 := by
  rcases hs i with h | h | h <;> rw [h] <;> norm_num
lemma tagged_signed_sum_abs_le_alternating
    {m : ℕ} (tags : List (Fin m × ℝ)) (s : Fin m → ℤ)
    (hsorted : tags.Pairwise (fun a b => b.2 ≤ a.2))
    (hnonneg : ∀ p ∈ tags, 0 ≤ p.2)
    (hs : ∀ i, s i = -1 ∨ s i = 0 ∨ s i = 1)
    (hcancel : ∀ e ∈ taggedPairEdges tags, s e.1 + s e.2 = 0) :
    |(tags.map (fun p => (s p.1 : ℝ) * p.2)).sum| ≤
      pairedAlternatingSum (tags.map Prod.snd) := by
  induction tags using List.twoStepInduction with
  | nil => simp [pairedAlternatingSum]
  | singleton a =>
      have ha : 0 ≤ a.2 := hnonneg a (by simp)
      simpa [pairedAlternatingSum, abs_mul, abs_of_nonneg ha] using
        (mul_le_mul_of_nonneg_right (int_sign_abs_le_one s hs a.1) ha)
  | cons_cons a b rest ih _ =>
      have hab : b.2 ≤ a.2 :=
        (List.pairwise_cons.mp hsorted).1 b (by simp)
      have hrest : rest.Pairwise (fun a b => b.2 ≤ a.2) :=
        (List.pairwise_cons.mp (List.pairwise_cons.mp hsorted).2).2
      have hnonneg_rest : ∀ p ∈ rest, 0 ≤ p.2 := by
        intro p hp
        exact hnonneg p (by simp [hp])
      have hcancel_rest :
          ∀ e ∈ taggedPairEdges rest, s e.1 + s e.2 = 0 := by
        intro e he
        exact hcancel e (by simp [taggedPairEdges, he])
      have hpair_cancel : s a.1 + s b.1 = 0 :=
        hcancel (a.1, b.1) (by simp [taggedPairEdges])
      have hpair_cancel_real : (s a.1 : ℝ) + (s b.1 : ℝ) = 0 := by
        exact_mod_cast hpair_cancel
      have hpair :
          (s a.1 : ℝ) * a.2 + (s b.1 : ℝ) * b.2 =
            (s a.1 : ℝ) * (a.2 - b.2) := by
        linear_combination b.2 * hpair_cancel_real
      have hdiff : 0 ≤ a.2 - b.2 := sub_nonneg.mpr hab
      have hpair_abs :
          |(s a.1 : ℝ) * a.2 + (s b.1 : ℝ) * b.2| ≤ a.2 - b.2 := by
        rw [hpair, abs_mul, abs_of_nonneg hdiff]
        exact mul_le_of_le_one_left hdiff (int_sign_abs_le_one s hs a.1)
      have ih' := ih hrest hnonneg_rest hcancel_rest
      calc
        |((a :: b :: rest).map (fun p => (s p.1 : ℝ) * p.2)).sum| =
            |((s a.1 : ℝ) * a.2 + (s b.1 : ℝ) * b.2) +
              (rest.map (fun p => (s p.1 : ℝ) * p.2)).sum| := by
                simp only [List.map_cons, List.sum_cons]
                ring
        _ ≤ |(s a.1 : ℝ) * a.2 + (s b.1 : ℝ) * b.2| +
              |(rest.map (fun p => (s p.1 : ℝ) * p.2)).sum| := abs_add_le _ _
        _ ≤ (a.2 - b.2) + pairedAlternatingSum (rest.map Prod.snd) :=
          add_le_add hpair_abs ih'
        _ = pairedAlternatingSum ((a :: b :: rest).map Prod.snd) := by
          simp [pairedAlternatingSum]
def pairedEvenSum : List ℝ → ℝ
  | [] => 0
  | [x] => x
  | x :: _y :: xs => x + pairedEvenSum xs
lemma zipIdx_even_sum_eq_pairedEvenSum (xs : List ℝ) (k : ℕ)
    (hk : k % 2 = 0) :
    (((xs.zipIdx k).filter (fun p => p.2 % 2 = 0)).map Prod.fst).sum =
      pairedEvenSum xs := by
  induction xs using List.twoStepInduction generalizing k with
  | nil => simp [pairedEvenSum]
  | singleton x => simp [pairedEvenSum, hk]
  | cons_cons x y xs ih _ =>
      have hk1 : (k + 1) % 2 ≠ 0 := by omega
      have hk2 : (k + 1 + 1) % 2 = 0 := by omega
      simp [pairedEvenSum, List.zipIdx_cons, hk, hk1, ih (k + 1 + 1) hk2]
lemma two_mul_pairedEvenSum (xs : List ℝ) :
    2 * pairedEvenSum xs = xs.sum + pairedAlternatingSum xs := by
  induction xs using List.twoStepInduction with
  | nil => simp [pairedEvenSum, pairedAlternatingSum]
  | singleton x => simp [pairedEvenSum, pairedAlternatingSum]; ring
  | cons_cons x y xs ih _ =>
      simp only [pairedEvenSum, pairedAlternatingSum, List.sum_cons]
      rw [mul_add, ih]
      ring
lemma firstPlayerShare_eq_pairedEvenSum (xs : List ℝ) :
    firstPlayerShare xs = pairedEvenSum (xs.mergeSort (· ≥ ·)) := by
  unfold firstPlayerShare
  exact zipIdx_even_sum_eq_pairedEvenSum _ 0 (by norm_num)
lemma two_mul_firstPlayerShare (xs : List ℝ) :
    2 * firstPlayerShare xs =
      xs.sum + pairedAlternatingSum (xs.mergeSort (· ≥ ·)) := by
  rw [firstPlayerShare_eq_pairedEvenSum, two_mul_pairedEvenSum]
  rw [(List.mergeSort_perm xs (· ≥ ·)).sum_eq]
def tagBlocks : (blocks : List (List ℝ)) → List (Fin blocks.length × ℝ)
  | [] => []
  | block :: blocks =>
      block.map (fun x => (0, x)) ++
        (tagBlocks blocks).map (fun p => (p.1.succ, p.2))
lemma tagBlocks_values (blocks : List (List ℝ)) :
    (tagBlocks blocks).map Prod.snd = blocks.flatten := by
  induction blocks with
  | nil => simp [tagBlocks]
  | cons block blocks ih =>
      simp only [tagBlocks, List.map_append, List.map_map, List.flatten_cons]
      simpa [Function.comp_def] using congrArg (block ++ ·) ih
lemma tagBlocks_weighted_sum (blocks : List (List ℝ))
    (f : Fin blocks.length → ℝ) :
    ((tagBlocks blocks).map (fun p => f p.1 * p.2)).sum =
      ∑ i : Fin blocks.length, f i * (blocks.get i).sum := by
  induction blocks with
  | nil => simp [tagBlocks]
  | cons block blocks ih =>
      simp only [List.length_cons] at f ⊢
      rw [tagBlocks]
      rw [Fin.sum_univ_succ]
      simp only [List.map_append, List.sum_append, List.map_map,
        Function.comp_def]
      simp only [List.get_eq_getElem, List.getElem_cons_zero,
        List.getElem_cons_succ]
      rw [List.sum_map_mul_left, ih (fun i => f i.succ)]
      simp
def castTagBlocks (n : ℕ) (blocks : List (List ℝ))
    (hlen : blocks.length = n + 1) : List (Fin (n + 1) × ℝ) :=
  (tagBlocks blocks).map (fun p => (Fin.cast hlen p.1, p.2))
lemma castTagBlocks_values (n : ℕ) (blocks : List (List ℝ))
    (hlen : blocks.length = n + 1) :
    (castTagBlocks n blocks hlen).map Prod.snd = blocks.flatten := by
  simp only [castTagBlocks, List.map_map, Function.comp_def]
  simpa using tagBlocks_values blocks
lemma castTagBlocks_weighted_sum (n : ℕ) (blocks : List (List ℝ))
    (hlen : blocks.length = n + 1) (s : Fin (n + 1) → ℝ) :
    ((castTagBlocks n blocks hlen).map (fun p => s p.1 * p.2)).sum =
      ∑ i : Fin (n + 1), s i * (blocks.get (Fin.cast hlen.symm i)).sum := by
  rw [castTagBlocks, List.map_map]
  change ((tagBlocks blocks).map
    (fun p => s (Fin.cast hlen p.1) * p.2)).sum = _
  rw [tagBlocks_weighted_sum blocks (fun i => s (Fin.cast hlen i))]
  apply Fintype.sum_equiv (finCongr hlen)
  intro i
  simp
noncomputable def sortedCastTagBlocks (n : ℕ) (blocks : List (List ℝ))
    (hlen : blocks.length = n + 1) : List (Fin (n + 1) × ℝ) :=
  (castTagBlocks n blocks hlen).mergeSort (fun a b => a.2 ≥ b.2)
lemma sortedCastTagBlocks_pairwise (n : ℕ) (blocks : List (List ℝ))
    (hlen : blocks.length = n + 1) :
    (sortedCastTagBlocks n blocks hlen).Pairwise (fun a b => b.2 ≤ a.2) := by
  exact List.pairwise_mergeSort' _ _
lemma sortedCastTagBlocks_values (n : ℕ) (blocks : List (List ℝ))
    (hlen : blocks.length = n + 1) :
    (sortedCastTagBlocks n blocks hlen).map Prod.snd =
      blocks.flatten.mergeSort (· ≥ ·) := by
  have hperm :
      ((sortedCastTagBlocks n blocks hlen).map Prod.snd).Perm blocks.flatten := by
    have hp := (List.mergeSort_perm (castTagBlocks n blocks hlen)
      (fun a b => a.2 ≥ b.2)).map Prod.snd
    rw [castTagBlocks_values n blocks hlen] at hp
    exact hp
  have hsorted_left :
      ((sortedCastTagBlocks n blocks hlen).map Prod.snd).Pairwise (· ≥ ·) :=
    (sortedCastTagBlocks_pairwise n blocks hlen).map Prod.snd (by
      intro a b hab
      exact hab)
  exact (hperm.trans (List.mergeSort_perm blocks.flatten (· ≥ ·)).symm).eq_of_pairwise'
    hsorted_left (List.pairwise_mergeSort' (· ≥ ·) blocks.flatten)
lemma block_sum_eq_of_map_sum_eq (n : ℕ) (c : ℝ) (blocks : List (List ℝ))
    (hblocks : blocks.map List.sum =
      (List.range (n + 1)).map (fun i => c * (2 : ℝ) ^ (n - i)))
    (hlen : blocks.length = n + 1)
    (i : Fin (n + 1)) :
    (blocks.get (Fin.cast hlen.symm i)).sum =
      c * (2 : ℝ) ^ (n - (i : ℕ)) := by
  have hi := congrArg (fun xs : List ℝ => xs[i.1]?) hblocks
  simp only [List.getElem?_map] at hi
  have hib : i.1 < blocks.length := by simpa [hlen] using i.2
  have hir : i.1 < (List.range (n + 1)).length := by simpa using i.2
  rw [List.getElem?_eq_getElem hib, List.getElem?_eq_getElem hir] at hi
  simp only [Option.map_some, List.getElem_range] at hi
  exact Option.some.inj hi
lemma sum_flatten_eq_map_sum (blocks : List (List ℝ)) :
    blocks.flatten.sum = (blocks.map List.sum).sum := by
  induction blocks with
  | nil => simp
  | cons block blocks ih => simp [ih]
lemma reverse_powers_two_sum (n : ℕ) :
    ((List.range (n + 1)).map (fun i => (2 : ℝ) ^ (n - i))).sum =
      (2 : ℝ) ^ (n + 1) - 1 := by
  change (∑ i ∈ Finset.range (n + 1), (2 : ℝ) ^ (n - i)) = _
  rw [show (∑ i ∈ Finset.range (n + 1), (2 : ℝ) ^ (n - i)) =
      ∑ i ∈ Finset.range (n + 1), (2 : ℝ) ^ i by
    simpa using Finset.sum_range_reflect (fun i => (2 : ℝ) ^ i) (n + 1)]
  have h := geom_sum_mul (2 : ℝ) (n + 1)
  norm_num at h ⊢
  exact h
theorem geometric_refinement_share_of_signing
    (sparseSigning :
      ∀ (n : ℕ) (edges : List (Fin (n + 1) × Fin (n + 1))),
        edges.length ≤ n →
        ∃ s : Fin (n + 1) → ℤ, (∃ i, s i ≠ 0) ∧
          (∀ i, s i = -1 ∨ s i = 0 ∨ s i = 1) ∧
          ∀ e ∈ edges, s e.1 + s e.2 = 0)
    (signedPowers :
      ∀ (n : ℕ) (s : Fin (n + 1) → ℤ),
        (∀ i, s i = -1 ∨ s i = 0 ∨ s i = 1) →
        (∃ i, s i ≠ 0) →
        (1 : ℝ) ≤
          |∑ i : Fin (n + 1),
            (s i : ℝ) * (2 : ℝ) ^ (n - (i : ℕ))|)
    (n : ℕ) (c : ℝ) (blocks : List (List ℝ))
    (hc : 0 ≤ c)
    (hblocks : blocks.map List.sum =
      (List.range (n + 1)).map (fun i => c * (2 : ℝ) ^ (n - i)))
    (hnonneg : ∀ x : ℝ, x ∈ blocks.flatten → 0 ≤ x)
    (hlength : blocks.flatten.length ≤ 2 * n + 1) :
    c * (2 : ℝ) ^ n ≤ firstPlayerShare blocks.flatten := by
  have hlen : blocks.length = n + 1 := by
    have h := congrArg List.length hblocks
    simpa using h
  let tags := sortedCastTagBlocks n blocks hlen
  let edges := taggedPairEdges tags
  have htags_length : tags.length = blocks.flatten.length := by
    have h := congrArg List.length (sortedCastTagBlocks_values n blocks hlen)
    simpa [tags] using h
  have hedges_length : edges.length ≤ n := by
    have hpairs := taggedPairEdges_length tags
    rw [htags_length] at hpairs
    dsimp only [edges]
    omega
  rcases sparseSigning n edges hedges_length with
    ⟨s, hs_nonzero, hs_values, hs_cancel⟩
  have htags_sorted : tags.Pairwise (fun a b => b.2 ≤ a.2) := by
    exact sortedCastTagBlocks_pairwise n blocks hlen
  have htags_nonneg : ∀ p ∈ tags, 0 ≤ p.2 := by
    intro p hp
    have hp' : p ∈ castTagBlocks n blocks hlen :=
      (List.mergeSort_perm (castTagBlocks n blocks hlen)
        (fun a b => a.2 ≥ b.2)).mem_iff.mp hp
    apply hnonneg p.2
    rw [← castTagBlocks_values n blocks hlen]
    exact List.mem_map.mpr ⟨p, hp', rfl⟩
  have hcancel : ∀ e ∈ taggedPairEdges tags, s e.1 + s e.2 = 0 := by
    exact hs_cancel
  have hledger := tagged_signed_sum_abs_le_alternating tags s htags_sorted
    htags_nonneg hs_values hcancel
  have hweighted :
      (tags.map (fun p => (s p.1 : ℝ) * p.2)).sum =
        c * ∑ i : Fin (n + 1),
          (s i : ℝ) * (2 : ℝ) ^ (n - (i : ℕ)) := by
    calc
      (tags.map (fun p => (s p.1 : ℝ) * p.2)).sum =
          ((castTagBlocks n blocks hlen).map
            (fun p => (s p.1 : ℝ) * p.2)).sum := by
        exact ((List.mergeSort_perm (castTagBlocks n blocks hlen)
          (fun a b => a.2 ≥ b.2)).map
            (fun p => (s p.1 : ℝ) * p.2)).sum_eq
      _ = ∑ i : Fin (n + 1),
          (s i : ℝ) * (blocks.get (Fin.cast hlen.symm i)).sum :=
        castTagBlocks_weighted_sum n blocks hlen (fun i => (s i : ℝ))
      _ = ∑ i : Fin (n + 1),
          (s i : ℝ) * (c * (2 : ℝ) ^ (n - (i : ℕ))) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [block_sum_eq_of_map_sum_eq n c blocks hblocks hlen i]
      _ = c * ∑ i : Fin (n + 1),
          (s i : ℝ) * (2 : ℝ) ^ (n - (i : ℕ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hsigned := signedPowers n s hs_values hs_nonzero
  have hc_weighted : c ≤ |(tags.map (fun p => (s p.1 : ℝ) * p.2)).sum| := by
    rw [hweighted, abs_mul, abs_of_nonneg hc]
    calc
      c = c * 1 := by ring
      _ ≤ c * |∑ i : Fin (n + 1),
          (s i : ℝ) * (2 : ℝ) ^ (n - (i : ℕ))| :=
        mul_le_mul_of_nonneg_left hsigned hc
  have hc_disc : c ≤ pairedAlternatingSum (blocks.flatten.mergeSort (· ≥ ·)) := by
    rw [← sortedCastTagBlocks_values n blocks hlen]
    exact hc_weighted.trans hledger
  have hsum : blocks.flatten.sum = c * ((2 : ℝ) ^ (n + 1) - 1) := by
    calc
      blocks.flatten.sum = (blocks.map List.sum).sum := sum_flatten_eq_map_sum blocks
      _ = ((List.range (n + 1)).map
          (fun i => c * (2 : ℝ) ^ (n - i))).sum := congrArg List.sum hblocks
      _ = c * ((List.range (n + 1)).map
          (fun i => (2 : ℝ) ^ (n - i))).sum := by
        rw [List.sum_map_mul_left]
      _ = c * ((2 : ℝ) ^ (n + 1) - 1) := by rw [reverse_powers_two_sum]
  have hshare := two_mul_firstPlayerShare blocks.flatten
  rw [hsum, pow_succ] at hshare
  nlinarith
theorem geometric_refinement_share
    (n : ℕ) (c : ℝ) (blocks : List (List ℝ))
    (hc : 0 ≤ c)
    (hblocks : blocks.map List.sum =
      (List.range (n + 1)).map (fun i => c * (2 : ℝ) ^ (n - i)))
    (hnonneg : ∀ x : ℝ, x ∈ blocks.flatten → 0 ≤ x)
    (hlength : blocks.flatten.length ≤ 2 * n + 1) :
    c * (2 : ℝ) ^ n ≤ firstPlayerShare blocks.flatten := by
  exact geometric_refinement_share_of_signing sparseEdgeSigning
    signedPowersOfTwo_abs_one_le n c blocks hc hblocks hnonneg hlength
lemma firstPlayerShare_pairs_residual_le (pairs residual : List ℝ)
    (hpairs : ∀ x ∈ pairs, 0 ≤ x)
    (hresidual : ∀ x ∈ residual, 0 ≤ x) :
    firstPlayerShare (pairs.flatMap (fun a => [a, a]) ++ residual) ≤
      pairs.sum + residual.sum := by
  let paritySums : List ℝ → ℝ × ℝ := fun l =>
    l.foldr (fun a p => (a + p.2, p.1)) (0, 0)
  have zipIdx_parity (l : List ℝ) (n : ℕ) :
      (((l.zipIdx n).filter (fun p => p.2 % 2 = 0)).map Prod.fst).sum =
        if n % 2 = 0 then (paritySums l).1 else (paritySums l).2 := by
    induction l generalizing n with
    | nil => simp [paritySums]
    | cons a l ih =>
        have hmod : n % 2 < 2 := Nat.mod_lt _ (by omega)
        by_cases hn : n % 2 = 0
        · have hn' : (n + 1) % 2 = 1 := by omega
          simp [hn, hn', ih, paritySums]
        · have hn0 : n % 2 = 1 := by omega
          have hn' : (n + 1) % 2 = 0 := by omega
          simp [hn0, hn', ih, paritySums]
  have share_eq (l : List ℝ) :
      firstPlayerShare l = (paritySums (l.mergeSort (· ≥ ·))).1 := by
    unfold firstPlayerShare
    simpa using zipIdx_parity (l.mergeSort (· ≥ ·)) 0
  have parity_bounds (l : List ℝ)
      (hsorted : l.Pairwise (· ≥ ·))
      (hnonneg : ∀ x ∈ l, 0 ≤ x) :
      (paritySums l).2 ≤ (paritySums l).1 ∧
        (paritySums l).1 ≤ (paritySums l).2 + l.headD 0 := by
    induction l with
    | nil => simp [paritySums]
    | cons a l ih =>
        have htail : ∀ x ∈ l, 0 ≤ x := by
          intro x hx
          exact hnonneg x (by simp [hx])
        have hi := ih hsorted.of_cons htail
        have hhead : l.headD 0 ≤ a := by
          cases l with
          | nil => simpa using hnonneg a (by simp)
          | cons b l =>
              simpa using (List.pairwise_cons_cons_iff_of_trans.mp hsorted).1
        simp only [paritySums, List.foldr, Prod.fst, Prod.snd, List.headD_cons]
        constructor
        · linarith [hi.2, hhead]
        · linarith [hi.1]
  have orderedInsert_le (x : ℝ) (l : List ℝ)
      (hx : 0 ≤ x) (hsorted : l.Pairwise (· ≥ ·))
      (hnonneg : ∀ y ∈ l, 0 ≤ y) :
      (paritySums (l.orderedInsert (· ≥ ·) x)).1 ≤
          (paritySums l).1 + x ∧
        (paritySums (l.orderedInsert (· ≥ ·) x)).2 ≤
          (paritySums l).2 + x := by
    induction l with
    | nil => simp [paritySums, hx]
    | cons a l ih =>
        by_cases hxa : x ≥ a
        · rw [List.orderedInsert_cons_of_le (r := fun x y : ℝ => x ≥ y) l hxa]
          simp only [paritySums, List.foldr, Prod.fst, Prod.snd]
          have hodd : (paritySums l).1 ≤ a + (paritySums l).2 := by
            simpa only [paritySums, List.foldr, Prod.fst, Prod.snd] using
              (parity_bounds (a :: l) hsorted hnonneg).1
          have heven : a + (paritySums l).2 ≤ (paritySums l).1 + a := by
            simpa only [paritySums, List.foldr, Prod.fst, Prod.snd,
              List.headD_cons] using
              (parity_bounds (a :: l) hsorted hnonneg).2
          constructor <;> linarith
        · rw [List.orderedInsert_of_not_le
            (r := fun x y : ℝ => x ≥ y) l hxa]
          simp only [paritySums, List.foldr, Prod.fst, Prod.snd]
          have hi := ih hsorted.of_cons (by
            intro y hy
            exact hnonneg y (by simp [hy]))
          exact ⟨by linarith [hi.2], hi.1⟩
  have share_cons_le (x : ℝ) (l : List ℝ)
      (hx : 0 ≤ x) (hnonneg : ∀ y ∈ l, 0 ≤ y) :
      firstPlayerShare (x :: l) ≤ firstPlayerShare l + x := by
    rw [share_eq, share_eq]
    rw [List.mergeSort_eq_insertionSort, List.mergeSort_eq_insertionSort,
      List.insertionSort_cons]
    exact (orderedInsert_le x (l.insertionSort (· ≥ ·)) hx
      (List.pairwise_insertionSort (· ≥ ·) l) (by
        intro y hy
        exact hnonneg y (by simpa using hy))).1
  have share_append_le (r base : List ℝ)
      (hr : ∀ x ∈ r, 0 ≤ x) (hbase : ∀ x ∈ base, 0 ≤ x) :
      firstPlayerShare (r ++ base) ≤ firstPlayerShare base + r.sum := by
    induction r with
    | nil => simp
    | cons x r ih =>
        simp only [List.cons_append, List.sum_cons]
        have hx : 0 ≤ x := hr x (by simp)
        have htail : ∀ y ∈ r, 0 ≤ y := by
          intro y hy
          exact hr y (by simp [hy])
        calc
          firstPlayerShare (x :: (r ++ base)) ≤
              firstPlayerShare (r ++ base) + x :=
            share_cons_le x (r ++ base) hx (by
              intro y hy
              rcases List.mem_append.mp hy with hy | hy
              · exact htail y hy
              · exact hbase y hy)
          _ ≤ firstPlayerShare base + r.sum + x := by
            linarith [ih htail]
          _ = firstPlayerShare base + (x + r.sum) := by ring
  have parity_dup (l : List ℝ) :
      (paritySums (l.flatMap (fun a => [a, a]))).1 = l.sum := by
    induction l with
    | nil => simp [paritySums]
    | cons a l ih => simp [paritySums, ih]
  have dup_pairwise (l : List ℝ) (hsorted : l.Pairwise (· ≥ ·)) :
      (l.flatMap (fun a => [a, a])).Pairwise (· ≥ ·) := by
    induction l with
    | nil => simp
    | cons a l ih =>
        have htail := hsorted.of_cons
        have hal : ∀ y ∈ l.flatMap (fun a => [a, a]), a ≥ y := by
          intro y hy
          simp only [List.mem_flatMap] at hy
          rcases hy with ⟨b, hb, hy⟩
          have : y = b := by simpa using hy
          subst y
          exact (List.pairwise_cons.mp hsorted).1 b hb
        change (a :: a :: l.flatMap (fun a => [a, a])).Pairwise (· ≥ ·)
        rw [List.pairwise_cons, List.pairwise_cons]
        exact ⟨by
          intro y hy
          rw [List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact le_rfl
          · exact hal y hy, hal, ih htail⟩
  have share_dup (l : List ℝ) :
      firstPlayerShare (l.flatMap (fun a => [a, a])) = l.sum := by
    let sorted := l.mergeSort (· ≥ ·)
    have hperm : List.Perm
        (sorted.flatMap (fun a => [a, a]))
        (l.flatMap (fun a => [a, a])) :=
      (List.mergeSort_perm l (· ≥ ·)).flatMap (fun _ _ => .refl _)
    have hsorted :
        (sorted.flatMap (fun a => [a, a])).mergeSort (· ≥ ·) =
          sorted.flatMap (fun a => [a, a]) :=
      List.mergeSort_eq_self (r := fun x y : ℝ => x ≥ y)
        (dup_pairwise sorted (List.pairwise_mergeSort' (· ≥ ·) l))
    calc
      firstPlayerShare (l.flatMap (fun a => [a, a])) =
          firstPlayerShare (sorted.flatMap (fun a => [a, a])) :=
        (firstPlayerShare_eq_of_perm _ _ hperm).symm
      _ = (paritySums (sorted.flatMap (fun a => [a, a]))).1 := by
        rw [share_eq, hsorted]
      _ = sorted.sum := parity_dup sorted
      _ = l.sum := (List.mergeSort_perm l (· ≥ ·)).sum_eq
  calc
    firstPlayerShare (pairs.flatMap (fun a => [a, a]) ++ residual) =
        firstPlayerShare (residual ++ pairs.flatMap (fun a => [a, a])) :=
      firstPlayerShare_eq_of_perm _ _ List.perm_append_comm
    _ ≤ firstPlayerShare (pairs.flatMap (fun a => [a, a])) + residual.sum :=
      share_append_le residual (pairs.flatMap (fun a => [a, a])) hresidual (by
        intro x hx
        simp only [List.mem_flatMap] at hx
        rcases hx with ⟨a, ha, hxa⟩
        have : x = a := by simpa using hxa
        subst x
        exact hpairs a ha)
    _ = pairs.sum + residual.sum := by rw [share_dup]
lemma permuteListToMappedTarget {α β : Type*} (f : α → β)
    (l : List α) (target : List β) (h : (l.map f).Perm target) :
    ∃ l' : List α, l'.Perm l ∧ l'.map f = target := by
  have lift : ∀ {source target : List β}, source.Perm target →
      ∀ l : List α, l.map f = source →
        ∃ l' : List α, l'.Perm l ∧ l'.map f = target := by
    intro source target hp
    induction hp with
    | nil =>
        intro l hl
        simp only [List.map_eq_nil_iff] at hl
        subst l
        exact ⟨[], .refl [], rfl⟩
    | cons a hp ih =>
        intro l hl
        cases l with
        | nil => simp at hl
        | cons b l =>
            simp only [List.map_cons, List.cons.injEq] at hl
            rcases hl with ⟨hfb, hl⟩
            rcases ih l hl with ⟨l', hperm, hmap⟩
            refine ⟨b :: l', hperm.cons b, ?_⟩
            simp [hfb, hmap]
    | swap a b l' =>
        intro l hl
        cases l with
        | nil => simp at hl
        | cons x l =>
            cases l with
            | nil => simp at hl
            | cons y l =>
                simp only [List.map_cons, List.cons.injEq] at hl
                rcases hl with ⟨hfx, hfy, htail⟩
                refine ⟨y :: x :: l, .swap x y l, ?_⟩
                simp [hfx, hfy, htail]
    | trans hp₁ hp₂ ih₁ ih₂ =>
        intro l hl
        rcases ih₁ l hl with ⟨l₁, hl₁, hmap₁⟩
        rcases ih₂ l₁ hmap₁ with ⟨l₂, hl₂, hmap₂⟩
        exact ⟨l₂, hl₂.trans hl₁, hmap₂⟩
  exact lift h l rfl
lemma positiveListTransport (as bs : List ℝ)
    (ha : ∀ x ∈ as, 0 < x) (hb : ∀ x ∈ bs, 0 < x)
    (hne : as ≠ [] ∨ bs ≠ []) (hsum : bs.sum ≤ as.sum) :
    ∃ (ablocks bblocks : List (List ℝ)) (pairs residual : List ℝ),
      ablocks.map List.sum = as ∧
      bblocks.map List.sum = bs ∧
      (∀ block ∈ ablocks, block ≠ []) ∧
      (∀ block ∈ bblocks, block ≠ []) ∧
      (∀ x ∈ ablocks.flatten, 0 < x) ∧
      (∀ x ∈ bblocks.flatten, 0 < x) ∧
      (ablocks.flatten ++ bblocks.flatten).Perm
        (pairs.flatMap (fun x => [x, x]) ++ residual) ∧
      (∀ x ∈ pairs, 0 < x) ∧
      (∀ x ∈ residual, 0 < x) ∧
      pairs.sum = bs.sum ∧
      residual.sum = as.sum - bs.sum ∧
      ablocks.flatten.length + bblocks.flatten.length ≤
        2 * (as.length + bs.length) - 1 := by
  have singleton_map_sums (l : List ℝ) :
      (l.map (fun x => [x])).map List.sum = l := by
    induction l with
    | nil => simp
    | cons x l ih => simp [ih]
  have singleton_map_flatten (l : List ℝ) :
      (l.map (fun x => [x])).flatten = l := by
    induction l with
    | nil => simp
    | cons x l ih => simp [ih]
  generalize hk : as.length + bs.length = k
  induction k using Nat.strong_induction_on generalizing as bs with
  | h k ih =>
      cases as with
      | nil =>
          cases bs with
          | nil => simp at hne
          | cons b bs =>
              have hbpos : 0 < b := hb b (by simp)
              have htail : 0 ≤ bs.sum := List.sum_nonneg (by
                intro x hx
                exact (hb x (by simp [hx])).le)
              simp only [List.sum_cons, List.sum_nil] at hsum
              linarith
      | cons a as =>
          have hapos : 0 < a := ha a (by simp)
          have hat : ∀ x ∈ as, 0 < x := by
            intro x hx
            exact ha x (by simp [hx])
          cases bs with
          | nil =>
              refine ⟨(a :: as).map (fun x => [x]), [], [], a :: as,
                ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · exact singleton_map_sums (a :: as)
              · simp
              · intro block hblock
                simp only [List.mem_map] at hblock
                rcases hblock with ⟨x, hx, rfl⟩
                simp
              · simp
              · simpa [singleton_map_flatten] using ha
              · simp
              · simpa [singleton_map_flatten] using
                  (List.Perm.refl (a :: as))
              · simp
              · simpa using ha
              · simp
              · simp
              · rw [singleton_map_flatten]
                simp only [List.flatten_nil, List.length_cons, List.length_nil,
                  add_zero, zero_add] at hk ⊢
                omega
          | cons b bs =>
              have hbpos : 0 < b := hb b (by simp)
              have hbt : ∀ x ∈ bs, 0 < x := by
                intro x hx
                exact hb x (by simp [hx])
              rcases lt_trichotomy a b with hab | hab | hab
              · let r := b - a
                have hr : 0 < r := sub_pos.mpr hab
                have hsum' : (r :: bs).sum ≤ as.sum := by
                  simp only [List.sum_cons] at hsum ⊢
                  dsimp [r]
                  linarith
                have hk' : as.length + (r :: bs).length < k := by
                  simp only [List.length_cons] at hk ⊢
                  omega
                rcases ih _ hk' as (r :: bs) hat (by
                    intro x hx
                    rcases List.mem_cons.mp hx with rfl | hx
                    · exact hr
                    · exact hbt x hx)
                    (Or.inr (by simp)) hsum' rfl with
                  ⟨ablocks, bblocks, pairs, residual, hmapa, hmapb,
                    hnea, hneb, hposa, hposb, hperm, hpospairs,
                    hposres, hpairsum, hressum, hlen⟩
                cases bblocks with
                | nil => simp at hmapb
                | cons block bblocks =>
                    simp only [List.map_cons, List.cons.injEq] at hmapb
                    rcases hmapb with ⟨hblocksum, hmapb⟩
                    refine ⟨[a] :: ablocks, (a :: block) :: bblocks,
                      a :: pairs, residual, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
                      ?_, ?_, ?_, ?_, ?_⟩
                    · simp [hmapa]
                    · simp only [List.map_cons, List.sum_cons,
                        List.cons.injEq, hmapb]
                      constructor
                      · dsimp [r] at hblocksum
                        linarith
                      · trivial
                    · intro tail htail
                      rcases List.mem_cons.mp htail with rfl | htail
                      · simp
                      · exact hnea tail htail
                    · intro tail htail
                      rcases List.mem_cons.mp htail with rfl | htail
                      · simp
                      · exact hneb tail (by simp [htail])
                    · intro x hx
                      simp only [List.flatten_cons, List.singleton_append,
                        List.mem_cons] at hx
                      exact hx.elim (fun h => h ▸ hapos) (hposa x)
                    · intro x hx
                      simp only [List.flatten_cons, List.cons_append,
                        List.mem_cons] at hx
                      exact hx.elim (fun h => h ▸ hapos) (hposb x)
                    · have hmove :
                          (a :: ablocks.flatten ++
                              a :: (block ++ bblocks.flatten)).Perm
                            (a :: a ::
                              (ablocks.flatten ++ block ++ bblocks.flatten)) := by
                          simpa [List.append_assoc] using
                            (List.perm_middle (a := a)
                              (l₁ := ablocks.flatten)
                              (l₂ := block ++ bblocks.flatten)).symm.cons a
                      have hperm' :
                          (ablocks.flatten ++ block ++ bblocks.flatten).Perm
                            (pairs.flatMap (fun x => [x, x]) ++ residual) := by
                        simpa [List.flatten_cons, List.append_assoc] using hperm
                      simpa [List.flatten_cons, List.append_assoc] using
                        hmove.trans ((hperm'.cons a).cons a)
                    · intro x hx
                      rcases List.mem_cons.mp hx with rfl | hx
                      · exact hapos
                      · exact hpospairs x hx
                    · exact hposres
                    · simp only [List.sum_cons, hpairsum]
                      dsimp [r]
                      ring
                    · dsimp [r] at hressum ⊢
                      linarith
                    · simp only [List.flatten_cons, List.singleton_append,
                        List.cons_append, List.length_cons,
                        List.length_append, List.length_nil, zero_add,
                        add_zero] at hlen ⊢
                      simp only [List.length_cons] at hk
                      omega
              · subst b
                by_cases hempty : as = [] ∧ bs = []
                · rcases hempty with ⟨rfl, rfl⟩
                  refine ⟨[[a]], [[a]], [a], [], ?_, ?_, ?_, ?_, ?_, ?_,
                    ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [hapos]
                  norm_num at hk
                  omega
                · have hsum' : bs.sum ≤ as.sum := by
                    simp only [List.sum_cons] at hsum
                    linarith
                  have hk' : as.length + bs.length < k := by
                    simp only [List.length_cons] at hk
                    omega
                  have hne' : as ≠ [] ∨ bs ≠ [] := by
                    tauto
                  rcases ih _ hk' as bs hat hbt hne' hsum' rfl with
                    ⟨ablocks, bblocks, pairs, residual, hmapa, hmapb,
                      hnea, hneb, hposa, hposb, hperm, hpospairs,
                      hposres, hpairsum, hressum, hlen⟩
                  refine ⟨[a] :: ablocks, [a] :: bblocks, a :: pairs,
                    residual, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
                    ?_, ?_⟩
                  · simp [hmapa]
                  · simp [hmapb]
                  · intro tail htail
                    rcases List.mem_cons.mp htail with rfl | htail
                    · simp
                    · exact hnea tail htail
                  · intro tail htail
                    rcases List.mem_cons.mp htail with rfl | htail
                    · simp
                    · exact hneb tail htail
                  · intro x hx
                    simp only [List.flatten_cons, List.singleton_append,
                      List.mem_cons] at hx
                    exact hx.elim (fun h => h ▸ hapos) (hposa x)
                  · intro x hx
                    simp only [List.flatten_cons, List.singleton_append,
                      List.mem_cons] at hx
                    exact hx.elim (fun h => h ▸ hapos) (hposb x)
                  · have hmove :
                        (a :: ablocks.flatten ++ a :: bblocks.flatten).Perm
                          (a :: a :: (ablocks.flatten ++ bblocks.flatten)) := by
                        simpa [List.append_assoc] using
                          (List.perm_middle (a := a)
                            (l₁ := ablocks.flatten)
                            (l₂ := bblocks.flatten)).symm.cons a
                    simpa [List.append_assoc] using
                      hmove.trans ((hperm.cons a).cons a)
                  · intro x hx
                    rcases List.mem_cons.mp hx with rfl | hx
                    · exact hapos
                    · exact hpospairs x hx
                  · exact hposres
                  · simp [hpairsum]
                  · simp only [List.sum_cons] at hressum ⊢
                    linarith
                  · simp only [List.flatten_cons, List.singleton_append,
                      List.length_cons] at hlen ⊢
                    simp only [List.length_cons] at hk
                    omega
              · let r := a - b
                have hr : 0 < r := sub_pos.mpr hab
                have hsum' : bs.sum ≤ (r :: as).sum := by
                  simp only [List.sum_cons] at hsum ⊢
                  dsimp [r]
                  linarith
                have hk' : (r :: as).length + bs.length < k := by
                  simp only [List.length_cons] at hk ⊢
                  omega
                rcases ih _ hk' (r :: as) bs (by
                    intro x hx
                    rcases List.mem_cons.mp hx with rfl | hx
                    · exact hr
                    · exact hat x hx) hbt (Or.inl (by simp)) hsum' rfl with
                  ⟨ablocks, bblocks, pairs, residual, hmapa, hmapb,
                    hnea, hneb, hposa, hposb, hperm, hpospairs,
                    hposres, hpairsum, hressum, hlen⟩
                cases ablocks with
                | nil => simp at hmapa
                | cons block ablocks =>
                    simp only [List.map_cons, List.cons.injEq] at hmapa
                    rcases hmapa with ⟨hblocksum, hmapa⟩
                    refine ⟨(b :: block) :: ablocks, [b] :: bblocks,
                      b :: pairs, residual, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
                      ?_, ?_, ?_, ?_, ?_⟩
                    · simp only [List.map_cons, List.sum_cons,
                        List.cons.injEq, hmapa]
                      constructor
                      · dsimp [r] at hblocksum
                        linarith
                      · trivial
                    · simp [hmapb]
                    · intro tail htail
                      rcases List.mem_cons.mp htail with rfl | htail
                      · simp
                      · exact hnea tail (by simp [htail])
                    · intro tail htail
                      rcases List.mem_cons.mp htail with rfl | htail
                      · simp
                      · exact hneb tail htail
                    · intro x hx
                      simp only [List.flatten_cons, List.cons_append,
                        List.mem_cons] at hx
                      exact hx.elim (fun h => h ▸ hbpos) (hposa x)
                    · intro x hx
                      simp only [List.flatten_cons, List.singleton_append,
                        List.mem_cons] at hx
                      exact hx.elim (fun h => h ▸ hbpos) (hposb x)
                    · have hmove :
                          (b :: (block ++ ablocks.flatten) ++
                              b :: bblocks.flatten).Perm
                            (b :: b ::
                              (block ++ ablocks.flatten ++ bblocks.flatten)) := by
                          simpa [List.append_assoc] using
                            (List.perm_middle (a := b)
                              (l₁ := block ++ ablocks.flatten)
                              (l₂ := bblocks.flatten)).cons b
                      simpa [List.flatten_cons, List.append_assoc] using
                        hmove.trans ((hperm.cons b).cons b)
                    · intro x hx
                      rcases List.mem_cons.mp hx with rfl | hx
                      · exact hbpos
                      · exact hpospairs x hx
                    · exact hposres
                    · simp [hpairsum]
                    · dsimp [r] at hressum ⊢
                      linarith
                    · simp only [List.flatten_cons, List.cons_append,
                        List.singleton_append, List.length_cons,
                        List.length_append, List.length_nil, zero_add,
                        add_zero] at hlen ⊢
                      simp only [List.length_cons] at hk
                      omega
lemma refinementFromDisjointSubsets
    {m : ℕ} (x : Fin m → ℝ)
    (hx : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1)
    (P Q : Finset (Fin m)) (hdisj : Disjoint P Q)
    (hne : P.Nonempty ∨ Q.Nonempty)
    (hQP : (∑ i ∈ Q, x i) ≤ ∑ i ∈ P, x i) :
    ∃ blocks : List (List ℝ),
      blocks.map List.sum = List.ofFn x ∧
      (∀ block ∈ blocks, block ≠ []) ∧
      (∀ y ∈ blocks.flatten, 0 < y) ∧
      blocks.flatten.length ≤ 2 * m - 1 ∧
      firstPlayerShare blocks.flatten ≤
        (1 + ((∑ i ∈ P, x i) - ∑ i ∈ Q, x i)) / 2 := by
  classical
  let R : Finset (Fin m) := Finset.univ \ (P ∪ Q)
  let as : List ℝ := P.toList.map x
  let bs : List ℝ := Q.toList.map x
  have sum_map_toList (f : Fin m → ℝ) (S : Finset (Fin m)) :
      (S.toList.map f).sum = ∑ i ∈ S, f i := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a S ha ih =>
        have hp := (Finset.toList_insert ha).map f
        calc
          ((insert a S).toList.map f).sum = ((a :: S.toList).map f).sum :=
            hp.sum_eq
          _ = ∑ i ∈ insert a S, f i := by simp [ha, ih]
  have ha : ∀ y ∈ as, 0 < y := by
    intro y hy
    simp only [as, List.mem_map] at hy
    rcases hy with ⟨i, hi, rfl⟩
    exact hx i
  have hb : ∀ y ∈ bs, 0 < y := by
    intro y hy
    simp only [bs, List.mem_map] at hy
    rcases hy with ⟨i, hi, rfl⟩
    exact hx i
  have hneLists : as ≠ [] ∨ bs ≠ [] := by
    rcases hne with hP | hQ
    · left
      intro ha0
      have hlist : P.toList = [] := List.map_eq_nil_iff.mp ha0
      exact hP.ne_empty (Finset.toList_eq_nil.mp hlist)
    · right
      intro hb0
      have hlist : Q.toList = [] := List.map_eq_nil_iff.mp hb0
      exact hQ.ne_empty (Finset.toList_eq_nil.mp hlist)
  have hsumLists : bs.sum ≤ as.sum := by
    rw [sum_map_toList, sum_map_toList]
    exact hQP
  rcases positiveListTransport as bs ha hb hneLists hsumLists with
    ⟨ablocks, bblocks, pairs, residual, hmapa, hmapb, hnea, hneb,
      hposa, hposb, htransport, hpospairs, hposres, hpairsum,
      hressum, htransportLen⟩
  let outsideBlocks : List (List ℝ) :=
    R.toList.map (fun i => [x i / 2, x i / 2])
  let outsidePairs : List ℝ := R.toList.map (fun i => x i / 2)
  have outside_map_sums : outsideBlocks.map List.sum = R.toList.map x := by
    dsimp [outsideBlocks]
    induction R.toList with
    | nil => simp
    | cons i l ih => simp [ih]
  have outside_flatten :
      outsideBlocks.flatten =
        outsidePairs.flatMap (fun y => [y, y]) := by
    dsimp [outsideBlocks, outsidePairs]
    induction R.toList with
    | nil => simp
    | cons i l ih => simp [ih]
  have outside_ne : ∀ block ∈ outsideBlocks, block ≠ [] := by
    intro block hblock
    simp only [outsideBlocks, List.mem_map] at hblock
    rcases hblock with ⟨i, hi, rfl⟩
    simp
  have outside_pairs_pos : ∀ y ∈ outsidePairs, 0 < y := by
    intro y hy
    simp only [outsidePairs, List.mem_map] at hy
    rcases hy with ⟨i, hi, rfl⟩
    linarith [hx i]
  have outside_pos : ∀ y ∈ outsideBlocks.flatten, 0 < y := by
    rw [outside_flatten]
    intro y hy
    simp only [List.mem_flatMap] at hy
    rcases hy with ⟨z, hz, hy⟩
    have hyz : y = z := by simpa using hy
    subst y
    exact outside_pairs_pos z hz
  have outside_len : outsideBlocks.flatten.length = 2 * R.card := by
    rw [outside_flatten]
    simp [outsidePairs]
    omega
  have outside_pairs_sum :
      outsidePairs.sum = (∑ i ∈ R, x i) / 2 := by
    rw [show outsidePairs.sum = ∑ i ∈ R, x i / 2 by
      exact sum_map_toList (fun i => x i / 2) R]
    rw [Finset.sum_div]
  have hindices :
      (P.toList ++ Q.toList ++ R.toList).Perm (List.finRange m) := by
    apply List.perm_of_nodup_nodup_toFinset_eq
    · rw [List.nodup_append]
      refine ⟨?_, Finset.nodup_toList _, ?_⟩
      · rw [List.nodup_append]
        refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, ?_⟩
        intro a haP b hbQ hab
        subst b
        exact Finset.disjoint_left.mp hdisj
          (by simpa using haP) (by simpa using hbQ)
      · intro a haPQ b hbR hab
        subst b
        simp only [List.mem_append, Finset.mem_toList] at haPQ hbR
        exact (Finset.mem_sdiff.mp hbR).2 (Finset.mem_union.mpr haPQ)
    · exact List.nodup_finRange m
    · ext i
      dsimp [R]
      simp only [List.toFinset_append, Finset.toList_toFinset,
        List.toFinset_finRange, Finset.mem_union, Finset.mem_sdiff,
        Finset.mem_univ, true_and]
      tauto
  have finRange_map : (List.finRange m).map x = List.ofFn x := by
    rw [← List.ofFn_id m, List.map_ofFn]
    rfl
  let rawBlocks := ablocks ++ bblocks ++ outsideBlocks
  have raw_map_perm : (rawBlocks.map List.sum).Perm (List.ofFn x) := by
    have hidxmap := hindices.map x
    rw [finRange_map] at hidxmap
    have hraw : rawBlocks.map List.sum =
        P.toList.map x ++ Q.toList.map x ++ R.toList.map x := by
      simp only [rawBlocks, List.map_append, hmapa, hmapb, outside_map_sums,
        as, bs]
    rw [hraw]
    simpa only [List.map_append] using hidxmap
  rcases permuteListToMappedTarget List.sum rawBlocks (List.ofFn x)
      raw_map_perm with ⟨blocks, hblocksPerm, hmapBlocks⟩
  have raw_ne : ∀ block ∈ rawBlocks, block ≠ [] := by
    intro block hblock
    simp only [rawBlocks, List.mem_append] at hblock
    rcases hblock with (hblock | hblock) | hblock
    · exact hnea block hblock
    · exact hneb block hblock
    · exact outside_ne block hblock
  have raw_pos : ∀ y ∈ rawBlocks.flatten, 0 < y := by
    intro y hy
    simp only [rawBlocks, List.flatten_append, List.mem_append] at hy
    rcases hy with (hy | hy) | hy
    · exact hposa y hy
    · exact hposb y hy
    · exact outside_pos y hy
  have hblocksFlatPerm : blocks.flatten.Perm rawBlocks.flatten := by
    simpa only [List.flatten_eq_flatMap] using
      hblocksPerm.flatMap (fun _ _ => List.Perm.refl _)
  have raw_flat_perm : rawBlocks.flatten.Perm
      ((pairs ++ outsidePairs).flatMap (fun y => [y, y]) ++ residual) := by
    have happend := htransport.append_right outsideBlocks.flatten
    rw [outside_flatten] at happend
    have hmove :
        (pairs.flatMap (fun y => [y, y]) ++ residual ++
            outsidePairs.flatMap (fun y => [y, y])).Perm
          (pairs.flatMap (fun y => [y, y]) ++
            outsidePairs.flatMap (fun y => [y, y]) ++ residual) := by
      have hcomm :
          (residual ++ outsidePairs.flatMap (fun y => [y, y])).Perm
            (outsidePairs.flatMap (fun y => [y, y]) ++ residual) :=
        List.perm_append_comm
      simpa only [List.append_assoc] using
        hcomm.append_left (pairs.flatMap (fun y => [y, y]))
    simp only [rawBlocks, List.flatten_append, List.flatMap_append,
      List.append_assoc]
    rw [outside_flatten]
    simpa only [List.append_assoc] using happend.trans hmove
  have hallFlatPerm := hblocksFlatPerm.trans raw_flat_perm
  have all_pairs_pos : ∀ y ∈ pairs ++ outsidePairs, 0 ≤ y := by
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact (hpospairs y hy).le
    · exact (outside_pairs_pos y hy).le
  have hresnonneg : ∀ y ∈ residual, 0 ≤ y := by
    intro y hy
    exact (hposres y hy).le
  have partition_sum :
      (∑ i ∈ P, x i) + (∑ i ∈ Q, x i) + (∑ i ∈ R, x i) = 1 := by
    have hu := Finset.sum_union hdisj (f := x)
    have hr := Finset.sum_sdiff (Finset.subset_univ (P ∪ Q)) (f := x)
    change (∑ i ∈ R, x i) + (∑ i ∈ P ∪ Q, x i) = ∑ i, x i at hr
    rw [hu, hsum] at hr
    linarith
  have hcardUnion : (P ∪ Q).card = P.card + Q.card :=
    Finset.card_union_of_disjoint hdisj
  have hcardR : R.card = m - (P.card + Q.card) := by
    dsimp [R]
    rw [Finset.card_sdiff]
    simp only [Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
      hcardUnion]
  have hcardPQ : P.card + Q.card ≤ m := by
    rw [← hcardUnion]
    simpa using Finset.card_le_univ (P ∪ Q)
  have hcardTotal : P.card + Q.card + R.card = m := by omega
  have hcardPos : 0 < P.card + Q.card := by
    rcases hne with hP | hQ
    · have := Finset.card_pos.mpr hP
      omega
    · have := Finset.card_pos.mpr hQ
      omega
  have raw_len : rawBlocks.flatten.length ≤ 2 * m - 1 := by
    have hablen : as.length = P.card := by simp [as]
    have hbblen : bs.length = Q.card := by simp [bs]
    simp only [rawBlocks, List.flatten_append, List.length_append]
    rw [outside_len]
    rw [hablen, hbblen] at htransportLen
    omega
  refine ⟨blocks, hmapBlocks, ?_, ?_, ?_, ?_⟩
  · intro block hblock
    exact raw_ne block (hblocksPerm.mem_iff.mp hblock)
  · intro y hy
    exact raw_pos y (hblocksFlatPerm.mem_iff.mp hy)
  · rw [hblocksFlatPerm.length_eq]
    exact raw_len
  · rw [firstPlayerShare_eq_of_perm _ _ hallFlatPerm]
    calc
      firstPlayerShare
          ((pairs ++ outsidePairs).flatMap (fun y => [y, y]) ++ residual) ≤
          (pairs ++ outsidePairs).sum + residual.sum :=
        firstPlayerShare_pairs_residual_le _ _ all_pairs_pos hresnonneg
      _ = (1 + ((∑ i ∈ P, x i) - ∑ i ∈ Q, x i)) / 2 := by
        rw [List.sum_append, hpairsum, hressum, outside_pairs_sum,
          sum_map_toList, sum_map_toList]
        linarith
lemma upperRefinementBlocks :
    ∀ (n : ℕ) (xs : List ℝ), 0 < n →
      (∀ x : ℝ, x ∈ xs → 0 < x) →
      xs.sum = 1 → xs.length ≤ n + 1 →
      ∃ blocks : List (List ℝ),
        blocks.map List.sum = xs ∧
        (∀ block : List ℝ, block ∈ blocks → block ≠ []) ∧
        (∀ x : ℝ, x ∈ blocks.flatten → 0 < x) ∧
        blocks.flatten.length ≤ xs.length + n ∧
        firstPlayerShare blocks.flatten ≤ answer n := by
  intro n xs hn hpos hsum hlen
  have half_le_answer : (1 : ℝ) / 2 ≤ answer n := by
    have hden := geometricDen_pos n
    unfold answer
    apply (le_div_iff₀ hden).2
    rw [pow_succ]
    nlinarith [show 0 < (2 : ℝ) ^ n by positivity]
  by_cases hshort : xs.length ≤ n
  · let blocks : List (List ℝ) := xs.map (fun y => [y / 2, y / 2])
    let pairs : List ℝ := xs.map (fun y => y / 2)
    have bisect_map_sums (l : List ℝ) :
        (l.map (fun y => [y / 2, y / 2])).map List.sum = l := by
      induction l with
      | nil => simp
      | cons y ys ih => simp [ih]
    have bisect_flatten (l : List ℝ) :
        (l.map (fun y => [y / 2, y / 2])).flatten =
          (l.map (fun y => y / 2)).flatMap (fun y => [y, y]) := by
      induction l with
      | nil => simp
      | cons y ys ih => simp [ih]
    have bisect_length (l : List ℝ) :
        (l.map (fun y => [y / 2, y / 2])).flatten.length =
          2 * l.length := by
      induction l with
      | nil => simp
      | cons y ys ih => simp [ih]; omega
    have half_sum (l : List ℝ) :
        (l.map (fun y => y / 2)).sum = l.sum / 2 := by
      induction l with
      | nil => simp
      | cons y ys ih => simp [ih]; ring
    have hmap : blocks.map List.sum = xs := by
      exact bisect_map_sums xs
    have hne : ∀ block ∈ blocks, block ≠ [] := by
      intro block hblock
      simp only [blocks, List.mem_map] at hblock
      rcases hblock with ⟨y, hy, rfl⟩
      simp
    have hpairs : ∀ y ∈ pairs, 0 ≤ y := by
      intro y hy
      simp only [pairs, List.mem_map] at hy
      rcases hy with ⟨z, hz, rfl⟩
      exact (div_pos (hpos z hz) (by norm_num)).le
    have hflat : blocks.flatten = pairs.flatMap (fun y => [y, y]) := by
      exact bisect_flatten xs
    have hflatpos : ∀ y ∈ blocks.flatten, 0 < y := by
      rw [hflat]
      intro y hy
      simp only [List.mem_flatMap] at hy
      rcases hy with ⟨z, hz, hy⟩
      have hyz : y = z := by simpa using hy
      subst y
      simp only [pairs, List.mem_map] at hz
      rcases hz with ⟨w, hw, rfl⟩
      exact div_pos (hpos w hw) (by norm_num)
    have hflatlen : blocks.flatten.length = 2 * xs.length := by
      exact bisect_length xs
    have hpairsum : pairs.sum = (1 : ℝ) / 2 := by
      rw [show pairs.sum = xs.sum / 2 by exact half_sum xs, hsum]
    refine ⟨blocks, hmap, hne, hflatpos, ?_, ?_⟩
    · rw [hflatlen]
      omega
    · rw [hflat]
      calc
        firstPlayerShare (pairs.flatMap (fun y => [y, y])) ≤ pairs.sum := by
          simpa using firstPlayerShare_pairs_residual_le pairs [] hpairs (by simp)
        _ = (1 : ℝ) / 2 := hpairsum
        _ ≤ answer n := half_le_answer
  · have hlength : xs.length = n + 1 := by omega
    have hmpos : 0 < xs.length := by omega
    let x : Fin xs.length → ℝ := xs.get
    have hx : ∀ i, 0 < x i := by
      intro i
      exact hpos (xs.get i) (List.get_mem xs i)
    have hxnonneg : ∀ i, 0 ≤ x i := fun i => (hx i).le
    have hxsum : (∑ i, x i) = 1 := by
      rw [← List.sum_ofFn, List.ofFn_get]
      exact hsum
    rcases closeSubsetSums xs.length hmpos x hxnonneg hxsum with
      ⟨U, V, hUV, hclose⟩
    let P : Finset (Fin xs.length) := U \ V
    let Q : Finset (Fin xs.length) := V \ U
    have hdisj : Disjoint P Q := by
      apply Finset.disjoint_left.mpr
      intro i hiP hiQ
      exact (Finset.mem_sdiff.mp hiP).2 (Finset.mem_sdiff.mp hiQ).1
    have hneSides : P.Nonempty ∨ Q.Nonempty := by
      by_cases hP : P.Nonempty
      · exact Or.inl hP
      · right
        by_contra hQ
        apply hUV
        apply Finset.Subset.antisymm
        · intro i hiU
          by_contra hiV
          exact hP ⟨i, Finset.mem_sdiff.mpr ⟨hiU, hiV⟩⟩
        · intro i hiV
          by_contra hiU
          exact hQ ⟨i, Finset.mem_sdiff.mpr ⟨hiV, hiU⟩⟩
    have hdiff :
        (∑ i ∈ P, x i) - (∑ i ∈ Q, x i) =
          (∑ i ∈ U, x i) - ∑ i ∈ V, x i := by
      have hU := Finset.sum_sdiff (Finset.inter_subset_left : U ∩ V ⊆ U)
          (f := x)
      have hV := Finset.sum_sdiff (Finset.inter_subset_right : U ∩ V ⊆ V)
          (f := x)
      change (∑ i ∈ U \ (U ∩ V), x i) + (∑ i ∈ U ∩ V, x i) =
          ∑ i ∈ U, x i at hU
      change (∑ i ∈ V \ (U ∩ V), x i) + (∑ i ∈ U ∩ V, x i) =
          ∑ i ∈ V, x i at hV
      have hPU : U \ (U ∩ V) = P := by
        ext i
        simp [P]
      have hQV : V \ (U ∩ V) = Q := by
        ext i
        simp [Q]
      rw [hPU] at hU
      rw [hQV] at hV
      linarith
    have hcloseSides :
        |(∑ i ∈ P, x i) - ∑ i ∈ Q, x i| ≤
          1 / ((2 : ℝ) ^ xs.length - 1) := by
      rw [hdiff]
      exact hclose
    by_cases horient : (∑ i ∈ Q, x i) ≤ ∑ i ∈ P, x i
    · rcases refinementFromDisjointSubsets x hx hxsum P Q hdisj hneSides
          horient with ⟨blocks, hmap, hne, hflatpos, hflatlen, hshare⟩
      refine ⟨blocks, ?_, hne, hflatpos, ?_, ?_⟩
      · simpa [x] using hmap
      · omega
      · calc
          firstPlayerShare blocks.flatten ≤
              (1 + ((∑ i ∈ P, x i) - ∑ i ∈ Q, x i)) / 2 := hshare
          _ ≤ (1 + 1 / ((2 : ℝ) ^ xs.length - 1)) / 2 := by
            rw [abs_of_nonneg (sub_nonneg.mpr horient)] at hcloseSides
            linarith
          _ = answer n := by
            rw [hlength]
            unfold answer
            have hden := geometricDen_pos n
            field_simp [ne_of_gt hden]
            rw [pow_succ]
            ring
    · have horient' : (∑ i ∈ P, x i) ≤ ∑ i ∈ Q, x i := le_of_not_ge horient
      rcases refinementFromDisjointSubsets x hx hxsum Q P hdisj.symm
          hneSides.symm horient' with
        ⟨blocks, hmap, hne, hflatpos, hflatlen, hshare⟩
      refine ⟨blocks, ?_, hne, hflatpos, ?_, ?_⟩
      · simpa [x] using hmap
      · omega
      · calc
          firstPlayerShare blocks.flatten ≤
              (1 + ((∑ i ∈ Q, x i) - ∑ i ∈ P, x i)) / 2 := hshare
          _ ≤ (1 + 1 / ((2 : ℝ) ^ xs.length - 1)) / 2 := by
            rw [abs_of_nonpos (sub_nonpos.mpr horient')] at hcloseSides
            linarith
          _ = answer n := by
            rw [hlength]
            unfold answer
            have hden := geometricDen_pos n
            field_simp [ne_of_gt hden]
            rw [pow_succ]
            ring
/-- The piece lengths of an admissible cut set sum to `1` (the total stick
length). -/
theorem pieceLengths_sum (S : Finset ℝ) (hS : ↑S ⊆ Set.Ioo (0 : ℝ) 1) :
    (pieceLengths S).sum = 1 := by
  have telescoping : ∀ (a b : ℝ) (xs : List ℝ),
      (List.zipWith (fun x y => y - x) (a :: xs ++ [b])
        (a :: xs ++ [b]).tail).sum = b - a := by
    intro a b xs
    induction xs generalizing a with
    | nil => simp
    | cons x xs ih =>
        simp only [List.cons_append, List.tail_cons, List.zipWith_cons_cons,
          List.sum_cons]
        have h : (List.zipWith (fun x y => y - x) (x :: (xs ++ [b]))
            (xs ++ [b])).sum = b - x := ih x
        rw [h]
        ring
  simpa [pieceLengths] using telescoping 0 1 (S.sort (· ≤ ·))
/-- There are `|S| + 1` pieces. -/
theorem pieceLengths_length (S : Finset ℝ) :
    (pieceLengths S).length = S.card + 1 := by
  simp [pieceLengths]
def cumulativeSumsFrom (a : ℝ) : List ℝ → List ℝ
  | [] => []
  | x :: xs => (a + x) :: cumulativeSumsFrom (a + x) xs
lemma cumulativeSumsFrom_append (a : ℝ) (xs ys : List ℝ) :
    cumulativeSumsFrom a (xs ++ ys) =
      cumulativeSumsFrom a xs ++ cumulativeSumsFrom (a + xs.sum) ys := by
  induction xs generalizing a with
  | nil => simp [cumulativeSumsFrom]
  | cons x xs ih =>
      simp only [List.cons_append, cumulativeSumsFrom, List.sum_cons,
        List.cons_append]
      rw [ih]
      congr 2
      ring_nf
lemma cumulativeSumsFrom_ne_nil (a : ℝ) (xs : List ℝ) :
    cumulativeSumsFrom a xs ≠ [] ↔ xs ≠ [] := by
  cases xs <;> simp [cumulativeSumsFrom]
lemma cumulativeSumsFrom_gt (a : ℝ) (xs : List ℝ)
    (hpos : ∀ x ∈ xs, 0 < x) (y : ℝ)
    (hy : y ∈ cumulativeSumsFrom a xs) : a < y := by
  induction xs generalizing a with
  | nil => simp [cumulativeSumsFrom] at hy
  | cons x xs ih =>
      simp only [cumulativeSumsFrom, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact lt_add_of_pos_right a (hpos x (by simp))
      · exact (lt_add_of_pos_right a (hpos x (by simp))).trans
          (ih (a + x) (fun z hz => hpos z (by simp [hz])) hy)
lemma cumulativeSumsFrom_pairwise (a : ℝ) (xs : List ℝ)
    (hpos : ∀ x ∈ xs, 0 < x) :
    (cumulativeSumsFrom a xs).Pairwise (· < ·) := by
  induction xs generalizing a with
  | nil => simp [cumulativeSumsFrom]
  | cons x xs ih =>
      rw [cumulativeSumsFrom, List.pairwise_cons]
      refine ⟨?_, ih (a + x) (fun z hz => hpos z (by simp [hz]))⟩
      intro y hy
      exact cumulativeSumsFrom_gt (a + x) xs
        (fun z hz => hpos z (by simp [hz])) y hy
lemma cumulativeSumsFrom_getLastOption (a : ℝ) (xs : List ℝ)
    (hxs : xs ≠ []) :
    (cumulativeSumsFrom a xs).getLast? = some (a + xs.sum) := by
  induction xs generalizing a with
  | nil => contradiction
  | cons x xs ih =>
      cases xs with
      | nil => simp [cumulativeSumsFrom]
      | cons y ys =>
          change ((a + x) :: cumulativeSumsFrom (a + x) (y :: ys)).getLast? =
            some (a + (x :: y :: ys).sum)
          rw [show cumulativeSumsFrom (a + x) (y :: ys) =
            ((a + x) + y) :: cumulativeSumsFrom ((a + x) + y) ys by rfl]
          rw [List.getLast?_cons_cons]
          have htail := ih (a + x) (by simp : y :: ys ≠ [])
          change (((a + x) + y) ::
            cumulativeSumsFrom ((a + x) + y) ys).getLast? =
              some ((a + x) + (y :: ys).sum) at htail
          rw [htail]
          congr 1
          simp only [List.sum_cons]
          ring
lemma cumulativeSumsFrom_getLastValue (a : ℝ) (xs : List ℝ)
    (hxs : xs ≠ []) :
    (cumulativeSumsFrom a xs).getLast
        ((cumulativeSumsFrom_ne_nil a xs).2 hxs) = a + xs.sum := by
  have h := cumulativeSumsFrom_getLastOption a xs hxs
  rw [List.getLast?_eq_getLast_of_ne_nil
    ((cumulativeSumsFrom_ne_nil a xs).2 hxs)] at h
  exact Option.some.inj h
lemma cumulativeSumsFrom_endpoint_mem (a : ℝ) (xs : List ℝ)
    (hxs : xs ≠ []) :
    a + xs.sum ∈ cumulativeSumsFrom a xs := by
  rw [← cumulativeSumsFrom_getLastValue a xs hxs]
  exact List.getLast_mem _
lemma cumulativeSumsFrom_dropLast_Ioo (a : ℝ) (xs : List ℝ)
    (hpos : ∀ x ∈ xs, 0 < x) (y : ℝ)
    (hy : y ∈ (cumulativeSumsFrom a xs).dropLast) :
    y ∈ Set.Ioo a (a + xs.sum) := by
  have hpair := cumulativeSumsFrom_pairwise a xs hpos
  have hyall : y ∈ cumulativeSumsFrom a xs := List.mem_of_mem_dropLast hy
  refine ⟨cumulativeSumsFrom_gt a xs hpos y hyall, ?_⟩
  have hlast :
      (cumulativeSumsFrom a xs).getLast (List.ne_nil_of_mem hyall) =
        a + xs.sum := by
    exact cumulativeSumsFrom_getLastValue a xs (by
      exact fun h => by subst xs; simp [cumulativeSumsFrom] at hyall)
  rw [← hlast]
  exact hpair.rel_dropLast_getLast hy
lemma cutDiffs_cumulativeSumsFrom_dropLast (a : ℝ) (xs : List ℝ)
    (hxs : xs ≠ []) :
    cutDiffs a (a + xs.sum) (cumulativeSumsFrom a xs).dropLast = xs := by
  induction xs generalizing a with
  | nil => contradiction
  | cons x xs ih =>
      cases xs with
      | nil => simp [cumulativeSumsFrom, cutDiffs]
      | cons y ys =>
          rw [show (cumulativeSumsFrom a (x :: y :: ys)).dropLast =
              (a + x) :: (cumulativeSumsFrom (a + x) (y :: ys)).dropLast by
            simp only [cumulativeSumsFrom]
            rw [List.dropLast_cons_of_ne_nil (by simp [cumulativeSumsFrom])]]
          rw [cutDiffs_cons]
          have htail := ih (a + x) (by simp : y :: ys ≠ [])
          congr 1
          · ring
          · rw [show a + (x :: y :: ys).sum =
                (a + x) + (y :: ys).sum by simp; ring]
            exact htail
lemma cumulativeSumsFrom_cutDiffs (a b : ℝ) (xs : List ℝ) :
    cumulativeSumsFrom a (cutDiffs a b xs) = xs ++ [b] := by
  induction xs generalizing a with
  | nil => simp [cutDiffs, cumulativeSumsFrom]
  | cons x xs ih =>
      rw [cutDiffs_cons]
      simp only [cumulativeSumsFrom]
      rw [show a + (x - a) = x by ring, ih x]
      rfl
lemma dropLast_append_right_ne_nil {α : Type*} (xs ys : List α)
    (hys : ys ≠ []) :
    (xs ++ ys).dropLast = xs ++ ys.dropLast := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.cons_append]
      rw [List.dropLast_cons_of_ne_nil (List.append_ne_nil_of_right_ne_nil xs hys)]
      simp [ih]
lemma cumulativeBlockBoundaries_subset (a : ℝ) (blocks : List (List ℝ))
    (hne : ∀ block ∈ blocks, block ≠ []) :
    ∀ y ∈ (cumulativeSumsFrom a (blocks.map List.sum)).dropLast,
      y ∈ (cumulativeSumsFrom a blocks.flatten).dropLast := by
  induction blocks generalizing a with
  | nil => simp [cumulativeSumsFrom]
  | cons block blocks ih =>
      cases blocks with
      | nil => simp [cumulativeSumsFrom]
      | cons next rest =>
          have hblock : block ≠ [] := hne block (by simp)
          have htail : ∀ u ∈ next :: rest, u ≠ [] := by
            intro u hu
            exact hne u (by simp [hu])
          have hflat : (next :: rest).flatten ≠ [] := by
            simp [htail next (by simp)]
          intro y hy
          simp only [List.map_cons, cumulativeSumsFrom] at hy
          rw [List.dropLast_cons_of_ne_nil (by simp [cumulativeSumsFrom])] at hy
          have hcumflat :
              cumulativeSumsFrom (a + block.sum) (next :: rest).flatten ≠ [] :=
            (cumulativeSumsFrom_ne_nil _ _).2 hflat
          rw [List.flatten_cons, cumulativeSumsFrom_append,
            dropLast_append_right_ne_nil _ _ hcumflat]
          rcases List.mem_cons.mp hy with rfl | hy
          · apply List.mem_append_left
            exact cumulativeSumsFrom_endpoint_mem a block hblock
          · apply List.mem_append_right
            exact ih (a + block.sum) htail _ hy
theorem positiveRefinementCutSet
    (A : Finset ℝ) (blocks : List (List ℝ))
    (hA : (↑A : Set ℝ) ⊆ Set.Ioo (0 : ℝ) 1)
    (hblocks : blocks.map List.sum = pieceLengths A)
    (hne : ∀ block : List ℝ, block ∈ blocks → block ≠ [])
    (hpos : ∀ x : ℝ, x ∈ blocks.flatten → 0 < x) :
    ∃ C : Finset ℝ,
      A ⊆ C ∧
      (↑C : Set ℝ) ⊆ Set.Ioo (0 : ℝ) 1 ∧
      C.card + 1 = blocks.flatten.length ∧
      pieceLengths C = blocks.flatten := by
  let xs := blocks.flatten
  let cuts := (cumulativeSumsFrom 0 xs).dropLast
  let C : Finset ℝ := cuts.toFinset
  have hxsum : xs.sum = 1 := by
    calc
      xs.sum = (blocks.map List.sum).sum := sum_flatten_eq_map_sum blocks
      _ = (pieceLengths A).sum := congrArg List.sum hblocks
      _ = 1 := pieceLengths_sum A hA
  have hxne : xs ≠ [] := by
    intro h
    rw [h] at hxsum
    norm_num at hxsum
  have hcumPair : (cumulativeSumsFrom 0 xs).Pairwise (· < ·) :=
    cumulativeSumsFrom_pairwise 0 xs hpos
  have hcutsPair : cuts.Pairwise (· < ·) := by
    exact hcumPair.sublist (List.dropLast_sublist _)
  have hsort : C.sort (· ≤ ·) = cuts := by
    exact (List.toFinset_sort (· ≤ ·) hcutsPair.nodup).2
      (hcutsPair.imp fun h => h.le)
  have hCint : (↑C : Set ℝ) ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro y hy
    have hycuts : y ∈ cuts := by
      simpa [C] using hy
    have hi := cumulativeSumsFrom_dropLast_Ioo 0 xs hpos y (by
      simpa only [cuts] using hycuts)
    simpa [hxsum] using hi
  have hCpieces : pieceLengths C = xs := by
    change cutDiffs 0 1 (C.sort (· ≤ ·)) = xs
    rw [hsort]
    have h := cutDiffs_cumulativeSumsFrom_dropLast 0 xs hxne
    simpa [cuts, hxsum] using h
  have hAcumulative :
      (cumulativeSumsFrom 0 (pieceLengths A)).dropLast = A.sort (· ≤ ·) := by
    change (cumulativeSumsFrom 0
      (cutDiffs 0 1 (A.sort (· ≤ ·)))).dropLast = A.sort (· ≤ ·)
    rw [cumulativeSumsFrom_cutDiffs]
    simp
  have hAC : A ⊆ C := by
    intro y hy
    have hysort : y ∈ A.sort (· ≤ ·) := by simpa using hy
    have hyblocks :
        y ∈ (cumulativeSumsFrom 0 (blocks.map List.sum)).dropLast := by
      rw [hblocks, hAcumulative]
      exact hysort
    have hycuts := cumulativeBlockBoundaries_subset 0 blocks hne y hyblocks
    simpa [C, cuts, xs] using hycuts
  have hCcard : C.card + 1 = xs.length := by
    rw [← pieceLengths_length C, hCpieces]
  exact ⟨C, hAC, hCint, by simpa [xs] using hCcard, by simpa [xs] using hCpieces⟩
theorem pieceLengthsRefinementRealizable
    (A : Finset ℝ) (blocks : List (List ℝ))
    (hA : (↑A : Set ℝ) ⊆ Set.Ioo (0 : ℝ) 1)
    (hblocks : blocks.map List.sum = pieceLengths A)
    (hne : ∀ block : List ℝ, block ∈ blocks → block ≠ [])
    (hpos : ∀ x : ℝ, x ∈ blocks.flatten → 0 < x) :
    ∃ B : Finset ℝ,
      (↑B : Set ℝ) ⊆ Set.Ioo (0 : ℝ) 1 ∧
      Disjoint A B ∧
      B.card + blocks.length = blocks.flatten.length ∧
      pieceLengths (A ∪ B) = blocks.flatten := by
  rcases positiveRefinementCutSet A blocks hA hblocks hne hpos with
    ⟨C, hAC, hCint, hCcard, hCpieces⟩
  let B : Finset ℝ := C \ A
  have hBint : (↑B : Set ℝ) ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro y hy
    apply hCint
    change y ∈ C \ A at hy
    exact (Finset.mem_sdiff.mp hy).1
  have hdisj : Disjoint A B := Finset.disjoint_sdiff
  have hunion : A ∪ B = C := Finset.union_sdiff_of_subset hAC
  have hblockslen : blocks.length = A.card + 1 := by
    have h := congrArg List.length hblocks
    simpa [pieceLengths_length] using h
  have hdiffcard : B.card + A.card = C.card := by
    have h := Finset.card_sdiff_add_card C A
    rw [Finset.union_eq_left.mpr hAC] at h
    exact h
  refine ⟨B, hBint, hdisj, ?_, ?_⟩
  · omega
  · rw [hunion, hCpieces]
/-- Basic sanity bound: Liu Bang's share lies in `[0, 1]` for admissible cut
sets (it is a subset-sum of the piece lengths, which are nonnegative and sum to
`1`). -/
theorem L_mem_Icc (A B : Finset ℝ)
    (hA : ↑A ⊆ Set.Ioo (0 : ℝ) 1) (hB : ↑B ⊆ Set.Ioo (0 : ℝ) 1) :
    L A B ∈ Set.Icc (0 : ℝ) 1 := by
  have hAB : (↑(A ∪ B) : Set ℝ) ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro x hx
    simp only [Finset.mem_coe, Finset.mem_union] at hx
    exact hx.elim (fun hxA => hA (by simpa using hxA))
      (fun hxB => hB (by simpa using hxB))
  exact firstPlayerShare_mem_Icc (pieceLengths (A ∪ B))
    (pieceLengths_nonneg (A ∪ B) hAB) (pieceLengths_sum (A ∪ B) hAB)
/-! ## Main Statements -/

theorem lowerStrategyCore_of_inputs
    (hrefine : ∀ (A B : Finset ℝ),
      (↑A : Set ℝ) ⊆ Set.Ioo (0 : ℝ) 1 →
      (↑B : Set ℝ) ⊆ Set.Ioo (0 : ℝ) 1 →
      Disjoint A B →
      ∃ blocks : List (List ℝ),
        blocks.map List.sum = pieceLengths A ∧
        blocks.flatten.Perm (pieceLengths (A ∪ B)) ∧
        blocks.flatten.length ≤ blocks.length + B.card ∧
        ∀ x : ℝ, x ∈ blocks.flatten → 0 ≤ x)
    (hshare : ∀ (n : ℕ) (c : ℝ) (blocks : List (List ℝ)),
      0 ≤ c →
      blocks.map List.sum =
        (List.range (n + 1)).map (fun i => c * (2 : ℝ) ^ (n - i)) →
      (∀ x : ℝ, x ∈ blocks.flatten → 0 ≤ x) →
      blocks.flatten.length ≤ 2 * n + 1 →
      c * (2 : ℝ) ^ n ≤ firstPlayerShare blocks.flatten)
    (n : ℕ) (hn : 0 < n) :
    ∃ A : Finset ℝ, AdmissibleMark n A ∧
      ∀ B : Finset ℝ, AdmissibleMark n B → Disjoint A B →
        answer n ≤ L A B := by
  let d : ℝ := (2 : ℝ) ^ (n + 1) - 1
  let A : Finset ℝ := (Finset.range n).image (fun k =>
    (∑ j ∈ Finset.range (k + 1), (2 : ℝ) ^ (n - j)) / d)
  have hspec : AdmissibleMark n A ∧
      pieceLengths A = (List.range (n + 1)).map
        (fun i => (1 / d) * (2 : ℝ) ^ (n - i)) := by
    simpa only [d, A] using geometricMarks_spec n hn
  refine ⟨A, hspec.1, ?_⟩
  intro B hB hdisj
  rcases hrefine A B hspec.1.1 hB.1 hdisj with
    ⟨blocks, hblocks, hperm, hlength, hnonneg⟩
  have hblocks_length : blocks.length = n + 1 := by
    have := congrArg List.length (hblocks.trans hspec.2)
    simpa using this
  have hflatten_length : blocks.flatten.length ≤ 2 * n + 1 := by
    calc
      blocks.flatten.length ≤ blocks.length + B.card := hlength
      _ = n + 1 + B.card := by rw [hblocks_length]
      _ ≤ n + 1 + n := Nat.add_le_add_left hB.2 (n + 1)
      _ = 2 * n + 1 := by omega
  have hc : 0 ≤ (1 / d : ℝ) :=
    (one_div_pos.mpr (by simpa only [d] using geometricDen_pos n)).le
  have hgeometric :
      (1 / d) * (2 : ℝ) ^ n ≤ firstPlayerShare blocks.flatten :=
    hshare n (1 / d) blocks hc (hblocks.trans hspec.2) hnonneg
      hflatten_length
  have htransport := firstPlayerShare_eq_of_perm blocks.flatten
    (pieceLengths (A ∪ B)) hperm
  rw [htransport] at hgeometric
  simpa only [answer, L, d, div_eq_mul_inv, one_mul, mul_comm] using hgeometric
theorem lowerStrategyCore (n : ℕ) (hn : 0 < n) :
    ∃ A : Finset ℝ, AdmissibleMark n A ∧
      ∀ B : Finset ℝ, AdmissibleMark n B → Disjoint A B →
        answer n ≤ L A B := by
  exact lowerStrategyCore_of_inputs pieceLengths_union_refines
    geometric_refinement_share n hn
theorem upperResponseCore (n : ℕ) (hn : 0 < n) :
    ∀ A : Finset ℝ, AdmissibleMark n A →
      ∃ B : Finset ℝ, AdmissibleMark n B ∧ Disjoint A B ∧
        L A B ≤ answer n := by
  intro A hA
  rcases hA with ⟨hAint, hAcard⟩
  have hlength : (pieceLengths A).length ≤ n + 1 := by
    rw [pieceLengths_length]
    omega
  rcases upperRefinementBlocks n (pieceLengths A) hn
      (pieceLengths_pos A hAint) (pieceLengths_sum A hAint) hlength with
    ⟨blocks, hmap, hne, hflatpos, hflatlen, hshare⟩
  rcases pieceLengthsRefinementRealizable A blocks hAint hmap hne hflatpos with
    ⟨B, hBint, hdisjoint, hcard, hpieces⟩
  refine ⟨B, ⟨hBint, ?_⟩, hdisjoint, ?_⟩
  · have hblockslen : blocks.length = (pieceLengths A).length := by
      simpa using congrArg List.length hmap
    omega
  · unfold L
    rw [hpieces]
    exact hshare
lemma V_eq_of_strategy_bounds (n : ℕ)
    (hlower : ∃ A : Finset ℝ, AdmissibleMark n A ∧
      ∀ B : Finset ℝ, AdmissibleMark n B → Disjoint A B → answer n ≤ L A B)
    (hupper : ∀ A : Finset ℝ, AdmissibleMark n A →
      ∃ B : Finset ℝ, AdmissibleMark n B ∧ Disjoint A B ∧ L A B ≤ answer n) :
    V n = answer n := by
  unfold V
  let A₀ : {A : Finset ℝ // AdmissibleMark n A} :=
    ⟨∅, by simp [AdmissibleMark]⟩
  letI : Nonempty {A : Finset ℝ // AdmissibleMark n A} := ⟨A₀⟩
  apply le_antisymm
  · apply ciSup_le
    intro A
    rcases hupper A.1 A.2 with ⟨B, hB, hdisj, hle⟩
    let B' : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B} :=
      ⟨B, hB, hdisj⟩
    have hbdd : BddBelow (Set.range fun B'' :
        {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B} => L A.1 B''.1) := by
      rw [bddBelow_def]
      refine ⟨0, ?_⟩
      rintro y ⟨B'', rfl⟩
      exact (L_mem_Icc A.1 B''.1 A.2.1 B''.2.1.1).1
    exact ciInf_le_of_le hbdd B' hle
  · rcases hlower with ⟨A, hA, hle⟩
    let A' : {A : Finset ℝ // AdmissibleMark n A} := ⟨A, hA⟩
    have hbddOuter : BddAbove (Set.range fun A'' :
        {A : Finset ℝ // AdmissibleMark n A} =>
          ⨅ B : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A''.1 B},
            L A''.1 B.1) := by
      rw [bddAbove_def]
      refine ⟨1, ?_⟩
      rintro y ⟨A'', rfl⟩
      let B₀ : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A''.1 B} :=
        ⟨∅, by simp [AdmissibleMark]⟩
      have hbdd : BddBelow (Set.range fun B'' :
          {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A''.1 B} =>
            L A''.1 B''.1) := by
        rw [bddBelow_def]
        refine ⟨0, ?_⟩
        rintro z ⟨B'', rfl⟩
        exact (L_mem_Icc A''.1 B''.1 A''.2.1 B''.2.1.1).1
      exact (ciInf_le hbdd B₀).trans
        (L_mem_Icc A''.1 B₀.1 A''.2.1 B₀.2.1.1).2
    apply le_ciSup_of_le hbddOuter A'
    let B₀ : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A'.1 B} :=
      ⟨∅, by simp [AdmissibleMark]⟩
    letI : Nonempty {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A'.1 B} :=
      ⟨B₀⟩
    apply le_ciInf
    intro B
    exact hle B.1 B.2.1 B.2.2
/-- **Main statement.** For every positive integer `n`, Liu Bang's guaranteed
value equals `2^n / (2^(n+1) - 1)`. -/
theorem V_eq (n : ℕ) (hn : 0 < n) : V n = (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1) := by
  simpa only [answer] using
    V_eq_of_strategy_bounds n (lowerStrategyCore n hn) (upperResponseCore n hn)
/-- **Lower bound.** Liu Bang has an admissible marking `A` such that for every
admissible marking `B` disjoint from `A`, his guaranteed share is at least
`2^n / (2^(n+1) - 1)`. -/
theorem lower_bound (n : ℕ) (hn : 0 < n) :
    ∃ A : Finset ℝ, AdmissibleMark n A ∧
      ∀ B : Finset ℝ, AdmissibleMark n B → Disjoint A B →
        (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1) ≤ L A B := by
  simpa only [answer] using lowerStrategyCore n hn
/-- **Upper bound / optimality.** For every admissible marking `A` of Liu Bang,
Xiang Yu has an admissible marking `B` disjoint from `A` with
`L A B ≤ 2^n / (2^(n+1) - 1)`, so Liu Bang cannot guarantee more. -/
theorem upper_bound (n : ℕ) (hn : 0 < n) :
    ∀ A : Finset ℝ, AdmissibleMark n A →
      ∃ B : Finset ℝ, AdmissibleMark n B ∧ Disjoint A B ∧
        L A B ≤ (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1) := by
  simpa only [answer] using upperResponseCore n hn
end LiuBangXiangYu
