import Mathlib
set_option backward.isDefEq.respectTransparency false

/-- The predicate stating that `a : ℕ → ℕ` (0-indexed) is a sequence satisfying Definition 1:
each term exceeds `1`, and each subsequent term is the smallest integer strictly larger than the
previous one that shares a common factor with every earlier term. -/
def IsValidSeq (a : ℕ → ℕ) : Prop :=
  (∀ n, 1 < a n) ∧
  (∀ n, a n < a (n + 1) ∧
        (∀ i ≤ n, 1 < Nat.gcd (a (n + 1)) (a i)) ∧
        (∀ b, a n < b → b < a (n + 1) → ∃ i ≤ n, Nat.gcd b (a i) = 1))

theorem validSeq_uniform_gap :
    ∀ (a : ℕ → ℕ), IsValidSeq a →
      ∃ R : ℕ, 0 < R ∧ ∀ n : ℕ, a (n + 1) ≤ a n + R := by
  intro a ha
  refine ⟨a 0, ?_, ?_⟩
  · exact lt_trans Nat.zero_lt_one (ha.1 0)
  · have hzero : ∀ i : ℕ, 1 < Nat.gcd (a 0) (a i) := by
      intro i
      cases i with
      | zero => simpa using ha.1 0
      | succ i =>
          simpa [Nat.succ_eq_add_one, Nat.gcd_comm] using
            (ha.2 i).2.1 0 (Nat.zero_le i)
    intro n
    let b := a 0 * (a n / a 0 + 1)
    have hmod : a n % a 0 < a 0 :=
      Nat.mod_lt _ (lt_trans Nat.zero_lt_one (ha.1 0))
    have hdiv : a 0 * (a n / a 0) + a n % a 0 = a n :=
      Nat.div_add_mod _ _
    have hnb : a n < b := by
      dsimp [b]
      rw [Nat.mul_add]
      omega
    have hb_le : b ≤ a n + a 0 := by
      dsimp [b]
      rw [Nat.mul_add]
      omega
    by_contra hgap
    have hsum_lt : a n + a 0 < a (n + 1) := Nat.lt_of_not_ge hgap
    have hb_lt : b < a (n + 1) := lt_of_le_of_lt hb_le hsum_lt
    obtain ⟨i, hi, hcoprime⟩ := (ha.2 n).2.2 b hnb hb_lt
    have ha0_dvd_b : a 0 ∣ b := by
      refine ⟨a n / a 0 + 1, ?_⟩
      simp [b]
    have hcommon_dvd : Nat.gcd (a 0) (a i) ∣ Nat.gcd b (a i) :=
      Nat.dvd_gcd (Nat.dvd_trans (Nat.gcd_dvd_left _ _) ha0_dvd_b)
        (Nat.gcd_dvd_right _ _)
    rw [hcoprime] at hcommon_dvd
    have : Nat.gcd (a 0) (a i) = 1 := Nat.dvd_one.mp hcommon_dvd
    have := hzero i
    omega
theorem validSeq_contains_universally_compatible :
    ∀ (a : ℕ → ℕ), IsValidSeq a → ∀ b : ℕ, a 0 ≤ b →
      (∀ i : ℕ, 1 < Nat.gcd b (a i)) → ∃ n : ℕ, a n = b := by
  intro a ha b hab hcompat
  have hgrowth : ∀ n : ℕ, n < a n := by
    intro n
    induction n with
    | zero => exact lt_trans Nat.zero_lt_one (ha.1 0)
    | succ n ih =>
        have hstep := (ha.2 n).1
        omega
  have hex : ∃ n : ℕ, b < a (n + 1) := by
    exact ⟨b, by have := hgrowth (b + 1); omega⟩
  let n := Nat.find hex
  have hn_lt : b < a (n + 1) := Nat.find_spec hex
  have hn_le : a n ≤ b := by
    by_cases hn : n = 0
    · simpa [hn] using hab
    · have hpred : n - 1 < n := Nat.sub_lt (Nat.zero_lt_of_ne_zero hn) Nat.zero_lt_one
      have hnot : ¬b < a ((n - 1) + 1) := Nat.find_min hex hpred
      simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)] using Nat.le_of_not_gt hnot
  by_cases hnb : a n = b
  · exact ⟨n, hnb⟩
  · have hn_strict : a n < b := lt_of_le_of_ne hn_le hnb
    obtain ⟨i, hi, hcoprime⟩ := (ha.2 n).2.2 b hn_strict hn_lt
    have := hcompat i
    omega
def SeqSupportMinimal (a : ℕ → ℕ) (i : ℕ) : Prop :=
  ∀ j : ℕ, (a j).primeFactors ⊆ (a i).primeFactors →
    (a i).primeFactors ⊆ (a j).primeFactors
def supportProd (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p
lemma validSeq_pairwise_gcd (a : ℕ → ℕ) (ha : IsValidSeq a) (i j : ℕ) :
    1 < Nat.gcd (a i) (a j) := by
  by_cases hij : i = j
  · subst j
    simpa using ha.1 i
  wlog hlt : i < j generalizing i j
  · rw [Nat.gcd_comm]
    exact this j i (Ne.symm hij) (by omega)
  have hj : 0 < j := by omega
  have hidx : j - 1 + 1 = j := Nat.sub_add_cancel hj
  simpa [hidx, Nat.gcd_comm] using (ha.2 (j - 1)).2.1 i (by omega)
lemma validSeq_rejected_has_earlier_coprime (a : ℕ → ℕ) (ha : IsValidSeq a)
    (b : ℕ) (hab : a 0 < b) (hmiss : ∀ n : ℕ, a n ≠ b) :
    ∃ i : ℕ, a i < b ∧ Nat.gcd b (a i) = 1 := by
  have hgrowth : ∀ n : ℕ, n < a n := by
    intro n
    induction n with
    | zero => exact lt_trans Nat.zero_lt_one (ha.1 0)
    | succ n ih =>
        have hstep := (ha.2 n).1
        omega
  have hex : ∃ n : ℕ, b < a (n + 1) := by
    exact ⟨b, by have := hgrowth (b + 1); omega⟩
  let n := Nat.find hex
  have hn_lt : b < a (n + 1) := Nat.find_spec hex
  have hn_le : a n ≤ b := by
    by_cases hn : n = 0
    · simpa [hn] using hab.le
    · have hpred : n - 1 < n := Nat.sub_lt (Nat.zero_lt_of_ne_zero hn) Nat.zero_lt_one
      have hnot : ¬b < a ((n - 1) + 1) := Nat.find_min hex hpred
      simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)] using Nat.le_of_not_gt hnot
  have hn_strict : a n < b := lt_of_le_of_ne hn_le (hmiss n)
  obtain ⟨i, hi, hcoprime⟩ := (ha.2 n).2.2 b hn_strict hn_lt
  have hmono : StrictMono a := strictMono_nat_of_lt_succ (fun k => (ha.2 k).1)
  exact ⟨i, lt_of_le_of_lt (hmono.monotone hi) hn_strict, hcoprime⟩
theorem validSeq_smaller_coprime_witness :
    ∀ (a : ℕ → ℕ), IsValidSeq a → ∀ b : ℕ, a 0 < b →
      (∃ n : ℕ, Nat.gcd b (a n) = 1) →
        ∃ i : ℕ, a i < b ∧ Nat.gcd b (a i) = 1 := by
  intro a ha b hab hcoprime
  obtain ⟨n, hn⟩ := hcoprime
  have hmiss : ∀ k : ℕ, a k ≠ b := by
    intro k hk
    have hpair := validSeq_pairwise_gcd a ha k n
    rw [hk] at hpair
    omega
  exact validSeq_rejected_has_earlier_coprime a ha b hab hmiss
lemma exists_minimal_support_subset (a : ℕ → ℕ) (n : ℕ) :
    ∃ i : ℕ, (a i).primeFactors ⊆ (a n).primeFactors ∧ SeqSupportMinimal a i := by
  classical
  let P : ℕ → Prop := fun k => ∃ i : ℕ,
    (a i).primeFactors ⊆ (a n).primeFactors ∧ (a i).primeFactors.card = k
  have hex : ∃ k, P k := ⟨(a n).primeFactors.card, n, Finset.Subset.rfl, rfl⟩
  obtain ⟨i, hin, hicard⟩ := Nat.find_spec hex
  refine ⟨i, hin, ?_⟩
  intro j hji
  by_contra hnsub
  have hss : (a j).primeFactors ⊂ (a i).primeFactors :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hji, by
      intro heq
      exact hnsub (heq ▸ Finset.Subset.rfl)⟩
  have hcard : (a j).primeFactors.card < (a i).primeFactors.card :=
    Finset.card_lt_card hss
  have hjP : P (a j).primeFactors.card :=
    ⟨j, hji.trans hin, rfl⟩
  have hmin := Nat.find_min' hex hjP
  omega
lemma prod_primeFactors_le (a : ℕ → ℕ) (ha : IsValidSeq a) (i : ℕ) :
    supportProd (a i) ≤ a i := by
  unfold supportProd
  exact Nat.le_of_dvd (Nat.zero_lt_of_lt (ha.1 i)) (Nat.prod_primeFactors_dvd (a i))
lemma primeFactors_supportProd (n : ℕ) :
    (supportProd n).primeFactors = n.primeFactors := by
  unfold supportProd
  exact Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors hp)
lemma exists_common_prime_of_valid (a : ℕ → ℕ) (ha : IsValidSeq a) (i j : ℕ) :
    ∃ p : ℕ, p ∈ (a i).primeFactors ∧ p ∈ (a j).primeFactors := by
  have hgcd := validSeq_pairwise_gcd a ha i j
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (by omega : Nat.gcd (a i) (a j) ≠ 1)
  refine ⟨p, ?_, ?_⟩
  · exact hp.mem_primeFactors
      (hpdvd.trans (Nat.gcd_dvd_left (a i) (a j)))
      (Nat.ne_of_gt (Nat.zero_lt_of_lt (ha.1 i)))
  · exact hp.mem_primeFactors
      (hpdvd.trans (Nat.gcd_dvd_right (a i) (a j)))
      (Nat.ne_of_gt (Nat.zero_lt_of_lt (ha.1 j)))
lemma minimal_support_prime_bound (a : ℕ → ℕ) (ha : IsValidSeq a) (i p : ℕ)
    (hmin : SeqSupportMinimal a i) (hp : p ∈ (a i).primeFactors) :
    p < (a 0) ^ (a 0 + 1) := by
  classical
  by_cases hp_small : p ≤ a 0
  · exact hp_small.trans_lt <| (Nat.lt_pow_self (ha.1 0)).trans_le <|
      Nat.pow_le_pow_right (Nat.zero_lt_of_lt (ha.1 0)) (Nat.le_succ _)
  let P : ℕ → Prop := fun r => ∃ e : ℕ,
    SeqSupportMinimal a e ∧ p ∈ (a e).primeFactors ∧ supportProd (a e) = r
  have hex : ∃ r, P r := ⟨supportProd (a i), i, hmin, hp, rfl⟩
  obtain ⟨e, he_min, hp_e, he_prod⟩ := Nat.find_spec hex
  let E := (a e).primeFactors
  let B := E.erase p
  let q := ∏ x ∈ B, x
  have hE : insert p B = E := Finset.insert_erase hp_e
  have hq_support : q.primeFactors = B := by
    dsimp [q]
    exact Nat.primeFactors_prod (fun x hx =>
      Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hx))
  have heq_prod : supportProd (a e) = p * q := by
    dsimp [supportProd, q, B, E]
    exact (Finset.mul_prod_erase (a e).primeFactors id hp_e).symm
  have hq_le : q ≤ a 0 := by
    by_contra hq
    have haq : a 0 < q := Nat.lt_of_not_ge hq
    have hmiss : ∀ k : ℕ, a k ≠ q := by
      intro k hak
      have hkE : (a k).primeFactors ⊆ (a e).primeFactors := by
        rw [hak, hq_support]
        exact Finset.erase_subset _ _
      have hEk := he_min k hkE
      rw [hak, hq_support] at hEk
      have : p ∈ B := hEk hp_e
      exact (Finset.notMem_erase p E) this
    obtain ⟨j, haj, hcoprime⟩ :=
      validSeq_rejected_has_earlier_coprime a ha q haq hmiss
    obtain ⟨k, hkj, hk_min⟩ := exists_minimal_support_subset a j
    obtain ⟨x, hxe, hxk⟩ := exists_common_prime_of_valid a ha e k
    have hdisj : Disjoint B (a j).primeFactors := by
      rw [← hq_support]
      exact (Nat.disjoint_primeFactors
        (Nat.ne_of_gt (lt_trans (Nat.zero_lt_of_lt (ha.1 0)) haq))
        (Nat.ne_of_gt (Nat.zero_lt_of_lt (ha.1 j)))).mpr
        (Nat.coprime_iff_gcd_eq_one.mpr hcoprime)
    have hx_not_B : x ∉ B := by
      exact fun hxb => (Finset.disjoint_left.mp hdisj hxb) (hkj hxk)
    have hxp : x = p := by
      have hx_insert : x ∈ insert p B := hE.symm ▸ hxe
      simpa [hx_not_B] using hx_insert
    have hp_k : p ∈ (a k).primeFactors := hxp ▸ hxk
    have hkP : P (supportProd (a k)) := ⟨k, hk_min, hp_k, rfl⟩
    have hleast : Nat.find hex ≤ supportProd (a k) := Nat.find_min' hex hkP
    have hprod_sub : supportProd (a k) ≤ supportProd (a j) := by
      unfold supportProd
      exact Finset.prod_le_prod_of_subset_of_one_le' hkj (fun x hx hxk =>
        (Nat.prime_of_mem_primeFactors hx).one_le)
    have hk_lt : supportProd (a k) < q :=
      lt_of_le_of_lt (hprod_sub.trans (prod_primeFactors_le a ha j)) haj
    have hq_pos : 0 < q := by
      dsimp [q]
      exact Finset.prod_pos (fun x hx =>
        Nat.pos_of_mem_primeFactors (Finset.mem_of_mem_erase hx))
    have hp_two : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp_e).two_le
    have hfind : Nat.find hex = p * q := he_prod.symm.trans heq_prod
    rw [hfind] at hleast
    nlinarith
  have hB_nonempty : B.Nonempty := by
    by_contra hB
    have hB_empty : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    obtain ⟨x, hxe, hx0⟩ := exists_common_prime_of_valid a ha e 0
    have hxp : x = p := by
      have hx_insert : x ∈ insert p B := hE.symm ▸ hxe
      simpa [hB_empty] using hx_insert
    have hp_dvd : p ∣ a 0 := Nat.dvd_of_mem_primeFactors (hxp ▸ hx0)
    exact hp_small (Nat.le_of_dvd (Nat.zero_lt_of_lt (ha.1 0)) hp_dvd)
  have hq_two : 2 ≤ q := by
    obtain ⟨x, hxB⟩ := hB_nonempty
    have hxprime : x.Prime :=
      Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hxB)
    have hxdvd : x ∣ q := by
      dsimp [q]
      exact Finset.dvd_prod_of_mem id hxB
    exact hxprime.two_le.trans (Nat.le_of_dvd (by
      dsimp [q]
      exact Finset.prod_pos (fun y hy =>
        Nat.pos_of_mem_primeFactors (Finset.mem_of_mem_erase hy))) hxdvd)
  let c := q ^ (a 0 + 1)
  have hac : a 0 < c := by
    have hpow : 2 ^ (a 0 + 1) ≤ c := Nat.pow_le_pow_left hq_two _
    exact Nat.lt_two_pow_self.trans_le ((by gcongr <;> omega :
      2 ^ a 0 ≤ 2 ^ (a 0 + 1)).trans hpow)
  have hc_support : c.primeFactors = B := by
    dsimp [c]
    rw [Nat.primeFactors_pow q (by omega), hq_support]
  have hmiss : ∀ k : ℕ, a k ≠ c := by
    intro k hak
    have hkE : (a k).primeFactors ⊆ (a e).primeFactors := by
      rw [hak, hc_support]
      exact Finset.erase_subset _ _
    have hEk := he_min k hkE
    rw [hak, hc_support] at hEk
    have : p ∈ B := hEk hp_e
    exact (Finset.notMem_erase p E) this
  obtain ⟨j, haj, hcoprime⟩ :=
    validSeq_rejected_has_earlier_coprime a ha c hac hmiss
  obtain ⟨x, hxe, hxj⟩ := exists_common_prime_of_valid a ha e j
  have hdisj : Disjoint B (a j).primeFactors := by
    rw [← hc_support]
    exact (Nat.disjoint_primeFactors
      (Nat.ne_of_gt (lt_trans (Nat.zero_lt_of_lt (ha.1 0)) hac))
      (Nat.ne_of_gt (Nat.zero_lt_of_lt (ha.1 j)))).mpr
      (Nat.coprime_iff_gcd_eq_one.mpr hcoprime)
  have hx_not_B : x ∉ B := fun hxb => (Finset.disjoint_left.mp hdisj hxb) hxj
  have hxp : x = p := by
    have hx_insert : x ∈ insert p B := hE.symm ▸ hxe
    simpa [hx_not_B] using hx_insert
  have hp_le_aj : p ≤ a j := Nat.le_of_dvd (Nat.zero_lt_of_lt (ha.1 j))
    (Nat.dvd_of_mem_primeFactors (hxp ▸ hxj))
  have hc_bound : c ≤ (a 0) ^ (a 0 + 1) := Nat.pow_le_pow_left hq_le _
  exact hp_le_aj.trans_lt (haj.trans_le hc_bound)
theorem validSeq_finite_prime_basis :
    ∀ (a : ℕ → ℕ), IsValidSeq a →
      ∃ N : ℕ, ∀ n : ℕ, ∃ i : ℕ, i ≤ N ∧
        ∀ p : ℕ, p.Prime → p ∣ a i → p ∣ a n := by
  classical
  intro a ha
  let M := (a 0) ^ (a 0 + 1)
  let N := (M ^ M) ^ (a 0 + 1)
  refine ⟨N, ?_⟩
  intro n
  obtain ⟨i, hin, hi_min⟩ := exists_minimal_support_subset a n
  let r := supportProd (a i)
  let b := r ^ (a 0 + 1)
  have hM_pos : 0 < M := by
    dsimp [M]
    exact Nat.pow_pos (Nat.zero_lt_of_lt (ha.1 0))
  have hs_range : (a i).primeFactors ⊆ Finset.range M := by
    intro p hp
    exact Finset.mem_range.mpr (minimal_support_prime_bound a ha i p hi_min hp)
  have hcard : (a i).primeFactors.card ≤ M := by
    simpa using Finset.card_le_card hs_range
  have hr_bound : r ≤ M ^ M := by
    calc
      r = ∏ p ∈ (a i).primeFactors, p := rfl
      _ ≤ ∏ _p ∈ (a i).primeFactors, M := by
        apply Finset.prod_le_prod
        · simp
        · intro p hp
          exact (Finset.mem_range.mp (hs_range hp)).le
      _ = M ^ (a i).primeFactors.card := Finset.prod_const M
      _ ≤ M ^ M := Nat.pow_le_pow_right hM_pos hcard
  obtain ⟨p, hp_prime, hp_dvd⟩ :=
    Nat.exists_prime_and_dvd (Nat.ne_of_gt (ha.1 i))
  have hp_mem : p ∈ (a i).primeFactors :=
    hp_prime.mem_primeFactors hp_dvd (Nat.ne_of_gt (Nat.zero_lt_of_lt (ha.1 i)))
  have hr_pos : 0 < r := by
    dsimp [r, supportProd]
    exact Finset.prod_pos (fun q hq => Nat.pos_of_mem_primeFactors hq)
  have hp_dvd_r : p ∣ r := by
    dsimp [r, supportProd]
    exact Finset.dvd_prod_of_mem id hp_mem
  have hr_two : 2 ≤ r :=
    hp_prime.two_le.trans (Nat.le_of_dvd hr_pos hp_dvd_r)
  have hab : a 0 ≤ b := by
    have hpow : 2 ^ (a 0 + 1) ≤ b := by
      dsimp [b]
      exact Nat.pow_le_pow_left hr_two _
    exact (Nat.lt_two_pow_self.trans_le
      ((Nat.pow_le_pow_right (by omega) (Nat.le_succ _)).trans hpow)).le
  have hb_support : b.primeFactors = (a i).primeFactors := by
    dsimp [b]
    rw [Nat.primeFactors_pow r (by omega), primeFactors_supportProd (a i)]
  have hcompat : ∀ j : ℕ, 1 < Nat.gcd b (a j) := by
    intro j
    obtain ⟨q, hqi, hqj⟩ := exists_common_prime_of_valid a ha i j
    have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hqi
    have hq_dvd_gcd : q ∣ Nat.gcd b (a j) := by
      apply Nat.dvd_gcd
      · exact Nat.dvd_of_mem_primeFactors (hb_support.symm ▸ hqi)
      · exact Nat.dvd_of_mem_primeFactors hqj
    exact hq_prime.one_lt.trans_le (Nat.le_of_dvd
      (Nat.gcd_pos_of_pos_right b (Nat.zero_lt_of_lt (ha.1 j))) hq_dvd_gcd)
  obtain ⟨k, hk⟩ := validSeq_contains_universally_compatible a ha b hab hcompat
  have hb_le : b ≤ N := by
    dsimp [b, N]
    exact Nat.pow_le_pow_left hr_bound _
  have hgrowth : ∀ m : ℕ, m < a m := by
    intro m
    induction m with
    | zero => exact lt_trans Nat.zero_lt_one (ha.1 0)
    | succ m hm =>
        have hstep := (ha.2 m).1
        omega
  have hk_lt_N : k < N := by
    have hk_lt_b : k < b := hk ▸ hgrowth k
    exact hk_lt_b.trans_le hb_le
  have hkN : k ≤ N := hk_lt_N.le
  refine ⟨k, hkN, ?_⟩
  intro q hq_prime hq_dvd
  apply Nat.dvd_of_mem_primeFactors
  apply hin
  have hq_mem : q ∈ (a k).primeFactors :=
    hq_prime.mem_primeFactors hq_dvd
      (Nat.ne_of_gt (Nat.zero_lt_of_lt (ha.1 k)))
  rw [hk, hb_support] at hq_mem
  exact hq_mem
theorem validSeq_periodic_of_finite_prime_basis (a : ℕ → ℕ)
    (ha : IsValidSeq a)
    (hbase : ∃ N : ℕ, ∀ n : ℕ, ∃ i : ℕ, i ≤ N ∧
      ∀ p : ℕ, p.Prime → p ∣ a i → p ∣ a n) :
    ∃ T L : ℕ, 0 < T ∧ 0 < L ∧ ∀ n, a (n + T) = a n + L := by
  obtain ⟨N, hbase⟩ := hbase
  have hmono : StrictMono a := strictMono_nat_of_lt_succ (fun n => (ha.2 n).1)
  have hpair_gcd : ∀ n i, 1 < Nat.gcd (a n) (a i) := by
    intro n i
    rcases le_total n i with hni | hin
    · by_cases heq : n = i
      · subst i
        simpa using ha.1 n
      · have hlt : n < i := lt_of_le_of_ne hni heq
        cases i with
        | zero => omega
        | succ k =>
            have hn : n ≤ k := by omega
            simpa [Nat.succ_eq_add_one, Nat.gcd_comm] using (ha.2 k).2.1 n hn
    · by_cases heq : i = n
      · subst i
        simpa using ha.1 n
      · have hlt : i < n := lt_of_le_of_ne hin heq
        cases n with
        | zero => omega
        | succ k =>
            have hi : i ≤ k := by omega
            simpa [Nat.succ_eq_add_one] using (ha.2 k).2.1 i hi
  have hpair_coprime : ∀ n i, ¬ Nat.Coprime (a n) (a i) := by
    intro n i hc
    have hg := hpair_gcd n i
    change Nat.gcd (a n) (a i) = 1 at hc
    omega
  have htransfer : ∀ b, (∀ i, i ≤ N → ¬ Nat.Coprime b (a i)) →
      ∀ n, ¬ Nat.Coprime b (a n) := by
    intro b hb n hc
    obtain ⟨i, hi, hsupp⟩ := hbase n
    have hgcd : Nat.gcd b (a i) ≠ 1 := by
      intro heq
      exact hb i hi (by change Nat.gcd b (a i) = 1; exact heq)
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hgcd
    have hpai : p ∣ a i := Nat.dvd_trans hpd (Nat.gcd_dvd_right b (a i))
    have hpan : p ∣ a n := hsupp p hp hpai
    have hpb : p ∣ b := Nat.dvd_trans hpd (Nat.gcd_dvd_left b (a i))
    have hpgcd : p ∣ Nat.gcd b (a n) := Nat.dvd_gcd hpb hpan
    change Nat.gcd b (a n) = 1 at hc
    have hpone : p ∣ 1 := by rw [← hc]; exact hpgcd
    exact hp.ne_one (Nat.dvd_one.mp hpone)
  let Good : ℕ → Prop := fun b =>
    a 0 < b ∧ ∀ i, i ≤ N → ¬ Nat.Coprime b (a i)
  have hLpos : 0 < ∏ i ∈ Finset.range (N + 1), a i := by
    apply Finset.prod_pos
    intro i hi
    exact Nat.zero_lt_of_lt (ha.1 i)
  let L : ℕ := ∏ i ∈ Finset.range (N + 1), a i
  have hLpos' : 0 < L := by simpa [L] using hLpos
  have hLdvd : ∀ i, i ≤ N → a i ∣ L := by
    intro i hi
    dsimp [L]
    apply Finset.dvd_prod_of_mem
    exact Finset.mem_range.mpr (by omega)
  have hcoprime_translate (b i : ℕ) (hi : i ≤ N) :
      Nat.Coprime (b + L) (a i) ↔ Nat.Coprime b (a i) := by
    exact Nat.add_coprime_iff_left (hLdvd i hi)
  have hbad_translate (b i : ℕ) (hi : i ≤ N) :
      ¬ Nat.Coprime (b + L) (a i) ↔ ¬ Nat.Coprime b (a i) :=
    not_congr (hcoprime_translate b i hi)
  have hgood_translate (b : ℕ) (hb : a 0 < b) :
      Good (b + L) ↔ Good b := by
    constructor
    · intro h
      refine ⟨hb, ?_⟩
      intro i hi
      exact (hbad_translate b i hi).mp (h.2 i hi)
    · intro h
      refine ⟨by omega, ?_⟩
      intro i hi
      exact (hbad_translate b i hi).mpr (h.2 i hi)
  have hgood_range : ∀ b, Good b → ∃ n, a n = b := by
    intro b hb
    have hex : ∃ k, b < a k := by
      refine ⟨b + 1, ?_⟩
      have hgrow : ∀ n, n + 2 ≤ a n := by
        intro n
        induction n with
        | zero => have := ha.1 0; omega
        | succ n ih =>
            have hs := Nat.succ_le_of_lt (ha.2 n).1
            omega
      have := hgrow (b + 1)
      omega
    have hkpos : Nat.find hex ≠ 0 := by
      intro hzero
      have hk0 : b < a 0 := by simpa [hzero] using Nat.find_spec hex
      omega
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hkpos
    have hk : b < a (m + 1) := by
      rw [← Nat.succ_eq_add_one, ← hm]
      exact Nat.find_spec hex
    have hmin : ¬ b < a m := by
      intro hbm
      have hfind := Nat.find_min' hex hbm
      rw [hm] at hfind
      omega
    have hle : a m ≤ b := Nat.le_of_not_gt hmin
    rcases hle.eq_or_lt with heq | hlt
    · exact ⟨m, heq⟩
    · obtain ⟨i, hi, hcop⟩ := (ha.2 m).2.2 b hlt hk
      have hcop' : Nat.Coprime b (a i) := by
        change Nat.gcd b (a i) = 1
        exact hcop
      exact False.elim (htransfer b hb.2 i hcop')
  have hgood_next : ∀ n, Good (a (n + 1)) := by
    intro n
    refine ⟨hmono (by omega), ?_⟩
    intro i hi
    exact hpair_coprime (n + 1) i
  have hleast_good : ∀ n b, Good b → a n < b → a (n + 1) ≤ b := by
    intro n b hb hlt
    by_contra hnot
    have hlt' : b < a (n + 1) := Nat.lt_of_not_ge hnot
    obtain ⟨i, hi, hcop⟩ := (ha.2 n).2.2 b hlt hlt'
    have hcop' : Nat.Coprime b (a i) := by
      change Nat.gcd b (a i) = 1
      exact hcop
    exact htransfer b hb.2 i hcop'
  have hgood_a0 : Good (a 0 + L) := by
    refine ⟨by omega, ?_⟩
    intro i hi
    exact (hbad_translate (a 0) i hi).mpr (hpair_coprime 0 i)
  obtain ⟨T, hTval⟩ := hgood_range (a 0 + L) hgood_a0
  have hTpos : 0 < T := by
    by_contra hT
    have : T = 0 := by omega
    subst T
    simp at hTval
    omega
  have hperiod : ∀ n, a (n + T) = a n + L := by
    intro n
    induction n with
    | zero => simpa using hTval
    | succ n ih =>
        have hbaseval : a (n + T) = a n + L := ih
        have hgNext : Good (a (n + 1) + L) := by
          have hlow : a 0 < a (n + 1) := hmono (by omega)
          exact (hgood_translate (a (n + 1)) hlow).2 (hgood_next n)
        have hsmall : a (n + T) < a (n + 1) + L := by
          have hs := (ha.2 n).1
          omega
        have hupper : a (n + T + 1) ≤ a (n + 1) + L :=
          hleast_good (n + T) (a (n + 1) + L) hgNext hsmall
        have hstep : a (n + T) < a (n + T + 1) := (ha.2 (n + T)).1
        have hLle : L ≤ a (n + T + 1) := by omega
        let b := a (n + T + 1) - L
        have hbadd : b + L = a (n + T + 1) := by
          dsimp [b]
          exact Nat.sub_add_cancel hLle
        have ha0n : a 0 ≤ a n := hmono.monotone (Nat.zero_le n)
        have hblow : a 0 < b := by
          have := hstep
          omega
        have hgb : Good b := by
          have hgt := hgood_next (n + T)
          rw [← hbadd] at hgt
          exact (hgood_translate b hblow).mp hgt
        have hsmall' : a n < b := by
          have := hstep
          omega
        have hlower := hleast_good n b hgb hsmall'
        have hlower' : a (n + 1) + L ≤ b + L := Nat.add_le_add_right hlower L
        rw [hbadd] at hlower'
        have heq : a (n + T + 1) = a (n + 1) + L := le_antisymm hupper hlower'
        simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using heq
  refine ⟨T, L, hTpos, hLpos', hperiod⟩
theorem validSeq_basis_transfer_nonCoprime :
    ∀ (a : ℕ → ℕ) (N : ℕ),
      (∀ n, ∃ i, i ≤ N ∧ ∀ p, p.Prime → p ∣ a i → p ∣ a n) →
      ∀ b, (∀ i, i ≤ N → Nat.gcd b (a i) ≠ 1) →
        ∀ n, Nat.gcd b (a n) ≠ 1 := by
  intro a N hbasis b hprefix n
  obtain ⟨i, hiN, htransfer⟩ := hbasis n
  obtain ⟨p, hp, hp_dvd_gcd⟩ := Nat.exists_prime_and_dvd (hprefix i hiN)
  have hp_dvd_b : p ∣ b := hp_dvd_gcd.trans (Nat.gcd_dvd_left b (a i))
  have hp_dvd_ai : p ∣ a i := hp_dvd_gcd.trans (Nat.gcd_dvd_right b (a i))
  have hp_dvd_an : p ∣ a n := htransfer p hp hp_dvd_ai
  have hp_dvd_target : p ∣ Nat.gcd b (a n) := Nat.dvd_gcd hp_dvd_b hp_dvd_an
  intro htarget
  rw [htarget] at hp_dvd_target
  have hp_one : p = 1 := Nat.dvd_one.mp hp_dvd_target
  exact hp.ne_one hp_one
/-- For any sequence satisfying Definition 1, there exist positive integers `T` and `L` such that
`a (n + T) = a n + L` for every `n`. Equivalently, the sequence of consecutive differences is
purely periodic. -/
theorem main_theorem (a : ℕ → ℕ) (ha : IsValidSeq a) :
    ∃ T L : ℕ, 0 < T ∧ 0 < L ∧ ∀ n, a (n + T) = a n + L := by
  exact validSeq_periodic_of_finite_prime_basis a ha
    (validSeq_finite_prime_basis a ha)
