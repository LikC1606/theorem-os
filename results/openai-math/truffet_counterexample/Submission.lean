import Mathlib

namespace OAI

noncomputable section
namespace TruffetV4Counterexample

abbrev Coeff := WithBot ℝ

abbrev Form := Fin 3 → Coeff

abbrev Var := Fin 2

abbrev RowIndex := Fin 2

def column (j : Var) : Fin 3 := ⟨j.val, Nat.lt_trans j.isLt (by decide)⟩

def nullForm : Form := fun _ => ⊥

structure Row where
  lhs : Form
  rhs : Form

structure State where
  rows : RowIndex → Row
  cost : Form
  remaining : Var → Prop

def wellFormed (s : State) : Prop := ∀ j, ¬ s.remaining j →
  s.cost (column j) = ⊥ ∧ ∀ i,
    (s.rows i).lhs (column j) = ⊥ ∧ (s.rows i).rhs (column j) = ⊥

def eval (f : Form) (w : Fin 3 → ℝ) : Coeff :=
  max (f 0 + (w 0 : Coeff)) (max (f 1 + (w 1 : Coeff)) (f 2 + (w 2 : Coeff)))

def feasible (s : State) (w : Fin 3 → ℝ) : Prop :=
  ∀ i, eval (s.rows i).rhs w ≤ eval (s.rows i).lhs w

def lower (s : State) (i : RowIndex) (j : Var) : Prop :=
  (s.rows i).lhs (column j) ≠ ⊥ ∧
    (s.rows i).rhs (column j) < (s.rows i).lhs (column j)

def upper (s : State) (i : RowIndex) (j : Var) : Prop :=
  (s.rows i).rhs (column j) ≠ ⊥ ∧
    (s.rows i).lhs (column j) < (s.rows i).rhs (column j)

def dominating (s : State) (j : Var) : Prop :=
  s.remaining j ∧ (∃ i, lower s i j) ∧ ∃ i, upper s i j

def eligible (s : State) (i : RowIndex) (j : Var) : Prop :=
  s.remaining j ∧ lower s i j ∧ ((∃ k, dominating s k) → dominating s j)

def bounded (s : State) : Prop :=
  ∀ j, s.remaining j → (∃ i, lower s i j) ∨ ∃ i, upper s i j

def stop (s : State) : Prop := ∀ i, (s.rows i).rhs 2 ≤ (s.rows i).lhs 2

def switch (s : State) : Prop :=
  (∀ j, s.remaining j → s.cost (column j) = ⊥) ∧ ¬ stop s ∧
  (∃ j, s.remaining j) ∧
  (¬ ∃ i j, s.remaining j ∧ lower s i j) ∧
  ∃ i j, s.remaining j ∧ upper s i j

def failure (s : State) : Prop := ¬ stop s ∧
  ((¬ ∃ j, s.remaining j) ∨
   ((¬ ∃ i j, s.remaining j ∧ lower s i j) ∧
    (¬ ∃ i j, s.remaining j ∧ upper s i j)))

def lowerForm (s : State) (i : RowIndex) (j : Var) : Form := fun k =>
  if k = column j then ⊥ else
    (s.rows i).rhs k + ((-WithBot.unbotD 0 ((s.rows i).lhs (column j)) : ℝ) : Coeff)

def substitute (f : Form) (j : Var) (g : Form) : Form := fun k =>
  if k = column j then ⊥ else max (f k) (f (column j) + g k)

def cleanup (r : Row) : Row := by
  classical
  exact if ∀ k, r.rhs k ≤ r.lhs k then ⟨nullForm, nullForm⟩ else r

def advance (s : State) (i : RowIndex) (j : Var) : State where
  rows := fun r => cleanup ⟨substitute (s.rows r).lhs j (lowerForm s i j),
    substitute (s.rows r).rhs j (lowerForm s i j)⟩
  cost := substitute s.cost j (lowerForm s i j)
  remaining := fun k => s.remaining k ∧ k ≠ j

def ForcedSingletonStep (s s' : State) (i : RowIndex) (j : Var) : Prop :=
  wellFormed s ∧ wellFormed s' ∧
  bounded s ∧ ¬ stop s ∧ ¬ switch s ∧ ¬ failure s ∧
  (∀ r k, eligible s r k ↔ r = i ∧ k = j) ∧
  (∃ k, (substitute s.cost j (lowerForm s i j)) k ≠ ⊥) ∧
  s' = advance s i j

def initial : State where
  rows := ![⟨![(0 : Coeff), 0, ⊥], ![⊥, ⊥, (0 : Coeff)]⟩,
    ⟨![(0 : Coeff), ⊥, ⊥], ![⊥, (1 : Coeff), ((-2 : ℝ) : Coeff)]⟩]
  cost := ![(0 : Coeff), ⊥, ⊥]
  remaining := fun _ => True

def middle : State where
  rows := ![⟨nullForm, nullForm⟩,
    ⟨![(0 : Coeff), ⊥, ⊥], ![⊥, ⊥, (1 : Coeff)]⟩]
  cost := ![(0 : Coeff), ⊥, ⊥]
  remaining := fun j => j = 0

def finalState : State where
  rows := fun _ => ⟨nullForm, nullForm⟩
  cost := ![⊥, ⊥, (1 : Coeff)]
  remaining := fun _ => False

def crossRowRestriction (s : State) : Prop :=
  ∀ i r : RowIndex, i ≠ r → ∀ α : ℝ, ∃ w : Fin 3 → ℝ,
    eval (s.rows i).lhs w < (α : Coeff) + eval (s.rows r).rhs w

def output : Fin 3 → ℝ := ![1, 0, 0]

def better : Fin 3 → ℝ := ![0, -1, 0]

lemma col_zero : column 0 = (0 : Fin 3) := rfl
lemma col_one : column 1 = (1 : Fin 3) := rfl
lemma eval_mk (a b c : Coeff) (w : Fin 3 → ℝ) :
    eval ![a, b, c] w =
      max (a + (w 0 : Coeff)) (max (b + (w 1 : Coeff)) (c + (w 2 : Coeff))) := rfl
lemma eval_coe (a b c : ℝ) (w : Fin 3 → ℝ) :
    eval ![((a : Coeff)), ((b : Coeff)), ((c : Coeff))] w =
      ((max (a + w 0) (max (b + w 1) (c + w 2)) : ℝ) : Coeff) := by
  rw [eval_mk]
  rw [← WithBot.coe_add, ← WithBot.coe_add, ← WithBot.coe_add, ← WithBot.coe_max,
    ← WithBot.coe_max]
lemma substitute_one (a b c : Coeff) (g : Form) :
    substitute (![a, b, c] : Form) 1 g = ![max a (b + g 0), ⊥, max c (b + g 2)] := by
  funext k
  fin_cases k <;> simp [substitute, col_one]
lemma substitute_zero (a b c : Coeff) (g : Form) :
    substitute (![a, b, c] : Form) 0 g = ![⊥, max b (a + g 1), max c (a + g 2)] := by
  funext k
  fin_cases k <;> simp [substitute, col_zero]
lemma substitute_nullForm (j : Var) (g : Form) : substitute nullForm j g = nullForm := by
  funext k
  by_cases h : k = column j <;> simp [substitute, nullForm, h]
lemma cleanup_eq_null (r : Row) (h : ∀ k, r.rhs k ≤ r.lhs k) :
    cleanup r = ⟨nullForm, nullForm⟩ := by
  rw [cleanup]
  exact if_pos h
lemma cleanup_eq_self (r : Row) (h : ¬ ∀ k, r.rhs k ≤ r.lhs k) : cleanup r = r := by
  rw [cleanup]
  exact if_neg h
lemma cleanup_nullRow : cleanup ⟨nullForm, nullForm⟩ = ⟨nullForm, nullForm⟩ :=
  cleanup_eq_null _ (fun k => by simp [nullForm])
lemma initial_rows_zero : initial.rows 0 =
    (⟨![((0:ℝ):Coeff), ((0:ℝ):Coeff), (⊥:Coeff)], ![⊥, ⊥, ((0:ℝ):Coeff)]⟩ : Row) := rfl
lemma initial_rows_one : initial.rows 1 =
    (⟨![((0:ℝ):Coeff), (⊥:Coeff), (⊥:Coeff)], ![⊥, ((1:ℝ):Coeff), ((-2:ℝ):Coeff)]⟩ : Row) := rfl
lemma initial_cost : initial.cost = ![((0:ℝ):Coeff), (⊥:Coeff), (⊥:Coeff)] := rfl
lemma middle_rows_zero : middle.rows 0 = (⟨nullForm, nullForm⟩ : Row) := rfl
lemma middle_rows_one : middle.rows 1 =
    (⟨![((0:ℝ):Coeff), (⊥:Coeff), (⊥:Coeff)], ![⊥, ⊥, ((1:ℝ):Coeff)]⟩ : Row) := rfl
lemma middle_cost : middle.cost = ![((0:ℝ):Coeff), (⊥:Coeff), (⊥:Coeff)] := rfl
lemma final_rows (i : RowIndex) : finalState.rows i = (⟨nullForm, nullForm⟩ : Row) := rfl
lemma final_cost : finalState.cost = ![(⊥:Coeff), (⊥:Coeff), ((1:ℝ):Coeff)] := rfl
lemma final_remaining (j : Var) : ¬ finalState.remaining j := by simp [finalState]
lemma lowerForm_initial : lowerForm initial 0 1 = ![(⊥:Coeff), (⊥:Coeff), ((0:ℝ):Coeff)] := by
  funext k
  fin_cases k <;> simp [lowerForm, initial_rows_zero, col_one]
lemma lowerForm_middle : lowerForm middle 1 0 = ![(⊥:Coeff), (⊥:Coeff), ((1:ℝ):Coeff)] := by
  funext k
  fin_cases k <;> simp [lowerForm, middle_rows_one, col_zero]
lemma initial_remaining_all (j : Var) : initial.remaining j := trivial
lemma initial_lower_00 : lower initial 0 0 := by simp [lower, initial_rows_zero, col_zero]
lemma initial_lower_01 : lower initial 0 1 := by simp [lower, initial_rows_zero, col_one]
lemma initial_lower_10 : lower initial 1 0 := by simp [lower, initial_rows_one, col_zero]
lemma initial_not_lower_11 : ¬ lower initial 1 1 := by simp [lower, initial_rows_one, col_one]
lemma initial_not_upper_00 : ¬ upper initial 0 0 := by simp [upper, initial_rows_zero, col_zero]
lemma initial_not_upper_01 : ¬ upper initial 0 1 := by simp [upper, initial_rows_zero, col_one]
lemma initial_not_upper_10 : ¬ upper initial 1 0 := by simp [upper, initial_rows_one, col_zero]
lemma initial_upper_11 : upper initial 1 1 := by simp [upper, initial_rows_one, col_one]
lemma initial_dominating_one : dominating initial 1 :=
  ⟨trivial, ⟨0, initial_lower_01⟩, ⟨1, initial_upper_11⟩⟩
lemma initial_not_dominating_zero : ¬ dominating initial 0 := by
  rintro ⟨-, -, hup⟩
  obtain ⟨i, hi⟩ := hup
  match i with
  | ⟨0, _⟩ => exact initial_not_upper_00 hi
  | ⟨1, _⟩ => exact initial_not_upper_10 hi
lemma initial_dominating_iff (k : Var) : dominating initial k ↔ k = 1 := by
  fin_cases k
  · exact ⟨fun h => absurd h initial_not_dominating_zero, fun h => by simp at h⟩
  · exact ⟨fun _ => rfl, fun _ => initial_dominating_one⟩
lemma initial_eligible_iff (r : RowIndex) (k : Var) :
    eligible initial r k ↔ r = 0 ∧ k = 1 := by
  have hdom : ∃ k, dominating initial k := ⟨1, initial_dominating_one⟩
  constructor
  · rintro ⟨-, hl, hd⟩
    have hk : k = 1 := (initial_dominating_iff k).1 (hd hdom)
    subst hk
    match r with
    | ⟨0, _⟩ => simp
    | ⟨1, _⟩ => exact absurd hl initial_not_lower_11
  · rintro ⟨rfl, rfl⟩
    exact ⟨trivial, initial_lower_01, fun _ => initial_dominating_one⟩
lemma middle_not_lower_00 : ¬ lower middle 0 0 := by
  simp [lower, middle_rows_zero, nullForm, col_zero]
lemma middle_not_lower_01 : ¬ lower middle 0 1 := by
  simp [lower, middle_rows_zero, nullForm, col_one]
lemma middle_lower_10 : lower middle 1 0 := by simp [lower, middle_rows_one, col_zero]
lemma middle_not_lower_11 : ¬ lower middle 1 1 := by
  simp [lower, middle_rows_one, col_one]
lemma middle_not_upper_00 : ¬ upper middle 0 0 := by
  simp [upper, middle_rows_zero, nullForm, col_zero]
lemma middle_not_upper_01 : ¬ upper middle 0 1 := by
  simp [upper, middle_rows_zero, nullForm, col_one]
lemma middle_not_upper_10 : ¬ upper middle 1 0 := by
  simp [upper, middle_rows_one, col_zero]
lemma middle_not_upper_11 : ¬ upper middle 1 1 := by
  simp [upper, middle_rows_one, col_one]
lemma middle_not_dominating (k : Var) : ¬ dominating middle k := by
  fin_cases k
  · rintro ⟨-, -, hup⟩
    obtain ⟨i, hi⟩ := hup
    match i with
    | ⟨0, _⟩ => exact middle_not_upper_00 hi
    | ⟨1, _⟩ => exact middle_not_upper_10 hi
  · rintro ⟨hrem, -, -⟩
    exact absurd hrem (by simp [middle])
lemma middle_eligible_iff (r : RowIndex) (k : Var) :
    eligible middle r k ↔ r = 1 ∧ k = 0 := by
  constructor
  · rintro ⟨hrem, hl, -⟩
    have hk : k = 0 := by simpa [middle] using hrem
    subst hk
    match r with
    | ⟨0, _⟩ => exact absurd hl middle_not_lower_00
    | ⟨1, _⟩ => simp
  · rintro ⟨rfl, rfl⟩
    refine ⟨rfl, middle_lower_10, ?_⟩
    rintro ⟨k, hk⟩
    exact (middle_not_dominating k hk).elim
lemma advance_initial_cost : (advance initial 0 1).cost = ![((0:ℝ):Coeff), (⊥:Coeff), (⊥:Coeff)] := by
  show substitute initial.cost 1 (lowerForm initial 0 1) = _
  rw [initial_cost, lowerForm_initial, substitute_one]
  simp only [WithBot.bot_add, WithBot.add_bot, WithBot.coe_zero]
  rfl
lemma advance_initial_remaining (k : Var) : (advance initial 0 1).remaining k ↔ k = 0 := by
  show (initial.remaining k ∧ k ≠ 1) ↔ k = 0
  constructor
  · rintro ⟨-, h⟩; fin_cases k <;> simp_all
  · rintro rfl; exact ⟨trivial, by decide⟩
lemma advance_initial_rows_zero :
    (advance initial 0 1).rows 0 = (⟨nullForm, nullForm⟩ : Row) := by
  show cleanup ⟨substitute (initial.rows 0).lhs 1 (lowerForm initial 0 1),
    substitute (initial.rows 0).rhs 1 (lowerForm initial 0 1)⟩ = _
  rw [show (initial.rows 0).lhs = (![((0:ℝ):Coeff), ((0:ℝ):Coeff), (⊥:Coeff)] : Form) from rfl]
  rw [show (initial.rows 0).rhs = (![⊥, ⊥, ((0:ℝ):Coeff)] : Form) from rfl]
  rw [lowerForm_initial]
  simp only [substitute_one, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [cleanup_eq_null]
  intro k
  fin_cases k <;> simp
lemma advance_initial_rows_one : (advance initial 0 1).rows 1 = middle.rows 1 := by
  show cleanup ⟨substitute (initial.rows 1).lhs 1 (lowerForm initial 0 1),
    substitute (initial.rows 1).rhs 1 (lowerForm initial 0 1)⟩ = _
  rw [show (initial.rows 1).lhs = (![((0:ℝ):Coeff), (⊥:Coeff), (⊥:Coeff)] : Form) from rfl]
  rw [show (initial.rows 1).rhs = (![⊥, ((1:ℝ):Coeff), ((-2:ℝ):Coeff)] : Form) from rfl]
  rw [middle_rows_one, lowerForm_initial]
  simp only [substitute_one, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [cleanup_eq_self]
  · simp only [WithBot.add_bot, WithBot.bot_add, WithBot.coe_zero, WithBot.coe_one,
      WithBot.coe_add, max_self]
    norm_num
  · intro h
    have h2 := h 2
    simp only [Matrix.cons_val_two, Matrix.head_cons] at h2
    norm_num at h2
lemma advance_initial_eq : advance initial 0 1 = middle := by
  refine State.mk.injEq .. |>.mpr ⟨?_, ?_, ?_⟩
  · funext i
    match i with
    | ⟨0, _⟩ => exact advance_initial_rows_zero
    | ⟨1, _⟩ => exact advance_initial_rows_one
  · show (advance initial 0 1).cost = middle.cost
    rw [advance_initial_cost, middle_cost]
  · funext k
    exact propext (advance_initial_remaining k)
lemma advance_middle_cost : (advance middle 1 0).cost = ![(⊥:Coeff), (⊥:Coeff), ((1:ℝ):Coeff)] := by
  show substitute middle.cost 0 (lowerForm middle 1 0) = _
  rw [middle_cost, lowerForm_middle, substitute_zero]
  simp only [WithBot.bot_add, WithBot.add_bot, WithBot.coe_zero, WithBot.coe_one,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, max_self, max_eq_left, max_eq_right, bot_le, zero_add]
lemma advance_middle_remaining (k : Var) : ¬ (advance middle 1 0).remaining k := by
  show ¬ (middle.remaining k ∧ k ≠ 0)
  simp [middle]
lemma advance_middle_rows_zero :
    (advance middle 1 0).rows 0 = (⟨nullForm, nullForm⟩ : Row) := by
  show cleanup ⟨substitute (middle.rows 0).lhs 0 (lowerForm middle 1 0),
    substitute (middle.rows 0).rhs 0 (lowerForm middle 1 0)⟩ = _
  rw [middle_rows_zero]
  simp only [substitute_nullForm, cleanup_nullRow]
lemma advance_middle_rows_one :
    (advance middle 1 0).rows 1 = (⟨nullForm, nullForm⟩ : Row) := by
  show cleanup ⟨substitute (middle.rows 1).lhs 0 (lowerForm middle 1 0),
    substitute (middle.rows 1).rhs 0 (lowerForm middle 1 0)⟩ = _
  rw [show (middle.rows 1).lhs = (![((0:ℝ):Coeff), (⊥:Coeff), (⊥:Coeff)] : Form) from rfl]
  rw [show (middle.rows 1).rhs = (![⊥, ⊥, ((1:ℝ):Coeff)] : Form) from rfl]
  rw [lowerForm_middle]
  simp only [substitute_zero, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [cleanup_eq_null]
  intro k
  fin_cases k <;> simp [WithBot.bot_add, WithBot.add_bot, WithBot.coe_zero, WithBot.coe_one]
lemma advance_middle_eq : advance middle 1 0 = finalState := by
  refine State.mk.injEq .. |>.mpr ⟨?_, ?_, ?_⟩
  · funext i
    fin_cases i
    · exact advance_middle_rows_zero
    · exact advance_middle_rows_one
  · show (advance middle 1 0).cost = finalState.cost
    rw [advance_middle_cost, final_cost]
  · funext k
    exact propext (by
      show middle.remaining k ∧ k ≠ 0 ↔ False
      simp [middle])
lemma wellFormed_initial : wellFormed initial := by
  intro j hj
  exact absurd hj (by simp [initial])
lemma wellFormed_middle : wellFormed middle := by
  intro j hj
  have hj0 : ¬ j = 0 := hj
  have : j = 1 := by fin_cases j <;> simp_all
  subst this
  refine ⟨rfl, ?_⟩
  intro i
  fin_cases i <;> simp [middle, nullForm, col_zero, col_one]
lemma wellFormed_final : wellFormed finalState := by
  intro j _
  fin_cases j
  · refine ⟨rfl, ?_⟩
    intro i
    exact ⟨rfl, rfl⟩
  · refine ⟨rfl, ?_⟩
    intro i
    exact ⟨rfl, rfl⟩
lemma bounded_initial : bounded initial := by
  intro j _
  fin_cases j
  · exact Or.inl ⟨0, initial_lower_00⟩
  · exact Or.inl ⟨0, initial_lower_01⟩
lemma not_stop_initial : ¬ stop initial := by
  intro h
  have := h 1
  simp [initial_rows_one] at this
lemma stop_final : stop finalState := by
  intro i
  rw [final_rows]
lemma not_switch_initial : ¬ switch initial := by
  rintro ⟨-, -, -, hnoLower, -⟩
  exact hnoLower ⟨1, 0, trivial, initial_lower_10⟩
lemma not_failure_initial : ¬ failure initial := by
  rintro ⟨-, h | h⟩
  · exact h ⟨0, trivial⟩
  · exact h.1 ⟨1, 0, trivial, initial_lower_10⟩
lemma not_stop_middle : ¬ stop middle := by
  intro h
  have := h 1
  simp [middle_rows_one] at this
lemma not_switch_middle : ¬ switch middle := by
  rintro ⟨-, -, -, hnoLower, -⟩
  exact hnoLower ⟨1, 0, rfl, middle_lower_10⟩
lemma not_failure_middle : ¬ failure middle := by
  rintro ⟨-, h | h⟩
  · exact h ⟨0, rfl⟩
  · exact h.1 ⟨1, 0, rfl, middle_lower_10⟩
lemma output_zero : output 0 = 1 := rfl
lemma output_one : output 1 = 0 := rfl
lemma output_two : output 2 = 0 := rfl
lemma better_zero : better 0 = 0 := rfl
lemma better_one : better 1 = -1 := rfl
lemma better_two : better 2 = 0 := rfl
lemma eval_initial_cost_output : eval initial.cost output = ((1:ℝ) : Coeff) := by
  rw [initial_cost, eval_mk]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, WithBot.bot_add, WithBot.add_bot,
    output_zero, output_one, output_two]
  norm_num
lemma eval_initial_cost_better : eval initial.cost better = ((0:ℝ) : Coeff) := by
  rw [initial_cost, eval_mk]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, WithBot.bot_add, WithBot.add_bot,
    better_zero, better_one, better_two]
  norm_num
lemma eval_final_cost_output : eval finalState.cost output = ((1:ℝ) : Coeff) := by
  rw [final_cost, eval_mk]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, WithBot.bot_add, WithBot.add_bot,
    output_zero, output_one, output_two]
  norm_num
lemma eval_lowerForm_initial_output :
    eval (lowerForm initial 0 1) output = ((0:ℝ) : Coeff) := by
  rw [lowerForm_initial, eval_mk]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, WithBot.bot_add, WithBot.add_bot,
    output_zero, output_one, output_two]
  norm_num
lemma eval_lowerForm_middle_output :
    eval (lowerForm middle 1 0) output = ((1:ℝ) : Coeff) := by
  rw [lowerForm_middle, eval_mk]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, WithBot.bot_add, WithBot.add_bot,
    output_zero, output_one, output_two]
  norm_num
lemma feasible_initial_output : feasible initial output := by
  intro i
  fin_cases i
  · show eval ![⊥, ⊥, ((0:ℝ):Coeff)] output ≤ eval ![((0:ℝ):Coeff), ((0:ℝ):Coeff), (⊥:Coeff)] output
    rw [eval_mk, eval_mk]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, WithBot.bot_add, WithBot.add_bot,
      output_zero, output_one, output_two, ← WithBot.coe_add, WithBot.coe_le_coe]
    norm_num
  · show eval ![⊥, ((1:ℝ):Coeff), ((-2:ℝ):Coeff)] output ≤ eval ![((0:ℝ):Coeff), (⊥:Coeff), (⊥:Coeff)] output
    rw [eval_mk, eval_mk]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, WithBot.bot_add, WithBot.add_bot,
      output_zero, output_one, output_two, ← WithBot.coe_add, WithBot.coe_le_coe]
    norm_num
lemma feasible_initial_better : feasible initial better := by
  intro i
  fin_cases i
  · show eval ![⊥, ⊥, ((0:ℝ):Coeff)] better ≤ eval ![((0:ℝ):Coeff), ((0:ℝ):Coeff), (⊥:Coeff)] better
    rw [eval_mk, eval_mk]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, WithBot.bot_add, WithBot.add_bot,
      better_zero, better_one, better_two, ← WithBot.coe_add, WithBot.coe_le_coe]
    norm_num
  · show eval ![⊥, ((1:ℝ):Coeff), ((-2:ℝ):Coeff)] better ≤ eval ![((0:ℝ):Coeff), (⊥:Coeff), (⊥:Coeff)] better
    rw [eval_mk, eval_mk]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, WithBot.bot_add, WithBot.add_bot,
      better_zero, better_one, better_two, ← WithBot.coe_add, WithBot.coe_le_coe]
    norm_num
lemma coe_max_real (a b : ℝ) : max ((a : Coeff)) ((b : Coeff)) = ((max a b : ℝ) : Coeff) :=
  (WithBot.coe_max a b).symm
lemma coe_add_real (a b : ℝ) : ((a : Coeff) + (b : Coeff)) = ((a + b : ℝ) : Coeff) :=
  (WithBot.coe_add a b).symm
lemma eval_initial_l10 (w : Fin 3 → ℝ) :
    eval (initial.rows 1).lhs w = ((w 0 : ℝ) : Coeff) := by
  rw [show (initial.rows 1).lhs = ![((0:ℝ):Coeff), (⊥:Coeff), (⊥:Coeff)] from rfl, eval_mk]
  rw [show max (((0:ℝ):Coeff) + ((w 0 : ℝ) : Coeff))
        (max ((⊥:Coeff) + ((w 1 : ℝ) : Coeff)) ((⊥:Coeff) + ((w 2 : ℝ) : Coeff)))
      = ((w 0 : ℝ) : Coeff) by
    rw [WithBot.bot_add, WithBot.bot_add, WithBot.coe_zero]
    simp]
lemma eval_initial_l01 (w : Fin 3 → ℝ) :
    eval (initial.rows 0).lhs w = ((max (w 0) (w 1) : ℝ) : Coeff) := by
  rw [show (initial.rows 0).lhs = ![((0:ℝ):Coeff), ((0:ℝ):Coeff), (⊥:Coeff)] from rfl, eval_mk]
  rw [show max (((0:ℝ):Coeff) + ((w 0 : ℝ) : Coeff))
        (max (((0:ℝ):Coeff) + ((w 1 : ℝ) : Coeff)) ((⊥:Coeff) + ((w 2 : ℝ) : Coeff)))
      = max ((w 0 : ℝ) : Coeff) ((w 1 : ℝ) : Coeff) by
    rw [WithBot.bot_add]
    simp]
  exact coe_max_real _ _
lemma eval_initial_r11 (w : Fin 3 → ℝ) :
    eval (initial.rows 1).rhs w = ((max (1 + w 1) (-2 + w 2) : ℝ) : Coeff) := by
  rw [show (initial.rows 1).rhs = ![⊥, ((1:ℝ):Coeff), ((-2:ℝ):Coeff)] from rfl, eval_mk]
  rw [show max ((⊥:Coeff) + ((w 0 : ℝ) : Coeff))
        (max (((1:ℝ):Coeff) + ((w 1 : ℝ) : Coeff)) ((((-2:ℝ)):Coeff) + ((w 2 : ℝ) : Coeff)))
      = max (((1:ℝ) : Coeff) + ((w 1 : ℝ) : Coeff))
        ((((-2:ℝ)) : Coeff) + ((w 2 : ℝ) : Coeff)) by
    rw [WithBot.bot_add]
    simp]
  rw [coe_add_real, coe_add_real, coe_max_real]
lemma eval_initial_r00 (w : Fin 3 → ℝ) :
    eval (initial.rows 0).rhs w = ((w 2 : ℝ) : Coeff) := by
  rw [show (initial.rows 0).rhs = ![⊥, ⊥, ((0:ℝ):Coeff)] from rfl, eval_mk]
  rw [show max ((⊥:Coeff) + ((w 0 : ℝ) : Coeff))
        (max ((⊥:Coeff) + ((w 1 : ℝ) : Coeff)) (((0:ℝ):Coeff) + ((w 2 : ℝ) : Coeff)))
      = ((w 2 : ℝ) : Coeff) by
    rw [WithBot.bot_add, WithBot.bot_add, WithBot.coe_zero]
    simp]
lemma crossRow_0_1 (α : ℝ) : ∃ w : Fin 3 → ℝ,
    eval (initial.rows 0).lhs w < ((α : Coeff) + eval (initial.rows 1).rhs w) := by
  refine ⟨![0, 0, |α| + 10], ?_⟩
  rw [eval_initial_l01, eval_initial_r11]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [show max (0:ℝ) 0 = 0 from max_self 0]
  rw [show max (1 + (0:ℝ)) (-2 + (|α| + 10)) = |α| + 8 from by
    rw [max_eq_right]; · ring
    · linarith [abs_nonneg α]]
  rw [coe_add_real]
  rw [WithBot.coe_lt_coe]
  have h1 : (0:ℝ) ≤ |α| := abs_nonneg α
  have h2 : -|α| ≤ α := neg_abs_le α
  linarith
lemma crossRow_1_0 (α : ℝ) : ∃ w : Fin 3 → ℝ,
    eval (initial.rows 1).lhs w < ((α : Coeff) + eval (initial.rows 0).rhs w) := by
  refine ⟨![0, 0, |α| + 10], ?_⟩
  rw [eval_initial_l10, eval_initial_r00]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [coe_add_real]
  rw [WithBot.coe_lt_coe]
  linarith [neg_abs_le α]
lemma crossRowRestriction_initial : crossRowRestriction initial := by
  intro i r hir α
  fin_cases i
  · fin_cases r
    · exact absurd rfl hir
    · exact crossRow_0_1 α
  · fin_cases r
    · exact crossRow_1_0 α
    · exact absurd rfl hir
lemma subst_cost_initial_nonbot :
    ∃ k, (substitute initial.cost 1 (lowerForm initial 0 1)) k ≠ (⊥ : Coeff) := by
  refine ⟨0, ?_⟩
  rw [initial_cost, lowerForm_initial, substitute_one]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, WithBot.bot_add, max_self]
  exact WithBot.coe_ne_bot
lemma subst_cost_middle_nonbot :
    ∃ k, (substitute middle.cost 0 (lowerForm middle 1 0)) k ≠ (⊥ : Coeff) := by
  refine ⟨2, ?_⟩
  rw [middle_cost, lowerForm_middle, substitute_zero]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, WithBot.bot_add, max_eq_right, WithBot.coe_one,
    le_refl]
  exact WithBot.coe_ne_bot
lemma forced_step_initial : ForcedSingletonStep initial middle 0 1 := by
  refine ⟨wellFormed_initial, wellFormed_middle, bounded_initial, not_stop_initial,
    not_switch_initial, not_failure_initial, ?_, subst_cost_initial_nonbot, ?_⟩
  · intro r k
    exact initial_eligible_iff r k
  · exact advance_initial_eq.symm
lemma forced_step_middle : ForcedSingletonStep middle finalState 1 0 := by
  refine ⟨wellFormed_middle, wellFormed_final, ?_, not_stop_middle, not_switch_middle,
    not_failure_middle, ?_, subst_cost_middle_nonbot, ?_⟩
  · intro j hj
    fin_cases j
    · exact Or.inl ⟨1, middle_lower_10⟩
    · exact absurd hj (by simp [middle])
  · intro r k
    exact middle_eligible_iff r k
  · exact advance_middle_eq.symm
theorem finite_execution_not_optimal :
    crossRowRestriction initial ∧
    ForcedSingletonStep initial middle 0 1 ∧
    ForcedSingletonStep middle finalState 1 0 ∧
    (¬ ∃ j, finalState.remaining j) ∧ stop finalState ∧
    feasible initial output ∧ feasible initial better ∧
    output 2 = 0 ∧ better 2 = 0 ∧
    (output 1 : Coeff) = eval (lowerForm initial 0 1) output ∧
    (output 0 : Coeff) = eval (lowerForm middle 1 0) output ∧
    eval initial.cost output = eval finalState.cost output ∧
    eval initial.cost better < eval finalState.cost output := by
  refine ⟨crossRowRestriction_initial, forced_step_initial, forced_step_middle, ?_,
    stop_final, feasible_initial_output, feasible_initial_better, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨j, hj⟩
    exact final_remaining j hj
  · exact output_two
  · exact better_two
  · show ((output 1 : ℝ) : Coeff) = eval (lowerForm initial 0 1) output
    rw [eval_lowerForm_initial_output, output_one]
  · show ((output 0 : ℝ) : Coeff) = eval (lowerForm middle 1 0) output
    rw [eval_lowerForm_middle_output, output_zero]
  · rw [eval_initial_cost_output, eval_final_cost_output]
  · rw [eval_initial_cost_better, eval_final_cost_output, WithBot.coe_lt_coe]
    norm_num
end TruffetV4Counterexample
end

end OAI
