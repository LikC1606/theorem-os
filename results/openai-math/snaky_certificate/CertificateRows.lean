import CertificateData
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace OAI.SnakyCertificate
set_option maxHeartbeats 0 in
lemma table_valid_probe : TableValid := by
  constructor
  · decide +kernel
  · have h : ∀ k : Fin table.size,
        let e := table[k.val]?.getD emptyEntry
        e.index = k.val + 6 ∧ e.terms ≠ [] ∧ ∀ t ∈ e.terms, t.child < e.index := by
      decide +kernel
    intro k hk
    exact h ⟨k, hk⟩

lemma rowData_ext (a b : RowData) (ha : a.A = b.A) (hh : a.H = b.H) (ht : a.height = b.height) : a = b := by
  cases a; cases b; simp_all

lemma tableChunk_size_0 : tableChunk_0.size = 20 := by rfl
lemma tableChunk_size_1 : tableChunk_1.size = 20 := by rfl
lemma tableChunk_size_2 : tableChunk_2.size = 20 := by rfl
lemma tableChunk_size_3 : tableChunk_3.size = 20 := by rfl
lemma tableChunk_size_4 : tableChunk_4.size = 20 := by rfl
lemma tableChunk_size_5 : tableChunk_5.size = 20 := by rfl
lemma tableChunk_size_6 : tableChunk_6.size = 20 := by rfl
lemma tableChunk_size_7 : tableChunk_7.size = 20 := by rfl
lemma tableChunk_size_8 : tableChunk_8.size = 20 := by rfl
lemma tableChunk_size_9 : tableChunk_9.size = 20 := by rfl
lemma tableChunk_size_10 : tableChunk_10.size = 20 := by rfl
lemma tableChunk_size_11 : tableChunk_11.size = 20 := by rfl
lemma tableChunk_size_12 : tableChunk_12.size = 20 := by rfl
lemma tableChunk_size_13 : tableChunk_13.size = 20 := by rfl
lemma tableChunk_size_14 : tableChunk_14.size = 20 := by rfl
lemma tableChunk_size_15 : tableChunk_15.size = 20 := by rfl
lemma tableChunk_size_16 : tableChunk_16.size = 20 := by rfl
lemma tableChunk_size_17 : tableChunk_17.size = 20 := by rfl
lemma tableChunk_size_18 : tableChunk_18.size = 20 := by rfl
lemma tableChunk_size_19 : tableChunk_19.size = 20 := by rfl
lemma tableChunk_size_20 : tableChunk_20.size = 20 := by rfl
lemma tableChunk_size_21 : tableChunk_21.size = 20 := by rfl
lemma tableChunk_size_22 : tableChunk_22.size = 20 := by rfl
lemma tableChunk_size_23 : tableChunk_23.size = 20 := by rfl
lemma tableChunk_size_24 : tableChunk_24.size = 20 := by rfl
lemma tableChunk_size_25 : tableChunk_25.size = 20 := by rfl
lemma tableChunk_size_26 : tableChunk_26.size = 20 := by rfl
lemma tableChunk_size_27 : tableChunk_27.size = 20 := by rfl
lemma tableChunk_size_28 : tableChunk_28.size = 20 := by rfl
lemma tableChunk_size_29 : tableChunk_29.size = 20 := by rfl
lemma tableChunk_size_30 : tableChunk_30.size = 10 := by rfl


def memoRow_0 : RowData := ⟨{(1, 0), (2, 0), (3, 0), (3, 1), (4, 1)}, {(0, 0), (1, 0), (2, 0), (3, 0), (3, 1), (4, 1)}, 1⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_0 : rowAt 0 = memoRow_0 := by
  rw [rowAt]
  decide +kernel


def memoRow_1 : RowData := ⟨{(-1, 0), (1, 0), (2, 0), (2, 1), (3, 1)}, {(-1, 0), (0, 0), (1, 0), (2, 0), (2, 1), (3, 1)}, 1⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_1 : rowAt 1 = memoRow_1 := by
  rw [rowAt]
  decide +kernel


def memoRow_2 : RowData := ⟨{(-2, 0), (-1, 0), (1, 0), (1, 1), (2, 1)}, {(-2, 0), (-1, 0), (0, 0), (1, 0), (1, 1), (2, 1)}, 1⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_2 : rowAt 2 = memoRow_2 := by
  rw [rowAt]
  decide +kernel


def memoRow_3 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0), (0, 1), (1, 1)}, {(-3, 0), (-2, 0), (-1, 0), (0, 0), (0, 1), (1, 1)}, 1⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_3 : rowAt 3 = memoRow_3 := by
  rw [rowAt]
  decide +kernel


def memoRow_4 : RowData := ⟨{(-3, -1), (-2, -1), (-1, -1), (0, -1), (1, 0)}, {(-3, -1), (-2, -1), (-1, -1), (0, -1), (0, 0), (1, 0)}, 1⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_4 : rowAt 4 = memoRow_4 := by
  rw [rowAt]
  decide +kernel


def memoRow_5 : RowData := ⟨{(-4, -1), (-3, -1), (-2, -1), (-1, -1), (-1, 0)}, {(-4, -1), (-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, 0)}, 1⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_5 : rowAt 5 = memoRow_5 := by
  rw [rowAt]
  decide +kernel


def memoRow_6 : RowData := ⟨{(-4, -1), (-3, -1), (-2, -1), (-1, -1), (-1, 0)}, {(-4, -1), (-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, 0)}, 2⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_6 : rowAt 6 = memoRow_6 := by
  have he : entryAt 6 = entry_6 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 6 < 6 by decide, ↓reduceDIte, he, entry_6, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0]
  apply rowData_ext <;> decide +kernel


def memoRow_7 : RowData := ⟨{(-4, -1), (-3, -1), (-2, -1), (-1, -1), (0, -1)}, {(-4, -1), (-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, 0)}, 3⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_7 : rowAt 7 = memoRow_7 := by
  have he : entryAt 7 = entry_7 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 7 < 6 by decide, ↓reduceDIte, he, entry_7, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_4, memoRow_eq_6]
  apply rowData_ext <;> decide +kernel


def memoRow_8 : RowData := ⟨{(0, -1), (1, -1), (1, 0), (2, -1), (3, -1)}, {(-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (3, -1), (4, -1)}, 3⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_8 : rowAt 8 = memoRow_8 := by
  have he : entryAt 8 = entry_8 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 8 < 6 by decide, ↓reduceDIte, he, entry_8, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_6]
  apply rowData_ext <;> decide +kernel


def memoRow_9 : RowData := ⟨{(-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0)}, {(-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (0, 0), (1, 0)}, 3⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_9 : rowAt 9 = memoRow_9 := by
  have he : entryAt 9 = entry_9 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 9 < 6 by decide, ↓reduceDIte, he, entry_9, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_6]
  apply rowData_ext <;> decide +kernel


def memoRow_10 : RowData := ⟨{(-4, -1), (-3, -1), (-3, 0), (-1, -1), (-1, 0)}, {(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0)}, 2⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_10 : rowAt 10 = memoRow_10 := by
  have he : entryAt 10 = entry_10 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 10 < 6 by decide, ↓reduceDIte, he, entry_10, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_2]
  apply rowData_ext <;> decide +kernel


def memoRow_11 : RowData := ⟨{(-1, -1), (-1, 0), (-1, 1), (1, 0), (2, 0)}, {(-2, -1), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (0, 0), (1, 0), (2, 0)}, 3⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_11 : rowAt 11 = memoRow_11 := by
  have he : entryAt 11 = entry_11 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 11 < 6 by decide, ↓reduceDIte, he, entry_11, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6]
  apply rowData_ext <;> decide +kernel


def memoRow_12 : RowData := ⟨{(-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0)}, {(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (1, 0)}, 2⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_12 : rowAt 12 = memoRow_12 := by
  have he : entryAt 12 = entry_12 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 12 < 6 by decide, ↓reduceDIte, he, entry_12, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0]
  apply rowData_ext <;> decide +kernel


def memoRow_13 : RowData := ⟨{(-3, -1), (-3, 0), (-3, 1), (-2, 0), (-1, 0)}, {(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-1, 0), (0, 0)}, 3⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_13 : rowAt 13 = memoRow_13 := by
  have he : entryAt 13 = entry_13 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 13 < 6 by decide, ↓reduceDIte, he, entry_13, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6]
  apply rowData_ext <;> decide +kernel


def memoRow_14 : RowData := ⟨{(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-1, 0)}, {(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0), (0, 0), (1, 0)}, 2⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_14 : rowAt 14 = memoRow_14 := by
  have he : entryAt 14 = entry_14 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 14 < 6 by decide, ↓reduceDIte, he, entry_14, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_3]
  apply rowData_ext <;> decide +kernel


def memoRow_15 : RowData := ⟨{(-3, -1), (-2, -1), (-1, -1), (-1, 0), (1, 0)}, {(-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (1, 0), (2, 0)}, 2⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_15 : rowAt 15 = memoRow_15 := by
  have he : entryAt 15 = entry_15 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 15 < 6 by decide, ↓reduceDIte, he, entry_15, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_3]
  apply rowData_ext <;> decide +kernel


def memoRow_16 : RowData := ⟨{(-2, -1), (-1, -1), (0, -1), (1, 0), (2, 0)}, {(-2, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, 0), (2, 0), (3, 0)}, 2⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_16 : rowAt 16 = memoRow_16 := by
  have he : entryAt 16 = entry_16 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 16 < 6 by decide, ↓reduceDIte, he, entry_16, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_3]
  apply rowData_ext <;> decide +kernel


def memoRow_17 : RowData := ⟨{(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-1, 0)}, {(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (1, 0)}, 2⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_17 : rowAt 17 = memoRow_17 := by
  have he : entryAt 17 = entry_17 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 17 < 6 by decide, ↓reduceDIte, he, entry_17, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_3]
  apply rowData_ext <;> decide +kernel


def memoRow_18 : RowData := ⟨{(-3, -1), (-2, -1), (-1, -1), (-1, 0), (1, 0)}, {(-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, 0)}, 2⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_18 : rowAt 18 = memoRow_18 := by
  have he : entryAt 18 = entry_18 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 18 < 6 by decide, ↓reduceDIte, he, entry_18, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_3]
  apply rowData_ext <;> decide +kernel


def memoRow_19 : RowData := ⟨{(-2, 0), (-2, 1), (-1, 0), (1, 0), (1, 1)}, {(-3, 1), (-2, 0), (-2, 1), (-1, 0), (0, 0), (1, 0), (1, 1), (2, 1)}, 3⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_19 : rowAt 19 = memoRow_19 := by
  have he : entryAt 19 = entry_19 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 19 < 6 by decide, ↓reduceDIte, he, entry_19, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6]
  apply rowData_ext <;> decide +kernel


def memoRow_20 : RowData := ⟨{(-3, 0), (-3, 1), (-2, 0), (-1, 0), (0, 1)}, {(-4, 1), (-3, 0), (-3, 1), (-2, 0), (-1, 0), (0, 0), (0, 1), (1, 1)}, 3⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_20 : rowAt 20 = memoRow_20 := by
  have he : entryAt 20 = entry_20 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 20 < 6 by decide, ↓reduceDIte, he, entry_20, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6]
  apply rowData_ext <;> decide +kernel


def memoRow_21 : RowData := ⟨{(-3, -1), (-2, 0), (-1, 0), (1, 0), (1, 1)}, {(-3, -1), (-2, -1), (-2, 0), (-1, 0), (0, 0), (1, 0), (1, 1), (2, 1)}, 3⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_21 : rowAt 21 = memoRow_21 := by
  have he : entryAt 21 = entry_21 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 21 < 6 by decide, ↓reduceDIte, he, entry_21, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_4, memoRow_eq_6]
  apply rowData_ext <;> decide +kernel


def memoRow_22 : RowData := ⟨{(-2, 0), (-1, 0), (0, 1), (1, 1), (2, 1)}, {(-2, 0), (-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1), (3, 1)}, 2⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_22 : rowAt 22 = memoRow_22 := by
  have he : entryAt 22 = entry_22 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 22 < 6 by decide, ↓reduceDIte, he, entry_22, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_3]
  apply rowData_ext <;> decide +kernel


def memoRow_23 : RowData := ⟨{(-2, -1), (-1, -1), (-1, 0), (0, -1), (1, 0)}, {(-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, 0), (2, 0)}, 2⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_23 : rowAt 23 = memoRow_23 := by
  have he : entryAt 23 = entry_23 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 23 < 6 by decide, ↓reduceDIte, he, entry_23, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0]
  apply rowData_ext <;> decide +kernel


def memoRow_24 : RowData := ⟨{(-3, -1), (-2, -1), (-1, -1), (-1, 0)}, {(-4, -1), (-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, 0), (2, 0)}, 3⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_24 : rowAt 24 = memoRow_24 := by
  have he : entryAt 24 = entry_24 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 24 < 6 by decide, ↓reduceDIte, he, entry_24, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_17]
  apply rowData_ext <;> decide +kernel


def memoRow_25 : RowData := ⟨{(-3, -1), (-2, -1), (-1, -1), (-1, 0)}, {(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (1, 0), (2, 0)}, 3⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_25 : rowAt 25 = memoRow_25 := by
  have he : entryAt 25 = entry_25 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 25 < 6 by decide, ↓reduceDIte, he, entry_25, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_14]
  apply rowData_ext <;> decide +kernel


def memoRow_26 : RowData := ⟨{(-2, 0), (-2, 1), (-1, 0), (-1, 1), (1, 0), (1, 1)}, {(-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (1, 0), (1, 1), (2, 0), (2, 1)}, 3⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_26 : rowAt 26 = memoRow_26 := by
  have he : entryAt 26 = entry_26 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 26 < 6 by decide, ↓reduceDIte, he, entry_26, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_6]
  apply rowData_ext <;> decide +kernel


def memoRow_27 : RowData := ⟨{(-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-1, 0)}, {(-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-1, 0), (0, 0), (1, 0)}, 3⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_27 : rowAt 27 = memoRow_27 := by
  have he : entryAt 27 = entry_27 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 27 < 6 by decide, ↓reduceDIte, he, entry_27, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_6]
  apply rowData_ext <;> decide +kernel


def memoRow_28 : RowData := ⟨{(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (1, 0)}, {(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, 0), (2, 0)}, 3⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_28 : rowAt 28 = memoRow_28 := by
  have he : entryAt 28 = entry_28 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 28 < 6 by decide, ↓reduceDIte, he, entry_28, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_6]
  apply rowData_ext <;> decide +kernel


def memoRow_29 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (4, -1)}, {(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (3, -1), (4, -1)}, 3⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_29 : rowAt 29 = memoRow_29 := by
  have he : entryAt 29 = entry_29 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 29 < 6 by decide, ↓reduceDIte, he, entry_29, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_1, memoRow_eq_6]
  apply rowData_ext <;> decide +kernel


def memoRow_30 : RowData := ⟨{(-2, -1), (-1, -1), (0, -1), (1, 0)}, {(-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, 0), (2, 0), (3, 0)}, 3⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_30 : rowAt 30 = memoRow_30 := by
  have he : entryAt 30 = entry_30 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 30 < 6 by decide, ↓reduceDIte, he, entry_30, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_14]
  apply rowData_ext <;> decide +kernel


def memoRow_31 : RowData := ⟨{(-2, 0), (-1, 0), (0, 1), (1, 1)}, {(-3, 0), (-2, 0), (-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1), (3, 1)}, 3⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_31 : rowAt 31 = memoRow_31 := by
  have he : entryAt 31 = entry_31 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 31 < 6 by decide, ↓reduceDIte, he, entry_31, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_17]
  apply rowData_ext <;> decide +kernel


def memoRow_32 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (3, -1)}, {(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (3, -1), (4, -1)}, 3⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_32 : rowAt 32 = memoRow_32 := by
  have he : entryAt 32 = entry_32 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 32 < 6 by decide, ↓reduceDIte, he, entry_32, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_6]
  apply rowData_ext <;> decide +kernel


def memoRow_33 : RowData := ⟨{(-1, 0), (1, 0), (1, 1), (2, 1)}, {(-2, 0), (-1, 0), (0, 0), (1, 0), (1, 1), (2, 0), (2, 1), (3, 1), (4, 1)}, 3⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_33 : rowAt 33 = memoRow_33 := by
  have he : entryAt 33 = entry_33 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 33 < 6 by decide, ↓reduceDIte, he, entry_33, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_17]
  apply rowData_ext <;> decide +kernel


def memoRow_34 : RowData := ⟨{(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (2, 0)}, {(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, 0), (2, 0)}, 3⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_34 : rowAt 34 = memoRow_34 := by
  have he : entryAt 34 = entry_34 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 34 < 6 by decide, ↓reduceDIte, he, entry_34, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_1, memoRow_eq_6]
  apply rowData_ext <;> decide +kernel


def memoRow_35 : RowData := ⟨{(-1, 0), (1, 0), (1, 1), (2, 1)}, {(-2, 0), (-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1), (3, 1), (4, 1)}, 3⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_35 : rowAt 35 = memoRow_35 := by
  have he : entryAt 35 = entry_35 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 35 < 6 by decide, ↓reduceDIte, he, entry_35, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_14]
  apply rowData_ext <;> decide +kernel


def memoRow_36 : RowData := ⟨{(1, 0), (2, 0), (2, 1), (3, 1)}, {(-1, 0), (0, 0), (1, 0), (2, 0), (2, 1), (3, 0), (3, 1), (4, 1), (5, 1)}, 3⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_36 : rowAt 36 = memoRow_36 := by
  have he : entryAt 36 = entry_36 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 36 < 6 by decide, ↓reduceDIte, he, entry_36, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_17]
  apply rowData_ext <;> decide +kernel


def memoRow_37 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0), (3, -1), (4, -1)}, {(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (3, -1), (4, -1)}, 3⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_37 : rowAt 37 = memoRow_37 := by
  have he : entryAt 37 = entry_37 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 37 < 6 by decide, ↓reduceDIte, he, entry_37, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_2, memoRow_eq_6]
  apply rowData_ext <;> decide +kernel


def memoRow_38 : RowData := ⟨{(-4, -1), (-3, -1), (-2, -1), (-1, 0)}, {(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (1, 0)}, 3⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_38 : rowAt 38 = memoRow_38 := by
  have he : entryAt 38 = entry_38 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 38 < 6 by decide, ↓reduceDIte, he, entry_38, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_3, memoRow_eq_16]
  apply rowData_ext <;> decide +kernel


def memoRow_39 : RowData := ⟨{(-2, -1), (-1, -1), (0, -1), (1, 0)}, {(-3, -1), (-2, -1), (-1, -1), (0, -1), (0, 0), (1, -1), (1, 0), (2, 0), (3, 0)}, 3⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_39 : rowAt 39 = memoRow_39 := by
  have he : entryAt 39 = entry_39 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 39 < 6 by decide, ↓reduceDIte, he, entry_39, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_17]
  apply rowData_ext <;> decide +kernel


def memoRow_40 : RowData := ⟨{(-3, -1), (-2, -1), (-1, -1), (1, 0)}, {(-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, 0), (2, 0)}, 3⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_40 : rowAt 40 = memoRow_40 := by
  have he : entryAt 40 = entry_40 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 40 < 6 by decide, ↓reduceDIte, he, entry_40, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_3, memoRow_eq_16]
  apply rowData_ext <;> decide +kernel


def memoRow_41 : RowData := ⟨{(-1, 0), (0, -3), (0, -2), (0, -1), (1, -1), (3, -1)}, {(-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -1), (2, -1), (3, -1)}, 3⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_41 : rowAt 41 = memoRow_41 := by
  have he : entryAt 41 = entry_41 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 41 < 6 by decide, ↓reduceDIte, he, entry_41, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_1, memoRow_eq_6]
  apply rowData_ext <;> decide +kernel


def memoRow_42 : RowData := ⟨{(-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (1, 0)}, {(-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (0, 0), (1, 0), (2, 0)}, 3⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_42 : rowAt 42 = memoRow_42 := by
  have he : entryAt 42 = entry_42 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 42 < 6 by decide, ↓reduceDIte, he, entry_42, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_6]
  apply rowData_ext <;> decide +kernel


def memoRow_43 : RowData := ⟨{(-1, 0), (0, -3), (0, -2), (0, -1), (2, -1), (3, -1)}, {(-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -1), (2, -1), (3, -1)}, 3⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_43 : rowAt 43 = memoRow_43 := by
  have he : entryAt 43 = entry_43 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 43 < 6 by decide, ↓reduceDIte, he, entry_43, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_2, memoRow_eq_6]
  apply rowData_ext <;> decide +kernel


def memoRow_44 : RowData := ⟨{(-4, 0), (-4, 1), (-3, 0), (-2, 0), (-1, 0)}, {(-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, 0), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 1)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_44 : rowAt 44 = memoRow_44 := by
  have he : entryAt 44 = entry_44 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 44 < 6 by decide, ↓reduceDIte, he, entry_44, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_4, memoRow_eq_7]
  apply rowData_ext <;> decide +kernel


def memoRow_45 : RowData := ⟨{(-4, 0), (-3, 0), (-3, 1), (-2, 0), (-1, 0)}, {(-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, 0), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 1)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_45 : rowAt 45 = memoRow_45 := by
  have he : entryAt 45 = entry_45 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 45 < 6 by decide, ↓reduceDIte, he, entry_45, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_7]
  apply rowData_ext <;> decide +kernel


def memoRow_46 : RowData := ⟨{(-4, 0), (-3, -1), (-3, 0), (-2, 0), (-1, 0)}, {(-4, -1), (-4, 0), (-3, -1), (-3, 0), (-2, 0), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 1)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_46 : rowAt 46 = memoRow_46 := by
  have he : entryAt 46 = entry_46 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 46 < 6 by decide, ↓reduceDIte, he, entry_46, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_7]
  apply rowData_ext <;> decide +kernel


def memoRow_47 : RowData := ⟨{(-1, 0), (0, -3), (0, -2), (0, -1), (1, 0), (2, -1), (2, 0)}, {(-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, 0), (2, -1), (2, 0), (3, -1)}, 3⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_47 : rowAt 47 = memoRow_47 := by
  have he : entryAt 47 = entry_47 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 47 < 6 by decide, ↓reduceDIte, he, entry_47, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6]
  apply rowData_ext <;> decide +kernel


def memoRow_48 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (3, -1), (3, 0)}, {(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (3, -1), (3, 0), (4, -1)}, 3⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_48 : rowAt 48 = memoRow_48 := by
  have he : entryAt 48 = entry_48 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 48 < 6 by decide, ↓reduceDIte, he, entry_48, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6]
  apply rowData_ext <;> decide +kernel


def memoRow_49 : RowData := ⟨{(-1, -4), (0, -4), (0, -3), (0, -2), (0, -1)}, {(-1, -4), (-1, -3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_49 : rowAt 49 = memoRow_49 := by
  have he : entryAt 49 = entry_49 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 49 < 6 by decide, ↓reduceDIte, he, entry_49, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_4, memoRow_eq_7]
  apply rowData_ext <;> decide +kernel


def memoRow_50 : RowData := ⟨{(-1, 0), (0, -4), (0, -3), (0, -2), (0, -1)}, {(-1, 0), (-1, 1), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_50 : rowAt 50 = memoRow_50 := by
  have he : entryAt 50 = entry_50 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 50 < 6 by decide, ↓reduceDIte, he, entry_50, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_7]
  apply rowData_ext <;> decide +kernel


def memoRow_51 : RowData := ⟨{(-3, -1), (-3, 0), (-2, -1), (-2, 0), (0, -1)}, {(-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_51 : rowAt 51 = memoRow_51 := by
  have he : entryAt 51 = entry_51 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 51 < 6 by decide, ↓reduceDIte, he, entry_51, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_10, memoRow_eq_26]
  apply rowData_ext <;> decide +kernel


def memoRow_52 : RowData := ⟨{(-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, -1), (1, -1), (2, -1)}, {(-4, -1), (-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (2, -1), (3, -1)}, 2⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_52 : rowAt 52 = memoRow_52 := by
  have he : entryAt 52 = entry_52 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 52 < 6 by decide, ↓reduceDIte, he, entry_52, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0]
  apply rowData_ext <;> decide +kernel


def memoRow_53 : RowData := ⟨{(0, -2), (0, -1), (1, -1), (1, 1), (1, 2), (2, -1), (3, -1)}, {(-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 1), (1, 2), (2, -1), (3, -1)}, 3⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_53 : rowAt 53 = memoRow_53 := by
  have he : entryAt 53 = entry_53 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 53 < 6 by decide, ↓reduceDIte, he, entry_53, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_3, memoRow_eq_6]
  apply rowData_ext <;> decide +kernel


def memoRow_54 : RowData := ⟨{(-4, -1), (-3, -1), (-2, 0), (-1, 0)}, {(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (1, 0)}, 3⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_54 : rowAt 54 = memoRow_54 := by
  have he : entryAt 54 = entry_54 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 54 < 6 by decide, ↓reduceDIte, he, entry_54, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_3, memoRow_eq_22]
  apply rowData_ext <;> decide +kernel


def memoRow_55 : RowData := ⟨{(-4, 0), (-3, 0), (-2, 0), (-1, 0)}, {(-5, 1), (-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, 0), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 1)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_55 : rowAt 55 = memoRow_55 := by
  have he : entryAt 55 = entry_55 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 55 < 6 by decide, ↓reduceDIte, he, entry_55, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_7]
  apply rowData_ext <;> decide +kernel


def memoRow_56 : RowData := ⟨{(-4, 0), (-3, 0), (-2, 0), (-1, 0)}, {(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-1, 0), (0, 0)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_56 : rowAt 56 = memoRow_56 := by
  have he : entryAt 56 = entry_56 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 56 < 6 by decide, ↓reduceDIte, he, entry_56, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_7]
  apply rowData_ext <;> decide +kernel


def memoRow_57 : RowData := ⟨{(-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0)}, {(-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_57 : rowAt 57 = memoRow_57 := by
  have he : entryAt 57 = entry_57 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 57 < 6 by decide, ↓reduceDIte, he, entry_57, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_7]
  apply rowData_ext <;> decide +kernel


def memoRow_58 : RowData := ⟨{(-4, 0), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0)}, {(-4, 0), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_58 : rowAt 58 = memoRow_58 := by
  have he : entryAt 58 = entry_58 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 58 < 6 by decide, ↓reduceDIte, he, entry_58, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_7]
  apply rowData_ext <;> decide +kernel


def memoRow_59 : RowData := ⟨{(-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0)}, {(-5, 1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-1, 0), (0, 0), (1, 0)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_59 : rowAt 59 = memoRow_59 := by
  have he : entryAt 59 = entry_59 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 59 < 6 by decide, ↓reduceDIte, he, entry_59, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_7]
  apply rowData_ext <;> decide +kernel


def memoRow_60 : RowData := ⟨{(-2, -1), (-2, 0), (-1, 0), (1, 0)}, {(-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (1, 0), (1, 1), (2, 0), (2, 1), (3, 1)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_60 : rowAt 60 = memoRow_60 := by
  have he : entryAt 60 = entry_60 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 60 < 6 by decide, ↓reduceDIte, he, entry_60, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_49]
  apply rowData_ext <;> decide +kernel


def memoRow_61 : RowData := ⟨{(-3, -1), (-2, -1), (-1, -3), (-1, -2), (-1, -1), (0, -1)}, {(-3, -1), (-2, -1), (-1, -3), (-1, -2), (-1, -1), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0)}, 3⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_61 : rowAt 61 = memoRow_61 := by
  have he : entryAt 61 = entry_61 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 61 < 6 by decide, ↓reduceDIte, he, entry_61, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_14]
  apply rowData_ext <;> decide +kernel


def memoRow_62 : RowData := ⟨{(-3, -1), (-3, 0), (-2, 0), (-2, 2), (-2, 3), (-1, 0)}, {(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, 0), (-2, 2), (-2, 3), (-1, 0), (0, 0)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_62 : rowAt 62 = memoRow_62 := by
  have he : entryAt 62 = entry_62 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 62 < 6 by decide, ↓reduceDIte, he, entry_62, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_53]
  apply rowData_ext <;> decide +kernel


def memoRow_63 : RowData := ⟨{(1, -4), (1, -3), (1, -2), (1, -1)}, {(0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_63 : rowAt 63 = memoRow_63 := by
  have he : entryAt 63 = entry_63 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 63 < 6 by decide, ↓reduceDIte, he, entry_63, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_4, memoRow_eq_50]
  apply rowData_ext <;> decide +kernel


def memoRow_64 : RowData := ⟨{(0, 1), (1, 1), (2, 1), (3, 1)}, {(-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1), (3, 1), (3, 2), (4, 1), (4, 2), (5, 2)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_64 : rowAt 64 = memoRow_64 := by
  have he : entryAt 64 = entry_64 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 64 < 6 by decide, ↓reduceDIte, he, entry_64, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_49]
  apply rowData_ext <;> decide +kernel


def memoRow_65 : RowData := ⟨{(-3, -1), (-3, 0), (-2, 0), (-1, 0)}, {(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_65 : rowAt 65 = memoRow_65 := by
  have he : entryAt 65 = entry_65 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 65 < 6 by decide, ↓reduceDIte, he, entry_65, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_49]
  apply rowData_ext <;> decide +kernel


def memoRow_66 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0), (3, -1), (4, -1)}, {(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (2, 1), (3, -1), (3, 0), (4, -1)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_66 : rowAt 66 = memoRow_66 := by
  have he : entryAt 66 = entry_66 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 66 < 6 by decide, ↓reduceDIte, he, entry_66, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_53]
  apply rowData_ext <;> decide +kernel


def memoRow_67 : RowData := ⟨{(-2, -1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0)}, {(-3, -1), (-2, -1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, 0), (2, 0)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_67 : rowAt 67 = memoRow_67 := by
  have he : entryAt 67 = entry_67 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 67 < 6 by decide, ↓reduceDIte, he, entry_67, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_9]
  apply rowData_ext <;> decide +kernel


def memoRow_68 : RowData := ⟨{(-3, 0), (-3, 1), (-2, 0), (-1, 0)}, {(-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_68 : rowAt 68 = memoRow_68 := by
  have he : entryAt 68 = entry_68 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 68 < 6 by decide, ↓reduceDIte, he, entry_68, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_44]
  apply rowData_ext <;> decide +kernel


def memoRow_69 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (4, 1)}, {(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, 1), (2, 2), (3, 1), (4, 1)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_69 : rowAt 69 = memoRow_69 := by
  have he : entryAt 69 = entry_69 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 69 < 6 by decide, ↓reduceDIte, he, entry_69, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_34]
  apply rowData_ext <;> decide +kernel


def memoRow_70 : RowData := ⟨{(1, -4), (1, -3), (1, -2), (1, -1), (2, -1), (4, -1)}, {(0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (3, -1), (4, -1)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_70 : rowAt 70 = memoRow_70 := by
  have he : entryAt 70 = entry_70 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 70 < 6 by decide, ↓reduceDIte, he, entry_70, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_4, memoRow_eq_41]
  apply rowData_ext <;> decide +kernel


def memoRow_71 : RowData := ⟨{(-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (1, -1)}, {(-3, 0), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (2, -1)}, 3⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_71 : rowAt 71 = memoRow_71 := by
  have he : entryAt 71 = entry_71 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 71 < 6 by decide, ↓reduceDIte, he, entry_71, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_23]
  apply rowData_ext <;> decide +kernel


def memoRow_72 : RowData := ⟨{(-2, 1), (-1, 1), (-1, 2), (-1, 3), (0, 1), (1, 1)}, {(-3, 1), (-2, 1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_72 : rowAt 72 = memoRow_72 := by
  have he : entryAt 72 = entry_72 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 72 < 6 by decide, ↓reduceDIte, he, entry_72, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_8]
  apply rowData_ext <;> decide +kernel


def memoRow_73 : RowData := ⟨{(-1, 1), (0, -3), (0, -2), (0, -1)}, {(-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_73 : rowAt 73 = memoRow_73 := by
  have he : entryAt 73 = entry_73 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 73 < 6 by decide, ↓reduceDIte, he, entry_73, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_4, memoRow_eq_50]
  apply rowData_ext <;> decide +kernel


def memoRow_74 : RowData := ⟨{(-1, -3), (-1, -2), (0, -2), (0, 1), (1, -2), (2, -2)}, {(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (2, -2)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_74 : rowAt 74 = memoRow_74 := by
  have he : entryAt 74 = entry_74 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 74 < 6 by decide, ↓reduceDIte, he, entry_74, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_2, memoRow_eq_53]
  apply rowData_ext <;> decide +kernel


def memoRow_75 : RowData := ⟨{(-2, -1), (-1, -1), (0, -1), (1, -1), (1, 0), (2, -1)}, {(-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (3, -1), (4, -1)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_75 : rowAt 75 = memoRow_75 := by
  have he : entryAt 75 = entry_75 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 75 < 6 by decide, ↓reduceDIte, he, entry_75, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_9]
  apply rowData_ext <;> decide +kernel


def memoRow_76 : RowData := ⟨{(-1, 0), (0, -1), (1, 0), (1, 1), (1, 2), (2, 1)}, {(-1, 0), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 1), (3, 1), (4, 1)}, 3⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_76 : rowAt 76 = memoRow_76 := by
  have he : entryAt 76 = entry_76 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 76 < 6 by decide, ↓reduceDIte, he, entry_76, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_14]
  apply rowData_ext <;> decide +kernel


def memoRow_77 : RowData := ⟨{(-2, -1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -1)}, {(-3, -1), (-2, -1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (1, 0), (2, 0)}, 3⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_77 : rowAt 77 = memoRow_77 := by
  have he : entryAt 77 = entry_77 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 77 < 6 by decide, ↓reduceDIte, he, entry_77, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_12]
  apply rowData_ext <;> decide +kernel


def memoRow_78 : RowData := ⟨{(-2, -1), (-1, -1), (0, -1), (1, -1), (2, -1), (3, -1)}, {(-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (3, -1), (4, -1)}, 3⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_78 : rowAt 78 = memoRow_78 := by
  have he : entryAt 78 = entry_78 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 78 < 6 by decide, ↓reduceDIte, he, entry_78, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_52]
  apply rowData_ext <;> decide +kernel


def memoRow_79 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, 0), (2, -1), (2, 0)}, {(-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, 0), (1, 1), (2, -1), (2, 0), (3, -1)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_79 : rowAt 79 = memoRow_79 := by
  have he : entryAt 79 = entry_79 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 79 < 6 by decide, ↓reduceDIte, he, entry_79, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_48]
  apply rowData_ext <;> decide +kernel


def memoRow_80 : RowData := ⟨{(-2, -1), (-1, -1), (-1, 0), (1, -1), (1, 0), (1, 1)}, {(-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_80 : rowAt 80 = memoRow_80 := by
  have he : entryAt 80 = entry_80 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 80 < 6 by decide, ↓reduceDIte, he, entry_80, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_13]
  apply rowData_ext <;> decide +kernel


def memoRow_81 : RowData := ⟨{(1, -4), (1, -3), (1, -2), (1, -1), (3, -1), (4, -1)}, {(0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (3, -1), (4, -1)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_81 : rowAt 81 = memoRow_81 := by
  have he : entryAt 81 = entry_81 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 81 < 6 by decide, ↓reduceDIte, he, entry_81, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_4, memoRow_eq_43]
  apply rowData_ext <;> decide +kernel


def memoRow_82 : RowData := ⟨{(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0)}, {(-4, -1), (-3, -1), (-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, 0), (2, 0)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_82 : rowAt 82 = memoRow_82 := by
  have he : entryAt 82 = entry_82 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 82 < 6 by decide, ↓reduceDIte, he, entry_82, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_36]
  apply rowData_ext <;> decide +kernel


def memoRow_83 : RowData := ⟨{(0, -1), (1, -1), (1, 0), (1, 1), (1, 2)}, {(-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (3, -1), (4, -1)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_83 : rowAt 83 = memoRow_83 := by
  have he : entryAt 83 = entry_83 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 83 < 6 by decide, ↓reduceDIte, he, entry_83, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_67]
  apply rowData_ext <;> decide +kernel


def memoRow_84 : RowData := ⟨{(0, -1), (1, -3), (1, -2), (1, -1), (1, 0)}, {(-1, -1), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (2, 1), (3, 0), (4, 0)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_84 : rowAt 84 = memoRow_84 := by
  have he : entryAt 84 = entry_84 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 84 < 6 by decide, ↓reduceDIte, he, entry_84, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_67]
  apply rowData_ext <;> decide +kernel


def memoRow_85 : RowData := ⟨{(-2, -1), (-1, -1), (-1, 0), (0, -1), (1, -1)}, {(-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_85 : rowAt 85 = memoRow_85 := by
  have he : entryAt 85 = entry_85 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 85 < 6 by decide, ↓reduceDIte, he, entry_85, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_8, memoRow_eq_9]
  apply rowData_ext <;> decide +kernel


def memoRow_86 : RowData := ⟨{(-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0)}, {(-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-1, 0), (0, 0), (1, 0)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_86 : rowAt 86 = memoRow_86 := by
  have he : entryAt 86 = entry_86 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 86 < 6 by decide, ↓reduceDIte, he, entry_86, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_67]
  apply rowData_ext <;> decide +kernel


def memoRow_87 : RowData := ⟨{(-2, 0), (-1, 0), (-1, 1), (-1, 2), (0, -1)}, {(-3, 0), (-2, 0), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (3, -1)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_87 : rowAt 87 = memoRow_87 := by
  have he : entryAt 87 = entry_87 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 87 < 6 by decide, ↓reduceDIte, he, entry_87, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_24]
  apply rowData_ext <;> decide +kernel


def memoRow_88 : RowData := ⟨{(-2, -1), (-2, 0), (-1, -1), (-1, 0), (1, 0)}, {(-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (1, 0), (2, 0)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_88 : rowAt 88 = memoRow_88 := by
  have he : entryAt 88 = entry_88 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 88 < 6 by decide, ↓reduceDIte, he, entry_88, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_67]
  apply rowData_ext <;> decide +kernel


def memoRow_89 : RowData := ⟨{(-1, -2), (0, -4), (0, -3), (0, -2), (0, -1)}, {(-1, -4), (-1, -3), (-1, -2), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_89 : rowAt 89 = memoRow_89 := by
  have he : entryAt 89 = entry_89 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 89 < 6 by decide, ↓reduceDIte, he, entry_89, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_7, memoRow_eq_8]
  apply rowData_ext <;> decide +kernel


def memoRow_90 : RowData := ⟨{(-3, -1), (-2, -1), (-1, 0)}, {(-5, -1), (-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, 0), (2, 0)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_90 : rowAt 90 = memoRow_90 := by
  have he : entryAt 90 = entry_90 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 90 < 6 by decide, ↓reduceDIte, he, entry_90, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_31, memoRow_eq_54]
  apply rowData_ext <;> decide +kernel


def memoRow_91 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0), (4, -1)}, {(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (4, -1)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_91 : rowAt 91 = memoRow_91 := by
  have he : entryAt 91 = entry_91 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 91 < 6 by decide, ↓reduceDIte, he, entry_91, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_74]
  apply rowData_ext <;> decide +kernel


def memoRow_92 : RowData := ⟨{(-3, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0)}, {(-4, -1), (-3, -1), (-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, 0), (2, 0)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_92 : rowAt 92 = memoRow_92 := by
  have he : entryAt 92 = entry_92 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 92 < 6 by decide, ↓reduceDIte, he, entry_92, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_33]
  apply rowData_ext <;> decide +kernel


def memoRow_93 : RowData := ⟨{(1, -4), (1, -3), (1, -2), (1, -1), (2, 0), (3, -1), (3, 0)}, {(0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (3, -1), (3, 0), (4, -1)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_93 : rowAt 93 = memoRow_93 := by
  have he : entryAt 93 = entry_93 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 93 < 6 by decide, ↓reduceDIte, he, entry_93, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_4, memoRow_eq_47]
  apply rowData_ext <;> decide +kernel


def memoRow_94 : RowData := ⟨{(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -1)}, {(-2, -2), (-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_94 : rowAt 94 = memoRow_94 := by
  have he : entryAt 94 = entry_94 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 94 < 6 by decide, ↓reduceDIte, he, entry_94, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_27]
  apply rowData_ext <;> decide +kernel


def memoRow_95 : RowData := ⟨{(-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -1), (2, 0)}, {(-2, 1), (-2, 2), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (1, 0), (2, 0)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_95 : rowAt 95 = memoRow_95 := by
  have he : entryAt 95 = entry_95 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 95 < 6 by decide, ↓reduceDIte, he, entry_95, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_29]
  apply rowData_ext <;> decide +kernel


def memoRow_96 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, 0), (3, 0)}, {(-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (3, 0)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_96 : rowAt 96 = memoRow_96 := by
  have he : entryAt 96 = entry_96 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 96 < 6 by decide, ↓reduceDIte, he, entry_96, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_70]
  apply rowData_ext <;> decide +kernel


def memoRow_97 : RowData := ⟨{(-3, -1), (-3, 0), (-3, 1), (-2, 0), (-1, 0)}, {(-4, -1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_97 : rowAt 97 = memoRow_97 := by
  have he : entryAt 97 = entry_97 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 97 < 6 by decide, ↓reduceDIte, he, entry_97, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_44]
  apply rowData_ext <;> decide +kernel


def memoRow_98 : RowData := ⟨{(-1, -1), (-1, 0), (-1, 1), (1, 0), (2, 0)}, {(-2, -1), (-1, -1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (2, 0), (2, 1), (3, 0), (3, 1), (4, 1)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_98 : rowAt 98 = memoRow_98 := by
  have he : entryAt 98 = entry_98 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 98 < 6 by decide, ↓reduceDIte, he, entry_98, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_44]
  apply rowData_ext <;> decide +kernel


def memoRow_99 : RowData := ⟨{(-2, -1), (-1, -4), (-1, -3), (-1, -1), (0, -1)}, {(-3, -1), (-2, -1), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (0, -1), (0, 0), (1, -1), (1, 0), (2, 0), (3, 0)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_99 : rowAt 99 = memoRow_99 := by
  have he : entryAt 99 = entry_99 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 99 < 6 by decide, ↓reduceDIte, he, entry_99, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_2, memoRow_eq_24]
  apply rowData_ext <;> decide +kernel


def memoRow_100 : RowData := ⟨{(-3, -1), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-1, 0), (0, -1)}, {(-3, -1), (-3, 0), (-3, 1), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_100 : rowAt 100 = memoRow_100 := by
  have he : entryAt 100 = entry_100 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 100 < 6 by decide, ↓reduceDIte, he, entry_100, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_48]
  apply rowData_ext <;> decide +kernel


def memoRow_101 : RowData := ⟨{(-2, -1), (-1, -2), (-1, -1), (0, -1), (0, 1)}, {(-3, -1), (-2, -1), (-1, -2), (-1, -1), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (2, 0), (3, 0)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_101 : rowAt 101 = memoRow_101 := by
  have he : entryAt 101 = entry_101 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 101 < 6 by decide, ↓reduceDIte, he, entry_101, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_24]
  apply rowData_ext <;> decide +kernel


def memoRow_102 : RowData := ⟨{(-1, 0), (1, -3), (1, -2), (1, -1), (1, 0)}, {(-2, 0), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (3, -1), (4, -1)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_102 : rowAt 102 = memoRow_102 := by
  have he : entryAt 102 = entry_102 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 102 < 6 by decide, ↓reduceDIte, he, entry_102, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_25]
  apply rowData_ext <;> decide +kernel


def memoRow_103 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0), (3, -1)}, {(-1, 0), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (3, -1), (4, -1)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_103 : rowAt 103 = memoRow_103 := by
  have he : entryAt 103 = entry_103 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 103 < 6 by decide, ↓reduceDIte, he, entry_103, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_71]
  apply rowData_ext <;> decide +kernel


def memoRow_104 : RowData := ⟨{(-3, -1), (-2, -1), (-1, -1), (0, -1), (1, -1)}, {(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (3, -1)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_104 : rowAt 104 = memoRow_104 := by
  have he : entryAt 104 = entry_104 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 104 < 6 by decide, ↓reduceDIte, he, entry_104, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_75]
  apply rowData_ext <;> decide +kernel


def memoRow_105 : RowData := ⟨{(-2, 0), (-1, 0), (-1, 1), (-1, 2), (-1, 3)}, {(-3, 0), (-2, 0), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (1, 1), (2, 1)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_105 : rowAt 105 = memoRow_105 := by
  have he : entryAt 105 = entry_105 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 105 < 6 by decide, ↓reduceDIte, he, entry_105, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_77]
  apply rowData_ext <;> decide +kernel


def memoRow_106 : RowData := ⟨{(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0)}, {(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, 0), (2, 0)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_106 : rowAt 106 = memoRow_106 := by
  have he : entryAt 106 = entry_106 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 106 < 6 by decide, ↓reduceDIte, he, entry_106, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_36]
  apply rowData_ext <;> decide +kernel


def memoRow_107 : RowData := ⟨{(-3, -1), (-3, 0), (-2, 0), (-1, 0)}, {(-4, -1), (-3, -1), (-3, 0), (-2, 0), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_107 : rowAt 107 = memoRow_107 := by
  have he : entryAt 107 = entry_107 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 107 < 6 by decide, ↓reduceDIte, he, entry_107, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_63]
  apply rowData_ext <;> decide +kernel


def memoRow_108 : RowData := ⟨{(-4, -1), (-3, 0), (-2, 0), (-1, 0)}, {(-4, -1), (-3, -1), (-3, 0), (-2, 0), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_108 : rowAt 108 = memoRow_108 := by
  have he : entryAt 108 = entry_108 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 108 < 6 by decide, ↓reduceDIte, he, entry_108, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_4, memoRow_eq_63]
  apply rowData_ext <;> decide +kernel


def memoRow_109 : RowData := ⟨{(-4, -1), (-3, 0), (-2, 0), (-1, 0)}, {(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_109 : rowAt 109 = memoRow_109 := by
  have he : entryAt 109 = entry_109 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 109 < 6 by decide, ↓reduceDIte, he, entry_109, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_4, memoRow_eq_55]
  apply rowData_ext <;> decide +kernel


def memoRow_110 : RowData := ⟨{(-2, -1), (-2, 0), (-1, 0), (1, 0)}, {(-3, -1), (-2, -1), (-2, 0), (-1, 0), (0, 0), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_110 : rowAt 110 = memoRow_110 := by
  have he : entryAt 110 = entry_110 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 110 < 6 by decide, ↓reduceDIte, he, entry_110, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_63]
  apply rowData_ext <;> decide +kernel


def memoRow_111 : RowData := ⟨{(1, 0), (1, 1), (1, 2), (1, 3)}, {(-1, 1), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (3, 0), (4, 0)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_111 : rowAt 111 = memoRow_111 := by
  have he : entryAt 111 = entry_111 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 111 < 6 by decide, ↓reduceDIte, he, entry_111, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_83]
  apply rowData_ext <;> decide +kernel


def memoRow_112 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, 1), (2, 0), (2, 1)}, {(-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_112 : rowAt 112 = memoRow_112 := by
  have he : entryAt 112 = entry_112 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 112 < 6 by decide, ↓reduceDIte, he, entry_112, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_4, memoRow_eq_93]
  apply rowData_ext <;> decide +kernel


def memoRow_113 : RowData := ⟨{(-1, -1), (0, -1), (1, 0), (1, 1), (2, 1), (3, 0)}, {(-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (4, 1)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_113 : rowAt 113 = memoRow_113 := by
  have he : entryAt 113 = entry_113 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 113 < 6 by decide, ↓reduceDIte, he, entry_113, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_1, memoRow_eq_36]
  apply rowData_ext <;> decide +kernel


def memoRow_114 : RowData := ⟨{(-2, -1), (-2, 0), (-1, -1), (-1, 0), (1, 0), (1, 1)}, {(-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (1, 0), (1, 1), (2, 1)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_114 : rowAt 114 = memoRow_114 := by
  have he : entryAt 114 = entry_114 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 114 < 6 by decide, ↓reduceDIte, he, entry_114, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_67]
  apply rowData_ext <;> decide +kernel


def memoRow_115 : RowData := ⟨{(-1, -3), (-1, -1), (-1, 0), (1, 0), (2, -1), (2, 0)}, {(-3, 1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, 0), (1, 0), (2, -1), (2, 0), (3, -1)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_115 : rowAt 115 = memoRow_115 := by
  have he : entryAt 115 = entry_115 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 115 < 6 by decide, ↓reduceDIte, he, entry_115, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_70]
  apply rowData_ext <;> decide +kernel


def memoRow_116 : RowData := ⟨{(-2, 1), (-1, -2), (-1, -1), (-1, 1), (0, -1), (0, 1)}, {(-3, 1), (-2, 1), (-1, -2), (-1, -1), (-1, 1), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 0), (3, 0)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_116 : rowAt 116 = memoRow_116 := by
  have he : entryAt 116 = entry_116 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 116 < 6 by decide, ↓reduceDIte, he, entry_116, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_24]
  apply rowData_ext <;> decide +kernel


def memoRow_117 : RowData := ⟨{(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (1, -1)}, {(-2, -1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, -1), (1, 0), (2, -1), (2, 0)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_117 : rowAt 117 = memoRow_117 := by
  have he : entryAt 117 = entry_117 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 117 < 6 by decide, ↓reduceDIte, he, entry_117, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_100]
  apply rowData_ext <;> decide +kernel


def memoRow_118 : RowData := ⟨{(-2, -1), (-1, -4), (-1, -1), (0, -3), (0, -2), (0, -1)}, {(-2, -1), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (1, 0), (1, 1), (2, 0), (3, 0)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_118 : rowAt 118 = memoRow_118 := by
  have he : entryAt 118 = entry_118 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 118 < 6 by decide, ↓reduceDIte, he, entry_118, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_4, memoRow_eq_61]
  apply rowData_ext <;> decide +kernel


def memoRow_119 : RowData := ⟨{(-2, -1), (-2, 0), (-1, 0), (1, 0)}, {(-3, -1), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (1, 0), (1, 1), (2, 0), (2, 1), (3, 1)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_119 : rowAt 119 = memoRow_119 := by
  have he : entryAt 119 = entry_119 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 119 < 6 by decide, ↓reduceDIte, he, entry_119, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_55]
  apply rowData_ext <;> decide +kernel


def memoRow_120 : RowData := ⟨{(-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (1, 1)}, {(-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_120 : rowAt 120 = memoRow_120 := by
  have he : entryAt 120 = entry_120 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 120 < 6 by decide, ↓reduceDIte, he, entry_120, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_4, memoRow_eq_58]
  apply rowData_ext <;> decide +kernel


def memoRow_121 : RowData := ⟨{(-1, -2), (-1, -1), (0, -4), (0, -3), (0, -2), (0, -1)}, {(-1, -3), (-1, -2), (-1, -1), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (1, 1)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_121 : rowAt 121 = memoRow_121 := by
  have he : entryAt 121 = entry_121 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 121 < 6 by decide, ↓reduceDIte, he, entry_121, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_7, memoRow_eq_9]
  apply rowData_ext <;> decide +kernel


def memoRow_122 : RowData := ⟨{(0, -1), (1, 0), (2, 0), (3, 0)}, {(-1, -1), (-1, 1), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 0), (3, 0), (4, 0)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_122 : rowAt 122 = memoRow_122 := by
  have he : entryAt 122 = entry_122 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 122 < 6 by decide, ↓reduceDIte, he, entry_122, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_105]
  apply rowData_ext <;> decide +kernel


def memoRow_123 : RowData := ⟨{(-2, -1), (-2, 0), (-1, 0), (1, 0)}, {(-3, -1), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_123 : rowAt 123 = memoRow_123 := by
  have he : entryAt 123 = entry_123 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 123 < 6 by decide, ↓reduceDIte, he, entry_123, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_64]
  apply rowData_ext <;> decide +kernel


def memoRow_124 : RowData := ⟨{(-1, -3), (-1, -2), (-1, -1), (-1, 0), (1, -1), (2, -1)}, {(-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (4, -1)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_124 : rowAt 124 = memoRow_124 := by
  have he : entryAt 124 = entry_124 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 124 < 6 by decide, ↓reduceDIte, he, entry_124, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_31]
  apply rowData_ext <;> decide +kernel


def memoRow_125 : RowData := ⟨{(-3, -1), (-2, -1), (-2, 1), (-1, -1), (-1, 1), (1, 0)}, {(-3, -1), (-3, 1), (-2, -1), (-2, 1), (-1, -1), (-1, 1), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (3, 0)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_125 : rowAt 125 = memoRow_125 := by
  have he : entryAt 125 = entry_125 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 125 < 6 by decide, ↓reduceDIte, he, entry_125, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_3, memoRow_eq_31]
  apply rowData_ext <;> decide +kernel


def memoRow_126 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2)}, {(0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (2, 4)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_126 : rowAt 126 = memoRow_126 := by
  have he : entryAt 126 = entry_126 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 126 < 6 by decide, ↓reduceDIte, he, entry_126, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_46]
  apply rowData_ext <;> decide +kernel


def memoRow_127 : RowData := ⟨{(-4, 0), (-3, -1), (-3, 0), (-2, 0), (-1, 0)}, {(-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_127 : rowAt 127 = memoRow_127 := by
  have he : entryAt 127 = entry_127 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 127 < 6 by decide, ↓reduceDIte, he, entry_127, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_7, memoRow_eq_44]
  apply rowData_ext <;> decide +kernel


def memoRow_128 : RowData := ⟨{(-2, 1), (-1, 0), (-1, 1), (0, 1), (1, 1)}, {(-4, 1), (-3, 1), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, 1), (2, 2), (3, 1), (3, 2)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_128 : rowAt 128 = memoRow_128 := by
  have he : entryAt 128 = entry_128 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 128 < 6 by decide, ↓reduceDIte, he, entry_128, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_9, memoRow_eq_57]
  apply rowData_ext <;> decide +kernel


def memoRow_129 : RowData := ⟨{(-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -1), (1, 0), (2, 0)}, {(-2, 1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (2, 0)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_129 : rowAt 129 = memoRow_129 := by
  have he : entryAt 129 = entry_129 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 129 < 6 by decide, ↓reduceDIte, he, entry_129, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_58]
  apply rowData_ext <;> decide +kernel


def memoRow_130 : RowData := ⟨{(-1, -3), (-1, -2), (-1, -1), (-1, 0), (2, 0)}, {(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, 0), (2, 0), (2, 1), (3, 0), (3, 1), (4, 1)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_130 : rowAt 130 = memoRow_130 := by
  have he : entryAt 130 = entry_130 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 130 < 6 by decide, ↓reduceDIte, he, entry_130, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_60]
  apply rowData_ext <;> decide +kernel


def memoRow_131 : RowData := ⟨{(-1, -2), (0, -4), (0, -3), (0, -2), (0, -1)}, {(-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_131 : rowAt 131 = memoRow_131 := by
  have he : entryAt 131 = entry_131 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 131 < 6 by decide, ↓reduceDIte, he, entry_131, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_7, memoRow_eq_45]
  apply rowData_ext <;> decide +kernel


def memoRow_132 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0), (1, 1)}, {(0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (2, 3)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_132 : rowAt 132 = memoRow_132 := by
  have he : entryAt 132 = entry_132 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 132 < 6 by decide, ↓reduceDIte, he, entry_132, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_89]
  apply rowData_ext <;> decide +kernel


def memoRow_133 : RowData := ⟨{(-2, 0), (-1, -2), (0, -2), (0, -1), (0, 1)}, {(-3, 0), (-2, 0), (-1, -3), (-1, -2), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, 1), (3, 1)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_133 : rowAt 133 = memoRow_133 := by
  have he : entryAt 133 = entry_133 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 133 < 6 by decide, ↓reduceDIte, he, entry_133, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_92]
  apply rowData_ext <;> decide +kernel


def memoRow_134 : RowData := ⟨{(-1, -3), (-1, -1), (0, -3), (0, -2), (0, -1)}, {(-3, -1), (-2, -1), (-1, -4), (-1, -3), (-1, -1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, 0), (3, 0)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_134 : rowAt 134 = memoRow_134 := by
  have he : entryAt 134 = entry_134 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 134 < 6 by decide, ↓reduceDIte, he, entry_134, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_82]
  apply rowData_ext <;> decide +kernel


def memoRow_135 : RowData := ⟨{(-4, 0), (-3, 0), (-3, 1), (-2, 0), (-1, 0)}, {(-6, 0), (-5, 0), (-4, 0), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_135 : rowAt 135 = memoRow_135 := by
  have he : entryAt 135 = entry_135 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 135 < 6 by decide, ↓reduceDIte, he, entry_135, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_7, memoRow_eq_44, memoRow_eq_75]
  apply rowData_ext <;> decide +kernel


def memoRow_136 : RowData := ⟨{(-2, -1), (-1, 2), (0, -1), (0, 1), (0, 2)}, {(-3, -1), (-2, -1), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (2, 0), (3, 0)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_136 : rowAt 136 = memoRow_136 := by
  have he : entryAt 136 = entry_136 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 136 < 6 by decide, ↓reduceDIte, he, entry_136, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_102]
  apply rowData_ext <;> decide +kernel


def memoRow_137 : RowData := ⟨{(-1, -4), (-1, -3), (-1, -2), (-1, -1), (2, 0)}, {(-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, 0), (2, 0)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_137 : rowAt 137 = memoRow_137 := by
  have he : entryAt 137 = entry_137 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 137 < 6 by decide, ↓reduceDIte, he, entry_137, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_4, memoRow_eq_96]
  apply rowData_ext <;> decide +kernel


def memoRow_138 : RowData := ⟨{(-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 2), (0, 2)}, {(-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (2, 0)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_138 : rowAt 138 = memoRow_138 := by
  have he : entryAt 138 = entry_138 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 138 < 6 by decide, ↓reduceDIte, he, entry_138, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_10, memoRow_eq_27]
  apply rowData_ext <;> decide +kernel


def memoRow_139 : RowData := ⟨{(-3, 0), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (0, 2)}, {(-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (2, 0)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_139 : rowAt 139 = memoRow_139 := by
  have he : entryAt 139 = entry_139 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 139 < 6 by decide, ↓reduceDIte, he, entry_139, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_27, memoRow_eq_28]
  apply rowData_ext <;> decide +kernel


def memoRow_140 : RowData := ⟨{(-1, -1), (-1, 1), (0, -1), (0, 1), (0, 2)}, {(-3, 1), (-2, 1), (-1, -2), (-1, -1), (-1, 1), (0, -1), (0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (1, 3), (2, 2), (3, 2)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_140 : rowAt 140 = memoRow_140 := by
  have he : entryAt 140 = entry_140 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 140 < 6 by decide, ↓reduceDIte, he, entry_140, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_82]
  apply rowData_ext <;> decide +kernel


def memoRow_141 : RowData := ⟨{(-5, 0), (-4, 0), (-3, 0), (-2, 0), (-1, 0)}, {(-6, 0), (-5, 0), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_141 : rowAt 141 = memoRow_141 := by
  have he : entryAt 141 = entry_141 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 141 < 6 by decide, ↓reduceDIte, he, entry_141, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_7, memoRow_eq_78]
  apply rowData_ext <;> decide +kernel


def memoRow_142 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0), (-1, 1), (-1, 2)}, {(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_142 : rowAt 142 = memoRow_142 := by
  have he : entryAt 142 = entry_142 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 142 < 6 by decide, ↓reduceDIte, he, entry_142, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_32, memoRow_eq_55, memoRow_eq_72]
  apply rowData_ext <;> decide +kernel


def memoRow_143 : RowData := ⟨{(0, 1), (1, 1), (2, 1), (3, 1)}, {(-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1), (3, 1), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 0), (6, 2)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_143 : rowAt 143 = memoRow_143 := by
  have he : entryAt 143 = entry_143 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 143 < 6 by decide, ↓reduceDIte, he, entry_143, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_108]
  apply rowData_ext <;> decide +kernel


def memoRow_144 : RowData := ⟨{(-4, 0), (-3, 0), (-2, 0), (-1, 0)}, {(-6, 0), (-5, 0), (-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_144 : rowAt 144 = memoRow_144 := by
  have he : entryAt 144 = entry_144 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 144 < 6 by decide, ↓reduceDIte, he, entry_144, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_7, memoRow_eq_55, memoRow_eq_104]
  apply rowData_ext <;> decide +kernel


def memoRow_145 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, -3), (1, -2), (3, -1)}, {(-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (3, -1)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_145 : rowAt 145 = memoRow_145 := by
  have he : entryAt 145 = entry_145 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 145 < 6 by decide, ↓reduceDIte, he, entry_145, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_91]
  apply rowData_ext <;> decide +kernel


def memoRow_146 : RowData := ⟨{(-2, -1), (-1, -2), (-1, -1), (-1, 0)}, {(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (2, 0)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_146 : rowAt 146 = memoRow_146 := by
  have he : entryAt 146 = entry_146 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 146 < 6 by decide, ↓reduceDIte, he, entry_146, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_24, memoRow_eq_36]
  apply rowData_ext <;> decide +kernel


def memoRow_147 : RowData := ⟨{(-3, -1), (-3, 0), (-2, 0), (-2, 2), (-2, 3), (-1, 0)}, {(-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -1), (-2, 0), (-2, 2), (-2, 3), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_147 : rowAt 147 = memoRow_147 := by
  have he : entryAt 147 = entry_147 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 147 < 6 by decide, ↓reduceDIte, he, entry_147, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_44, memoRow_eq_53]
  apply rowData_ext <;> decide +kernel


def memoRow_148 : RowData := ⟨{(-1, -2), (0, -4), (0, -3), (0, -2), (0, -1), (1, -2)}, {(-1, -3), (-1, -2), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_148 : rowAt 148 = memoRow_148 := by
  have he : entryAt 148 = entry_148 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 148 < 6 by decide, ↓reduceDIte, he, entry_148, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_7, memoRow_eq_46, memoRow_eq_94, memoRow_eq_97]
  apply rowData_ext <;> decide +kernel


def memoRow_149 : RowData := ⟨{(-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 1), (0, 1)}, {(-3, 1), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 1), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 0), (3, 0)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_149 : rowAt 149 = memoRow_149 := by
  have he : entryAt 149 = entry_149 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 149 < 6 by decide, ↓reduceDIte, he, entry_149, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_16, memoRow_eq_24]
  apply rowData_ext <;> decide +kernel


def memoRow_150 : RowData := ⟨{(-5, 0), (-4, -1), (-4, 0), (-3, 0), (-2, 0), (-1, 0)}, {(-5, 0), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_150 : rowAt 150 = memoRow_150 := by
  have he : entryAt 150 = entry_150 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 150 < 6 by decide, ↓reduceDIte, he, entry_150, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_4, memoRow_eq_126]
  apply rowData_ext <;> decide +kernel


def memoRow_151 : RowData := ⟨{(0, -3), (0, -2), (1, 0), (1, 1), (2, -2), (2, 0)}, {(-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (1, 0), (1, 1), (2, -3), (2, -2), (2, -1), (2, 0), (3, -1), (3, 0), (4, -1), (5, -1)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_151 : rowAt 151 = memoRow_151 := by
  have he : entryAt 151 = entry_151 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 151 < 6 by decide, ↓reduceDIte, he, entry_151, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_2, memoRow_eq_101]
  apply rowData_ext <;> decide +kernel


def memoRow_152 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (4, -1)}, {(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 1)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_152 : rowAt 152 = memoRow_152 := by
  have he : entryAt 152 = entry_152 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 152 < 6 by decide, ↓reduceDIte, he, entry_152, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_73]
  apply rowData_ext <;> decide +kernel


def memoRow_153 : RowData := ⟨{(-3, 0), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0)}, {(-5, 0), (-4, 0), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_153 : rowAt 153 = memoRow_153 := by
  have he : entryAt 153 = entry_153 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 153 < 6 by decide, ↓reduceDIte, he, entry_153, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_27, memoRow_eq_59]
  apply rowData_ext <;> decide +kernel


def memoRow_154 : RowData := ⟨{(1, 0), (2, 0), (3, 0), (4, 0)}, {(-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (4, 0), (4, 1), (5, 0), (6, 0)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_154 : rowAt 154 = memoRow_154 := by
  have he : entryAt 154 = entry_154 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 154 < 6 by decide, ↓reduceDIte, he, entry_154, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_7, memoRow_eq_104]
  apply rowData_ext <;> decide +kernel


def memoRow_155 : RowData := ⟨{(0, -4), (0, -3), (0, -2), (0, -1)}, {(-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_155 : rowAt 155 = memoRow_155 := by
  have he : entryAt 155 = entry_155 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 155 < 6 by decide, ↓reduceDIte, he, entry_155, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_7, memoRow_eq_55]
  apply rowData_ext <;> decide +kernel


def memoRow_156 : RowData := ⟨{(-3, -1), (-3, 0), (-3, 1), (-1, -1), (-1, 0)}, {(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_156 : rowAt 156 = memoRow_156 := by
  have he : entryAt 156 = entry_156 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 156 < 6 by decide, ↓reduceDIte, he, entry_156, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_11, memoRow_eq_33, memoRow_eq_98]
  apply rowData_ext <;> decide +kernel


def memoRow_157 : RowData := ⟨{(0, -1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1)}, {(0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (2, 3)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_157 : rowAt 157 = memoRow_157 := by
  have he : entryAt 157 = entry_157 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 157 < 6 by decide, ↓reduceDIte, he, entry_157, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_57]
  apply rowData_ext <;> decide +kernel


def memoRow_158 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, -2), (2, -1), (3, -1)}, {(-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (3, -1)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_158 : rowAt 158 = memoRow_158 := by
  have he : entryAt 158 = entry_158 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 158 < 6 by decide, ↓reduceDIte, he, entry_158, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_45, memoRow_eq_46, memoRow_eq_66]
  apply rowData_ext <;> decide +kernel


def memoRow_159 : RowData := ⟨{(-1, -2), (0, -4), (0, -3), (0, -2), (0, -1)}, {(-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (1, 3)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_159 : rowAt 159 = memoRow_159 := by
  have he : entryAt 159 = entry_159 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 159 < 6 by decide, ↓reduceDIte, he, entry_159, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_7, memoRow_eq_45, memoRow_eq_65]
  apply rowData_ext <;> decide +kernel


def memoRow_160 : RowData := ⟨{(1, 0), (1, 1), (1, 2), (2, 0), (3, 0)}, {(-1, -1), (0, -1), (0, 0), (1, 0), (1, 1), (1, 2), (1, 3), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 1)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_160 : rowAt 160 = memoRow_160 := by
  have he : entryAt 160 = entry_160 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 160 < 6 by decide, ↓reduceDIte, he, entry_160, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_32, memoRow_eq_63]
  apply rowData_ext <;> decide +kernel


def memoRow_161 : RowData := ⟨{(-2, -1), (-2, 0), (-1, -2), (-1, -1), (-1, 0), (0, 2)}, {(-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (2, 0)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_161 : rowAt 161 = memoRow_161 := by
  have he : entryAt 161 = entry_161 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 161 < 6 by decide, ↓reduceDIte, he, entry_161, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_15, memoRow_eq_86]
  apply rowData_ext <;> decide +kernel


def memoRow_162 : RowData := ⟨{(-1, -2), (0, -4), (0, -3), (0, -2), (0, -1)}, {(-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_162 : rowAt 162 = memoRow_162 := by
  have he : entryAt 162 = entry_162 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 162 < 6 by decide, ↓reduceDIte, he, entry_162, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_7, memoRow_eq_63, memoRow_eq_127, memoRow_eq_157]
  apply rowData_ext <;> decide +kernel


def memoRow_163 : RowData := ⟨{(-3, -1), (-3, 0), (-2, 0), (-1, 0)}, {(-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_163 : rowAt 163 = memoRow_163 := by
  have he : entryAt 163 = entry_163 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 163 < 6 by decide, ↓reduceDIte, he, entry_163, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_44, memoRow_eq_49, memoRow_eq_56]
  apply rowData_ext <;> decide +kernel


def memoRow_164 : RowData := ⟨{(-1, -3), (-1, -2), (-1, -1), (-1, 0), (2, 0)}, {(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, 0), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_164 : rowAt 164 = memoRow_164 := by
  have he : entryAt 164 = entry_164 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 164 < 6 by decide, ↓reduceDIte, he, entry_164, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_110]
  apply rowData_ext <;> decide +kernel


def memoRow_165 : RowData := ⟨{(0, 1), (1, 1), (1, 2), (1, 3), (2, 1)}, {(-1, 0), (0, 0), (0, 1), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0), (5, 2)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_165 : rowAt 165 = memoRow_165 := by
  have he : entryAt 165 = entry_165 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 165 < 6 by decide, ↓reduceDIte, he, entry_165, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_107]
  apply rowData_ext <;> decide +kernel


def memoRow_166 : RowData := ⟨{(-1, -1), (-1, 0), (0, 2), (0, 3), (1, 0)}, {(-2, -1), (-1, -1), (-1, 0), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_166 : rowAt 166 = memoRow_166 := by
  have he : entryAt 166 = entry_166 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 166 < 6 by decide, ↓reduceDIte, he, entry_166, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_2, memoRow_eq_107]
  apply rowData_ext <;> decide +kernel


def memoRow_167 : RowData := ⟨{(-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0)}, {(-5, 0), (-5, 1), (-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_167 : rowAt 167 = memoRow_167 := by
  have he : entryAt 167 = entry_167 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 167 < 6 by decide, ↓reduceDIte, he, entry_167, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_57]
  apply rowData_ext <;> decide +kernel


def memoRow_168 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, 0), (3, -1)}, {(-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_168 : rowAt 168 = memoRow_168 := by
  have he : entryAt 168 = entry_168 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 168 < 6 by decide, ↓reduceDIte, he, entry_168, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_152]
  apply rowData_ext <;> decide +kernel


def memoRow_169 : RowData := ⟨{(0, 2), (1, -1), (1, 0), (2, 0), (3, 0)}, {(-1, 1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 1)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_169 : rowAt 169 = memoRow_169 := by
  have he : entryAt 169 = entry_169 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 169 < 6 by decide, ↓reduceDIte, he, entry_169, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_28, memoRow_eq_63]
  apply rowData_ext <;> decide +kernel


def memoRow_170 : RowData := ⟨{(-4, -1), (-3, 0), (-2, 0), (-2, 1), (-1, 0)}, {(-4, -1), (-3, -1), (-3, 0), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, 1)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_170 : rowAt 170 = memoRow_170 := by
  have he : entryAt 170 = entry_170 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 170 < 6 by decide, ↓reduceDIte, he, entry_170, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_4, memoRow_eq_127]
  apply rowData_ext <;> decide +kernel


def memoRow_171 : RowData := ⟨{(-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-1, -1), (0, -1)}, {(-4, 1), (-4, 2), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (1, 0)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_171 : rowAt 171 = memoRow_171 := by
  have he : entryAt 171 = entry_171 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 171 < 6 by decide, ↓reduceDIte, he, entry_171, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_91]
  apply rowData_ext <;> decide +kernel


def memoRow_172 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-5, -1), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_172 : rowAt 172 = memoRow_172 := by
  have he : entryAt 172 = entry_172 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 172 < 6 by decide, ↓reduceDIte, he, entry_172, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_55, memoRow_eq_63, memoRow_eq_64]
  apply rowData_ext <;> decide +kernel


def memoRow_173 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-5, -1), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-2, 0), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_173 : rowAt 173 = memoRow_173 := by
  have he : entryAt 173 = entry_173 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 173 < 6 by decide, ↓reduceDIte, he, entry_173, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_55, memoRow_eq_63, memoRow_eq_64]
  apply rowData_ext <;> decide +kernel


def memoRow_174 : RowData := ⟨{(-1, -2), (-1, -1), (0, -3), (0, -2), (0, -1)}, {(-2, -1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (3, 0)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_174 : rowAt 174 = memoRow_174 := by
  have he : entryAt 174 = entry_174 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 174 < 6 by decide, ↓reduceDIte, he, entry_174, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_57, memoRow_eq_58, memoRow_eq_84]
  apply rowData_ext <;> decide +kernel


def memoRow_175 : RowData := ⟨{(-4, 0), (-3, 0), (-2, 0), (-1, 0)}, {(-5, 0), (-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_175 : rowAt 175 = memoRow_175 := by
  have he : entryAt 175 = entry_175 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 175 < 6 by decide, ↓reduceDIte, he, entry_175, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_7, memoRow_eq_63, memoRow_eq_141]
  apply rowData_ext <;> decide +kernel


def memoRow_176 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-5, -1), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_176 : rowAt 176 = memoRow_176 := by
  have he : entryAt 176 = entry_176 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 176 < 6 by decide, ↓reduceDIte, he, entry_176, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_55, memoRow_eq_63, memoRow_eq_64]
  apply rowData_ext <;> decide +kernel


def memoRow_177 : RowData := ⟨{(-1, -3), (-1, -2), (-1, -1), (-1, 0), (2, -2), (2, 0)}, {(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -3), (2, -2), (2, -1), (2, 0), (3, -1)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_177 : rowAt 177 = memoRow_177 := by
  have he : entryAt 177 = entry_177 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 177 < 6 by decide, ↓reduceDIte, he, entry_177, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_136]
  apply rowData_ext <;> decide +kernel


def memoRow_178 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, -2), (2, -1), (3, -1)}, {(-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, -1), (1, 1), (1, 2), (1, 3), (2, -1), (3, -1)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_178 : rowAt 178 = memoRow_178 := by
  have he : entryAt 178 = entry_178 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 178 < 6 by decide, ↓reduceDIte, he, entry_178, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_37, memoRow_eq_46, memoRow_eq_68]
  apply rowData_ext <;> decide +kernel


def memoRow_179 : RowData := ⟨{(-3, -1), (-3, 0), (-2, 0), (-1, -1), (-1, 0), (-1, 1)}, {(-4, -1), (-3, -1), (-3, 0), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (4, -1)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_179 : rowAt 179 = memoRow_179 := by
  have he : entryAt 179 = entry_179 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 179 < 6 by decide, ↓reduceDIte, he, entry_179, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_148]
  apply rowData_ext <;> decide +kernel


def memoRow_180 : RowData := ⟨{(0, -4), (0, -3), (0, -2), (0, -1)}, {(-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_180 : rowAt 180 = memoRow_180 := by
  have he : entryAt 180 = entry_180 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 180 < 6 by decide, ↓reduceDIte, he, entry_180, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_7, memoRow_eq_63, memoRow_eq_132, memoRow_eq_155]
  apply rowData_ext <;> decide +kernel


def memoRow_181 : RowData := ⟨{(1, -2), (1, -1), (1, 0), (2, 1)}, {(-2, 0), (-1, 0), (0, 0), (0, 1), (0, 2), (0, 3), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (4, 1), (5, 1)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_181 : rowAt 181 = memoRow_181 := by
  have he : entryAt 181 = entry_181 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 181 < 6 by decide, ↓reduceDIte, he, entry_181, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_24, memoRow_eq_87, memoRow_eq_90]
  apply rowData_ext <;> decide +kernel


def memoRow_182 : RowData := ⟨{(1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (3, 2)}, {(-1, 0), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -1), (4, 0), (4, 1), (5, 0)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_182 : rowAt 182 = memoRow_182 := by
  have he : entryAt 182 = entry_182 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 182 < 6 by decide, ↓reduceDIte, he, entry_182, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_12, memoRow_eq_139]
  apply rowData_ext <;> decide +kernel


def memoRow_183 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_183 : rowAt 183 = memoRow_183 := by
  have he : entryAt 183 = entry_183 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 183 < 6 by decide, ↓reduceDIte, he, entry_183, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_55, memoRow_eq_63, memoRow_eq_64]
  apply rowData_ext <;> decide +kernel


def memoRow_184 : RowData := ⟨{(0, -3), (1, -4), (1, -3), (2, -3), (2, -1), (2, 0), (3, -3), (3, -1)}, {(-1, -2), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (1, -4), (1, -3), (1, -1), (1, 0), (2, -3), (2, -1), (2, 0), (3, -3), (3, -1), (4, -1), (5, -1)}, 4⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_184 : rowAt 184 = memoRow_184 := by
  have he : entryAt 184 = entry_184 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 184 < 6 by decide, ↓reduceDIte, he, entry_184, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_34, memoRow_eq_35]
  apply rowData_ext <;> decide +kernel


def memoRow_185 : RowData := ⟨{(-1, -3), (-1, -1), (0, -3), (0, -2), (0, -1)}, {(-2, -1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, 0), (3, 0)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_185 : rowAt 185 = memoRow_185 := by
  have he : entryAt 185 = entry_185 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 185 < 6 by decide, ↓reduceDIte, he, entry_185, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_44, memoRow_eq_49, memoRow_eq_84]
  apply rowData_ext <;> decide +kernel


def memoRow_186 : RowData := ⟨{(-4, 0), (-3, 0), (-2, 0), (-1, 0)}, {(-5, -1), (-5, 0), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_186 : rowAt 186 = memoRow_186 := by
  have he : entryAt 186 = entry_186 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 186 < 6 by decide, ↓reduceDIte, he, entry_186, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_7, memoRow_eq_141]
  apply rowData_ext <;> decide +kernel


def memoRow_187 : RowData := ⟨{(0, -2), (0, -1), (1, -3), (1, -1), (2, -1), (3, -1)}, {(-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, -1), (1, 1), (1, 2), (1, 3), (2, -1), (3, -1)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_187 : rowAt 187 = memoRow_187 := by
  have he : entryAt 187 = entry_187 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 187 < 6 by decide, ↓reduceDIte, he, entry_187, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_108]
  apply rowData_ext <;> decide +kernel


def memoRow_188 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (3, -2), (4, -2), (4, -1)}, {(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (4, -2), (4, -1), (4, 0), (4, 1), (5, 1)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_188 : rowAt 188 = memoRow_188 := by
  have he : entryAt 188 = entry_188 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 188 < 6 by decide, ↓reduceDIte, he, entry_188, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_112]
  apply rowData_ext <;> decide +kernel


def memoRow_189 : RowData := ⟨{(-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1)}, {(-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (2, 0)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_189 : rowAt 189 = memoRow_189 := by
  have he : entryAt 189 = entry_189 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 189 < 6 by decide, ↓reduceDIte, he, entry_189, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_12, memoRow_eq_86]
  apply rowData_ext <;> decide +kernel


def memoRow_190 : RowData := ⟨{(-3, 0), (-2, -1), (-2, 0), (-1, 0)}, {(-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (2, 0), (2, 1)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_190 : rowAt 190 = memoRow_190 := by
  have he : entryAt 190 = entry_190 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 190 < 6 by decide, ↓reduceDIte, he, entry_190, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_46, memoRow_eq_85, memoRow_eq_111]
  apply rowData_ext <;> decide +kernel


def memoRow_191 : RowData := ⟨{(0, -2), (0, -1), (1, -2), (1, -1), (2, -1), (3, -1), (3, 0)}, {(-1, 0), (-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_191 : rowAt 191 = memoRow_191 := by
  have he : entryAt 191 = entry_191 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 191 < 6 by decide, ↓reduceDIte, he, entry_191, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_145]
  apply rowData_ext <;> decide +kernel


def memoRow_192 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (2, -1)}, {(-2, 0), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (3, -1)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_192 : rowAt 192 = memoRow_192 := by
  have he : entryAt 192 = entry_192 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 192 < 6 by decide, ↓reduceDIte, he, entry_192, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_55, memoRow_eq_64, memoRow_eq_103]
  apply rowData_ext <;> decide +kernel


def memoRow_193 : RowData := ⟨{(-1, -1), (-1, 0), (1, -1), (1, 0), (2, 0)}, {(-2, -1), (-1, -1), (-1, 0), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_193 : rowAt 193 = memoRow_193 := by
  have he : entryAt 193 = entry_193 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 193 < 6 by decide, ↓reduceDIte, he, entry_193, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_162]
  apply rowData_ext <;> decide +kernel


def memoRow_194 : RowData := ⟨{(-3, -1), (-2, -1), (-1, -1), (-1, 0), (-1, 1)}, {(-4, -1), (-4, 1), (-3, -1), (-3, 1), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, 0), (0, 1), (1, 0), (2, 0)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_194 : rowAt 194 = memoRow_194 := by
  have he : entryAt 194 = entry_194 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 194 < 6 by decide, ↓reduceDIte, he, entry_194, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_146]
  apply rowData_ext <;> decide +kernel


def memoRow_195 : RowData := ⟨{(-3, -1), (-3, 0), (-2, 0), (-1, -1), (-1, 0)}, {(-4, -1), (-3, -1), (-3, 0), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_195 : rowAt 195 = memoRow_195 := by
  have he : entryAt 195 = entry_195 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 195 < 6 by decide, ↓reduceDIte, he, entry_195, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_162]
  apply rowData_ext <;> decide +kernel


def memoRow_196 : RowData := ⟨{(-1, -1), (1, -3), (1, -2), (1, -1), (1, 0)}, {(-1, -1), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 1)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_196 : rowAt 196 = memoRow_196 := by
  have he : entryAt 196 = entry_196 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 196 < 6 by decide, ↓reduceDIte, he, entry_196, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_187]
  apply rowData_ext <;> decide +kernel


def memoRow_197 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_197 : rowAt 197 = memoRow_197 := by
  have he : entryAt 197 = entry_197 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 197 < 6 by decide, ↓reduceDIte, he, entry_197, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_63]
  apply rowData_ext <;> decide +kernel


def memoRow_198 : RowData := ⟨{(-4, 0), (-3, 0), (-2, 0), (-1, -1), (-1, 0)}, {(-5, 1), (-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_198 : rowAt 198 = memoRow_198 := by
  have he : entryAt 198 = entry_198 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 198 < 6 by decide, ↓reduceDIte, he, entry_198, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_7, memoRow_eq_131]
  apply rowData_ext <;> decide +kernel


def memoRow_199 : RowData := ⟨{(-1, -1), (0, -3), (0, -2), (0, -1)}, {(-2, -1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, 0), (3, 0)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_199 : rowAt 199 = memoRow_199 := by
  have he : entryAt 199 = entry_199 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 199 < 6 by decide, ↓reduceDIte, he, entry_199, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_55, memoRow_eq_64, memoRow_eq_84]
  apply rowData_ext <;> decide +kernel


def memoRow_200 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (2, -1)}, {(-2, 0), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (3, -1)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_200 : rowAt 200 = memoRow_200 := by
  have he : entryAt 200 = entry_200 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 200 < 6 by decide, ↓reduceDIte, he, entry_200, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_55, memoRow_eq_64, memoRow_eq_103]
  apply rowData_ext <;> decide +kernel


def memoRow_201 : RowData := ⟨{(1, -2), (1, -1), (1, 0), (1, 1), (1, 2)}, {(-2, 0), (-1, 0), (0, -1), (0, 0), (0, 2), (0, 3), (0, 4), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (3, 1), (4, 1)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_201 : rowAt 201 = memoRow_201 := by
  have he : entryAt 201 = entry_201 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 201 < 6 by decide, ↓reduceDIte, he, entry_201, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_45, memoRow_eq_82]
  apply rowData_ext <;> decide +kernel


def memoRow_202 : RowData := ⟨{(-4, 0), (-3, -1), (-3, 0), (-2, 0), (-1, 0)}, {(-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_202 : rowAt 202 = memoRow_202 := by
  have he : entryAt 202 = entry_202 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 202 < 6 by decide, ↓reduceDIte, he, entry_202, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_7, memoRow_eq_108, memoRow_eq_150]
  apply rowData_ext <;> decide +kernel


def memoRow_203 : RowData := ⟨{(-4, -1), (-2, -1), (-2, 0), (-1, 0)}, {(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_203 : rowAt 203 = memoRow_203 := by
  have he : entryAt 203 = entry_203 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 203 < 6 by decide, ↓reduceDIte, he, entry_203, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_18, memoRow_eq_107, memoRow_eq_163]
  apply rowData_ext <;> decide +kernel


def memoRow_204 : RowData := ⟨{(0, -3), (0, -1), (1, -4), (1, -3), (2, -1)}, {(-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (1, -4), (1, -3), (1, -2), (1, -1), (2, -1), (3, -2), (3, -1), (3, 0), (4, -2), (4, -1), (4, 0), (5, -2), (5, 0)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_204 : rowAt 204 = memoRow_204 := by
  have he : entryAt 204 = entry_204 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 204 < 6 by decide, ↓reduceDIte, he, entry_204, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_2, memoRow_eq_166]
  apply rowData_ext <;> decide +kernel


def memoRow_205 : RowData := ⟨{(-1, -4), (-1, -3), (-1, -2), (-1, -1), (2, -1)}, {(-2, 0), (-2, 1), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_205 : rowAt 205 = memoRow_205 := by
  have he : entryAt 205 = entry_205 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 205 < 6 by decide, ↓reduceDIte, he, entry_205, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_4, memoRow_eq_168]
  apply rowData_ext <;> decide +kernel


def memoRow_206 : RowData := ⟨{(0, 2), (1, -1), (1, 0), (2, 0), (3, 0)}, {(-2, 0), (-1, 0), (-1, 1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (4, -1), (4, 0), (5, -1), (5, 0), (6, -1)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_206 : rowAt 206 = memoRow_206 := by
  have he : entryAt 206 = entry_206 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 206 < 6 by decide, ↓reduceDIte, he, entry_206, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_28, memoRow_eq_135]
  apply rowData_ext <;> decide +kernel


def memoRow_207 : RowData := ⟨{(0, 2), (1, -1), (1, 0), (2, 0), (3, 0)}, {(-1, 1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (2, -1), (2, 0), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_207 : rowAt 207 = memoRow_207 := by
  have he : entryAt 207 = entry_207 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 207 < 6 by decide, ↓reduceDIte, he, entry_207, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_28, memoRow_eq_127]
  apply rowData_ext <;> decide +kernel


def memoRow_208 : RowData := ⟨{(-4, 0), (-3, 0), (-2, -1), (-2, 0), (-1, 0)}, {(-5, 1), (-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_208 : rowAt 208 = memoRow_208 := by
  have he : entryAt 208 = entry_208 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 208 < 6 by decide, ↓reduceDIte, he, entry_208, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_7, memoRow_eq_127]
  apply rowData_ext <;> decide +kernel


def memoRow_209 : RowData := ⟨{(-3, 2), (-2, -1), (-2, 2), (-1, -1), (-1, 2), (0, -1), (0, 2)}, {(-3, -1), (-3, 2), (-2, -1), (-2, 2), (-1, -1), (-1, 0), (-1, 2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 2), (1, 3), (2, 0), (2, 3), (3, 0)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_209 : rowAt 209 = memoRow_209 := by
  have he : entryAt 209 = entry_209 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 209 < 6 by decide, ↓reduceDIte, he, entry_209, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_25, memoRow_eq_81]
  apply rowData_ext <;> decide +kernel


def memoRow_210 : RowData := ⟨{(-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (-1, 2)}, {(-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_210 : rowAt 210 = memoRow_210 := by
  have he : entryAt 210 = entry_210 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 210 < 6 by decide, ↓reduceDIte, he, entry_210, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_57, memoRow_eq_58, memoRow_eq_117]
  apply rowData_ext <;> decide +kernel


def memoRow_211 : RowData := ⟨{(-3, -1), (-3, 0), (-3, 1), (-2, 0), (-1, 0)}, {(-4, -1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_211 : rowAt 211 = memoRow_211 := by
  have he : entryAt 211 = entry_211 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 211 < 6 by decide, ↓reduceDIte, he, entry_211, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_49]
  apply rowData_ext <;> decide +kernel


def memoRow_212 : RowData := ⟨{(-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 1), (-1, -1), (0, -1)}, {(-4, 1), (-4, 2), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 2)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_212 : rowAt 212 = memoRow_212 := by
  have he : entryAt 212 = entry_212 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 212 < 6 by decide, ↓reduceDIte, he, entry_212, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_188]
  apply rowData_ext <;> decide +kernel


def memoRow_213 : RowData := ⟨{(-1, -1), (-1, 0), (0, -1), (1, 0), (2, 0), (2, 1)}, {(-2, 1), (-2, 2), (-2, 3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (3, 1)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_213 : rowAt 213 = memoRow_213 := by
  have he : entryAt 213 = entry_213 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 213 < 6 by decide, ↓reduceDIte, he, entry_213, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_191]
  apply rowData_ext <;> decide +kernel


def memoRow_214 : RowData := ⟨{(0, -4), (0, -3), (0, -2), (0, -1), (1, -3), (3, -2)}, {(-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, 1), (1, 2), (1, 3), (2, -2), (3, -2)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_214 : rowAt 214 = memoRow_214 := by
  have he : entryAt 214 = entry_214 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 214 < 6 by decide, ↓reduceDIte, he, entry_214, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_7, memoRow_eq_95, memoRow_eq_108]
  apply rowData_ext <;> decide +kernel


def memoRow_215 : RowData := ⟨{(-2, -1), (-1, -1), (0, -1), (0, 1)}, {(-3, -1), (-2, -1), (-1, -2), (-1, -1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, 0), (3, 0)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_215 : rowAt 215 = memoRow_215 := by
  have he : entryAt 215 = entry_215 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 215 < 6 by decide, ↓reduceDIte, he, entry_215, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_24, memoRow_eq_107]
  apply rowData_ext <;> decide +kernel


def memoRow_216 : RowData := ⟨{(-4, 0), (-3, 0), (-2, 0), (-1, 0)}, {(-5, -1), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, 1)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_216 : rowAt 216 = memoRow_216 := by
  have he : entryAt 216 = entry_216 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 216 < 6 by decide, ↓reduceDIte, he, entry_216, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_7, memoRow_eq_155]
  apply rowData_ext <;> decide +kernel


def memoRow_217 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_217 : rowAt 217 = memoRow_217 := by
  have he : entryAt 217 = entry_217 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 217 < 6 by decide, ↓reduceDIte, he, entry_217, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_55, memoRow_eq_64, memoRow_eq_111]
  apply rowData_ext <;> decide +kernel


def memoRow_218 : RowData := ⟨{(-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -1), (1, 2)}, {(-3, 0), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (3, 0)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_218 : rowAt 218 = memoRow_218 := by
  have he : entryAt 218 = entry_218 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 218 < 6 by decide, ↓reduceDIte, he, entry_218, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_182]
  apply rowData_ext <;> decide +kernel


def memoRow_219 : RowData := ⟨{(-1, 0), (-1, 1), (-1, 2), (0, -1), (1, -1), (1, 0), (1, 1)}, {(-2, 1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (4, 0), (4, 1), (5, 0), (5, 1), (6, 1)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_219 : rowAt 219 = memoRow_219 := by
  have he : entryAt 219 = entry_219 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 219 < 6 by decide, ↓reduceDIte, he, entry_219, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_179]
  apply rowData_ext <;> decide +kernel


def memoRow_220 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-5, 0), (-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_220 : rowAt 220 = memoRow_220 := by
  have he : entryAt 220 = entry_220 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 220 < 6 by decide, ↓reduceDIte, he, entry_220, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_56, memoRow_eq_63, memoRow_eq_144, memoRow_eq_154, memoRow_eq_155]
  apply rowData_ext <;> decide +kernel


def memoRow_221 : RowData := ⟨{(-3, -1), (-3, 0), (-2, 0), (-1, 0)}, {(-4, -1), (-3, -1), (-3, 0), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, 1)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_221 : rowAt 221 = memoRow_221 := by
  have he : entryAt 221 = entry_221 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 221 < 6 by decide, ↓reduceDIte, he, entry_221, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_180]
  apply rowData_ext <;> decide +kernel


def memoRow_222 : RowData := ⟨{(-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2)}, {(-2, -1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, 0), (0, 1), (1, -2), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_222 : rowAt 222 = memoRow_222 := by
  have he : entryAt 222 = entry_222 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 222 < 6 by decide, ↓reduceDIte, he, entry_222, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_158]
  apply rowData_ext <;> decide +kernel


def memoRow_223 : RowData := ⟨{(-3, 0), (-2, -1), (-2, 0), (-1, 0)}, {(-5, 0), (-4, 0), (-3, 0), (-2, -1), (-2, 0), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_223 : rowAt 223 = memoRow_223 := by
  have he : entryAt 223 = entry_223 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 223 < 6 by decide, ↓reduceDIte, he, entry_223, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_63, memoRow_eq_111, memoRow_eq_127, memoRow_eq_128, memoRow_eq_135]
  apply rowData_ext <;> decide +kernel


def memoRow_224 : RowData := ⟨{(-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (1, -2), (2, -2)}, {(-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, -2), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_224 : rowAt 224 = memoRow_224 := by
  have he : entryAt 224 = entry_224 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 224 < 6 by decide, ↓reduceDIte, he, entry_224, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_212]
  apply rowData_ext <;> decide +kernel


def memoRow_225 : RowData := ⟨{(1, -2), (1, -1), (1, 0), (2, 0), (3, 0)}, {(-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (2, 0), (2, 1), (2, 2), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_225 : rowAt 225 = memoRow_225 := by
  have he : entryAt 225 = entry_225 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 225 < 6 by decide, ↓reduceDIte, he, entry_225, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_61, memoRow_eq_111]
  apply rowData_ext <;> decide +kernel


def memoRow_226 : RowData := ⟨{(-3, -1), (-3, 0), (-1, -1), (-1, 0)}, {(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_226 : rowAt 226 = memoRow_226 := by
  have he : entryAt 226 = entry_226 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 226 < 6 by decide, ↓reduceDIte, he, entry_226, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_10, memoRow_eq_33, memoRow_eq_193, memoRow_eq_203]
  apply rowData_ext <;> decide +kernel


def memoRow_227 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, -2), (1, 0), (2, -2), (3, -2)}, {(-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -2), (1, 0), (1, 1), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -2), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_227 : rowAt 227 = memoRow_227 := by
  have he : entryAt 227 = entry_227 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 227 < 6 by decide, ↓reduceDIte, he, entry_227, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_212]
  apply rowData_ext <;> decide +kernel


def memoRow_228 : RowData := ⟨{(1, -2), (1, -1), (1, 0), (1, 1), (1, 2)}, {(-2, 0), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 3), (0, 4), (0, 5), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (3, 1), (4, 1)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_228 : rowAt 228 = memoRow_228 := by
  have he : entryAt 228 = entry_228 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 228 < 6 by decide, ↓reduceDIte, he, entry_228, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_68, memoRow_eq_82]
  apply rowData_ext <;> decide +kernel


def memoRow_229 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, -2), (2, -2), (3, -2)}, {(-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -2), (2, -1), (2, 0), (3, -2), (3, -1), (4, -1)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_229 : rowAt 229 = memoRow_229 := by
  have he : entryAt 229 = entry_229 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 229 < 6 by decide, ↓reduceDIte, he, entry_229, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_45, memoRow_eq_46, memoRow_eq_171]
  apply rowData_ext <;> decide +kernel


def memoRow_230 : RowData := ⟨{(0, 1), (2, 0), (2, 1), (3, 1)}, {(-1, 0), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 0), (6, 1), (6, 2), (7, 0), (7, 2)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_230 : rowAt 230 = memoRow_230 := by
  have he : entryAt 230 = entry_230 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 230 < 6 by decide, ↓reduceDIte, he, entry_230, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_10, memoRow_eq_33, memoRow_eq_193, memoRow_eq_203]
  apply rowData_ext <;> decide +kernel


def memoRow_231 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0), (2, -3), (2, -2)}, {(0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -3), (2, -2), (2, 0), (2, 1), (3, -2), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 1)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_231 : rowAt 231 = memoRow_231 := by
  have he : entryAt 231 = entry_231 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 231 < 6 by decide, ↓reduceDIte, he, entry_231, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_222]
  apply rowData_ext <;> decide +kernel


def memoRow_232 : RowData := ⟨{(-2, 1), (-1, -1), (-1, 1), (0, -1), (0, 1)}, {(-3, 1), (-2, 1), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (3, 0)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_232 : rowAt 232 = memoRow_232 := by
  have he : entryAt 232 = entry_232 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 232 < 6 by decide, ↓reduceDIte, he, entry_232, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_24, memoRow_eq_107]
  apply rowData_ext <;> decide +kernel


def memoRow_233 : RowData := ⟨{(-1, -2), (0, -2), (0, -1), (1, -2), (2, -2), (2, -1), (2, 1)}, {(-2, -3), (-1, -3), (-1, -2), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, 0), (2, -2), (2, -1), (2, 0), (2, 1), (3, 0), (3, 1), (3, 2), (4, 1), (5, 1)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_233 : rowAt 233 = memoRow_233 := by
  have he : entryAt 233 = entry_233 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 233 < 6 by decide, ↓reduceDIte, he, entry_233, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_32, memoRow_eq_133]
  apply rowData_ext <;> decide +kernel


def memoRow_234 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, -2), (2, -1), (3, -1)}, {(-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (3, -1)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_234 : rowAt 234 = memoRow_234 := by
  have he : entryAt 234 = entry_234 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 234 < 6 by decide, ↓reduceDIte, he, entry_234, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_37, memoRow_eq_63, memoRow_eq_129, memoRow_eq_180]
  apply rowData_ext <;> decide +kernel


def memoRow_235 : RowData := ⟨{(0, -4), (0, -3), (0, -2), (0, -1), (1, 0), (3, 0)}, {(-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 1)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_235 : rowAt 235 = memoRow_235 := by
  have he : entryAt 235 = entry_235 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 235 < 6 by decide, ↓reduceDIte, he, entry_235, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_7, memoRow_eq_70, memoRow_eq_110]
  apply rowData_ext <;> decide +kernel


def memoRow_236 : RowData := ⟨{(-1, -3), (-1, -2), (-1, -1)}, {(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (2, 0), (3, 0)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_236 : rowAt 236 = memoRow_236 := by
  have he : entryAt 236 = entry_236 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 236 < 6 by decide, ↓reduceDIte, he, entry_236, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_30, memoRow_eq_38, memoRow_eq_122, memoRow_eq_181]
  apply rowData_ext <;> decide +kernel


def memoRow_237 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0), (2, 0)}, {(-2, -1), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 1)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_237 : rowAt 237 = memoRow_237 := by
  have he : entryAt 237 = entry_237 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 237 < 6 by decide, ↓reduceDIte, he, entry_237, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_172]
  apply rowData_ext <;> decide +kernel


def memoRow_238 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0), (2, -3), (2, -2), (2, 0)}, {(0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -3), (2, -2), (2, -1), (2, 0), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_238 : rowAt 238 = memoRow_238 := by
  have he : entryAt 238 = entry_238 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 238 < 6 by decide, ↓reduceDIte, he, entry_238, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_178]
  apply rowData_ext <;> decide +kernel


def memoRow_239 : RowData := ⟨{(-1, -2), (-1, -1), (-1, 0), (0, -1), (1, -1), (2, -1)}, {(-4, 1), (-3, 1), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (2, -1), (3, -1)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_239 : rowAt 239 = memoRow_239 := by
  have he : entryAt 239 = entry_239 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 239 < 6 by decide, ↓reduceDIte, he, entry_239, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_174]
  apply rowData_ext <;> decide +kernel


def memoRow_240 : RowData := ⟨{(-1, -3), (-1, -2), (-1, -1), (-1, 0)}, {(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_240 : rowAt 240 = memoRow_240 := by
  have he : entryAt 240 = entry_240 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 240 < 6 by decide, ↓reduceDIte, he, entry_240, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_237]
  apply rowData_ext <;> decide +kernel


def memoRow_241 : RowData := ⟨{(-3, 0), (-2, 0), (-1, -2), (-1, -1), (-1, 0)}, {(-3, 0), (-2, -1), (-2, 0), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, 1)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_241 : rowAt 241 = memoRow_241 := by
  have he : entryAt 241 = entry_241 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 241 < 6 by decide, ↓reduceDIte, he, entry_241, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_61, memoRow_eq_131, memoRow_eq_159]
  apply rowData_ext <;> decide +kernel


def memoRow_242 : RowData := ⟨{(-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0)}, {(-3, 0), (-2, -1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (3, 0), (3, 1)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_242 : rowAt 242 = memoRow_242 := by
  have he : entryAt 242 = entry_242 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 242 < 6 by decide, ↓reduceDIte, he, entry_242, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_190]
  apply rowData_ext <;> decide +kernel


def memoRow_243 : RowData := ⟨{(-3, -1), (-2, -1), (-2, 0), (-1, -1), (0, -1), (0, 2)}, {(-4, -2), (-3, -2), (-3, -1), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -2), (-1, -1), (-1, 1), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (1, 3), (2, 2), (3, 2)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_243 : rowAt 243 = memoRow_243 := by
  have he : entryAt 243 = entry_243 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 243 < 6 by decide, ↓reduceDIte, he, entry_243, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_233]
  apply rowData_ext <;> decide +kernel


def memoRow_244 : RowData := ⟨{(-2, 0), (-1, -3), (-1, -2), (-1, 0)}, {(-5, 1), (-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_244 : rowAt 244 = memoRow_244 := by
  have he : entryAt 244 = entry_244 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 244 < 6 by decide, ↓reduceDIte, he, entry_244, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_11, memoRow_eq_99, memoRow_eq_173]
  apply rowData_ext <;> decide +kernel


def memoRow_245 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-6, -1), (-6, 0), (-6, 1), (-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_245 : rowAt 245 = memoRow_245 := by
  have he : entryAt 245 = entry_245 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 245 < 6 by decide, ↓reduceDIte, he, entry_245, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_64, memoRow_eq_143, memoRow_eq_175, memoRow_eq_186]
  apply rowData_ext <;> decide +kernel


def memoRow_246 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-5, -1), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_246 : rowAt 246 = memoRow_246 := by
  have he : entryAt 246 = entry_246 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 246 < 6 by decide, ↓reduceDIte, he, entry_246, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_64, memoRow_eq_143, memoRow_eq_175, memoRow_eq_186]
  apply rowData_ext <;> decide +kernel


def memoRow_247 : RowData := ⟨{(0, -2), (0, -1), (1, -1), (2, -1), (3, -1)}, {(-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (4, 0)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_247 : rowAt 247 = memoRow_247 := by
  have he : entryAt 247 = entry_247 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 247 < 6 by decide, ↓reduceDIte, he, entry_247, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_229]
  apply rowData_ext <;> decide +kernel


def memoRow_248 : RowData := ⟨{(-1, 0), (1, 0), (2, 0)}, {(-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_248 : rowAt 248 = memoRow_248 := by
  have he : entryAt 248 = entry_248 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 248 < 6 by decide, ↓reduceDIte, he, entry_248, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_64, memoRow_eq_143, memoRow_eq_175, memoRow_eq_186]
  apply rowData_ext <;> decide +kernel


def memoRow_249 : RowData := ⟨{(-2, -2), (-1, -3), (-1, -2), (0, -2), (0, -1)}, {(-3, 0), (-2, -2), (-2, 0), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (2, -3), (2, -1), (3, -3)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_249 : rowAt 249 = memoRow_249 := by
  have he : entryAt 249 = entry_249 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 249 < 6 by decide, ↓reduceDIte, he, entry_249, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_225]
  apply rowData_ext <;> decide +kernel


def memoRow_250 : RowData := ⟨{(-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2)}, {(-2, -1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_250 : rowAt 250 = memoRow_250 := by
  have he : entryAt 250 = entry_250 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 250 < 6 by decide, ↓reduceDIte, he, entry_250, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_238]
  apply rowData_ext <;> decide +kernel


def memoRow_251 : RowData := ⟨{(-3, 1), (-2, 1), (-1, 1), (0, 1), (0, 2)}, {(-4, 1), (-3, 1), (-2, 1), (-2, 2), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 3), (1, 4), (1, 5), (2, 3), (3, 3)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_251 : rowAt 251 = memoRow_251 := by
  have he : entryAt 251 = entry_251 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 251 < 6 by decide, ↓reduceDIte, he, entry_251, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_239]
  apply rowData_ext <;> decide +kernel


def memoRow_252 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-5, 0), (-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_252 : rowAt 252 = memoRow_252 := by
  have he : entryAt 252 = entry_252 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 252 < 6 by decide, ↓reduceDIte, he, entry_252, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_63, memoRow_eq_111, memoRow_eq_144, memoRow_eq_154, memoRow_eq_155]
  apply rowData_ext <;> decide +kernel


def memoRow_253 : RowData := ⟨{(-1, -3), (0, -3), (0, -2), (1, -3), (2, -3), (2, 0)}, {(-2, -4), (-1, -4), (-1, -3), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (2, -3), (2, -2), (2, -1), (2, 0), (3, -2), (3, -1), (4, -1), (5, -1)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_253 : rowAt 253 = memoRow_253 := by
  have he : entryAt 253 = entry_253 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 253 < 6 by decide, ↓reduceDIte, he, entry_253, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_29, memoRow_eq_177]
  apply rowData_ext <;> decide +kernel


def memoRow_254 : RowData := ⟨{(0, -2), (1, 1), (2, 1), (3, 1)}, {(-2, 2), (-1, 0), (-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 1), (3, 1), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 0), (6, 2)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_254 : rowAt 254 = memoRow_254 := by
  have he : entryAt 254 = entry_254 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 254 < 6 by decide, ↓reduceDIte, he, entry_254, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_96, memoRow_eq_108]
  apply rowData_ext <;> decide +kernel


def memoRow_255 : RowData := ⟨{(0, -4), (0, -3), (0, -2), (0, -1), (3, 0)}, {(-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 2)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_255 : rowAt 255 = memoRow_255 := by
  have he : entryAt 255 = entry_255 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 255 < 6 by decide, ↓reduceDIte, he, entry_255, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_7, memoRow_eq_69, memoRow_eq_205]
  apply rowData_ext <;> decide +kernel


def memoRow_256 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, -3), (1, -2)}, {(-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, 0), (1, 1), (2, -2), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_256 : rowAt 256 = memoRow_256 := by
  have he : entryAt 256 = entry_256 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 256 < 6 by decide, ↓reduceDIte, he, entry_256, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_231]
  apply rowData_ext <;> decide +kernel


def memoRow_257 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, 1), (3, 1)}, {(-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 1), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0), (5, 2)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_257 : rowAt 257 = memoRow_257 := by
  have he : entryAt 257 = entry_257 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 257 < 6 by decide, ↓reduceDIte, he, entry_257, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_4, memoRow_eq_235]
  apply rowData_ext <;> decide +kernel


def memoRow_258 : RowData := ⟨{(0, -2), (0, -1), (1, -1), (1, 1), (2, -1), (3, -1)}, {(-1, 0), (-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 1), (1, 2), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (3, -1), (3, 0), (3, 1), (3, 2), (4, 0), (4, 2)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_258 : rowAt 258 = memoRow_258 := by
  have he : entryAt 258 = entry_258 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 258 < 6 by decide, ↓reduceDIte, he, entry_258, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_227]
  apply rowData_ext <;> decide +kernel


def memoRow_259 : RowData := ⟨{(0, -1), (1, -1), (1, 0), (2, -1), (3, -1)}, {(-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, -2), (2, -1), (2, 1), (2, 2), (2, 3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (4, -2), (4, 0), (4, 1), (4, 2), (4, 3)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_259 : rowAt 259 = memoRow_259 := by
  have he : entryAt 259 = entry_259 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 259 < 6 by decide, ↓reduceDIte, he, entry_259, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_231]
  apply rowData_ext <;> decide +kernel


def memoRow_260 : RowData := ⟨{(0, -2), (0, -1), (0, 1), (1, -2), (1, -1)}, {(-1, 0), (-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -2), (1, -1), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 2)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_260 : rowAt 260 = memoRow_260 := by
  have he : entryAt 260 = entry_260 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 260 < 6 by decide, ↓reduceDIte, he, entry_260, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_231]
  apply rowData_ext <;> decide +kernel


def memoRow_261 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0)}, {(-1, 0), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -1), (4, 0), (4, 1), (5, 0), (5, 1)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_261 : rowAt 261 = memoRow_261 := by
  have he : entryAt 261 = entry_261 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 261 < 6 by decide, ↓reduceDIte, he, entry_261, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_242]
  apply rowData_ext <;> decide +kernel


def memoRow_262 : RowData := ⟨{(-2, -1), (-2, 0), (-1, -1), (0, -1), (1, 0), (1, 1), (1, 2)}, {(-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (1, 3), (2, 1)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_262 : rowAt 262 = memoRow_262 := by
  have he : entryAt 262 = entry_262 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 262 < 6 by decide, ↓reduceDIte, he, entry_262, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_213]
  apply rowData_ext <;> decide +kernel


def memoRow_263 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-6, -1), (-5, -1), (-5, 0), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_263 : rowAt 263 = memoRow_263 := by
  have he : entryAt 263 = entry_263 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 263 < 6 by decide, ↓reduceDIte, he, entry_263, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_55, memoRow_eq_143, memoRow_eq_144, memoRow_eq_175]
  apply rowData_ext <;> decide +kernel


def memoRow_264 : RowData := ⟨{(0, -1), (1, -1), (1, 0), (2, -1), (3, -1)}, {(-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (2, 2), (2, 3), (2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -2), (4, 0), (4, 1), (4, 2), (4, 3)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_264 : rowAt 264 = memoRow_264 := by
  have he : entryAt 264 = entry_264 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 264 < 6 by decide, ↓reduceDIte, he, entry_264, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_250]
  apply rowData_ext <;> decide +kernel


def memoRow_265 : RowData := ⟨{(0, 1), (1, 1), (2, 1), (3, 1)}, {(-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (4, 2)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_265 : rowAt 265 = memoRow_265 := by
  have he : entryAt 265 = entry_265 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 265 < 6 by decide, ↓reduceDIte, he, entry_265, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_247]
  apply rowData_ext <;> decide +kernel


def memoRow_266 : RowData := ⟨{(-1, 0), (0, -3), (0, -2), (0, -1)}, {(-2, 0), (-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -2), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, 0), (4, 1)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_266 : rowAt 266 = memoRow_266 := by
  have he : entryAt 266 = entry_266 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 266 < 6 by decide, ↓reduceDIte, he, entry_266, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_242]
  apply rowData_ext <;> decide +kernel


def memoRow_267 : RowData := ⟨{(-2, 0), (-1, 0), (1, 0)}, {(-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (4, -1)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_267 : rowAt 267 = memoRow_267 := by
  have he : entryAt 267 = entry_267 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 267 < 6 by decide, ↓reduceDIte, he, entry_267, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_55, memoRow_eq_143, memoRow_eq_144, memoRow_eq_175]
  apply rowData_ext <;> decide +kernel


def memoRow_268 : RowData := ⟨{(-3, -1), (-2, -1), (-1, -1), (0, -1)}, {(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (2, 1), (3, 1)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_268 : rowAt 268 = memoRow_268 := by
  have he : entryAt 268 = entry_268 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 268 < 6 by decide, ↓reduceDIte, he, entry_268, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_251]
  apply rowData_ext <;> decide +kernel


def memoRow_269 : RowData := ⟨{(-1, 1), (-1, 3), (0, 1), (1, 1), (2, 1)}, {(-2, 2), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, 1), (2, 2), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 0), (6, 2)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_269 : rowAt 269 = memoRow_269 := by
  have he : entryAt 269 = entry_269 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 269 < 6 by decide, ↓reduceDIte, he, entry_269, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_28, memoRow_eq_202]
  apply rowData_ext <;> decide +kernel


def memoRow_270 : RowData := ⟨{(-1, -1), (0, -1), (0, 1), (0, 2)}, {(-1, -2), (-1, -1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (1, 4)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_270 : rowAt 270 = memoRow_270 := by
  have he : entryAt 270 = entry_270 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 270 < 6 by decide, ↓reduceDIte, he, entry_270, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_63]
  apply rowData_ext <;> decide +kernel


def memoRow_271 : RowData := ⟨{(0, -1), (0, 1), (1, -1), (2, -1)}, {(-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 2), (1, 3), (1, 4), (2, -1), (3, -2), (3, -1), (3, 0), (4, -2), (4, -1), (4, 0), (5, -2), (5, 0)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_271 : rowAt 271 = memoRow_271 := by
  have he : entryAt 271 = entry_271 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 271 < 6 by decide, ↓reduceDIte, he, entry_271, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_107]
  apply rowData_ext <;> decide +kernel


def memoRow_272 : RowData := ⟨{(-2, -1), (-1, -4), (-1, -2), (-1, -1), (0, -1)}, {(-3, 1), (-2, -1), (-2, 1), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, -2), (2, 0), (3, -2)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_272 : rowAt 272 = memoRow_272 := by
  have he : entryAt 272 = entry_272 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 272 < 6 by decide, ↓reduceDIte, he, entry_272, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_1, memoRow_eq_249]
  apply rowData_ext <;> decide +kernel


def memoRow_273 : RowData := ⟨{(-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0)}, {(-4, 0), (-3, 0), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_273 : rowAt 273 = memoRow_273 := by
  have he : entryAt 273 = entry_273 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 273 < 6 by decide, ↓reduceDIte, he, entry_273, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_223]
  apply rowData_ext <;> decide +kernel


def memoRow_274 : RowData := ⟨{(-1, -2), (0, -2), (0, -1), (0, 1)}, {(-3, 0), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 2)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_274 : rowAt 274 = memoRow_274 := by
  have he : entryAt 274 = entry_274 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 274 < 6 by decide, ↓reduceDIte, he, entry_274, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_240]
  apply rowData_ext <;> decide +kernel


def memoRow_275 : RowData := ⟨{(-3, -1), (-3, 0), (-2, 0), (-1, 0)}, {(-7, -1), (-6, -1), (-6, 0), (-6, 1), (-5, -1), (-5, 0), (-5, 1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_275 : rowAt 275 = memoRow_275 := by
  have he : entryAt 275 = entry_275 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 275 < 6 by decide, ↓reduceDIte, he, entry_275, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_44, memoRow_eq_63, memoRow_eq_198]
  apply rowData_ext <;> decide +kernel


def memoRow_276 : RowData := ⟨{(0, -4), (0, -3), (0, -2), (0, -1), (3, -2), (3, 0)}, {(-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -3), (3, -2), (3, -1), (3, 0), (4, -1)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_276 : rowAt 276 = memoRow_276 := by
  have he : entryAt 276 = entry_276 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 276 < 6 by decide, ↓reduceDIte, he, entry_276, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_7, memoRow_eq_63, memoRow_eq_177]
  apply rowData_ext <;> decide +kernel


def memoRow_277 : RowData := ⟨{(-1, -3), (-1, -1), (0, -1), (1, -3), (1, -2), (1, -1)}, {(-2, -4), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, -1), (2, -4), (2, -3), (2, -2), (3, -4), (3, -3), (3, -2), (4, -4), (4, -2)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_277 : rowAt 277 = memoRow_277 := by
  have he : entryAt 277 = entry_277 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 277 < 6 by decide, ↓reduceDIte, he, entry_277, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_14, memoRow_eq_33, memoRow_eq_204]
  apply rowData_ext <;> decide +kernel


def memoRow_278 : RowData := ⟨{(1, 0), (2, -1), (2, 0), (3, 0)}, {(-2, -1), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1), (7, -1)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_278 : rowAt 278 = memoRow_278 := by
  have he : entryAt 278 = entry_278 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 278 < 6 by decide, ↓reduceDIte, he, entry_278, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_63, memoRow_eq_162]
  apply rowData_ext <;> decide +kernel


def memoRow_279 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0), (2, -3), (2, -2), (2, 0)}, {(0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -3), (2, -2), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1), (7, -1)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_279 : rowAt 279 = memoRow_279 := by
  have he : entryAt 279 = entry_279 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 279 < 6 by decide, ↓reduceDIte, he, entry_279, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_234]
  apply rowData_ext <;> decide +kernel


def memoRow_280 : RowData := ⟨{(-3, -2), (-2, -3), (-2, -2), (-1, -2), (-1, 0), (-1, 1), (0, -2)}, {(-4, -1), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -3), (-2, -2), (-2, 0), (-2, 1), (-1, -2), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_280 : rowAt 280 = memoRow_280 := by
  have he : entryAt 280 = entry_280 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 280 < 6 by decide, ↓reduceDIte, he, entry_280, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_116, memoRow_eq_184]
  apply rowData_ext <;> decide +kernel


def memoRow_281 : RowData := ⟨{(-2, 0), (-2, 1), (-1, 0), (-1, 1)}, {(-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_281 : rowAt 281 = memoRow_281 := by
  have he : entryAt 281 = entry_281 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 281 < 6 by decide, ↓reduceDIte, he, entry_281, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_36, memoRow_eq_163, memoRow_eq_189]
  apply rowData_ext <;> decide +kernel


def memoRow_282 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, 0), (-1, 1), (-1, 2), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_282 : rowAt 282 = memoRow_282 := by
  have he : entryAt 282 = entry_282 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 282 < 6 by decide, ↓reduceDIte, he, entry_282, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_55, memoRow_eq_56, memoRow_eq_64, memoRow_eq_265]
  apply rowData_ext <;> decide +kernel


def memoRow_283 : RowData := ⟨{(-3, 0), (-2, 0), (-1, -2), (-1, 0)}, {(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 1)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_283 : rowAt 283 = memoRow_283 := by
  have he : entryAt 283 = entry_283 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 283 < 6 by decide, ↓reduceDIte, he, entry_283, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_55, memoRow_eq_64, memoRow_eq_196]
  apply rowData_ext <;> decide +kernel


def memoRow_284 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, -2), (2, -2), (3, -2)}, {(-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -2), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_284 : rowAt 284 = memoRow_284 := by
  have he : entryAt 284 = entry_284 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 284 < 6 by decide, ↓reduceDIte, he, entry_284, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_45, memoRow_eq_46, memoRow_eq_224]
  apply rowData_ext <;> decide +kernel


def memoRow_285 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0)}, {(-2, 0), (-1, 0), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_285 : rowAt 285 = memoRow_285 := by
  have he : entryAt 285 = entry_285 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 285 < 6 by decide, ↓reduceDIte, he, entry_285, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_273]
  apply rowData_ext <;> decide +kernel


def memoRow_286 : RowData := ⟨{(-1, -3), (0, -3), (0, -2), (0, -1)}, {(-2, 0), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -2), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, 0), (4, 1)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_286 : rowAt 286 = memoRow_286 := by
  have he : entryAt 286 = entry_286 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 286 < 6 by decide, ↓reduceDIte, he, entry_286, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_261]
  apply rowData_ext <;> decide +kernel


def memoRow_287 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0), (-1, 1)}, {(-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 3), (-2, 4), (-2, 5), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 1)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_287 : rowAt 287 = memoRow_287 := by
  have he : entryAt 287 = entry_287 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 287 < 6 by decide, ↓reduceDIte, he, entry_287, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_55, memoRow_eq_56, memoRow_eq_64, memoRow_eq_264]
  apply rowData_ext <;> decide +kernel


def memoRow_288 : RowData := ⟨{(-3, -3), (-3, -2), (-3, -1), (-2, -3), (-2, 0), (-1, -3), (0, -3)}, {(-4, 0), (-4, 1), (-4, 2), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -3), (-2, 0), (-2, 1), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (1, 0), (1, 1), (1, 2)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_288 : rowAt 288 = memoRow_288 := by
  have he : entryAt 288 = entry_288 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 288 < 6 by decide, ↓reduceDIte, he, entry_288, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_96, memoRow_eq_130]
  apply rowData_ext <;> decide +kernel


def memoRow_289 : RowData := ⟨{(-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2)}, {(-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_289 : rowAt 289 = memoRow_289 := by
  have he : entryAt 289 = entry_289 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 289 < 6 by decide, ↓reduceDIte, he, entry_289, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_279]
  apply rowData_ext <;> decide +kernel


def memoRow_290 : RowData := ⟨{(-2, -1), (-1, -2), (-1, -1), (0, -2), (0, -1), (0, 1)}, {(-4, 0), (-4, 2), (-3, 0), (-3, 1), (-3, 2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, -2), (3, -2)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_290 : rowAt 290 = memoRow_290 := by
  have he : entryAt 290 = entry_290 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 290 < 6 by decide, ↓reduceDIte, he, entry_290, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_67, memoRow_eq_231]
  apply rowData_ext <;> decide +kernel


def memoRow_291 : RowData := ⟨{(1, -1), (1, 0), (2, 0), (3, 0)}, {(-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1), (7, -1), (7, 1)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_291 : rowAt 291 = memoRow_291 := by
  have he : entryAt 291 = entry_291 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 291 < 6 by decide, ↓reduceDIte, he, entry_291, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_55, memoRow_eq_89, memoRow_eq_202]
  apply rowData_ext <;> decide +kernel


def memoRow_292 : RowData := ⟨{(-3, -1), (-2, -1), (-2, 1), (-1, -1), (-1, 1), (0, 1)}, {(-4, -1), (-3, -1), (-2, -2), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (1, 0), (2, 0)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_292 : rowAt 292 = memoRow_292 := by
  have he : entryAt 292 = entry_292 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 292 < 6 by decide, ↓reduceDIte, he, entry_292, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_39, memoRow_eq_79, memoRow_eq_219]
  apply rowData_ext <;> decide +kernel


def memoRow_293 : RowData := ⟨{(-2, -2), (-1, -3), (-1, -2), (0, -2), (0, 1), (1, -2)}, {(-3, -1), (-3, 1), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (3, -1), (3, 0), (4, -1)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_293 : rowAt 293 = memoRow_293 := by
  have he : entryAt 293 = entry_293 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 293 < 6 by decide, ↓reduceDIte, he, entry_293, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_2, memoRow_eq_280]
  apply rowData_ext <;> decide +kernel


def memoRow_294 : RowData := ⟨{(-3, 0), (-2, -2), (-2, 0), (-1, 0)}, {(-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_294 : rowAt 294 = memoRow_294 := by
  have he : entryAt 294 = entry_294 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 294 < 6 by decide, ↓reduceDIte, he, entry_294, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_63, memoRow_eq_196]
  apply rowData_ext <;> decide +kernel


def memoRow_295 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 1)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_295 : rowAt 295 = memoRow_295 := by
  have he : entryAt 295 = entry_295 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 295 < 6 by decide, ↓reduceDIte, he, entry_295, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_55, memoRow_eq_63, memoRow_eq_64, memoRow_eq_265]
  apply rowData_ext <;> decide +kernel


def memoRow_296 : RowData := ⟨{(-3, -3), (-3, -2), (-3, -1), (-3, 0), (-1, -2), (0, -2), (0, -1)}, {(-4, 0), (-4, 1), (-4, 2), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (1, 3)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_296 : rowAt 296 = memoRow_296 := by
  have he : entryAt 296 = entry_296 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 296 < 6 by decide, ↓reduceDIte, he, entry_296, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_65, memoRow_eq_107, memoRow_eq_209]
  apply rowData_ext <;> decide +kernel


def memoRow_297 : RowData := ⟨{(0, -1), (1, -1), (1, 0), (2, -1), (3, -1)}, {(-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -2), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_297 : rowAt 297 = memoRow_297 := by
  have he : entryAt 297 = entry_297 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 297 < 6 by decide, ↓reduceDIte, he, entry_297, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_289]
  apply rowData_ext <;> decide +kernel


def memoRow_298 : RowData := ⟨{(0, -1), (1, 0), (2, -1), (2, 0)}, {(-3, -1), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1), (7, -1)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_298 : rowAt 298 = memoRow_298 := by
  have he : entryAt 298 = entry_298 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 298 < 6 by decide, ↓reduceDIte, he, entry_298, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_24, memoRow_eq_107, memoRow_eq_195]
  apply rowData_ext <;> decide +kernel


def memoRow_299 : RowData := ⟨{(0, -2), (0, -1), (1, -1), (2, -1), (3, -1)}, {(-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -2), (1, -1), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (3, -1), (3, 0), (3, 1), (3, 2), (4, 0), (4, 2)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_299 : rowAt 299 = memoRow_299 := by
  have he : entryAt 299 = entry_299 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 299 < 6 by decide, ↓reduceDIte, he, entry_299, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_284]
  apply rowData_ext <;> decide +kernel


def memoRow_300 : RowData := ⟨{(0, -3), (0, -2), (0, -1)}, {(-3, -2), (-2, -3), (-2, -2), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (2, -4), (2, -3), (2, -2), (3, -4), (3, -3), (3, -2), (4, -4), (4, -2)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_300 : rowAt 300 = memoRow_300 := by
  have he : entryAt 300 = entry_300 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 300 < 6 by decide, ↓reduceDIte, he, entry_300, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_55, memoRow_eq_64, memoRow_eq_240]
  apply rowData_ext <;> decide +kernel


def memoRow_301 : RowData := ⟨{(-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (-1, 2), (0, -1)}, {(-4, 1), (-4, 3), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (1, 3), (2, 0), (2, 1)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_301 : rowAt 301 = memoRow_301 := by
  have he : entryAt 301 = entry_301 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 301 < 6 by decide, ↓reduceDIte, he, entry_301, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_57, memoRow_eq_59, memoRow_eq_258]
  apply rowData_ext <;> decide +kernel


def memoRow_302 : RowData := ⟨{(-2, -2), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -2), (2, -1)}, {(-2, -2), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -2), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (4, -1)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_302 : rowAt 302 = memoRow_302 := by
  have he : entryAt 302 = entry_302 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 302 < 6 by decide, ↓reduceDIte, he, entry_302, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_125, memoRow_eq_162]
  apply rowData_ext <;> decide +kernel


def memoRow_303 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, -3)}, {(-2, 0), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, 0), (4, 1)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_303 : rowAt 303 = memoRow_303 := by
  have he : entryAt 303 = entry_303 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 303 < 6 by decide, ↓reduceDIte, he, entry_303, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_44, memoRow_eq_49, memoRow_eq_63, memoRow_eq_261]
  apply rowData_ext <;> decide +kernel


def memoRow_304 : RowData := ⟨{(1, -1), (1, 0), (2, 0), (3, 0)}, {(-3, -1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (3, 0), (3, 1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1), (7, -1), (7, 1)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_304 : rowAt 304 = memoRow_304 := by
  have he : entryAt 304 = entry_304 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 304 < 6 by decide, ↓reduceDIte, he, entry_304, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_55, memoRow_eq_131, memoRow_eq_202]
  apply rowData_ext <;> decide +kernel


def memoRow_305 : RowData := ⟨{(-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0)}, {(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_305 : rowAt 305 = memoRow_305 := by
  have he : entryAt 305 = entry_305 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 305 < 6 by decide, ↓reduceDIte, he, entry_305, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_278]
  apply rowData_ext <;> decide +kernel


def memoRow_306 : RowData := ⟨{(-1, -4), (-1, -3), (-1, -2), (-1, -1), (0, -3), (1, -3), (2, -3)}, {(-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, 0), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -2), (3, 0), (3, 1), (3, 2)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_306 : rowAt 306 = memoRow_306 := by
  have he : entryAt 306 = entry_306 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 306 < 6 by decide, ↓reduceDIte, he, entry_306, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_4, memoRow_eq_288]
  apply rowData_ext <;> decide +kernel


def memoRow_307 : RowData := ⟨{(-1, -2), (-1, -1), (-1, 1), (0, -2), (0, -1), (0, 1)}, {(-3, 1), (-2, 1), (-1, -2), (-1, -1), (-1, 1), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_307 : rowAt 307 = memoRow_307 := by
  have he : entryAt 307 = entry_307 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 307 < 6 by decide, ↓reduceDIte, he, entry_307, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_273]
  apply rowData_ext <;> decide +kernel


def memoRow_308 : RowData := ⟨{(0, 1), (1, 1), (2, 1), (3, 1)}, {(-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 1), (3, 2), (3, 3), (3, 4), (4, 2), (4, 4)}, 11⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_308 : rowAt 308 = memoRow_308 := by
  have he : entryAt 308 = entry_308 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 308 < 6 by decide, ↓reduceDIte, he, entry_308, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_299]
  apply rowData_ext <;> decide +kernel


def memoRow_309 : RowData := ⟨{(-2, 0), (0, 1), (0, 2), (0, 3), (1, 1)}, {(-3, 0), (-2, 0), (-1, -1), (-1, 0), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 2), (3, 3), (3, 4), (4, 2), (4, 3), (4, 4)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_309 : rowAt 309 = memoRow_309 := by
  have he : entryAt 309 = entry_309 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 309 < 6 by decide, ↓reduceDIte, he, entry_309, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_28, memoRow_eq_268]
  apply rowData_ext <;> decide +kernel


def memoRow_310 : RowData := ⟨{(-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1)}, {(-3, 0), (-2, -1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -2), (3, -1), (3, 0), (4, -2), (4, 0)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_310 : rowAt 310 = memoRow_310 := by
  have he : entryAt 310 = entry_310 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 310 < 6 by decide, ↓reduceDIte, he, entry_310, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_281]
  apply rowData_ext <;> decide +kernel


def memoRow_311 : RowData := ⟨{(-1, 0), (0, -3), (0, -2), (0, -1), (1, 0)}, {(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_311 : rowAt 311 = memoRow_311 := by
  have he : entryAt 311 = entry_311 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 311 < 6 by decide, ↓reduceDIte, he, entry_311, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_278]
  apply rowData_ext <;> decide +kernel


def memoRow_312 : RowData := ⟨{(-2, -1), (-2, 0), (-1, -3), (-1, -1), (-1, 0)}, {(-3, -1), (-3, 2), (-2, -1), (-2, 0), (-2, 2), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (3, -1)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_312 : rowAt 312 = memoRow_312 := by
  have he : entryAt 312 = entry_312 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 312 < 6 by decide, ↓reduceDIte, he, entry_312, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_9, memoRow_eq_272]
  apply rowData_ext <;> decide +kernel


def memoRow_313 : RowData := ⟨{(-2, -1), (-1, -1), (0, -3), (0, -2), (0, -1), (1, -1)}, {(-2, -1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (3, -2), (3, -1), (4, -2), (4, -1), (5, -2)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_313 : rowAt 313 = memoRow_313 := by
  have he : entryAt 313 = entry_313 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 313 < 6 by decide, ↓reduceDIte, he, entry_313, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_148, memoRow_eq_162]
  apply rowData_ext <;> decide +kernel


def memoRow_314 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0)}, {(-3, -1), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_314 : rowAt 314 = memoRow_314 := by
  have he : entryAt 314 = entry_314 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 314 < 6 by decide, ↓reduceDIte, he, entry_314, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_305]
  apply rowData_ext <;> decide +kernel


def memoRow_315 : RowData := ⟨{(-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-1, -1), (0, -1)}, {(-4, 1), (-4, 2), (-4, 3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -1), (-2, 1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 2), (1, 3), (1, 4)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_315 : rowAt 315 = memoRow_315 := by
  have he : entryAt 315 = entry_315 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 315 < 6 by decide, ↓reduceDIte, he, entry_315, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_296]
  apply rowData_ext <;> decide +kernel


def memoRow_316 : RowData := ⟨{(0, 1), (0, 2), (0, 3), (1, 1), (2, 1), (3, 1)}, {(-1, 0), (-1, 4), (-1, 5), (-1, 6), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 1), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 4), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 2), (4, 4), (4, 5), (4, 6)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_316 : rowAt 316 = memoRow_316 := by
  have he : entryAt 316 = entry_316 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 316 < 6 by decide, ↓reduceDIte, he, entry_316, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_306]
  apply rowData_ext <;> decide +kernel


def memoRow_317 : RowData := ⟨{(-1, -3), (-1, -2), (-1, 0), (0, -3), (0, -2), (1, 0)}, {(-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_317 : rowAt 317 = memoRow_317 := by
  have he : entryAt 317 = entry_317 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 317 < 6 by decide, ↓reduceDIte, he, entry_317, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_26, memoRow_eq_99, memoRow_eq_263]
  apply rowData_ext <;> decide +kernel


def memoRow_318 : RowData := ⟨{(0, -3), (0, -2), (0, -1)}, {(-2, 0), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, 0), (4, 1)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_318 : rowAt 318 = memoRow_318 := by
  have he : entryAt 318 = entry_318 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 318 < 6 by decide, ↓reduceDIte, he, entry_318, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_55, memoRow_eq_63, memoRow_eq_64, memoRow_eq_261]
  apply rowData_ext <;> decide +kernel


def memoRow_319 : RowData := ⟨{(-3, 1), (-2, 1), (-1, 1)}, {(-6, 2), (-5, 1), (-5, 2), (-4, 1), (-4, 2), (-3, 1), (-2, 1), (-2, 2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 3), (3, 3)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_319 : rowAt 319 = memoRow_319 := by
  have he : entryAt 319 = entry_319 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 319 < 6 by decide, ↓reduceDIte, he, entry_319, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_39, memoRow_eq_109, memoRow_eq_122, memoRow_eq_266]
  apply rowData_ext <;> decide +kernel


def memoRow_320 : RowData := ⟨{(0, -3), (0, -2), (1, -3), (1, 0), (3, 0)}, {(-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (4, 0), (4, 1), (5, 0), (5, 1), (6, 1)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_320 : rowAt 320 = memoRow_320 := by
  have he : entryAt 320 = entry_320 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 320 < 6 by decide, ↓reduceDIte, he, entry_320, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_19, memoRow_eq_115, memoRow_eq_267]
  apply rowData_ext <;> decide +kernel


def memoRow_321 : RowData := ⟨{(0, 1), (0, 2), (1, 1), (2, 1)}, {(-3, 3), (-2, 3), (-1, -1), (-1, 0), (-1, 3), (-1, 4), (-1, 5), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 1), (2, 2), (3, 1), (3, 2), (4, 1), (4, 2), (5, 2)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_321 : rowAt 321 = memoRow_321 := by
  have he : entryAt 321 = entry_321 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 321 < 6 by decide, ↓reduceDIte, he, entry_321, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_97, memoRow_eq_165, memoRow_eq_223]
  apply rowData_ext <;> decide +kernel


def memoRow_322 : RowData := ⟨{(-3, -3), (-3, -2), (-3, -1), (-2, -3), (-2, 0), (-1, -3), (0, -3)}, {(-4, 0), (-4, 1), (-4, 2), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -3), (-2, 0), (-2, 1), (-1, -3), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (2, -4), (2, -2), (2, -1), (2, 0), (2, 1)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_322 : rowAt 322 = memoRow_322 := by
  have he : entryAt 322 = entry_322 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 322 < 6 by decide, ↓reduceDIte, he, entry_322, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_96, memoRow_eq_205]
  apply rowData_ext <;> decide +kernel


def memoRow_323 : RowData := ⟨{(-2, 0), (-1, -2), (-1, -1), (-1, 0)}, {(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_323 : rowAt 323 = memoRow_323 := by
  have he : entryAt 323 = entry_323 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 323 < 6 by decide, ↓reduceDIte, he, entry_323, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_25, memoRow_eq_165, memoRow_eq_278]
  apply rowData_ext <;> decide +kernel


def memoRow_324 : RowData := ⟨{(-1, -1), (1, -3), (1, -2), (1, -1), (1, 0)}, {(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_324 : rowAt 324 = memoRow_324 := by
  have he : entryAt 324 = entry_324 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 324 < 6 by decide, ↓reduceDIte, he, entry_324, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_298]
  apply rowData_ext <;> decide +kernel


def memoRow_325 : RowData := ⟨{(-1, 0), (1, -2), (1, -1), (1, 0), (1, 1)}, {(-2, 0), (-1, 0), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, 1)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_325 : rowAt 325 = memoRow_325 := by
  have he : entryAt 325 = entry_325 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 325 < 6 by decide, ↓reduceDIte, he, entry_325, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_24, memoRow_eq_25, memoRow_eq_313]
  apply rowData_ext <;> decide +kernel


def memoRow_326 : RowData := ⟨{(-4, -3), (-3, 0), (-2, 0), (-1, 0)}, {(-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 1), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, 0), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_326 : rowAt 326 = memoRow_326 := by
  have he : entryAt 326 = entry_326 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 326 < 6 by decide, ↓reduceDIte, he, entry_326, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_63, memoRow_eq_255]
  apply rowData_ext <;> decide +kernel


def memoRow_327 : RowData := ⟨{(-1, -1), (-1, 0), (1, -1), (1, 0)}, {(-6, -1), (-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_327 : rowAt 327 = memoRow_327 := by
  have he : entryAt 327 = entry_327 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 327 < 6 by decide, ↓reduceDIte, he, entry_327, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_24, memoRow_eq_195]
  apply rowData_ext <;> decide +kernel


def memoRow_328 : RowData := ⟨{(-1, -3), (0, -3), (0, -2), (0, -1)}, {(-3, 0), (-2, 0), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_328 : rowAt 328 = memoRow_328 := by
  have he : entryAt 328 = entry_328 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 328 < 6 by decide, ↓reduceDIte, he, entry_328, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_44, memoRow_eq_49, memoRow_eq_285]
  apply rowData_ext <;> decide +kernel


def memoRow_329 : RowData := ⟨{(-1, -2), (-1, -1), (-1, 1), (0, -2), (0, -1), (0, 1)}, {(-4, 0), (-4, 2), (-3, 0), (-3, 1), (-3, 2), (-2, 0), (-2, 1), (-2, 2), (-1, -2), (-1, -1), (-1, 1), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_329 : rowAt 329 = memoRow_329 := by
  have he : entryAt 329 = entry_329 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 329 < 6 by decide, ↓reduceDIte, he, entry_329, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_305]
  apply rowData_ext <;> decide +kernel


def memoRow_330 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-5, 0), (-4, 0), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (3, 1), (3, 2)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_330 : rowAt 330 = memoRow_330 := by
  have he : entryAt 330 = entry_330 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 330 < 6 by decide, ↓reduceDIte, he, entry_330, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_63, memoRow_eq_144, memoRow_eq_154, memoRow_eq_155, memoRow_eq_268]
  apply rowData_ext <;> decide +kernel


def memoRow_331 : RowData := ⟨{(-4, -1), (-3, -1), (-2, -1), (-2, 0), (-2, 1), (-1, 1)}, {(-7, 0), (-6, 0), (-6, 1), (-6, 2), (-5, 0), (-5, 1), (-5, 2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (3, 0), (3, 2)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_331 : rowAt 331 = memoRow_331 := by
  have he : entryAt 331 = entry_331 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 331 < 6 by decide, ↓reduceDIte, he, entry_331, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_15, memoRow_eq_90, memoRow_eq_113, memoRow_eq_298]
  apply rowData_ext <;> decide +kernel


def memoRow_332 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, -1), (1, 0)}, {(-3, 0), (-2, 0), (-1, -4), (-1, -3), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (2, -4), (2, -3), (2, -2), (2, -1), (3, -4), (3, -3), (3, -2), (4, -4), (4, -3), (4, -2), (5, -4), (5, -3), (5, -2), (6, -2)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_332 : rowAt 332 = memoRow_332 := by
  have he : entryAt 332 = entry_332 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 332 < 6 by decide, ↓reduceDIte, he, entry_332, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_67, memoRow_eq_289]
  apply rowData_ext <;> decide +kernel


def memoRow_333 : RowData := ⟨{(0, -3), (0, -2), (1, -4), (1, -3), (1, -2), (2, 0)}, {(-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_333 : rowAt 333 = memoRow_333 := by
  have he : entryAt 333 = entry_333 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 333 < 6 by decide, ↓reduceDIte, he, entry_333, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_1, memoRow_eq_317]
  apply rowData_ext <;> decide +kernel


def memoRow_334 : RowData := ⟨{(0, -2), (0, -1), (0, 1), (1, -2), (1, -1)}, {(-3, -2), (-2, -2), (-1, -3), (-1, -2), (-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 0)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_334 : rowAt 334 = memoRow_334 := by
  have he : entryAt 334 = entry_334 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 334 < 6 by decide, ↓reduceDIte, he, entry_334, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_67, memoRow_eq_289]
  apply rowData_ext <;> decide +kernel


def memoRow_335 : RowData := ⟨{(-3, 0), (-2, -2), (-2, 0), (-1, -1), (-1, 0)}, {(-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_335 : rowAt 335 = memoRow_335 := by
  have he : entryAt 335 = entry_335 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 335 < 6 by decide, ↓reduceDIte, he, entry_335, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_162, memoRow_eq_196]
  apply rowData_ext <;> decide +kernel


def memoRow_336 : RowData := ⟨{(-1, -1), (-1, 0), (1, 0)}, {(-5, -1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 1)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_336 : rowAt 336 = memoRow_336 := by
  have he : entryAt 336 = entry_336 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 336 < 6 by decide, ↓reduceDIte, he, entry_336, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_25, memoRow_eq_65, memoRow_eq_199, memoRow_eq_304]
  apply rowData_ext <;> decide +kernel


def memoRow_337 : RowData := ⟨{(-3, 0), (-1, 0), (-1, 1), (-1, 2)}, {(-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-2, 3), (-2, 4), (-2, 5), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_337 : rowAt 337 = memoRow_337 := by
  have he : entryAt 337 = entry_337 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 337 < 6 by decide, ↓reduceDIte, he, entry_337, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_107, memoRow_eq_230]
  apply rowData_ext <;> decide +kernel


def memoRow_338 : RowData := ⟨{(-1, 0), (1, -2), (1, -1), (1, 0)}, {(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, -1), (0, 0), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, 1)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_338 : rowAt 338 = memoRow_338 := by
  have he : entryAt 338 = entry_338 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 338 < 6 by decide, ↓reduceDIte, he, entry_338, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_107, memoRow_eq_241, memoRow_eq_275]
  apply rowData_ext <;> decide +kernel


def memoRow_339 : RowData := ⟨{(-1, -4), (-1, -3), (-1, -2), (-1, -1), (0, -3), (1, -3), (2, -3)}, {(-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -1), (0, 0), (0, 1), (1, -3), (1, 0), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (4, -4), (4, -2), (4, -1), (4, 0), (4, 1)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_339 : rowAt 339 = memoRow_339 := by
  have he : entryAt 339 = entry_339 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 339 < 6 by decide, ↓reduceDIte, he, entry_339, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_4, memoRow_eq_322]
  apply rowData_ext <;> decide +kernel


def memoRow_340 : RowData := ⟨{(-1, 1), (0, -1), (0, 1)}, {(-4, -2), (-4, 0), (-3, -2), (-3, -1), (-3, 0), (-2, -2), (-2, -1), (-2, 0), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (3, 0)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_340 : rowAt 340 = memoRow_340 := by
  have he : entryAt 340 = entry_340 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 340 < 6 by decide, ↓reduceDIte, he, entry_340, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_24, memoRow_eq_25, memoRow_eq_300]
  apply rowData_ext <;> decide +kernel


def memoRow_341 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0), (-1, 1)}, {(-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-1, 0), (-1, 1), (-1, 2), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, 1)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_341 : rowAt 341 = memoRow_341 := by
  have he : entryAt 341 = entry_341 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 341 < 6 by decide, ↓reduceDIte, he, entry_341, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_143, memoRow_eq_162, memoRow_eq_208, memoRow_eq_259]
  apply rowData_ext <;> decide +kernel


def memoRow_342 : RowData := ⟨{(-2, -2), (-1, -3), (-1, -2), (0, -3), (0, -2)}, {(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, -3), (2, -2), (2, -1), (3, -3), (3, -2), (3, -1)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_342 : rowAt 342 = memoRow_342 := by
  have he : entryAt 342 = entry_342 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 342 < 6 by decide, ↓reduceDIte, he, entry_342, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_88, memoRow_eq_210, memoRow_eq_260, memoRow_eq_290]
  apply rowData_ext <;> decide +kernel


def memoRow_343 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, -3), (1, -2)}, {(-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_343 : rowAt 343 = memoRow_343 := by
  have he : entryAt 343 = entry_343 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 343 < 6 by decide, ↓reduceDIte, he, entry_343, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_250]
  apply rowData_ext <;> decide +kernel


def memoRow_344 : RowData := ⟨{(0, -4), (0, -3), (0, -2), (0, -1), (1, -3), (2, -3), (3, -3), (3, -2)}, {(-1, -1), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_344 : rowAt 344 = memoRow_344 := by
  have he : entryAt 344 = entry_344 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 344 < 6 by decide, ↓reduceDIte, he, entry_344, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_7, memoRow_eq_108, memoRow_eq_262]
  apply rowData_ext <;> decide +kernel


def memoRow_345 : RowData := ⟨{(-3, 0), (-3, 3), (-2, 0), (-1, 0), (-1, 3), (0, 1)}, {(-6, 4), (-5, 3), (-5, 4), (-4, 3), (-4, 4), (-3, 0), (-3, 3), (-3, 4), (-2, 0), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (-1, 3), (-1, 4), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 2), (2, 3), (2, 4), (3, 2), (3, 3), (3, 4)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_345 : rowAt 345 = memoRow_345 := by
  have he : entryAt 345 = entry_345 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 345 < 6 by decide, ↓reduceDIte, he, entry_345, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_320]
  apply rowData_ext <;> decide +kernel


def memoRow_346 : RowData := ⟨{(-3, -4), (-3, -3), (-3, -2), (-3, -1), (-1, -3), (0, -3), (0, -2)}, {(-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (1, 1), (1, 2)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_346 : rowAt 346 = memoRow_346 := by
  have he : entryAt 346 = entry_346 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 346 < 6 by decide, ↓reduceDIte, he, entry_346, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_60, memoRow_eq_255, memoRow_eq_276]
  apply rowData_ext <;> decide +kernel


def memoRow_347 : RowData := ⟨{(0, 1), (0, 2), (0, 3), (1, 1), (2, 1), (3, 1)}, {(-1, 0), (-1, 4), (-1, 5), (-1, 6), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 1), (1, 3), (1, 4), (1, 5), (2, 1), (2, 4), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 0), (5, 2), (5, 3), (5, 4), (5, 5)}, 11⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_347 : rowAt 347 = memoRow_347 := by
  have he : entryAt 347 = entry_347 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 347 < 6 by decide, ↓reduceDIte, he, entry_347, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_339]
  apply rowData_ext <;> decide +kernel


def memoRow_348 : RowData := ⟨{(-2, 0), (-2, 1), (-1, -1), (0, -2), (0, -1), (1, -1), (1, 0)}, {(-3, 1), (-2, 0), (-2, 1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (2, 3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2)}, 11⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_348 : rowAt 348 = memoRow_348 := by
  have he : entryAt 348 = entry_348 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 348 < 6 by decide, ↓reduceDIte, he, entry_348, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_114, memoRow_eq_139, memoRow_eq_312]
  apply rowData_ext <;> decide +kernel


def memoRow_349 : RowData := ⟨{(-1, -3), (-1, -2), (-1, -1), (0, -1)}, {(-4, 0), (-3, 0), (-2, -4), (-2, -3), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -4), (1, -3), (1, -2), (1, -1), (2, -4), (2, -3), (2, -2), (3, -4), (3, -3), (3, -2), (4, -4), (4, -3), (4, -2), (5, -2)}, 11⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_349 : rowAt 349 = memoRow_349 := by
  have he : entryAt 349 = entry_349 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 349 < 6 by decide, ↓reduceDIte, he, entry_349, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_14, memoRow_eq_17, memoRow_eq_332]
  apply rowData_ext <;> decide +kernel


def memoRow_350 : RowData := ⟨{(-1, 0), (-1, 1), (1, 0), (1, 2)}, {(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 3), (2, 4), (2, 5), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_350 : rowAt 350 = memoRow_350 := by
  have he : entryAt 350 = entry_350 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 350 < 6 by decide, ↓reduceDIte, he, entry_350, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_24, memoRow_eq_107, memoRow_eq_215, memoRow_eq_271]
  apply rowData_ext <;> decide +kernel


def memoRow_351 : RowData := ⟨{(-2, -1), (-2, 0), (-2, 1), (-1, 0)}, {(-5, 1), (-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 3), (-1, 4), (-1, 5), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)}, 11⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_351 : rowAt 351 = memoRow_351 := by
  have he : entryAt 351 = entry_351 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 351 < 6 by decide, ↓reduceDIte, he, entry_351, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_25, memoRow_eq_163, memoRow_eq_287]
  apply rowData_ext <;> decide +kernel


def memoRow_352 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, -2), (2, -2), (3, -2), (3, -1)}, {(-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2)}, 11⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_352 : rowAt 352 = memoRow_352 := by
  have he : entryAt 352 = entry_352 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 352 < 6 by decide, ↓reduceDIte, he, entry_352, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_63, memoRow_eq_91, memoRow_eq_180, memoRow_eq_214, memoRow_eq_344]
  apply rowData_ext <;> decide +kernel


def memoRow_353 : RowData := ⟨{(-3, 0), (-3, 1), (-3, 2), (-2, 0), (-1, 0)}, {(-4, -1), (-4, 1), (-4, 3), (-4, 4), (-4, 5), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-1, 0), (-1, 3), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 1), (2, 2), (2, 3), (2, 4)}, 12⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_353 : rowAt 353 = memoRow_353 := by
  have he : entryAt 353 = entry_353 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 353 < 6 by decide, ↓reduceDIte, he, entry_353, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_347]
  apply rowData_ext <;> decide +kernel


def memoRow_354 : RowData := ⟨{(-1, -1), (-1, 0), (-1, 1), (0, -2), (0, 1), (1, -2)}, {(-3, 0), (-2, -1), (-2, 0), (-2, 3), (-1, -1), (-1, 0), (-1, 1), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 3), (0, 4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (4, 0)}, 11⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_354 : rowAt 354 = memoRow_354 := by
  have he : entryAt 354 = entry_354 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 354 < 6 by decide, ↓reduceDIte, he, entry_354, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_114, memoRow_eq_138, memoRow_eq_182, memoRow_eq_312]
  apply rowData_ext <;> decide +kernel


def memoRow_355 : RowData := ⟨{(1, -1), (1, 0), (2, -1), (2, 0)}, {(-2, 0), (-2, 1), (-2, 3), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_355 : rowAt 355 = memoRow_355 := by
  have he : entryAt 355 = entry_355 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 355 < 6 by decide, ↓reduceDIte, he, entry_355, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_12, memoRow_eq_167, memoRow_eq_342]
  apply rowData_ext <;> decide +kernel


def memoRow_356 : RowData := ⟨{(-1, -1), (-1, 0), (1, -1), (1, 0), (1, 1)}, {(-4, -1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (3, -1), (3, 0), (4, -1), (4, 0), (5, -1), (5, 0), (6, -1)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_356 : rowAt 356 = memoRow_356 := by
  have he : entryAt 356 = entry_356 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 356 < 6 by decide, ↓reduceDIte, he, entry_356, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_24, memoRow_eq_179, memoRow_eq_211]
  apply rowData_ext <;> decide +kernel


def memoRow_357 : RowData := ⟨{(-2, 2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, 2)}, {(-4, -1), (-3, -1), (-3, 1), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, 0), (0, 1), (0, 2), (0, 4), (0, 5), (0, 6), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 3)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_357 : rowAt 357 = memoRow_357 := by
  have he : entryAt 357 = entry_357 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 357 < 6 by decide, ↓reduceDIte, he, entry_357, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_82, memoRow_eq_283]
  apply rowData_ext <;> decide +kernel


def memoRow_358 : RowData := ⟨{(-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-1, -1), (0, -1)}, {(-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 2), (-2, 3), (-2, 4), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4)}, 11⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_358 : rowAt 358 = memoRow_358 := by
  have he : entryAt 358 = entry_358 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 358 < 6 by decide, ↓reduceDIte, he, entry_358, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_346]
  apply rowData_ext <;> decide +kernel


def memoRow_359 : RowData := ⟨{(-1, -1), (-1, 1), (0, -1), (0, 1)}, {(-4, 0), (-4, 2), (-3, 0), (-3, 1), (-3, 2), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 1), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_359 : rowAt 359 = memoRow_359 := by
  have he : entryAt 359 = entry_359 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 359 < 6 by decide, ↓reduceDIte, he, entry_359, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_24, memoRow_eq_134, memoRow_eq_323]
  apply rowData_ext <;> decide +kernel


def memoRow_360 : RowData := ⟨{(-2, -2), (0, -4), (0, -3), (0, -2), (0, -1)}, {(-3, -1), (-2, -2), (-2, -1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, -1), (1, 1), (1, 2), (1, 3), (2, -3), (2, -2), (2, -1), (3, -3), (3, -2), (3, -1), (4, -3), (4, -2), (4, -1), (5, -3), (5, -1)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_360 : rowAt 360 = memoRow_360 := by
  have he : entryAt 360 = entry_360 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 360 < 6 by decide, ↓reduceDIte, he, entry_360, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_7, memoRow_eq_155, memoRow_eq_228, memoRow_eq_337]
  apply rowData_ext <;> decide +kernel


def memoRow_361 : RowData := ⟨{(0, -2), (0, -1), (1, -1), (2, -1), (3, -1), (3, 0)}, {(-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, 1), (4, 2), (4, 3)}, 12⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_361 : rowAt 361 = memoRow_361 := by
  have he : entryAt 361 = entry_361 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 361 < 6 by decide, ↓reduceDIte, he, entry_361, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_352]
  apply rowData_ext <;> decide +kernel


def memoRow_362 : RowData := ⟨{(-4, -1), (-3, -1), (-3, 2), (-2, -1), (-1, -1), (-1, 2)}, {(-6, 3), (-5, 2), (-5, 3), (-4, -1), (-4, 2), (-4, 3), (-3, -1), (-3, 2), (-3, 3), (-2, -1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (3, 3)}, 11⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_362 : rowAt 362 = memoRow_362 := by
  have he : entryAt 362 = entry_362 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 362 < 6 by decide, ↓reduceDIte, he, entry_362, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_4, memoRow_eq_345]
  apply rowData_ext <;> decide +kernel


def memoRow_363 : RowData := ⟨{(-4, -3), (-3, -3), (-3, 0), (-2, -3), (-1, -3), (-1, 0)}, {(-5, -1), (-4, -3), (-4, -1), (-4, 0), (-3, -3), (-3, -1), (-3, 0), (-2, -3), (-2, -1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, -4), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_363 : rowAt 363 = memoRow_363 := by
  have he : entryAt 363 = entry_363 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 363 < 6 by decide, ↓reduceDIte, he, entry_363, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_137, memoRow_eq_248]
  apply rowData_ext <;> decide +kernel


def memoRow_364 : RowData := ⟨{(0, -3), (0, -2), (0, -1)}, {(-4, -4), (-4, -2), (-3, -4), (-3, -3), (-3, -2), (-2, -4), (-2, -3), (-2, -2), (-1, -4), (-1, -3), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, -4), (2, -3), (2, -2), (3, -4), (3, -3), (3, -2), (4, -4), (4, -3), (4, -2), (5, -2)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_364 : rowAt 364 = memoRow_364 := by
  have he : entryAt 364 = entry_364 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 364 < 6 by decide, ↓reduceDIte, he, entry_364, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_63, memoRow_eq_314]
  apply rowData_ext <;> decide +kernel


def memoRow_365 : RowData := ⟨{(-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (1, -3)}, {(-3, -1), (-2, -2), (-2, -1), (-2, 2), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, -1)}, 12⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_365 : rowAt 365 = memoRow_365 := by
  have he : entryAt 365 = entry_365 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 365 < 6 by decide, ↓reduceDIte, he, entry_365, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_354]
  apply rowData_ext <;> decide +kernel


def memoRow_366 : RowData := ⟨{(1, -3), (1, -2), (1, -1), (1, 0), (2, 0)}, {(-2, -3), (-1, -3), (-1, -1), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (2, 2), (2, 3), (2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 1)}, 11⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_366 : rowAt 366 = memoRow_366 := by
  have he : entryAt 366 = entry_366 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 366 < 6 by decide, ↓reduceDIte, he, entry_366, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_357]
  apply rowData_ext <;> decide +kernel


def memoRow_367 : RowData := ⟨{(-3, 1), (-3, 2), (-2, 1), (-1, 1), (0, 1)}, {(-4, 3), (-4, 4), (-4, 5), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 0), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7)}, 13⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_367 : rowAt 367 = memoRow_367 := by
  have he : entryAt 367 = entry_367 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 367 < 6 by decide, ↓reduceDIte, he, entry_367, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_361]
  apply rowData_ext <;> decide +kernel


def memoRow_368 : RowData := ⟨{(-1, -3), (-1, -2), (-1, -1), (-1, 0)}, {(-4, -3), (-3, -3), (-3, -1), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 1)}, 12⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_368 : rowAt 368 = memoRow_368 := by
  have he : entryAt 368 = entry_368 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 368 < 6 by decide, ↓reduceDIte, he, entry_368, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_366]
  apply rowData_ext <;> decide +kernel


def memoRow_369 : RowData := ⟨{(-3, -1), (-2, -1), (-1, -1), (0, -1)}, {(-4, -2), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3)}, 14⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_369 : rowAt 369 = memoRow_369 := by
  have he : entryAt 369 = entry_369 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 369 < 6 by decide, ↓reduceDIte, he, entry_369, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_367]
  apply rowData_ext <;> decide +kernel


def memoRow_370 : RowData := ⟨{(-2, -1), (-2, 0), (-1, 0)}, {(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 2), (4, 2)}, 11⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_370 : rowAt 370 = memoRow_370 := by
  have he : entryAt 370 = entry_370 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 370 < 6 by decide, ↓reduceDIte, he, entry_370, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_24, memoRow_eq_199, memoRow_eq_286, memoRow_eq_319]
  apply rowData_ext <;> decide +kernel


def memoRow_371 : RowData := ⟨{(-4, -3), (-3, -3), (-3, 0), (-2, -3), (-1, -3), (-1, 0)}, {(-6, 1), (-5, 0), (-5, 1), (-4, -3), (-4, 0), (-4, 1), (-3, -3), (-3, 0), (-3, 1), (-2, -3), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, -4), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_371 : rowAt 371 = memoRow_371 := by
  have he : entryAt 371 = entry_371 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 371 < 6 by decide, ↓reduceDIte, he, entry_371, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_137, memoRow_eq_267]
  apply rowData_ext <;> decide +kernel


def memoRow_372 : RowData := ⟨{(-2, -3), (-2, -2), (-1, -4), (-1, -3), (-1, -2)}, {(-5, 1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (1, 0), (1, 1), (2, -2), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1)}, 11⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_372 : rowAt 372 = memoRow_372 := by
  have he : entryAt 372 = entry_372 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 372 < 6 by decide, ↓reduceDIte, he, entry_372, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_40, memoRow_eq_120, memoRow_eq_161, memoRow_eq_333]
  apply rowData_ext <;> decide +kernel


def memoRow_373 : RowData := ⟨{(-1, -1), (0, -1), (0, 1), (2, -1), (2, 0), (2, 1)}, {(-5, 0), (-5, 2), (-4, 0), (-4, 1), (-4, 2), (-3, 0), (-3, 1), (-3, 2), (-2, 0), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 0), (6, 1), (6, 2), (7, 0)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_373 : rowAt 373 = memoRow_373 := by
  have he : entryAt 373 = entry_373 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 373 < 6 by decide, ↓reduceDIte, he, entry_373, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_80, memoRow_eq_156, memoRow_eq_226, memoRow_eq_327]
  apply rowData_ext <;> decide +kernel


def memoRow_374 : RowData := ⟨{(1, -2), (1, 0), (2, -1), (2, 0)}, {(-3, -1), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (3, -1), (3, 0), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1), (7, -1)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_374 : rowAt 374 = memoRow_374 := by
  have he : entryAt 374 = entry_374 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 374 < 6 by decide, ↓reduceDIte, he, entry_374, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_24, memoRow_eq_65, memoRow_eq_163, memoRow_eq_335]
  apply rowData_ext <;> decide +kernel


def memoRow_375 : RowData := ⟨{(-2, -1), (-2, 0), (-1, 1), (0, -1), (0, 1)}, {(-7, 0), (-6, -2), (-6, -1), (-6, 0), (-5, -2), (-5, -1), (-5, 0), (-4, -2), (-4, -1), (-4, 0), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (3, -2), (3, -1), (3, 0), (4, -2), (4, -1), (4, 0), (5, 0)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_375 : rowAt 375 = memoRow_375 := by
  have he : entryAt 375 = entry_375 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 375 < 6 by decide, ↓reduceDIte, he, entry_375, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_24, memoRow_eq_327]
  apply rowData_ext <;> decide +kernel


def memoRow_376 : RowData := ⟨{(-3, 0), (-2, 0), (-1, -1), (-1, 0)}, {(-6, 2), (-5, 2), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_376 : rowAt 376 = memoRow_376 := by
  have he : entryAt 376 = entry_376 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 376 < 6 by decide, ↓reduceDIte, he, entry_376, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_162, memoRow_eq_285]
  apply rowData_ext <;> decide +kernel


def memoRow_377 : RowData := ⟨{(-1, -3), (0, -3), (0, -2), (1, -3), (2, -3), (2, 0)}, {(-3, 1), (-2, -4), (-2, 0), (-2, 1), (-1, -4), (-1, -3), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, 0), (1, 1), (2, -4), (2, -3), (2, -2), (2, 0), (2, 1), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1)}, 12⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_377 : rowAt 377 = memoRow_377 := by
  have he : entryAt 377 = entry_377 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 377 < 6 by decide, ↓reduceDIte, he, entry_377, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_29, memoRow_eq_362]
  apply rowData_ext <;> decide +kernel


def memoRow_378 : RowData := ⟨{(-2, 0), (-1, -2), (-1, 0)}, {(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 1)}, 11⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_378 : rowAt 378 = memoRow_378 := by
  have he : entryAt 378 = entry_378 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 378 < 6 by decide, ↓reduceDIte, he, entry_378, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_172, memoRow_eq_176, memoRow_eq_183, memoRow_eq_294, memoRow_eq_295]
  apply rowData_ext <;> decide +kernel


def memoRow_379 : RowData := ⟨{(0, -3), (0, -2), (0, -1)}, {(-3, -3), (-2, -3), (-2, -1), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 1)}, 13⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_379 : rowAt 379 = memoRow_379 := by
  have he : entryAt 379 = entry_379 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 379 < 6 by decide, ↓reduceDIte, he, entry_379, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_55, memoRow_eq_63, memoRow_eq_64, memoRow_eq_368]
  apply rowData_ext <;> decide +kernel


def memoRow_380 : RowData := ⟨{(-2, 0), (-2, 2), (-1, -1), (-1, 0)}, {(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 3), (-3, 4), (-3, 5), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (-1, 3), (-1, 4), (-1, 5), (0, -2), (0, -1), (0, 0), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_380 : rowAt 380 = memoRow_380 := by
  have he : entryAt 380 = entry_380 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 380 < 6 by decide, ↓reduceDIte, he, entry_380, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_101, memoRow_eq_192, memoRow_eq_223, memoRow_eq_271]
  apply rowData_ext <;> decide +kernel


def memoRow_381 : RowData := ⟨{(1, 0), (2, -1), (2, 0), (2, 1)}, {(-3, -1), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1), (7, 1)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_381 : rowAt 381 = memoRow_381 := by
  have he : entryAt 381 = entry_381 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 381 < 6 by decide, ↓reduceDIte, he, entry_381, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_24, memoRow_eq_163, memoRow_eq_211, memoRow_eq_341]
  apply rowData_ext <;> decide +kernel


def memoRow_382 : RowData := ⟨{(-2, -2), (-1, -3), (-1, -2), (0, -2), (0, 1), (1, -2)}, {(-2, -2), (-1, -3), (-1, -2), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, -1)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_382 : rowAt 382 = memoRow_382 := by
  have he : entryAt 382 = entry_382 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 382 < 6 by decide, ↓reduceDIte, he, entry_382, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_2, memoRow_eq_124]
  apply rowData_ext <;> decide +kernel


def memoRow_383 : RowData := ⟨{(-1, 0), (-1, 2), (1, 0)}, {(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 3), (-2, 4), (-2, 5), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_383 : rowAt 383 = memoRow_383 := by
  have he : entryAt 383 = entry_383 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 383 < 6 by decide, ↓reduceDIte, he, entry_383, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_172, memoRow_eq_192, memoRow_eq_197, memoRow_eq_215, memoRow_eq_271]
  apply rowData_ext <;> decide +kernel


def memoRow_384 : RowData := ⟨{(-1, 0), (1, 0)}, {(-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (-1, 2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1)}, 11⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_384 : rowAt 384 = memoRow_384 := by
  have he : entryAt 384 = entry_384 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 384 < 6 by decide, ↓reduceDIte, he, entry_384, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_173, memoRow_eq_183, memoRow_eq_220, memoRow_eq_246, memoRow_eq_263, memoRow_eq_282, memoRow_eq_295]
  apply rowData_ext <;> decide +kernel


def memoRow_385 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -1), (2, 1)}, 15⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_385 : rowAt 385 = memoRow_385 := by
  have he : entryAt 385 = entry_385 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 385 < 6 by decide, ↓reduceDIte, he, entry_385, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_55, memoRow_eq_63, memoRow_eq_64, memoRow_eq_369]
  apply rowData_ext <;> decide +kernel


def memoRow_386 : RowData := ⟨{(-2, 0), (-1, -2), (-1, 0)}, {(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_386 : rowAt 386 = memoRow_386 := by
  have he : entryAt 386 = entry_386 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 386 < 6 by decide, ↓reduceDIte, he, entry_386, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_172, memoRow_eq_173, memoRow_eq_217, memoRow_eq_294]
  apply rowData_ext <;> decide +kernel


def memoRow_387 : RowData := ⟨{(-1, -2), (-1, -1), (-1, 0), (0, 1)}, {(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 2), (5, 2)}, 12⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_387 : rowAt 387 = memoRow_387 := by
  have he : entryAt 387 = entry_387 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 387 < 6 by decide, ↓reduceDIte, he, entry_387, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_14, memoRow_eq_370]
  apply rowData_ext <;> decide +kernel


def memoRow_388 : RowData := ⟨{(0, -2), (1, -3), (1, -2), (1, -1), (1, 0)}, {(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -3), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1)}, 11⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_388 : rowAt 388 = memoRow_388 := by
  have he : entryAt 388 = entry_388 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 388 < 6 by decide, ↓reduceDIte, he, entry_388, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_374]
  apply rowData_ext <;> decide +kernel


def memoRow_389 : RowData := ⟨{(-2, -2), (0, -2), (0, -1)}, {(-5, -3), (-5, -1), (-4, -3), (-4, -2), (-4, -1), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-2, -2), (-2, 0), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -3), (2, 0), (2, 1), (3, 1), (4, 1)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_389 : rowAt 389 = memoRow_389 := by
  have he : entryAt 389 = entry_389 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 389 < 6 by decide, ↓reduceDIte, he, entry_389, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_192, memoRow_eq_197, memoRow_eq_215, memoRow_eq_236, memoRow_eq_271]
  apply rowData_ext <;> decide +kernel


def memoRow_390 : RowData := ⟨{(-1, -2), (-1, -1), (0, -2), (0, -1)}, {(-4, -5), (-3, -5), (-3, -4), (-2, -5), (-2, -4), (-2, -3), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -5), (2, -4), (2, -2), (3, -5), (3, -4), (3, -3), (3, -2), (4, -5), (4, -4), (4, -3), (5, -5), (5, -4), (5, -3)}, 12⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_390 : rowAt 390 = memoRow_390 := by
  have he : entryAt 390 = entry_390 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 390 < 6 by decide, ↓reduceDIte, he, entry_390, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_12, memoRow_eq_167, memoRow_eq_372]
  apply rowData_ext <;> decide +kernel


def memoRow_391 : RowData := ⟨{(-1, -1), (0, -2), (0, -1), (0, 1), (1, -2)}, {(-5, 0), (-5, 2), (-4, 0), (-4, 1), (-4, 2), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -2), (0, -1), (0, 0), (0, 1), (1, -3), (1, -2), (1, 0), (1, 1), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0)}, 12⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_391 : rowAt 391 = memoRow_391 := by
  have he : entryAt 391 = entry_391 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 391 < 6 by decide, ↓reduceDIte, he, entry_391, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_388]
  apply rowData_ext <;> decide +kernel


def memoRow_392 : RowData := ⟨{(-1, -2), (0, -2), (0, -1)}, {(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)}, 11⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_392 : rowAt 392 = memoRow_392 := by
  have he : entryAt 392 = entry_392 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 392 < 6 by decide, ↓reduceDIte, he, entry_392, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_24, memoRow_eq_107, memoRow_eq_236, memoRow_eq_364]
  apply rowData_ext <;> decide +kernel


def memoRow_393 : RowData := ⟨{(0, -2), (0, -1), (1, -2), (2, -3), (2, -2), (3, -2), (3, -1)}, {(-2, 1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1)}, 12⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_393 : rowAt 393 = memoRow_393 := by
  have he : entryAt 393 = entry_393 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 393 < 6 by decide, ↓reduceDIte, he, entry_393, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_65, memoRow_eq_107, memoRow_eq_303, memoRow_eq_348]
  apply rowData_ext <;> decide +kernel


def memoRow_394 : RowData := ⟨{(-2, -1), (-2, 0), (0, -1)}, {(-7, -2), (-7, -1), (-7, 0), (-7, 1), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (2, 1), (3, -2), (3, -1), (3, 0), (3, 1), (4, -2), (4, -1), (4, 0), (4, 1), (5, -2), (5, -1), (5, 0), (5, 1)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_394 : rowAt 394 = memoRow_394 := by
  have he : entryAt 394 = entry_394 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 394 < 6 by decide, ↓reduceDIte, he, entry_394, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_226, memoRow_eq_327]
  apply rowData_ext <;> decide +kernel


def memoRow_395 : RowData := ⟨{(-1, 0), (1, -1), (1, 0), (1, 1)}, {(-4, -1), (-4, 1), (-4, 2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1)}, 11⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_395 : rowAt 395 = memoRow_395 := by
  have he : entryAt 395 = entry_395 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 395 < 6 by decide, ↓reduceDIte, he, entry_395, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_24, memoRow_eq_211, memoRow_eq_236, memoRow_eq_376]
  apply rowData_ext <;> decide +kernel


def memoRow_396 : RowData := ⟨{(0, -2), (0, -1), (1, -2), (2, -2), (3, -2)}, {(-2, 1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (4, -1), (4, 0), (4, 1), (4, 2), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1)}, 13⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_396 : rowAt 396 = memoRow_396 := by
  have he : entryAt 396 = entry_396 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 396 < 6 by decide, ↓reduceDIte, he, entry_396, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_65, memoRow_eq_107, memoRow_eq_303, memoRow_eq_365]
  apply rowData_ext <;> decide +kernel


def memoRow_397 : RowData := ⟨{(0, -2), (1, -2), (1, -1), (1, 0)}, {(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (2, -5), (2, -4), (2, -3), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1)}, 11⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_397 : rowAt 397 = memoRow_397 := by
  have he : entryAt 397 = entry_397 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 397 < 6 by decide, ↓reduceDIte, he, entry_397, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_24, memoRow_eq_65, memoRow_eq_374]
  apply rowData_ext <;> decide +kernel


def memoRow_398 : RowData := ⟨{(-3, -4), (-3, -3), (-3, -2), (-2, -3), (-2, 0), (-1, -3), (0, -3)}, {(-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -3), (-2, -1), (-2, 0), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -4), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_398 : rowAt 398 = memoRow_398 := by
  have he : entryAt 398 = entry_398 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 398 < 6 by decide, ↓reduceDIte, he, entry_398, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_130, memoRow_eq_177, memoRow_eq_257, memoRow_eq_363]
  apply rowData_ext <;> decide +kernel


def memoRow_399 : RowData := ⟨{(-2, -2), (0, -2), (0, -1)}, {(-5, -3), (-5, -1), (-4, -3), (-4, -2), (-4, -1), (-3, -3), (-3, -2), (-3, -1), (-2, -2), (-2, 1), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (4, 1), (4, 2)}, 11⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_399 : rowAt 399 = memoRow_399 := by
  have he : entryAt 399 = entry_399 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 399 < 6 by decide, ↓reduceDIte, he, entry_399, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_173, memoRow_eq_192, memoRow_eq_215, memoRow_eq_271, memoRow_eq_319]
  apply rowData_ext <;> decide +kernel


def memoRow_400 : RowData := ⟨{(-1, -2), (-1, 0), (1, -2), (1, 0)}, {(-5, -1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_400 : rowAt 400 = memoRow_400 := by
  have he : entryAt 400 = entry_400 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 400 < 6 by decide, ↓reduceDIte, he, entry_400, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_176, memoRow_eq_197, memoRow_eq_245, memoRow_eq_252, memoRow_eq_283]
  apply rowData_ext <;> decide +kernel


def memoRow_401 : RowData := ⟨{(-1, -1), (0, -1), (0, 1)}, {(-4, 0), (-4, 2), (-3, 0), (-3, 1), (-3, 2), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0)}, 11⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_401 : rowAt 401 = memoRow_401 := by
  have he : entryAt 401 = entry_401 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 401 < 6 by decide, ↓reduceDIte, he, entry_401, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_24, memoRow_eq_286, memoRow_eq_319, memoRow_eq_364]
  apply rowData_ext <;> decide +kernel


def memoRow_402 : RowData := ⟨{(-1, -3), (0, -3), (0, -2), (1, -3), (2, -3), (2, 0)}, {(-3, 1), (-2, -4), (-2, 0), (-2, 1), (-1, -4), (-1, -3), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -3), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1)}, 12⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_402 : rowAt 402 = memoRow_402 := by
  have he : entryAt 402 = entry_402 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 402 < 6 by decide, ↓reduceDIte, he, entry_402, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_29, memoRow_eq_384]
  apply rowData_ext <;> decide +kernel


def memoRow_403 : RowData := ⟨{(-1, -2), (0, -3), (0, -2), (0, -1)}, {(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)}, 12⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_403 : rowAt 403 = memoRow_403 := by
  have he : entryAt 403 = entry_403 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 403 < 6 by decide, ↓reduceDIte, he, entry_403, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_63, memoRow_eq_180, memoRow_eq_202, memoRow_eq_314, memoRow_eq_388]
  apply rowData_ext <;> decide +kernel


def memoRow_404 : RowData := ⟨{(-1, -1), (-1, 0), (-1, 1), (-1, 2)}, {(-6, 1), (-5, 1), (-5, 2), (-5, 3), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (4, 1), (4, 3)}, 12⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_404 : rowAt 404 = memoRow_404 := by
  have he : entryAt 404 = entry_404 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 404 < 6 by decide, ↓reduceDIte, he, entry_404, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_82, memoRow_eq_388]
  apply rowData_ext <;> decide +kernel


def memoRow_405 : RowData := ⟨{(-2, -2), (-1, -3), (-1, -2), (0, -3), (0, -2), (1, -3)}, {(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (2, 1), (3, -2), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)}, 13⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_405 : rowAt 405 = memoRow_405 := by
  have he : entryAt 405 = entry_405 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 405 < 6 by decide, ↓reduceDIte, he, entry_405, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_42, memoRow_eq_301, memoRow_eq_391]
  apply rowData_ext <;> decide +kernel


def memoRow_406 : RowData := ⟨{(0, -2), (0, -1)}, {(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -5), (-1, -4), (-1, -3), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (2, 2), (3, -1), (3, 0), (3, 1), (3, 2), (4, -1), (4, 0), (4, 1), (4, 2), (5, -1)}, 11⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_406 : rowAt 406 = memoRow_406 := by
  have he : entryAt 406 = entry_406 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 406 < 6 by decide, ↓reduceDIte, he, entry_406, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_172, memoRow_eq_176, memoRow_eq_197, memoRow_eq_236, memoRow_eq_245, memoRow_eq_295, memoRow_eq_364]
  apply rowData_ext <;> decide +kernel


def memoRow_407 : RowData := ⟨{(0, 1), (0, 2), (0, 3)}, {(-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 3), (-2, -1), (-2, 0), (-2, 1), (-2, 3), (-1, -1), (-1, 0), (-1, 1), (-1, 3), (-1, 4), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 1), (4, 2), (4, 3), (4, 4), (5, 2)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_407 : rowAt 407 = memoRow_407 := by
  have he : entryAt 407 = entry_407 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 407 < 6 by decide, ↓reduceDIte, he, entry_407, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_285, memoRow_eq_314]
  apply rowData_ext <;> decide +kernel


def memoRow_408 : RowData := ⟨{(-1, 0), (0, -3), (0, -2), (0, -1), (1, 0)}, {(-5, -1), (-4, -1), (-4, 0), (-4, 1), (-3, -3), (-3, -1), (-3, 0), (-3, 1), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (5, -1)}, 11⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_408 : rowAt 408 = memoRow_408 := by
  have he : entryAt 408 = entry_408 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 408 < 6 by decide, ↓reduceDIte, he, entry_408, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_223, memoRow_eq_229, memoRow_eq_357]
  apply rowData_ext <;> decide +kernel


def memoRow_409 : RowData := ⟨{(0, -3), (0, -2), (1, -3), (2, -1), (2, 0)}, {(-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1)}, 12⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_409 : rowAt 409 = memoRow_409 := by
  have he : entryAt 409 = entry_409 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 409 < 6 by decide, ↓reduceDIte, he, entry_409, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_110, memoRow_eq_133, memoRow_eq_136, memoRow_eq_384]
  apply rowData_ext <;> decide +kernel


def memoRow_410 : RowData := ⟨{(-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1)}, {(-6, 2), (-6, 4), (-5, 2), (-5, 3), (-5, 4), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (2, 3), (2, 4), (3, 2), (3, 3), (3, 4), (4, 2)}, 14⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_410 : rowAt 410 = memoRow_410 := by
  have he : entryAt 410 = entry_410 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 410 < 6 by decide, ↓reduceDIte, he, entry_410, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_405]
  apply rowData_ext <;> decide +kernel


def memoRow_411 : RowData := ⟨{(1, 0), (2, 0)}, {(-3, -1), (-2, -1), (-2, 0), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (7, 1), (7, 3)}, 14⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_411 : rowAt 411 = memoRow_411 := by
  have he : entryAt 411 = entry_411 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 411 < 6 by decide, ↓reduceDIte, he, entry_411, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_173, memoRow_eq_246, memoRow_eq_252, memoRow_eq_263, memoRow_eq_300, memoRow_eq_379]
  apply rowData_ext <;> decide +kernel


def memoRow_412 : RowData := ⟨{(-3, -1), (-2, -1), (-1, -1), (-1, 0), (-1, 1)}, {(-6, 1), (-5, 1), (-5, 2), (-5, 3), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (4, 1), (4, 3)}, 13⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_412 : rowAt 412 = memoRow_412 := by
  have he : entryAt 412 = entry_412 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 412 < 6 by decide, ↓reduceDIte, he, entry_412, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_403]
  apply rowData_ext <;> decide +kernel


def memoRow_413 : RowData := ⟨{(-1, -2), (-1, -1), (-1, 1), (0, 1), (0, 2)}, {(-5, 2), (-5, 4), (-4, 2), (-4, 3), (-4, 4), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 2), (2, 3), (2, 4), (3, 2), (3, 3), (3, 4), (4, 2), (4, 3), (4, 4), (5, 2)}, 13⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_413 : rowAt 413 = memoRow_413 := by
  have he : entryAt 413 = entry_413 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 413 < 6 by decide, ↓reduceDIte, he, entry_413, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_3, memoRow_eq_403]
  apply rowData_ext <;> decide +kernel


def memoRow_414 : RowData := ⟨{(-1, -1), (-1, 1), (0, -1), (0, 1)}, {(-5, 0), (-5, 2), (-4, 0), (-4, 1), (-4, 2), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, -2), (2, 0), (2, 1), (2, 2), (3, -2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0)}, 11⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_414 : rowAt 414 = memoRow_414 := by
  have he : entryAt 414 = entry_414 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 414 < 6 by decide, ↓reduceDIte, he, entry_414, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_185, memoRow_eq_199, memoRow_eq_374]
  apply rowData_ext <;> decide +kernel


def memoRow_415 : RowData := ⟨{(-3, -3), (-2, -3), (-2, 0), (-1, -3), (0, -3)}, {(-5, 1), (-4, 0), (-4, 1), (-3, -3), (-3, 0), (-3, 1), (-2, -3), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -4), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1)}, 12⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_415 : rowAt 415 = memoRow_415 := by
  have he : entryAt 415 = entry_415 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 415 < 6 by decide, ↓reduceDIte, he, entry_415, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_164, memoRow_eq_177, memoRow_eq_205, memoRow_eq_371, memoRow_eq_384]
  apply rowData_ext <;> decide +kernel


def memoRow_416 : RowData := ⟨{(-2, 0), (-1, 0)}, {(-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (4, 1)}, 16⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_416 : rowAt 416 = memoRow_416 := by
  have he : entryAt 416 = entry_416 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 416 < 6 by decide, ↓reduceDIte, he, entry_416, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_176, memoRow_eq_197, memoRow_eq_220, memoRow_eq_245, memoRow_eq_295, memoRow_eq_385]
  apply rowData_ext <;> decide +kernel


def memoRow_417 : RowData := ⟨{(-2, -3), (-2, -2), (-1, -3), (0, -3), (0, -1), (1, -3)}, {(-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1)}, 13⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_417 : rowAt 417 = memoRow_417 := by
  have he : entryAt 417 = entry_417 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 417 < 6 by decide, ↓reduceDIte, he, entry_417, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_11, memoRow_eq_270, memoRow_eq_409]
  apply rowData_ext <;> decide +kernel


def memoRow_418 : RowData := ⟨{(-2, -1), (-1, -4), (-1, -3), (-1, -1), (0, -1)}, {(-5, 0), (-5, 2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0)}, 14⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_418 : rowAt 418 = memoRow_418 := by
  have he : entryAt 418 = entry_418 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 418 < 6 by decide, ↓reduceDIte, he, entry_418, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_62, memoRow_eq_68, memoRow_eq_147, memoRow_eq_413]
  apply rowData_ext <;> decide +kernel


def memoRow_419 : RowData := ⟨{(-3, -3), (-2, -3), (-2, -2), (-1, -3), (0, -3)}, {(-5, 1), (-4, -4), (-4, 0), (-4, 1), (-3, -4), (-3, -3), (-3, -1), (-3, 0), (-3, 1), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1)}, 13⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_419 : rowAt 419 = memoRow_419 := by
  have he : entryAt 419 = entry_419 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 419 < 6 by decide, ↓reduceDIte, he, entry_419, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_164, memoRow_eq_243, memoRow_eq_253, memoRow_eq_377, memoRow_eq_402]
  apply rowData_ext <;> decide +kernel


def memoRow_420 : RowData := ⟨{(-1, -3), (0, -3), (0, -2), (1, -3), (2, -3)}, {(-3, 1), (-2, -4), (-2, 0), (-2, 1), (-1, -4), (-1, -3), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -4), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1)}, 13⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_420 : rowAt 420 = memoRow_420 := by
  have he : entryAt 420 = entry_420 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 420 < 6 by decide, ↓reduceDIte, he, entry_420, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_29, memoRow_eq_415]
  apply rowData_ext <;> decide +kernel


def memoRow_421 : RowData := ⟨{(-1, -2), (-1, -1), (-1, 0), (1, 0)}, {(-6, 1), (-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 2), (2, 3), (2, 4), (3, -3), (3, -2), (3, -1), (4, -3), (4, -2), (4, -1), (5, -3), (5, -1)}, 12⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_421 : rowAt 421 = memoRow_421 := by
  have he : entryAt 421 = entry_421 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 421 < 6 by decide, ↓reduceDIte, he, entry_421, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_24, memoRow_eq_25, memoRow_eq_241, memoRow_eq_397]
  apply rowData_ext <;> decide +kernel


def memoRow_422 : RowData := ⟨{(-1, -1), (-1, 0), (-1, 1), (-1, 2)}, {(-4, -1), (-3, -1), (-2, -2), (-2, -1), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 1), (5, 2), (5, 3), (5, 4), (6, 1), (6, 2), (6, 3), (6, 4)}, 14⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_422 : rowAt 422 = memoRow_422 := by
  have he : entryAt 422 = entry_422 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 422 < 6 by decide, ↓reduceDIte, he, entry_422, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_45, memoRow_eq_106, memoRow_eq_419]
  apply rowData_ext <;> decide +kernel


def memoRow_423 : RowData := ⟨{(-1, -2), (-1, 0), (0, -2)}, {(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 1)}, 12⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_423 : rowAt 423 = memoRow_423 := by
  have he : entryAt 423 = entry_423 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 423 < 6 by decide, ↓reduceDIte, he, entry_423, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_226, memoRow_eq_378, memoRow_eq_386]
  apply rowData_ext <;> decide +kernel


def memoRow_424 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (2, -1)}, {(-5, -2), (-5, -1), (-5, 0), (-5, 1), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (3, -1), (3, 0), (4, -2), (4, -1), (4, 0), (4, 1), (5, -2), (5, -1), (5, 0), (5, 1), (6, -2), (6, -1), (6, 0), (6, 1), (7, -2), (7, -1), (7, 0), (7, 1)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_424 : rowAt 424 = memoRow_424 := by
  have he : entryAt 424 = entry_424 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 424 < 6 by decide, ↓reduceDIte, he, entry_424, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_55, memoRow_eq_216, memoRow_eq_394]
  apply rowData_ext <;> decide +kernel


def memoRow_425 : RowData := ⟨{(-1, -2), (-1, 0), (0, -2)}, {(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 1)}, 12⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_425 : rowAt 425 = memoRow_425 := by
  have he : entryAt 425 = entry_425 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 425 < 6 by decide, ↓reduceDIte, he, entry_425, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_226, memoRow_eq_378, memoRow_eq_386]
  apply rowData_ext <;> decide +kernel


def memoRow_426 : RowData := ⟨{(-1, -2), (0, -2), (0, -1)}, {(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (4, -1), (4, 0), (4, 1), (4, 2), (5, -1), (5, 0)}, 12⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_426 : rowAt 426 = memoRow_426 := by
  have he : entryAt 426 = entry_426 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 426 < 6 by decide, ↓reduceDIte, he, entry_426, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_252, memoRow_eq_291, memoRow_eq_300, memoRow_eq_319, memoRow_eq_328, memoRow_eq_397]
  apply rowData_ext <;> decide +kernel


def memoRow_427 : RowData := ⟨{(-1, -1), (-1, 0), (-1, 1), (-1, 2)}, {(-4, -1), (-3, -1), (-2, -2), (-2, -1), (-2, 1), (-2, 3), (-2, 4), (-2, 5), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 1), (5, 2), (5, 3), (5, 4), (6, 1), (6, 2), (6, 3), (6, 4)}, 14⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_427 : rowAt 427 = memoRow_427 := by
  have he : entryAt 427 = entry_427 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 427 < 6 by decide, ↓reduceDIte, he, entry_427, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_45, memoRow_eq_106, memoRow_eq_420]
  apply rowData_ext <;> decide +kernel


def memoRow_428 : RowData := ⟨{(-1, -3), (-1, -2), (-1, 0), (0, -3), (0, -2)}, {(-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (5, -1), (5, 1)}, 17⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_428 : rowAt 428 = memoRow_428 := by
  have he : entryAt 428 = entry_428 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 428 < 6 by decide, ↓reduceDIte, he, entry_428, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_26, memoRow_eq_244, memoRow_eq_329, memoRow_eq_416]
  apply rowData_ext <;> decide +kernel


def memoRow_429 : RowData := ⟨{(0, 2), (1, -1), (1, 0), (2, 0), (3, 0)}, {(-2, 0), (-1, 0), (-1, 1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (4, 0), (4, 1), (5, 0), (5, 1)}, 6⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_429 : rowAt 429 = memoRow_429 := by
  have he : entryAt 429 = entry_429 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 429 < 6 by decide, ↓reduceDIte, he, entry_429, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_28, memoRow_eq_128]
  apply rowData_ext <;> decide +kernel


def memoRow_430 : RowData := ⟨{(-2, -2), (-2, -1), (-2, 0), (-1, -2), (0, -2)}, {(-7, -1), (-7, 1), (-6, -1), (-6, 0), (-6, 1), (-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -3), (2, -1), (2, 0), (2, 1), (3, -3), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_430 : rowAt 430 = memoRow_430 := by
  have he : entryAt 430 = entry_430 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 430 < 6 by decide, ↓reduceDIte, he, entry_430, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_277, memoRow_eq_336, memoRow_eq_338, memoRow_eq_375]
  apply rowData_ext <;> decide +kernel


def memoRow_431 : RowData := ⟨{(-1, -4), (-1, -3), (-1, -2), (0, -3), (1, -3), (2, -3)}, {(-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -3), (0, -1), (0, 0), (0, 1), (0, 2), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (6, -2), (6, -1), (6, 0), (6, 1)}, 13⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_431 : rowAt 431 = memoRow_431 := by
  have he : entryAt 431 = entry_431 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 431 < 6 by decide, ↓reduceDIte, he, entry_431, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_73, memoRow_eq_302, memoRow_eq_398, memoRow_eq_415]
  apply rowData_ext <;> decide +kernel


def memoRow_432 : RowData := ⟨{(-1, -3), (0, -3), (0, -2), (1, -3), (1, -2)}, {(-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (6, -1), (6, 1)}, 18⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_432 : rowAt 432 = memoRow_432 := by
  have he : entryAt 432 = entry_432 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 432 < 6 by decide, ↓reduceDIte, he, entry_432, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_42, memoRow_eq_274, memoRow_eq_428]
  apply rowData_ext <;> decide +kernel


def memoRow_433 : RowData := ⟨{(0, -4), (0, -3), (0, -2), (0, -1)}, {(-3, -3), (-2, -3), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (6, -1), (6, 0), (6, 1), (6, 2), (7, -1), (7, 0), (7, 1), (7, 2)}, 15⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_433 : rowAt 433 = memoRow_433 := by
  have he : entryAt 433 = entry_433 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 433 < 6 by decide, ↓reduceDIte, he, entry_433, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_7, memoRow_eq_63, memoRow_eq_422, memoRow_eq_427]
  apply rowData_ext <;> decide +kernel


def memoRow_434 : RowData := ⟨{(-2, 0), (-1, -3), (-1, -2), (-1, 0), (0, -2)}, {(-5, 1), (-5, 3), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, 1)}, 15⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_434 : rowAt 434 = memoRow_434 := by
  have he : entryAt 434 = entry_434 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 434 < 6 by decide, ↓reduceDIte, he, entry_434, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_116, memoRow_eq_176, memoRow_eq_263, memoRow_eq_295, memoRow_eq_418]
  apply rowData_ext <;> decide +kernel


def memoRow_435 : RowData := ⟨{(0, -2), (0, -1), (1, -1), (2, -1), (3, -1)}, {(-2, 3), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 1), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (7, 0), (7, 1), (7, 2), (7, 3)}, 14⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_435 : rowAt 435 = memoRow_435 := by
  have he : entryAt 435 = entry_435 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 435 < 6 by decide, ↓reduceDIte, he, entry_435, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_431]
  apply rowData_ext <;> decide +kernel


def memoRow_436 : RowData := ⟨{(0, -3), (0, -2), (1, -3), (1, -2)}, {(-4, -1), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (6, -1), (6, 1)}, 18⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_436 : rowAt 436 = memoRow_436 := by
  have he : entryAt 436 = entry_436 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 436 < 6 by decide, ↓reduceDIte, he, entry_436, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_51, memoRow_eq_60, memoRow_eq_274, memoRow_eq_428]
  apply rowData_ext <;> decide +kernel


def memoRow_437 : RowData := ⟨{(0, -3), (0, -2), (0, -1)}, {(-3, -3), (-2, -3), (-1, -5), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (6, -1), (6, 0), (6, 1), (6, 2), (7, -1), (7, 0), (7, 1), (7, 2)}, 15⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_437 : rowAt 437 = memoRow_437 := by
  have he : entryAt 437 = entry_437 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 437 < 6 by decide, ↓reduceDIte, he, entry_437, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_55, memoRow_eq_63, memoRow_eq_422, memoRow_eq_427]
  apply rowData_ext <;> decide +kernel


def memoRow_438 : RowData := ⟨{(-2, -1), (-1, -1), (0, -1), (1, -1), (1, 0)}, {(-3, -1), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 3), (6, 1), (6, 3)}, 19⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_438 : rowAt 438 = memoRow_438 := by
  have he : entryAt 438 = entry_438 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 438 < 6 by decide, ↓reduceDIte, he, entry_438, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_432]
  apply rowData_ext <;> decide +kernel


def memoRow_439 : RowData := ⟨{(-2, 0), (-1, -4), (-1, -3), (-1, -2), (-1, 0)}, {(-5, 1), (-5, 3), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, 1)}, 15⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_439 : rowAt 439 = memoRow_439 := by
  have he : entryAt 439 = entry_439 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 439 < 6 by decide, ↓reduceDIte, he, entry_439, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_149, memoRow_eq_176, memoRow_eq_263, memoRow_eq_295, memoRow_eq_418]
  apply rowData_ext <;> decide +kernel


def memoRow_440 : RowData := ⟨{(-2, -1), (-2, 0), (-1, 0), (1, 0)}, {(-4, 4), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 1), (5, 2), (5, 3), (5, 4)}, 15⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_440 : rowAt 440 = memoRow_440 := by
  have he : entryAt 440 = entry_440 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 440 < 6 by decide, ↓reduceDIte, he, entry_440, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_435]
  apply rowData_ext <;> decide +kernel


def memoRow_441 : RowData := ⟨{(0, 1), (1, 1), (2, 1), (3, 1)}, {(-2, 5), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 1), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, 2), (7, 3), (7, 4), (7, 5)}, 15⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_441 : rowAt 441 = memoRow_441 := by
  have he : entryAt 441 = entry_441 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 441 < 6 by decide, ↓reduceDIte, he, entry_441, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_435]
  apply rowData_ext <;> decide +kernel


def memoRow_442 : RowData := ⟨{(0, -4), (0, -3), (0, -2), (0, -1)}, {(-3, -2), (-2, -2), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, 0), (6, 1), (6, 2), (6, 3), (7, 0), (7, 1), (7, 2), (7, 3)}, 16⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_442 : rowAt 442 = memoRow_442 := by
  have he : entryAt 442 = entry_442 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 442 < 6 by decide, ↓reduceDIte, he, entry_442, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_7, memoRow_eq_63, memoRow_eq_201, memoRow_eq_433]
  apply rowData_ext <;> decide +kernel


def memoRow_443 : RowData := ⟨{(-3, -1), (-2, -1), (-1, -1), (0, -1)}, {(-4, -1), (-4, 1), (-4, 2), (-4, 3), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-2, -2), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2), (4, 3), (5, 1), (5, 3)}, 20⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_443 : rowAt 443 = memoRow_443 := by
  have he : entryAt 443 = entry_443 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 443 < 6 by decide, ↓reduceDIte, he, entry_443, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_438]
  apply rowData_ext <;> decide +kernel


def memoRow_444 : RowData := ⟨{(-2, -2), (-1, -2), (0, -2), (0, -1)}, {(-5, -3), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -2), (-2, 0), (-2, 1), (-2, 2), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (5, 0), (5, 2)}, 14⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_444 : rowAt 444 = memoRow_444 := by
  have he : entryAt 444 = entry_444 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 444 < 6 by decide, ↓reduceDIte, he, entry_444, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_142, memoRow_eq_160, memoRow_eq_194, memoRow_eq_236, memoRow_eq_353, memoRow_eq_412]
  apply rowData_ext <;> decide +kernel


def memoRow_445 : RowData := ⟨{(1, 0), (1, 1), (2, 0), (2, 1)}, {(-2, 0), (-2, 2), (-2, 3), (-2, 4), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, -1), (0, 0), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (7, 2), (7, 4)}, 19⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_445 : rowAt 445 = memoRow_445 := by
  have he : entryAt 445 = entry_445 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 445 < 6 by decide, ↓reduceDIte, he, entry_445, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_9, memoRow_eq_432]
  apply rowData_ext <;> decide +kernel


def memoRow_446 : RowData := ⟨{(-1, -1), (1, 0), (2, 0), (3, 0), (3, 1)}, {(-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 2), (7, 3), (7, 4), (8, 2), (8, 4)}, 20⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_446 : rowAt 446 = memoRow_446 := by
  have he : entryAt 446 = entry_446 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 446 < 6 by decide, ↓reduceDIte, he, entry_446, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_4, memoRow_eq_438]
  apply rowData_ext <;> decide +kernel


def memoRow_447 : RowData := ⟨{(-3, -1), (-2, -1), (-1, -1), (-1, 0), (0, -1)}, {(-6, 1), (-6, 3), (-5, 1), (-5, 2), (-5, 3), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (4, 1), (4, 3)}, 19⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_447 : rowAt 447 = memoRow_447 := by
  have he : entryAt 447 = entry_447 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 447 < 6 by decide, ↓reduceDIte, he, entry_447, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_436]
  apply rowData_ext <;> decide +kernel


def memoRow_448 : RowData := ⟨{(-2, -1), (-1, -1), (-1, 0), (0, -1)}, {(-5, 1), (-5, 3), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2), (4, 3), (5, 1), (5, 3)}, 19⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_448 : rowAt 448 = memoRow_448 := by
  have he : entryAt 448 = entry_448 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 448 < 6 by decide, ↓reduceDIte, he, entry_448, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_9, memoRow_eq_436]
  apply rowData_ext <;> decide +kernel


def memoRow_449 : RowData := ⟨{(-1, -3), (-1, -2), (-1, 0), (0, -4), (0, -3), (0, -2)}, {(-4, 1), (-4, 3), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, 1)}, 16⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_449 : rowAt 449 = memoRow_449 := by
  have he : entryAt 449 = entry_449 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 449 < 6 by decide, ↓reduceDIte, he, entry_449, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_26, memoRow_eq_244, memoRow_eq_307, memoRow_eq_439]
  apply rowData_ext <;> decide +kernel


def memoRow_450 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, 0), (3, 0)}, {(-2, 4), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, 1), (7, 2), (7, 3), (7, 4)}, 16⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_450 : rowAt 450 = memoRow_450 := by
  have he : entryAt 450 = entry_450 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 450 < 6 by decide, ↓reduceDIte, he, entry_450, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_440]
  apply rowData_ext <;> decide +kernel


def memoRow_451 : RowData := ⟨{(0, -3), (0, -2), (1, -4), (1, -3), (1, -2)}, {(-3, 1), (-3, 3), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (7, 1)}, 17⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_451 : rowAt 451 = memoRow_451 := by
  have he : entryAt 451 = entry_451 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 451 < 6 by decide, ↓reduceDIte, he, entry_451, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_1, memoRow_eq_449]
  apply rowData_ext <;> decide +kernel


def memoRow_452 : RowData := ⟨{(-1, 1), (-1, 2), (0, 1), (0, 2), (1, 2)}, {(-4, 5), (-4, 7), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 5)}, 18⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_452 : rowAt 452 = memoRow_452 := by
  have he : entryAt 452 = entry_452 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 452 < 6 by decide, ↓reduceDIte, he, entry_452, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_24, memoRow_eq_25, memoRow_eq_451]
  apply rowData_ext <;> decide +kernel


def memoRow_453 : RowData := ⟨{(-1, -2), (-1, 0), (0, -2)}, {(-6, -1), (-5, -1), (-5, 0), (-5, 1), (-4, -3), (-4, -1), (-4, 0), (-4, 1), (-3, -3), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -7), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -7), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)}, 12⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_453 : rowAt 453 = memoRow_453 := by
  have he : entryAt 453 = entry_453 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 453 < 6 by decide, ↓reduceDIte, he, entry_453, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_226, memoRow_eq_359, memoRow_eq_386, memoRow_eq_389, memoRow_eq_414]
  apply rowData_ext <;> decide +kernel


def memoRow_454 : RowData := ⟨{(-2, -1), (-1, -1), (-1, 0), (0, -1), (1, -1)}, {(-5, 1), (-5, 3), (-4, 1), (-4, 2), (-4, 3), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2), (4, 3), (5, 1), (5, 3)}, 19⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_454 : rowAt 454 = memoRow_454 := by
  have he : entryAt 454 = entry_454 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 454 < 6 by decide, ↓reduceDIte, he, entry_454, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_58, memoRow_eq_436]
  apply rowData_ext <;> decide +kernel


def memoRow_455 : RowData := ⟨{(-3, -1), (-3, 0), (-3, 1), (-2, 1), (-1, 1)}, {(-5, 2), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, 0), (2, 0)}, 5⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_455 : rowAt 455 = memoRow_455 := by
  have he : entryAt 455 = entry_455 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 455 < 6 by decide, ↓reduceDIte, he, entry_455, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_20, memoRow_eq_39, memoRow_eq_118]
  apply rowData_ext <;> decide +kernel


def memoRow_456 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-4, 1), (-4, 3), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 1)}, 12⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_456 : rowAt 456 = memoRow_456 := by
  have he : entryAt 456 = entry_456 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 456 < 6 by decide, ↓reduceDIte, he, entry_456, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_55, memoRow_eq_63, memoRow_eq_64, memoRow_eq_308]
  apply rowData_ext <;> decide +kernel


def memoRow_457 : RowData := ⟨{(-1, -3), (-1, -1), (0, -1), (1, -1), (2, -1)}, {(-4, 1), (-4, 3), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 3), (6, 1), (6, 3)}, 20⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_457 : rowAt 457 = memoRow_457 := by
  have he : entryAt 457 = entry_457 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 457 < 6 by decide, ↓reduceDIte, he, entry_457, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_28, memoRow_eq_454]
  apply rowData_ext <;> decide +kernel


def memoRow_458 : RowData := ⟨{(-3, -3), (-3, -2), (-3, -1), (-2, -3), (-2, 0), (-1, -3), (0, -3)}, {(-5, 4), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -3), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 1), (4, 2), (4, 3), (4, 4)}, 17⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_458 : rowAt 458 = memoRow_458 := by
  have he : entryAt 458 = entry_458 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 458 < 6 by decide, ↓reduceDIte, he, entry_458, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_130, memoRow_eq_177, memoRow_eq_450]
  apply rowData_ext <;> decide +kernel


def memoRow_459 : RowData := ⟨{(-1, -1), (0, -2), (0, -1), (1, -1), (2, -1)}, {(-4, 1), (-4, 3), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -2), (3, -1), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -2), (4, -1), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, -2), (5, 1), (5, 2), (5, 3), (6, 1), (6, 3)}, 20⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_459 : rowAt 459 = memoRow_459 := by
  have he : entryAt 459 = entry_459 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 459 < 6 by decide, ↓reduceDIte, he, entry_459, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_65, memoRow_eq_97, memoRow_eq_448]
  apply rowData_ext <;> decide +kernel


def memoRow_460 : RowData := ⟨{(-2, 0), (-1, 0)}, {(-5, 1), (-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1)}, 11⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_460 : rowAt 460 = memoRow_460 := by
  have he : entryAt 460 = entry_460 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 460 < 6 by decide, ↓reduceDIte, he, entry_460, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_173, memoRow_eq_183, memoRow_eq_220, memoRow_eq_246, memoRow_eq_263, memoRow_eq_282, memoRow_eq_295]
  apply rowData_ext <;> decide +kernel


def memoRow_461 : RowData := ⟨{(-1, -4), (-1, -3), (-1, -2), (-1, -1), (0, -3), (1, -3), (2, -3)}, {(-3, 4), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, 1), (6, 2), (6, 3), (6, 4)}, 18⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_461 : rowAt 461 = memoRow_461 := by
  have he : entryAt 461 = entry_461 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 461 < 6 by decide, ↓reduceDIte, he, entry_461, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_4, memoRow_eq_458]
  apply rowData_ext <;> decide +kernel


def memoRow_462 : RowData := ⟨{(-2, -1), (-2, 0), (-1, -1), (-1, 0)}, {(-5, 3), (-5, 5), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 3)}, 19⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_462 : rowAt 462 = memoRow_462 := by
  have he : entryAt 462 = entry_462 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 462 < 6 by decide, ↓reduceDIte, he, entry_462, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_86, memoRow_eq_328, memoRow_eq_452]
  apply rowData_ext <;> decide +kernel


def memoRow_463 : RowData := ⟨{(-2, -2), (-2, -1), (-1, -3), (-1, -1), (0, -1), (1, -1)}, {(-5, 1), (-5, 3), (-4, 1), (-4, 2), (-4, 3), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, -2), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -3), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, -2), (2, -1), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0), (5, 1), (5, 3)}, 20⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_463 : rowAt 463 = memoRow_463 := by
  have he : entryAt 463 = entry_463 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 463 < 6 by decide, ↓reduceDIte, he, entry_463, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_76, memoRow_eq_170, memoRow_eq_447]
  apply rowData_ext <;> decide +kernel


def memoRow_464 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, -2), (2, -2), (3, -2)}, {(-2, 5), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, 2), (7, 3), (7, 4), (7, 5)}, 19⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_464 : rowAt 464 = memoRow_464 := by
  have he : entryAt 464 = entry_464 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 464 < 6 by decide, ↓reduceDIte, he, entry_464, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_63, memoRow_eq_224, memoRow_eq_306, memoRow_eq_315, memoRow_eq_358, memoRow_eq_461]
  apply rowData_ext <;> decide +kernel


def memoRow_465 : RowData := ⟨{(0, -3), (0, -2), (0, -1)}, {(-3, 0), (-2, 0), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_465 : rowAt 465 = memoRow_465 := by
  have he : entryAt 465 = entry_465 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 465 < 6 by decide, ↓reduceDIte, he, entry_465, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_55, memoRow_eq_64, memoRow_eq_285]
  apply rowData_ext <;> decide +kernel


def memoRow_466 : RowData := ⟨{(-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -2)}, {(-7, -1), (-7, 0), (-7, 1), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -1), (-3, 0), (-3, 1), (-3, 3), (-3, 4), (-3, 5), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (4, -1), (4, 0), (4, 1), (4, 2), (5, -1), (5, 0), (5, 1), (5, 2)}, 14⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_466 : rowAt 466 = memoRow_466 := by
  have he : entryAt 466 = entry_466 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 466 < 6 by decide, ↓reduceDIte, he, entry_466, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_324, memoRow_eq_325, memoRow_eq_360, memoRow_eq_395, memoRow_eq_417]
  apply rowData_ext <;> decide +kernel


def memoRow_467 : RowData := ⟨{(0, 1), (0, 2), (0, 3)}, {(-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (8, 0), (8, 1), (8, 2), (9, 0), (9, 2)}, 21⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_467 : rowAt 467 = memoRow_467 := by
  have he : entryAt 467 = entry_467 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 467 < 6 by decide, ↓reduceDIte, he, entry_467, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_64, memoRow_eq_314, memoRow_eq_443]
  apply rowData_ext <;> decide +kernel


def memoRow_468 : RowData := ⟨{(0, 1), (0, 2), (1, 1), (2, 1), (3, 1)}, {(-2, 8), (-1, 0), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, 1), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, 5), (7, 6), (7, 7), (7, 8)}, 20⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_468 : rowAt 468 = memoRow_468 := by
  have he : entryAt 468 = entry_468 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 468 < 6 by decide, ↓reduceDIte, he, entry_468, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_464]
  apply rowData_ext <;> decide +kernel


def memoRow_469 : RowData := ⟨{(0, 1), (0, 2), (0, 3)}, {(-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (8, 0), (8, 1), (8, 2), (9, 0), (9, 2)}, 21⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_469 : rowAt 469 = memoRow_469 := by
  have he : entryAt 469 = entry_469 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 469 < 6 by decide, ↓reduceDIte, he, entry_469, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_55, memoRow_eq_314, memoRow_eq_443]
  apply rowData_ext <;> decide +kernel


def memoRow_470 : RowData := ⟨{(0, -1), (1, -1), (2, -1), (3, -1)}, {(-2, 6), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -1), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, 3), (7, 4), (7, 5), (7, 6)}, 21⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_470 : rowAt 470 = memoRow_470 := by
  have he : entryAt 470 = entry_470 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 470 < 6 by decide, ↓reduceDIte, he, entry_470, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_468]
  apply rowData_ext <;> decide +kernel


def memoRow_471 : RowData := ⟨{(-1, 0), (-1, 1), (-1, 2), (-1, 3)}, {(-6, 1), (-6, 2), (-6, 3), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, 1), (-2, 2), (-2, 3), (-2, 5), (-2, 6), (-2, 7), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -1), (0, 0), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 1), (5, 2), (5, 3), (5, 4), (6, 1), (6, 2), (6, 3), (6, 4)}, 15⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_471 : rowAt 471 = memoRow_471 := by
  have he : entryAt 471 = entry_471 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 471 < 6 by decide, ↓reduceDIte, he, entry_471, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_466]
  apply rowData_ext <;> decide +kernel


def memoRow_472 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, -3)}, {(-5, -2), (-5, -1), (-5, 0), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (6, -2), (6, -1), (6, 0), (6, 1), (7, -2), (7, -1), (7, 0), (7, 1)}, 15⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_472 : rowAt 472 = memoRow_472 := by
  have he : entryAt 472 = entry_472 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 472 < 6 by decide, ↓reduceDIte, he, entry_472, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_466]
  apply rowData_ext <;> decide +kernel


def memoRow_473 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0), (-1, 1), (0, 1)}, {(-6, 2), (-6, 4), (-5, 2), (-5, 3), (-5, 4), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, 0), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, -1), (2, 0), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 0), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (5, 2), (5, 4)}, 20⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_473 : rowAt 473 = memoRow_473 := by
  have he : entryAt 473 = entry_473 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 473 < 6 by decide, ↓reduceDIte, he, entry_473, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_121, memoRow_eq_436, memoRow_eq_445]
  apply rowData_ext <;> decide +kernel


def memoRow_474 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, -2), (1, 0), (2, 0), (3, 0)}, {(-3, 2), (-3, 4), (-2, 2), (-2, 3), (-2, 4), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, -1), (4, 0), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, 1), (7, 2), (7, 4)}, 21⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_474 : rowAt 474 = memoRow_474 := by
  have he : entryAt 474 = entry_474 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 474 < 6 by decide, ↓reduceDIte, he, entry_474, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_70, memoRow_eq_83, memoRow_eq_463]
  apply rowData_ext <;> decide +kernel


def memoRow_475 : RowData := ⟨{(-3, -2), (-3, 0), (-2, 0), (-1, 0)}, {(-6, 2), (-6, 4), (-5, 2), (-5, 3), (-5, 4), (-4, -1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 1), (4, 2), (4, 4)}, 21⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_475 : rowAt 475 = memoRow_475 := by
  have he : entryAt 475 = entry_475 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 475 < 6 by decide, ↓reduceDIte, he, entry_475, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_63, memoRow_eq_261, memoRow_eq_269, memoRow_eq_457]
  apply rowData_ext <;> decide +kernel


def memoRow_476 : RowData := ⟨{(-2, -1), (-1, -1), (0, -1), (1, 0)}, {(-5, 1), (-5, 3), (-4, 1), (-4, 2), (-4, 3), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, -2), (2, -1), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -2), (3, -1), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, -1), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 3), (6, 1), (6, 3)}, 21⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_476 : rowAt 476 = memoRow_476 := by
  have he : entryAt 476 = entry_476 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 476 < 6 by decide, ↓reduceDIte, he, entry_476, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_473]
  apply rowData_ext <;> decide +kernel


def memoRow_477 : RowData := ⟨{(0, -3), (0, -2), (0, -1)}, {(-5, -3), (-5, -2), (-5, -1), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-1, -7), (-1, -6), (-1, -5), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (6, -4), (6, -3), (6, -2), (6, -1), (7, -4), (7, -3), (7, -2), (7, -1)}, 16⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_477 : rowAt 477 = memoRow_477 := by
  have he : entryAt 477 = entry_477 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 477 < 6 by decide, ↓reduceDIte, he, entry_477, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_55, memoRow_eq_154, memoRow_eq_471]
  apply rowData_ext <;> decide +kernel


def memoRow_478 : RowData := ⟨{(1, -2), (1, -1), (1, 0), (2, 0)}, {(-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -3), (1, -2), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_478 : rowAt 478 = memoRow_478 := by
  have he : entryAt 478 = entry_478 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 478 < 6 by decide, ↓reduceDIte, he, entry_478, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_25, memoRow_eq_165, memoRow_eq_190]
  apply rowData_ext <;> decide +kernel


def memoRow_479 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-8, 2), (-8, 4), (-7, 2), (-7, 3), (-7, 4), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 2), (4, 3), (4, 4), (5, 2), (5, 4)}, 21⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_479 : rowAt 479 = memoRow_479 := by
  have he : entryAt 479 = entry_479 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 479 < 6 by decide, ↓reduceDIte, he, entry_479, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_55, memoRow_eq_443]
  apply rowData_ext <;> decide +kernel


def memoRow_480 : RowData := ⟨{(-1, -3), (0, -3), (0, -2), (0, -1), (1, 1)}, {(-1, -3), (-1, -2), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (1, 3)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_480 : rowAt 480 = memoRow_480 := by
  have he : entryAt 480 = entry_480 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 480 < 6 by decide, ↓reduceDIte, he, entry_480, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_4, memoRow_eq_108]
  apply rowData_ext <;> decide +kernel


def memoRow_481 : RowData := ⟨{(-3, -2), (-2, 0), (-2, 1), (-1, 0)}, {(-5, 0), (-4, -1), (-4, 0), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 1), (3, 2), (4, 2)}, 11⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_481 : rowAt 481 = memoRow_481 := by
  have he : entryAt 481 = entry_481 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 481 < 6 by decide, ↓reduceDIte, he, entry_481, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_169, memoRow_eq_206, memoRow_eq_207, memoRow_eq_303, memoRow_eq_309, memoRow_eq_429]
  apply rowData_ext <;> decide +kernel


def memoRow_482 : RowData := ⟨{(-1, -3), (-1, -2), (-1, -1), (-1, 0), (1, -3)}, {(-3, -1), (-2, -2), (-2, -1), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (3, -1)}, 7⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_482 : rowAt 482 = memoRow_482 := by
  have he : entryAt 482 = entry_482 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 482 < 6 by decide, ↓reduceDIte, he, entry_482, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_218]
  apply rowData_ext <;> decide +kernel


def memoRow_483 : RowData := ⟨{(-2, -3), (-2, -2), (-2, -1), (0, -2), (0, -1)}, {(-7, -1), (-6, -2), (-6, -1), (-5, -2), (-5, -1), (-4, -2), (-4, -1), (-3, -2), (-3, -1), (-2, -3), (-2, -2), (-2, -1), (-2, 1), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (8, -3), (8, -2), (8, -1), (9, -3), (9, -1)}, 22⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_483 : rowAt 483 = memoRow_483 := by
  have he : entryAt 483 = entry_483 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 483 < 6 by decide, ↓reduceDIte, he, entry_483, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_173, memoRow_eq_192, memoRow_eq_292, memoRow_eq_319, memoRow_eq_475]
  apply rowData_ext <;> decide +kernel


def memoRow_484 : RowData := ⟨{(-2, 0), (-2, 1), (-1, 0)}, {(-5, 1), (-4, -1), (-4, 1), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-2, 2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)}, 12⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_484 : rowAt 484 = memoRow_484 := by
  have he : entryAt 484 = entry_484 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 484 < 6 by decide, ↓reduceDIte, he, entry_484, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_25, memoRow_eq_107, memoRow_eq_163, memoRow_eq_349]
  apply rowData_ext <;> decide +kernel


def memoRow_485 : RowData := ⟨{(-1, 0), (-1, 1), (0, -3), (0, -2)}, {(-4, 1), (-3, -1), (-3, 1), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)}, 13⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_485 : rowAt 485 = memoRow_485 := by
  have he : entryAt 485 = entry_485 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 485 < 6 by decide, ↓reduceDIte, he, entry_485, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_2, memoRow_eq_484]
  apply rowData_ext <;> decide +kernel


def memoRow_486 : RowData := ⟨{(0, -3), (0, -1), (1, -4), (1, -3)}, {(-3, 0), (-2, -2), (-2, 0), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -2), (4, -1), (4, 0), (5, -2), (5, 0)}, 14⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_486 : rowAt 486 = memoRow_486 := by
  have he : entryAt 486 = entry_486 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 486 < 6 by decide, ↓reduceDIte, he, entry_486, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_2, memoRow_eq_485]
  apply rowData_ext <;> decide +kernel


def memoRow_487 : RowData := ⟨{(-2, -2), (-1, 0), (-1, 1), (0, -3), (0, -2)}, {(-4, 0), (-3, -1), (-3, 0), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 1), (4, 2), (5, 2)}, 12⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_487 : rowAt 487 = memoRow_487 := by
  have he : entryAt 487 = entry_487 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 487 < 6 by decide, ↓reduceDIte, he, entry_487, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_2, memoRow_eq_481]
  apply rowData_ext <;> decide +kernel


def memoRow_488 : RowData := ⟨{(-2, -1), (-2, 0), (-1, -1), (-1, 0), (1, 0)}, {(-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (2, 0), (2, 1)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_488 : rowAt 488 = memoRow_488 := by
  have he : entryAt 488 = entry_488 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 488 < 6 by decide, ↓reduceDIte, he, entry_488, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_0, memoRow_eq_247]
  apply rowData_ext <;> decide +kernel


def memoRow_489 : RowData := ⟨{(-2, -2), (-2, 0), (-1, -2), (-1, 0)}, {(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 1)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_489 : rowAt 489 = memoRow_489 := by
  have he : entryAt 489 = entry_489 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 489 < 6 by decide, ↓reduceDIte, he, entry_489, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_172, memoRow_eq_197, memoRow_eq_356]
  apply rowData_ext <;> decide +kernel


def memoRow_490 : RowData := ⟨{(0, -3), (0, -2), (0, -1)}, {(-5, -2), (-5, -1), (-5, 0), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (8, -4), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (9, -1), (9, 0), (9, 1), (9, 2), (10, -1), (10, 0), (10, 1), (10, 2)}, 22⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_490 : rowAt 490 = memoRow_490 := by
  have he : entryAt 490 = entry_490 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 490 < 6 by decide, ↓reduceDIte, he, entry_490, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_64, memoRow_eq_111, memoRow_eq_470, memoRow_eq_471]
  apply rowData_ext <;> decide +kernel


def memoRow_491 : RowData := ⟨{(-1, 0), (0, -3), (0, -2), (0, -1)}, {(-3, 0), (-2, 0), (-1, 0), (-1, 1), (0, -3), (0, -2), (0, -1), (0, 0), (1, -2), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_491 : rowAt 491 = memoRow_491 := by
  have he : entryAt 491 = entry_491 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 491 < 6 by decide, ↓reduceDIte, he, entry_491, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_273]
  apply rowData_ext <;> decide +kernel


def memoRow_492 : RowData := ⟨{(1, 0), (1, 2), (1, 3), (2, -1), (2, 0)}, {(-3, -1), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (0, -1), (0, 0), (0, 1), (0, 2), (1, 0), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, 1), (6, 3), (6, 4), (7, 4)}, 13⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_492 : rowAt 492 = memoRow_492 := by
  have he : entryAt 492 = entry_492 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 492 < 6 by decide, ↓reduceDIte, he, entry_492, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_62, memoRow_eq_107, memoRow_eq_487]
  apply rowData_ext <;> decide +kernel


def memoRow_493 : RowData := ⟨{(-2, -2), (-2, -1), (-2, 0), (-1, 0)}, {(-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (-1, 2), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, 1)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_493 : rowAt 493 = memoRow_493 := by
  have he : entryAt 493 = entry_493 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 493 < 6 by decide, ↓reduceDIte, he, entry_493, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_221, memoRow_eq_225, memoRow_eq_236, memoRow_eq_455]
  apply rowData_ext <;> decide +kernel


def memoRow_494 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0), (-1, 1)}, {(-6, 2), (-5, 2), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, 1)}, 11⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_494 : rowAt 494 = memoRow_494 := by
  have he : entryAt 494 = entry_494 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 494 < 6 by decide, ↓reduceDIte, he, entry_494, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_162, memoRow_eq_268, memoRow_eq_297]
  apply rowData_ext <;> decide +kernel


def memoRow_495 : RowData := ⟨{(-2, -1), (-2, 0), (-1, -1), (-1, 0)}, {(-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 3), (2, 0), (2, 1)}, 13⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_495 : rowAt 495 = memoRow_495 := by
  have he : entryAt 495 = entry_495 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 495 < 6 by decide, ↓reduceDIte, he, entry_495, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_25, memoRow_eq_167, memoRow_eq_456]
  apply rowData_ext <;> decide +kernel


def memoRow_496 : RowData := ⟨{(1, 0), (2, 0), (2, 1)}, {(-3, -1), (-3, 1), (-3, 2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1), (7, 1)}, 12⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_496 : rowAt 496 = memoRow_496 := by
  have he : entryAt 496 = entry_496 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 496 < 6 by decide, ↓reduceDIte, he, entry_496, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_25, memoRow_eq_107, memoRow_eq_163, memoRow_eq_494]
  apply rowData_ext <;> decide +kernel


def memoRow_497 : RowData := ⟨{(1, -1), (1, 0), (2, -1), (2, 0)}, {(-3, 1), (-3, 3), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0), (5, 1), (5, 2), (5, 3), (6, 1), (6, 2), (6, 3), (7, 1)}, 15⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_497 : rowAt 497 = memoRow_497 := by
  have he : entryAt 497 = entry_497 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 497 < 6 by decide, ↓reduceDIte, he, entry_497, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_36, memoRow_eq_167, memoRow_eq_410]
  apply rowData_ext <;> decide +kernel


def memoRow_498 : RowData := ⟨{(-2, 1), (-1, -2), (-1, -1), (-1, 0), (0, 1)}, {(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, 1)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_498 : rowAt 498 = memoRow_498 := by
  have he : entryAt 498 = entry_498 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 498 < 6 by decide, ↓reduceDIte, he, entry_498, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_14, memoRow_eq_298]
  apply rowData_ext <;> decide +kernel


def memoRow_499 : RowData := ⟨{(-1, -2), (-1, -1), (-1, 0)}, {(-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, 1)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_499 : rowAt 499 = memoRow_499 := by
  have he : entryAt 499 = entry_499 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 499 < 6 by decide, ↓reduceDIte, he, entry_499, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_25, memoRow_eq_478, memoRow_eq_493]
  apply rowData_ext <;> decide +kernel


def memoRow_500 : RowData := ⟨{(-1, -1), (-1, 0), (-1, 1), (-1, 3), (0, -1)}, {(-4, 1), (-3, 0), (-3, 1), (-2, 0), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -1), (0, 0), (0, 1), (0, 3), (0, 4), (0, 5), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)}, 12⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_500 : rowAt 500 = memoRow_500 := by
  have he : entryAt 500 = entry_500 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 500 < 6 by decide, ↓reduceDIte, he, entry_500, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_1, memoRow_eq_351]
  apply rowData_ext <;> decide +kernel


def memoRow_501 : RowData := ⟨{(-3, 0), (-3, 1), (-3, 2), (-2, 0), (-1, 0)}, {(-4, -1), (-4, 1), (-4, 3), (-4, 4), (-4, 5), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (-1, 1), (-1, 3), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 1), (1, 3), (1, 4), (1, 5)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_501 : rowAt 501 = memoRow_501 := by
  have he : entryAt 501 = entry_501 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 501 < 6 by decide, ↓reduceDIte, he, entry_501, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_316]
  apply rowData_ext <;> decide +kernel


def memoRow_502 : RowData := ⟨{(-2, -2), (-2, 0), (-1, -2), (-1, 0), (0, -2)}, {(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -5), (-3, -4), (-3, -3), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -1), (2, 0), (2, 1), (3, -1), (3, 1)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_502 : rowAt 502 = memoRow_502 := by
  have he : entryAt 502 = entry_502 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 502 < 6 by decide, ↓reduceDIte, he, entry_502, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_173, memoRow_eq_192, memoRow_eq_215, memoRow_eq_232, memoRow_eq_271]
  apply rowData_ext <;> decide +kernel


def memoRow_503 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, -2)}, {(-1, -5), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -2), (1, 0), (1, 1), (1, 2), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (6, -1), (6, 0), (6, 1), (6, 2), (7, -1), (7, 0), (7, 1), (7, 2)}, 14⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_503 : rowAt 503 = memoRow_503 := by
  have he : entryAt 503 = entry_503 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 503 < 6 by decide, ↓reduceDIte, he, entry_503, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_55, memoRow_eq_63, memoRow_eq_419, memoRow_eq_420]
  apply rowData_ext <;> decide +kernel


def memoRow_504 : RowData := ⟨{(1, -2), (1, -1), (1, 0), (1, 1)}, {(-4, -1), (-4, 1), (-4, 2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 3), (2, 4), (2, 5), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, 1)}, 13⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_504 : rowAt 504 = memoRow_504 := by
  have he : entryAt 504 = entry_504 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 504 < 6 by decide, ↓reduceDIte, he, entry_504, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_159, memoRow_eq_310, memoRow_eq_351, memoRow_eq_381, memoRow_eq_496]
  apply rowData_ext <;> decide +kernel


def memoRow_505 : RowData := ⟨{(0, -2), (0, -1)}, {(-2, 0), (-2, 1), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -3), (4, -1), (4, 0), (4, 1), (5, -1), (5, 0), (5, 1), (6, -1), (6, 0), (6, 1), (7, 1)}, 11⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_505 : rowAt 505 = memoRow_505 := by
  have he : entryAt 505 = entry_505 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 505 < 6 by decide, ↓reduceDIte, he, entry_505, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_173, memoRow_eq_183, memoRow_eq_282, memoRow_eq_499]
  apply rowData_ext <;> decide +kernel


def memoRow_506 : RowData := ⟨{(-2, -2), (-2, 0), (-1, -3), (-1, -2), (-1, 0)}, {(-5, -1), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -2), (3, -1), (3, 1), (4, -2)}, 11⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_506 : rowAt 506 = memoRow_506 := by
  have he : entryAt 506 = entry_506 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 506 < 6 by decide, ↓reduceDIte, he, entry_506, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_99, memoRow_eq_173, memoRow_eq_200, memoRow_eq_318]
  apply rowData_ext <;> decide +kernel


def memoRow_507 : RowData := ⟨{(-2, -3), (-2, -2), (-1, 0), (-1, 1), (0, -2)}, {(-4, 0), (-3, -1), (-3, 0), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 1), (4, 2), (5, 2)}, 12⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_507 : rowAt 507 = memoRow_507 := by
  have he : entryAt 507 = entry_507 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 507 < 6 by decide, ↓reduceDIte, he, entry_507, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_33, memoRow_eq_151, memoRow_eq_481]
  apply rowData_ext <;> decide +kernel


def memoRow_508 : RowData := ⟨{(-3, -1), (-3, 0), (-2, -1), (-1, -2), (-1, -1), (0, -1)}, {(-5, 2), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2)}, 13⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_508 : rowAt 508 = memoRow_508 := by
  have he : entryAt 508 = entry_508 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 508 < 6 by decide, ↓reduceDIte, he, entry_508, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_393]
  apply rowData_ext <;> decide +kernel


def memoRow_509 : RowData := ⟨{(-1, -2), (-1, -1), (-1, 0), (1, 0)}, {(-6, 1), (-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (0, -1), (0, 0), (1, -2), (1, -1), (1, 0), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_509 : rowAt 509 = memoRow_509 := by
  have he : entryAt 509 = entry_509 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 509 < 6 by decide, ↓reduceDIte, he, entry_509, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_68, memoRow_eq_241, memoRow_eq_252, memoRow_eq_455]
  apply rowData_ext <;> decide +kernel


def memoRow_510 : RowData := ⟨{(0, -1), (1, -1), (2, -2), (2, -1), (3, -1)}, {(-2, 2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, 0), (4, 1), (4, 2), (4, 3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (6, 0), (6, 1), (6, 2)}, 14⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_510 : rowAt 510 = memoRow_510 := by
  have he : entryAt 510 = entry_510 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 510 < 6 by decide, ↓reduceDIte, he, entry_510, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_508]
  apply rowData_ext <;> decide +kernel


def memoRow_511 : RowData := ⟨{(-3, -2), (-2, -2), (-1, -2), (-1, -1), (-1, 0), (0, 2)}, {(-6, -1), (-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-1, -2), (-1, -1), (-1, 0), (-1, 3), (-1, 4), (-1, 5), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -2), (1, -1), (1, 0), (1, 1), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)}, 10⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_511 : rowAt 511 = memoRow_511 := by
  have he : entryAt 511 = entry_511 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 511 < 6 by decide, ↓reduceDIte, he, entry_511, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_15, memoRow_eq_331, memoRow_eq_380]
  apply rowData_ext <;> decide +kernel


def memoRow_512 : RowData := ⟨{(-2, -1), (-2, 0), (-1, 0), (-1, 2), (-1, 3)}, {(-4, 2), (-3, -1), (-3, 1), (-3, 2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 3), (4, 4), (5, 4)}, 13⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_512 : rowAt 512 = memoRow_512 := by
  have he : entryAt 512 = entry_512 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 512 < 6 by decide, ↓reduceDIte, he, entry_512, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_62, memoRow_eq_107, memoRow_eq_507]
  apply rowData_ext <;> decide +kernel


def memoRow_513 : RowData := ⟨{(0, -1), (1, -1), (2, -1), (3, -1)}, {(-2, 2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, 0), (4, 1), (4, 2), (4, 3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (6, 0), (6, 1), (6, 2)}, 14⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_513 : rowAt 513 = memoRow_513 := by
  have he : entryAt 513 = entry_513 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 513 < 6 by decide, ↓reduceDIte, he, entry_513, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_396]
  apply rowData_ext <;> decide +kernel


def memoRow_514 : RowData := ⟨{(-3, 0), (-2, -1), (-2, 0), (-1, -1), (-1, 0)}, {(-8, 2), (-8, 4), (-7, 2), (-7, 3), (-7, 4), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (3, 3)}, 21⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_514 : rowAt 514 = memoRow_514 := by
  have he : entryAt 514 = entry_514 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 514 < 6 by decide, ↓reduceDIte, he, entry_514, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_57, memoRow_eq_443, memoRow_eq_510]
  apply rowData_ext <;> decide +kernel


def memoRow_515 : RowData := ⟨{(-4, -1), (-3, -1), (-3, 0), (-1, 0)}, {(-4, -2), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 1), (3, 2), (3, 3), (3, 4)}, 14⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_515 : rowAt 515 = memoRow_515 := by
  have he : entryAt 515 = entry_515 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 515 < 6 by decide, ↓reduceDIte, he, entry_515, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_2, memoRow_eq_512]
  apply rowData_ext <;> decide +kernel


def memoRow_516 : RowData := ⟨{(-1, -3), (-1, -2), (-1, 0), (0, -3), (0, -2)}, {(-6, -2), (-5, -2), (-5, -1), (-5, 1), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)}, 12⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_516 : rowAt 516 = memoRow_516 := by
  have he : entryAt 516 = entry_516 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 516 < 6 by decide, ↓reduceDIte, he, entry_516, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_10, memoRow_eq_244, memoRow_eq_329, memoRow_eq_506]
  apply rowData_ext <;> decide +kernel


def memoRow_517 : RowData := ⟨{(-1, -3), (-1, -1), (0, -3), (0, -1)}, {(-5, -2), (-5, 0), (-5, 1), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (2, 0), (3, -2), (3, -1), (3, 0), (4, -2), (4, -1), (4, 0), (5, 0)}, 13⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_517 : rowAt 517 = memoRow_517 := by
  have he : entryAt 517 = entry_517 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 517 < 6 by decide, ↓reduceDIte, he, entry_517, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_140, memoRow_eq_193, memoRow_eq_496]
  apply rowData_ext <;> decide +kernel


def memoRow_518 : RowData := ⟨{(1, -1), (1, 0), (2, -1), (2, 0)}, {(-5, 2), (-5, 4), (-4, 2), (-4, 3), (-4, 4), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, 1), (6, 2), (6, 3)}, 22⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_518 : rowAt 518 = memoRow_518 := by
  have he : entryAt 518 = entry_518 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 518 < 6 by decide, ↓reduceDIte, he, entry_518, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_9, memoRow_eq_514]
  apply rowData_ext <;> decide +kernel


def memoRow_519 : RowData := ⟨{(-2, 0), (-1, -3), (-1, -2), (-1, -1)}, {(-6, -1), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (4, -2), (4, -1), (4, 0), (5, 0)}, 12⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_519 : rowAt 519 = memoRow_519 := by
  have he : entryAt 519 = entry_519 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 519 < 6 by decide, ↓reduceDIte, he, entry_519, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_38, memoRow_eq_311, memoRow_eq_408, memoRow_eq_498]
  apply rowData_ext <;> decide +kernel


def memoRow_520 : RowData := ⟨{(-2, -3), (-1, 0), (1, -2), (1, 0)}, {(-5, -1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -2), (-1, -1), (-1, 0), (0, -5), (0, -4), (0, -3), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (2, -5), (2, -4), (2, -3), (2, -1), (2, 0), (2, 1), (2, 2), (3, -1), (3, 0), (3, 1), (4, -1), (4, 1)}, 8⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_520 : rowAt 520 = memoRow_520 := by
  have he : entryAt 520 = entry_520 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 520 < 6 by decide, ↓reduceDIte, he, entry_520, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_200, memoRow_eq_215, memoRow_eq_252, memoRow_eq_254, memoRow_eq_271]
  apply rowData_ext <;> decide +kernel


def memoRow_521 : RowData := ⟨{(-1, -4), (-1, -3), (0, -3), (0, -1)}, {(-6, 1), (-5, -2), (-5, 0), (-5, 1), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -4), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (1, -4), (1, -3), (1, -2), (1, -1), (2, -4), (2, -3), (2, -2), (2, -1), (3, -4), (3, -3), (3, -2), (3, -1), (4, -4), (4, -2)}, 14⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_521 : rowAt 521 = memoRow_521 := by
  have he : entryAt 521 = entry_521 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 521 < 6 by decide, ↓reduceDIte, he, entry_521, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_2, memoRow_eq_492]
  apply rowData_ext <;> decide +kernel


def memoRow_522 : RowData := ⟨{(-2, -1), (0, -1), (0, 1)}, {(-5, -2), (-5, 0), (-4, -2), (-4, -1), (-4, 0), (-3, -2), (-3, -1), (-3, 0), (-2, -2), (-2, -1), (-2, 1), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -2), (2, -1), (2, 0), (2, 2), (3, -2), (3, -1), (3, 0), (3, 2), (4, -2), (4, -1), (4, 0), (5, -2)}, 9⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_522 : rowAt 522 = memoRow_522 := by
  have he : entryAt 522 = entry_522 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 522 < 6 by decide, ↓reduceDIte, he, entry_522, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_176, memoRow_eq_252, memoRow_eq_338]
  apply rowData_ext <;> decide +kernel


def memoRow_523 : RowData := ⟨{(-3, 4), (-2, 0), (-2, 1), (-2, 2), (-1, 0)}, {(-7, 1), (-7, 3), (-6, 1), (-6, 2), (-6, 3), (-5, 1), (-5, 2), (-5, 3), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 5), (-4, 6), (-4, 7), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, 0), (-2, 1), (-2, 2), (-2, 5), (-2, 6), (-2, 7), (-1, 0), (-1, 1), (-1, 2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 1), (3, 2), (4, 2)}, 11⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_523 : rowAt 523 = memoRow_523 := by
  have he : entryAt 523 = entry_523 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 523 < 6 by decide, ↓reduceDIte, he, entry_523, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_25, memoRow_eq_107, memoRow_eq_303, memoRow_eq_511]
  apply rowData_ext <;> decide +kernel


def memoRow_524 : RowData := ⟨{(0, -3), (0, -2), (0, -1)}, {(-5, -2), (-5, 0), (-5, 1), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -2), (4, -1), (4, 0), (4, 1), (5, -2), (5, 0), (5, 1)}, 14⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_524 : rowAt 524 = memoRow_524 := by
  have he : entryAt 524 = entry_524 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 524 < 6 by decide, ↓reduceDIte, he, entry_524, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_180, memoRow_eq_261, memoRow_eq_504]
  apply rowData_ext <;> decide +kernel


def memoRow_525 : RowData := ⟨{(-2, 0), (-2, 1), (-2, 2), (-1, 0)}, {(-7, 1), (-7, 3), (-6, 1), (-6, 2), (-6, 3), (-5, 1), (-5, 2), (-5, 3), (-4, 1), (-4, 2), (-4, 3), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 4), (-1, 5), (-1, 6), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 1), (3, 2), (3, 3), (4, 1), (4, 2), (4, 3), (5, 1)}, 11⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_525 : rowAt 525 = memoRow_525 := by
  have he : entryAt 525 = entry_525 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 525 < 6 by decide, ↓reduceDIte, he, entry_525, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_25, memoRow_eq_107, memoRow_eq_303, memoRow_eq_430]
  apply rowData_ext <;> decide +kernel


def memoRow_526 : RowData := ⟨{(-1, -2), (-1, 0), (0, -2)}, {(-6, 1), (-6, 2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -6), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 0), (3, 1), (4, -1), (4, 0), (4, 1), (5, -1)}, 17⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_526 : rowAt 526 = memoRow_526 := by
  have he : entryAt 526 = entry_526 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 526 < 6 by decide, ↓reduceDIte, he, entry_526, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_327, memoRow_eq_359, memoRow_eq_399, memoRow_eq_416, memoRow_eq_489]
  apply rowData_ext <;> decide +kernel


def memoRow_527 : RowData := ⟨{(1, -3), (1, -2), (1, -1)}, {(-5, 1), (-4, -2), (-4, -1), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, -1), (1, 0), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -2), (5, -1), (5, 0), (5, 1), (6, -2), (6, -1), (6, 0), (7, 0)}, 13⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_527 : rowAt 527 = memoRow_527 := by
  have he : entryAt 527 = entry_527 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 527 < 6 by decide, ↓reduceDIte, he, entry_527, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_38, memoRow_eq_387, memoRow_eq_491, memoRow_eq_519]
  apply rowData_ext <;> decide +kernel


def memoRow_528 : RowData := ⟨{(-2, -1), (-2, 0), (-2, 1), (0, 1)}, {(-7, 0), (-7, 2), (-6, 0), (-6, 1), (-6, 2), (-5, 0), (-5, 1), (-5, 2), (-4, 0), (-4, 1), (-4, 2), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -1), (-2, 0), (-2, 1), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (1, 5), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 3)}, 12⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_528 : rowAt 528 = memoRow_528 := by
  have he : entryAt 528 = entry_528 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 528 < 6 by decide, ↓reduceDIte, he, entry_528, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_226, memoRow_eq_359, memoRow_eq_386, memoRow_eq_414, memoRow_eq_502]
  apply rowData_ext <;> decide +kernel


def memoRow_529 : RowData := ⟨{(1, 0), (2, 0), (3, 0)}, {(-2, -1), (-2, 1), (-2, 4), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, 1), (7, 2), (7, 3), (7, 4)}, 16⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_529 : rowAt 529 = memoRow_529 := by
  have he : entryAt 529 = entry_529 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 529 < 6 by decide, ↓reduceDIte, he, entry_529, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_55, memoRow_eq_63, memoRow_eq_64, memoRow_eq_441]
  apply rowData_ext <;> decide +kernel


def memoRow_530 : RowData := ⟨{(0, -1), (0, 1), (2, -1), (2, 1)}, {(-4, -3), (-4, -1), (-4, 0), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -1), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2), (6, 0), (6, 2)}, 13⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_530 : rowAt 530 = memoRow_530 := by
  have he : entryAt 530 = entry_530 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 530 < 6 by decide, ↓reduceDIte, he, entry_530, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_271, memoRow_eq_283, memoRow_eq_336, memoRow_eq_456]
  apply rowData_ext <;> decide +kernel


def memoRow_531 : RowData := ⟨{(0, -2), (1, -2)}, {(-5, -1), (-5, 1), (-5, 2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -3), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -7), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -7), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (6, -1)}, 18⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_531 : rowAt 531 = memoRow_531 := by
  have he : entryAt 531 = entry_531 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 531 < 6 by decide, ↓reduceDIte, he, entry_531, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_336, memoRow_eq_340, memoRow_eq_394, memoRow_eq_401, memoRow_eq_423, memoRow_eq_425, memoRow_eq_453, memoRow_eq_526]
  apply rowData_ext <;> decide +kernel


def memoRow_532 : RowData := ⟨{(-1, -3), (0, -3), (0, -2), (0, -1)}, {(-5, 0), (-4, -2), (-4, -1), (-4, 0), (-3, -2), (-3, -1), (-3, 0), (-2, -2), (-2, -1), (-2, 0), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -2), (4, -1), (4, 0), (4, 1), (5, -2), (5, 0), (5, 1)}, 14⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_532 : rowAt 532 = memoRow_532 := by
  have he : entryAt 532 = entry_532 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 532 < 6 by decide, ↓reduceDIte, he, entry_532, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_504]
  apply rowData_ext <;> decide +kernel


def memoRow_533 : RowData := ⟨{(0, -2), (0, -1)}, {(-5, -1), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -5), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (2, -4), (2, -3), (2, -2), (2, 0), (2, 1), (3, -4), (3, -3), (3, -2), (3, 0), (4, -4), (4, -3), (4, -2), (5, -2)}, 11⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_533 : rowAt 533 = memoRow_533 := by
  have he : entryAt 533 = entry_533 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 533 < 6 by decide, ↓reduceDIte, he, entry_533, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_173, memoRow_eq_217, memoRow_eq_318, memoRow_eq_319, memoRow_eq_407]
  apply rowData_ext <;> decide +kernel


def memoRow_534 : RowData := ⟨{(-2, -1), (-2, 0), (-2, 2), (-1, -1), (-1, 0), (-1, 2)}, {(-5, 3), (-5, 5), (-4, -1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-3, -1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-2, -1), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, 3)}, 16⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_534 : rowAt 534 = memoRow_534 := by
  have he : entryAt 534 = entry_534 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 534 < 6 by decide, ↓reduceDIte, he, entry_534, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_12, memoRow_eq_434]
  apply rowData_ext <;> decide +kernel


def memoRow_535 : RowData := ⟨{(-2, -1), (-1, -1), (0, -1)}, {(-5, -2), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0), (5, 1), (5, 3)}, 15⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_535 : rowAt 535 = memoRow_535 := by
  have he : entryAt 535 = entry_535 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 535 < 6 by decide, ↓reduceDIte, he, entry_535, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_25, memoRow_eq_321, memoRow_eq_426, memoRow_eq_444]
  apply rowData_ext <;> decide +kernel


def memoRow_536 : RowData := ⟨{(-1, -3), (-1, -2), (-1, 0), (0, -3), (0, -2)}, {(-4, 1), (-4, 3), (-3, -3), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -3), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, 1)}, 17⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_536 : rowAt 536 = memoRow_536 := by
  have he : entryAt 536 = entry_536 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 536 < 6 by decide, ↓reduceDIte, he, entry_536, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_26, memoRow_eq_244, memoRow_eq_307, memoRow_eq_534]
  apply rowData_ext <;> decide +kernel


def memoRow_537 : RowData := ⟨{(-3, 1), (-2, -1), (-2, 1), (0, -1), (0, 1)}, {(-7, -2), (-7, 0), (-6, -2), (-6, -1), (-6, 0), (-5, -2), (-5, -1), (-5, 0), (-4, -2), (-4, -1), (-4, 0), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0)}, 11⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_537 : rowAt 537 = memoRow_537 := by
  have he : entryAt 537 = entry_537 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 537 < 6 by decide, ↓reduceDIte, he, entry_537, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_176, memoRow_eq_271, memoRow_eq_330, memoRow_eq_373]
  apply rowData_ext <;> decide +kernel


def memoRow_538 : RowData := ⟨{(1, 0), (2, 0), (3, 0)}, {(-2, -1), (-2, 1), (-2, 7), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 0), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 4), (7, 5), (7, 6), (7, 7)}, 22⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_538 : rowAt 538 = memoRow_538 := by
  have he : entryAt 538 = entry_538 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 538 < 6 by decide, ↓reduceDIte, he, entry_538, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_55, memoRow_eq_63, memoRow_eq_64, memoRow_eq_470]
  apply rowData_ext <;> decide +kernel


def memoRow_539 : RowData := ⟨{(0, -3), (0, -2), (1, -3), (1, -2)}, {(-5, -2), (-4, -4), (-4, -2), (-4, -1), (-4, 1), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (6, -1), (6, 1)}, 18⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_539 : rowAt 539 = memoRow_539 := by
  have he : entryAt 539 = entry_539 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 539 < 6 by decide, ↓reduceDIte, he, entry_539, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_51, memoRow_eq_428, memoRow_eq_488, memoRow_eq_516]
  apply rowData_ext <;> decide +kernel


def memoRow_540 : RowData := ⟨{(0, -3), (0, -2), (1, -3), (1, -2)}, {(-3, -3), (-3, 1), (-3, 3), (-2, -3), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -4), (-1, -3), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (7, 1)}, 18⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_540 : rowAt 540 = memoRow_540 := by
  have he : entryAt 540 = entry_540 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 540 < 6 by decide, ↓reduceDIte, he, entry_540, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_51, memoRow_eq_88, memoRow_eq_334, memoRow_eq_536]
  apply rowData_ext <;> decide +kernel


def memoRow_541 : RowData := ⟨{(-2, -2), (-1, -2), (0, -2), (0, -1)}, {(-5, 0), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1), (4, 2), (5, 0), (5, 2)}, 14⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_541 : rowAt 541 = memoRow_541 := by
  have he : entryAt 541 = entry_541 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 541 < 6 by decide, ↓reduceDIte, he, entry_541, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_142, memoRow_eq_160, memoRow_eq_194, memoRow_eq_236, memoRow_eq_412, memoRow_eq_501]
  apply rowData_ext <;> decide +kernel


def memoRow_542 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, -3)}, {(-3, -1), (-2, -1), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, 1), (6, 2), (6, 3), (6, 4), (7, 1), (7, 2), (7, 3), (7, 4)}, 17⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_542 : rowAt 542 = memoRow_542 := by
  have he : entryAt 542 = entry_542 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 542 < 6 by decide, ↓reduceDIte, he, entry_542, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_442]
  apply rowData_ext <;> decide +kernel


def memoRow_543 : RowData := ⟨{(-2, 0), (-2, 1), (-1, 0)}, {(-6, 3), (-5, -1), (-5, 3), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-3, -2), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -2), (3, -1), (3, 1), (4, -2)}, 11⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_543 : rowAt 543 = memoRow_543 := by
  have he : entryAt 543 = entry_543 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 543 < 6 by decide, ↓reduceDIte, he, entry_543, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_107, memoRow_eq_318, memoRow_eq_493]
  apply rowData_ext <;> decide +kernel


def memoRow_544 : RowData := ⟨{(1, -1), (1, 0), (2, -1), (2, 0)}, {(-3, 1), (-2, 0), (-2, 1), (-1, 0), (-1, 1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (10, -2), (10, 0), (10, 2)}, 18⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_544 : rowAt 544 = memoRow_544 := by
  have he : entryAt 544 = entry_544 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 544 < 6 by decide, ↓reduceDIte, he, entry_544, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_9, memoRow_eq_263, memoRow_eq_451]
  apply rowData_ext <;> decide +kernel


def memoRow_545 : RowData := ⟨{(-1, -1), (0, -2), (0, -1), (1, -2), (1, -1)}, {(-4, 1), (-4, 3), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 0), (5, 1), (5, 2), (5, 3), (6, 1), (6, 3)}, 20⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_545 : rowAt 545 = memoRow_545 := by
  have he : entryAt 545 = entry_545 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 545 < 6 by decide, ↓reduceDIte, he, entry_545, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_153, memoRow_eq_256, memoRow_eq_343, memoRow_eq_448]
  apply rowData_ext <;> decide +kernel


def memoRow_546 : RowData := ⟨{(1, 0), (2, 0), (3, -2), (3, 0)}, {(-2, -1), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, -3), (2, -2), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, -2), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -2), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 2), (7, 3), (7, 4), (8, 2), (8, 4)}, 21⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_546 : rowAt 546 = memoRow_546 := by
  have he : entryAt 546 = entry_546 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 546 < 6 by decide, ↓reduceDIte, he, entry_546, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_64, memoRow_eq_443, memoRow_eq_482]
  apply rowData_ext <;> decide +kernel


def memoRow_547 : RowData := ⟨{(1, -1), (1, 0), (2, 0), (3, 0)}, {(-3, -1), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 2), (7, 3), (7, 4), (8, 2), (8, 4)}, 21⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_547 : rowAt 547 = memoRow_547 := by
  have he : entryAt 547 = entry_547 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 547 < 6 by decide, ↓reduceDIte, he, entry_547, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_131, memoRow_eq_443, memoRow_eq_510]
  apply rowData_ext <;> decide +kernel


def memoRow_548 : RowData := ⟨{(-2, -1), (-1, -1), (0, -1)}, {(-5, 0), (-5, 1), (-5, 2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0), (5, 1), (5, 3)}, 15⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_548 : rowAt 548 = memoRow_548 := by
  have he : entryAt 548 = entry_548 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 548 < 6 by decide, ↓reduceDIte, he, entry_548, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_25, memoRow_eq_321, memoRow_eq_426, memoRow_eq_541]
  apply rowData_ext <;> decide +kernel


def memoRow_549 : RowData := ⟨{(-2, -3), (-1, 0), (1, 0)}, {(-5, 1), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 1), (5, 2), (5, 3), (5, 4)}, 17⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_549 : rowAt 549 = memoRow_549 := by
  have he : entryAt 549 = entry_549 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 549 < 6 by decide, ↓reduceDIte, he, entry_549, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_252, memoRow_eq_326, memoRow_eq_330, memoRow_eq_385, memoRow_eq_529]
  apply rowData_ext <;> decide +kernel


def memoRow_550 : RowData := ⟨{(0, -1), (0, 1), (2, 1)}, {(-5, 0), (-5, 1), (-5, 2), (-5, 3), (-4, -3), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 4), (-1, 5), (-1, 6), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 1), (2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1), (4, 2), (4, 3), (5, 0), (5, 1), (5, 2), (5, 3), (6, 0), (6, 1), (6, 2), (6, 3), (7, 0), (7, 1), (7, 2), (7, 3)}, 13⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_550 : rowAt 550 = memoRow_550 := by
  have he : entryAt 550 = entry_550 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 550 < 6 by decide, ↓reduceDIte, he, entry_550, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_172, memoRow_eq_215, memoRow_eq_424, memoRow_eq_456]
  apply rowData_ext <;> decide +kernel


def memoRow_551 : RowData := ⟨{(0, 1), (0, 2)}, {(-6, 3), (-5, 1), (-5, 2), (-5, 3), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -3), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, 1), (5, 2), (5, 4), (6, 4)}, 14⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_551 : rowAt 551 = memoRow_551 := by
  have he : entryAt 551 = entry_551 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 551 < 6 by decide, ↓reduceDIte, he, entry_551, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_172, memoRow_eq_176, memoRow_eq_300, memoRow_eq_319, memoRow_eq_527]
  apply rowData_ext <;> decide +kernel


def memoRow_552 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-8, 2), (-8, 4), (-7, 2), (-7, 3), (-7, 4), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (4, -3), (4, -2), (4, -1), (4, 1), (5, -1)}, 21⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_552 : rowAt 552 = memoRow_552 := by
  have he : entryAt 552 = entry_552 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 552 < 6 by decide, ↓reduceDIte, he, entry_552, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_64, memoRow_eq_404, memoRow_eq_443, memoRow_eq_504]
  apply rowData_ext <;> decide +kernel


def memoRow_553 : RowData := ⟨{(0, -3), (0, -2), (0, -1)}, {(-5, -2), (-5, -1), (-5, 0), (-5, 1), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4)}, 17⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_553 : rowAt 553 = memoRow_553 := by
  have he : entryAt 553 = entry_553 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 553 < 6 by decide, ↓reduceDIte, he, entry_553, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_63, memoRow_eq_180, memoRow_eq_261, memoRow_eq_442, memoRow_eq_471, memoRow_eq_504]
  apply rowData_ext <;> decide +kernel


def memoRow_554 : RowData := ⟨{(0, -2), (0, -1), (1, -1), (1, 1), (2, 1), (3, 1)}, {(-3, 3), (-3, 5), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -1), (1, 0), (1, 1), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 0), (4, 1), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, 2), (7, 3), (7, 5)}, 22⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_554 : rowAt 554 = memoRow_554 := by
  have he : entryAt 554 = entry_554 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 554 < 6 by decide, ↓reduceDIte, he, entry_554, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_30, memoRow_eq_96, memoRow_eq_474]
  apply rowData_ext <;> decide +kernel


def memoRow_555 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-8, 2), (-8, 4), (-7, 2), (-7, 3), (-7, 4), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -1), (4, 1), (4, 2), (4, 3), (5, 1)}, 21⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_555 : rowAt 555 = memoRow_555 := by
  have he : entryAt 555 = entry_555 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 555 < 6 by decide, ↓reduceDIte, he, entry_555, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_55, memoRow_eq_443, memoRow_eq_471, memoRow_eq_504, memoRow_eq_513]
  apply rowData_ext <;> decide +kernel


def memoRow_556 : RowData := ⟨{(-3, -3), (-2, -3), (-2, 0), (-1, -4), (-1, -3), (0, -3)}, {(-6, 1), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, -3), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, 1), (4, 2), (4, 3), (4, 4)}, 18⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_556 : rowAt 556 = memoRow_556 := by
  have he : entryAt 556 = entry_556 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 556 < 6 by decide, ↓reduceDIte, he, entry_556, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_34, memoRow_eq_549]
  apply rowData_ext <;> decide +kernel


def memoRow_557 : RowData := ⟨{(-1, 0)}, {(-6, -1), (-6, 0), (-6, 1), (-6, 3), (-6, 4), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -1), (5, 0), (5, 1), (5, 3), (5, 4)}, 19⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_557 : rowAt 557 = memoRow_557 := by
  have he : entryAt 557 = entry_557 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 557 < 6 by decide, ↓reduceDIte, he, entry_557, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_406, memoRow_eq_411, memoRow_eq_460, memoRow_eq_531]
  apply rowData_ext <;> decide +kernel


def memoRow_558 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-8, 2), (-8, 4), (-7, 2), (-7, 3), (-7, 4), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, -1), (5, 2), (5, 3), (5, 4), (6, 2), (6, 3), (6, 4)}, 21⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_558 : rowAt 558 = memoRow_558 := by
  have he : entryAt 558 = entry_558 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 558 < 6 by decide, ↓reduceDIte, he, entry_558, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_180, memoRow_eq_442, memoRow_eq_443, memoRow_eq_513]
  apply rowData_ext <;> decide +kernel


def memoRow_559 : RowData := ⟨{(0, -4), (0, -3), (0, -2), (0, -1)}, {(-3, -1), (-2, -1), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -3), (1, -2), (1, -1), (1, 1), (1, 2), (1, 3), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (5, -6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 2), (9, -4), (9, -3), (9, -2), (9, -1), (10, -4), (10, -3), (10, -2), (10, -1)}, 23⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_559 : rowAt 559 = memoRow_559 := by
  have he : entryAt 559 = entry_559 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 559 < 6 by decide, ↓reduceDIte, he, entry_559, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_7, memoRow_eq_155, memoRow_eq_228, memoRow_eq_538]
  apply rowData_ext <;> decide +kernel


def memoRow_560 : RowData := ⟨{(-2, -1), (-2, 0), (-2, 1), (0, 1)}, {(-7, 1), (-6, 0), (-6, 1), (-5, 0), (-5, 1), (-4, 0), (-4, 1), (-3, 0), (-3, 1), (-2, -1), (-2, 0), (-2, 1), (-2, 3), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (8, -1), (8, 0), (8, 1), (9, -1), (9, 1)}, 23⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_560 : rowAt 560 = memoRow_560 := by
  have he : entryAt 560 = entry_560 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 560 < 6 by decide, ↓reduceDIte, he, entry_560, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_356, memoRow_eq_359, memoRow_eq_416, memoRow_eq_483, memoRow_eq_517]
  apply rowData_ext <;> decide +kernel


def memoRow_561 : RowData := ⟨{(-2, -2), (-2, 0), (-1, 0)}, {(-7, 2), (-7, 4), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, -2), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -2), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -1), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 4), (5, 1), (5, 2), (5, 4)}, 22⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_561 : rowAt 561 = memoRow_561 := by
  have he : entryAt 561 = entry_561 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 561 < 6 by decide, ↓reduceDIte, he, entry_561, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_173, memoRow_eq_176, memoRow_eq_236, memoRow_eq_263, memoRow_eq_295, memoRow_eq_535, memoRow_eq_546]
  apply rowData_ext <;> decide +kernel


def memoRow_562 : RowData := ⟨{(-1, -3), (0, -3), (0, -2), (0, -1)}, {(-3, 0), (-2, 0), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 3), (9, -3), (9, -2), (9, -1), (9, 0), (10, -3), (10, -2), (10, -1), (10, 0)}, 24⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_562 : rowAt 562 = memoRow_562 := by
  have he : entryAt 562 = entry_562 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 562 < 6 by decide, ↓reduceDIte, he, entry_562, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_6, memoRow_eq_559]
  apply rowData_ext <;> decide +kernel


def memoRow_563 : RowData := ⟨{(1, -1), (1, 0), (2, -1), (2, 0)}, {(-5, 2), (-5, 4), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 2), (7, 4)}, 23⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_563 : rowAt 563 = memoRow_563 := by
  have he : entryAt 563 = entry_563 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 563 < 6 by decide, ↓reduceDIte, he, entry_563, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_167, memoRow_eq_330, memoRow_eq_514, memoRow_eq_538, memoRow_eq_545]
  apply rowData_ext <;> decide +kernel


def memoRow_564 : RowData := ⟨{(-2, -2), (-2, -1), (-2, 0)}, {(-7, -1), (-7, 0), (-7, 1), (-6, -1), (-6, 0), (-6, 1), (-5, -1), (-5, 0), (-5, 1), (-4, -1), (-4, 0), (-4, 1), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -2), (-2, -1), (-2, 0), (-2, 2), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (8, -2), (8, -1), (8, 0), (9, -2), (9, 0)}, 24⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_564 : rowAt 564 = memoRow_564 := by
  have he : entryAt 564 = entry_564 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 564 < 6 by decide, ↓reduceDIte, he, entry_564, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_336, memoRow_eq_340, memoRow_eq_401, memoRow_eq_421, memoRow_eq_423, memoRow_eq_425, memoRow_eq_509, memoRow_eq_528, memoRow_eq_560]
  apply rowData_ext <;> decide +kernel


def memoRow_565 : RowData := ⟨{(1, -1), (1, 0), (2, 0), (3, 0)}, {(-5, 2), (-5, 4), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, -1), (4, 0), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, -1), (5, 0), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, -1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 2), (7, 4)}, 23⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_565 : rowAt 565 = memoRow_565 := by
  have he : entryAt 565 = entry_565 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 565 < 6 by decide, ↓reduceDIte, he, entry_565, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_131, memoRow_eq_144, memoRow_eq_443, memoRow_eq_459, memoRow_eq_538]
  apply rowData_ext <;> decide +kernel


def memoRow_566 : RowData := ⟨{(0, -3), (0, -2), (0, -1), (1, -3)}, {(-5, -2), (-5, -1), (-5, 0), (-5, 1), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4)}, 17⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_566 : rowAt 566 = memoRow_566 := by
  have he : entryAt 566 = entry_566 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 566 < 6 by decide, ↓reduceDIte, he, entry_566, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_180, memoRow_eq_314, memoRow_eq_442, memoRow_eq_466, memoRow_eq_504]
  apply rowData_ext <;> decide +kernel


def memoRow_567 : RowData := ⟨{(-1, -4), (0, -4), (0, -3), (0, -2), (1, 0)}, {(-5, -4), (-5, -2), (-5, 2), (-5, 4), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, -1), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 1), (6, 2), (6, 3), (6, 4), (7, 1), (7, 2), (7, 4)}, 23⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_567 : rowAt 567 = memoRow_567 := by
  have he : entryAt 567 = entry_567 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 567 < 6 by decide, ↓reduceDIte, he, entry_567, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_21, memoRow_eq_500, memoRow_eq_561]
  apply rowData_ext <;> decide +kernel


def memoRow_568 : RowData := ⟨{(-1, -1), (-1, 0), (1, 0)}, {(-7, 2), (-7, 4), (-6, 2), (-6, 3), (-6, 4), (-5, -1), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 4), (6, 2), (6, 4)}, 24⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_568 : rowAt 568 = memoRow_568 := by
  have he : entryAt 568 = entry_568 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 568 < 6 by decide, ↓reduceDIte, he, entry_568, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_275, memoRow_eq_330, memoRow_eq_538, memoRow_eq_547, memoRow_eq_565]
  apply rowData_ext <;> decide +kernel


def memoRow_569 : RowData := ⟨{(0, -3), (1, -4), (1, -3), (2, -3), (2, -1), (2, 0), (3, -3)}, {(-5, 2), (-5, 4), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, -3), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, -3), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, -1), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 2), (7, 3), (7, 4), (8, 2), (8, 4)}, 25⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_569 : rowAt 569 = memoRow_569 := by
  have he : entryAt 569 = entry_569 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 569 < 6 by decide, ↓reduceDIte, he, entry_569, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_34, memoRow_eq_568]
  apply rowData_ext <;> decide +kernel


def memoRow_570 : RowData := ⟨{(-2, -2), (-1, -3), (-1, -2), (0, -2), (0, 1), (1, -2)}, {(-7, 3), (-7, 5), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, -2), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 0), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 3), (5, 4), (5, 5), (6, 3), (6, 5)}, 26⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_570 : rowAt 570 = memoRow_570 := by
  have he : entryAt 570 = entry_570 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 570 < 6 by decide, ↓reduceDIte, he, entry_570, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_2, memoRow_eq_569]
  apply rowData_ext <;> decide +kernel


def memoRow_571 : RowData := ⟨{(-2, -3), (-1, -4), (-1, -3), (0, -3), (1, -3)}, {(-7, 2), (-7, 4), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, -2), (4, -1), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 2), (5, 3), (5, 4), (6, 2), (6, 4)}, 27⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_571 : rowAt 571 = memoRow_571 := by
  have he : entryAt 571 = entry_571 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 571 < 6 by decide, ↓reduceDIte, he, entry_571, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_293, memoRow_eq_382, memoRow_eq_556, memoRow_eq_570]
  apply rowData_ext <;> decide +kernel


def memoRow_572 : RowData := ⟨{(1, 0), (2, 0)}, {(-4, 1), (-4, 2), (-4, 3), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, -1), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (8, 1), (8, 3), (8, 4), (8, 6)}, 25⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_572 : rowAt 572 = memoRow_572 := by
  have he : entryAt 572 = entry_572 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 572 < 6 by decide, ↓reduceDIte, he, entry_572, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_364, memoRow_eq_385, memoRow_eq_465, memoRow_eq_499, memoRow_eq_564]
  apply rowData_ext <;> decide +kernel


def memoRow_573 : RowData := ⟨{(0, -2), (0, -1)}, {(-8, -3), (-8, -1), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-3, -7), (-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 2), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (3, -7), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (6, -4), (6, -3), (6, -1), (6, 0), (6, 1), (7, 1)}, 19⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_573 : rowAt 573 = memoRow_573 := by
  have he : entryAt 573 = entry_573 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 573 < 6 by decide, ↓reduceDIte, he, entry_573, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_407, memoRow_eq_499, memoRow_eq_527, memoRow_eq_531]
  apply rowData_ext <;> decide +kernel


def memoRow_574 : RowData := ⟨{(-1, -1), (-1, 0), (0, -1)}, {(-7, 2), (-7, 3), (-7, 4), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (8, -2), (8, 0), (8, 2)}, 24⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_574 : rowAt 574 = memoRow_574 := by
  have he : entryAt 574 = entry_574 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 574 < 6 by decide, ↓reduceDIte, he, entry_574, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_355, memoRow_eq_390, memoRow_eq_462, memoRow_eq_495, memoRow_eq_497, memoRow_eq_518, memoRow_eq_539, memoRow_eq_540, memoRow_eq_544, memoRow_eq_563]
  apply rowData_ext <;> decide +kernel


def memoRow_575 : RowData := ⟨{(0, -3), (0, -2), (0, -1)}, {(-7, 1), (-7, 2), (-7, 3), (-7, 4), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 3), (9, -3), (9, -2), (9, -1), (9, 0), (10, -3), (10, -2), (10, -1), (10, 0)}, 24⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_575 : rowAt 575 = memoRow_575 := by
  have he : entryAt 575 = entry_575 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 575 < 6 by decide, ↓reduceDIte, he, entry_575, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_180, memoRow_eq_314, memoRow_eq_442, memoRow_eq_504, memoRow_eq_559]
  apply rowData_ext <;> decide +kernel


def memoRow_576 : RowData := ⟨{(-1, -1), (-1, 0), (0, -1)}, {(-9, -2), (-9, 0), (-9, 2), (-8, -2), (-8, -1), (-8, 0), (-8, 1), (-8, 2), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (6, 2), (6, 3), (6, 4)}, 24⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_576 : rowAt 576 = memoRow_576 := by
  have he : entryAt 576 = entry_576 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 576 < 6 by decide, ↓reduceDIte, he, entry_576, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_355, memoRow_eq_390, memoRow_eq_462, memoRow_eq_495, memoRow_eq_497, memoRow_eq_518, memoRow_eq_539, memoRow_eq_540, memoRow_eq_544, memoRow_eq_563]
  apply rowData_ext <;> decide +kernel


def memoRow_577 : RowData := ⟨{(0, -3), (0, -2), (0, -1)}, {(-9, -2), (-9, 0), (-8, -2), (-8, -1), (-8, 0), (-7, -6), (-7, -5), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-6, -6), (-6, -5), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-5, -6), (-5, -5), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-4, -8), (-4, -7), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-3, -7), (-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-2, -8), (-2, -7), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1), (1, 2), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (8, -3), (8, -2), (8, -1), (9, -3), (9, -1)}, 21⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_577 : rowAt 577 = memoRow_577 := by
  have he : entryAt 577 = entry_577 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 577 < 6 by decide, ↓reduceDIte, he, entry_577, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_64, memoRow_eq_443]
  apply rowData_ext <;> decide +kernel


def memoRow_578 : RowData := ⟨{(0, -3), (0, -2), (1, 0), (1, 1)}, {(-8, -1), (-8, 1), (-8, 3), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, 3), (7, 4), (7, 5)}, 25⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_578 : rowAt 578 = memoRow_578 := by
  have he : entryAt 578 = entry_578 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 578 < 6 by decide, ↓reduceDIte, he, entry_578, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_2, memoRow_eq_574]
  apply rowData_ext <;> decide +kernel


def memoRow_579 : RowData := ⟨{(0, -3), (0, -2), (1, 0), (1, 1)}, {(-6, 3), (-6, 4), (-6, 5), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (9, -1), (9, 1), (9, 3)}, 25⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_579 : rowAt 579 = memoRow_579 := by
  have he : entryAt 579 = entry_579 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 579 < 6 by decide, ↓reduceDIte, he, entry_579, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_2, memoRow_eq_576]
  apply rowData_ext <;> decide +kernel


def memoRow_580 : RowData := ⟨{(-1, -4), (-1, -3), (0, -3), (0, -1)}, {(-7, 2), (-7, 3), (-7, 4), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (8, -2), (8, 0), (8, 2)}, 26⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_580 : rowAt 580 = memoRow_580 := by
  have he : entryAt 580 = entry_580 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 580 < 6 by decide, ↓reduceDIte, he, entry_580, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_2, memoRow_eq_579]
  apply rowData_ext <;> decide +kernel


def memoRow_581 : RowData := ⟨{(0, -3), (0, -1), (1, -4), (1, -3)}, {(-6, 2), (-6, 3), (-6, 4), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (9, -2), (9, 0), (9, 2)}, 26⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_581 : rowAt 581 = memoRow_581 := by
  have he : entryAt 581 = entry_581 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 581 < 6 by decide, ↓reduceDIte, he, entry_581, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_2, memoRow_eq_578]
  apply rowData_ext <;> decide +kernel


def memoRow_582 : RowData := ⟨{(1, -4), (1, -3), (1, -2), (2, -4)}, {(-6, 1), (-6, 2), (-6, 4), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, -3), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -4), (2, -3), (2, -2), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -9), (3, -8), (3, -7), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -8), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, -9), (5, -8), (5, -7), (5, -6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, -7), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 2), (6, 4), (7, -7), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (8, -7), (8, -6), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (9, -3), (9, -2), (9, -1), (10, -3), (10, -1)}, 24⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_582 : rowAt 582 = memoRow_582 := by
  have he : entryAt 582 = entry_582 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 582 < 6 by decide, ↓reduceDIte, he, entry_582, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_40, memoRow_eq_446, memoRow_eq_480, memoRow_eq_523, memoRow_eq_567]
  apply rowData_ext <;> decide +kernel


def memoRow_583 : RowData := ⟨{(-1, 0), (-1, 1), (-1, 2)}, {(-8, 5), (-8, 6), (-8, 8), (-7, 5), (-7, 6), (-7, 7), (-7, 8), (-6, 1), (-6, 3), (-6, 5), (-6, 6), (-6, 7), (-6, 8), (-6, 9), (-6, 10), (-6, 11), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-4, 13), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-2, 13), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 6), (4, 8), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (7, 1), (7, 2), (7, 3), (8, 1), (8, 3)}, 25⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_583 : rowAt 583 = memoRow_583 := by
  have he : entryAt 583 = entry_583 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 583 < 6 by decide, ↓reduceDIte, he, entry_583, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_25, memoRow_eq_221, memoRow_eq_525, memoRow_eq_582]
  apply rowData_ext <;> decide +kernel


def memoRow_584 : RowData := ⟨{(0, -2), (0, -1)}, {(-9, -1), (-9, 1), (-8, -1), (-8, 0), (-8, 1), (-7, -5), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 3), (-6, -5), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-5, -5), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-4, -7), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -7), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (8, -2), (8, -1), (8, 0), (9, -2), (9, 0)}, 22⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_584 : rowAt 584 = memoRow_584 := by
  have he : entryAt 584 = entry_584 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 584 < 6 by decide, ↓reduceDIte, he, entry_584, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_173, memoRow_eq_236, memoRow_eq_263, memoRow_eq_295, memoRow_eq_548, memoRow_eq_577]
  apply rowData_ext <;> decide +kernel


def memoRow_585 : RowData := ⟨{(0, -2), (0, -1)}, {(-9, -1), (-9, 1), (-8, -1), (-8, 0), (-8, 1), (-7, -5), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-6, -5), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-5, -5), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-4, -7), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -7), (-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -7), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -7), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (8, -2), (8, -1), (8, 0), (8, 1), (9, -2), (9, -1), (9, 0), (9, 1)}, 22⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_585 : rowAt 585 = memoRow_585 := by
  have he : entryAt 585 = entry_585 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 585 < 6 by decide, ↓reduceDIte, he, entry_585, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_183, memoRow_eq_236, memoRow_eq_300, memoRow_eq_479, memoRow_eq_527, memoRow_eq_577]
  apply rowData_ext <;> decide +kernel


def memoRow_586 : RowData := ⟨{(0, -2), (0, -1)}, {(-7, 3), (-7, 4), (-7, 6), (-6, 1), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, -7), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (10, -2), (10, -1), (10, 0), (11, -2), (11, 0)}, 26⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_586 : rowAt 586 = memoRow_586 := by
  have he : entryAt 586 = entry_586 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 586 < 6 by decide, ↓reduceDIte, he, entry_586, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_379, memoRow_eq_385, memoRow_eq_465, memoRow_eq_467, memoRow_eq_469, memoRow_eq_524, memoRow_eq_527, memoRow_eq_552, memoRow_eq_553, memoRow_eq_555, memoRow_eq_558, memoRow_eq_564, memoRow_eq_583]
  apply rowData_ext <;> decide +kernel


def memoRow_587 : RowData := ⟨{(0, -2), (0, -1)}, {(-7, -2), (-7, -1), (-7, 0), (-7, 1), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -5), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, -7), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (8, -2), (8, -1), (8, 0), (8, 1), (9, -2), (9, -1), (9, 0), (9, 1)}, 22⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_587 : rowAt 587 = memoRow_587 := by
  have he : entryAt 587 = entry_587 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 587 < 6 by decide, ↓reduceDIte, he, entry_587, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_252, memoRow_eq_300, memoRow_eq_319, memoRow_eq_467, memoRow_eq_477, memoRow_eq_479]
  apply rowData_ext <;> decide +kernel


def memoRow_588 : RowData := ⟨{(-1, -4), (-1, -3), (-1, -2), (0, -1)}, {(-7, 4), (-7, 5), (-7, 7), (-6, 2), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (10, -1), (10, 0), (10, 1), (11, -1), (11, 1)}, 27⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_588 : rowAt 588 = memoRow_588 := by
  have he : entryAt 588 = entry_588 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 588 < 6 by decide, ↓reduceDIte, he, entry_588, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_3, memoRow_eq_586]
  apply rowData_ext <;> decide +kernel


def memoRow_589 : RowData := ⟨{(-1, -4), (-1, -3), (-1, -2), (-1, -1)}, {(-7, 5), (-7, 6), (-7, 8), (-6, 3), (-6, 5), (-6, 6), (-6, 7), (-6, 8), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-5, 11), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-3, 13), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (10, 0), (10, 1), (10, 2), (11, 0), (11, 2)}, 28⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_589 : rowAt 589 = memoRow_589 := by
  have he : entryAt 589 = entry_589 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 589 < 6 by decide, ↓reduceDIte, he, entry_589, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_4, memoRow_eq_588]
  apply rowData_ext <;> decide +kernel


def memoRow_590 : RowData := ⟨{(0, 1), (0, 2)}, {(-9, 1), (-9, 3), (-8, 1), (-8, 2), (-8, 3), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 5), (-1, 6), (-1, 7), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -3), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (9, 0), (9, 2), (9, 3), (9, 4), (9, 5), (10, 2), (10, 3), (10, 4), (10, 5)}, 23⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_590 : rowAt 590 = memoRow_590 := by
  have he : entryAt 590 = entry_590 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 590 < 6 by decide, ↓reduceDIte, he, entry_590, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_173, memoRow_eq_217, memoRow_eq_295, memoRow_eq_490, memoRow_eq_577]
  apply rowData_ext <;> decide +kernel


def memoRow_591 : RowData := ⟨{(0, -2), (0, -1)}, {(-10, -1), (-10, 0), (-10, 1), (-10, 2), (-9, -1), (-9, 0), (-9, 1), (-9, 2), (-8, -4), (-8, -2), (-8, -1), (-8, 0), (-8, 1), (-8, 2), (-7, -5), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-1, -5), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (8, -4), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (9, -1), (9, 0), (9, 1), (9, 2), (10, -1), (10, 0), (10, 1), (10, 2)}, 23⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_591 : rowAt 591 = memoRow_591 := by
  have he : entryAt 591 = entry_591 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 591 < 6 by decide, ↓reduceDIte, he, entry_591, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_197, memoRow_eq_524, memoRow_eq_529, memoRow_eq_538]
  apply rowData_ext <;> decide +kernel


def memoRow_592 : RowData := ⟨{(-1, -3), (-1, -2), (-1, -1)}, {(-7, 5), (-7, 6), (-7, 8), (-6, 3), (-6, 5), (-6, 6), (-6, 7), (-6, 8), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-5, 11), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-3, 13), (-2, -6), (-2, -5), (-2, -4), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (0, -6), (0, -5), (0, -4), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (10, 0), (10, 1), (10, 2), (11, 0), (11, 2)}, 28⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_592 : rowAt 592 = memoRow_592 := by
  have he : entryAt 592 = entry_592 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 592 < 6 by decide, ↓reduceDIte, he, entry_592, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_108, memoRow_eq_588]
  apply rowData_ext <;> decide +kernel


def memoRow_593 : RowData := ⟨{(-1, -4), (-1, -3), (0, -3), (0, -1)}, {(-7, 4), (-7, 5), (-7, 7), (-6, 2), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-1, -4), (-1, -3), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (10, -1), (10, 0), (10, 1), (11, -1), (11, 1)}, 27⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_593 : rowAt 593 = memoRow_593 := by
  have he : entryAt 593 = entry_593 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 593 < 6 by decide, ↓reduceDIte, he, entry_593, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_2, memoRow_eq_586]
  apply rowData_ext <;> decide +kernel


def memoRow_594 : RowData := ⟨{(-1, -3), (-1, -2), (-1, -1)}, {(-7, 5), (-7, 6), (-7, 8), (-6, 3), (-6, 5), (-6, 6), (-6, 7), (-6, 8), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-5, 11), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-3, 13), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, -3), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (10, 0), (10, 1), (10, 2), (11, 0), (11, 2)}, 28⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_594 : rowAt 594 = memoRow_594 := by
  have he : entryAt 594 = entry_594 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 594 < 6 by decide, ↓reduceDIte, he, entry_594, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_30, memoRow_eq_476, memoRow_eq_588]
  apply rowData_ext <;> decide +kernel


def memoRow_595 : RowData := ⟨{(-1, 0)}, {(-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, -7), (5, -6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, -7), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (10, -5), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (11, -3), (11, -2), (11, -1), (12, -3), (12, -1)}, 27⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_595 : rowAt 595 = memoRow_595 := by
  have he : entryAt 595 = entry_595 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 595 < 6 by decide, ↓reduceDIte, he, entry_595, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_406, memoRow_eq_411, memoRow_eq_460, memoRow_eq_551, memoRow_eq_572, memoRow_eq_586]
  apply rowData_ext <;> decide +kernel


def memoRow_596 : RowData := ⟨{(0, -1), (0, 1)}, {(-6, 7), (-6, 8), (-6, 10), (-5, 5), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-4, 13), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-2, 13), (-2, 14), (-2, 15), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (-1, 14), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (0, 15), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (11, 2), (11, 3), (11, 4), (12, 2), (12, 4)}, 29⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_596 : rowAt 596 = memoRow_596 := by
  have he : entryAt 596 = entry_596 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 596 < 6 by decide, ↓reduceDIte, he, entry_596, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_330, memoRow_eq_385, memoRow_eq_529, memoRow_eq_592]
  apply rowData_ext <;> decide +kernel


def memoRow_597 : RowData := ⟨{(-1, -1), (-1, 0), (1, 0)}, {(-4, -1), (-4, 1), (-4, 2), (-4, 4), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, -6), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (10, -6), (10, -5), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (12, -4), (12, -3), (12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (13, -4), (13, -2), (13, -1), (13, 0), (13, 1), (13, 2), (13, 3), (13, 4), (14, -2), (14, -1), (14, 0), (15, -2), (15, 0)}, 29⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_597 : rowAt 597 = memoRow_597 := by
  have he : entryAt 597 = entry_597 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 597 < 6 by decide, ↓reduceDIte, he, entry_597, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_24, memoRow_eq_199, memoRow_eq_221, memoRow_eq_594]
  apply rowData_ext <;> decide +kernel


def memoRow_598 : RowData := ⟨{(-3, -2), (-2, -2), (-2, -1), (0, -1), (0, 1)}, {(-6, 7), (-6, 8), (-6, 10), (-5, 5), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-4, 13), (-3, -2), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-2, -2), (-2, -1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-2, 13), (-2, 14), (-2, 15), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (-1, 14), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (0, 15), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (9, -1), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (11, 2), (11, 3), (11, 4), (12, 2), (12, 4)}, 29⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_598 : rowAt 598 = memoRow_598 := by
  have he : entryAt 598 = entry_598 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 598 < 6 by decide, ↓reduceDIte, he, entry_598, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_254, memoRow_eq_456, memoRow_eq_465, memoRow_eq_554, memoRow_eq_594]
  apply rowData_ext <;> decide +kernel


def memoRow_599 : RowData := ⟨{(0, -3), (0, -1), (1, -4), (1, -3)}, {(-11, -1), (-11, 1), (-10, -1), (-10, 0), (-10, 1), (-9, -1), (-9, 0), (-9, 1), (-9, 2), (-9, 3), (-9, 4), (-9, 5), (-8, -2), (-8, -1), (-8, 0), (-8, 1), (-8, 2), (-8, 3), (-8, 4), (-8, 5), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-7, 5), (-7, 6), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (0, -3), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (2, -4), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 7), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (9, -2), (9, 0), (9, 2)}, 27⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_599 : rowAt 599 = memoRow_599 := by
  have he : entryAt 599 = entry_599 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 599 < 6 by decide, ↓reduceDIte, he, entry_599, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_485, memoRow_eq_492, memoRow_eq_512, memoRow_eq_578, memoRow_eq_579, memoRow_eq_586]
  apply rowData_ext <;> decide +kernel


def memoRow_600 : RowData := ⟨{(-2, 0), (-1, 0), (-1, 1)}, {(-5, -1), (-5, 1), (-5, 2), (-5, 4), (-4, -5), (-4, -3), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-2, -8), (-2, -7), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -8), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (0, -8), (0, -7), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, -12), (1, -11), (1, -10), (1, -9), (1, -8), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, -11), (2, -10), (2, -9), (2, -8), (2, -7), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, -12), (3, -11), (3, -10), (3, -9), (3, -8), (3, -7), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, -10), (4, -9), (4, -8), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (5, -10), (5, -9), (5, -8), (5, -7), (5, -6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (6, -10), (6, -9), (6, -8), (6, -7), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (7, -10), (7, -9), (7, -8), (7, -7), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (8, -8), (8, -7), (8, -6), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (9, -7), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (10, -5), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (12, -4), (12, -3), (12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 4), (13, 0), (13, 1), (13, 2), (14, 0), (14, 2)}, 29⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_600 : rowAt 600 = memoRow_600 := by
  have he : entryAt 600 = entry_600 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 600 < 6 by decide, ↓reduceDIte, he, entry_600, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_146, memoRow_eq_278, memoRow_eq_403, memoRow_eq_448, memoRow_eq_592]
  apply rowData_ext <;> decide +kernel


def memoRow_601 : RowData := ⟨{(0, -2), (0, -1)}, {(-9, -3), (-9, -1), (-8, -3), (-8, -2), (-8, -1), (-7, -5), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-6, -5), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 6), (-6, 7), (-6, 9), (-5, -5), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-4, -7), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-3, -7), (-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-2, -7), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-2, 13), (-2, 14), (-1, -5), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (11, 1), (11, 2), (11, 3), (12, 1), (12, 3)}, 29⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_601 : rowAt 601 = memoRow_601 := by
  have he : entryAt 601 = entry_601 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 601 < 6 by decide, ↓reduceDIte, he, entry_601, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_236, memoRow_eq_437, memoRow_eq_469, memoRow_eq_553, memoRow_eq_592]
  apply rowData_ext <;> decide +kernel


def memoRow_602 : RowData := ⟨{(0, 1), (0, 2)}, {(-9, -1), (-9, 1), (-8, -1), (-8, 0), (-8, 1), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-7, 5), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 8), (-6, 9), (-6, 11), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 8), (-5, 9), (-5, 10), (-5, 11), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-4, 13), (-4, 14), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-3, 13), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-2, 13), (-2, 14), (-2, 15), (-2, 16), (-1, -3), (-1, -2), (-1, -1), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (-1, 14), (-1, 15), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (0, 15), (0, 16), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (1, 14), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (3, 14), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (4, 14), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (11, 3), (11, 4), (11, 5), (12, 3), (12, 5)}, 29⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_602 : rowAt 602 = memoRow_602 := by
  have he : entryAt 602 = entry_602 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 602 < 6 by decide, ↓reduceDIte, he, entry_602, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_236, memoRow_eq_437, memoRow_eq_467, memoRow_eq_553, memoRow_eq_592]
  apply rowData_ext <;> decide +kernel


def memoRow_603 : RowData := ⟨{(-1, 0)}, {(-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, -7), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-3, -8), (-3, -7), (-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -8), (-2, -7), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-1, -11), (-1, -10), (-1, -9), (-1, -8), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (0, -10), (0, -9), (0, -8), (0, -7), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (1, -11), (1, -10), (1, -9), (1, -8), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (2, -9), (2, -8), (2, -7), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, -9), (3, -8), (3, -7), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, -9), (4, -8), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (5, -9), (5, -8), (5, -7), (5, -6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (6, -7), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, -7), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (10, -5), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 5), (11, -3), (11, -2), (11, -1), (11, 1), (11, 2), (11, 3), (12, -3), (12, -1), (12, 1), (12, 3)}, 27⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_603 : rowAt 603 = memoRow_603 := by
  have he : entryAt 603 = entry_603 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 603 < 6 by decide, ↓reduceDIte, he, entry_603, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_505, memoRow_eq_531, memoRow_eq_533, memoRow_eq_551, memoRow_eq_573, memoRow_eq_585, memoRow_eq_586]
  apply rowData_ext <;> decide +kernel


def memoRow_604 : RowData := ⟨{(-2, -1), (-2, 0), (-1, -2), (0, -2)}, {(-7, -1), (-6, -1), (-6, 0), (-6, 1), (-6, 6), (-6, 7), (-6, 9), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 4), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-2, -2), (-2, -1), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-2, 13), (-2, 14), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (1, -6), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (12, -4), (12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (13, -2), (13, -1), (13, 0), (14, -2), (14, 0)}, 30⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_604 : rowAt 604 = memoRow_604 := by
  have he : entryAt 604 = entry_604 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 604 < 6 by decide, ↓reduceDIte, he, entry_604, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_350, memoRow_eq_375, memoRow_eq_597]
  apply rowData_ext <;> decide +kernel


def memoRow_605 : RowData := ⟨{(-3, -3), (-2, -3), (-2, -2), (-2, 0), (0, -2)}, {(-7, -1), (-7, 0), (-7, 1), (-7, 2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 6), (-6, 7), (-6, 9), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-3, -3), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-2, -3), (-2, -2), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-2, 13), (-2, 14), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (12, -4), (12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (13, -2), (13, -1), (13, 0), (14, -2), (14, 0)}, 30⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_605 : rowAt 605 = memoRow_605 := by
  have he : entryAt 605 = entry_605 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 605 < 6 by decide, ↓reduceDIte, he, entry_605, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_383, memoRow_eq_400, memoRow_eq_520, memoRow_eq_522, memoRow_eq_530, memoRow_eq_537, memoRow_eq_550, memoRow_eq_596, memoRow_eq_598]
  apply rowData_ext <;> decide +kernel


def memoRow_606 : RowData := ⟨{(-1, -3), (0, -3), (0, -2), (2, -2)}, {(-5, -1), (-5, 0), (-5, 1), (-5, 2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 6), (-4, 7), (-4, 9), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (3, -7), (3, -6), (3, -5), (3, -4), (3, -3), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, -6), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (10, -5), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (11, -6), (11, -5), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (12, -4), (12, -3), (12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (13, -4), (13, -3), (13, -2), (13, -1), (13, 0), (13, 1), (13, 2), (13, 3), (13, 4), (14, -4), (14, -2), (14, -1), (14, 0), (14, 1), (14, 2), (14, 3), (14, 4), (15, -2), (15, -1), (15, 0), (16, -2), (16, 0)}, 31⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_606 : rowAt 606 = memoRow_606 := by
  have he : entryAt 606 = entry_606 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 606 < 6 by decide, ↓reduceDIte, he, entry_606, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_119, memoRow_eq_123, memoRow_eq_274, memoRow_eq_605]
  apply rowData_ext <;> decide +kernel


def memoRow_607 : RowData := ⟨{(-1, -2), (0, -3), (0, -2), (0, -1)}, {(-7, -1), (-7, 0), (-7, 1), (-7, 2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 6), (-6, 7), (-6, 9), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 4), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-2, 13), (-2, 14), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (5, -8), (5, -7), (5, -6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, -7), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (7, -8), (7, -7), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (8, -6), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (10, -6), (10, -5), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (11, -5), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (12, -4), (12, -3), (12, -2), (12, -1), (12, 0), (12, 1), (12, 3), (13, -4), (13, -3), (13, -2), (13, -1), (13, 0), (13, 1)}, 29⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_607 : rowAt 607 = memoRow_607 := by
  have he : entryAt 607 = entry_607 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 607 < 6 by decide, ↓reduceDIte, he, entry_607, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_314, memoRow_eq_419, memoRow_eq_420, memoRow_eq_571, memoRow_eq_589]
  apply rowData_ext <;> decide +kernel


def memoRow_608 : RowData := ⟨{(-1, -3), (-1, -2), (0, -2)}, {(-9, -1), (-9, 1), (-9, 3), (-8, -1), (-8, 0), (-8, 1), (-8, 2), (-8, 3), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-7, 5), (-7, 6), (-7, 8), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-6, 8), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-5, 11), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-3, 13), (-2, -3), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (2, -7), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (3, -7), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (5, -6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, -6), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (10, -5), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (11, -6), (11, -5), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (12, -4), (12, -3), (12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (13, -4), (13, -3), (13, -2), (13, -1), (13, 0), (13, 1), (13, 2), (13, 3), (13, 4), (14, -4), (14, -2), (14, -1), (14, 0), (14, 1), (14, 2), (14, 3), (14, 4), (15, -2), (15, -1), (15, 0), (16, -2), (16, 0)}, 32⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_608 : rowAt 608 = memoRow_608 := by
  have he : entryAt 608 = entry_608 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 608 < 6 by decide, ↓reduceDIte, he, entry_608, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_486, memoRow_eq_515, memoRow_eq_521, memoRow_eq_580, memoRow_eq_581, memoRow_eq_593, memoRow_eq_599, memoRow_eq_606]
  apply rowData_ext <;> decide +kernel


def memoRow_609 : RowData := ⟨{(0, -2), (0, -1), (1, -2), (2, -2)}, {(-10, -2), (-10, -1), (-10, 0), (-10, 1), (-9, -2), (-9, -1), (-9, 0), (-9, 1), (-8, -2), (-8, -1), (-8, 0), (-8, 1), (-8, 2), (-8, 4), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-7, 5), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 6), (-4, 7), (-4, 9), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (3, -6), (3, -5), (3, -4), (3, -3), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, -6), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (10, -5), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (11, -6), (11, -5), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (12, -4), (12, -3), (12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (13, -4), (13, -3), (13, -2), (13, -1), (13, 0), (13, 1), (13, 2), (13, 3), (13, 4), (14, -4), (14, -2), (14, -1), (14, 0), (14, 1), (14, 2), (14, 3), (14, 4), (15, -2), (15, -1), (15, 0), (16, -2), (16, 0)}, 31⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_609 : rowAt 609 = memoRow_609 := by
  have he : entryAt 609 = entry_609 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 609 < 6 by decide, ↓reduceDIte, he, entry_609, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_107, memoRow_eq_221, memoRow_eq_286, memoRow_eq_532, memoRow_eq_542, memoRow_eq_562, memoRow_eq_575, memoRow_eq_604]
  apply rowData_ext <;> decide +kernel


def memoRow_610 : RowData := ⟨{(-2, 0), (-2, 1), (-1, 0)}, {(-12, 0), (-12, 1), (-12, 2), (-12, 3), (-11, 0), (-11, 1), (-11, 2), (-11, 3), (-10, 0), (-10, 1), (-10, 2), (-10, 3), (-10, 4), (-10, 6), (-9, -2), (-9, -1), (-9, 0), (-9, 1), (-9, 2), (-9, 3), (-9, 4), (-9, 5), (-9, 6), (-9, 7), (-8, -2), (-8, -1), (-8, 0), (-8, 1), (-8, 2), (-8, 3), (-8, 4), (-8, 5), (-8, 6), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-7, 5), (-7, 6), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 8), (-6, 9), (-6, 11), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-5, 11), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-4, 13), (-4, 14), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-3, 13), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-2, 13), (-2, 14), (-2, 15), (-2, 16), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (-1, 14), (-1, 15), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (0, 15), (0, 16), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (1, 14), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (3, 14), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (4, 14), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (12, -2), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (13, 0), (13, 1), (13, 2), (14, 0), (14, 2)}, 32⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_610 : rowAt 610 = memoRow_610 := by
  have he : entryAt 610 = entry_610 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 610 < 6 by decide, ↓reduceDIte, he, entry_610, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_107, memoRow_eq_221, memoRow_eq_286, memoRow_eq_472, memoRow_eq_532, memoRow_eq_542, memoRow_eq_566, memoRow_eq_609]
  apply rowData_ext <;> decide +kernel


def memoRow_611 : RowData := ⟨{(-2, 0), (-1, 0)}, {(-16, 0), (-16, 2), (-15, 0), (-15, 1), (-15, 2), (-14, -4), (-14, -3), (-14, -2), (-14, -1), (-14, 0), (-14, 1), (-14, 2), (-14, 4), (-13, -4), (-13, -3), (-13, -2), (-13, -1), (-13, 0), (-13, 1), (-13, 2), (-13, 3), (-13, 4), (-12, -5), (-12, -4), (-12, -3), (-12, -2), (-12, -1), (-12, 0), (-12, 1), (-12, 2), (-12, 3), (-12, 4), (-11, -7), (-11, -6), (-11, -5), (-11, -4), (-11, -3), (-11, -2), (-11, -1), (-11, 0), (-11, 1), (-11, 2), (-11, 3), (-11, 4), (-11, 5), (-11, 6), (-10, -8), (-10, -7), (-10, -6), (-10, -5), (-10, -4), (-10, -3), (-10, -2), (-10, -1), (-10, 0), (-10, 1), (-10, 2), (-10, 3), (-10, 4), (-10, 5), (-9, -10), (-9, -9), (-9, -8), (-9, -7), (-9, -6), (-9, -5), (-9, -4), (-9, -3), (-9, -2), (-9, -1), (-9, 0), (-9, 1), (-9, 2), (-9, 3), (-9, 4), (-9, 5), (-9, 6), (-8, -10), (-8, -9), (-8, -8), (-8, -7), (-8, -6), (-8, -5), (-8, -4), (-8, -3), (-8, -2), (-8, -1), (-8, 0), (-8, 1), (-8, 2), (-8, 3), (-8, 4), (-8, 5), (-8, 6), (-7, -10), (-7, -9), (-7, -8), (-7, -7), (-7, -6), (-7, -5), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-6, -10), (-6, -9), (-6, -8), (-6, -7), (-6, -6), (-6, -5), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-5, -12), (-5, -11), (-5, -10), (-5, -9), (-5, -8), (-5, -7), (-5, -6), (-5, -5), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, -11), (-4, -10), (-4, -9), (-4, -8), (-4, -7), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-3, -12), (-3, -11), (-3, -10), (-3, -9), (-3, -8), (-3, -7), (-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-2, -9), (-2, -8), (-2, -7), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-1, -8), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -9), (0, -8), (0, -7), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (12, -4), (12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (13, -2), (13, -1), (13, 0), (14, -2), (14, 0)}, 29⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_611 : rowAt 611 = memoRow_611 := by
  have he : entryAt 611 = entry_611 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 611 < 6 by decide, ↓reduceDIte, he, entry_611, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_456, memoRow_eq_594]
  apply rowData_ext <;> decide +kernel


def memoRow_612 : RowData := ⟨{(-3, 0), (-2, 0), (-1, 0)}, {(-17, 0), (-17, 2), (-16, 0), (-16, 1), (-16, 2), (-15, -4), (-15, -3), (-15, -2), (-15, -1), (-15, 0), (-15, 1), (-15, 2), (-15, 4), (-14, -4), (-14, -3), (-14, -2), (-14, -1), (-14, 0), (-14, 1), (-14, 2), (-14, 3), (-14, 4), (-13, -5), (-13, -4), (-13, -3), (-13, -2), (-13, -1), (-13, 0), (-13, 1), (-13, 2), (-13, 3), (-13, 4), (-12, -7), (-12, -6), (-12, -5), (-12, -4), (-12, -3), (-12, -2), (-12, -1), (-12, 0), (-12, 1), (-12, 2), (-12, 3), (-12, 4), (-12, 5), (-12, 6), (-11, -8), (-11, -7), (-11, -6), (-11, -5), (-11, -4), (-11, -3), (-11, -2), (-11, -1), (-11, 0), (-11, 1), (-11, 2), (-11, 3), (-11, 4), (-11, 5), (-10, -10), (-10, -9), (-10, -8), (-10, -7), (-10, -6), (-10, -5), (-10, -4), (-10, -3), (-10, -2), (-10, -1), (-10, 0), (-10, 1), (-10, 2), (-10, 3), (-10, 4), (-10, 5), (-10, 6), (-9, -10), (-9, -9), (-9, -8), (-9, -7), (-9, -6), (-9, -5), (-9, -4), (-9, -3), (-9, -2), (-9, -1), (-9, 0), (-9, 1), (-9, 2), (-9, 3), (-9, 4), (-9, 5), (-9, 6), (-8, -10), (-8, -9), (-8, -8), (-8, -7), (-8, -6), (-8, -5), (-8, -4), (-8, -3), (-8, -2), (-8, -1), (-8, 0), (-8, 1), (-8, 2), (-8, 3), (-8, 4), (-7, -10), (-7, -9), (-7, -8), (-7, -7), (-7, -6), (-7, -5), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-7, 5), (-6, -12), (-6, -11), (-6, -10), (-6, -9), (-6, -8), (-6, -7), (-6, -6), (-6, -5), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-5, -11), (-5, -10), (-5, -9), (-5, -8), (-5, -7), (-5, -6), (-5, -5), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-4, -12), (-4, -11), (-4, -10), (-4, -9), (-4, -8), (-4, -7), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 3), (-4, 5), (-3, -8), (-3, -7), (-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-2, -8), (-2, -7), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -8), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -5), (0, -4), (0, -3), (0, -2), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -5), (1, -3), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (12, -4), (12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (13, -2), (13, -1), (13, 0), (14, -2), (14, 0)}, 29⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_612 : rowAt 612 = memoRow_612 := by
  have he : entryAt 612 = entry_612 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 612 < 6 by decide, ↓reduceDIte, he, entry_612, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_589]
  apply rowData_ext <;> decide +kernel


def memoRow_613 : RowData := ⟨{(-2, 0), (-1, 0), (-1, 1)}, {(-17, -2), (-17, 0), (-17, 2), (-16, -2), (-16, -1), (-16, 0), (-16, 1), (-16, 2), (-15, -4), (-15, -3), (-15, -2), (-15, -1), (-15, 0), (-15, 1), (-15, 2), (-15, 3), (-15, 4), (-14, -4), (-14, -3), (-14, -2), (-14, -1), (-14, 0), (-14, 1), (-14, 2), (-14, 3), (-14, 4), (-13, -5), (-13, -4), (-13, -3), (-13, -2), (-13, -1), (-13, 0), (-13, 1), (-13, 2), (-13, 3), (-13, 4), (-13, 5), (-12, -7), (-12, -6), (-12, -5), (-12, -4), (-12, -3), (-12, -2), (-12, -1), (-12, 0), (-12, 1), (-12, 2), (-12, 3), (-12, 4), (-12, 5), (-12, 6), (-12, 7), (-11, -8), (-11, -7), (-11, -6), (-11, -5), (-11, -4), (-11, -3), (-11, -2), (-11, -1), (-11, 0), (-11, 1), (-11, 2), (-11, 3), (-11, 4), (-11, 5), (-11, 6), (-11, 7), (-11, 8), (-10, -10), (-10, -9), (-10, -8), (-10, -7), (-10, -6), (-10, -5), (-10, -4), (-10, -3), (-10, -2), (-10, -1), (-10, 0), (-10, 1), (-10, 2), (-10, 3), (-10, 4), (-10, 5), (-10, 6), (-10, 7), (-10, 8), (-10, 9), (-10, 10), (-9, -10), (-9, -9), (-9, -8), (-9, -7), (-9, -6), (-9, -5), (-9, -4), (-9, -3), (-9, -2), (-9, -1), (-9, 0), (-9, 1), (-9, 2), (-9, 3), (-9, 4), (-9, 5), (-9, 6), (-9, 7), (-9, 8), (-9, 9), (-9, 10), (-8, -10), (-8, -9), (-8, -8), (-8, -7), (-8, -6), (-8, -5), (-8, -4), (-8, -3), (-8, -2), (-8, -1), (-8, 0), (-8, 1), (-8, 2), (-8, 3), (-8, 4), (-8, 5), (-8, 6), (-8, 7), (-8, 8), (-8, 9), (-8, 10), (-7, -10), (-7, -9), (-7, -8), (-7, -7), (-7, -6), (-7, -5), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-7, 5), (-7, 6), (-7, 7), (-7, 8), (-7, 9), (-7, 10), (-6, -12), (-6, -11), (-6, -10), (-6, -9), (-6, -8), (-6, -7), (-6, -6), (-6, -5), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-6, 8), (-6, 9), (-6, 10), (-6, 11), (-6, 12), (-5, -12), (-5, -11), (-5, -10), (-5, -9), (-5, -8), (-5, -7), (-5, -6), (-5, -5), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-5, 11), (-4, -13), (-4, -12), (-4, -11), (-4, -10), (-4, -9), (-4, -8), (-4, -7), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-3, -13), (-3, -12), (-3, -11), (-3, -10), (-3, -9), (-3, -8), (-3, -7), (-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-2, -13), (-2, -12), (-2, -11), (-2, -10), (-2, -9), (-2, -8), (-2, -7), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-1, -13), (-1, -12), (-1, -11), (-1, -10), (-1, -9), (-1, -8), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (0, -13), (0, -12), (0, -11), (0, -10), (0, -9), (0, -8), (0, -7), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, -13), (1, -12), (1, -11), (1, -10), (1, -9), (1, -8), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, -13), (2, -12), (2, -11), (2, -10), (2, -9), (2, -8), (2, -7), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (3, -12), (3, -11), (3, -10), (3, -9), (3, -8), (3, -7), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (4, -12), (4, -11), (4, -10), (4, -9), (4, -8), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (5, -10), (5, -9), (5, -8), (5, -7), (5, -6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (6, -10), (6, -9), (6, -8), (6, -7), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, -10), (7, -9), (7, -8), (7, -7), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (8, -10), (8, -9), (8, -8), (8, -7), (8, -6), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (9, -8), (9, -7), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (10, -7), (10, -6), (10, -5), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (11, -5), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (12, -4), (12, -3), (12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (13, -4), (13, -3), (13, -2), (13, -1), (13, 0), (13, 1), (13, 2), (13, 3), (13, 4), (14, -2), (14, -1), (14, 0), (14, 1), (14, 2), (15, -2), (15, 0), (15, 2)}, 30⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_613 : rowAt 613 = memoRow_613 := by
  have he : entryAt 613 = entry_613 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 613 < 6 by decide, ↓reduceDIte, he, entry_613, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_503, memoRow_eq_592, memoRow_eq_607, memoRow_eq_612]
  apply rowData_ext <;> decide +kernel


def memoRow_614 : RowData := ⟨{(1, 0), (1, 1)}, {(-15, -2), (-15, 0), (-15, 2), (-14, -2), (-14, -1), (-14, 0), (-14, 1), (-14, 2), (-13, -4), (-13, -3), (-13, -2), (-13, -1), (-13, 0), (-13, 1), (-13, 2), (-13, 3), (-13, 4), (-13, 5), (-13, 6), (-12, -4), (-12, -3), (-12, -2), (-12, -1), (-12, 0), (-12, 1), (-12, 2), (-12, 3), (-12, 4), (-12, 5), (-12, 6), (-11, -5), (-11, -4), (-11, -3), (-11, -2), (-11, -1), (-11, 0), (-11, 1), (-11, 2), (-11, 3), (-11, 4), (-11, 5), (-11, 6), (-11, 7), (-11, 8), (-11, 9), (-10, -7), (-10, -6), (-10, -5), (-10, -4), (-10, -3), (-10, -2), (-10, -1), (-10, 0), (-10, 1), (-10, 2), (-10, 3), (-10, 4), (-10, 5), (-10, 6), (-10, 7), (-10, 8), (-10, 9), (-9, -8), (-9, -7), (-9, -6), (-9, -5), (-9, -4), (-9, -3), (-9, -2), (-9, -1), (-9, 0), (-9, 1), (-9, 2), (-9, 3), (-9, 4), (-9, 5), (-9, 6), (-9, 7), (-9, 8), (-9, 9), (-9, 10), (-8, -10), (-8, -9), (-8, -8), (-8, -7), (-8, -6), (-8, -5), (-8, -4), (-8, -3), (-8, -2), (-8, -1), (-8, 0), (-8, 1), (-8, 2), (-8, 3), (-8, 4), (-8, 5), (-8, 6), (-8, 7), (-8, 8), (-8, 9), (-8, 10), (-8, 11), (-8, 12), (-7, -10), (-7, -9), (-7, -8), (-7, -7), (-7, -6), (-7, -5), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-7, 5), (-7, 6), (-7, 7), (-7, 8), (-7, 9), (-7, 10), (-7, 11), (-7, 12), (-6, -10), (-6, -9), (-6, -8), (-6, -7), (-6, -6), (-6, -5), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-6, 8), (-6, 9), (-6, 10), (-6, 11), (-6, 12), (-5, -10), (-5, -9), (-5, -8), (-5, -7), (-5, -6), (-5, -5), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-5, 11), (-5, 12), (-5, 13), (-5, 14), (-4, -12), (-4, -11), (-4, -10), (-4, -9), (-4, -8), (-4, -7), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-4, 13), (-4, 14), (-3, -12), (-3, -11), (-3, -10), (-3, -9), (-3, -8), (-3, -7), (-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-3, 13), (-3, 14), (-2, -13), (-2, -12), (-2, -11), (-2, -10), (-2, -9), (-2, -8), (-2, -7), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-2, 13), (-2, 14), (-1, -13), (-1, -12), (-1, -11), (-1, -10), (-1, -9), (-1, -8), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (-1, 14), (-1, 15), (-1, 16), (0, -13), (0, -12), (0, -11), (0, -10), (0, -9), (0, -8), (0, -7), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (0, 15), (1, -13), (1, -12), (1, -11), (1, -10), (1, -9), (1, -8), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (1, 14), (1, 15), (1, 16), (1, 17), (2, -13), (2, -12), (2, -11), (2, -10), (2, -9), (2, -8), (2, -7), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (2, 15), (2, 16), (3, -13), (3, -12), (3, -11), (3, -10), (3, -9), (3, -8), (3, -7), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (3, 14), (3, 15), (3, 16), (3, 17), (4, -13), (4, -12), (4, -11), (4, -10), (4, -9), (4, -8), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (4, 14), (4, 15), (5, -12), (5, -11), (5, -10), (5, -9), (5, -8), (5, -7), (5, -6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (5, 14), (5, 15), (6, -12), (6, -11), (6, -10), (6, -9), (6, -8), (6, -7), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (6, 14), (6, 15), (7, -10), (7, -9), (7, -8), (7, -7), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (7, 14), (7, 15), (8, -10), (8, -9), (8, -8), (8, -7), (8, -6), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (9, -10), (9, -9), (9, -8), (9, -7), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (9, 12), (9, 13), (10, -10), (10, -9), (10, -8), (10, -7), (10, -6), (10, -5), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (10, 10), (10, 11), (10, 12), (10, 13), (11, -8), (11, -7), (11, -6), (11, -5), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (11, 8), (11, 9), (11, 10), (11, 11), (12, -7), (12, -6), (12, -5), (12, -4), (12, -3), (12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (12, 8), (12, 9), (12, 10), (13, -5), (13, -4), (13, -3), (13, -2), (13, -1), (13, 0), (13, 1), (13, 2), (13, 3), (13, 4), (13, 5), (13, 6), (13, 7), (13, 8), (13, 9), (13, 10), (14, -4), (14, -3), (14, -2), (14, -1), (14, 0), (14, 1), (14, 2), (14, 3), (14, 4), (14, 5), (14, 6), (14, 7), (15, -4), (15, -3), (15, -2), (15, -1), (15, 0), (15, 1), (15, 2), (15, 3), (15, 4), (15, 5), (15, 6), (15, 7), (16, -2), (16, -1), (16, 0), (16, 1), (16, 2), (16, 3), (17, -2), (17, 0), (17, 1), (17, 2), (17, 3)}, 33⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_614 : rowAt 614 = memoRow_614 := by
  have he : entryAt 614 = entry_614 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 614 < 6 by decide, ↓reduceDIte, he, entry_614, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_370, memoRow_eq_392, memoRow_eq_543, memoRow_eq_600, memoRow_eq_608, memoRow_eq_610, memoRow_eq_613]
  apply rowData_ext <;> decide +kernel


def memoRow_615 : RowData := ⟨{(1, 0)}, {(-15, 0), (-15, 2), (-14, 0), (-14, 1), (-14, 2), (-13, -4), (-13, -3), (-13, -2), (-13, -1), (-13, 0), (-13, 1), (-13, 2), (-13, 3), (-13, 4), (-12, -5), (-12, -4), (-12, -3), (-12, -2), (-12, -1), (-12, 0), (-12, 1), (-12, 2), (-12, 3), (-12, 4), (-12, 5), (-11, -5), (-11, -4), (-11, -3), (-11, -2), (-11, -1), (-11, 0), (-11, 1), (-11, 2), (-11, 3), (-11, 4), (-11, 5), (-10, -9), (-10, -8), (-10, -7), (-10, -6), (-10, -5), (-10, -4), (-10, -3), (-10, -2), (-10, -1), (-10, 0), (-10, 1), (-10, 2), (-10, 3), (-10, 4), (-10, 5), (-10, 6), (-10, 7), (-10, 8), (-10, 9), (-9, -9), (-9, -8), (-9, -7), (-9, -6), (-9, -5), (-9, -4), (-9, -3), (-9, -2), (-9, -1), (-9, 0), (-9, 1), (-9, 2), (-9, 3), (-9, 4), (-9, 5), (-9, 6), (-9, 7), (-9, 8), (-9, 9), (-8, -10), (-8, -9), (-8, -8), (-8, -7), (-8, -6), (-8, -5), (-8, -4), (-8, -3), (-8, -2), (-8, -1), (-8, 0), (-8, 1), (-8, 2), (-8, 3), (-8, 4), (-8, 5), (-8, 6), (-8, 7), (-8, 8), (-8, 9), (-8, 10), (-7, -11), (-7, -10), (-7, -9), (-7, -8), (-7, -7), (-7, -6), (-7, -5), (-7, -4), (-7, -3), (-7, -2), (-7, -1), (-7, 0), (-7, 1), (-7, 2), (-7, 3), (-7, 4), (-7, 5), (-7, 6), (-7, 7), (-7, 8), (-7, 9), (-7, 10), (-7, 11), (-6, -11), (-6, -10), (-6, -9), (-6, -8), (-6, -7), (-6, -6), (-6, -5), (-6, -4), (-6, -3), (-6, -2), (-6, -1), (-6, 0), (-6, 1), (-6, 2), (-6, 3), (-6, 4), (-6, 5), (-6, 6), (-6, 7), (-6, 8), (-6, 9), (-6, 10), (-6, 11), (-5, -12), (-5, -11), (-5, -10), (-5, -9), (-5, -8), (-5, -7), (-5, -6), (-5, -5), (-5, -4), (-5, -3), (-5, -2), (-5, -1), (-5, 0), (-5, 1), (-5, 2), (-5, 3), (-5, 4), (-5, 5), (-5, 6), (-5, 7), (-5, 8), (-5, 9), (-5, 10), (-5, 11), (-5, 12), (-4, -14), (-4, -13), (-4, -12), (-4, -11), (-4, -10), (-4, -9), (-4, -8), (-4, -7), (-4, -6), (-4, -5), (-4, -4), (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-4, 3), (-4, 4), (-4, 5), (-4, 6), (-4, 7), (-4, 8), (-4, 9), (-4, 10), (-4, 11), (-4, 12), (-4, 13), (-4, 14), (-3, -14), (-3, -13), (-3, -12), (-3, -11), (-3, -10), (-3, -9), (-3, -8), (-3, -7), (-3, -6), (-3, -5), (-3, -4), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-3, 4), (-3, 5), (-3, 6), (-3, 7), (-3, 8), (-3, 9), (-3, 10), (-3, 11), (-3, 12), (-3, 13), (-3, 14), (-2, -16), (-2, -15), (-2, -14), (-2, -13), (-2, -12), (-2, -11), (-2, -10), (-2, -9), (-2, -8), (-2, -7), (-2, -6), (-2, -5), (-2, -4), (-2, -3), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-2, 3), (-2, 4), (-2, 5), (-2, 6), (-2, 7), (-2, 8), (-2, 9), (-2, 10), (-2, 11), (-2, 12), (-2, 13), (-2, 14), (-2, 15), (-2, 16), (-1, -15), (-1, -14), (-1, -13), (-1, -12), (-1, -11), (-1, -10), (-1, -9), (-1, -8), (-1, -7), (-1, -6), (-1, -5), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6), (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12), (-1, 13), (-1, 14), (-1, 15), (0, -16), (0, -15), (0, -14), (0, -13), (0, -12), (0, -11), (0, -10), (0, -9), (0, -8), (0, -7), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13), (0, 14), (0, 15), (0, 16), (1, -15), (1, -14), (1, -13), (1, -12), (1, -11), (1, -10), (1, -9), (1, -8), (1, -7), (1, -6), (1, -5), (1, -4), (1, -3), (1, -2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10), (1, 11), (1, 12), (1, 13), (1, 14), (1, 15), (1, 16), (2, -16), (2, -15), (2, -14), (2, -13), (2, -12), (2, -11), (2, -10), (2, -9), (2, -8), (2, -7), (2, -6), (2, -5), (2, -4), (2, -3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11), (2, 12), (2, 13), (2, 14), (2, 15), (2, 16), (3, -14), (3, -13), (3, -12), (3, -11), (3, -10), (3, -9), (3, -8), (3, -7), (3, -6), (3, -5), (3, -4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11), (3, 12), (3, 13), (3, 14), (3, 15), (3, 16), (4, -14), (4, -13), (4, -12), (4, -11), (4, -10), (4, -9), (4, -8), (4, -7), (4, -6), (4, -5), (4, -4), (4, -3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13), (4, 14), (5, -14), (5, -13), (5, -12), (5, -11), (5, -10), (5, -9), (5, -8), (5, -7), (5, -6), (5, -5), (5, -4), (5, -3), (5, -2), (5, -1), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (5, 14), (6, -14), (6, -13), (6, -12), (6, -11), (6, -10), (6, -9), (6, -8), (6, -7), (6, -6), (6, -5), (6, -4), (6, -3), (6, -2), (6, -1), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (6, 14), (7, -12), (7, -11), (7, -10), (7, -9), (7, -8), (7, -7), (7, -6), (7, -5), (7, -4), (7, -3), (7, -2), (7, -1), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13), (7, 14), (8, -12), (8, -11), (8, -10), (8, -9), (8, -8), (8, -7), (8, -6), (8, -5), (8, -4), (8, -3), (8, -2), (8, -1), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7), (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (9, -12), (9, -11), (9, -10), (9, -9), (9, -8), (9, -7), (9, -6), (9, -5), (9, -4), (9, -3), (9, -2), (9, -1), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (9, 12), (10, -10), (10, -9), (10, -8), (10, -7), (10, -6), (10, -5), (10, -4), (10, -3), (10, -2), (10, -1), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (10, 10), (10, 11), (10, 12), (11, -9), (11, -8), (11, -7), (11, -6), (11, -5), (11, -4), (11, -3), (11, -2), (11, -1), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7), (11, 8), (11, 9), (11, 10), (12, -9), (12, -8), (12, -7), (12, -6), (12, -5), (12, -4), (12, -3), (12, -2), (12, -1), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (12, 8), (12, 9), (13, -6), (13, -5), (13, -4), (13, -3), (13, -2), (13, -1), (13, 0), (13, 1), (13, 2), (13, 3), (13, 4), (13, 5), (13, 6), (13, 7), (13, 8), (13, 9), (14, -6), (14, -5), (14, -4), (14, -3), (14, -2), (14, -1), (14, 0), (14, 1), (14, 2), (14, 3), (14, 4), (14, 5), (14, 6), (15, -2), (15, -1), (15, 0), (15, 1), (15, 2), (15, 3), (15, 4), (15, 5), (15, 6), (16, -2), (16, 0), (16, 1), (16, 2), (17, 0), (17, 2)}, 34⟩

set_option maxHeartbeats 0 in
lemma memoRow_eq_615 : rowAt 615 = memoRow_615 := by
  have he : entryAt 615 = entry_615 := by
    simp only [entryAt, table, Array.getElem?_append, Array.size_append, tableChunk_size_0, tableChunk_size_1, tableChunk_size_2, tableChunk_size_3, tableChunk_size_4, tableChunk_size_5, tableChunk_size_6, tableChunk_size_7, tableChunk_size_8, tableChunk_size_9, tableChunk_size_10, tableChunk_size_11, tableChunk_size_12, tableChunk_size_13, tableChunk_size_14, tableChunk_size_15, tableChunk_size_16, tableChunk_size_17, tableChunk_size_18, tableChunk_size_19, tableChunk_size_20, tableChunk_size_21, tableChunk_size_22, tableChunk_size_23, tableChunk_size_24, tableChunk_size_25, tableChunk_size_26, tableChunk_size_27, tableChunk_size_28, tableChunk_size_29, tableChunk_size_30, Nat.reduceSub, Nat.reduceLT, ite_true, ite_false]
    rfl
  rw [rowAt]
  simp only [show ¬ 615 < 6 by decide, ↓reduceDIte, he, entry_615, List.map_cons, List.map_nil]
  simp only [Nat.reduceLT, dite_true]
  rw [memoRow_eq_406, memoRow_eq_533, memoRow_eq_584, memoRow_eq_586, memoRow_eq_587, memoRow_eq_590, memoRow_eq_591, memoRow_eq_601, memoRow_eq_602, memoRow_eq_611, memoRow_eq_614]
  apply rowData_ext <;> decide +kernel



end OAI.SnakyCertificate
