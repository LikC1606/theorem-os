namespace WidthFive

def inside : Vertex → Prop
  | .up _ j => 0 ≤ j ∧ j < 5
  | .down _ j => 0 ≤ j ∧ j < 5

lemma inside_iff (v : Vertex) : inside v ↔ 0 ≤ layer v ∧ layer v < 5 := by
  cases v <;> rfl

instance (v : Vertex) : Decidable (inside v) := by
  cases v <;> unfold inside <;> infer_instance

def rawNeighbors : Vertex → Finset Vertex
  | .up i j => {.down i (j-1), .down i j, .down (i-1) j}
  | .down i j => {.up i (j+1), .up i j, .up (i+1) j}

def neighbors (v : Vertex) : Finset Vertex := (rawNeighbors v).filter inside

lemma mem_neighbors {a b : Vertex} :
    b ∈ neighbors a ↔ adjacent a b ∧ inside b := by
  cases a <;> cases b <;>
    simp [neighbors, rawNeighbors, adjacent, inside, Vertex.up.injEq, Vertex.down.injEq] <;> omega

def shift (t : ℤ) : Vertex → Vertex
  | .up i j => .up (t+i) j
  | .down i j => .down (t+i) j

lemma shift_injective (t : ℤ) : Function.Injective (shift t) := by
  intro a b he
  cases a <;> cases b <;>
    simp [shift, Vertex.up.injEq, Vertex.down.injEq] at he ⊢ <;> tauto

@[simp] lemma inside_shift (t : ℤ) (v : Vertex) : inside (shift t v) ↔ inside v := by
  cases v <;> rfl

lemma neighbors_shift (t : ℤ) (b : Vertex) :
    neighbors (shift t b) = (neighbors b).image (shift t) := by
  have hr : rawNeighbors (shift t b) = (rawNeighbors b).image (shift t) := by
    cases b <;> simp [rawNeighbors, shift, add_sub_assoc, add_assoc]
  simp only [neighbors, hr, Finset.filter_image, inside_shift]

def last (w : List Vertex) : Vertex := w.getLastD (.up 0 0)

lemma last_eq_getLast {w : List Vertex} (hne : w ≠ []) :
    last w = w.getLast hne := by
  simp [last, List.getLast?_eq_some_getLast hne]

lemma last_shift (t : ℤ) {w : List Vertex} (hne : w ≠ []) :
    last (w.map (shift t)) = shift t (last w) := by
  simp [last, List.getLast?_map, List.getLast?_eq_some_getLast hne]

def horizontal : Vertex → ℤ
  | .up i _ => i
  | .down i _ => i

def origin (w : List Vertex) : ℤ := horizontal (last w)

def normalize (w : List Vertex) : List Vertex := w.map (shift (-origin w))

lemma normalize_shift (t : ℤ) {w : List Vertex} (hne : w ≠ []) :
    normalize (w.map (shift t)) = normalize w := by
  have ho : origin (w.map (shift t)) = t + origin w := by
    unfold origin
    rw [last_shift t hne]
    cases last w <;> rfl
  simp only [normalize, ho, List.map_map]
  apply List.map_congr_left
  intro v _
  cases v <;> simp [shift]

def candidates (w : List Vertex) : Finset Vertex :=
  (neighbors (last w)).filter (fun c => c ∉ w)

lemma candidates_shift (t : ℤ) {w : List Vertex} (hne : w ≠ []) :
    candidates (w.map (shift t)) = (candidates w).image (shift t) := by
  rw [candidates, last_shift t hne, neighbors_shift]
  ext v
  constructor
  · intro h
    obtain ⟨hin,hnot⟩ := Finset.mem_filter.mp h
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hin
    apply Finset.mem_image.mpr
    refine ⟨c, Finset.mem_filter.mpr ⟨hc, ?_⟩, rfl⟩
    intro hcw
    exact hnot (List.mem_map_of_mem hcw)
  · intro h
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hin,hnot⟩ := Finset.mem_filter.mp hc
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨c,hin,rfl⟩, ?_⟩
    intro hcw
    obtain ⟨d,hd,hde⟩ := List.mem_map.mp hcw
    exact hnot ((shift_injective t hde) ▸ hd)

def slide (w : List Vertex) (c : Vertex) : List Vertex :=
  (if w.length < 6 then w else w.tail) ++ [c]

lemma slide_ne_nil (w : List Vertex) (c : Vertex) : slide w c ≠ [] := by
  simp [slide]

lemma slide_shift (t : ℤ) (w : List Vertex) (c : Vertex) :
    slide (w.map (shift t)) (shift t c) = (slide w c).map (shift t) := by
  simp only [slide, List.length_map]
  split_ifs <;> simp [List.map_append]

def count (w : List Vertex) : ℕ → ℕ
  | 0 => 1
  | n+1 => ∑ c ∈ candidates w, count (slide w c) n

lemma count_shift (t : ℤ) (n : ℕ) (w : List Vertex) (hne : w ≠ []) :
    count (w.map (shift t)) n = count w n := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    rw [count, candidates_shift t hne, Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro c _
      rw [slide_shift]
      exact ih _ (slide_ne_nil w c)
    · intro c hc d hd he
      exact shift_injective t he

