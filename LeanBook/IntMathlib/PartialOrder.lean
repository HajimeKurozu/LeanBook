import LeanBook.IntMathlib.PreOrder

@[simp ↓]
theorem MyInt.add_right_eq_self {a b : MyInt} : a + b = a ↔ b = 0 := by
  constructor <;> intro h
  case mp => calc
    _ = b := by rfl
    _ = a + b - a := by abel
    _ = a - a := by rw [h]
    _ = 0 := by abel
  case mpr =>
    simp [h]

theorem MyInt.le_antisymm (a b : MyInt) (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  notation_simp at *
  obtain ⟨m, hm⟩ := h1
  obtain ⟨n, hn⟩ := h2
  have : a + (↑ m + ↑ n) = a := calc
    _ = a + ↑ m + ↑ n := by ac_rfl
    _ = b + ↑ n := by rw [hm]
    _ = a := by rw [hn]
  replace : ↑ (m + n) = (0 : MyInt) := by
    push_cast
    simp_all
  have ⟨mz, nz⟩ : m = 0 ∧ n = 0 := by
    simp_all
  simp_all

instance : PartialOrder MyInt where
  le_antisymm := by apply MyInt.le_antisymm

example (a b : MyInt) (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  order

example {a b : MyInt} (h : a = b ∨ a < b) : a ≤ b := by
  cases h with
  | inl h => rw [h]
  | inr h => order
