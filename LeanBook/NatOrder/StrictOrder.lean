import LeanBook.NatOrder.OrderDef

def MyNat.lt (m n : MyNat) : Prop := (m + 1) ≤ n
instance : LT MyNat where
  lt := MyNat.lt

example (m n : MyNat) : m < n ↔ (m + 1) ≤ n := by
  dsimp [(· < ·), MyNat.lt]
  rfl

@[simp] theorem MyNat.one_neq_zero : 1 ≠ 0 := by
  intro h
  injection h

@[simp] theorem MyNat.zero_neq_one : 0 ≠ 1 := by
  intro h
  injection h

@[simp] theorem MyNat.zero_le (n : MyNat) : 0 ≤ n := by
  rw [MyNat.le_iff_add]

  exists n
  simp

theorem MyNat.zero_of_le_zero {n : MyNat} (h : n ≤ 0) : n = 0 := by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    exfalso
    rw [MyNat.le_iff_add] at h
    obtain ⟨k, hk⟩ := h
    simp_all

@[simp] theorem MyNat.le_zero {n : MyNat} : n ≤ 0 ↔ n = 0 := by
  constructor <;> intro h
  · apply MyNat.zero_of_le_zero h
  · simp [h]

theorem MyNat.eq_zero_or_pos (n : MyNat) : n = 0 ∨ 0 < n := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    dsimp [(· < ·), MyNat.lt] at *
    cases ih with
    | inl ih =>
      simp_all
    | inr ih =>
      simp_all [MyNat.le_step]

theorem MyNat.eq_or_lt_of_le {n : MyNat} : n ≤ m → n = m ∨ n < m := by
  intro h
  dsimp [(· < ·), MyNat.lt]
  rw [MyNat.le_iff_add] at *
  obtain ⟨k, hk⟩ := h
  induction k with
  | zero => simp_all
  | succ k _ =>
    have : ∃ k, n + 1 + k = m := by
      exists k
      rw [← hk]
      ac_rfl
    simp_all

theorem MyNat.le_of_lt { a b : MyNat} (h : a < b) : a ≤ b := by
  dsimp [(· < ·), MyNat.lt] at h
  have : a ≤ b := calc
    _ ≤ a + 1 := by simp
    _ ≤ b := by assumption
  assumption

theorem MyNat.le_of_eq_or_lt {m n : MyNat} : n = m ∨ n < m → n ≤ m := by
  intro h
  cases h with
  | inl h =>
    rw [h]
  | inr h =>
    exact MyNat.le_of_lt h

theorem MyNat.le_iff_eq_or_lt {m n : MyNat} : n ≤ m ↔ n = m ∨ n < m := by
  constructor
  · apply MyNat.eq_or_lt_of_le
  · apply MyNat.le_of_eq_or_lt


theorem MyNat.lt_or_ge (a b : MyNat) : a < b ∨ b ≤ a := by
  dsimp [(· < ·), MyNat.lt]

  induction a with
  | zero =>
    suffices 1 ≤ b ∨ b ≤ 0 from by
      simp_all
    have : b = 0 ∨ 0 < b := MyNat.eq_zero_or_pos b
    dsimp [(· < ·), MyNat.lt] at this
    cases this <;> simp_all
  | succ a ih =>
    cases ih with
    | inr h =>
      right
      exact le_step h
    | inl h =>
      simp [MyNat.le_iff_eq_or_lt] at h
      cases h with
      | inl h =>
        right
        simp_all
      | inr h =>
        dsimp [(· < ·), MyNat.lt] at h
        left
        assumption

theorem MyNat.lt_of_not_le {a b : MyNat} (h : ¬ a ≤ b) : b < a := by
  cases (MyNat.lt_or_ge b a) with
  | inl h => assumption
  | inr h => contradiction

theorem MyNat.not_le_of_lt {a b : MyNat} (h : a < b) : ¬ b ≤ a := by
  intro hle
  dsimp [(· < ·), MyNat.lt] at h
  rw [MyNat.le_iff_add] at *
  obtain ⟨k, hk⟩ := h
  obtain ⟨l, hl⟩ := hle
  have : a + (k + l + 1) = a := calc
    _ = a + 1 + k + l := by ac_rfl
    _ = b + l := by rw [hk]
    _ = a := by rw [hl]
  simp at this

theorem MyNat.lt_iff_le_not_le (a b : MyNat) : a < b ↔ a ≤ b ∧ ¬ b ≤ a := by
  constructor <;> intro h
  case mp => simp_all [MyNat.not_le_of_lt, MyNat.le_of_lt]
  case mpr => simp_all [MyNat.lt_of_not_le]

theorem MyNat.le_total (a b : MyNat) : a ≤ b ∨ b ≤ a := by
  cases (MyNat.lt_or_ge a b) <;> simp_all [MyNat.le_of_lt]

example (a : MyNat) : a ≠ a + 1 := by
  simp_all

example (n : MyNat) : ¬ n + 1 ≤ n := by
  intro h
  rw [MyNat.le_iff_add] at *
  obtain ⟨k, hk⟩ := h
  have : n + (1 + k) = n := calc
    _ = n + 1 + k := by ac_rfl
    _ = n := by rw [hk]
  simp_all
