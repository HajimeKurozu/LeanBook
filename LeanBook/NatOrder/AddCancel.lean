import LeanBook.NatSemiring.Distrib

example (n : MyNat) : MyNat.succ n ≠ MyNat.zero := by
  intro h
  injection h

example (m n : MyNat) (h : MyNat.succ m = MyNat.succ n) : m = n := by
  injection h

example (m n : MyNat) (h : m + 1 = n + 1) : m = n := by
  injection h

variable {l m n : MyNat}

theorem MyNat.add_right_cancel (h : l + m = n + m) : l = n := by
  induction m with
  | zero =>
    simp_all
  | succ m ih =>
    have lem : (l + m) + 1 = (n + m) + 1 := calc
      _ = l + (m + 1) := by ac_rfl
      _ = n + (m + 1) := by rw [h]
      _ = (n + m) + 1 := by ac_rfl
    have : l + m = n + m := by
      injection lem
    exact ih this

theorem MyNat.add_left_cancel (h : l + m = l + n) : m = n := by
  rw [MyNat.add_comm l m, MyNat.add_comm l n] at h
  apply MyNat.add_right_cancel h


section
  attribute [local simp] MyNat.add_left_cancel
  example : l + m = l + n → m = n := by
    sorry
end

@[simp ↓] theorem MyNat.add_right_cancel_iff : l + m = n + m ↔ l = n := by
  constructor
  · apply MyNat.add_right_cancel
  · intro h
    rw [h]

@[simp ↓] theorem MyNat.add_left_cancel_iff : l + m = l + n ↔ m = n := by
  constructor
  · apply MyNat.add_left_cancel
  · intro h
    rw [h]

example : l + m = l + n → m = n := by
  simp


@[simp] theorem MyNat.add_right_eq_self : m + n = m ↔ n = 0 := by
  constructor <;> intro h
  case mpr => simp_all
  case mp =>
    have : m + n = m + 0 := by
     rw [h]
     simp
    simp_all

@[simp] theorem MyNat.add_left_er_self : n + m = m ↔ n = 0 := by
  rw [MyNat.add_comm n m, MyNat.add_right_eq_self]

@[simp] theorem MyNat.self_eq_add_right : m = m + n ↔ n = 0 := by
  rw [show (m = m + n) ↔ (m + n = m) from by exact eq_comm]
  exact add_right_eq_self

@[simp] theorem MyNat.self_eq_add_left : m = n + m ↔ n = 0 := by
  rw [MyNat.add_comm n m, MyNat.self_eq_add_right]


theorem MyNat.eq_zero_of_add_eq_zero : m + n = 0 → m = 0 ∧ n = 0 := by
  intro h
  induction n with
  | zero => simp_all
  | succ n ih =>
    exfalso
    rw [show m + (n + 1) = m + n + 1 from by ac_rfl] at h
    injection h

theorem MyNat.add_eq_zero_of_eq_zero : m = 0 ∧ n = 0 → m + n = 0 := by
  intro h
  simp_all

@[simp]
theorem MyNat.add_eq_zero_iff_eq_zero : m + n = 0 ↔ m = 0 ∧ n = 0 := by
  exact ⟨MyNat.eq_zero_of_add_eq_zero, MyNat.add_eq_zero_of_eq_zero⟩


@[simp]
theorem MyNat.mul_eq_zero (m n : MyNat) : m * n = 0 ↔ m = 0 ∨ n = 0 := by
  constructor <;> intro h
  case mpr =>
    cases h <;> simp_all
  case mp =>
    induction n with
    | zero =>
      simp_all
    | succ n =>
      have : m * n + m = 0 := calc
        _ = m * (n + 1) := by distrib
        _ = 0 := by rw [h]
      simp_all


example (n m : MyNat) : n + (1 + m) = n + 2 → m = 1 := by
  intro h
  rw [show 2 = 1 + 1 from rfl] at h
  simp_all
