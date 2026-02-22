import Mathlib.Data.Real.Basic

-- 行の先頭から書き始める
example (a : ℝ) (m n : ℕ) : a ^ m * a ^ n = a ^ (m + n) := by
  induction n with
  | zero =>
    rw [pow_zero, mul_one, add_zero]
  | succ n ih =>
    rw [pow_succ, ← mul_assoc, ih, ← pow_succ]
    rfl
