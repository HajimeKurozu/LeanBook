import Mathlib.Data.Real.Basic

-- 変数 a は実数、m, n は自然数（正の整数を含む）とします
variable (a : ℝ) (m n : ℕ)

example : a ^ m * a ^ n = a ^ (m + n) := by
  -- Mathlibの定理 pow_add を適用して書き換える(rewrite)だけです
  rw [pow_add]
