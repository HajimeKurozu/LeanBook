import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic

open Filter Topology

-- 変数 a を実数として定義
variable (a : ℝ)

-- 【方法1】 Mathlibに用意されている定理を直接使う
-- "tendsto_pow_div_factorial_atTop_zero" というそのものズバリの定理があります。
example : Tendsto (fun n => a ^ n / n.factorial) atTop (𝓝 0) := by
  exact tendsto_pow_div_factorial_atTop_zero a

-- 【方法2】 指数関数の級数が収束することを利用する
-- Σ(a^n / n!) が収束するならば、その一般項 (a^n / n!) は 0 に収束します。
example : Tendsto (fun n => a ^ n / n.factorial) atTop (𝓝 0) := by
  -- 実数の指数関数の級数展開が収束可能(Summable)であることを示す定理
  have h_summable := Real.summable_pow_div_factorial a

  -- 級数が収束するなら、項は0に収束するという定理(Summable.tendsto_atTop_zero)を適用
  exact h_summable.tendsto_atTop_zero
