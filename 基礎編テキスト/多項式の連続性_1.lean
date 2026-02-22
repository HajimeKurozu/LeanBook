import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Data.Real.Basic

open Filter Topology

variable (a : ℝ)

-- 1. 定数の極限: lim(x→a) 1 = 1
example : Tendsto (fun x : ℝ => 1) (𝓝 a) (𝓝 1) := by
  -- 定数関数の極限に関する定理を適用
  exact tendsto_const_nhds

-- 2. xの極限: lim(x→a) x = a
example : Tendsto (fun x : ℝ => x) (𝓝 a) (𝓝 a) := by
  -- 恒等写像(id)の極限に関する定理を適用
  exact tendsto_id

-- 3. 多項式の極限: lim(x→a) P(x) = P(a)
-- P は実数係数の多項式 (Polynomial ℝ) とします
example (P : Polynomial ℝ) : Tendsto (fun x => P.eval x) (𝓝 a) (𝓝 (P.eval a)) := by
  -- 【解説】
  -- 多項式関数は連続である(Polynomial.continuous)という定理を使います。
  -- 関数が点 a で連続であれば、lim(x→a) f(x) = f(a) が成り立ちます。

  -- P.continuous は「Pは全ての点で連続」という証明です
  -- .tendsto a は「ゆえに点 a で極限値を持つ」という変換です
  exact P.continuous.tendsto a
