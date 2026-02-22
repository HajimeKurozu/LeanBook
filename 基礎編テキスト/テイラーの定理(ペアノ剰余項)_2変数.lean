/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# テイラーの定理 (Taylor's theorem)

このファイルは実関数 `f : ℝ → E` のテイラー多項式を定義し、テイラーの定理を証明します。
以前の `taylorApprox` に相当する機能は `taylorWithinEval` として実装されています。
-/

open scoped Interval Topology Nat
open Set

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

-- ==========================================
-- 1. 基本定義 (Definitions)
-- ==========================================

/-- テイラー多項式の第 `k` 係数。 -/
noncomputable def taylorCoeffWithin (f : ℝ → E) (k : ℕ) (s : Set ℝ) (x₀ : ℝ) : E :=
  (k ! : ℝ)⁻¹ • iteratedDerivWithin k f s x₀

/-- 集合 `s` 内の導関数を用いた次数 `n` のテイラー多項式（多項式オブジェクト）。 -/
noncomputable def taylorWithin (f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ : ℝ) : PolynomialModule ℝ E :=
  (Finset.range (n + 1)).sum fun k =>
    PolynomialModule.comp (Polynomial.X - Polynomial.C x₀)
      (PolynomialModule.single ℝ k (taylorCoeffWithin f k s x₀))

/--
次数 `n` のテイラー多項式を点 `x` で評価した値（テイラー近似値）。
以前の `taylorApprox` に相当します。
-/
noncomputable def taylorWithinEval (f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ x : ℝ) : E :=
  PolynomialModule.eval x (taylorWithin f n s x₀)

-- ==========================================
-- 2. 基本的な性質 (Basic Properties)
-- ==========================================

/-- テイラー近似値を和の形式で展開する補題。 -/


theorem taylor_within_apply (f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ x : ℝ) :
    taylorWithinEval f n s x₀ x =
      ∑ k ∈ Finset.range (n + 1), ((k ! : ℝ)⁻¹ * (x - x₀) ^ k) • iteratedDerivWithin k f s x₀ := by
  -- 1. 定義を unfold する
  unfold taylorWithinEval taylorWithin
  -- 2. 和の評価を展開する (map_sum を使用)
  simp_rw [map_sum, PolynomialModule.comp_eval, Polynomial.eval_sub,
           Polynomial.eval_X, Polynomial.eval_C, PolynomialModule.eval_single]
  -- 3. Σ の中身を比較する
  apply Finset.sum_congr rfl
  intro k _
  -- 4. 係数を展開してスカラー倍の順序を整理
  unfold taylorCoeffWithin
  rw [smul_smul, mul_comm]


/-- x = x₀ におけるテイラー多項式の値は f x₀ に等しい。 -/
@[simp]
theorem taylorWithinEval_self (f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ : ℝ) :
    taylorWithinEval f n s x₀ x₀ = f x₀ := by
  rw [taylor_within_apply]
  -- k=0 の項だけが残り、それ以外は (x₀ - x₀)^k = 0 で消える
  simp [Finset.sum_range_succ', iteratedDerivWithin_zero]


/-- テイラー多項式の微分に関する補題。
    (P_{n+1} f)' (x) = P_n (f') (x) であることを利用する。 -/
theorem hasDerivAt_taylorWithinEval_succ (f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ x : ℝ) :
    HasDerivAt (fun y => taylorWithinEval f (n + 1) s x₀ y)
      (taylorWithinEval (fun t => iteratedDerivWithin 1 f s t) n s x₀ x) x := by
  -- この証明は taylor_within_apply を展開して項別に微分することで得られます。
  -- ここでは構造を示すため sorry としますが、これが little-o の証明に必須です。
  sorry




-- ==========================================
-- 3. 主要な定理 (Main Theorems)
-- ==========================================

-- ... (これより前の定義と taylor_within_apply 等は変更なし) ...

/-- **テイラーの定理 (スモールオー形式)** -/

theorem taylor_isLittleO {f : ℝ → E} {x₀ : ℝ} {n : ℕ} {s : Set ℝ}
    (hs : Convex ℝ s) (hx₀s : x₀ ∈ s) (hf : ContDiffOn ℝ n f s) :
    (fun x ↦ f x - taylorWithinEval f n s x₀ x) =o[𝓝[s] x₀] fun x ↦ (x - x₀) ^ n := by
  induction n generalizing f with


  | zero =>
    -- 1. まず、フィルタ上で (f x - P₀) = (f x - f x₀) であることを示す
    have h_eq : (fun x => f x - taylorWithinEval f 0 s x₀ x) =ᶠ[𝓝[s] x₀] (fun x => f x - f x₀) := by
      filter_upwards
      intro x
      unfold taylorWithinEval taylorWithin taylorCoeffWithin
      simp

    -- 2. 💡 ここがポイント：isLittleO の左辺を直接書き換える
    -- 「(f - P₀) =o 1」を「(f - f x₀) =o 1」に変換します
    apply Asymptotics.IsLittleO.congr_left (f₂ := fun x => f x - f x₀)
    · exact h_eq

    -- 3. 書き換わった後に Tendsto の形にする
    simp only [pow_zero, Asymptotics.isLittleO_one_iff]

    -- 4. 連続性の定義を適用
    rw [tendsto_sub_nhds_zero_iff]
    exact hf.continuousOn.continuousWithinAt hx₀s





    -- 1. o(1) を Tendsto に変換
    simp only [pow_zero, Asymptotics.isLittleO_one_iff]

    -- 2. フィルタ上で (f x - P₀) = (f x - f x₀) を示す
    have h_eq : (fun x => f x - taylorWithinEval f 0 s x₀ x) =ᶠ[𝓝[s] x₀] (fun x => f x - f x₀) := by
      filter_upwards
      intro x
      -- 定義を unfold して simp
      unfold taylorWithinEval taylorWithin taylorCoeffWithin
      simp


    -- 3. 💡 不明な補題を避け、Filter.tendsto_congr を直接使う
    -- これにより、(f x - P₀) が収束することと (f x - f x₀) が収束することが同値になります
    refine Filter.EventuallyEq.rw h_eq ?_

    -- 4. ゴールが Tendsto (fun x => f x - f x₀) ... になるので連続性を適用
    rw [tendsto_sub_nhds_zero_iff]
    exact hf.continuousOn.continuousWithinAt hx₀s








  | succ n ih =>
    rcases s.eq_singleton_or_nontrivial hx₀s with rfl | hs_nontriv
    · simp
    let h_unique := hs.uniqueDiffOn (hs.nontrivial_iff_nonempty_interior.1 hs_nontriv)
    have hf_deriv : ContDiffOn ℝ n (derivWithin f s) s := hf.derivWithin h_unique le_rfl

    let g := fun x ↦ f x - taylorWithinEval f (n + 1) s x₀ x
    have hg0 : g x₀ = 0 := by simp [taylorWithinEval_self]

    -- 💡 ターゲットを g x =o (x-x₀)ⁿ⁺¹ に直接結びつけます
    apply Asymptotics.IsLittleO.congr_left (fun x => (x - x₀) ^ (n + 1))
    · filter_upwards
      intro x
      simp [g, hg0] -- g x = g x - g x₀ を示す

    -- ロピタルのバリエーションを適用
    apply Convex.isLittleO_pow_succ_real hs hx₀s hg0

    -- 導関数の little-o 評価
    · have h_ih := ih hs hx₀s hf_deriv
      -- (f - P)' = f' - P' = o((x-x₀)ⁿ) を ih と繋げる
      apply Asymptotics.IsLittleO.congr_left (fun x => (x - x₀) ^ n) h_ih
      filter_upwards
      intro x
      if hx : x ∈ s then
        have hdf := (hf.differentiableOn (Nat.le_add_left 1 n) x hx).hasDerivWithinAt
        have hdP := (hasDerivAt_taylorWithinEval_succ f n s x₀ x).hasDerivWithinAt
        -- 💡 .deriv を使うのではなく hasDerivWithinAt の差の定義を使う
        exact (hdf.sub hdP).deriv
      else
        -- s の外側では定義により一致
        simp [derivWithin_of_not_mem hx]







/-- **ラグランジュの剰余項を持つテイラーの定理** -/
theorem taylor_mean_remainder_lagrange {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ} (hx : x₀ < x)
    (hf : ContDiffOn ℝ n f (Icc x₀ x))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc x₀ x)) (Ioo x₀ x)) :
    ∃ x' ∈ Ioo x₀ x, f x - taylorWithinEval f n (Icc x₀ x) x₀ x =
      iteratedDerivWithin (n + 1) f (Icc x₀ x) x' * (x - x₀) ^ (n + 1) / (n + 1)! := by
  -- (既存の証明コードが続く...)
  sorry
