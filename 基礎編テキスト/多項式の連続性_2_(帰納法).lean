import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Data.Real.Basic

open Filter Topology Polynomial

variable (a : ℝ)

-- 証明したい命題: lim(x→a) P(x) = P(a)
example (P : Polynomial ℝ) : Tendsto (fun x => P.eval x) (𝓝 a) (𝓝 (P.eval a)) := by
  -- 多項式の構造に関する帰納法を適用します
  -- 以下の3つのケースを証明すれば、全ての多項式で成り立つことになります
  induction P using Polynomial.induction_on with
  | h_C c =>
    -- 【ケース1: 定数関数 P(x) = c の場合】
    -- P.eval x は c に、P.eval a も c になります
    simp only [eval_C]
    -- 定数の極限は定数そのもの (lim c = c)
    exact tendsto_const_nhds

  | h_add p q hp hq =>
    -- 【ケース2: 足し算 P(x) = p(x) + q(x) の場合】
    -- 仮定 hp: p(x)→p(a), hq: q(x)→q(a) があるとき、和も収束することを示します
    simp only [eval_add]
    -- 極限の和の性質: lim (f + g) = lim f + lim g を適用
    exact Filter.Tendsto.add hp hq

  | h_mul_X p hp =>
    -- 【ケース3: P(x) = p(x) * x の場合】
    -- 多項式 p(x) に x を掛けた形です。
    -- 仮定 hp: p(x)→p(a) があるとき、これに x を掛けても収束することを示します
    simp only [eval_mul_X]
    -- ここで「積の極限」と「lim x = a (tendsto_id)」を組み合わせます
    -- apply Filter.Tendsto.mul としても良いですが、ドット記法で書くと簡潔です
    apply hp.mul
    -- 最後に残ったのが lim(x→a) x = a の証明です
    exact tendsto_id
