/-

3.7.演習

以下の識別子を証明し、謝罪されたプレースホルダーを実際の証明に置き換えてください。

-/

variable (p q r : Prop)

-- ∧ と ∨ の可換性
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q =>
      -- 左から右への証明 (→)
      have hp : p := h.left
      have hq : q := h.right
      show q ∧ p from ⟨hq, hp⟩)
    (fun h : q ∧ p =>
      -- 右から左への証明 (←)
      have hq : q := h.left
      have hp : p := h.right
      show p ∧ q from ⟨hp, hq⟩)

 example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h : p ∨ q =>
      -- 左から右への証明 (→)
      Or.elim h
        (fun hp : p =>
          show q ∨ p from Or.inr hp)
        (fun hq : q =>
          show q ∨ p from Or.inl hq))
    (fun h : q ∨ p =>
      -- 右から左への証明 (←)
      Or.elim h
        (fun hq : q =>
          show p ∨ q from Or.inr hq)
        (fun hp : p =>
          show p ∨ q from Or.inl hp))

-- ∧ と ∨ の結合性
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun h : (p ∧ q) ∧ r =>
      -- 左から右への証明 (→)
      -- 1. まず外側の ∧ を分解
      have hpq : p ∧ q := h.left
      have hr  : r     := h.right
      -- 2. 次に内側の p ∧ q を分解
      have hp  : p     := hpq.left
      have hq  : q     := hpq.right
      -- 3. 目的の形 p ∧ (q ∧ r) を構築
      show p ∧ (q ∧ r) from ⟨hp, ⟨hq, hr⟩⟩)
    (fun h : p ∧ (q ∧ r) =>
      -- 右から左への証明 (←)
      -- 1. まず外側の ∧ を分解
      have hp  : p     := h.left
      have hqr : q ∧ r := h.right
      -- 2. 次に内側の q ∧ r を分解
      have hq  : q     := hqr.left
      have hr  : r     := hqr.right
      -- 3. 目的の形 (p ∧ q) ∧ r を構築
      show (p ∧ q) ∧ r from ⟨⟨hp, hq⟩, hr⟩)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun h : (p ∨ q) ∨ r =>
      -- 左から右への証明 (→)
      Or.elim h
        (fun hpq : p ∨ q =>
          -- (p ∨ q) の場合をさらに分解
          Or.elim hpq
            (fun hp : p => show p ∨ (q ∨ r) from Or.inl hp)
            (fun hq : q => show p ∨ (q ∨ r) from Or.inr (Or.inl hq)))
        (fun hr : r =>
          -- r の場合
          show p ∨ (q ∨ r) from Or.inr (Or.inr hr)))
    (fun h : p ∨ (q ∨ r) =>
      -- 右から左への証明 (←)
      Or.elim h
        (fun hp : p =>
          -- p の場合
          show (p ∨ q) ∨ r from Or.inl (Or.inl hp))
        (fun hqr : q ∨ r =>
          -- (q ∨ r) の場合をさらに分解
          Or.elim hqr
            (fun hq : q => show (p ∨ q) ∨ r from Or.inl (Or.inr hq))
            (fun hr : r => show (p ∨ q) ∨ r from Or.inr hr)))

-- 分配性
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
      -- 左から右への証明 (→)
      have hp  : p     := h.left
      have hqr : q ∨ r := h.right
      -- q ∨ r を場合分けします
      Or.elim hqr
        (fun hq : q =>
          -- p と q を組み合わせて左側の (p ∧ q) を作る
          show (p ∧ q) ∨ (p ∧ r) from Or.inl ⟨hp, hq⟩)
        (fun hr : r =>
          -- p と r を組み合わせて右側の (p ∧ r) を作る
          show (p ∧ q) ∨ (p ∧ r) from Or.inr ⟨hp, hr⟩))
    (fun h : (p ∧ q) ∨ (p ∧ r) =>
      -- 右から左への証明 (←)
      -- (p ∧ q) ∨ (p ∧ r) を場合分けします
      Or.elim h
        (fun hpq : p ∧ q =>
          -- 左側のケース: p ∧ q
          have hp : p := hpq.left
          have hq : q := hpq.right
          -- p と (q ∨ r) の左側を組み合わせて作る
          show p ∧ (q ∨ r) from ⟨hp, Or.inl hq⟩)
        (fun hpr : p ∧ r =>
          -- 右側のケース: p ∧ r
          have hp : p := hpr.left
          have hr : r := hpr.right
          -- p と (q ∨ r) の右側を組み合わせて作る
          show p ∧ (q ∨ r) from ⟨hp, Or.inr hr⟩))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (fun h : p ∨ (q ∧ r) =>
      -- 左から右への証明 (→)
      -- 1. まず p ∨ (q ∧ r) を場合分けします
      Or.elim h
        (fun hp : p =>
          -- p が真の場合、(p ∨ q) も (p ∨ r) も両方 p から作れます
          have hpq : p ∨ q := Or.inl hp
          have hpr : p ∨ r := Or.inl hp
          show (p ∨ q) ∧ (p ∨ r) from ⟨hpq, hpr⟩)
        (fun hqr : q ∧ r =>
          -- (q ∧ r) が真の場合、q と r を取り出してそれぞれに使います
          have hq : q := hqr.left
          have hr : r := hqr.right
          have hpq : p ∨ q := Or.inr hq
          have hpr : p ∨ r := Or.inr hr
          show (p ∨ q) ∧ (p ∨ r) from ⟨hpq, hpr⟩))
    (fun h : (p ∨ q) ∧ (p ∨ r) =>
      -- 右から左への証明 (←)
      -- 1. まず外側の ∧ を分解します
      have hpq : p ∨ q := h.left
      have hpr : p ∨ r := h.right
      -- 2. 次に (p ∨ q) を場合分けします
      Or.elim hpq
        (fun hp : p =>
          -- p が真なら、結論 p ∨ (q ∧ r) の左側として即座に示せます
          show p ∨ (q ∧ r) from Or.inl hp)
        (fun hq : q =>
          -- q が真の場合、さらに (p ∨ r) の中身を確認する必要があります
          Or.elim hpr
            (fun hp : p =>
              -- p が真なら、やはり結論の左側
              show p ∨ (q ∧ r) from Or.inl hp)
            (fun hr : r =>
              -- q と r が揃ったので、結論の右側 (q ∧ r) を作ります
              show p ∨ (q ∧ r) from Or.inr ⟨hq, hr⟩)))

example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun h : p → (q → r) =>
      -- 左から右への証明 (→)
      -- 引数として (p ∧ q) を受け取る関数を定義します
      fun hpq : p ∧ q =>
        -- p ∧ q を分解してそれぞれのパーツを取り出す
        have hp : p := hpq.left
        have hq :q := hpq.right
        -- h に hp を渡すと (q → r) が返り、そこに hq を渡すと r が得られる
        show r from h hp hq)
    (fun h : p ∧ q → r =>
      -- 右から左への証明 (←)
      -- p を受け取り、「q を受け取って r を返す関数」を返す
      fun hp : p =>
        fun hq : q =>
        -- p と q を組み合わせて (p ∧ q) を作る
        have hpq : p ∧ q := ⟨hp, hq⟩
        -- h に hpq を渡して r を得る
        show r from h hpq)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun h : (p ∨ q) → r =>
      -- 左から右への証明 (→)
      -- 1. (p → r) を作る
      have hpr : p → r :=
        fun hp : p =>
          show r from h (Or.inl hp)
      -- 2. (q → r) を作る
      have hqr : q → r :=
        fun hq : q =>
          show r from h (Or.inr hq)
      -- 3. 両方を組み合わせて And (∧) を作る
      show (p → r) ∧ (q → r) from ⟨hpr, hqr⟩)
    (fun h : (p → r) ∧ (q → r) =>
      -- 右から左への証明 (←)
      -- 引数として (p ∨ q) を受け取り、r を返す関数を作る
      fun hpq : p ∨ q =>
        -- ∧ を分解してそれぞれの関数を取り出す
        have hpr : p → r := h.left
        have hqr : q → r := h.right
        -- (p ∨ q) を場合分けして、適切な関数を適用する
        Or.elim hpq
          (fun hp : p => show r from hpr hp)
          (fun hq : q => show r from hqr hq))

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun h : ¬(p ∨ q) =>
      -- 左から右への証明 (→)
      -- 1. ¬p (p → False) を導く
      have hnp : ¬p :=
      fun hp : p =>
        show False from h (Or.inl hp)
      -- 2. ¬q (q → False) を導く
      have hnq : ¬q :=
        fun hq : q =>
          show False from h (Or.inr hq)
      -- 3. それらを組み合わせて ∧ を作る
      show ¬p ∧ ¬q from ⟨hnp, hnq⟩)
    (fun h : ¬p ∧ ¬q =>
      -- 右から左への証明 (←)
      -- 1. (p ∨ q) を仮定して False を導く関数を作る
      fun hpq : p ∨ q =>
        have hnp : ¬p := h.left
        have hnq : ¬q := h.right
        -- 2. (p ∨ q) を場合分けして、それぞれ矛盾(False)を出す
        Or.elim hpq
          (fun hp : p => show False from hnp hp)
          (fun hq : q => show False from hnq hq))

example (p q : Prop) : ¬p ∨ ¬q → ¬(p ∧ q) :=
  -- 1. 仮定 h : ¬p ∨ ¬q を受け取り、結論 ¬(p ∧ q) を導く関数を作る
  fun h : ¬p ∨ ¬q =>
    -- 2. ¬(p ∧ q) つまり (p ∧ q) → False を証明するため、引数 hpq を取る
    fun hpq : p ∧ q =>
      -- 3. hpq を分解して p と q を手に入れる
      have hp : p := hpq.left
      have hq : q := hpq.right
      -- 4. 最初の仮定 h (¬p ∨ ¬q) を場合分けする
      show False from Or.elim h
        (fun hnp : ¬p =>
          -- ¬p (p → False) に hp を渡して矛盾を出す
          show False from hnp hp)
        (fun hnq : ¬q =>
          -- ¬q (q → False) に hq を渡して矛盾を出す
          show False from hnq hq)

example (p : Prop) : ¬(p ∧ ¬p) :=
  -- 1. ¬(p ∧ ¬p) は (p ∧ ¬p) → False と同義。
  -- そのため、(p ∧ ¬p) を仮定として受け取る関数を書く。
  fun h : p ∧ ¬p =>
    -- 2. 仮定 h から、p と ¬p をそれぞれ取り出す。
    have hp  : p  := h.left
    have hnp : ¬p := h.right
    -- 3. ¬p は (p → False) なので、これに hp を渡せば False が得られる。
    show False from hnp hp

example (p q : Prop) : p ∧ ¬q → ¬(p → q) :=
  -- 1. 仮定 h : p ∧ ¬q を受け取る
  fun h : p ∧ ¬q =>
    -- 2. ¬(p → q) を証明するため、(p → q) を仮定して False を導く
    fun hpq : p → q =>
      -- 3. 最初の大切な仮定 h をバラす
      have hp  : p  := h.left
      have hnq : ¬q := h.right -- hnq は (q → False) と同義
      -- 4. hpq に hp を渡すと q が得られる
      have hq : q := hpq hp
      -- 5. 得られた q を hnq に渡して矛盾(False)を導く
      show False from hnq hq

example (p q : Prop) : ¬p → (p → q) :=
  -- 1. 仮定 hnp : ¬p (つまり p → False) を受け取る
  fun hnp : ¬p =>
    -- 2. 次に 仮定 hp : p を受け取る
    fun hp : p =>
      -- 3. hnp に hp を渡すと、矛盾 (False) が得られる
      have hf : False := hnp hp
      -- 4. 矛盾が起きたので、そこから望みの命題 q を導き出す
      show q from False.elim hf

example (p q : Prop) : (¬p ∨ q) → (p → q) :=
  -- 1. 仮定 h : ¬p ∨ q を受け取る
  fun h : ¬p ∨ q =>
    -- 2. 結論 (p → q) を導くため、仮定 hp : p を受け取る
    fun hp : p =>
      -- 3. 手元にある h (¬p ∨ q) を場合分けする
      Or.elim h
        (fun hnp : ¬p =>
          -- ケースA: ¬p (p → False) の場合
          -- p と ¬p で矛盾が発生するので、False.elim で q を導く
          have hf : False := hnp hp
          show q from False.elim hf)
        (fun hq : q =>
          -- ケースB: q の場合
          -- すでに q そのものを持っているので、そのまま show する
          show q from hq)

example (p : Prop) : p ∨ False ↔ p :=
  Iff.intro
    (fun h : p ∨ False =>
      -- 左から右への証明 (→)
      -- 1. p ∨ False を場合分けします
      Or.elim h
        (fun hp : p =>
          -- ケースA: p が真の場合、そのまま p を返す
          show p from hp)
        (fun hf : False =>
          -- ケースB: False が真（！？）という仮定の場合
          -- 矛盾が起きているので、False.elim を使って p を導く
          show p from False.elim hf))
    (fun hp : p =>
      -- 右から左への証明 (←)
      -- p が真なら、p ∨ False の左側 (inl) を採用すればよい
      show p ∨ False from Or.inl hp)


example (p : Prop) : p ∧ False ↔ False :=
  Iff.intro
    (fun h : p ∧ False =>
      -- 左から右への証明 (→)
      -- h (p ∧ False) の右側を取り出せば、そのまま False が得られる
      show False from h.right)
    (fun hf : False =>
      -- 右から左への証明 (←)
      -- False（矛盾）からは何でも導ける（False.elim）
      have hp : p := False.elim hf
      show p ∧ False from ⟨hp, hf⟩)


example (p q : Prop) : (p → q) → (¬q → ¬p) :=
  -- 1. 仮定 h : p → q を受け取る
  fun h : p → q =>
    -- 2. 結論 ¬q → ¬p を証明するため、仮定 hnq : ¬q を受け取る
    fun hnq : ¬q =>
      -- 3. さらに ¬p (p → False) を証明するため、仮定 hp : p を受け取る
      fun hp : p =>
        -- 4. h に hp を渡すと q が得られる
        have hq : q := h hp
        -- 5. hnq (q → False) に hq を渡すと矛盾 (False) が得られる
        show False from hnq hq


/-
以下の識別子を証明し、sorryプレースホルダーを実際の証明に置き換えてください。
これらは古典的な推論を必要とします。
-/

open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
-- 1. 仮定 h : p → q ∨ r を受け取る
  fun h : p → q ∨ r =>
    -- 2. 排中律を p に適用して場合分けする
    Or.elim (em p)
      (fun hp : p =>
        -- ケースA: p が真の場合
        -- h に hp を渡すと (q ∨ r) が得られるので、これをさらに分解する
        have hqr : q ∨ r := h hp
        Or.elim hqr
          (fun hq : q =>
            -- q が真なら、(p → q) が作れる
            have hpq : p → q := fun _ => hq
            Or.inl hpq)
          (fun hr : r =>
            -- r が真なら、(p → r) が作れる
            have hpr : p → r := fun _ => hr
            Or.inr hpr))
      (fun hnp : ¬p =>
        -- ケースB: p が偽 (¬p) の場合
        -- p が偽なら「爆発原理」により (p → q) は自動的に真になる
        have hpq : p → q :=
          fun hp_absurd : p =>
            False.elim (hnp hp_absurd)
        Or.inl hpq)

example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
example : ¬(p → q) → p ∧ ¬q := sorry
example : (p → q) → (¬p ∨ q) := sorry
example : (¬q → ¬p) → (p → q) := sorry
example : p ∨ ¬p := sorry
example : (((p → q) → p) → p) := sorry

/-
古典論理を使用せずに ¬(p ↔ ¬p) を証明してください。
-/

example (p : Prop) : ¬(p ↔ ¬p) :=
  -- 1. (p ↔ ¬p) を仮定して矛盾 (False) を導く
  fun h : p ↔ ¬p =>
    -- 2. 二つの向きの関数を取り出す
    have hp_to_hnp : p → ¬p := h.mp
    have hnp_to_hp : ¬p → p := h.mpr

    -- 3. 「¬p」そのものを証明できてしまう
    have hnp : ¬p :=
      fun hp : p =>
        -- p があるなら、hp_to_hnp を使って ¬p を作り、hp とぶつけて矛盾させる
        show False from (hp_to_hnp hp) hp

    -- 4. 「p」そのものも証明できてしまう
    have hp : p := hnp_to_hp hnp

    -- 5. ついに p と ¬p が揃ったので矛盾！
    show False from hnp hp
