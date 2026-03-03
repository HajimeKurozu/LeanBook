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
