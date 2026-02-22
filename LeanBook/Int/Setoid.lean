structure Point where
  x : Int
  y : Int

#check { x := 1, y := 2 : Point }

#check Point.mk

#check Point.mk 1 2

#check Point.x
#check Point.y

#eval
  let p : Point := { x := 1, y := 2 }
  p.x

--structure Equivalence {α : Sort u} (r : α → α → Prop) : Prop where
--  refl  : ∀ x, r x x
--  symm  : ∀ {x y}, r x y → r y x
--  trans : ∀ {x y z}, r x y → r y z → r x z

example {α : Type} (r : α → α → Prop) (h : Equivalence r) : ∀ x, r x x := by
  exact h.refl

example {α : Type} : Equivalence (fun x y : α => x = y) := by
  constructor
  case refl =>
    intro x
    rfl
  case symm =>
    intro x y h
    rw [h]
  case trans =>
    intro x y z hxy hyz
    rw [hxy, hyz]

--class Setoid (α : Sort u) where
--  r : α → α → Prop
--  iseqv : Equivalence r

example {α : Type} (sr : Setoid α) (x y : α) : sr.r x y = (x ≈ y) := by
  rfl

-- α という任意の型、その型上の Setoid（同値関係）、および α の要素 x, y を引数に取ります
example {α : Type} (sr : Setoid α) (x y : α) :
  -- 「sr における関係 r」と「チルダ記号 (≈) による表記」が定義上同じであることを示します
  sr.r x y = (x ≈ y) := by
  -- どちらも定義上同一（definitional equality）であるため、rfl（反射律）だけで証明が完了します
  rfl


example {α : Type} : Equivalence (fun _x _y : α => True) := by
  constructor
  case refl =>
    intro x
    trivial
  case symm =>
    intro x y h
    trivial
  case trans =>
    intro x y z
    trivial

-- α という型（集合のようなもの）に対して、
-- 「どんな x と y も常に True（真）である」という二項関係が
-- Equivalence（同値関係）であることを証明します。
example {α : Type} : Equivalence (fun _x _y : α => True) := by
  -- Equivalence は 3つの性質（反射律、対称律、推移律）が必要なので
  -- constructor でそれら 3つを証明する準備をします。
  constructor

  -- 1. refl (反射律): すべての x について、自分自身と関係があるか？
  case refl =>
    intro x    -- 任意の要素 x を取ってきます
    trivial    -- 関係は常に「True」なので、証明は自明（trivial）です

  -- 2. symm (対称律): x と y に関係があれば、y と x にも関係があるか？
  case symm =>
    intro x y h -- 任意の x, y と、「x と y が関係を持つ」という仮定 h を取ります
    trivial     -- 結論（y と x が関係を持つ）も「True」なので自明です

  -- 3. trans (推移律): x と y、y と z に関係があれば、x と z にも関係があるか？
  case trans =>
    intro x y z -- 任意の x, y, z を取ります（関係性の仮定は自動的に導入されます）
    trivial     -- 結論（x と z が関係を持つ）も「True」なので自明です
