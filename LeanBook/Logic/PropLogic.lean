#check Prop
#check (1 + 1 = 3 : Prop)
#check (fun n => n + 3 = 39 : Nat → Prop)
#check True
#check False

example : True := by trivial

example (P: Prop) (h : P) : P := by
  exact h

example (P : Prop)  (h : P) : P := by
  assumption

example (h: False) : ∀ x y z n : Nat,
  n >= 3 → x^n + y^n = z^n → x * y * z = 0 := by
  trivial

example (P Q R : Prop) : (P → Q → R) = (P → (Q → R)) := by
  rfl

#eval True → True
#eval True → False
#eval False → True
#eval False → False

example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  apply h
  apply hp

example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  exact h hp

example (P Q : Prop) (hq : Q) : P → Q := by
  intro hp
  exact hq

#eval ¬ True
#eval ¬ False

example (P : Prop) : (¬ P) = (P → False) := by
  rfl

example (P : Prop) (hnp : ¬ P) (hp : P) : False := by
  apply hnp
  exact hp

example (P : Prop) (h : P → ¬ Q) : Q → ¬ P := by
  intro hq
  intro hp
  exact h hp hq

example (P : Prop) (hnp : ¬ P) (hp : P) : False := by
  contradiction

example (P Q : Prop) (hnp : ¬ P) (hp : P) : Q := by
  exfalso
  contradiction

#eval True ↔ True
#eval True ↔ False
#eval False ↔ True
#eval False ↔ False

example (P Q : Prop) (h1 : P → Q) (h2 : Q → P) : P ↔ Q := by
  constructor
  · apply h1
  · apply h2

example (P Q : Prop) (hq : Q) : (Q → P) ↔ P := by
  constructor

  case mp =>
    intro h
    exact h hq

  case mpr =>
    intro hp hq
    exact hp


example (P Q : Prop) (hq : Q) : (Q → P) ↔ P:= by
  constructor <;> intro h

  case mp =>
    exact h hq

  case mpr =>
    intro hq
    exact h


example (P Q : Prop) (h : P ↔ Q) (hq : Q) : P := by
  rw [h]
  exact hq

example (P Q : Prop) (h : P ↔ Q) (hp : P) : Q := by
  rw [← h]
  exact hp

example (P Q : Prop) (h : P ↔ Q) : P =Q := by
  rw [h]


#eval True ∧ True
#eval True ∧ False
#eval False ∧ True
#eval False ∧ False

example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  · exact hp
  · exact hq

example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  exact ⟨hp, hq⟩

example (P Q : Prop) (h : P ∧ Q) : P := by
  exact h.left

example (P Q : Prop) (h : P ∧ Q) : Q := by
  exact h.right

#eval True ∨ True
#eval True ∨ False
#eval False ∨ True
#eval False ∨ False

example (P Q : Prop) (hp : P) : P ∨ Q := by
  left
  exact hp

example (P Q : Prop) (hq : Q) : P ∨ Q := by
  right
  exact hq

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hp =>
    right
    exact hp
  | inr hq =>
    left
    exact hq

  example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h
  case inl hp =>
    right
    exact hp
  case inr hq =>
    left
    exact hq

example (P Q : Prop) : (¬ P ∨ Q) → (P → Q) := by
  intro h hp
  cases h with
  | inl h => contradiction
  | inr h => exact h

example (P Q : Prop) : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q := by
  constructor <;> intro h1
  · constructor <;> intro h2
    · apply h1
      left
      assumption
    · apply h1
      right
      assumption
  · intro hpq
    cases hpq with
    | inl hp =>
      apply h1.left
      assumption
    | inr hq =>
      apply h1.right
      assumption


-- ド・モルガンの定理の証明
example (P Q : Prop) : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q := by
  -- 1. 同値 (↔) を示すため、左向き (→) と右向き (←) の2つの目標に分割する。
  --    さらに、それぞれの前提（¬(P ∨ Q) と ¬P ∧ ¬Q）を共通して `h1` という名前で導入する。
  constructor <;> intro h1

  -- 【左から右への証明: ¬(P ∨ Q) → ¬P ∧ ¬Q】
  -- 2. 結論の「かつ (∧)」を示すため、さらに ¬P と ¬Q の2つの目標に分割する。
  --    そして ¬P や ¬Q を証明するために、前提 P や Q を `h2` として導入する（Leanで ¬P は P → False のため）。
  · constructor <;> intro h2
    -- (a) ¬P の証明
    · apply h1      -- 前提 h1: ¬(P ∨ Q) を適用し、矛盾を示すための目標を (P ∨ Q) に変える
      left          -- (P ∨ Q) のうち、左側の P が正しいと言えば証明が終わる状態にする
      assumption    -- 導入した仮定 h2: P があるので、これで P ∨ Q が示され、矛盾が確定する
    -- (b) ¬Q の証明
    · apply h1      -- 前提 h1: ¬(P ∨ Q) を適用し、目標を (P ∨ Q) に変える
      right         -- (P ∨ Q) のうち、右側の Q が正しいと言えば証明が終わる状態にする
      assumption    -- 導入した仮定 h2: Q を使って証明完了

  -- 【右から左への証明: ¬P ∧ ¬Q → ¬(P ∨ Q)】
  -- 3. ¬(P ∨ Q) つまり (P ∨ Q) → False を示すため、仮定 (P ∨ Q) を `hpq` として導入する。
  · intro hpq
    -- 4. 仮定 hpq: P ∨ Q を使って、「P が真の場合」と「Q が真の場合」で場合分けを行う。
    cases hpq with
    -- (a) 左側の P が真である場合 (inl)
    | inl hp =>
      apply h1.left -- h1 は (¬P ∧ ¬Q) なので、その左側である ¬P (P → False) を取り出して適用する
      assumption    -- 仮定 hp: P を使って矛盾 (False) が導かれ、このケースの証明が終わる
    -- (b) 右側の Q が真である場合 (inr)
    | inr hq =>
      apply h1.right -- h1 は (¬P ∧ ¬Q) なので、その右側である ¬Q (Q → False) を取り出して適用する
      assumption    -- 仮定 hq: Q を使って矛盾が導かれ、すべてのケースの証明が完了する
