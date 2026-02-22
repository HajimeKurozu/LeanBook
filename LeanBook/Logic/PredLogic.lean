def P (n : Nat) : Prop:= n = n
example : ∀ a : Nat, P a := by
  intro x
  dsimp [P]

example (P : Nat → Prop) (h : ∀ x : Nat, P x) : P 0 := by
  exact h 0

def even (n: Nat) : Prop := ∃ m : Nat, n = m + m
example : even 4 := by
  exists 2

example (α : Type) (P Q : α → Prop) (h : ∃ x : α, P x ∧ Q x)
    : ∃ x : α, Q x := by
  obtain ⟨y, hy⟩ := h
  exists y
  exact hy.right

/--人間たちの集合-/
opaque Human : Type
/--愛の関係-/
opaque Love : Human → Human → Prop
@[inherit_doc] infix:50 " -♥→ " => Love

def IdolExists : Prop := ∃ idol : Human, ∀ h : Human, h -♥→ idol

def EveryoneLovesSomeone : Prop := ∀ h : Human, ∃ tgt : Human, h -♥→ tgt

#check ∃ philan : Human, ∀ h : Human, philan -♥→ h

def PhilanExists : Prop := ∃ philan : Human, ∀ h : Human, philan -♥→ h

#check ∀ h : Human, ∃ lover : Human, lover -♥→ h

def EveryoneLoved : Prop := ∀ h : Human, ∃ lover : Human, lover -♥→ h

example : PhilanExists → EveryoneLoved := by
  intro h
  obtain ⟨philan, h⟩ := h
  dsimp [EveryoneLoved]
  intro human
  exists philan
  exact h human


example : IdolExists → EveryoneLovesSomeone := by
  dsimp [EveryoneLovesSomeone]
  intro hidol h
  obtain ⟨idol, hidol⟩ := hidol
  exists idol
  exact hidol h

-- 前提条件：IdolExists（全員から愛される人がいる）ならば EveryoneLovesSomeone（誰もが誰かを愛している）を証明
example : IdolExists → EveryoneLovesSomeone := by
  -- 1. EveryoneLovesSomeone の定義を簡約（展開）して、具体的な論理式（∀ x, ∃ y, ...）にする
  dsimp [EveryoneLovesSomeone]

  -- 2. 前提（アイドルが存在する）を `hidol` とし、
  --    「誰でも」を証明するために任意の人物を `h` として導入する
  intro hidol h

  -- 3. 「アイドルが存在する」という仮定 `hidol` を分解し、
  --    実際のアイドルの個体を `idol`、その人が全員に愛されているという性質を `hidol`（名前再利用）として取り出す
  obtain ⟨idol, hidol⟩ := hidol

  -- 4. 「h さんが誰かを愛している」という結論に対し、その相手として先ほどの `idol` を指定する
  exists idol

  -- 5. `hidol` は「すべての人は idol を愛している」という性質なので、
  --    それを `h` さんに適用して、証明を完了する
  exact hidol h
