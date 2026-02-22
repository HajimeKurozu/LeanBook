example (P : Prop) : ¬¬P → P := by
intro hn2p

by_cases h : P
· exact h
· contradiction



example (P : Prop) : ¬¬P → P := by
  intro hn2p
  by_cases h : P
  · exact h
  · contradiction

example (P Q :Prop) : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q := by
  constructor
  · intro hnpq
    by_cases h : P
    · right
      intro hq
      exact hnpq ⟨h, hq⟩
    · left
      exact h

  · intro hpq' hpq
    cases hpq' with
    | inl hnp =>
      have := hpq.left
      contradiction
    | inr hnq =>
      have := hpq.right
      contradiction


example (P Q :Prop) : (P → Q) ↔ (¬ Q → ¬ P) := by
  constructor
  · intro h hq hp
    exact hq (h hp)
  · intro h hp
    by_cases hq : Q

    · assumption
    · have := h hq
      contradiction
