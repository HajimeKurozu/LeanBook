theorem one_and_one_eq_two : 1 + 1 = 2 := by
  rfl

#check one_and_one_eq_two

#check (by rfl : 1 + 1 = 2)

example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  exact h hp

def idOnNat : Nat → Nat := by
  intro n
  exact n

#eval idOnNat 42


example (P Q :Prop) (hp : P) : Q → P :=
  fun _hq => hp
