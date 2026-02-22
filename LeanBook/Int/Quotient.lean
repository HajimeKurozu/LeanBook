section
  variable {α : Type} (sr : Setoid α)
  #check (Quotient.mk sr : α → Quotient sr)
end

section
  variable {α : Type} (sr : Setoid α)
  example (a : Quotient sr) : True := by
    induction a using Quotient.inductionOn with
    | h x =>
      guard_hyp x : α
      trivial
end

section
  variable {α β : Type} (sr : Setoid α)
  variable (f : β → α)
  #check (Quotient.mk sr ∘ f : β → Quotient sr)
end

section
  variable {α β : Type} (sr : Setoid α)
  variable (f : α → β) (h : ∀ x y, x ≈ y → f x = f y)
  #check (Quotient.lift f h : Quotient sr → β)
end

section
  variable {α β :Type} (sr : Setoid α)
  variable (f : α → β) (h : ∀ x y, x ≈ y → f x = f y)
  example : ∀ x, (Quotient.lift f h) (Quotient.mk sr x) = f x := by
    intro x
    rfl
end

section
  variable {α : Type} (sr : Setoid α)
  variable (x y : α) (h : x ≈ y)
  example : Quotient.mk sr x = Quotient.mk sr y := by
    apply Quotient.sound
    exact h
end

section
  variable {α : Type} (sr : Setoid α)
  variable (x y : α)
  example (h : Quotient.mk sr x = Quotient.mk sr y) : x ≈ y := by
    exact Quotient.exact h
end


private def Rel.comap {α β : Type} (f : α → β) (r : β → β → Prop)
  : α → α → Prop :=
  fun x y => r (f x) (f y)

private def Setoid.cmap {α β : Type} (f : α → β) (sr : Setoid β)
    :Setoid α where
  r := Rel.comap f (· ≈ ·)
  iseqv := by
    constructor
    case refl =>
      intro x
      apply Setoid.iseqv.refl
    case symm =>
      intro x y
      apply Setoid.iseqv.symm
    case trans =>
      intro x y z
      apply Setoid.iseqv.trans
