#check Classical.em

#print axioms Classical.em

#check Classical.choice

def Surjective {X Y :Type} (f : X → Y) : Prop :=
  ∀ y : Y, ∃ x : X, f x = y

example : Surjective (fun x : Nat => x) := by
  intro y
  exists y


variable {X Y : Type}

noncomputable def inverse (f : X → Y) (hf : Surjective f) : Y → X := by
  intro y

  have : Nonempty {x // f x = y} := by
    let ⟨x, hx⟩ := hf y
    exact ⟨⟨x, hx⟩⟩

  have x := Classical.choice this
  exact x.val


theorem double_negation_of_contra_equiv (P : Prop)
  (contra_equiv : ∀ (P Q : Prop), (¬ P → ¬ Q) ↔ (Q → P)) : ¬¬P → P := by
  have := contra_equiv P True
  rw [show ¬ True ↔ False from by simp] at this
  rw [show (True → P) ↔ P from by simp] at this
  rw [show (¬P → False) ↔ ¬¬ P from by rfl] at this
  rw [this]
  simp

#print axioms double_negation_of_contra_equiv
