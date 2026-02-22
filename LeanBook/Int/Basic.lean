import LeanBook.NatOrder.DecidableOrd

abbrev PreInt := MyNat × MyNat

def PreInt.r (m n : PreInt) : Prop :=
  match m, n with
  | (m₁, m₂), (n₁, n₂) => m₁ + n₂ = m₂ + n₁

theorem PreInt.r.refl : ∀ (m : PreInt), r m m := by
  intro (m₁, m₂)
  dsimp [r]
  ac_rfl

theorem PreInt.r.symm : ∀ {m n : PreInt}, r m n → r n m := by
  intro (m₁, m₂) (n₁, n₂) h
  dsimp [r] at *
  have : n₁ + m₂ = n₂ + m₁ := calc
    _ = m₂ + n₁ := by ac_rfl
    _ = m₁ + n₂ := by rw [← h]
    _ = n₂ + m₁ := by ac_rfl
  exact this

theorem PreInt.r.trans : ∀ {l m n : PreInt}, r l m → r m n → r l n := by
  intro (l₁, l₂) (m₁, m₂) (n₁, n₂) hlm hmn
  dsimp [r] at *
  have : m₁ + (l₁ + n₂) = m₁ + (l₂ + n₁) := calc
    _ = m₁ + n₂ + l₁ := by ac_rfl
    _ = m₂ + n₁ + l₁ := by rw [hmn]
    _ = l₁ + m₂ + n₁ := by ac_rfl
    _ = l₂ + m₁ + n₁ := by rw [hlm]
    _ = m₁ + (l₂ + n₁) := by ac_rfl
  simp_all

theorem PreInt.r.equiv : Equivalence r :=
  { refl := r.refl, symm := r.symm, trans := r.trans }

@[instance] def PreInt.sr : Setoid PreInt := ⟨r, r.equiv⟩
abbrev MyInt := Quotient PreInt.sr

#check
  let a : PreInt := (1, 3)
  (Quotient.mk PreInt.sr a : MyInt)

#check
  let a : PreInt := (1, 3)
  Quotient.mk _ a

notation:arg (priority := low) "⟦" a "⟧" => Quotient.mk _ a
#check (⟦(1, 3)⟧ : MyInt)

def MyInt.ofNat (n : Nat) : MyInt := ⟦(MyNat.ofNat n, 0)⟧

instance {n : Nat} : OfNat MyInt n where
  ofNat := MyInt.ofNat n

#check (4 : MyInt)

#check_failure (-4 : MyInt)

def PreInt.neg : PreInt → MyInt
  | (m, n) => ⟦(n, m)⟧

@[notation_simp]
theorem MyInt.sr_def (m n : PreInt) : m ≈ n ↔ m.1 + n.2 = m.2 + n.1 := by
  rfl

def MyInt.neg : MyInt → MyInt := Quotient.lift PreInt.neg <| by
  intro (a₁, a₂) (b₁, b₂) hab
  suffices (a₂, a₁) ≈ (b₂, b₁) from by
    dsimp [PreInt.neg]
    rw [Quotient.sound]
    assumption
  notation_simp at *
  simp_all

instance : Neg MyInt where
  neg := MyInt.neg

@[simp]
theorem MyInt.neg_def (x y : MyNat) : - ⟦(x, y)⟧ = (⟦(y, x)⟧ : MyInt) := by
  dsimp [Neg.neg, MyInt.neg, PreInt.neg]
  rfl

#check (-4 : MyInt)

#check_failure -4

#check Setoid


variable {α : Type} {r : α → α → Prop}

private theorem Ex.symm (refl : ∀ x, r x x) (h : ∀ x y z, r x y → r y z → r z x)
    : ∀ {x y : α}, r x y → r y x := by
  intro x y hxy
  have := h x y y
  exact this hxy (refl y)

private theorem Ex.equiv (refl : ∀ x, r x x)
    (h : ∀ x y z, r x y → r y z → r z x) : Equivalence r := by
  constructor
  case refl => exact refl
  case symm =>
    intro x y hxy
    have := h x y y
    exact this hxy (refl y)
  case trans =>
    intro x y z hxy hyz
    have lem := h z y x
    exact lem (Ex.symm refl h hyz) (Ex.symm refl h hxy)
