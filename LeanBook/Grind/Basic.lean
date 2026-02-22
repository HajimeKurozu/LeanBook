variable {α : Type} {a₁ a₂ : α}

example (f : α → α) (h : a₁ = a₂) : f (f a₁) = f (f a₂) := by
  grind

set_option trace.grind.assert true in
set_option trace.grind.eqc true in

theorem easy_proof (P : Prop) (h : P) : P := by
  grind

#print axioms easy_proof


def f : Nat → Nat := fun x => x - 1
def g : Nat → Nat := fun x => x + 1

@[grind]
theorem fg (x : Nat) : f (g x) = x := by
  dsimp [f, g]

example (a b c : Nat) (h1 : f a = b) (h2 : a = g c) : b = c := by
  grind

inductive Nat.myle (n : Nat) : Nat → Prop
  | refl : Nat.myle n n
  | step {m : Nat} : Nat.myle n m → Nat.myle n (m + 1)

infix:50 " ≤? " => Nat.myle

attribute [grind →] Nat.myle.step

variable {m n a b k : Nat}

theorem Nat.myle_trans (hnm : n ≤? m) (hmk : m ≤? k) : n ≤? k := by
  induction hmk with grind

class Group (G : Type) [One G] [Mul G] [Inv G] where
  mul_one : ∀ g : G, g * 1 = g
  one_mul : ∀ g : G, 1 * g = g
  mul_inv : ∀ g : G, g * g⁻¹ = 1
  inv_mul : ∀ g : G, g⁻¹ * g = 1
  mul_assoc : ∀ g₁ g₂ g₃ : G, g₁ * (g₂ * g₃) = (g₁ * g₂) * g₃

variable {G: Type} [One G] [Mul G] [Inv G] [Group G]

attribute [grind =>]
  Group.mul_one Group.one_mul
  Group.mul_inv Group.inv_mul Group.mul_assoc

theorem mul_right_inv {g h : G} (hy : g * h = 1) : h = g⁻¹ := calc
  _ = 1 * h := by grind
  _ = g⁻¹ := by grind

@[grind =>]
theorem mul_left_inv {g h : G} (hy : h * g = 1) : h = g⁻¹  := calc
  _ = h * 1 := by grind
  _ = g⁻¹  := by grind

theorem inv_inv (g : G) : g⁻¹⁻¹ = g := by
  grind
