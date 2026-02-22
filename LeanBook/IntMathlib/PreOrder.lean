import LeanBook.IntMathlib.Mul

private def MyInt.const (z : MyInt) : MyInt → MyInt := fun _ => z
#check_failure MyInt.const (0 : MyNat)

def MyInt.ofMyNat (n : MyNat) : MyInt := ⟦(n, 0)⟧
#check MyInt.const (.ofMyNat 0)

instance : Coe MyNat MyInt where
  coe := MyInt.ofMyNat

#check MyInt.const (0 : MyNat)

example : ((0 : MyNat) : MyInt) = (0 : MyInt) := by
  guard_target =ₛ MyInt.ofMyNat 0 = 0
  sorry

attribute [coe] MyInt.ofMyNat

@[simp]
theorem MyInt.ofMynat_zero_eq_zero : MyInt.ofMyNat 0 = (0 : MyInt) := by
  dsimp [MyInt.ofMyNat]
  rfl

example : ((0 : MyNat) : MyInt) = (0 : MyInt) := by
  guard_target =ₛ ↑ (0 : MyNat) = (0 : MyInt)
  simp

@[norm_cast]
theorem MyInt.ofMyNat_inj {m n : MyNat}
    : (m : MyInt) = (n : MyInt) ↔ m = n := by
  constructor <;> intro h
  case mp =>
    have : (m, 0) ≈ (n, 0) := by
      exact Quotient.exact h
    notation_simp at this
    simp_all
  case mpr =>
    rw [h]

@[simp]
theorem MyInt.ofMyNat_eq_zero {n : MyNat} : (n : MyInt) = 0 ↔ n = 0 := by
  constructor <;> intro h
  · rw [show (0 : MyInt) = ↑ (0 : MyNat) from rfl] at h
    norm_cast at h
  · simp_all

@[push_cast]
theorem MyInt.ofNat_add (m n : MyNat)
  : ↑ (m + n) = (m : MyInt) + (n : MyInt) := by
  rfl

def MyInt.le (m n :MyInt) : Prop :=
  ∃ k : MyNat, m + ↑ k = n

instance : LE MyInt where
  le := MyInt.le

@[notation_simp]
theorem MyInt.le_def (m n : MyInt) : m ≤ n ↔ ∃ k : MyNat, m + ↑ k = n := by
  rfl

def MyInt.lt (m n : MyInt) : Prop :=
  m ≤ n ∧ ¬n ≤ m

instance : LT MyInt where
  lt := MyInt.lt

@[notation_simp]
theorem MyInt.lt_def (a b : MyInt) : a < b ↔ a ≤ b ∧ ¬ (b ≤ a) := by
  rfl

@[refl]
theorem MyInt.le_refl (m : MyInt) : m ≤ m := by
  exists 0
  simp

theorem MyInt.le_trans {m n k : MyInt} (hnm : n ≤ m) (hmk : m ≤ k) : n ≤ k := by
  notation_simp at *
  obtain ⟨a, ha⟩ := hnm
  obtain ⟨b, hb⟩ := hmk
  use a + b
  push_cast
  have : n + (↑ a + ↑ b) = k := calc
   _ = (n + ↑ a) + ↑ b := by ac_rfl
   _ = m + ↑ b := by rw [ha]
   _ = k := by rw [hb]
  assumption

instance : Trans (· ≤ · : MyInt → MyInt → Prop) (· ≤ ·) (· ≤ ·) where
  trans := MyInt.le_trans

instance : Preorder MyInt where
  le_refl := MyInt.le_refl
  le_trans := by
    intro a b c hab hbc
    apply MyInt.le_trans hab hbc

example (a b c : MyInt) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  order

example (a b : MyInt) (h1 : a ≤ b) (h2 : ¬ (a < b)) : b ≤ a := by
  order
