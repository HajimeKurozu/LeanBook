import LeanBook.IntMathlib.OrderedAddCommGroup

theorem MyInt.mk_def (x y : MyNat) : ⟦(x, y)⟧ = (x : MyInt) - (y : MyInt) := by
  simp [ofMyNat]

def PreInt.bpos (n : PreInt) : Bool :=
  match n with
  | (n₁, n₂) => decide (n₂ ≤ n₁)

def MyInt.bpos : MyInt → Bool := Quotient.lift PreInt.bpos <| by
  intro (a, b) (c, d) hr
  notation_simp at hr
  dsimp [PreInt.bpos]
  suffices b ≤ a ↔ d ≤ c from by
    simp_all
  constructor <;> intro h
  case mp =>
    have : a + d ≤ a + c := calc
      _ = b + c := by rw [hr]
      _ ≤ a + c := by compatible
    simp at this
    assumption
  case mpr =>
    have : b + c ≤ a + c := calc
      _ = a + d := by rw [hr]
      _ ≤ a + c := by compatible
    simp at this
    assumption

@[simp]
theorem MyInt.bpos_def (m n : MyNat) : MyInt.bpos ⟦(m, n)⟧ = true ↔ n ≤ m := by
  dsimp [MyInt.bpos, PreInt.bpos]
  simp

@[norm_cast]
theorem MyInt.ofMyNat_le (m n : MyNat) : (m : MyInt) ≤ (n : MyInt) ↔ m ≤ n := by
  rw [MyNat.le_iff_add]
  notation_simp
  constructor <;> intro ⟨k, hk⟩
  case mp =>
    use k
    have : ↑ (m + k) = (n : MyInt) := by
      norm_cast at hk
    norm_cast at *
  case mpr =>
    use k
    rw [← hk]
    norm_cast

theorem MyInt.le_sub_iff (x y z : MyInt) : z ≤ x - y ↔ z + y ≤ x := by
  notation_simp
  constructor <;> intro ⟨k, hk⟩
  case mp =>
    use k
    have : z + y + ↑ k = x := calc
      _ = z + ↑ k + y := by ac_rfl
      _ = (x - y) + y := by simp [hk]
      _ = x := by abel
    assumption
  case mpr =>
    use k
    have : z + ↑ k = x - y := calc
      _ = (z + y + ↑ k) - y := by abel
      _ = x - y := by rw [hk]
    assumption

theorem MyInt.sub_nonneg (m n : MyInt) : 0 ≤ m - n ↔ n ≤ m := by
  have := MyInt.le_sub_iff m n 0
  simp_all

theorem MyInt.bpos_iff (z : MyInt) : MyInt.bpos z = true ↔ 0 ≤ z := by
  induction z using Quotient.inductionOn with
  | h a =>
    obtain ⟨x, y⟩ := a
    rw [MyInt.bpos_def, MyInt.mk_def]
    rw [MyInt.sub_nonneg]
    norm_cast

instance : DecidablePred (0 ≤ · : MyInt → Prop) := by
  intro n
  apply decidable_of_iff (MyInt.bpos n = true)
  exact MyInt.bpos_iff n

example : 0 ≤ (3 : MyInt) := by
  decide

instance : DecidableLE MyInt := by
  intro n m
  apply decidable_of_iff (0 ≤ m - n)
  exact MyInt.sub_nonneg m n

#eval (3 : MyInt) ≤ 4

example : (3 : MyInt) ≤ 4 := by
  decide

instance : DecidableLT MyInt := by
  intro n m
  dsimp [(· < ·), MyInt.lt]
  infer_instance

#eval (3 : MyInt) < 4

example : (3 : MyInt) < 4 := by
  decide

instance : DecidableEq MyInt := decidableEqOfDecidableLE

#eval (3 : MyInt) = 4

example : ¬ (3 : MyInt) = 4 := by
  decide

example (a : MyInt) (h : ∃ k : MyNat, a = ↑ k) : 0 ≤ a := by
  obtain⟨k, hk⟩ := h
  notation_simp
  exists k
  simp [hk]
