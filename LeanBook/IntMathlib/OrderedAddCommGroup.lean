import LeanBook.IntMathlib.PartialOrder

theorem MyInt.add_le_add_left (a b : MyInt) (h : a ≤ b) (c : MyInt)
    : a + c ≤ b + c := by
  notation_simp at *
  obtain ⟨m, hm⟩ := h
  use m
  have : a + c + ↑ m = b + c := calc
   _ = (a + ↑ m) + c := by ac_rfl
   _ = b + c := by rw [hm]
  assumption

instance : IsOrderedAddMonoid MyInt where
--  add_le_add_left := MyInt.add_le_add_left
-- 変更前: add_le_add_left := MyInt.add_le_add_left
-- 変更後 (交換法則で左右を合わせる):
  add_le_add_left := fun a b h c => by
    rw [MyInt.add_comm c a, MyInt.add_comm c b]
    exact MyInt.add_le_add_left a b h c


example {a : MyInt} (nneg : 0 ≤ a) : ∃ k : MyNat, a = ↑ k := by
  notation_simp at nneg
  obtain ⟨k, hk⟩ := nneg
  use k
  simp_all
