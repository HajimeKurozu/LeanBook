import LeanBook.NatSemiring.Mult

example (m n : MyNat) : m * (n + 1) + 2 * (m + n) = m * n + 3 * m + 2 * n := by
  rw [MyNat.mul_add]
  guard_target =ₛ m * n + m * 1 + 2 * (m + n) = m * n + 3 * m + 2 * n
  sorry

example (m n : MyNat) : m * (n + 1) + 2 * (m + n) = m * n + 3 * m + 2 * n := by
  rw [MyNat.mul_add m n 1, MyNat.mul_add 2 m n]
  guard_target =ₛ m * n + m * 1 + (2 * m + 2 * n) = m * n + 3 * m + 2 * n
  sorry

example (m n : MyNat) : m * (n + 1) + 2 * (m + n) = m * n + 3 * m + 2 * n := by
  simp only [MyNat.mul_add]
  guard_target =ₛ m * n + m * 1 + (2 * m + 2 * n) = m * n + 3 * m + 2 * n
  sorry


example (m n : MyNat) : m * (n + 1) + (2 + m) * m = m * n + 3 * m + m * m := by
  simp only [MyNat.mul_add, MyNat.add_mul]
  guard_target =ₛ m * n + m * 1 + (2 * m + m * m) = m * n + 3 * m + m * m
  sorry

macro "distrib" : tactic => `(tactic| simp only [MyNat.mul_add, MyNat.add_mul])

example (m n : MyNat) : m * (n + 1) + (2 + m) * m = m * n + 3 * m + m * m := by
  distrib
  guard_target =ₛ m * n + m * 1 + (2 * m + m * m) = m * n + 3 * m + m * m
  sorry

macro "distrib" : tactic => `(tactic| focus
  simp only [MyNat.mul_add, MyNat.add_mul]
  simp only [MyNat.mul_zero, MyNat.zero_mul, MyNat.mul_one, MyNat.one_mul]
  ac_rfl
)

example (m n : MyNat)
  : m * (n + 1) + (2 + n) * n = m * n + m + 2 * n + n * n := by
  distrib


example (m n : MyNat) : m * (n + 1) + (2 + m) * m = m * n + 3 * m + m * m := by
  simp only [MyNat.mul_add, MyNat.add_mul]
  simp only [MyNat.mul_zero, MyNat.zero_mul, MyNat.mul_one, MyNat.one_mul]
  fail_if_success ac_rfl
  guard_target =ₛ m * n + m + (2 * m + m * m) = m * n + 3 * m + m * m
  sorry


example (m n : MyNat) : m * (n + 1) + (2 + m) * m = m * n + 3 * m + m * m := by
  rw [show 3 = 1 + 2 from rfl]
  rw [show 2 = 1 + 1 from rfl]
  simp only [MyNat.mul_add, MyNat.add_mul]
  simp only [MyNat.mul_zero, MyNat.zero_mul, MyNat.mul_one, MyNat.one_mul]

  ac_rfl

macro "distrib" : tactic => `(tactic| focus
  rw [show 3 = 1 + 1 +1 from rfl]
  rw [show 2 = 1 + 1 from rfl]
  simp only [MyNat.mul_add, MyNat.add_mul]
  simp only [MyNat.mul_zero, MyNat.zero_mul, MyNat.mul_one, MyNat.one_mul]
  ac_rfl
)

example (m n : MyNat) : m * (n + 1) + (2 + m) * m = m * n + 3 * m + m * m := by
  distrib


theorem unfoldNatLit (x : Nat)
  : (OfNat.ofNat (x + 2) : MyNat) = (OfNat.ofNat (x + 1) : MyNat) + 1 :=
  rfl

macro "expand_num" : tactic => `(tactic| focus
  simp only [unfoldNatLit]
  simp only [Nat.reduceAdd]
  dsimp only [OfNat.ofNat]
  simp only [
    show MyNat.ofNat 1 = 1 from rfl,
    show MyNat.ofNat 0 = 0 from rfl
  ]
)


macro "distrib" : tactic => `(tactic| focus
  expand_num
  simp only [
    MyNat.mul_add,
    MyNat.add_mul,
    MyNat.mul_zero,
    MyNat.zero_mul,
    MyNat.mul_one,
    MyNat.one_mul
  ]
  ac_rfl
)
example (m n : MyNat) : (m + 4) * n + n = m * n + 5 * n := by
  distrib

example (m n : MyNat) : m * n + n * n = (m + n) * n := by
  sorry



macro "expand_num" : tactic => `(tactic| focus
  try simp only [unfoldNatLit, Nat.reduceAdd]
  try dsimp only [OfNat.ofNat]
  try simp only [
    show MyNat.ofNat 1 = 1 from rfl,
    show MyNat.ofNat 0 = 0 from rfl
  ]
)

macro "distrib" : tactic => `(tactic| focus
  expand_num
  try simp only [
    MyNat.mul_add,
    MyNat.add_mul,
    MyNat.mul_zero,
    MyNat.zero_mul,
    MyNat.mul_one,
    MyNat.one_mul
  ]
  try ac_rfl
)

example (m n : MyNat) : m * n + n * n = (m + n) * n := by
  distrib


example (n : MyNat) : ∃ s t : MyNat, s * t = n * n + 8 * n + 16 := by
  exists n + 4, n + 4
  distrib
