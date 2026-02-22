import LeanBook.NatOrder.StrictOrder
import LeanBook.NatOrder.NotationSimpTag

theorem MyNat.lt_def (m n : MyNat) : m < n ↔ m + 1 ≤ n := by
  rfl

section
  attribute [local simp] MyNat.lt_def

example (m n : MyNat) : m < n := by
  simp
  guard_target =ₛ m + 1 ≤ n
  sorry
end


section
open Lean Parser Tactic
syntax "notation_simp" (simpArgs)? (location)? : tactic
macro_rules
| `(tactic| notation_simp $[[$simpArgs,*]]? $[at $location]?) =>
  let args := simpArgs.map (·.getElems) |>.getD #[]
  `(tactic| simp only [notation_simp, $args,*] $[at $location]?)
end


attribute [notation_simp] MyNat.lt_def
example (m n : MyNat) : m < n := by
  notation_simp
  guard_target =ₛ m + 1 ≤ n
  sorry

example (m n : MyNat) (h: m < n) : m + 1 ≤ n := by
  notation_simp at *
  assumption


-- example (m n : MyNat) : m < n := by
--  simp


section
open Lean Parser Tactic
syntax "notation_simp?" (simpArgs)? (location)? : tactic
macro_rules
| `(tactic| notation_simp? $[[$simpArgs,*]]? $[at $location]?) =>
  let args := simpArgs.map (·.getElems) |>.getD #[]
  `(tactic| simp? only [notation_simp, $args,*] $[at $location]?)
end

--section
--open Lean Parser Tactic
--syntax "notation_simp?" (simpArgs)? (location)? : tactic
--macro_rules
--| `(tactic| notation_simp? $[[$simpArgs,*]]? $[at $location]?) =>
--  let args := simpArgs.map (·.getElems) |>.getD #[]
--  `(tactic| simp? only [notation_simp, $args,*] $[at $location]?)
--end


-- example (m n : MyNat) : m < n := by
--  notation_simp?


example (a b : MyNat) (h1 : a < b) (h2 : b < a) : False := by
  notation_simp at *
  have : b + 1 ≤ b := calc
    _ ≤ a := by apply h2
    _ ≤ a + 1 := by exact MyNat.le_add_one_right a
    _ ≤ b := by apply h1

  rw [MyNat.le_iff_add] at this
  obtain ⟨k, hk⟩ := this
  have : 1 + k = 0 := by
    rw [show b + 1 + k = b + (1 + k) from by ac_rfl] at hk
    simp_all
  simp_all
