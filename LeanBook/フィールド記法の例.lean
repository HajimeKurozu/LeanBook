structure Point (α : Type) where
  x : α
  y : α

#eval
  let p : Point Nat := ⟨1, 2⟩
  p.x + p.y
