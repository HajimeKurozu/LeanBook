declare_syntax_cat compClause
syntax "for" term "in" term : compClause
syntax "if" term : compClause
syntax "[" term " | " compClause,* "]" : term

macro_rules
  | `([$t |]) => `([$t])
  | `([$t | for $x in $xs]) => `(List.map (fun $x => $t) $xs)
  | `([$t | if $x]) => `(if $x then [$t] else [])
  | `([$t | $c, $cs,*]) => `(List.flatten [[$t | $cs,*] | $c])

#guard [x^2 | for x in [1, 2, 3, 4, 5]] = [1, 4, 9, 16, 25]

#guard
  let lhs := [(x, y) | for x in [1, 2, 3], for y in [4, 5]]
  let rhs := [(1, 4), (1, 5), (2, 4), (2, 5), (3, 4), (3, 5)]
  lhs = rhs

#guard [x | for x in [1, 2, 3], if x < 2] = [1]
