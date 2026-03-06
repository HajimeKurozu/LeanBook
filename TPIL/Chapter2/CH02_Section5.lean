/-

2.5.ローカル定義🔗

Lean は、let キーワードを使用して「local」な定義を導入することも可能です。
式 let a := t1; t2 は、t2 における a のすべての出現を t1 に置き換えた結果と定義上等しい。
-/

#check let y := 2 + 2; y * y
#eval  let y := 2 + 2; y * y

def twice_double (x : Nat) : Nat :=
  let y := x + x; y * y

#eval twice_double 2

/-

ここでは、twice_double x は定義上、項 (x + x) * (x + x) と等しいです。

Let 文を連鎖させることで、複数の代入を組み合わせることができます。
-/

#check let y := 2 + 2; let z := y + y; z * z
#eval  let y := 2 + 2; let z := y + y; z * z

/-
改行が使用された場合、; は省略できます。
-/

def t (x : Nat) : Nat :=
  let y := x + x
  y * y

/-
式 let a := t1; t2 の意味が (fun a => t2) t1 の意味と非常に似ていることにご注意ください。
ただし、両者は同じではありません。最初の式では、t2 の a のすべての例を t1 の構文的略語と考えるべきです。
第2の式では、a は変数であり、式 fun a => t2 は a の値に依存せずに意味を成す必要があります。
Let構文は略語のより強い手段であり、let a := t1; t2 の形の式は (fun a => t2) t1 として表すことができません。
演習として、foo の定義が type check であるのに対し、bar の定義が行わない理由を理解しようと試みてください。
-/

def foo := let a := Nat; fun x : a => x + 2
#check foo

/-
  def bar := (fun a => fun x : a => x + 2) Nat
-/
