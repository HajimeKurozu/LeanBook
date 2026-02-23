/-

2.2.オブジェクトとしての型

Lean の従属型理論が単純型理論を拡張する一つの方法は、
型そのもの――ナットやブールのようなエンティティ――が第一級の市民である、
すなわち彼ら自身が対象であるということです。
そのようにするには、各々がタイプを持つ必要があります。
-/

#check Nat
#check Bool
#check Nat → Bool
#check Nat × Bool
#check Nat → Nat
#check Nat × Nat → Nat
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check Nat → Nat → Bool
#check (Nat → Nat) → Nat

/-
上記の各式は Type 型のオブジェクトであることが確認できます。
型に対して新しい定数を宣言することもできます。
-/

def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check α
#check F α
#check F Nat
#check G α
#check G α β
#check G α Nat

/-
上記の例が示すように、Type → Type → Type 型の関数、
すなわちデカルト積 Prod の例をすでにご覧になっているでしょう。
-/

-- def α : Type := Nat
-- def β : Type := Bool
#check Prod α β
#check α × β
#check Prod Nat Nat
#check Nat × Nat

/-こちらは別の例です。任意の型αが与えられると、
型リストαは型αの要素のリストの型を示します。-/

-- def α : Type := Nat
#check List α
#check List Nat

/-Lean のすべての式には型があることを考えると、タイプ自体の型はどのタイプを
持つのかと問うのは自然なことです。-/

#check Type

/-実際に、Lean のタイピングシステムの最も微妙な側面の一つに出くわしました。
Lean の根底にある基盤は、無限の種類の階層を持っています：-/

#check Type
#check Type 1
#check Type 2
#check Type 3
#check Type 4

/-
タイプ0を「小さい」または「普通」なタイプの宇宙と考えてください。
タイプ1は、タイプ0を要素として含む、より大きなタイプの宇宙であり、
タイプ2は、タイプ1を要素として含む、さらに大きなタイプの宇宙です。
リストは無限です：すべての自然数 n に対してタイプ n が存在します。
Type は Type 0 の略語です。-/

#check Type
#check Type 0

/-以下の表は、議論されている関係を具体化するのに役立つかもしれません。
X軸に沿った動きは宇宙の変化を表し、y軸に沿った動きは時に「度」と呼ばれる変化を表します。-/

/-
sort
Prop (Sort 0)
Type (Sort 1)
Type 1 (Sort 2)
Type 2 (Sort 3)
...
type
True
Bool
Nat -> Type
Type -> Type 1
...
term
True.intro
true
fun n => Fin n
fun (_ : Type) => Type
...
-/

/-しかしながら、いくつかの操作は型ユニバース上で多型である必要があります。
例えば、リストαは、どのタイプの宇宙αが存在していても、任意のタイプαに対して意味があるはずです。
これは関数「List」の型シグネチャについて説明しています。-/

#check List

/-ここで u は型レベルにわたる変数です。#Check コマンドの出力は、α が Type u を持つたびに、
List α も Type u を持つことを意味します。関数 Prod は同様に多型です：-/

#check Prod

/-ポリモーフィック定数を定義するために、Lean は universe コマンドを使用して universe 変数を明示的に
宣言できるようにします。-/

--universe u
def FF (α : Type u) : Type u := Prod α α
#check FF -- F.{u} : Type u → Type u

/-F を定義する際に universe パラメータを指定することで、universe コマンドを回避できます。-/

def FFF.{u} (α : Type u) : Type u := Prod α α
#check FFF
