/-

4.2.平等

それでは、Lean のライブラリで定義された最も根本的な関係の一つである平等関係に向きましょう。
帰納型に関する章では、Lean の論理フレームワークのプリミティブから等価性がどのように定義されるかを説明します。
その間、こちらでそれの使い方を説明します。

もちろん、等価性の根本的な性質は、それが同値関係であるということです：

-/

#check Eq.refl
#check Eq.symm
#check Eq.trans

/-
Leanに暗黙の引数（ここではメタ変数として表示されています）を挿入しないように指示することで、出力を読みやすくすることができます。
-/

universe u
#check @Eq.refl.{u}
#check @Eq.symm.{u}
#check @Eq.trans.{u}

/-
碑文 .{u} は、Lean に宇宙 u の定数をインスタンス化するよう指示します。

したがって、例えば、前節の例を等価関係に特化することができます。
-/

variable (α : Type) (a b c d : α)
variable (hab : a = b) (hcb : c = b) (hcd : c = d)

example : a = d :=
  Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd

/-
投影表記も使用できます。
-/

example : a = d := (hab.trans hcb.symm).trans hcd

/-
反射性は見た目以上に強力です。構文の微積分における項は計算的解釈を有し、論理的枠組みは共通の還元の項を同一として扱うことをご承知ください。
その結果、いくつかの非自明な同一性は反射性によって証明できます：
-/

variable (α β : Type)

example (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl _
example (a : α) (b : β) : (a, b).1 = a := Eq.refl _
example : 2 + 3 = 5 := Eq.refl _

/-
このフレームワークの機能は非常に重要であり、ライブラリは Eq.refl _ の表記法 rfl を定義しています。
-/

example (f : α → β) (a : α) : (fun x => f x) a = f a := rfl
example (a : α) (b : β) : (a, b).1 = a := rfl
example : 2 + 3 = 5 := rfl

/-
しかし、平等は単なる等価関係以上のものです。それは、すべての主張が等価性を尊重するという重要な性質を持ち、真理値を変えることなく等しい表現を置き換えることができるという意味です。
すなわち、h1 : a = b かつ h2 : p a と与えられた場合、置換を用いて p b の証明を構築することができます: Eq.subst h1 h2.
-/

example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) (h2 : p a) : p b :=
  Eq.subst h1 h2

example (α : Type) (a b : α) (p : α → Prop)
    (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2 -- ▸ : \t

/-
第2プレゼンテーションの三角形は、Eq.subst と Eq.symm の上に構築されたマクロであり、\t と入力することで入力できます。

規則 Eq.subst は、より明示的な置換を実行する以下の補助規則を定義するために使用されます。それらは適用用語、すなわち形式の用語を扱うように設計されています。
具体的には、congrArg は引数を置き換えるために使用でき、congrFun は適用されている用語を置き換えるために使用でき、さらに congr は両方を同時に置き換えるために使用できます。
-/

variable (α : Type)
variable (a b : α)
variable (f g : α → Nat)
variable (h₁ : a = b)
variable (h₂ : f = g)

example : f a = f b := congrArg f h₁
example : f a = g a := congrFun h₂ a
example : f a = g b := congr h₂ h₁

/-
Lean のライブラリには、以下のような多数の一般的なアイデンティティが含まれています。
-/

variable (a b c : Nat)

example : a + 0 = a := Nat.add_zero a
example : 0 + a = a := Nat.zero_add a
example : a * 1 = a := Nat.mul_one a
example : 1 * a = a := Nat.one_mul a
example : a + b = b + a := Nat.add_comm a b
example : a + b + c = a + (b + c) := Nat.add_assoc a b c
example : a * b = b * a := Nat.mul_comm a b
example : a * b * c = a * (b * c) := Nat.mul_assoc a b c
example : a * (b + c) = a * b + a * c := Nat.mul_add a b c
example : a * (b + c) = a * b + a * c := Nat.left_distrib a b c
example : (a + b) * c = a * c + b * c := Nat.add_mul a b c
example : (a + b) * c = a * c + b * c := Nat.right_distrib a b c

/-
Nat.mul_add と Nat.add_mul は、それぞれ Nat.left_distrib と Nat.right_distrib の代替名であることにご留意ください。
上記の性質は自然数（型 Nat）に対して述べられています。

以下は、置換と結合性および分配性を組み合わせた自然数の計算例です。
-/

example (x y : Nat) :
    (x + y) * (x + y) =
    x * x + y * x + x * y + y * y :=
  have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
    Nat.mul_add (x + y) x y
  have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
    (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h1
  h2.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm

/-
置換が行われる文脈を提供する Eq.subst の第2暗黙パラメータは、型 α → Prop であることに注意してください。したがって、この述語を推論するには、より高次の統一のインスタンスが必要です。
一般的に言えば、より高次ユニファイアが存在するかどうかを判定する問題は決定不可能であり、Leanは最大でも不完全かつ近似的な解決策を提供できる。その結果、Eq.subst は必ずしもご希望通りに動作するわけではありません。
マクロ h ▸ e は、この暗黙パラメータを計算するために、より効果的なヒューリスティックを使用し、Eq.subst の適用が失敗する状況でしばしば成功します。

方程式的推論が非常に一般的で重要であるため、リーンはそれをより効果的に実行するための多数のメカニズムを提供します。次のセクションでは、計算証明をより自然で明示的に記述できる構文を提供します。
しかし、より重要なのは、方程式的推論が用語リライター、簡略化、その他の自動化によって支えられていることです。「Rewriter」と「simplifier」という用語は次のセクションで簡潔に説明され、次の章でより詳しく説明されます。
-/
