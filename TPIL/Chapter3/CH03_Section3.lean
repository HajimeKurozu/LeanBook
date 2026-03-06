/-

3.3.命題論理

Leanは、すべての標準的な論理接続と表記を定義します。命題接続詞は以下の表記とともに来ます。


ASCII Unicode Editor shortcut Definition
True                          True
False                         False
Not   ¬       \not, \neg.     Not
/\    ∧.      \and.           And
\/.   ∨.      \or.            Or
->.   →.      \to, \r, \imp.
<->.  ↔.      \iff, \lr.      Iff


それらはすべて、Prop. の値を取ります。

-/

variable (p q : Prop)

#check p → q → p ∧ q
#check ¬ p → p ↔ False
#check p ∨ q → q ∨ p

/-
演算の順序は次のとおりです：一次否定 ¬ が最も強く結合し、次に ∧、次に ∨、次に →、そして最後に ↔。例えば、a ∧ b → c ∨ d ∧ e は (a ∧ b) → (c ∨ (d ∧ e)) を意味します。
→ が右側にアソシエイトされることを覚えておいてください（引数が別の型ではなく Prop の要素であるため、現在は何も変わりません）、他のバイナリ結合子も同様にそうです。
したがって、p q r : Prop がある場合、式 p → q → r は「if p, then if q, then r.」と読みます。これは単に p ∧ q → r の「カレード」形です。

前章では、ラムダ抽象は→に対する「導入規則」とみなすことができると観察しました。現在の設定では、「導入」または含意の設定方法が示されています。
アプリケーションは「除外ルール」とみなすことができ、証明において「削除」する方法や含意の使用方法を示します。他の命題結合はLeanのライブラリで定義されており、自動的にインポートされます。
各接続には、正典の導入規則と除外規則が付属しています。
-/

/-
3.3.1.接続詞

式 And.intro h1 h2 は、p ∧ q の証明 h1 : p および h2 : q を用いて証明を構築します。And.intro を and-introduction ルールとして記述することは一般的です。
次の例では、And.intro を使用して p → q → p ∧ q の証明を作成します。
-/

variable (p q : Prop)

example (hp : p) (hq : q) : p ∧ q := And.intro hp hq

#check fun (hp : p) (hq : q) => And.intro hp hq

/-
例のコマンドは、定理を指定せず、永続的なコンテキストに保存せずに定理を指定します。本質的には、与えられた用語が示された型を持っているかどうかを確認するだけです。
イラストに便利で、頻繁に使用いたします。

式 And.left h は、証明 h : p ∧ q から p の証明を生成します。同様に、And.right h は q の証明です。それらは一般に、左と右の排除規則として知られています。
-/

variable (p q : Prop)

example (h : p ∧ q) : p := And.left h
example (h : p ∧ q) : q := And.right h

/-
次の証明項を用いて、p ∧ q → q ∧ p を証明できるようになりました。
-/

variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  And.intro (And.right h) (And.left h)

/-
ご注意ください、and-introduction と and-elimination は、デカルト積のペアリングおよび射影演算と類似しています。
違いは、hp : p と hq : q が与えられた場合、And.intro hp hq は型 p ∧ q : Prop であり、a : α と b : β が与えられた場合、Prod.mk a b は型 α × β : Type である。
ProdはPropsでは使用できず、AndはTypesでは使用できません。∧ と × の類似性は Curry‐Howard 同型写像の別の例ですが、含意や関数空間コンストラクタとは対照的に、∧ と × は Lean で別々に扱われます。
しかし、類推を用いると、我々が先ほど構築した証明は、対の要素を入れ替える関数に似ています。

Structures and Records では、Lean の特定の型が構造体であることがわかります。つまり、その型は単一のカノニカルコンストラクタで定義され、適切な引数のシーケンスからその要素が構築されます。
すべての p q : Prop に対して、p ∧ q は例です。要素を構築する正典的な方法は、適切な引数 hp : p と hq : q に And.intro を適用することです。
Lean は、該当する型が帰納型であり、コンテキストから推測できるこのような状況で、匿名コンストラクタ表記 ⟨arg1, arg2, ...⟩ を使用することを可能にします。特に、And.intro hp hq の代わりに ⟨hp, hq⟩ と書くことがよくあります。

-/

variable (p q : Prop)
variable (hp : p) (hq : q)

#check ( ⟨hp, hq⟩ : p ∧ q)

/-
これらの角括弧は、それぞれ \< と \> を入力することで得られます。

Leanは別の有用な構文ガジェットを提供します。帰納型 Foo の式 e（いくつかの引数に適用される可能性があります）が与えられた場合、記法 e.bar は Foo.bar e の略称です。
これにより、名前空間を開くことなく関数にアクセスできる便利な方法が提供されます。例えば、以下の2つの式は同じ意味です。

-/

variable (xs : List Nat)

#check List.length xs
#check xs.length

/-
結果として、h : p ∧ q が与えられた場合、And.left に対して h.left を、And.right h に対して h.right と書くことができます。
したがって、上記のサンプル証明を便利に次のように書き換えることができます。
-/

variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  ⟨h.right, h.left⟩

/-
簡潔さと曖昧さの間には微細な境界があり、このように情報を省略すると、証明が読みにくくなることがあります。しかし、上記のような単純な構文の場合、h の型と構文の目的が顕著な場合、記法は簡潔で効果的です。

「And」のような構文を反復することは一般的です。Leanは、右側に関連付けられた入れ子構造体をフラット化することも可能であり、これら二つの証明が等価となります。

-/

variable (p q : Prop)

example (h : p ∧ q) : q ∧ p ∧ q :=
  ⟨h.right, ⟨h.left, h.right⟩⟩

example (h : p ∧ q) : q ∧ p ∧ q :=
  ⟨h.right, h.left, h.right⟩

/-
これもしばしば有用です。
-/

/-

3.3.2.離合

式 Or.intro_left q hp は、証明 hp : p から p ∨ q の証明を生成します。同様に、Or.intro_right p hq は、証明 hq : q を使用して p ∨ q に対する証明を作成します。これらは左側と右側の導入規則です。

-/

variable (p q : Prop)
example (hp : p) : p ∨ q := Or.intro_left q hp
example (hq : q) : p ∨ q := Or.intro_right p hq

/-
Or-eligination の規則はやや複雑です。この考え方は、r が p から続き、r が q から続くことを示すことにより、p ∨ q から r を証明できるということです。言い換えれば、それは事例による証明です。
式 Or.elim hpq hpr hqr において、Or.elim は hpq : p ∨ q、hpr : p → r、hqr : q → r の3つの引数を取り、r の証明を生成します。以下の例では、Or.elim を用いて p ∨ q → q ∨ p を証明します。
-/

variable (p q r : Prop)

example (h : p ∨ q) : q ∨ p :=
  Or.elim h
    (fun hp : p =>
      show q ∨ p from Or.intro_right q hp)
    (fun hq : q =>
      show q ∨ p from Or.intro_left p hq)

/-
ほとんどの場合、Or.intro_right と Or.intro_left の最初の引数は、Lean によって自動的に推測できます。
したがって、Lean は Or.inr と Or.inl を提供しており、これらは Or.intro_right _ と Or.intro_left _ の略称とみなすことができます。
したがって、上記の証明項はより簡潔に記述できます。
-/

variable (p q r : Prop)

example (h : p ∨ q) : q ∨ p :=
  Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq)

/-
完全な表現には、Lean が hp と hq のタイプを推測できるだけの十分な情報があることにご留意ください。しかし、長いバージョンで型アノテーションを使用すると、校正がより読みやすくなり、エラーの検出やデバッグに役立ちます。

Or には 2 つのコンストラクタがあるため、匿名コンストラクタ表記は使用できません。しかし、Or.elim の代わりに h.elim と書くことはまだ可能です。
-/

variable (p q r : Prop)

example (h : p ∨ q) : q ∨ p :=
  h.elim (fun hp => Or.inr hp) (fun hq => Or.inl hq)

/-
改めて、そのような略語が可読性を高めるか低下させるかについて判断すべきです。
-/

/-

3.3.3.否定と偽

否定、¬p は実際には p → False と定義されており、したがって p から矛盾を導出することにより ¬p を得ます。同様に、式 hnp hp は hp : p と hnp : ¬p から False の証明を生成します。
次の例では、これら両方の規則を使用して、(p → q) → ¬q → ¬p の証明を生成します。（記号 ¬ は \not または \neg と入力することで生成されます。）

-/

variable (p q : Prop)

example (hpq : p → q) (hnq : ¬ q) : ¬ p :=
  fun hp : p =>
  show False from hnq (hpq hp)

/-
結合法 False は単一の除去規則である False.elim を持ち、矛盾からあらゆるものが導かれるという事実を表します。この規則は時々「ex falso」（ex falso sequitur quodlibet の略）または「爆発原理」と呼ばれます。
-/

variable (p q : Prop)

example (hp : p) (hnp : ¬ p) : q := False.elim (hnp hp)

/-
Falsity から導かる任意の事実 q は False.elim における暗黙の引数であり、自動的に推論されます。このパターンは、矛盾する仮説から恣意的な事実を導き出しており、かなり一般的であり、不条理として表現されます。
-/

variable (p q : Prop)

example (hp : p) (hnp : ¬ p) : q := absurd hp hnp

/-
例えば、ここでは ¬p → q → (q → p) → r の証明があります。
-/

variable (p q r : Prop)

example (hnp : ¬ p) (hq : q) (hqp : q → p) : r :=
  absurd (hqp hq) hnp

/-
ちなみに、False が除外ルールのみを持つのと同様に、True が導入ルールのみを持つように、True.intro は True です。言い換えれば、Trueは単に真であり、正典的な証明であるTrue.introがあります。
-/

/-

3.3.4.論理的等価性

式 Iff.intro h1 h2 は、h1 : p → q および h2 : q → p から p ↔ q の証明を生成します。式 Iff.mp h は、h : p ↔ q から p → q の証明を生成します。
同様に、Iff.mpr h は h : p ↔ q から q → p の証明を生成します。こちらは p ∧ q ↔ q ∧ p の証明です。

-/

variable (p q : Prop)

theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q =>
      show q ∧ p from And.intro (And.right h) (And.left h))
    (fun h : q ∧ p =>
      show p ∧ q from And.intro (And.right h) (And.left h))

#check and_swap p q

variable (h : p ∧ q)

example : q ∧ p := Iff.mp (and_swap p q) h

/-
匿名コンストラクタ表記を使用して、前後方向の証明から p ↔ q の証明を構築できます。また、mp と mpr を用いた . 表記も使用できます。したがって、前述の例は以下のように簡潔に記述できます。
-/

variable (p q : Prop)

theorem and_swap_1 : p ∧ q ↔ q ∧ p :=
  ⟨ fun h => ⟨h.right, h.left⟩, fun h => ⟨h.right, h.left⟩ ⟩

example (h : p ∧ q) : q ∧ p := (and_swap_1 p q).mp h
