/-

3.6.命題の妥当性の例

Lean の標準ライブラリには、多くの有効な命題論理の証明が含まれており、これらはすべてご自身の証明として自由にご利用いただけます。
以下のリストには、いくつかの一般的なアイデンティティが含まれています。

-/

/-

Commutativity:
p ∧ q ↔ q ∧ p
p ∨ q ↔ q ∨ p

Associativity:
(p ∧ q) ∧ r ↔ p ∧ (q ∧ r)
(p ∨ q) ∨ r ↔ p ∨ (q ∨ r)

Distributivity:
p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r)
p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r)

Other properties:
(p → (q → r)) ↔ (p ∧ q → r)
((p ∨ q) → r) ↔ (p → r) ∧ (q → r)
¬(p ∨ q) ↔ ¬p ∧ ¬q
¬p ∨ ¬q → ¬(p ∧ q)
¬(p ∧ ¬p)
p ∧ ¬q → ¬(p → q)
¬p → (p → q)
(¬p ∨ q) → (p → q)
p ∨ False ↔ p
p ∧ False ↔ False
¬(p ↔ ¬p)
(p → q) → (¬q → ¬p)

These require classical reasoning:
(p → r ∨ s) → ((p → r) ∨ (p → s))
¬(p ∧ q) → ¬p ∨ ¬q
¬(p → q) → p ∧ ¬q
(p → q) → (¬p ∨ q)
(¬q → ¬p) → (p → q)
p ∨ ¬p
(((p → q) → p) → p)

-/

/-
Sorry identifier は、魔法のようにあらゆるものの証明を生成し、あるいはあらゆるデータ型のオブジェクトを提供します。
もちろん、証明手法としては不健全です――たとえば、偽を証明するために使用できます――そして、Leanは、ファイルがそれに依存する定理を使用またはインポートする際に、厳しい警告を発生させます。
しかし、それは長い証明を段階的に構築するのに非常に有用です。校正を上から下へ書き始め、sorry を使用してサブ校正を記入してください。Leanがすべての謝罪を含む用語を受け入れていることを確認してください。
もし受け入れられない場合は、修正すべき誤りがあります。それから戻って、各謝罪を実際の証拠に置き換え、残りが残らないまで続けてください。

こちらは別の便利なコツです。「Sorry」の代わりに、アンダースコアの _ をプレースホルダーとして使用できます。ご承知のとおり、これはLeanに対し、議論が暗黙的であり、自動的に入力すべきであることを伝えています。
Leanがそれを試みて失敗した場合、エラーメッセージ「don't know how to synthesize placeholder」が表示され、続いて期待している用語のタイプと、コンテキスト内で利用可能なすべてのオブジェクトおよび仮説が返されます。
言い換えれば、未解決のプレースホルダーごとに、Leanはその時点で埋める必要があるサブゴールを報告します。その後、これらのプレースホルダーを段階的に入力することで、証明を作成できます。

参考までに、上記のリストから取得した有効性のサンプル証明を2つ示します。
-/

open Classical

-- distributivity
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
      have hp : p := h.left
      Or.elim (h.right)
        (fun hq : q =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inl ⟨hp, hq⟩)
        (fun hr : r =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inr ⟨hp, hr⟩))
    (fun h : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim h
        (fun hpq : p ∧ q =>
          have hp : p := hpq.left
          have hq : q := hpq.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inl hq⟩)
        (fun hpr : p ∧ r =>
          have hp : p := hpr.left
          have hr : r := hpr.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inr hr⟩))

-- an example that requires classical reasoning
example (p q : Prop) : ¬ (p ∧ ¬q) → (p → q) :=
  fun h : ¬ (p ∧ ¬q) =>
  fun hp : p =>
  show q from
    Or.elim (em q)
      (fun hq : q => hq)
      (fun hnq : ¬q => absurd (And.intro hp hnq) h)
