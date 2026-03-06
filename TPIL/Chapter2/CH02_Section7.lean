/-

2.7.名前空間

Lean は、定義を入れ子構造の階層型名前空間にグループ化する機能を提供します。
-/

namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a
  def ffa : Nat := f (f a)

  #check a
  #check f
  #check fa
  #check ffa
  #check Foo.fa

end Foo

-- #check a  -- error
-- #check f  -- error
#check Foo.a
#check Foo.f
#check Foo.fa
#check Foo.ffa

open Foo
#check a
#check f
#check fa
#check Foo.fa

/-

名前空間「Foo」で作業していることを宣言すると、宣言するすべての識別子には
プレフィックス「Foo」のフルネームが付与されます。
名前空間内では、識別子を短い名前で参照できますが、名前空間を終了したら、
長い名前を使用しなければなりません。
セクションとは異なり、名前空間は名前が必要です。
ルートレベルには匿名の名前空間が1つだけあります。

Open コマンドは、短い名前を現在のコンテキストに引き込みます。
多くの場合、モジュールをインポートする際、短い識別子にアクセスするために、
そのモジュールに含まれる名前空間のうち1つまたは複数を開きたくなることがあります。
しかし、場合によっては、この情報を完全に修飾された名前で保護したままにしたいことがあります。
たとえば、別の名前空間の識別子と競合する場合などです。
したがって、名前空間は作業環境において名前を管理する手段を提供します。

例えば、Leanはリストを含む定義や定理を名前空間のリストにグループ化します。

-/

#check List.nil
#check List.cons
#check List.map

/-
Open List コマンドを使用すると、短い名前を使用できます。
-/

open List
#check nil
#check cons
#check map

/-
セクションと同様に、名前空間は入れ子にすることができます。
-/

namespace Foo1
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7
  def fa : Nat := f a

  namespace Bar
    def ffa : Nat := f (f a)
    #check fa
    #check ffa
  end Bar

  #check fa
  #check Bar.ffa

end Foo1

#check Foo1.fa
#check Foo1.Bar.ffa

open Foo1
#check fa
#check Bar.ffa

/-
閉じられた名前空間は、後で別のファイルでも再度開くことができます：
-/

namespace Foo2
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a
end Foo2

#check Foo2.a
#check Foo2.f

namespace Foo2
  def ffa : Nat := f (f a)

end Foo2

/-
セクションと同様に、入れ子の名前空間は開く順序で閉じる必要があります。
名前空間とセクションは異なる目的を持ち、名前空間はデータを整理し、
セクションは定義に挿入するための変数を宣言します。
セクションは、set_option や open などのコマンドの範囲を区切る際にも便利です。

しかしながら、多くの点で、名前空間 ... エンドブロックはセクション ... エンドブロックと同様に動作します。
特に、名前空間内で変数コマンドを使用する場合、そのスコープは名前空間に限定されます。
同様に、名前空間内で open コマンドを使用した場合、その効果は名前空間が閉じられたときに消えます。
-/
