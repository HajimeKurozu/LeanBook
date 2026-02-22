example (P: Prop) : ¬¬¬ P → ¬ P := by
  intro hn3p hp
  have hn2p : ¬¬ P := by
    intro hnp
    contradiction
  contradiction

  example (P: Prop) : ¬¬¬ P → ¬ P := by
    intro hn3p hp
    have : ¬¬ P := by
      intro hnp
      contradiction

    guard_hyp this : ¬¬ P
    contradiction

  example (P: Prop) : ¬¬ (P ∨ ¬ P) := by
    intro h
    suffices hyp : ¬ P from by
      have hyp' : P ∨ ¬ P := by
        right
        exact hyp
      contradiction
    guard_target =ₛ ¬ P

    intro hq
    have : P ∨ ¬ P := by
      left
      exact hq
    contradiction

  example (P : Prop) : (P → True) ↔ True := by
    exact?

  example (P : Prop) : (True → P) ↔ P := by
    exact?

  example (P Q : Prop) (h : ¬P ↔ Q) : (P → False) ↔ Q := by
    rw [show (P → False) ↔ ¬P from by rfl]
    rw [h]



  example (P : Prop) : ¬(P ↔ ¬ P) := by
    intro h  -- * `intro h`: 「P ↔ \not P」 を仮定する。
    have hnp : ¬ P := by  -- * `have hnp : ¬ P`: 「\not P」を導き出すためのブロック。
      intro hq  -- * `intro hq`: 「仮に P だとすると」
      have : ¬ P := by
        rw [h] at hq  -- * `rw [h] at hq`: 「仮定h を使って P を \not P に書き換えると」
        exact hq
      contradiction  -- * `contradiction`: 「P と \not P が同時に存在するので矛盾」

    have hp : P := by  -- * `have hp : P`: 「P」を導き出すためのブロック。
      rw [← h] at hnp  -- * `rw [← h] at hnp`: 「仮定h  を逆向きに使って、\not P を P に書き換える」
      exact hnp
    contradiction  --  `contradiction`: 最後に導いた P  と、先に導いた \not P が矛盾することを示す。

-- 解説：

-- 「ある命題  とその否定  が同値（等価）になることはありえない」**という論理学上の基本原理の証明
-- 数学的には「ラッセルのパラドックス」などに関連する構造を持つ、背理法を用いた証明

-- 命題：任意の命題Pに対して、「Pであることと Pでないことは同値である」ということはない。
-- この命題を背理法によって証明する。

-- 1. 仮定： まず、 が成り立つと仮定する（これを仮定hとする）。
-- 2. \notPの導出：ここで仮にPが正しいと仮定してみる。
-- * 仮定hによれば P と \not P は同値なので、P が正しいなら \not P も正しいことになる。
-- * これは「Pである」ことと「Pではない」ことが同時に成り立つことになり、矛盾する。
-- * したがって、最初の「仮にPが正しいとした」仮定が誤りであるため、 \not P であることがわかる。


-- 3. P の導出：
-- * 今、 \not P が成り立つことがわかった。
-- * 仮定 h（P ↔ \not P）を逆向きに適用すると、\npt P が成り立つならば P も成り立つことになる。


-- 4. 最終的な矛盾：
-- * 以上のステップより、「\npt P」と「P」の両方が導かれた。
-- * これは矛盾である。


-- 結論：したがって、最初の仮定「P ↔ \not P」は誤りであり、\not(P ↔ \not P) が示された。


-- theorem / lemma: 定理 / 補題
-- intro / intros: 「〜を導入する」「〜と仮定する」
-- apply: 「〜を適用する」
-- exact: 「まさにこれが証明すべき内容である」
-- induction: 「〜について数学的帰納法を用いる」
-- rw (rewrite): 「〜を用いて書き換える」
-- cases: 「〜で場合分けをする」
