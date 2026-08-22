/-
================================================================
  第 06 次優化（前半）— 抽象計數器型別 `Ticks`
  檔案      : SortRubric/Opt06_Ticks.lean
  依賴      : 無（純 Lean，不依賴 Velvet）
----------------------------------------------------------------
  這個檔案**只有型別**，沒有排序、沒有 method、沒有 spec。

  分成獨立模組的理由是 R16：`Ticks` 的唯一公開起點
  `Ticks.mkForTesting` 定義在這裡，而 `private mk` 的作用域是**模組**。
  把型別單獨關進一個小模組，等於把「能造出 `Ticks` 的程式碼」
  縮到這 40 行以內；模組外的每一個建構點都必須寫出
  `Ticks.mkForTesting` 這個字，因此可以用 grep 完整列舉
  （`check_isolation.sh` 的 R16 段）。

  如果把型別和排序放在同一個檔，實作自己就落在 `private` 的作用域內，
  這個列舉性質就沒有了。
----------------------------------------------------------------
  這一步關掉的洞: 「老實計費，最後 `ticks := ticksOld`」
  仍然活著的洞: 計數器**分身**（複製一個值不需要建構子）→ 第 09 次
----------------------------------------------------------------
  狀態: [x] 完成
================================================================
-/

namespace SortRubric.Opt06

/-- 抽象計數器。

`private mk` 是整個第 06 次的全部內容——模組外**造不出** `Ticks` 值，
只能把手上已有的那個往前推。

★ **禁止清單**（違反其中任一條，M1 就靜默失效，而且不會有任何錯誤訊息）：

- 不得 `deriving` 任何造得出值的 typeclass：`Inhabited` / `OfNat` / `Zero`
- 不得定義 `Nat → Ticks` 的 coercion
- 不得導出 `Ticks.zero` / `Ticks.ofNat` / 任何 `Ticks.mk` 的別名

`Ticks.rec` / `Ticks.casesOn` **不是洞**——它們只能消解，不能造。
`Repr` / `DecidableEq` 之類**只消費不生產**的 typeclass 同理，不在禁止清單上
（本檔一個都沒 derive，是因為用不到，不是因為不安全）。 -/
structure Ticks where
  private mk ::
  /-- 目前累計的比較次數。**可讀**——規格要談它。 -/
  val : Nat

namespace Ticks

/-- 往前推一格。**模組外唯一能對 `Ticks` 做的事。** -/
def bump (t : Ticks) : Ticks := ⟨t.val + 1⟩

/-- `bump` 的規格。`Ticks` 是 structure，`loom_solve` 對它沒有原生支援，
所有關於 `.val` 的算術都要餵這條。依 P1 保持 **local**（`grind [Ticks.val_bump]`）。 -/
theorem val_bump (t : Ticks) : (bump t).val = t.val + 1 := rfl

/-- ★ **唯一的公開起點，只供 SPOTs 與 `#eval`。**

`Cheats/` 與所有實作檔**不得使用**——由 R16 強制，
`check_isolation.sh` 會 grep 整個 `SortRubric/` 列舉建構點。

為什麼不能改叫 `Ticks.zero` 公開出去：那等於把 `ticks := Ticks.zero`
送回作弊者手上，也就是把這一步剛殺掉的 `ResetToOld` 原封不動放回來。
名字寫成 `mkForTesting` 不是禮貌，是**讓 grep 找得到**。 -/
def mkForTesting (n : Nat) : Ticks := ⟨n⟩

end Ticks

end SortRubric.Opt06
