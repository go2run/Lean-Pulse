import Velvet.Std
import LeanLC917

/-!
# LeetCode 917 — Reverse Only Letters（Velvet 版）

> 字母（A–Z / a–z）整體反轉，非字母留在原位。
> `"Test1ng-Leet=code-Q!"` → `"Qedo1ct-eeLg=ntse-T!"`

命令式的雙指標解法，用來量 Velvet 自動化的邊界在哪。
規格裡的 `isLetter` / `revOnly` 來自 `LeanLC917.lean`（純函數版，已完整證明），
在這裡當**參考實作**用——規格不必高效，只要說清楚什麼是對的。

| | 規格 | 結果 |
|---|---|---|
| §1 雙指標 | 完整（等於 `revOnly`） | **`loom_solve` 證不出來** |
| §2 雙指標 | 弱規格（長度／字母位置／非字母不動／multiset） | 自動過，但**不足以蘊涵題目要求** |
| `LeanLC917.lean` | 完整（三條，唯一決定答案） | **完整證明** |

結論先講：卡住的不是「反轉字母」這件事，是**雙指標迴圈的不變式**。
細節見 §1 底下記錄的實際失敗訊息。
-/

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/-! ## 1. 完整規格（證不出來）

標準的 LeetCode 解法：兩個指標往中間夾，遇到非字母就跳過，兩邊都是字母才交換。
規格直接寫「結果等於參考實作」——一條 `ensures` 就把題目說完。 -/

method ReverseOnlyLetters (mut a: Array Char) return (u: Unit)
    require a.size > 0
    ensures a.toList = revOnly aOld.toList
    do
    let mut i := 0
    let mut j := a.size - 1
    while i < j
      invariant a.size = aOld.size
      invariant j < a.size
      invariant i ≤ j + 1
      invariant ∀ k, k < a.size → isLetter a[k]! = isLetter aOld[k]!
      invariant ∀ k, k < a.size → isLetter aOld[k]! = false → a[k]! = aOld[k]!
      invariant a.toMultiset = aOld.toMultiset
      done_with i ≥ j
    do
      if !isLetter a[i]! then
        i := i + 1
      else
        if !isLetter a[j]! then
          j := j - 1
        else
          swap! a[i]! a[j]!
          i := i + 1
          j := j - 1
    return

/-
✗ 證不出來。這六條不變式**全部是真的**，而且 `loom_solve!` 把它們的
歸納步驟（進入迴圈、每次迭代保持）**全部自動證掉了**——失敗的只有最後一條：

    error: Failed to prove assertion
    error: unsolved goals
    case «ensures_1: a.toList = revOnly aOld.toList»
    invariant_1 : a.size = aOld.size
    invariant_2 : j < a.size
    invariant_3 : i ≤ j + 1
    invariant_4 : ∀ k < a.size, isLetter a[k]! = isLetter aOld[k]!
    invariant_5 : ∀ k < a.size, isLetter aOld[k]! = false → a[k]! = aOld[k]!
    invariant_6 : a.toMultiset = aOld.toMultiset
    ⊢ i_1.toList = revOnly aOld.toList

診斷很明確：**不是自動化不夠力，是不變式不夠強**。上面這組全是「逐點的」
性質（每格是不是字母、非字母有沒有動、multiset 有沒有變），對單次交換天然成立，
所以 grind 一路過關；但它們合起來根本推不出「字母被反轉」——
`ReverseOnlyLettersIdentity`（§2 末）滿足全部六條卻什麼也沒做。

真正夠強的不變式必須是三段式的：

  「[0, i) 已經放上原字串**尾端**的字母，(j, size) 已經放上原字串**開頭**的字母，
    [i, j] 這一段還是原樣」

也就是要把 `filter isLetter = reverse` 這個**全域**等式，沿著 i、j 拆成
take/drop 的接合，並且用「[0,i) 裡的字母個數」當成連結兩邊的計數。
這種不變式 grind 生不出來；人寫出來之後，每次迭代的保持性又各自是一條
獨立的 list 引理（`filter_append`、`take_succ`、`reverse_drop`…）。
成本已經超過 `LeanLC917.lean` 那個一次前向掃描 + 兩次歸納的版本。

打開下面三行可以自己重跑這個實驗：
-/
set_option maxHeartbeats 1000000 in
prove_correct ReverseOnlyLetters by
  loom_solve!

/-! ### 1.1 先測再證：PBT 確認實作本身沒錯

證不出來有兩種可能：實作錯了，或不變式不夠強。先用 PBT 排除前者。
這裡用 `LeanLC917.revOnly` 當 oracle。 -/

extract_program_for ReverseOnlyLetters
prove_precondition_decidable_for ReverseOnlyLetters
prove_postcondition_decidable_for ReverseOnlyLetters
derive_tester_for ReverseOnlyLetters

-- 全部通過就不會有輸出（實作是對的，卡住的是證明）
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arr ← Plausible.SampleableExt.interpSample (Array Char)
    let res := ReverseOnlyLettersTester arr
    pure (arr, res)
  for _ in [1: 500] do
    let res ← Plausible.Gen.run g 10
    unless res.2 do
      IO.println s!"postcondition violated for input {res.1}"
      break

-- Velvet method 是可執行的：包成 String → String 直接對三個官方範例
def rolStr (s : String) : String :=
  String.mk ((ReverseOnlyLetters s.toList.toArray).run.run).2.toList

#guard rolStr "ab-cd" = "dc-ba"
#guard rolStr "a-bC-dEf-ghIj" = "j-Ih-gfE-dCba"
#guard rolStr "Test1ng-Leet=code-Q!" = "Qedo1ct-eeLg=ntse-T!"

-- 雙指標版和參考實作逐字相同（只是這件事沒有被證明，只被測試過）
#guard rolStr "Test1ng-Leet=code-Q!" = reverseOnlyLetters "Test1ng-Leet=code-Q!"

/-! ## 2. 弱規格（自動過，但不夠）

換一組**逐點的**、對每次交換都天然成立的性質，`grind` 就吃得下了：
交換只發生在「兩端都是字母」的時候，所以字母／非字母的分布不會變、
非字母不會移動、整體 multiset 也不變。 -/

attribute [grind] Array.multiset_swap

method ReverseOnlyLettersWeak (mut a: Array Char) return (u: Unit)
    require a.size > 0
    ensures a.size = aOld.size
    ensures ∀ k, k < a.size → isLetter a[k]! = isLetter aOld[k]!
    ensures ∀ k, k < a.size → isLetter aOld[k]! = false → a[k]! = aOld[k]!
    ensures a.toMultiset = aOld.toMultiset
    do
    let mut i := 0
    let mut j := a.size - 1
    while i < j
      invariant a.size = aOld.size
      invariant j < a.size
      invariant ∀ k, k < a.size → isLetter a[k]! = isLetter aOld[k]!
      invariant ∀ k, k < a.size → isLetter aOld[k]! = false → a[k]! = aOld[k]!
      invariant a.toMultiset = aOld.toMultiset
      done_with i ≥ j
    do
      if !isLetter a[i]! then
        i := i + 1
      else
        if !isLetter a[j]! then
          j := j - 1
        else
          swap! a[i]! a[j]!
          i := i + 1
          j := j - 1
    return

prove_correct ReverseOnlyLettersWeak by
  loom_solve

/-
但這組規格**太弱**：什麼都不做也照樣滿足全部四條。
下面這個「解法」直接回傳原陣列，一樣通過驗證——
這就是 `doc/VelvetTutorial.md` §1.4 那一課在真實題目上的樣子。
-/
method ReverseOnlyLettersIdentity (mut a: Array Char) return (u: Unit)
    ensures a.size = aOld.size
    ensures ∀ k, k < a.size → isLetter a[k]! = isLetter aOld[k]!
    ensures ∀ k, k < a.size → isLetter aOld[k]! = false → a[k]! = aOld[k]!
    ensures a.toMultiset = aOld.toMultiset
    do
    return

prove_correct ReverseOnlyLettersIdentity by
  loom_solve
