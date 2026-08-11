import Velvet.Std

/-!
# Velvet 入門六例 — 可執行版

`doc/VelvetTutorial.md` 全部範例的實作，含**正確**與**錯誤**兩種版本。

錯誤版本分成兩類，讀的時候要分清楚：

* `✗ 規格太弱` —— **驗證會通過**，但方法根本不對。這類全部是活的程式碼，
  `prove_correct` 就在下面，它們真的過了。這是本教材最重要的一課。
* `✗ 證不出來` —— 實作或不變式有問題。這類只留 `method`（`method` 本身
  永遠會編譯），刻意不寫 `prove_correct`，否則 build 會紅。想看錯誤訊息就
  自己把註解掉的 `prove_correct` 打開。
-/

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/-! ## 1. Maximum — method / ensures / prove_correct -/

method Maximum (a: Int) (b: Int) return (m: Int)
    ensures m ≥ a
    ensures m ≥ b
    ensures m = a ∨ m = b
    do
    if a ≥ b then
      return a
    else
      return b

prove_correct Maximum by
  loom_solve

-- Velvet method 是可執行的 Lean 程式，回傳值包在 `DivM.res` 裡
/-- info: DivM.res 7 -/
#guard_msgs in
#eval (Maximum 3 7).run

/-- info: DivM.res 5 -/
#guard_msgs in
#eval (Maximum 5 5).run

/-
✗ 規格太弱：拿掉 `m = a ∨ m = b` 之後，`≥` 只框住一個方向，
任何夠大的數都合格 —— 所以這個「取最大值」回傳 max + 1 也照樣驗證通過。
驗證通過只代表實作符合規格，不代表規格符合意圖。
-/
method MaximumWeak (a: Int) (b: Int) return (m: Int)
    ensures m ≥ a
    ensures m ≥ b
    do
    if a ≥ b then
      return a + 1
    else
      return b + 1

prove_correct MaximumWeak by
  loom_solve

-- 練習 1：三參數版。注意第三條同樣不能省
method Maximum3 (a: Int) (b: Int) (c: Int) return (m: Int)
    ensures m ≥ a
    ensures m ≥ b
    ensures m ≥ c
    ensures m = a ∨ m = b ∨ m = c
    do
    -- Velvet 沒有 `else if`，必須巢狀
    if a ≥ b then
      if a ≥ c then
        return a
      else
        return c
    else
      if b ≥ c then
        return b
      else
        return c

prove_correct Maximum3 by
  loom_solve

-- 練習 2：兩條 ensures 就唯一決定 Abs —— 「等於自己或相反數」＋「非負」
method Abs (x: Int) return (r: Int)
    ensures r = x ∨ r = -x
    ensures r ≥ 0
    do
    if x ≥ 0 then
      return x
    else
      return -x

prove_correct Abs by
  loom_solve

/-! ## 2. LastDigit — require、Nat vs Int、solver hint -/

/-
要避開的寫法：用 `Int` 就得自己扛 `require n ≥ 0`，
而且還多一條 `ensures 0 ≤ d` 要證。
-/
method LastDigitInt (n: Int) return (d: Int)
    require n ≥ 0
    ensures 0 ≤ d
    ensures d < 10
    ensures n % 10 = d
    do
    return n % 10

prove_correct LastDigitInt by
  loom_solve

-- `Nat` 本身排除負數：前條件消失，少一條 ensures，證明更好過。
-- 經驗法則：值不會是負的就用 `Nat`——把約束從「要證的東西」搬到型別系統。
method LastDigit (n: Nat) return (d: Nat)
    ensures d < 10
    ensures n % 10 = d
    do
    return n % 10

-- solver 缺數學知識時就補 hint（`n % 10 < 10` 屬於標準庫，grind 預設不會去翻）：
--     attribute [grind] Nat.mod_lt
-- 兩種 hint 別配錯：`[grind]` 餵 grind / `loom_solve`；
-- `[solverHint]` 餵 SMT / `loom_auto`。配錯等於沒加。
prove_correct LastDigit by
  loom_solve

-- 練習：商與餘數。`require` 是除數非零；tuple 用 .1 / .2 存取
method DivMod (a: Nat) (b: Nat) return (result: Nat × Nat)
    require b > 0
    ensures result.1 = a / b
    ensures result.2 = a % b
    do
    return (a / b, a % b)

prove_correct DivMod by
  loom_solve

/-! ## 3. IncrementAt — mut / varOld / frame condition -/

method IncrementAt (mut a: Array Int) (i: Nat) return (u: Unit)
    require i < a.size
    ensures a.size = aOld.size
    ensures a[i]! = aOld[i]! + 1
    ensures ∀ k, k < a.size ∧ k ≠ i → a[k]! = aOld[k]!
    do
    a := a.set! i (a[i]! + 1)
    return

prove_correct IncrementAt by
  loom_solve

/-- info: DivM.res ((), #[1, 8, 3]) -/
#guard_msgs in
#eval (IncrementAt #[1, 7, 3] 1).run

/-
✗ 規格太弱（frame problem）：少了「其他格子沒變」那條，
把整個陣列清空、只填回第 i 格，兩條 ensures 照樣滿足。

規格不只要說「什麼變了」，還要說「什麼沒變」。後者最容易漏，
因為它描述的是「什麼都沒發生」，寫的時候很難覺得需要說。
-/
method IncrementAtBad (mut a: Array Int) (i: Nat) return (u: Unit)
    require i < a.size
    ensures a.size = aOld.size
    ensures a[i]! = aOld[i]! + 1
    do
    let v := a[i]! + 1
    a := Array.replicate a.size 0
    a := a.set! i v
    return

prove_correct IncrementAtBad by
  loom_solve

/-- info: DivM.res ((), #[0, 8, 0]) -/
#guard_msgs in
#eval (IncrementAtBad #[1, 7, 3] 1).run

-- 練習：Swap。規格只有兩條，完全不提暫存變數——
-- 因為規格描述的是「呼叫前後的關係」，實作用什麼中間狀態不關規格的事
method Swap (mut x: Int) (mut y: Int) return (u: Unit)
    ensures x = yOld
    ensures y = xOld
    do
    let t := x
    x := y
    y := t
    return

prove_correct Swap by
  loom_solve

/- ✗ 規格太弱：只留 `x = yOld`，「把兩個都設成 y」就過關了。 -/
method SwapBad (mut x: Int) (mut y: Int) return (u: Unit)
    ensures x = yOld
    do
    x := y
    return

prove_correct SwapBad by
  loom_solve

/-! ## 4. DoubleAll — while / invariant / done_with -/

/-
陣列迴圈的四條通用不變式：
長度沒動、索引在範圍內、**已處理的前綴**達成目標、**未處理的後綴**維持原狀。
第四條最常被漏掉，少了它迴圈結束時無法排除「後綴被亂改」。
-/
method DoubleAll (mut arr: Array Int) return (u: Unit)
    ensures arr.size = arrOld.size
    ensures ∀ i, i < arr.size → arr[i]! = 2 * arrOld[i]!
    do
    let mut i := 0
    while i < arr.size
      invariant arr.size = arrOld.size
      invariant i ≤ arr.size
      invariant ∀ k, k < i → arr[k]! = 2 * arrOld[k]!
      invariant ∀ k, i ≤ k ∧ k < arr.size → arr[k]! = arrOld[k]!
      done_with i = arr.size
    do
      arr := arr.set! i (2 * arr[i]!)
      i := i + 1
    return

prove_correct DoubleAll by
  loom_solve

/-- info: DivM.res ((), #[2, 4, 6]) -/
#guard_msgs in
#eval (DoubleAll #[1, 2, 3]).run

/-
✗ 證不出來：拿掉第四條不變式（後綴維持原狀）。
迴圈結束時只知道前綴被加倍了，推不出後條件。
打開下面的 `prove_correct` 可以看 `loom_solve!` 標出斷在哪一條。
-/
method DoubleAllNoFrame (mut arr: Array Int) return (u: Unit)
    ensures arr.size = arrOld.size
    ensures ∀ i, i < arr.size → arr[i]! = 2 * arrOld[i]!
    do
    let mut i := 0
    while i < arr.size
      invariant arr.size = arrOld.size
      invariant i ≤ arr.size
      invariant ∀ k, k < i → arr[k]! = 2 * arrOld[k]!
      done_with i = arr.size
    do
      arr := arr.set! i (2 * arr[i]!)
      i := i + 1
    return

-- prove_correct DoubleAllNoFrame by
--   loom_solve!

/-! ### 4.6 先測再證：property-based testing

不變式先寫對、跑通，**再**植入 bug 觀察 PBT 抓它。順序反過來會讓人誤以為
PBT 是「不變式寫不出來時的替代品」——它不是。PBT 只能反駁，不能證明。 -/

-- ✗ 植入 bug：迴圈條件少跑一格，最後一格沒加倍。
-- 不寫 prove_correct（證不出來），改用 PBT 直接要一個具體反例。
method DoubleAllBuggy (mut arr: Array Int) return (u: Unit)
    ensures arr.size = arrOld.size
    ensures ∀ i, i < arr.size → arr[i]! = 2 * arrOld[i]!
    do
    let mut i := 0
    while i < arr.size - 1
      invariant arr.size = arrOld.size
      invariant i ≤ arr.size
      invariant ∀ k, k < i → arr[k]! = 2 * arrOld[k]!
      invariant ∀ k, i ≤ k ∧ k < arr.size → arr[k]! = arrOld[k]!
      done_with i = arr.size - 1
    do
      arr := arr.set! i (2 * arr[i]!)
      i := i + 1
    return

extract_program_for DoubleAllBuggy
prove_precondition_decidable_for DoubleAllBuggy
prove_postcondition_decidable_for DoubleAllBuggy
derive_tester_for DoubleAllBuggy

-- build 時會在輸出印出違反後條件的具體輸入
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arr ← Plausible.SampleableExt.interpSample (Array Int)
    let res := DoubleAllBuggyTester arr
    pure (arr, res)
  for _ in [1: 500] do
    let res ← Plausible.Gen.run g 10
    unless res.2 do
      IO.println s!"postcondition violated for input {res.1}"
      break

-- 練習：SumArray。累積型迴圈的不變式＝「已累積的 = 前綴的總和」。
-- 規格用遞迴 `def` 寫（而不是 `(a.extract 0 n).sum`），兩條展開引理就是 `rfl`，
-- solver 幾乎不用幫忙——選對規格形式比事後補 hint 划算。
def sumTo (a: Array Int) : Nat → Int
  | 0 => 0
  | n + 1 => sumTo a n + a[n]!

@[grind] lemma sumTo_zero (a : Array Int) : sumTo a 0 = 0 := rfl
@[grind] lemma sumTo_succ (a : Array Int) (n : Nat) :
    sumTo a (n + 1) = sumTo a n + a[n]! := rfl

method SumArray (a: Array Int) return (s: Int)
    ensures s = sumTo a a.size
    do
    let mut i := 0
    let mut acc := 0
    while i < a.size
      invariant i ≤ a.size
      invariant acc = sumTo a i
      done_with i = a.size
    do
      acc := acc + a[i]!
      i := i + 1
    return acc

prove_correct SumArray by
  loom_solve

/-- info: DivM.res 6 -/
#guard_msgs in
#eval (SumArray #[1, 2, 3]).run

/-! ### 4.5 迴圈內不能 early return：用 break / continue

迴圈**外**的 early return 沒問題；迴圈**內**不支援。
用 `break` 時 `done_with` 必須涵蓋 break 的離開條件，否則證明會斷在那裡。 -/

method CountToTen (a: Nat) return (res: Nat)
    require a > 0
    ensures res > 0
    do
    let mut x := 0
    let mut t := a
    while t > 0
      invariant x + t = a
      done_with (x = 10 ∨ t = 0)
    do
      x := x + 1
      t := t - 1
      if (x = 10) then break
    return x

prove_correct CountToTen by
  loom_solve

method SumEven (arr: Array Nat) return (res: Nat)
    ensures res = Array.sum (Array.filter (fun x => x % 2 = 0) arr)
    do
    let mut i := 0
    let mut s := 0
    while (i < arr.size)
      invariant i ≤ arr.size
      invariant s = Array.sum (Array.filter (fun x => x % 2 = 0) (Array.extract arr 0 i))
      done_with (s = Array.sum (Array.filter (fun x => x % 2 = 0) arr))
    do
      if (arr[i]! % 2 != 0) then
        i := i + 1
        continue
      s := s + arr[i]!
      i := i + 1
    return s

lemma filter_sum_snoc (arr: Array Nat) (p: Nat → Bool) :
    ∀ i, i < arr.size →
      (Array.filter p (Array.extract arr 0 i)).sum + (if (p arr[i]!) then arr[i]! else 0) =
      (Array.filter p (Array.extract arr 0 (i + 1))).sum := by
  intro i hi
  have extract_app : Array.extract arr 0 (i + 1) = Array.extract arr 0 i ++ #[arr[i]!] := by
    aesop
  rw [extract_app, Array.filter_append]
  · simp ; aesop
  · rw [Array.size_append]

attribute [grind] filter_sum_snoc

-- `loom_solve` 沒解完的部分直接往下寫 Lean tactic——這就是 Velvet 嵌在 Lean 裡的好處
prove_correct SumEven by
  loom_solve
  rw [invariant_2]
  have i_eq_size : i = arr.size := by omega
  have extract_eq : arr = (arr.extract 0 i) := by aesop
  rw [← extract_eq]

/-! ## 5. SumOfDigits — 輔助 def、method 呼叫 method -/

-- 規格不必高效，甚至不必實際可執行。它的任務是說清楚什麼是對的。
def SumDigits (n: Nat): Nat :=
  if n = 0 then 0
  else (n % 10) + SumDigits (n / 10)
termination_by n
decreasing_by grind

lemma SumDigits_unfold (n : Nat) (h : n > 0) :
    SumDigits n = (n % 10) + SumDigits (n / 10) := by
  rw [SumDigits]
  have h' : n ≠ 0 := Nat.ne_of_gt h
  simp [h']

lemma SumDigits_zero : SumDigits 0 = 0 := by
  unfold SumDigits
  simp

attribute [grind] Nat.mod_add_div SumDigits_unfold SumDigits_zero

-- 第三條 `result.2 < n` 現在用不到，但它是這個 method 的「有用性保證」：
-- 呼叫者靠它知道遞減
method PopDigit (n: Nat) return (result: Nat × Nat)
    require n > 0
    ensures result.1 = n % 10
    ensures result.2 = n / 10
    ensures result.2 < n
    do
    return (n % 10, n / 10)

attribute [grind] Nat.div_lt_self

prove_correct PopDigit by
  loom_solve

/-
不變式 `sum + SumDigits n = SumDigits number` 念出來是
**已累積的 + 還沒處理的 = 總量**，適合沒有索引的迴圈。

呼叫用左箭頭 `←`（method 是 `VelvetM` 裡的計算，不是普通函式）。
**前條件是呼叫端的義務**：`PopDigit` 的 `require n > 0` 在這裡由迴圈條件保證，
搬到迴圈外面驗證就會失敗。
-/
method SumOfDigits (number: Nat) return (sum: Nat)
    ensures sum = SumDigits number
    do
    let mut sum := 0
    let mut n := number
    while n > 0
      invariant sum + SumDigits n = SumDigits number
      invariant 0 ≤ sum
      done_with n = 0
    do
      let step ← PopDigit n
      sum := sum + step.1
      n := step.2
    return sum

-- 卡住時的除錯順序：`loom_solve!` 標出失敗位置 →
-- `loom_goals_intro` + `sorry` 看原始 goal → 補 hint → 最後才調旋鈕
-- （splits / smt.timeout / maxHeartbeats 都只是「給更多資源」，
--   缺知識的話調多久都不會過）
prove_correct SumOfDigits by
  loom_solve

/-- info: DivM.res 6 -/
#guard_msgs in
#eval (SumOfDigits 123).run

/-! ## 6. CountDown — total correctness 與 decreasing

前面五節都在 `partial`：「證明通過」的意思是**「如果它停下來」**。
`while true` 在 partial 下也可能通過，因為前提永遠不成立。

實務建議：先用 `partial` 把功能正確性弄對，最後再切 `total`。 -/

section TotalCorrectness

set_option loom.semantics.termination "total"

-- `decreasing i`：i : Nat 有下界 0，不可能無限下降，所以迴圈必然終止
method CountDown (n: Nat) return (res: Nat)
    ensures res = 0
    do
    let mut i := n
    while i > 0
      invariant i ≤ n
      decreasing i
    do
      i := i - 1
    return i

prove_correct CountDown by
  loom_solve

-- 練習 1：DoubleAll 切到 total。測度不一定是迴圈變數本身，
-- 遞增迴圈的測度通常是「還剩多少」
method DoubleAllTotal (mut arr: Array Int) return (u: Unit)
    ensures arr.size = arrOld.size
    ensures ∀ i, i < arr.size → arr[i]! = 2 * arrOld[i]!
    do
    let mut i := 0
    while i < arr.size
      invariant arr.size = arrOld.size
      invariant i ≤ arr.size
      invariant ∀ k, k < i → arr[k]! = 2 * arrOld[k]!
      invariant ∀ k, i ≤ k ∧ k < arr.size → arr[k]! = arrOld[k]!
      done_with i = arr.size
      decreasing arr.size - i
    do
      arr := arr.set! i (2 * arr[i]!)
      i := i + 1
    return

prove_correct DoubleAllTotal by
  loom_solve

/-
✗ 證不出來（練習 2）：測度不變。功能正確性照樣成立，
但 `decreasing i` 生出的遞減 goal 永遠證不了——這正是 total 比 partial 多做的事。
-/
method CountDownStuck (n: Nat) return (res: Nat)
    ensures res = 0
    do
    let mut i := n
    while i > 0
      invariant i ≤ n
      decreasing i
    do
      i := i
    return i

prove_correct CountDownStuck by
  loom_solve!

end TotalCorrectness

/-! ## 進階題

`BubbleSort` 需要兩條 `ensures`——排序好，**以及** multiset 保存。
少了第二條，回傳全零陣列也算「排序好的」。這是 §1.4 的教訓在最複雜情境下的版本。
見 `LeanPulse/BubbleSort.lean`。 -/
