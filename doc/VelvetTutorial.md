# Velvet 入門：用六個例子走完一輪

> **V1 教學**：本文以 Velvet V1（Loom 架構，commit
> [`d254391`](https://github.com/verse-lab/velvet/tree/d254391d5e84546f96576e5b67dfb6bafe9fc301)，Lean `v4.24.0`）為準。
> V2（tag `v2.0`，Lean `v4.34.0`）已重寫，`loom_solve`、`DivM`、`extract_program_for`、
> `(mut …)` 參數等都不再存在，本文不適用於 V2。

> **關於這份教材**
> 每一節引進一組新語法，並且**只**引進那一組。前一節出現過的東西不再解釋，所以請照順序讀。
> 六節走完，你會寫過純函數、陣列變更、迴圈不變式、method 組合、互動式證明、終止性證明各一次。
>
> 程式碼依 Velvet 官方文件語法撰寫。第一次在你的環境跑之前，建議逐節確認——Velvet 仍在活躍開發，語法細節可能與文件有出入。

---

## 目錄

| 節 | 例子 | 引進的功能 |
|---|---|---|
| 1 | Maximum | 檔頭設定、`method` / `ensures` / `prove_correct`、`#eval`、規格太弱 |
| 2 | LastDigit | `require`、`Nat` vs `Int`、solver hint、切換 solver |
| 3 | IncrementAt | `mut` / `varOld`、陣列存取與更新、frame condition |
| 4 | DoubleAll | `while` / `invariant` / `done_with`、不變式模式、PBT |
| 5 | SumOfDigits | 輔助 `def`、method 呼叫 method、互動式證明、效能旋鈕 |
| 6 | CountDown | total correctness、`decreasing` |

---

## 1. Maximum — 第一個 Velvet 方法

### 1.1 檔頭

每個 Velvet 檔案都從這四行開始：

```lean
import Velvet.Std

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"
```

兩個 `set_option` 是**必填**的，不寫會報錯。現在先照抄，`partial` 和 `demonic` 是最常用的組合；`partial` 的確切意思在 §4.4 拆解，`demonic` 只在用到非確定性時才有差別（見附錄 C）。

### 1.2 三件套

```lean
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
```

三個部分：

- **`method`** 宣告簽章。參數逐個加括號並標型別，回傳值也要**命名**（這裡是 `m`），因為規格要用到它。
- **`ensures`** 是後條件——方法保證的性質。可以寫多條，**多條之間是 AND**，全部都得成立。
- **`prove_correct`** 觸發驗證。`loom_solve` 是自動化的第一道防線，這題它一次過。

`do` 之後是實作，語法和一般 Lean 的 `do` 區塊接近。

### 1.3 執行看看

Velvet 方法是**可執行的** Lean 程式，不是只能拿來證明的宣告：

```lean
#eval (Maximum 3 7).run    -- DivM.res 7
#eval (Maximum 5 5).run    -- DivM.res 5
```

輸出的 `DivM.res 7` 是 Velvet 的包裝格式，實際回傳值 `7` 包在裡面。

想把預期輸出寫成測試，用 `#guard_msgs`：

```lean
/--
info: DivM.res 7
-/
#guard_msgs in
#eval (Maximum 3 7).run
```

註解的開頭必須是 `/--`、結尾必須是 `-/`，少一個字元就不會生效。

### 1.4 拿掉一條 `ensures` 會怎樣

現在遮掉第三條，只留前兩條：

```lean
method MaximumWeak (a: Int) (b: Int) return (m: Int)
    ensures m ≥ a
    ensures m ≥ b
    do
    if a ≥ b then
        return a + 1        -- 明顯不是最大值
    else
        return b + 1

prove_correct MaximumWeak by
  loom_solve              -- 照樣通過
```

驗證通過了，但這個方法根本不算最大值。

原因是 `≥` 只框住**一個方向**：它說「`m` 不小於兩者」，卻沒說「`m` 必須是兩者之一」。任何足夠大的數都符合。第三條 `ensures m = a ∨ m = b` 才把 `m` 拉回值域內。

> **這是整份教材最重要的一課。** 驗證通過只代表「實作符合規格」，不代表「規格符合你的意圖」。規格寫得太弱，驗證就是在證明一件無意義的事。之後每一節都會再遇到這個問題的變形。

### 1.5 順帶一提：沒有 `else if`

Velvet **不支援** `else if`，必須巢狀：

```lean
-- ✗ 不能這樣寫
-- if m = 0 then ... else if n = 0 then ...

-- ✓ 要這樣寫
if m = 0 then
    return n + 1
else
    if n = 0 then
        return m
    else
        return m + n
```

### 練習

1. 把 `Maximum` 改成三個參數的 `Maximum3`，規格該怎麼寫才不會太弱？
2. 寫 `Abs (x: Int) return (r: Int)`。用兩條 `ensures` 就能唯一決定答案——找出是哪兩條。

---

## 2. LastDigit — 前條件與自動化調校

### 2.1 先看要避開的寫法

取一個非負整數的個位數。直覺會這樣寫：

```lean
method LastDigitInt (n: Int) return (d: Int)
    require n ≥ 0
    ensures 0 ≤ d
    ensures d < 10
    ensures n % 10 = d
    do
    return n % 10
```

**`require`** 是前條件——呼叫者必須保證的事。前條件不成立時，方法不負任何責任。

但這裡的 `require n ≥ 0` 是自找的麻煩。

### 2.2 換型別，前條件消失

```lean
method LastDigit (n: Nat) return (d: Nat)
    ensures d < 10
    ensures n % 10 = d
    do
    return n % 10
```

`Nat` 本身就排除了負數，於是：

- `require n ≥ 0` 不必寫了
- `ensures 0 ≤ d` 不必寫了
- solver 少了兩條假設要處理，證明更容易過

> **經驗法則：值不會是負的，就用 `Nat` 而不是 `Int`。** 這不只是省字，是把約束從「要證明的東西」搬到「型別系統免費給的東西」。

### 2.3 `loom_solve` 卡住了

現在跑：

```lean
prove_correct LastDigit by
  loom_solve
```

會失敗。`grind` 不知道 `n % 10 < 10`——這是模運算的性質，屬於 Lean 標準庫的知識，但 solver 預設不會去翻。

補上：

```lean
attribute [grind] Nat.mod_lt

prove_correct LastDigit by
  loom_solve              -- 現在過了
```

`attribute [grind]` 把一條引理加進 `grind` 的搜尋範圍。這是最常用的排錯手段。

### 2.4 換一個 solver

`loom_solve` 底下實際用哪個 solver，由 `loom.solver` 決定：

```lean
set_option loom.solver "grind"      -- 預設，不寫也是這個
set_option loom.solver "cvc5"       -- 換成 SMT solver
set_option loom.solver "z3"         -- 另一個 SMT solver
```

Z3 和 CVC5 在專案 build 時會自動安裝，不必另外設定。

**什麼時候換？** `grind` 對一般情況夠用，但**算術密集**的題目（大量線性不等式、模運算、除法）換 SMT 常常直接過。

換 SMT 時通常要放寬 timeout，預設只有 1 秒：

```lean
set_option loom.solver "cvc5"
set_option loom.solver.smt.timeout 4
```

### 2.5 兩種 hint，別配錯

這是最容易搞混的地方：

| Attribute | 餵給誰 | 搭配的 tactic |
|---|---|---|
| `attribute [grind]` | `grind` solver | `loom_solve`（solver 為 grind 時） |
| `attribute [solverHint]` | SMT solver | `loom_auto` |

**配錯等於沒加。** 用 `grind` 卻標 `[solverHint]`，那條引理不會被看到。

也可以混用——先讓 `grind` 處理大部分，剩下的丟給 SMT：

```lean
set_option loom.solver "grind"

attribute [solverHint] Nat.mod_lt

prove_correct LastDigit by
  loom_solve      -- grind 先做
  loom_auto       -- 剩下的用 SMT，自動帶入 solverHint 的引理
```

或是直接把引理當參數傳：

```lean
prove_correct LastDigit by
  loom_solve
  loom_smt [Nat.mod_lt, Nat.div_le_iff_le_mul_right]
```

### 練習

1. 寫 `DivMod (a: Nat) (b: Nat) return (result: Nat × Nat)`，回傳商與餘數。這題的 `require` 是什麼？（提示：tuple 元素用 `.1` / `.2` 存取。）
2. 把 §1 的 `Maximum` 改成 `Nat` 版本，然後試試 `return a + b` 能不能通過弱規格。

---

## 3. IncrementAt — 狀態變更與 frame condition

### 3.1 `mut` 與 `varOld`

到目前為止，方法的輸出都是回傳值。但很多程式是**改變傳進來的東西**：

```lean
method IncrementAt (mut a: Array Int) (i: Nat) return (u: Unit)
    require i < a.size
    ensures a.size = aOld.size
    ensures a[i]! = aOld[i]! + 1
    ensures ∀ k, k < a.size ∧ k ≠ i → a[k]! = aOld[k]!
    do
    a := a.set! i (a[i]! + 1)
    return

attribute [grind] Array.size_set

prove_correct IncrementAt by
  loom_solve
```

兩個新東西：

- **`mut`** 標在參數名前面，表示這個參數可以被修改。
- **`aOld`** 是 `a` 的**原始值**。命名規則是變數名加 `Old` 後綴，在 `ensures` 和 `invariant` 裡都能用。

沒有有意義回傳值的方法，回傳型別寫 `Unit`，實作最後寫 `return`（後面不接東西）。

### 3.2 陣列語法

| 操作 | 寫法 | 注意 |
|---|---|---|
| 建立 | `Array.replicate 10 0` | 長度 10、初值 0 |
| 長度 | `a.size` | |
| 讀取 | `a[i]!` | **驚嘆號不能省** |
| 寫入 | `a := a.set! i v` | 回傳新陣列，必須重新賦值 |

`a[i]!` 的 `!` 表示「越界就用預設值」，不會編譯期擋你。**越界的責任在規格**——這就是為什麼上面要寫 `require i < a.size`。

### 3.3 第三條 `ensures` 在擋什麼

那條 `∀ k, k < a.size ∧ k ≠ i → a[k]! = aOld[k]!` 看起來像廢話：「其他格子沒變」。試試拿掉它：

```lean
method IncrementAtBad (mut a: Array Int) (i: Nat) return (u: Unit)
    require i < a.size
    ensures a.size = aOld.size
    ensures a[i]! = aOld[i]! + 1
    do
    let v := a[i]! + 1
    a := Array.replicate a.size 0    -- 把整個陣列清空
    a := a.set! i v                   -- 只有第 i 格填回去
    return

prove_correct IncrementAtBad by
  loom_solve                          -- 通過
```

長度沒變、第 i 格正確——兩條 `ensures` 都滿足，但陣列被清光了。

> **這叫 frame problem：規格不只要說「什麼變了」，還要說「什麼沒變」。**
> 這是 §1.4「規格太弱」在狀態變更情境下的版本，而且更難察覺——因為漏掉的那條規格描述的是「什麼都沒發生」，寫規格時很容易覺得不必說。

### 3.4 為什麼要 `attribute [grind] Array.size_set`

`Array.set!` 不改變長度，這對人來說顯然，但 solver 需要被告知。陣列題目常見的 hint 還有：

```lean
attribute [grind] Array.size_replicate Array.size_set
```

### 練習

1. 寫 `Swap (mut x: Int) (mut y: Int) return (u: Unit)`。規格只要兩條，而且完全不會提到你用的暫存變數——想清楚為什麼。
2. 承上，拿掉其中一條 `ensures`，寫出一個能通過的錯誤實作。

---

## 4. DoubleAll — 迴圈與不變式

### 4.1 完整例子

```lean
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

attribute [grind] Array.size_set

prove_correct DoubleAll by
  loom_solve
```

### 4.2 迴圈語法

Velvet **只有 `while`**，沒有 `for`。計數器要自己宣告、自己遞增。

```lean
while <條件>
    invariant <每次迭代開始時都成立的性質>
    done_with <離開迴圈時成立的性質>
do
    <迴圈本體>
```

- **`invariant`** 是不變式。**必填**——沒有不變式，驗證無從進行。
- **`done_with`** 描述離開迴圈時你知道什麼。可省略，預設是迴圈條件的否定。這題明寫成 `i = arr.size`，比預設的 `¬(i < arr.size)` 更好用。

### 4.3 陣列迴圈的四條不變式

上面那四條是**通用模式**，之後每個陣列演算法都會用到：

| 不變式 | 作用 |
|---|---|
| `arr.size = arrOld.size` | 長度沒被動過 |
| `i ≤ arr.size` | 索引在範圍內（注意是 `≤`，因為結束時 `i` 剛好等於長度） |
| `∀ k, k < i → ...` | **已處理的前綴**滿足目標性質 |
| `∀ k, i ≤ k ∧ k < arr.size → ...` | **未處理的後綴**維持原狀 |

第四條是最常被漏掉的。少了它，迴圈結束時你只知道前綴被加倍了，卻無法排除「後綴在過程中被亂改」——後條件推不出來。

> 直覺上：不變式要**同時**描述「做完的部分變成什麼」和「還沒做的部分還是什麼」，兩邊合起來才涵蓋整個陣列。

### 4.4 回頭看 `partial` 是什麼意思

檔頭那行 `set_option loom.semantics.termination "partial"`，現在有東西可以對照了。

**`partial` 的意思是「部分正確性」——如果方法停下來，結果滿足後條件。** 它**不保證**方法會停下來。

也就是說，把迴圈條件寫成 `while true`，`prove_correct` 仍然可能通過——因為前提「如果停下來」永遠不成立。

要連終止性一起證，得切到 `"total"`，那是 §6 的主題。

### 4.5 迴圈內不能 early return

從 C 或 Dafny 過來的人一定會踩：

```lean
-- ✗ 不支援：迴圈內 return
while i < arr.size
    invariant ...
do
    if arr[i]! = 10 then
        return true          -- 這會壞掉
    i := i + 1
```

要提早離開迴圈用 **`break`**；要跳過本次迭代用 **`continue`**：

```lean
method SumEven (arr: Array Nat) return (res: Nat)
  ensures res = Array.sum (Array.filter (fun x => x % 2 = 0) arr)
  do
    let mut i := 0
    let mut s := 0
    while (i < arr.size)
      invariant i ≤ arr.size
      invariant s = Array.sum (Array.filter (fun x => x % 2 = 0) (Array.extract arr 0 i))
    do
      if (arr[i]! % 2 != 0) then
        i := i + 1
        continue
      s := s + arr[i]!
      i := i + 1
    return s
```

用 `break` 時要注意：**`done_with` 必須涵蓋 break 的離開條件**，否則證明會斷在那裡。

迴圈**外面**的 early return 是可以的：

```lean
do
  if arr.size ≤ 1 then
    return          -- 這樣沒問題
  else
    ...
```

### 4.6 先測再證

證明之前，先用隨機測試把明顯的 bug 篩掉。Velvet 內建 property-based testing：

```lean
import CaseStudies.TestingUtil

extract_program_for DoubleAll
prove_precondition_decidable_for DoubleAll
prove_postcondition_decidable_for DoubleAll
derive_tester_for DoubleAll

run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arr ← Plausible.SampleableExt.interpSample (Array Int)
    let res := DoubleAllTester arr
    pure (arr, res)
  for _ in [1: 500] do
    let res ← Plausible.Gen.run g 10
    unless res.2 do
      IO.println s!"postcondition violated for input {res.1}"
      break
```

四個指令的分工：

- `extract_program_for` — 抽出可執行版本
- `prove_precondition_decidable_for` / `prove_postcondition_decidable_for` — 讓前後條件可以在執行時判斷真假。多數情況自動完成；失敗時會留下 goal 讓你手動證。
- `derive_tester_for` — 生出 tester 函式

### 4.7 植入一個 bug

把迴圈條件改成 `i < arr.size - 1`（最後一格漏掉）：

```lean
    while i < arr.size - 1
```

跑 PBT，立刻得到：

```
postcondition violated for input #[3, -7, 12]
```

**具體的反例。** 對照組是直接跑 `loom_solve`：你會得到一個沒證出來的 goal，但不知道是實作錯了、還是不變式寫得不夠強。PBT 兩秒鐘就告訴你「這個輸入會爆」。

> **這是 Velvet 多模態的核心價值。** 測試、SMT 自動化、互動式證明三種模式在同一個框架裡，可以按成本從低到高依序用——不必在證明卡住時才發現實作本來就是錯的。
>
> 順序很重要：**先把不變式寫對、跑通，再植入 bug 觀察 PBT 抓它**。反過來做會讓人誤以為 PBT 是「不變式寫不出來時的替代品」——它不是。PBT 只能**反駁**，不能證明；通過測試的不變式仍然可能不是 inductive。

### 練習

1. 把第四條不變式（後綴維持原狀）拿掉，觀察 `loom_solve` 在哪裡斷掉。
2. 寫 `SumArray (a: Array Int) return (s: Int)`。不變式該怎麼寫？（提示：§5 有答案的模式。）

---

## 5. SumOfDigits — method 組合與互動式證明

### 5.1 規格可以慢

計算一個數的各位數字和。規格用遞迴 `def` 表達：

```lean
def SumDigits (n: Nat): Nat :=
  if n = 0 then 0
  else (n % 10) + SumDigits (n / 10)
```

> 如果 Lean 抱怨終止性，加上 `decreasing_by omega` 或提供 `Nat.div_lt_self`。

這個 `def` 是規格的一部分，不是實作。它慢、它遞迴、它對大數會爆堆疊——**都無所謂**。

> **規格不必高效，甚至不必實際可執行。** 規格的任務是**說清楚什麼是對的**，效率是實作的事。這一點在 Velvet 裡特別自然，因為規格就是普通的 Lean 命題，能用上整個 Mathlib。

配套的引理：

```lean
lemma SumDigits_unfold (n : Nat) (h : n > 0) :
  SumDigits n = (n % 10) + SumDigits (n / 10) := by
  rw [SumDigits]
  have h' : n ≠ 0 := Nat.ne_of_gt h
  simp [h']

lemma SumDigits_zero : SumDigits 0 = 0 := by
  unfold SumDigits
  simp

attribute [grind] Nat.mod_add_div SumDigits_unfold SumDigits_zero
```

### 5.2 把子步驟抽成 method

取出個位數、去掉個位數——這是一個獨立的動作，值得自己成為一個 method：

```lean
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
```

第三條 `ensures result.2 < n` 現在用不到，但它是這個 method 的「有用性保證」——呼叫者靠它知道遞減。

### 5.3 method 呼叫 method

```lean
method SumOfDigits (number: Nat) return (sum: Nat)
    ensures sum = SumDigits number
    do
    let mut sum := 0
    let mut n := number
    while n > 0
        invariant sum + SumDigits n = SumDigits number
        done_with n = 0
    do
        let step ← PopDigit n
        sum := sum + step.1
        n := step.2
    return sum
```

**`let step ← PopDigit n`** ——注意是左箭頭 `←`，不是 `:=`。

原因是 Velvet method 本質上是 `VelvetM` 這個 monad 裡的計算，不是普通函式。呼叫要用 monadic 語法。

> **關鍵觀念：呼叫端必須證明被呼叫方的前條件。**
>
> `PopDigit` 寫了 `require n > 0`。在 `SumOfDigits` 的迴圈本體裡，這個條件由迴圈條件 `n > 0` 保證，所以 `loom_solve` 能自動接上。
>
> 但如果你把 `PopDigit n` 搬到迴圈外面，驗證就會失敗——因為那裡沒人保證 `n > 0`。**前條件是呼叫端的義務**，這正是 method 之間的介面契約。

抽成 method 的好處：`PopDigit` 的正確性只證一次，`SumOfDigits` 的證明裡只需要用到它的 `ensures`，不必再展開它的實作。這就是**組合式推理**。

### 5.4 那條不變式

```lean
invariant sum + SumDigits n = SumDigits number
```

念出來是：**已累積的 + 還沒處理的 = 總量**。

這是累積型迴圈的通用模式，值得記下來：

- 迴圈開始時：`sum = 0`、`n = number`，等式成立
- 每次迭代：`sum` 增加 `n % 10`，`n` 變成 `n / 10`，靠 `SumDigits_unfold` 保持等式
- 迴圈結束時：`n = 0`，於是 `SumDigits n = 0`，等式化為 `sum = SumDigits number`——正好是後條件

比起 §4 的「前綴／後綴」模式，這個模式適合處理**沒有索引**的迴圈。

### 5.5 `loom_solve` 擋住了怎麼辦

這題 `loom_solve` 未必一次過。第一步是換成 `loom_solve!` 定位：

```lean
prove_correct SumOfDigits by
  loom_solve!        -- 標示出哪一條 ensures / invariant 沒證出來
```

`loom_solve!` 和 `loom_solve` 做一樣的事，但會**highlight 失敗的位置**。除錯用它，最終版本用 `loom_solve`。

看不出問題時，用更粗暴的方式檢查原始 goal：

```lean
prove_correct SumOfDigits by
  loom_goals_intro   -- 展開未經處理的 goal
  sorry              -- 暫時跳過，先看清楚剩下什麼
```

### 5.6 接手剩下的 goal

Velvet 嵌在 Lean 裡，所以自動化擋住時你不會卡死——直接往下寫 Lean tactic：

```lean
prove_correct SumOfDigits by
  loom_solve
  -- 自動化沒解掉的部分，手動處理
  { omega }
  { simp_all
    grind }
```

**用 `{ }` 包住每個子目標。** 這不只是排版習慣，Velvet 靠它支援 incremental 模式——改動某個子目標的證明時，不會重跑整個 `loom_solve`。

如果證明複雜到互動式編輯很卡，還有一招：

```lean
prove_correct? SumOfDigits by
  loom_solve
```

`prove_correct?` 會把 Velvet 內部產生的定理**印出來**，你可以複製成一般的 Lean `theorem` 自己證。一般 theorem 的 incrementality 比 `prove_correct` 好，編輯時不會重跑自動化。

### 5.7 三個旋鈕，對應三種症狀

卡住時先看**錯誤訊息長什麼樣**，再決定轉哪一個：

| 症狀 | 旋鈕 | 說明 |
|---|---|---|
| grind 說 split 用完了 | `set_option loom.solver.grind.splits 40` | 預設 20，巢狀條件多時調 40–100 |
| SMT 回 unknown | `set_option loom.solver.smt.timeout 4` | 預設只有 1 秒 |
| Lean 說 maximum heartbeats exceeded | `set_option maxHeartbeats 1000000` | 預設 200000，複雜證明 1M–2M |

`maxHeartbeats` 可以只套用在單一證明上：

```lean
set_option maxHeartbeats 2000000 in
prove_correct VeryComplexMethod by
  loom_solve
```

> **調旋鈕之前先想清楚。** 這三個都是「給更多資源」，不是「換更好的方法」。如果是 solver 缺知識（像 §2.3 的 `Nat.mod_lt`），調多久都不會過——該補的是 hint。

### 練習

1. 把 `PopDigit` 的 `require n > 0` 拿掉，改成在 `ensures` 裡處理 `n = 0` 的情況。哪一種寫法讓 `SumOfDigits` 的證明比較容易？
2. 把 `PopDigit n` 的呼叫搬到迴圈外面，觀察錯誤訊息，確認前條件確實是呼叫端的義務。

---

## 6. CountDown — 終止性

### 6.1 換一個 semantics

前面五節全都在 `partial` 模式下——所有「證明通過」的意思都是**「如果它停下來」**。

要連停下來一起證，改檔頭：

```lean
set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"
```

### 6.2 `decreasing`

在 `total` 模式下，每個迴圈都要加 **`decreasing`** 子句，提供一個**終止測度**：

```lean
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
```

`decreasing i` 宣告「每次迭代 `i` 都會嚴格變小」。因為 `i : Nat` 有下界 0，不可能無限下降，迴圈必然終止。Velvet 會生一個 goal 要求你證明 `i` 確實遞減。

**測度不一定是迴圈變數本身。** 遞增迴圈的測度通常是「還剩多少」：

```lean
    while i < arr.size
      invariant i ≤ arr.size
      decreasing arr.size - i
```

### 6.3 什麼時候要用 `total`

| | `partial` | `total` |
|---|---|---|
| 證明的內容 | 若終止則正確 | 終止且正確 |
| 成本 | 低 | 每個迴圈多一個 goal |
| 適用 | 開發階段、終止性顯然 | 最終交付、終止性非平凡 |

實務建議：**先用 `partial` 把功能正確性弄對，最後再切 `total`**。同時處理兩件事容易搞不清楚失敗來自哪一邊。

Velvet 也支援把兩者**分開證再組合**——用不同 method 的 `triple` 組起來。這屬於進階主題，見官方 `VelvetExample/Total_Partial_example.lean`。

### 練習

1. 把 §4 的 `DoubleAll` 切到 `total` 模式，補上 `decreasing`。
2. 故意寫一個 `decreasing` 錯誤的迴圈（例如測度不變），觀察錯誤訊息。

---

## 附錄 A：語法速查

### 檔頭

```lean
import Velvet.Std
import CaseStudies.TestingUtil          -- 需要 PBT 時

set_option loom.semantics.termination "partial"   -- 或 "total"
set_option loom.semantics.choice "demonic"        -- 或 "angelic"
set_option loom.solver "grind"                     -- 或 "cvc5" / "z3"
```

### 方法

```lean
method Name (a: Int) (mut b: Array Int) return (r: Nat)
    require <前條件>
    ensures <後條件>            -- 可多條，之間是 AND
    do
    <實作>
    return <值>

prove_correct Name by
  loom_solve
```

### 迴圈

```lean
while <條件>
    invariant <不變式>          -- 必填，可多條
    done_with <離開時成立>       -- 可省略
    decreasing <測度>            -- total 模式必填
do
    <本體>
```

### 常見對照（Dafny → Velvet）

| Dafny | Velvet |
|---|---|
| `{ ... }` | `do` 區塊 |
| `var x := 0;` | `let mut x := 0` |
| `old(a)` | `aOld` |
| `for` | 只有 `while` |
| `a[i]` | `a[i]!` |
| `a[i] := v;` | `a := a.set! i v` |
| `new int[n]` | `Array.replicate n 0` |
| `<==>` / `&&` / `||` | `↔` / `∧` / `∨` |
| `forall` / `exists` | `∀` / `∃` |
| `else if` | 巢狀 `if` |

---

## 附錄 B：排錯對照表

| 症狀 | 先試什麼 |
|---|---|
| `loom_solve` 失敗、不知道哪裡 | `loom_solve!` |
| 想看原始 goal | `loom_goals_intro` + `sorry` |
| solver 缺數學知識 | `attribute [grind] <引理>` |
| 算術很重 | `set_option loom.solver "cvc5"` |
| grind splits 用完 | `loom.solver.grind.splits 40` |
| SMT 回 unknown | `loom.solver.smt.timeout 4` |
| heartbeats exceeded | `maxHeartbeats 1000000` |
| 陣列長度性質證不出來 | `attribute [grind] Array.size_set Array.size_replicate` |
| 互動編輯很卡 | `prove_correct?` 轉成一般 theorem |
| 不確定實作對不對 | 先跑 PBT，不要硬證 |

---

## 附錄 C：本教材沒涵蓋的

主線刻意省略，需要時再查文件：

- **遞迴 method** 與 `termination_by` / `decreasing_by`（§6 只講了迴圈的 `decreasing`）
- **`match` 模式比對**，包含多參數匹配
- **非確定性 `:|`**，以及 `angelic` / `demonic` 的差別
- **自訂 `structure`** 當作資料型別
- **`triple` 組合推理**：把終止性與功能正確性分開證再合併
- **custom solver**：用 `macro_rules` 自訂 `loom_solver`

### 補充練習（對應各節）

| 節 | 練習題 |
|---|---|
| 1 | `Abs`、`Maximum3` |
| 2 | `DivMod` |
| 3 | `Swap` |
| 4 | `SumArray`、`FindMax` |
| 5 | `Factorial`（遞迴 method 版）、`GCD` |
| 6 | `BinarySearch`（`decreasing` 是什麼？） |

進階題：`BubbleSort`。它需要兩條 `ensures`——排序好，**以及** multiset 保存。少了第二條，回傳全零陣列也算「排序好的」。這是 §1.4 的教訓在最複雜情境下的版本。