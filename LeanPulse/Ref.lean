/-
  LeanPulse.Ref — 對應 `src/tutorial/PulseTutorial.Ref.fst`

  Pulse 這一課教：ref 的讀寫、ghost 初值 'v、permission（分數權限、
  share/gather）、區域可變變數 let mut、以及幾個刻意失敗的例子。

  權限模型的翻譯總表：
  │ Pulse                          │ Velvet                          │
  │ pts_to r #1.0R v（全權限）      │ (mut r : τ)——可讀可寫、獨佔     │
  │ pts_to r #p v（分數權限、唯讀） │ (r : τ)——只能讀                 │
  │ share r（1 分裂成 ½+½）        │ 把值同時給兩個唯讀使用者（自由） │
  │ gather r（½+½ 收回 1）         │ 唯讀借用結束後 mut 恢復（自動）  │
  │ 對唯讀權限寫入 → 驗證錯誤       │ 對非 mut 參數賦值 → 編譯錯誤    │
  這正是 Rust 借用檢查器的關係：&mut = mut、& = 非 mut。
  Pulse 把權限做成「可運算的證明資產」（可存進資料結構、跨執行緒分割），
  Velvet/Rust 把它烤進參數模式——表達力較低，但零證明負擔。
-/
import Velvet.Std

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Pulse: fn incr (r:ref int) requires pts_to r 'v ensures pts_to r ('v+1) -/
method incrRef (mut r : Int) return (u : Unit)
    ensures r = rOld + 1
    do
    let v := r
    r := v + 1
    return

prove_correct incrRef by
  loom_solve

/- Pulse: fn swap (r0 r1:ref a) — 多型版的交換。
   Velvet 方法可以帶型別參數（Lean 的普通多型）。 -/
method swapRef (mut r0 : Int) (mut r1 : Int) return (u : Unit)
    ensures r0 = r1Old
    ensures r1 = r0Old
    do
    let v0 := r0
    let v1 := r1
    r0 := v1
    r1 := v0
    return

prove_correct swapRef by
  loom_solve

/- Pulse:
     fn value_of (r:ref a) preserves pts_to r 'v
       returns v:a ensures pure (v == 'v)
   preserves（讀完原樣奉還）↦ 非 mut 參數 + 回傳它的值。 -/
method valueOf (r : Int) return (v : Int)
    ensures v = r
    do
    return r

prove_correct valueOf by
  loom_solve

/- Pulse 的 value_of_explicit_fail 刻意示範：直接 `reveal w` 回傳 ghost 值
   而不去讀 r，會被拒絕（228）——ghost 的東西不能變出執行期的值。
   Velvet 對應：規格中的量（rOld、require 裡的變數）不在 do 區塊的
   作用域內，想「直接回傳規格值」根本寫不出來——同一道防線，
   Pulse 靠 effect 檢查，Velvet 靠作用域。 -/

/- Pulse: fn assign (r:ref a) (v:a) requires pts_to r 'v ensures pts_to r v -/
method assign (mut r : Int) (v : Int) return (u : Unit)
    ensures r = v
    do
    r := v
    return

prove_correct assign by
  loom_solve

/- Pulse: fn add (r:ref int) (n:int) requires pts_to r 'v ensures pts_to r ('v+n) -/
method add (mut r : Int) (n : Int) return (u : Unit)
    ensures r = rOld + n
    do
    let v := r
    r := v + n
    return

prove_correct add by
  loom_solve

/- Pulse:
     fn quadruple (r:ref int) requires pts_to r 'v ensures pts_to r (4 * 'v)
     { let v1 = !r; add r v1; let v2 = !r; add r v2; }
   Pulse 教材在這裡展示 proof state 如何隨呼叫演化
   （pts_to r v1 → pts_to r (v1+v1) → ...）。
   Velvet 中同樣的推理由驗證條件自動完成。

   Pulse 還附了一個 quad_fail：`add r (!r)` 在參數位置讀 ref 會失敗，
   因為分離邏輯要檢查求值順序與資源交錯。Velvet 沒有這個陷阱——
   表達式裡的 r 是值，`r + r` 永遠合法。陷阱本身是「指標語言的成本」。 -/
method quadruple (mut r : Int) return (u : Unit)
    ensures r = 4 * rOld
    do
    let v1 := r
    r := r + v1     -- 對應 add r v1
    let v2 := r
    r := r + v2     -- 對應 add r v2
    return

prove_correct quadruple by
  loom_solve

/- Pulse 權限範例的翻譯示範：
     fn value_of_perm #p (r:ref a) preserves pts_to r #p 'v — 分數權限唯讀
   ↦ 非 mut 參數（見 valueOf）。
     [@@expect_failure] fn assign_perm #p (r:ref a) — 對分數權限寫入
   ↦ 在 Velvet 中對非 mut 參數寫 `r := v` 直接是編譯錯誤，
     不需要（也無法）寫出這個反例方法。
     share_ref / gather_ref / alias_ref
   ↦ 無對應物：值語意下「別名」不存在，分裂/合併權限沒有意義。
     這是兩個系統真正分道揚鑣的地方——當你需要在資料結構裡
     *儲存*可變引用（linked list、lock），Velvet 式的翻譯就得
     像 Box.lean 那樣顯式建模整個堆積。 -/

/- Pulse:
     fn one () returns v:int ensures pure (v == 1)
     { let mut i = 0; incr i; !i }
   區域可變變數：Pulse 的 let mut 造出棧上 ref；Velvet 的 let mut
   就是可變綁定，兩邊語法幾乎相同。 -/
method one (u : Unit) return (v : Int)
    ensures v = 1
    do
    let mut i := 0
    i := i + 1      -- 對應 incr i
    return i

prove_correct one by
  loom_solve

/- Pulse 的 refs_are_scoped（回傳區域 ref → 拒絕 228）：
   區域 ref 的生命週期不能逃出函式。Velvet 中這件事無法表達——
   `return i` 回傳的是值的拷貝，沒有「引用逃逸」可言。
   同一條安全性，Pulse 用檢查器擋，Velvet 用語意消滅。 -/
