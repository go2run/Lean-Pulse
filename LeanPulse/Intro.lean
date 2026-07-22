/-
  LeanPulse.Intro — 對應 `src/tutorial/PulseTutorial.Intro.fst`

  Pulse 這一課的主題：incr、ghost 參數、frame rule、平行組合（par）。

  Frame rule 的翻譯是本檔重點：
  - Pulse: `fn incr_frame (x y:ref int) requires pts_to x 'i preserves pts_to y 'j`
    ——沒被動到的資源（y）自動穿越呼叫、保持不變。
  - Velvet: 沒宣告成 `mut` 的東西*根本不可能*被改。frame rule 不是
    一條推理規則，而是值語意的免費贈品。這是「淺嵌入到純函數式宿主」
    給的紅利；代價是失去 Pulse 能表達的並行（par_incr 無法翻譯，
    Velvet 目前沒有並行——這正是分離邏輯不可取代的地盤）。
-/
import Velvet.Std

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Pulse: let incr_functional (x:int) = x + 1
   純函數規格層：兩邊一樣，都是宿主語言的普通定義。 -/
def incrFunctional (x : Int) : Int := x + 1

/- Pulse:
     fn incr (x:ref int) requires pts_to x 'i ensures pts_to x ('i + 1) -/
method incr (mut x : Int) return (u : Unit)
    ensures x = xOld + 1
    do
    x := x + 1
    return

prove_correct incr by
  loom_solve

/- Pulse 的 incr_explicit_i 把 ghost 值 'i 改成顯式參數 (i:erased int)。
   Velvet 對應：把「初值」當一般參數傳入，並用 require 綁定。
   erased（不出現在執行碼中）的性質由 Lean 編譯器的擦除保證。 -/
method incrExplicit (mut x : Int) (i : Int) return (u : Unit)
    require x = i
    ensures x = i + 1
    do
    x := x + 1
    return

prove_correct incrExplicit by
  loom_solve

/- Pulse:
     fn incr_frame (x y:ref int)
       requires pts_to x 'i  preserves pts_to y 'j
       ensures pts_to x ('i + 1)
   y 以非 mut 傳入：呼叫後 y 不變是型別系統的事實，
   連 ensures 都不用寫——這就是內建的 frame rule。 -/
method incrFrame (mut x : Int) (y : Int) return (u : Unit)
    ensures x = xOld + 1
    do
    x := x + 1
    return

prove_correct incrFrame by
  loom_solve

/- Pulse 的 par_incr（平行遞增兩個 ref）在 Velvet 沒有對應物：
   Velvet 的效果單子目前只有循序狀態與非決定性，沒有並行組合。
   循序版本如下；並行版請留在 Pulse/Iris 的世界。 -/
method seqIncrBoth (mut x : Int) (mut y : Int) return (u : Unit)
    ensures x = xOld + 1
    ensures y = yOld + 1
    do
    x := x + 1
    y := y + 1
    return

prove_correct seqIncrBoth by
  loom_solve
