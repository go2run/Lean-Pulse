/-
  LeanPulse.Conditionals — 對應 `src/tutorial/PulseTutorial.Conditionals.fst`

  Pulse 這一課表面在講 `if` 和 `match`，真正的主題是
  **多條控制流路徑匯合時，狀態該用什麼斷言描述**。

  它分兩段，各自對應到 Velvet 的一個重要落差：

  ┌ 第一段：if 的匯合點 ────────────────────────────────────────┐
  │ Pulse 的 max_alt 會失敗，必須由人手寫 `if ... ensures`。     │
  │ Velvet 不需要——VC 產生器把後置條件推進兩個分支，SMT/grind   │
  │ 自己做 case split。這是 auto-active 驗證器相對於分離邏輯     │
  │ 檢查器的主要人體工學優勢。                                   │
  │ 但注意：這個「自動」有邊界，見本檔最後的討論。               │
  └──────────────────────────────────────────────────────────────┘

  ┌ 第二段：值決定資源形狀（nullable pointer）─────────────────┐
  │ Pulse 的 pts_to_or_null 是一個述詞，None 分支「不擁有資源」、│
  │ Some 分支「擁有一格」——同一個斷言描述兩種資源形狀。         │
  │ Velvet 沒有資源概念，所以它退化成一個普通的**命題**：        │
  │ 「若 r 是 some x，則 x 是合法且已配置的索引」。              │
  │ 隨之而來的 fold/unfold 樣板（Pulse 最惱人的機械勞動）        │
  │ 在這裡完全消失——因為沒有東西需要被「打開」。                │
  └──────────────────────────────────────────────────────────────┘
-/
import Velvet.Std

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- ═══════════════════════════════════════════════════════════════
   第一段：if 的匯合點
   ═══════════════════════════════════════════════════════════════ -/

/- Pulse: let max_spec x y = if x < y then y else x
   規格層的純函數：兩邊完全一樣。「用純函數當規格、用指令式程式碼
   實作、再證明兩者相符」是 PoP 的標準結構。 -/
def maxSpec (x y : Int) : Int := if x < y then y else x

/- Pulse:
     fn max #p #q (x y:ref int)
     preserves pts_to x #p 'vx        -- 分數權限：唯讀
     requires pts_to y #q 'vy
     returns n:int
     ensures pts_to y #q 'vy ** pure (n == max_spec 'vx 'vy)
     { let vx = !x; let vy = !y; if (vx > vy) { vx } else { vy } }

   兩個分數權限的 ref ↦ 兩個非 mut 參數（見 Ref.lean 的權限對照表）。
   ensures 裡重述 `pts_to y #q 'vy`（把讀完的資源還回去）在 Velvet
   是免費的：y 不是 mut，呼叫者的值不可能被動到。 -/
method maxOf (x : Int) (y : Int) return (n : Int)
    ensures n = maxSpec x y
    do
    if x > y then
        return x
    else
        return y

prove_correct maxOf by
  loom_solve

/- Pulse 的 max_alt（**這個版本在 Pulse 會失敗**）：
     { let mut result = 0;
       if (vx > vy) { result := vx; } else { result := vy; };
       !result; }

   為什麼失敗？在 `if` 的匯合點，Pulse 需要一個涵蓋兩條路徑的斷言
   來描述 result 現在裝什麼。它推得出各分支的具體事實
   （pts_to result vx / pts_to result vy），但無法自己「發明」
   把兩者統一起來的抽象：
       exists* r. pts_to result r ** pure (r == max_spec 'vx 'vy)

   Pulse 的解法（max_alt2）是人把這個斷言寫在 `if` 上當 ensures。

   Velvet 這裡不需要任何標註——同樣一段程式碼直接過。原因是
   Velvet 走 auto-active 路線：後置條件 `n = maxSpec x y` 被
   反向推進兩個分支，變成兩個純命題的證明義務
     (x > y  → x = maxSpec x y)
     (¬x > y → y = maxSpec x y)
   交給 SMT/grind，case split 是它們的看家本領。 -/
method maxAlt (x : Int) (y : Int) return (n : Int)
    ensures n = maxSpec x y
    do
    let mut result := 0
    if x > y then
        result := x
    else
        result := y
    return result

prove_correct maxAlt by
  loom_solve

/- ═══════════════════════════════════════════════════════════════
   第二段：可為空的指標
   ═══════════════════════════════════════════════════════════════ -/

/- 沿用 Box.lean 的堆積模型：store 是整個堆積，位址就是索引，
   `some v` 表示已配置且裝著 v，`none` 表示未配置／已釋放。 -/
@[reducible]
def Store := Array (Option Int)

/- Pulse: let nullable_ref (a:Type0) = option (ref a)
   可為空的指標＝「可能沒有的位址」。 -/
@[reducible]
def NullableRef := Option Nat

/- Pulse:
     let pts_to_or_null x #p v : slprop =
       match x with
       | None   -> pure (v == None)                       -- 不擁有任何資源
       | Some x -> exists* w. pts_to x #p w ** pure (v == Some w)  -- 擁有一格

   這是整個檔案最重要的觀念：**一個述詞可以讓「擁有多少資源」
   取決於值**。C 的 nullable pointer、tagged union、狀態機
   （某些狀態持有 buffer、某些不持有）全靠這一招建模。

   Velvet 版本退化成純命題——因為值語意下沒有「擁有」這件事，
   只剩下「這個索引合法嗎、這格配置了嗎」。
   代價與收穫都在這裡：
   - 收穫：不需要 fold/unfold，寫起來乾淨。
   - 代價：它不再保證「別人動不到這格」，那份保證要靠
     手寫的 frame 條款（見下面 writeNullable 的最後一條 ensures）。 -/
@[reducible]
def ptsToOrNull (store : Store) (r : NullableRef) (v : Option Int) : Prop :=
  match r with
  | none   => v = none
  | some x => x < store.size ∧ store[x]! = v ∧ v ≠ none

/- Pulse:
     fn read_nullable (r:nullable_ref a)
     requires pts_to_or_null r #p 'v
     returns o:option a
     ensures pts_to_or_null r #p 'v ** pure ('v == o)

   Pulse 的實作要走一整套樣板：
       unfold (pts_to_or_null (Some x) #p 'v);   -- 拆包裹拿到 pts_to
       let o = !x;
       fold (pts_to_or_null (Some x) #p 'v);     -- 包回去
       rewrite each (Some x) as r;               -- 把 Some x 換回 r
   四行裡只有第二行在做事，其餘三行是為了讓資源帳目對得起來。
   這正是 Nik 文章中「該外包給 agent 的機械性工作」的典型樣本。

   Velvet 版本：讀就是讀。ghost 值 'v 依 Ref.lean 的慣例作為
   顯式參數傳入（對應 Pulse 的 value_of_explicit 寫法）。
   `ensures ptsToOrNull store r v` 不必寫——store 非 mut，不變是免費的。 -/
method readNullable (store : Store) (r : NullableRef) (v : Option Int) return (o : Option Int)
    require ptsToOrNull store r v
    ensures o = v
    do
    match r with
    | some x => return store[x]!
    | none   => return none

prove_correct readNullable by
  loom_solve

/- Pulse 有一個 [@@expect_failure] 的陷阱範例：
     match r { Some x -> {...}  _ -> { assert (pure (r == None)); ... } }
   在 Pulse 裡走到萬用 pattern `_` **拿不到前面分支的否定資訊**，
   所以斷言 r == None 會失敗；必須寫顯式的 `None ->`。

   Lean/Velvet 沒有這個坑：`match` 是相依模式匹配，在 `none` 分支
   Lean 本來就知道 r = none，grind 也用得上這個事實。
   這是工具實作差異，不是理論差異——但 debug 時撞到會很困惑，
   值得記在腦裡。 -/

/- Pulse:
     fn write_nullable (r:nullable_ref a) (v:a)
     requires pts_to_or_null r 'v
     ensures exists* w. pts_to_or_null r w ** pure (Some? r ==> w == Some v)

   注意 Pulse 規格的講究之處：後置條件用 `exists* w` 說「現在裝著某個 w」，
   再用蘊含 `Some? r ==> w == Some v` 分情況說明——
   **r 是 null 時什麼都沒發生，這也是規格的一部分**。
   一個只寫「寫入後就是 v」的規格會是錯的（null 時根本沒寫）。

   Velvet 版本把同一件事拆成三條 ensures：寫成功的情況、null 的情況、
   以及 Pulse 免費贈送、這裡必須手寫的 frame 條款。 -/
method writeNullable (mut store : Store) (r : NullableRef) (v : Option Int) (x : Int)
    return (u : Unit)
    require ptsToOrNull store r v
    ensures store.size = storeOld.size
    -- 情況一：r 指向某格，該格變成 x
    ensures ∀ i, r = some i → store[i]! = some x
    -- 情況二：r 是 null，整個堆積原封不動
    ensures r = none → store = storeOld
    -- 手寫的 frame：其他格子一律不變（Pulse 由 ** 免費保證）
    ensures ∀ k, k < store.size → (∀ i, r = some i → k ≠ i) → store[k]! = storeOld[k]!
    do
    match r with
    | some i =>
      store := store.set! i (some x)
      return
    | none =>
      return

attribute [grind] Array.size_set Array.getElem!_set

prove_correct writeNullable by
  loom_solve

/- ═══════════════════════════════════════════════════════════════
   收尾：自動化的邊界在哪裡？
   ═══════════════════════════════════════════════════════════════

   本檔第一段給人的印象可能是「Velvet 全自動、Pulse 要手寫標註」。
   這個印象只對了一半，界線是這樣畫的：

   ● 分支的匯合點：路徑數量有限（兩條），把後置條件推進去、
     case split、各自求解——**自動化真的能包辦**。

   ● 迴圈的匯合點：路徑數量無限（迴圈可繞任意多次），必須有一個
     對所有次數都成立的斷言。這個斷言不能靠列舉得到，只能靠
     **歸納法的洞察**——所以 Dafny、Verus、Velvet、Pulse、Iris
     無一例外都要人寫 `invariant`。

   換句話說：分支的 ensures 是「可以自動化的匯合」，
   迴圈的 invariant 是「不可自動化的匯合」。
   下一課（Loops）就是在練那個不可自動化的部分——
   也正是你在 agentic 工作流裡真正要保留的能力。

   還有一個界線值得注意：Velvet 的自動化幫你省掉的是 fold/unfold
   與匯合標註這類**機械勞動**，但 writeNullable 那條手寫 frame
   顯示，它並沒有省掉**規格設計**。分離邏輯用 `**` 把「其他東西
   沒被動到」變成免費的；值語意的模型裡，這件事得你自己想清楚
   並寫下來——而且很容易漏寫或寫錯。這是規格審查的重點區。 -/
