/-
  LeanPulse.Box — 對應 `src/tutorial/PulseTutorial.Box.fst`

  Pulse 的 Box 是「可 free 的堆積配置」：alloc 產生 Box.pts_to r v，
  free 消滅它。分離邏輯的殺手級特性在此登場：free 之後
  `Box.pts_to r v` 這塊資產從 context 消失，任何 use-after-free
  都因為「拿不出資產」而無法通過驗證。

  Velvet 沒有內建堆積，所以我們照 Dafny 傳統*顯式建模*它：
  一個 store（Array (Option Int)）當作堆積整體，位址就是索引，
  `store[r]! = some v` 扮演 pts_to r v，`none` 表示已釋放。

  對照表：
  │ Pulse                        │ 本檔的模型                        │
  │ Box.alloc v : box a          │ alloc：store.push (some v)，回索引 │
  │ Box.pts_to r v               │ store[r]! = some v                │
  │ !r / r := v                  │ 讀寫 store[r]!                    │
  │ Box.free r（資產消失）        │ store := store.set! r none        │
  │ use-after-free 無法驗證       │ require store[r]! ≠ none 擋掉     │
  這個翻譯忠實但笨重——每個方法都得攜帶整個 store，並自己聲明
  「其他位址不變」（分離邏輯的 frame rule 免費給的東西，這裡要
  手寫 ∀ k ≠ r → 不變）。體會這份笨重，就是本課的教學重點：
  它正是分離邏輯被發明出來的理由。
-/
import Velvet.Std

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

@[reducible]
def Store := Array (Option Int)

/- Pulse:
     fn new_heap_ref (v:a) returns r:Box.box a ensures Box.pts_to r v -/
method newHeapRef (mut store : Store) (v : Int) return (r : Nat)
    ensures r = storeOld.size
    ensures store.size = storeOld.size + 1
    ensures store[r]! = some v                                   -- Box.pts_to r v
    ensures ∀ k, k < storeOld.size → store[k]! = storeOld[k]!    -- 手寫 frame
    do
    let r := store.size
    store := store.push (some v)
    return r

attribute [grind] Array.size_push Array.getElem_push Array.size_set Array.getElem_set

prove_correct newHeapRef by
  loom_solve

/- Pulse:
     fn last_value_of (r:Box.box a) requires Box.pts_to r 'v
       returns v:a ensures pure (v == 'v)
     { let v = !r; free r; v }
   注意 Pulse 的 ensures *沒有* Box.pts_to——資產被 free 吃掉了。
   模型版：ensures store[r]! = none 明說這塊已死。 -/
method lastValueOf (mut store : Store) (r : Nat) return (v : Int)
    require r < store.size
    require store[r]! ≠ none                       -- 持有 Box.pts_to r 'v
    ensures ∀ w, storeOld[r]! = some w → v = w     -- v == 'v（require 保證這樣的 w 存在）
    ensures store.size = storeOld.size
    ensures store[r]! = none                       -- free 之後資產消失
    ensures ∀ k, k < store.size ∧ k ≠ r → store[k]! = storeOld[k]!
    do
    let v := (store[r]!).getD 0
    store := store.set! r none                     -- free r
    return v

prove_correct lastValueOf by
  loom_solve

/- Pulse:
     fn incr_box (r:Box.box int) requires Box.pts_to r 'v
       ensures Box.pts_to r ('v + 1)
   Pulse 版核心是 box ↔ ref 的權限轉換（to_ref_pts_to / to_box_pts_to）；
   模型版中 box 與 ref 都是 store 索引，轉換是恆等，直接讀改寫。 -/
method incrBox (mut store : Store) (r : Nat) return (u : Unit)
    require r < store.size
    require store[r]! ≠ none
    ensures store.size = storeOld.size
    ensures ∀ v, storeOld[r]! = some v → store[r]! = some (v + 1)
    ensures ∀ k, k < store.size ∧ k ≠ r → store[k]! = storeOld[k]!
    do
    let v := (store[r]!).getD 0
    store := store.set! r (some (v + 1))
    return

prove_correct incrBox by
  loom_solve

/- Pulse:
     fn copy_free_box (r:Box.box a) requires Box.pts_to r 'v
       returns r':Box.box a ensures Box.pts_to r' 'v
     { let v = !r; free r; alloc v }
   舊 box 死、新 box 生，值搬家。 -/
method copyFreeBox (mut store : Store) (r : Nat) return (r' : Nat)
    require r < store.size
    require store[r]! ≠ none
    ensures r' = storeOld.size
    ensures store.size = storeOld.size + 1
    ensures store[r']! = storeOld[r]!              -- 新 box 裝著舊值
    ensures store[r]! = none                       -- 舊 box 已 free
    ensures ∀ k, k < storeOld.size ∧ k ≠ r → store[k]! = storeOld[k]!
    do
    let v := store[r]!
    store := store.set! r none                     -- free r
    let r' := store.size
    store := store.push v                          -- alloc v
    return r'

prove_correct copyFreeBox by
  loom_solve

/- Pulse:
     fn copy_box #p (r:Box.box a) preserves Box.pts_to r #p 'v
       returns s:Box.box a ensures Box.pts_to s 'v
   分數權限唯讀 r（preserves）+ 配置新 box。
   模型版：r 完全不動（連 none 都不設），只 push 新格。 -/
method copyBox (mut store : Store) (r : Nat) return (s : Nat)
    require r < store.size
    require store[r]! ≠ none
    ensures s = storeOld.size
    ensures store.size = storeOld.size + 1
    ensures store[s]! = storeOld[r]!
    ensures ∀ k, k < storeOld.size → store[k]! = storeOld[k]!   -- r 原樣保留
    do
    let v := store[r]!
    let s := store.size
    store := store.push v
    return s

prove_correct copyBox by
  loom_solve

/- 收尾思考：本檔每個方法都拖著 store 和一條手寫的 frame 條款。
   在 Pulse 中這些全部免費——`Box.pts_to r v` 只談 r 這一格，
   別的格子連提都不用提。當你之後在 Velvet 裡做 linked list 或
   allocator（見 Velvet 自帶的 MemAlloc 案例），這份成本會急速放大。
   「什麼時候值語意夠用、什麼時候必須上分離邏輯」——能回答這個
   問題，第一階段就畢業了。 -/
