/-
  LeanPulse.RingBuffer — 對應 Pulse 的
  `lib/pulse/lib/Pulse.Lib.RingBuffer.fst`（分支 `_nik_ring_buffer`）

  原檔是一個「環形佇列（FIFO）」的完整驗證：固定大小的 vec 當底層儲存，
  head/tail/count 三個 box 當可變狀態，抽象規格則是一條邏輯序列 s。
  它把 Pulse 的招數幾乎用了一輪：
    * 記錄型別裡*存放*可變資源（vec + 3 個 box）
    * `is_ringbuffer rb s cap` 這個自訂 slprop 把「資源 + 純不變量」打包
    * `exists* buf h tl cnt. ...` 把四個底層值藏進 slprop
    * 每個操作開頭 `unfold`、結尾 `fold`，中間再 `rewrite` 把
      `pts_to buffer buf` 換成 `pts_to rb.buffer buf`
    * `#s:erased (Seq.seq t)`：抽象序列是 ghost，只活在規格裡
    * `is_full_vec` + `Vec.free`/`B.free`：可釋放性也是資源的一部分

  搬到 Velvet（值語意）之後，第 1、3、4、6 條整個消失，第 2 條退化成
  一個純 Prop（`isRingBuffer`），第 5 條變成一個可以*從值算出來*的
  函數（`rbContents`）——不必是 ghost，因為欄位本身就看得見。剩下真正的數學
  內容只有一件事：**環形索引的模運算與抽象序列的關係**，也就是
  Pulse 那幾條 lemma（lemma_push_contents / lemma_tail_invariant_maintained /
  lemma_contents_length）。這些在哪個系統裡都得手寫，本檔照樣寫了。

  對照表：
  │ Pulse                                  │ 本檔                                │
  │ ringbuffer_t = vec t + 3×box SZ.t      │ structure RingBuffer（純值紀錄）     │
  │ Vec.pts_to rb.buffer buf               │ rb.buf : Array Int                  │
  │ B.pts_to rb.head h（+tail、count）     │ rb.head / rb.tail / rb.count : Nat  │
  │ is_ringbuffer rb s cap : slprop        │ isRingBuffer rb : Prop（純不變量）  │
  │ exists* buf h tl cnt. ...              │ 不需要——欄位本身就是那些值          │
  │ #s:erased (Seq.seq t)（ghost 序列）    │ rbContents rb（從值算出來的函數）   │
  │ #cap:erased nat                        │ rb.cap（就在紀錄裡）                │
  │ unfold / fold / rewrite                │ 不需要——@[reducible] + grind        │
  │ Seq.snoc s x / Seq.head / Seq.tail     │ s ++ [x] / s.head! / s.tail         │
  │ 舊狀態 'v（規格裡的 ghost 初值）        │ rbOld（Velvet 的 mut 參數舊值）      │
  │ is_full_vec（為了能 free）             │ 無對應物                            │
  │ Vec.free / B.free                      │ 無對應物（值語意，交給 GC）          │

  兩點刻意的取捨：
  1. 元素型別寫死成 `Int`。Pulse 的 `#t:Type0` 完全多型；Velvet 的
     method 參數語法只收 `(x : τ)` 與 `(mut x : τ)`，收不了
     `[Inhabited α]` 這種 instance binder，而 `a[i]!` 需要它。
     這是語法層的限制，不是驗證能力的限制。
  2. Pulse 的不變量把 tail 分成兩種情況（cnt = 0 時 head = tail；
     cnt > 0 時 tail = (head + cnt) % cap）。因為 head < cap ⇒
     (head + 0) % cap = head，兩條可以合成一條，見 isRingBuffer。
-/
import Velvet.Std

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/-! ## 資料表示

  Pulse:
    noeq type ringbuffer_t (t:Type0) = {
      buffer : vec t; head : box SZ.t; tail : box SZ.t;
      count : box SZ.t; cap : SZ.t }
  三個 box 是「可變的指標」；在 Velvet 裡整個紀錄就是一個值，
  「修改」= 產生一個新紀錄（`{ rb with ... }`）並賦值回 mut 參數。 -/
structure RingBuffer where
  buf   : Array Int   -- 底層儲存（Pulse: vec t，長度固定 = cap）
  head  : Nat         -- 下一個要 pop 的位置
  tail  : Nat         -- 下一個要 push 的位置
  count : Nat         -- 目前元素個數
  cap   : Nat         -- 容量（常數）
deriving Repr, Inhabited, DecidableEq

/-! ## 抽象序列

  Pulse 的 `contents_of_buffer_aux`：從 head 出發、繞著環走 count 步，
  把實體佈局解讀成一條 FIFO 序列。這是整個驗證的「抽象函數」。 -/
def rbContentsFrom (buf : Array Int) (h count cap : Nat) : List Int :=
  match count with
  | 0     => []
  | n + 1 => buf[h]! :: rbContentsFrom buf ((h + 1) % cap) n cap

/-- Pulse: `contents_of_buffer buf (SZ.v h) (SZ.v cnt) cap`。
    在 Pulse 裡這條序列必須是 ghost 參數 `#s`（因為它是 slprop 的一部分，
    而 slprop 談的是資源）；在 Velvet 裡它就是一個普通函數。 -/
def rbContents (rb : RingBuffer) : List Int :=
  rbContentsFrom rb.buf rb.head rb.count rb.cap

@[grind =, simp]
theorem rbContents_eq (rb : RingBuffer) :
    rbContents rb = rbContentsFrom rb.buf rb.head rb.count rb.cap := rfl

@[grind =, simp]
theorem rbContentsFrom_zero (buf : Array Int) (h cap : Nat) :
    rbContentsFrom buf h 0 cap = [] := rfl

@[grind =]
theorem rbContentsFrom_succ (buf : Array Int) (h n cap : Nat) :
    rbContentsFrom buf h (n + 1) cap
      = buf[h]! :: rbContentsFrom buf ((h + 1) % cap) n cap := rfl

/-- Pulse: `lemma_contents_length`（抽象序列長度 = count）。
    Pulse 那邊要對 count 做遞歸證明，這裡一樣。 -/
@[grind =, simp]
theorem rbContentsFrom_length (buf : Array Int) (h count cap : Nat) :
    (rbContentsFrom buf h count cap).length = count := by
  induction count generalizing h with
  | zero => rfl
  | succ n ih => rw [rbContentsFrom_succ]; simp [ih]

/-! ## 不變量

  Pulse 的 `is_ringbuffer rb s cap` 是 slprop：
    exists* buf h tl cnt. Vec.pts_to rb.buffer buf ** B.pts_to rb.head h
      ** ... ** pure (<一堆純條件>)
  Velvet 版只留下 `pure (...)` 那一半——資源那一半在值語意下不存在。
  抽象序列 s 也不放進來：它是 `rbContents rb`，需要時直接算。 -/
@[reducible]
def isRingBuffer (rb : RingBuffer) : Prop :=
  0 < rb.cap ∧
  rb.buf.size = rb.cap ∧
  rb.head < rb.cap ∧
  rb.tail < rb.cap ∧
  rb.count ≤ rb.cap ∧
  rb.tail = (rb.head + rb.count) % rb.cap   -- 合併 Pulse 的兩種情況

/-- 對應 Pulse 的 `unfold (is_ringbuffer rb s cap)` / `fold (...)`：
    在 Pulse 裡這是*程式裡的一步*（要在對的位置寫對的方向）；
    在 Velvet 裡它只是一條 `Iff.rfl`，交給 grind 自動雙向使用。 -/
@[grind =]
theorem isRingBuffer_def (rb : RingBuffer) :
    isRingBuffer rb ↔
      (0 < rb.cap ∧ rb.buf.size = rb.cap ∧ rb.head < rb.cap ∧ rb.tail < rb.cap ∧
        rb.count ≤ rb.cap ∧ rb.tail = (rb.head + rb.count) % rb.cap) :=
  Iff.rfl

/-! ## 模運算工具

  對應 Pulse 的 `lemma_mod_add_small` / `lemma_mod_add_assoc` /
  `lemma_tail_invariant_maintained`。Pulse 用 `FStar.Math.Lemmas`；
  這裡把對應的 Nat 規則餵給 grind。 -/
attribute [grind =] Nat.mod_add_mod Nat.zero_mod List.head!_cons List.tail_cons
attribute [grind] Array.size_replicate

/-- 「餘數比除數小」——環形索引 `(i + 1) % cap < cap` 全靠這條。
    直接 `attribute [grind] Nat.mod_lt` 沒用：grind 會拿結論
    `x % y < y` 當觸發模式，而我們的目標長成 `cap ≤ (tail+1) % cap`
    的否定形，對不上。用 `grind_pattern` 把觸發點改成「只要看到
    `x % y` 這個項」就好。 -/
theorem Nat.mod_lt_of_pos (x : Nat) {y : Nat} (hy : 0 < y) : x % y < y :=
  Nat.mod_lt x hy

grind_pattern Nat.mod_lt_of_pos => x % y

@[grind =]
theorem Array.size_set!_eq (a : Array Int) (i : Nat) (v : Int) :
    (a.set! i v).size = a.size := by simp

/-- push 之後 tail 的不變量還在（Pulse: `lemma_tail_invariant_maintained`）：
    (tl + 1) % cap = (h + (c + 1)) % cap，其中 tl = (h + c) % cap。 -/
@[grind =]
theorem rbTailStep (h c cap : Nat) :
    ((h + c) % cap + 1) % cap = (h + (c + 1)) % cap := by
  rw [Nat.mod_add_mod, Nat.add_assoc]

/-- pop 之後 tail 的不變量還在：head 前進一格、count 少一個，
    ((h + 1) % cap + (c - 1)) % cap 仍然是 (h + c) % cap。 -/
@[grind =]
theorem rbHeadStep (h c cap : Nat) (hc : 0 < c) :
    ((h + 1) % cap + (c - 1)) % cap = (h + c) % cap := by
  rw [Nat.mod_add_mod]
  congr 1
  omega

/-- 環上「走 c 步（0 < c < cap）回不到原點」——這是 push 寫入位置
    tail 不會踩到 head 的理由。Pulse 版藏在 lemma_push_contents 的
    歸納步驟裡（由 SMT 自動處理）。 -/
theorem rbWrapNe (h c cap : Nat) (hh : h < cap) (hc : 0 < c) (hlt : c < cap) :
    (h + c) % cap ≠ h := by
  rcases Nat.lt_or_ge (h + c) cap with hb | hb
  · rw [Nat.mod_eq_of_lt hb]; omega
  · rw [Nat.mod_eq_sub_mod hb, Nat.mod_eq_of_lt (by omega)]
    omega

/-! ## 核心 lemma：push 如何改變抽象序列

  Pulse: `lemma_push_contents`——把 x 寫到 tail、count + 1，
  抽象序列就從 s 變成 `Seq.snoc s x`。證明對 count 歸納：
  每剝掉一個 head，寫入點 tail 都還在剩下那段的尾巴。 -/
theorem rbContentsFrom_push (x : Int) (count : Nat) :
    ∀ (buf : Array Int) (h tl cap : Nat),
      0 < cap → buf.size = cap → h < cap → count < cap →
      tl = (h + count) % cap →
      rbContentsFrom (buf.set! tl x) h (count + 1) cap
        = rbContentsFrom buf h count cap ++ [x] := by
  induction count with
  | zero =>
    intro buf h tl cap hcap hsize hh _ htl
    have htl' : tl = h := by
      rw [htl, Nat.add_zero, Nat.mod_eq_of_lt hh]
    subst htl'
    have hget : (buf.set! tl x)[tl]! = x := by
      rw [Array.get_set_c tl tl x buf (by omega)]; simp
    rw [rbContentsFrom_succ, hget]
    simp
  | succ n ih =>
    intro buf h tl cap hcap hsize hh hn htl
    -- 寫入點不是目前的 head，所以第一個元素沒被動到
    have hne : tl ≠ h := by
      rw [htl]; exact rbWrapNe h (n + 1) cap hh (by omega) hn
    have hhead : (buf.set! tl x)[h]! = buf[h]! := by
      rw [Array.get_set_c h tl x buf (by omega)]
      simp [Ne.symm hne]
    -- 剝掉 head 之後：新 head 是 (h+1)%cap，剩下 n 個元素，tail 不變
    have hnext : (h + 1) % cap < cap := Nat.mod_lt _ hcap
    have htl2 : tl = ((h + 1) % cap + n) % cap := by
      rw [Nat.mod_add_mod, htl]
      congr 1
      omega
    rw [rbContentsFrom_succ, hhead,
        ih buf ((h + 1) % cap) tl cap hcap hsize hnext (by omega) htl2,
        rbContentsFrom_succ]
    simp

/-- 給 grind 用的版本：把「tl = (h+count)%cap」寫成假設，
    讓它在 pushBack 的驗證條件上直接對上模式。 -/
@[grind =]
theorem rbContentsFrom_set_snoc (buf : Array Int) (x : Int) (h tl count cap : Nat)
    (hcap : 0 < cap) (hsize : buf.size = cap) (hh : h < cap) (hlt : count < cap)
    (htl : tl = (h + count) % cap) :
    rbContentsFrom (buf.set! tl x) h (count + 1) cap
      = rbContentsFrom buf h count cap ++ [x] :=
  rbContentsFrom_push x count buf h tl cap hcap hsize hh hlt htl

/-- Pulse: `lemma_pop_contents`——在 Pulse 裡它的證明是 `()`，
    因為 `contents_of_buffer` 的定義就是 cons；這裡也一樣，
    只是要把 `count` 與 `count - 1` 的 Nat 減法搬開。 -/
@[grind =]
theorem rbContentsFrom_pop (buf : Array Int) (h count cap : Nat) (hc : 0 < count) :
    rbContentsFrom buf h count cap
      = buf[h]! :: rbContentsFrom buf ((h + 1) % cap) (count - 1) cap := by
  obtain ⟨n, rfl⟩ : ∃ n, count = n + 1 := ⟨count - 1, by omega⟩
  rw [rbContentsFrom_succ]
  simp

/-! ## 操作

  Pulse 每個 fn 的骨架都是
    unfold (is_ringbuffer rb s cap);  with buf h tl cnt. _;  ...;  fold (...)
  ——把資源拆開、動它、再包回去。Velvet 版沒有這層儀式：
  `require isRingBuffer rb` / `ensures isRingBuffer rb` 就是全部。 -/

/- Pulse:
     fn create (capacity:SZ.t{SZ.v capacity > 0}) (init:t)
       requires emp returns rb:ringbuffer t
       ensures is_ringbuffer rb Seq.empty (SZ.v capacity)
   原版要 alloc 一個 vec + 三個 box，然後用四次 rewrite 把
   `pts_to buffer buf` 對齊成 `pts_to rb.buffer buf` 才能 fold。 -/
method rbCreate (cap : Nat) (init : Int) return (rb : RingBuffer)
    require 0 < cap
    ensures isRingBuffer rb
    ensures rb.cap = cap
    ensures rbContents rb = []
    do
    return { buf   := Array.replicate cap init,
             head  := 0,
             tail  := 0,
             count := 0,
             cap   := cap }

prove_correct rbCreate by
  loom_solve

/- Pulse: fn capacity ... preserves is_ringbuffer ... ensures pure (SZ.v n == cap)
   Pulse 需要 unfold/fold 只為了「讀一個不可變欄位」；Velvet 直接投影。 -/
method rbCapacity (rb : RingBuffer) return (n : Nat)
    require isRingBuffer rb
    ensures n = rb.cap
    do
    return rb.cap

prove_correct rbCapacity by
  loom_solve

/- Pulse: fn size ... ensures pure (SZ.v n == Seq.length s)
   「count 等於抽象序列長度」在 Pulse 是不變量裡的一條 pure；
   這裡是 rbContentsFrom_length 這條 lemma 的直接推論。 -/
method rbSize (rb : RingBuffer) return (n : Nat)
    require isRingBuffer rb
    ensures n = (rbContents rb).length
    ensures n = rb.count
    do
    return rb.count

prove_correct rbSize by
  loom_solve

/- Pulse: fn is_empty ... ensures pure (b <==> Seq.length s == 0) -/
method rbIsEmpty (rb : RingBuffer) return (b : Bool)
    require isRingBuffer rb
    ensures b ↔ rbContents rb = []
    do
    return rb.count = 0

prove_correct rbIsEmpty by
  loom_solve

/- Pulse: fn is_full ... ensures pure (b <==> Seq.length s == cap) -/
method rbIsFull (rb : RingBuffer) return (b : Bool)
    require isRingBuffer rb
    ensures b ↔ (rbContents rb).length = rb.cap
    do
    return rb.count = rb.cap

prove_correct rbIsFull by
  loom_solve

/- Pulse:
     fn push_back (rb:ringbuffer t) (x:t) ... returns success:bool
       ensures exists* s'. is_ringbuffer rb s' cap **
         pure ((success ==> (Seq.length s < cap /\ s' == Seq.snoc s x)) /\
               (not success ==> (Seq.length s == cap /\ s' == s)))
   Pulse 用 `exists* s'` 表達「新的抽象序列不知道是哪一條，看成功與否」；
   Velvet 不需要這個存在量詞——新序列就是 `rbContents rb`，
   而舊序列是 `rbContents rbOld`（mut 參數的舊值免費提供，
   對應 Pulse 規格裡的 ghost `s`）。 -/
method rbPushBack (mut rb : RingBuffer) (x : Int) return (success : Bool)
    require isRingBuffer rb
    ensures isRingBuffer rb
    ensures rb.cap = rbOld.cap
    ensures success ↔ rbOld.count < rbOld.cap
    ensures success = true → rbContents rb = rbContents rbOld ++ [x]
    ensures success = false → rb = rbOld
    do
    if rb.count = rb.cap then
      return false
    else
      rb := { rb with
                buf   := rb.buf.set! rb.tail x,
                tail  := (rb.tail + 1) % rb.cap,
                count := rb.count + 1 }
      return true

prove_correct rbPushBack by
  loom_solve

/- Pulse:
     fn pop_front (rb:ringbuffer t) (#s:erased (Seq.seq t){Seq.length s > 0}) ...
       returns x:t
       ensures is_ringbuffer rb (Seq.tail s) cap ** pure (x == Seq.head s)
   注意 Pulse 把「非空」寫在 ghost 參數的 refinement 裡（`{Seq.length s > 0}`）；
   Velvet 寫成一般的 require。 -/
method rbPopFront (mut rb : RingBuffer) return (x : Int)
    require isRingBuffer rb
    require 0 < rb.count
    ensures isRingBuffer rb
    ensures rb.cap = rbOld.cap
    ensures x = (rbContents rbOld).head!
    ensures rbContents rb = (rbContents rbOld).tail
    do
    let v := rb.buf[rb.head]!
    rb := { rb with
              head  := (rb.head + 1) % rb.cap,
              count := rb.count - 1 }
    return v

prove_correct rbPopFront by
  loom_solve

/- Pulse: fn peek_front ... preserves is_ringbuffer rb s cap
     ensures pure (x == Seq.head s)
   Pulse 的 preserves（讀完原樣奉還）↦ 非 mut 參數。 -/
method rbPeekFront (rb : RingBuffer) return (x : Int)
    require isRingBuffer rb
    require 0 < rb.count
    ensures x = (rbContents rb).head!
    do
    return rb.buf[rb.head]!

prove_correct rbPeekFront by
  loom_solve

/- Pulse 的 `fn free (rb:ringbuffer t) requires is_ringbuffer rb s cap ensures emp`
   在這裡沒有對應物：值語意下沒有「擁有權」可歸還。
   附帶失去的東西也值得記一筆：Pulse 不變量裡那條 `is_full_vec rb.buffer`
   存在的唯一理由就是「將來要能 free」——可釋放性在分離邏輯裡是
   規格的一部分，在值語意裡連提都不用提。 -/

/-! ## 組合：push 完馬上 pop，拿回同一個元素

  這段展示 Velvet 的方法呼叫如何直接用上別的方法的 triple
  （`prove_correct` 產生的 `*_correct` 定理帶 `@[loomSpec]`，
  loom_solve 會自動拿來用）。對照 Pulse：那邊每個呼叫點都要
  讓 slprop 對得上（fold/unfold/rewrite），這裡只要前置條件成立。

  帶 mut 參數的方法在 Lean 層的型別是
    rbPushBack : RingBuffer → Int → VelvetM (Bool × RingBuffer)
  ——回傳值與被改動的參數打包成一個 tuple，所以呼叫端要自己
  把 `.2` 寫回 mut 變數。這正是「值語意版的 in-out 參數」。 -/
method rbPushThenPop (mut rb : RingBuffer) (x : Int) return (y : Int)
    require isRingBuffer rb
    require rb.count = 0
    ensures isRingBuffer rb
    ensures y = x
    ensures rbContents rb = []
    do
    let r ← rbPushBack rb x
    rb := r.2
    let p ← rbPopFront rb
    rb := p.2
    return p.1

prove_correct rbPushThenPop by
  loom_solve

/-! ## 執行

  Velvet 的 method 同時是可執行的 Lean 定義（Pulse 也是——它抽取到 C；
  這裡是 Lean 直接跑）。用 `#guard_msgs` 把預期輸出釘住，
  規格之外再多一層「真的跑得對」的保險。 -/

/-- info: DivM.res { buf := #[0, 0, 0], head := 0, tail := 0, count := 0, cap := 3 } -/
#guard_msgs in
#eval (rbCreate 3 0).run

/-- info: DivM.res (42, { buf := #[42, 0, 0], head := 1, tail := 1, count := 0, cap := 3 }) -/
#guard_msgs in
#eval (rbPushThenPop ⟨Array.replicate 3 0, 0, 0, 0, 3⟩ 42).run

-- 滿了就拒絕（回傳 false、狀態原封不動）
/-- info: DivM.res (false, { buf := #[7, 8, 9], head := 1, tail := 1, count := 3, cap := 3 }) -/
#guard_msgs in
#eval (rbPushBack ⟨#[7, 8, 9], 1, 1, 3, 3⟩ 5).run

-- head 在 2、pop 之後繞回 0——這就是「環形」那個字
/-- info: DivM.res (9, { buf := #[7, 8, 9], head := 0, tail := 2, count := 2, cap := 3 }) -/
#guard_msgs in
#eval (rbPopFront ⟨#[7, 8, 9], 2, 2, 3, 3⟩).run

/- 收尾思考：
   這一課的翻譯裡，Pulse 的「難」與 Velvet 的「難」剛好錯開。
   * Pulse 難在資源管理：欄位是資源、抽象序列是 ghost，
     每個操作都得 unfold/fold/rewrite 把它們搬進搬出，
     還要保證 free 得掉（is_full_vec）。
   * Velvet 難在——沒有難的：資源那一半整個消失。
     剩下的數學（環形索引的模運算、抽象序列的 snoc/tail）
     兩邊一樣重，因為那才是 ring buffer 真正的內容。
   代價在哪？值語意下 `rb := { rb with buf := rb.buf.set! ... }` 是
   「概念上的整份拷貝」，Velvet 沒有辦法在型別層保證這份拷貝
   會被編譯成就地更新（Pulse 的 vec 則保證了）。也就是說：
   驗證負擔搬走了，但「這段程式在真機上是 O(1) 還是 O(n)」這件事，
   從規格裡消失了。 -/
