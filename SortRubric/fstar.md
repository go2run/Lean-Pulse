## 前情回顧

* 肯定 AI 自，2025 年底起，Opus 4.5 和 GPT-5.2（及更後續）等模型的推出，Agent 可以有效協助撰寫程式、證明(ex: F*與Pulse，Lean、Coq、Verus、Dafny 等)
* 但 Agent 產出的東西，標準不一致，在複雜的系統上無法說清楚，甚麼是對的。

所以提出了
* Rubrics
  * 規格要寫到怎麼樣的程度。
* Templates
  * 我們可以給予怎樣的資料，讓 Agent 能更有效的寫出證明，透過範圍更大的模板。
* Audits
  * 我們依然要檢查的範圍。


## Rubrics 的排序例子

* 在 Rubrics 的介紹下，如何將已有的排序法，改寫成 Rubrics 的標準。

```fstar
let sorted (s: Seq.seq int) : prop
  = forall (i j: nat). i <= j /\ j < Seq.length s ==> Seq.index s i <= Seq.index s j

let permutation (s1 s2: Seq.seq int) : prop = (Seq.Properties.permutation int s1 s2)
```

```fstar
fn insertion_sort
    (a: array int)
    (#s0: Ghost.erased (Seq.seq int))
    (len: SZ.t)
requires
    a |-> s0 **
    pure (
        SZ.v len == Seq.length s0 /\
        Seq.length s0 <= A.length a)
ensures
    a |-> s **
    pure (
        Seq.length s == Seq.length s0 /\
        sorted s /\
        permutation s0 s)
```

```fstar
fn heapsort
    (a: A.array int)
    (n: SZ.t)
    (#s0: erased (Seq.seq int) {
        SZ.v n <= A.length a /\
        Seq.length s0 == A.length a /\
        SZ.fits (op_Star 2 (Seq.length s0) + 2)     // ← 多一個溢位前條件
    })
requires a |-> s0
ensures exists* s.
    a |-> s **
    pure (
        Seq.length s == Seq.length s0 /\
        sorted_upto s (SZ.v n) /\                    // ← 只證前 n 個排好
        permutation s0 s /\
        (forall (k:nat). SZ.v n <= k /\ k < Seq.length s ==> Seq.index s k == Seq.index s0 k)
    )
```


簽章

| 欄位說明 | insertion_sort | heapsort | 說明 |
|---|---|---|---|
| 陣列參數 | `a: array int` | `a: A.array int` | **同、寫法差異**、`A.`差有沒有 open 而已、同一個型別 |
| ghost 內容 | `#s0: Ghost.erased (Seq.seq int)` | `#s0: erased (Seq.seq int) { 溢位前條件 }` | **同、寫法差異**＋heapsort 多掛 refinement |
| 參數順序 | `a, #s0, len` | `a, n, #s0` | **寫法**。ghost 參數都用 `#` 具名傳，位置對呼叫端無影響 |
| ※長度參數 | `len: SZ.t` | `n: SZ.t` | **異**（語意）。型別相同，但 `len` 鎖死成全長、`n` 是可小於全長的前綴長。實際約束見下方兩列 |


前條件

| 欄位說明 | insertion_sort | heapsort | 說明 |
|---|---|---|---|
| 所有權 | `a \|-> s0` | `a \|-> s0` | 同、獨佔資源 |
| 事實擺放 | `requires` 內的 `pure (…)` | `#s0` 的 refinement | **同、寫法差異**。語意等價；差別只在 refinement 的事實在型別層直接可見，`pure` 要先從分離邏輯脈絡取出 |
| 序列長 vs 陣列長 | `Seq.length s0 <= A.length a` | `Seq.length s0 == A.length a` | **寫法**（且兩者皆多餘）。`a \|-> s0` 本來就蘊含 `==`，所以 `<=` 也恆真，兩邊都給不出新資訊 |
| ※長度參數綁定 | `SZ.v len == Seq.length s0` | `SZ.v n <= A.length a` | **異**、`==` 鎖死全長、`<=` 允許前綴。**這是兩份規格分岔的唯一源頭** |
| ※溢位 | — | `SZ.fits (2 * Seq.length s0 + 2)` | **異、僅 heapsort**。子節點索引 `2i+1` / `2i+2` 的 `fits` 義務，局部證不掉只好丟給呼叫者；且是平台相依的假設 |



後條件

| 欄位說明 | insertion_sort | heapsort | 說明 |
|---|---|---|---|
| 存在量化 | `a \|-> s`（隱式） | `exists* s.`（顯式） | **同、寫法差異**。Pulse 對 `ensures` 裡的自由變數自動存在量化，兩者等價 |
| 所有權歸還 | `a \|-> s` | `a \|-> s` | **同** |
| 長度保持 | `Seq.length s == Seq.length s0` | `Seq.length s == Seq.length s0` | **同** |
| 排列 | `permutation s0 s` | `permutation s0 s` | **同** |
| ※排序 | `sorted s` | `sorted_upto s (SZ.v n)` | **異**。全排序 vs 前 n 個排序。`n` 取全長時後者退化成前者，但要一條橋接引理才對得上 |
| ※未動區域 | — | `forall k. SZ.v n <= k /\ k < Seq.length s ==> s[k] == s0[k]` | **異、僅 heapsort**。不能省：沒有它，「把最小的 n 個搬到前面、其餘亂放」也滿足前三條 |

---

註解：講短篇幅甚麼是TypeClasses 讓 array_sort 可以看懂


## Shared Rubrics：Q1 Spec 各寫各的、不好維護、分散 reviewer 注意力
依照 Rubric 的品質，一份好的 Spec 可以付復用

最終樣子：
```
class array_sort (f:nat -> nat) = {
    sort : SortFunctionType f
}

let insertion_sort_bound (n:nat) = n * (n - 1) / 2
instance insertion_sort_array_sort : array_sort insertion_sort_bound = {
  sort = insertion_sort_impl
}
```


```
instance merge_sort_array_sort
: array_sort (fun n -> if n > 0 then 4 * n * MS.log2_ceil n + 4 * n else 0)

instance heapsort_array_sort
: array_sort (fun n ->
    if n > 0 then
      (n / 2) * (2 * HC.log2_floor n) +
      (n - 1) * (2 * HC.log2_floor n)
    else 0)

instance quicksort_array_sort
: array_sort (fun n -> n * (n - 1) / 2)
```

### Fstar TypeClasses

```
class array_sort = {
    sort:
        (fn (#a:Type)
            (arr:array a)
            (len:SZ.t)
            (ord:Pulse.Lib.TotalOrder.total_order a)
            (#s:erased (Seq.seq a))
            requires arr |-> s ** pure (A.length arr == SZ.v len)
            ensures exists* s'.
                arr |-> s' **
                pure (sorted #_ #ord s' /\ permutation s s'))
}

instance insertion_sort_array_sort : array_sort{
    sort = insertion_sort_impl
}

fn insertion_sort_impl
    (#a:Type)
    (arr:array a)
    (len:SZ.t)
    (ord:Pulse.Lib.TotalOrder.total_order a)
    (#s:erased (Seq.seq a))
requires
    arr |-> s **
    pure (A.length arr == SZ.v len)
ensures exists* s'.
    arr |-> s' **
    pure (
        sorted #_ #ord s' /\
        permutation s s'
    )
{
    // 這裡寫 insertion sort 的實際程式與證明
}
```

## Ghost State For Complexity Proofs：Q2 結果正確，仍無法區分不同演算法的時間、空間複雜度
* 時間複雜度分析的主要方式
  * 用計數器，測量每次 Comparisons, Swaps。
   * 豐富 invariants 追蹤 ghost counter 的界限。
      *  當 spec 要求滿足某種「不超出邊界的時候」，遇到經過迴圈的程式我們無法直接判斷，所以需要一個過程「豐富 invariants，補充過程資訊」，當迴圈結束後協助推倒判斷。
    * 證明 ghost counter 器受限於輸入大小的函數（例如，堆排序的 n log n ）。
      *  ghost counter 數值不等於演算法滿足複雜度，而是 Comparisons, Swaps 的次數。
* 空間複雜度：這邊沒介紹到。
* 
```
module GR = Pulse.Lib.GhostReference

let complexity_bounded (cf c0: nat) (n: nat) : prop =
    cf >= c0 /\
    cf - c0 <= n * (n - 1) / 2

fn insertion_sort
    (a: array int)
    (#s0: Ghost.erased (Seq.seq int))
    (len: SZ.t)
    (ctr: GR.ref nat)                        // ghost reference
    (#c0: Ghost.erased nat)                  // 第一次進入比較的時候，起始值從哪裡開始(通常是0)
requires a |-> s0 ** ctr |-> c0
requires pure (
    SZ.v len == Seq.length s0 /\ Seq.length s0 <= A.length a
)
ensures exists* s (cf: nat).
    a |-> s ** ctr |-> cf **
    pure (Seq.length s == Seq.length s0 /\
          sorted s /\
          permutation s0 s /\
          complexity_bounded cf c0 (SZ.v len))
```


## Better Rubrics with Abstraction

**考慮 Q1+Q2+Q3+Q4**

* Q1：規格不可以分裂
* Q2：加入複雜度
* Q3：ctr 要強制觸發
    * 加入了 ctr 測量了複雜度，依然不可免去確認 ctr 是否正確被觸發。
    * 提供一個比較API，`iord`。
* Q4：作弊下修 ctr
    * 假設 Q3 已解決，ctr 有沒有可能再最後一行作弊寫成`ctr = 0`。
    * Monotonic Ghost State，是 fstar 內建功能 `Pulse.Lib.MonotonicGhostRef`
       * 只有一個目的：讓 ctr 的值一旦增加就不能減少。
* Q5問題：時間複雜度不一樣
    * 每一種排序時間複雜度不一樣，同一個 Spec 不能描述那麼多。
    * 參數化 array_sort，也就是一種生成 Spec 的技巧。
* Q6問題：忽略`iord`API
    * 作弊方式有沒有可能是直接呼叫 `arr[i] <= arr[k]`，而直接忽略規格提供的`iord`API。
    *  已經解決，因為宣告的 a:Type，無法取得比較方式。

   

```
module MR = Pulse.Lib.MonotonicGhostRef
module TO = Pulse.Lib.TotalOrder

let leq_nat (x y:nat) : prop = x <= y           // 舊值x <= 新值y

let ticks_t = MR.mref leq_nat                   // Monotonic Ghost State 的機制，保證之後用到的 ctr 記數器無法作弊。
                                                // ctr: ticks_t
let instrumented_total_order (#a:Type) (ord:TO.total_order a) (ctr:ticks_t) =
    fn (x y:a) (#i:erased nat)
    requires MR.pts_to ctr #1.0R i
    returns o:order
    ensures MR.pts_to ctr #1.0R (i + 1)         // 每走一次必定家一次
    ensures pure (o == x `ord.TO.compare` y)    // returns 的結果 o 不可以造假

class array_sort (f: nat -> nat) = {
    sort:
        (fn (a:Type)
            (arr:A.array a)
            (len:SZ.t)
            (ctr:ticks_t)
            (#ord:erased (TO.total_order a))
            (iord:instrumented_total_order ord ctr)
            (#s:erased (Seq.seq a)) (#i:erased nat)
        requires arr |-> s ** MR.pts_to ctr #1.0R i
        requires pure (A.length arr == SZ.v len)
        ensures exists* s' ticks.
            arr |-> s' **
            MR.pts_to ctr #1.0R ticks **
            pure (sorted #_ #ord s' /\ permutation s s' /\ ticks <= i + f (Seq.length s)))
}
```



## 最後的問題

簡化 Spec 為 array_sort，但 Heap Sort 依然未解決

1. Q7a：全排序「`sorted s`」 vs 前 n 個排序 「`sorted_upto s (SZ.v n)`」
    * `sorted_upto s (SZ.v n)` 不能放在公開規格中
2. Q7b：為了避免寫 `SZ.fits (2*idx+1)` 在共用的介面上 `array_sort` 怎麼改寫。


**Q7.a：**
```
let sorted_upto_implies_sc_sorted ord s
  : Lemma (requires sorted_upto ord s (Seq.length s))
          (ensures SC.sorted #a #ord s)
  = assert_norm (SC.sorted #a #ord s ==
      (forall (i j:nat). i <= j /\ j < Seq.length s ==>
        le_ord ord (Seq.index s i) (Seq.index s j)))
```


**Q7.b：**

```
let half = SZ.div heap_size 2sz;
if (SZ.gte idx half) {
  left_idx_after_heap_size heap_size idx;    // 純數學：沒有左子節點
  ...                                         // 完全不碰機器乘法
} else {
  left_idx_before_heap_size heap_size idx;   // 先得到 left_idx idx < heap_size
  left_child_sizet (Seq.length s) heap_size idx;
  let two_idx = SZ.mul 2sz idx;              // 到這裡才算
  ...
}
```


* 因為 `2N+1` 可以取得，某 N 個節點的左節點，`2N+2`可以取右節點
  * 假設要取索引為0算起，第3的`[3]`，那`2*3+1` 剛好是左節點`7`、`2*3+2` 剛好是右節點`8`

```
n = 10
陣列:
    [0  1  2  3  4  5  6  7  8  9] 

樹：
                  0
              /       \
            1           2
          /   \       /   \
        [3]    4    (5)     6
        / \   /
       7   8 9


half = ⌊10/2⌋ = 5
分界剛好落在 (5)

索引：
      [ 0  1  2  3  4 │ 5  6  7  8  9 ]
        <──── PP ───> │ <─── LP ────>
                half = 5

奇數也一樣，n = 9、half = ⌊9/2⌋ = 4

樹：
                  0
              /       \
            1           2
          /   \       /   \
         3    (4)     5     6
        / \ 
       7   8
```




`SZ.div heap_size 2sz;`

n 是偶數： `half = ⌊n/2⌋ = n/2`

n 是奇數： `half = ⌊n/2⌋ = (n-1)/2`


```
let half = SZ.div heap_size 2sz;
even：n=10 half=5
odd：n=9 half=4
if (idx >= half) {
  ex1 even: 、(idx=5)>= half，就進來
  [ 0  1  2  3  4 │ 5  6  7  8  9 ]
    <──── PP ───> │ <─── LP ────>
  ex2: odd 、(idx=4)>= half，就進來
  [ 0  1  2  3 │ 4  5  6  7  8 ]
    <─── PP ─> │ <────── LP ─>
} else {
  ex1 even: (idx=4)<= 剛好是 <──── PP ───>
  ex2  odd: (idx=3)<= 剛好是 <─── PP ─>
  得到 left_idx idx < heap_size
  到這裡才算 idx*2，安全
  ...
}
```