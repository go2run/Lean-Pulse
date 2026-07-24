/-
  LeanPulse.PulseByExample — 對應 `src/PulseByExample.fst`

  這一課在 Pulse 中介紹：fn、requires/ensures、`pts_to`（|->）、
  分離連接 `**`、erased（ghost）值、陣列與迴圈不變式。

  ── 核心翻譯表（Pulse → Velvet）─────────────────────────────
  │ pts_to r 'v（擁有 r，初值為 ghost 'v） │ (mut r : τ) 參數；'v ↦ rOld  │
  │ 唯讀的 fractional permission          │ 一般（非 mut）參數           │
  │ p ** q（兩塊分離的資源）              │ 兩個不同的 mut 參數（Lean 的 │
  │                                       │ 值語意保證它們永不 alias）   │
  │ exists* s. a |-> s ** pure (...)      │ ensures 直接用最終值 + 量詞  │
  │ while ... invariant（slprop 形式）    │ while ... invariant（純命題）│
  ──────────────────────────────────────────────────────────────
  重點直覺：分離邏輯用「資源斷言」管理 aliasing；Velvet/Dafny 用
  「值語意 + mut 參數」讓 aliasing 從語言中消失。兩者解決同一個問題，
  代價不同：Pulse 能談指標別名與並行，Velvet 的規格則更簡單直接。
-/
import Velvet.Std

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Pulse:
     fn five () returns n:int ensures pure (n == 5) { fstar_five }  -/
@[reducible]
def fstar_five : Int := 5

method five (u : Unit) return (n : Int)
    ensures n = 5
    do
    return fstar_five

prove_correct five by
  loom_solve

/- Pulse 的 five_alt 用精化型別 `n:int { n == 5 }` 取代 ensures。
   Lean 也有 subtype `{ n : Int // n = 5 }`，但在 Velvet 中慣用 ensures。 -/

/- Pulse:
     fn ref_swap (r1 r2:ref int)
       requires r1 |-> 'n1 ** r2 |-> 'n2
       ensures  r1 |-> 'n2 ** r2 |-> 'n1
   兩個 `mut` 參數對應兩塊分離的資源；'n1/'n2 這兩個 ghost 初值
   對應 r1Old/r2Old。Pulse 需要 ** 保證 r1 ≠ r2（不 alias）；
   Velvet 的參數是值，天生不會 alias。 -/
method refSwap (mut r1 : Int) (mut r2 : Int) return (u : Unit)
    ensures r1 = r2Old
    ensures r2 = r1Old
    do
    let v1 := r1
    r1 := r2
    r2 := v1
    return

prove_correct refSwap by
  loom_solve

/- Pulse:
     fn ref_non_zero (r1:ref int) (n1:Ghost.erased int)
       requires r1 |-> n1  returns b:bool
       ensures r1 |-> n1 ensures pure (b == (reveal n1 <> 0))
   唯讀存取（preserves）↦ 非 mut 參數；ghost 值 n1 ↦ 參數本身。 -/
method refNonZero (r1 : Int) return (b : Bool)
    ensures b = (r1 ≠ 0)
    do
    return (r1 ≠ 0)

prove_correct refNonZero by
  loom_solve

/- Pulse:
     fn arr_swap (n i j) (a:larray t (v n))
       requires a |-> 's0 ** pure (i < n /\ j < n)
       ensures exists* s. a |-> s ** pure (交換 i j、其餘不變)
   Pulse 用 exists* 引出「最終序列 s」；Velvet 直接用 arr（最終值）
   與 arrOld（初始值）描述同一件事，existential 消失了。 -/
method arrSwap (mut arr : Array Int) (i : Nat) (j : Nat) return (u : Unit)
    require i < arr.size
    require j < arr.size
    ensures arr.size = arrOld.size
    ensures arr[i]! = arrOld[j]!
    ensures arr[j]! = arrOld[i]!
    ensures ∀ k, k < arr.size ∧ k ≠ i ∧ k ≠ j → arr[k]! = arrOld[k]!
    do
    let vi := arr[i]!
    arr := arr.set! i (arr[j]!)
    arr := arr.set! j vi
    return

attribute [grind] Array.size_set Array.getElem_set

prove_correct arrSwap by
  loom_solve

/- Pulse:
     fn max (n:SZ.t) (a:larray nat (v n))
       requires a |-> Frac 'p 's ** pure (...)
       returns r:nat
       ensures a |-> Frac 'p 's ** pure (forall i < n. 's[i] <= r)
   `Frac 'p`（分數權限、唯讀共享）↦ 非 mut 的 a——呼叫者的陣列
   自動不變，這正是 fractional permission 想表達的「只讀不寫」。
   while 的 invariant 從 slprop（i |-> vi ** ...）簡化為純命題，
   因為區域變數 i、maxV 在 Velvet 中就是值，不需要 pts_to。 -/
method maxElem (a : Array Nat) return (r : Nat)
    ensures ∀ i, i < a.size → a[i]! ≤ r
    do
    let mut i := 0
    let mut maxV := 0
    while i < a.size
        invariant i ≤ a.size
        invariant ∀ j, j < i → a[j]! ≤ maxV
        done_with i = a.size
    do
        let v := a[i]!
        i := i + 1
        if v > maxV then
            maxV := v
    return maxV

prove_correct maxElem by
  loom_solve

#eval (maxElem #[3, 1, 4, 1, 5]).run   -- 期望：DivM.res 5
