# 指引勘誤表 — `排序 rubric 分階段強化：實作指引 v1`

**產出於**：第 00 次環境勘查
**用途**：併回專案端的指引文件，讓兩邊不再分岔
**原則**：只列**實測過**的。未驗證的另列於 §E，不混進正表。

驗證環境：`leanprover/lean4:v4.24.0`、Velvet@master、Loom@master（`lake-manifest.json` 為準）
所有「真實 API」欄的行號，指的是 `.lake/packages/` 底下的實際檔案。

---

## A. 語法與記號

| 指引原文（含節號） | 真實 API（含檔名:行號） | 影響哪幾步 | 建議改法 |
|---|---|---|---|
| §4.2 表格：「`[part\| ...]` / `[total\| ...]` 記號」<br>§6.11 亦用 `[total\|` | `Velvet/VelvetTheory.lean:6`<br>`notation "[totl\|" t "]" => open TotalCorrectness TotalCorrectness.DemonicChoice in t` | 11 | `[total\|` → **`[totl\|`**（四個字母，無 `a`）。全文替換。 |
| §2.4：「寫法上有 `method` / `requires` / `ensures` / ...」 | `Velvet/Syntax.lean:65`<br>`syntax "require" termBeforeReqEnsDo : require_caluse` | 全部 | `requires` → **`require`**（單數）。`requires` 是 F\*/Pulse 拼法，Velvet 不收。<br>註：`ensures` 確實有 s（`Syntax.lean:66`），兩者不對稱，容易寫錯。 |
| §6.3 / §6.7 / §6.8 草稿碼在 `structure` 欄位裡寫 `[part\| triple ... ]` | **兩個同名記號打架**：<br>`Loom/MonadAlgebras/WP/Liberal.lean:143`<br>`notation "[part\|" t "]" => open ExceptionAsSuccess in t`<br>`Velvet/VelvetTheory.lean:8`<br>`notation "[part\|" t "]" => open PartialCorrectness ... in t` | 03–09 | 在 `structure` 欄位裡**不要用 `[part\|`**，改成顯式 open：<br>`open PartialCorrectness PartialCorrectness.DemonicChoice in`<br>`structure SortImpl where ...`<br>（已實測可行） |
| （指引未提） | `Velvet/Syntax.lean:68-72`：`method` 是 `command` 語法，前面**不能**放 `/-- -/` docstring | 全部 | `method` 的說明改用 `/-! ... -/` 或 `--`。<br>逐字錯誤：`unexpected token 'method'; expected 'lemma'` |
| （指引未提） | `velvet_documentation.md:88`：`#guard_msgs` 的 docstring **只能**放預期訊息本身 | 10（SPOTs） | 說明文字要放到 docstring **外面**。<br>逐字錯誤：`❌️ Docstring on '#guard_msgs' does not match generated message` |

### A 的逐字錯誤訊息

`[part|` 歧義（`probe/P6.lean`）：
```
error: Ambiguous term
  [part|triple True (sort a) (fun r => SortSpec a r.2)]
Possible interpretations:
  {True}sort a{r,SortSpec a r.2} : Prop

  {True}sort a{r,SortSpec a r.2} : Prop
```
> 注意兩個 interpretation **印出來一模一樣**——這個錯誤訊息本身很難自我診斷，
> 必須回去讀 `notation` 的定義才找得到原因。值得寫進指引的除錯章節。

`method` 前放 docstring：
```
error: SortRubric/Cheats/Unresolved_FakeCounterPadded.lean:49:57: unexpected token 'method'; expected 'lemma'
```

---

## B. 型別形狀

| 指引原文（含節號） | 真實 API（含檔名:行號） | 影響哪幾步 | 建議改法 |
|---|---|---|---|
| §6.3：`sort : Array Int → VelvetM (Array Int)` | `Velvet/Syntax.lean:330-337`：`mut` 參數併進回傳 tuple<br>`retType <- \`($retType × $mutTypeProd)` | 03–09 | 改成 **`VelvetM (Unit × Array Int)`**。<br>一般規則：`method f (mut a : A) (mut b : B) return (r : R)`<br>⇒ `f : … → VelvetM (R × A × B)` |
| §6.9：假設 `SortM` 可以搭配 `method` 使用（Q1 待測） | `Velvet/Syntax.lean:343`<br>`def $name $bindersIdents* : VelvetM $retType:term := do $mods* $doSeq*`<br>**`VelvetM` 是寫死的** | **09** | Q1 的答案是**否**。指引 §6.9 的三種結局應改寫：<br>「成功」一欄要刪掉「用 `method` 寫」的假設；<br>走 `SortM` 就必須手寫 monadic code，失去 `invariant`/`decreasing`/`done_with`/`loom_solve`。 |
| §6.2：`SortSpec = Sorted after ∧ SameElements before after` | Velvet 把多條 `ensures` **反序**合取<br>（實測：`ensures A` `ensures B` ⇒ 後條件為 `B ∧ A`） | 02–09 | 指引不必改定義（人類順序較好讀），但要**加一句警告**：<br>與 `<method>_correct` 對接時形狀會差一個 `And.comm`，<br>橋接成本見 `Opt02_Notes.md` 的實測數字。 |
| §6.8 草稿碼：`def Sorted (ord : SpecOrder α) (a : Array α) : Prop := ∀ i j, i ≤ j ∧ j < a.size → ord.le a[i]! a[j]!` | `a[i]!` 需要 `[Inhabited α]`；<br>而 `leafny_binder` **不收 instance binder**（`Velvet/Syntax.lean:63-64`，只有 `(id : t)` 與 `(mut id : t)`） | **08** | 加一行 `variable [Inhabited α]`（section 層級，如 `Velvet/Demo/Demo.lean:42` 的 `variable [FinEnum α]`）。<br>**並在 §6.8 加註**：`Inhabited` 安全，**條件是 `SameElements` 留在後條件裡**（它讓實作能生 `default`，靠 multiset 相等擋住）。<br>逐字錯誤：`failed to synthesize Inhabited α` |
| §6.2 陷阱 3：建議用 `Velvet/Examples/IsSorted.lean` 的 `chain_le` | `IsSorted.lean:26`：`def chain_le (a : Array Int) …` 寫死 `Array Int` 與 `le_trans` | 08 | 第 08 次抽象化 α 之後**不能直接用**，須自行改寫成 `ord.trans` 版本。指引應把這筆移植成本寫明。 |

---

## C. 指引沒提、但實務上必要

| 缺什麼 | 真實 API（含檔名:行號） | 影響哪幾步 | 建議補進指引 |
|---|---|---|---|
| `done_with` 子句 | `Velvet/Syntax.lean:243`：`$[done_with $inv_done]?` | 02–11 | 迴圈退出時要導出的事實。缺了會出現 `case «done_1: …»` 的 unsolved goal。<br>官方 `insertionSort`（`Examples.lean:60`）就有。 |
| `loom_solve!`（驚嘆號版） | `Velvet/Examples/Total_Partial_example.lean:44` 用的是 `loom_solve!` | 02–11 | 巢狀迴圈時 `loom_solve` 力道不足，要用 `loom_solve!`。指引 §2.4 只提到 `loom_solve`。 |
| `set_option loom.solver.grind.splits 40` | `Total_Partial_example.lean:11` | 02–11 | 預設 20 對巢狀插入排序不夠。<br>逐字錯誤：`Failed to prove assertion` + 一個 ordering invariant 的目標。 |
| `attribute [grind] Array.multiset_swap` | `Velvet/Std.lean:105` | 02–11 | 少了它，跨 `swap!` 的 multiset 保存 invariant 證不出來。官方 `Examples.lean:47` 亦如此。 |
| `swap!` 的語法 | `Velvet/Std.lean:70`<br>`\| \`(doElem\|swap! $id1:ident[$idx1:term]! $id2:ident[$idx2:term]!)` | 02–11 | 形式固定為 `swap! arr[i]! arr[j]!`，兩邊都要有 `!`。 |
| **`@[grind]` 於具名 predicate** ★ | 實測：`ensures Sorted arr`（引用 `def`）不加 `@[grind]` 會讓 `loom_solve!` 卡在 `Failed to prove assertion` | **02–09** | **這是一條依賴鏈，不只是一列 API 差異**：<br>`ensures` 引用具名 predicate 需要 `@[grind]` → 否則規格只能就地展開 → 沒有具名 predicate → **第 03 次的 interface 抽象不成立**。<br>建議同時寫進指引 §6.2「陷阱」與 §6.3「前提」。 |
| **`triple_cons`（consequence rule）** ★ | `Loom/MonadAlgebras/WP/Basic.lean:54`<br>`lemma triple_cons (x : m α) {pre pre' post post'} : pre' ≤ pre → (∀ y, post y ≤ post' y) → triple pre x post → triple pre' x post'` | **03–09** | **指引完全沒提到 Loom 有 consequence rule，但它是 interface 抽象的關鍵工具。**<br>`l = Prop` 時 `≤` 就是蘊涵，後條件重排寫成 `fun _ h => ⟨…⟩` 即可。<br>相較 `funext`/`propext`/`▸` 的寫法，它對**任意項數與任意重排**都成立（實測：三項時前者失效、它成立）。 |
| **`#guard_msgs` 可以釘住 `prove_correct` 的失敗** ★ | 實測可行（`probe/G1.lean`、`G2.lean`） | 02–10 | 「這支作弊證不出來」可以從**一次性觀察**升級成**迴歸測試**：<br>`/-- error: … -/ #guard_msgs in prove_correct X by …`<br>訊息相符 → 吃掉，build 綠；不符或**根本沒有訊息（作弊通過了）** → 報錯。<br>⚠ **代價**見下一列。 |
| ⚠ 失敗的 `prove_correct` 會留下 `sorryAx` **且帶 `@[loomSpec]`** | `Velvet/Syntax.lean:411` 產生 `@[loomSpec] lemma <name>_correct`；證明失敗時 Lean 仍加入環境並依賴 `sorryAx` | 02–10 | 用上一列的手法時**必須圍堵**：<br>① `#print axioms` + `#guard_msgs` 把 `sorryAx` 釘成明文<br>② **不得有任何模組 import 該檔**——sorry 過的 `@[loomSpec]` 若被下游看見，可能污染 `loom_solve`<br>本專案以 `check_isolation.sh` 的「圍堵」段機械保證，並附負向測試。 |
| **`#guard_msgs` 釘多則訊息** | 實測：docstring 內用 `---` 分隔即可一次釘住多則 | 02–10 | 一次 `prove_correct` 失敗常產生兩則訊息（`Failed to prove assertion` ＋ `unsolved goals`）。 |
| **呼叫 `mut` 參數的 method** | 只有 `let ⟨_, x'⟩ ← M args` 可用；bare `M args` 與文件記載的 `let r ← M args` **都會注入 `sorry`** | **05、09** | 見 `UPSTREAM_REPORT.md` Instance 2。指引示範遞迴分解時務必用解構形式，**並且要帶 R12 控制組**——這個 bug 的症狀跟「界限疊不起來」長得一樣。 |
| `<method>_correct` 的實際形狀 | 實測 `#print`：<br>`theorem f_correct : ∀ (aOld : T), {have a := aOld; True} f aOld {x, match x with \| (r, a) => …}` | 03–09 | 兩個好消息值得寫進指引：<br>① 前條件 `have a := aOld; True` **與 `True` 定義相等**<br>② 後條件 `match x with \| (r,a) => …` **與 `… x.2` 定義相等**（結構 eta）<br>兩者都不需要額外的橋接。 |

---

## D. 專案結構假設

| 指引原文 | 本專案的實況 | 影響哪幾步 | 建議改法 |
|---|---|---|---|
| R1：「放在專案 Lean source root 底下（**與 `Velvet/` 同層**）」 | `Velvet/` 是 **git 外部依賴**，位於 `.lake/packages/Velvet/Velvet/`，不在專案內 | 全部 | 改成「放在專案的 Lean source root」。<br>「與 Velvet 同層」只在 Velvet 是 vendored 子目錄時才成立。 |
| R1：「**只新建一個資料夾** `SortRubric/`」 | Lake 不會自動收錄新資料夾，必須改 `lakefile.lean` | 全部 | 補一句例外：允許在 `lakefile.lean` **末尾追加** `lean_lib SortRubric`（不動既有行）。<br>實測：`globs := #[Glob.submodules \`SortRubric]` **不需要**根檔 `SortRubric.lean`。 |
| §4.2 表格的檔案路徑寫成 `Velvet/Syntax.lean`、`velvet_documentation.md` 等 | 實際在 `.lake/packages/Velvet/` 底下 | 00 | 加一句：路徑相對於 `.lake/packages/Velvet/`。 |
| R4：「每完成一步，`lake build` 必須全綠」 | 本專案基準 build **在動手前就是紅的**（`VelvetLC917`，commit `69e292a`） | 全部 | 改成：`lake build SortRubric` 全綠 **且** 完整 build 的失敗集合與釘住的 baseline 逐字相同。<br>已機械化為 `SortRubric/check_build.sh`。 |

---

## E. 尚未驗證（不列入正表，待後續步驟實測）

| 指引處 | 待驗證的事 | 預定在第幾步驗 |
|---|---|---|
| ~~§6.2~~ | ~~`example : ¬ SortSpec …` 的戰術~~ **已解決**：`Sorted` 含無界 `∀` 不可判定，`decide` 也看不穿 `def`。配方：`rintro ⟨-, h⟩; revert h; unfold SameElements Array.toMultiset; decide` | ~~02~~ ✅ |
| §6.7 | `InstrOrder.cmp : α → α → Ticks → VelvetM (Bool × Ticks)` 能否在 `method` 的 `do` 區塊裡用 `←` 呼叫 | 07 |
| §6.8 | α 抽象、`ord.le` 為 `Prop` 之後，`loom_solve` 還能不能證出 bubble sort（`grind` 失去 `Int` 的算術支援，風險高） | 08 |
| §6.9 | Q2：`loom_solve` 能否穿過一層 opaque monad | 09（spike） |
| §6.11 | `VelvetM.total_decompose_triple` 在加了 `ticks` 參數之後是否仍適用 | 11 |

---

## F. 指引中**經實測確認正確**的部分（避免下一個人重複驗證）

| 指引處 | 主張 | 驗證方式 |
|---|---|---|
| §2.4 | Velvet 的 `mut` 是「回傳 tuple 的語法糖」，只多檢查 alias | `Syntax.lean:330-337`（tuple）、`:215`（`mutable arguments cannot alias`） |
| §2.4 | Velvet **沒有**分離邏輯／所有權，因此計數器可被複製 | ★ 實測作弊通過，見 `Cheats/Unresolved_FakeCounter.lean` |
| §2.5 | `Array.toMultiset` 對任意 α 可用，不需 `DecidableEq` | `Std.lean:103`：`def Array.toMultiset (arr : Array α) := Multiset.ofList arr.toList`（零 typeclass） |
| §4.3 Q1 | `method` 能吃 `structure` 型別參數 | `probe/P1.lean`，連 `mut` 都可以 |
| §4.3 Q2 | `method` 參數可以多型 | `probe/P2.lean`（顯式 `(α : Type)`）、`probe/P3.lean`（auto-bound + `variable`） |
| §4.3 Q3 | `set_option loom.semantics.termination` 是 **section 層級** | `Total_Partial_example.lean` 的三個 `section … end` |
| §6.6 | `private mk` 讓模組外「寫不出來」 | 三種路徑全被擋，逐字錯誤見 `Opt00_Recon.md` |
| §6.11 | total correctness 要寫三份 body，且 `by rfl` 要求定義相等 | `Total_Partial_example.lean` 逐字確認 |

### §6.6 的三個逐字錯誤訊息（跨模組偽造 `Ticks`）

```
Priv/B.lean:3:21: error(lean.unknownIdentifier): Unknown constant `Ticks.mk`
Priv/C.lean:3:34: error: Invalid `⟨...⟩` notation: Constructor for `Ticks` is marked as private
Priv/C.lean:4:34: error: invalid {...} notation, constructor for `Ticks` is marked as private
Priv/C.lean:5:34: error: invalid {...} notation, constructor for `Ticks` is marked as private
```
（`C.lean` 的三行分別是 `⟨0⟩`、`{ val := 0 }`、`{ t with val := 0 }`）

---

## §G 第 06 次：`private mk` 殺的不是指引預期的那一支（v2 §1.3／§5.1.1／§5.1.6）

**這一條與前面六類不同**：不是措辭或 API 細節，是一個**實質的技術判斷需要修正**。

### G.1 指引的主張

- v2 §1.3「還活著的作弊」表：`ResetToOld`（老實計費，最後 `ticks := ticksOld`）→ **預定死於第 06 次**
- v2 §5.1.1：`ensures ticksOld ≤ ticks`「**從來不是在擋歸零**，它擋的是『減到起點以下』」
- v2 §5.1.6：第 06 次「買到 kill 表第一列型別錯誤」，「買不到複製」

### G.2 實測

| | 歸到**起點以下**（`ticks := 0`） | 歸到**起點**（`ticks := t_in`） |
|---|---|---|
| `Nat`，無守衛 | ✅ 通過 | ✅ 通過 |
| `Nat` + `ensures ticksOld ≤ ticks` | ❌ `⊢ ticksOld ≤ 0` | ✅ 通過 |
| 抽象 `Ticks` | ❌ **型別錯誤** ×4 | ✅ 通過（完整插入排序，12 秒） |

證據：`Cheats/Opt06_Cheat_ForgeZero.lean`（上兩列）、
`Cheats/Unresolved_ResetToOld.lean`（下一列 + 全表）。

### G.3 修正

1. **`ResetToOld` 不死於第 06 次。** 它不需要**造**一個 `Ticks`，只需要**複製**一個：
   `let t_in := ticks; …; ticks := t_in`。而 §5.1.6 自己就寫了「買不到複製」——
   指引沒有注意到 **`ResetToOld` 本身就是一個複製**。

2. **§5.1.1 的措辭要反過來。** `ensures ticksOld ≤ ticks` 確實擋得住「歸零」
   （在 `ticksOld ≠ 0` 時，歸零就是減到起點以下）。它擋不住的是「歸到**起點**」。
   而抽象 `Ticks` 擋住的集合**與它一模一樣**：

   > 抽象 `Ticks` ≡ `ensures ticksOld.val ≤ ticks.val`

3. **第 06 次仍然有一列型別錯誤的 kill**，但那一支是新的：
   `ForgeZero`（「無視呼叫端的起點，直接報 0」）。它在第 05 次是綠的。

4. **`ResetToOld` 與第 09 次的 `FakeCounter` 是同一支作弊的兩種穿法**
   （複製後放回去 / 複製後拿去記帳）。
   ⇒ **面 2 的缺口從第 06 次就在了，不是第 09 次才出現。**

### G.4 §5.1.5 的自動化預期也可以放寬

指引預期 `Ticks` 會逼出全域 `@[grind]`（R15 預算表 + 全量 rebuild）。
實測有第三條路：**`attribute [local grind] Ticks.val_bump`**。
`local` 不外洩給 importer，從結構上消掉第 04 次 `tick_step` 那一類事故。
⇒ 依 P1 這算 local，R15 不觸發。建議把它寫成 07/08 的預設做法。

### G.5 一個指引沒提、但一定會踩到的坑

`VelvetM.extract` 需要 `[Inhabited α]`，α 是整個回傳 tuple。
所以 `#eval (sortWithTicks …).extract` 會要求 `Inhabited Ticks`——
**那正是 §5.1.3 禁止清單的第一條**。

不知道的話，很容易為了讓 `#eval` 跑起來而 `deriving Inhabited`，**M1 就靜默失效了**。
正解是先在 `VelvetM` 裡 map 成 `Nat` 再 `.extract`：

```lean
#eval (do let r ← sortWithTicks … ; pure r.2.2.val : VelvetM Nat).extract
```

建議把這一段加進 §5.1.3 的禁止清單旁邊，因為它是那條禁令**最可能的真實觸發路徑**。
