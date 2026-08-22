# SortRubric — 用十次優化把「看起來像排序」逼成「只有真排序才滿足」

> ### ⚠ 關於本專案的 build 狀態
> **本專案的基準 `lake build` 在 commit `69e292a` 即為紅燈（`VelvetLC917` 三個錯誤），與 `SortRubric/` 無關。**
> 該紅燈早於本資料夾存在，`SortRubric/` 的 import 閉包**不含**任何專案根目錄模組（機械證明見
> [`check_isolation.sh`](check_isolation.sh)）。
>
> 驗收請跑：`bash SortRubric/check_build.sh`
> 它同時檢查 ① import 隔離（含 `Cheats/` 圍堵）② `lake build SortRubric` 全綠 ③ 完整 build 的失敗集合與
> [`baseline_errors.txt`](baseline_errors.txt) **逐字相同**（多一個新錯誤就算該步未完成）。
>
> 加 `--with-selftest` 會先跑守衛自己的負向測試（**每一步都該跑**——守衛腳本本身也會被改）。

---

## 這個資料夾在做什麼

成本規格（複雜度）天生只能寫**上界**：

```
ticks ≤ ticksOld + f n
```

而 `ticks` 停在原地一定滿足這個式子。所以「**少計**」永遠是安全的作弊方向，
而且你**沒辦法**把它改寫成「`ticks` 等於真實比較次數」——「真實比較次數」不在 Lean 的語意裡。

**結論：不要試圖補強那句後條件。要把逃逸路徑用型別封死。**

十次優化，每一次都必須回答同一個問題：
**這一次堵住了哪一個作弊？哪一個作弊還活著？**

---

## ★ 目前最強的一句話：分身計數器撐過了全部十次優化

一支**貨真價實的插入排序**，做滿 O(n²) 次比較，每一次都記到區域變數 `fake`，
真計數器 `ticks` 從頭到尾一動不動——它**通過**了 `Sorted ∧ SameElements ∧ ticks ≤ ticksOld + n²`。

```lean
let mut fake := ticks              -- 一行，複製一份計數器
...
        invariant ticks = ticksOld  -- ★ 迴圈的證明機制主動認證「計數器全程沒動」
        do
          fake := fake + 1          -- 所有計費流向分身
```

機械可檢的證據（`#guard_msgs` 釘進 build）：

| 輸入 | `(observed, arr, ticks)` | 讀法 |
|---|---|---|
| `#[8,2,5,3]`, ticks=0 | `(6, #[2,3,5,8], 0)` | 6 = 4·3/2 次比較，排好了，**ticks 沒動** |
| n=8 逆序, ticks=0 | `(28, sorted, 0)` | 28 = 8·7/2，**ticks 沒動** |
| n=8 逆序, ticks=**100** | `(128, sorted, **100**)` | 比較次數 +28，**ticks 一字不差停在 100** |

**根因**：F\* 的 `MR.pts_to ctr #1.0R i` 是**資源**不是值，`1.0R` 分不出第二份 `1.0R`——那是線性性。
Velvet 的 `VelvetM = NonDetT DivM` 是純值上的不確定性 + 發散，沒有 heap、沒有分離邏輯、沒有所有權。

**「加一條下界」救不了**（也已機械化，見 [`Cheats/Unresolved_FakeCounterPadded.lean`](Cheats/Unresolved_FakeCounterPadded.lean)）：
實作只要對真計數器做 `n−1` 次無意義的比較湊數即可。加了下界之後，
計數器報出 `n−1`——**線性**——而 Θ(n) 的比較排序在資訊論上不存在。
規格不只被少報，它接受了一個**不可能的複雜度等級**。

→ 檔案：[`Cheats/Unresolved_FakeCounter.lean`](Cheats/Unresolved_FakeCounter.lean)
→ 為什麼不叫 `Opt09_Cheat_*`：**沒有任何一步淘汰得了它**，照慣例取名等於在檔名裡寫一句沒驗證過的宣稱。

### ★ 第 06 次的發現：這個洞不是第 09 次才出現的

第 06 次把計數器換成抽象型別 `Ticks`（`private mk`）之後，本來預期會殺掉
「老實計費，最後 `ticks := ticksOld`」。**實測沒有。**

```lean
let t_in := ticks            -- 複製一個值，不需要建構子
… ticks := ticks.bump …      -- 老實計費 n(n−1)/2 次
ticks := t_in                -- 把複製品放回去
```

`private mk` 管的是「**造**」，管不到「**複製**」。而這兩支作弊做的是同一件事：

| 作弊 | 動作 |
|---|---|
| `ResetToOld` | 複製 → 對本尊計費 → 把複製品放回去 |
| `FakeCounter` | 複製 → 對複製品計費 → 從不碰本尊 |

⇒ **M1（單調計數器）與 M2 面 2（計數器身分）不是兩個問題，是同一個問題。**

最尖銳的形式：`Unresolved_ResetToOld.lean` 裡那支作弊**住得進
`ArraySort (fun _ => 0)`**——第 06 次的 rubric 承認一支「零次比較的比較排序」。

→ 檔案：[`Cheats/Unresolved_ResetToOld.lean`](Cheats/Unresolved_ResetToOld.lean)
→ 指引勘誤：[`Opt00_GUIDE_ERRATA.md`](Opt00_GUIDE_ERRATA.md) §G

---

## 十步總表

| 第 N 次 | 檔案 | 加上什麼 | 之前通得過的作弊 | 狀態 | 風險 |
|---|---|---|---|---|---|
| 00 | `Opt00_Recon.md` | 環境勘查 | — | ✅ 完成 | — |
| 01 | `Opt01_Sorted` | `Sorted` | — | ✅ | 低 |
| 02 | `Opt02_SameElements` | `+ SameElements` | 全填 0、刪元素、只留最小值 | ✅ | 低 |
| 03 | `Opt03_Interface` | 統一成 interface | 各寫各的簽章與前條件 | ⚠ | 中 |
| 04 | `Opt04_TicksAbsolute` | `ticks ≤ f n`；`f` 升格成 rubric 參數 | bogosort；一種複雜度一份規格 | ✅ | 低 |
| 05 | `Opt05_TicksRelative` | 改成 `ticks ≤ ticksOld + f n` | **（不防作弊）** 遞迴界限疊不起來 | ✅ | 低 |
| 05.5 | `Opt05b_Composition` | rubric 層（非 method 層）的界限可組合 | **（不防作弊）** 補驗，非新的一刀 | ✅ | 低 |
| 06 | `Opt06_MonotonicTicks` | M1 抽象 `Ticks`（`private mk`） | 無視呼叫端起點，直接報 0 | ✅ | 中 |
| 07 | `Opt07_InstrOrder` | M2 面 1：比較器必計費、不說謊 | 不計費／亂回答的比較器 | ⬜ | 中 |
| 08 | `Opt08_AbstractElem` | M2 面 3：`SpecOrder`(Prop) + 抽象 α | 用 `Int` 直接 `x < y` 繞過比較器 | ⬜ | **高** |
| 09 | `Opt09_SortM` | M2 面 2：計數器身分 | `let mut fake := ticks` 分身 | ⬜ | **必要，且已知受限**※ |
| 10 | `Opt10_Audit` | D 軸：`#print axioms` + SPOTs | `sorry` 掉整個 spec | ⬜ | 低 |
| 11 | `Opt11_Termination`（選配） | total correctness | `while true do skip` | ⬜ | 高（三倍抄寫） |

**兩個要特別標記的格子：**

- **第 05 次是唯一「不防作弊」的一步。** 它防的是「不可用」（遞迴的界限疊不起來），不是「不誠實」。
- **※ 第 09 次的地位已改變。** 原本標「實驗性，可能失敗」；勘查實測後改為 **必要**——
  因為作弊已確認成立。但同時已知 `method` 把回傳型別**寫死成 `VelvetM`**
  （`Velvet/Syntax.lean:343`），`SortM` 路線無法沿用 `invariant`/`decreasing`/`loom_solve`。
  因此第 09 次**改為時間盒 spike**，只回答「自動化能不能穿過 opaque monad」，
  由人決定要不要全面改寫。**負面結果是合格交付物。**

---

## `α` 的 typeclass 預算表

> **規則：要往 `α` 上加任何 typeclass，先在這張表加一列並論證，才能寫 code。**
> 這條規則已加進最終 checklist。理由：`DecidableRel` 之類的 typeclass 會讓 M2 面 3
> **靜默失效**——實作可以 `if decide (x ≤ y)` 完全繞過比較器，而且**不會有任何錯誤訊息**。

| typeclass | 為什麼需要 | 讓實作能做什麼 | 破面 3？ | 依賴 |
|---|---|---|---|---|
| `Inhabited α` | **兩層，硬的是第二層**：<br>① 語法層（軟）：`a[i]!`、`swap!` 要它 —— 換成 `a[i]'h` / `a[i]?` **可以**避開<br>② **證明層（硬）：`Array.multiset_swap [Inhabited α]`（`Velvet/Std.lean:105`）與 `Array.get_set_c [Inhabited α]`（`:77`）這兩個 `[grind]` 引理自己就要求它。**每一條 preservation invariant 都要用到，換索引寫法**繞不過去** | 生出一個 `default : α` | **否**——只能「生」，不能「觀察」 | ⚠ **有條件**：必須 `SameElements` 留在後條件裡。`default` 讓實作能生出輸入裡沒有的元素，是 multiset 相等擋住它，不是 `Inhabited` 本身無害。 |
| ~~`DecidableRel (·≤·)`~~ | — | `if decide (x ≤ y) then …` 繞過 `cmp` | **是** | 🚫 禁止 |
| ~~`DecidableEq α`~~ | — | `x = y` 分支 | **是** | 🚫 禁止 |
| ~~`FinEnum α`~~ | — | 列舉所有元素 | **是** | 🚫 禁止 |
| ~~`LE α`~~ | — | 直接寫 `x ≤ y` | **是** | 🚫 禁止 |
| ~~`Classical.dec` / `classical`~~ | — | 從 `Prop` 生 `Decidable` | **是**（且讓定義變 `noncomputable`） | 🚫 禁止；由第 10 次 `#print axioms` 稽核 |

### 能不能連 `Inhabited` 都不要？——實測過，代價高，保留

| 層 | 能否避開 `Inhabited` | 證據 |
|---|---|---|
| **規格層** | ✅ **能** | `a[i]'(by omega)`（dependent indexing）與 `a[i]?` 兩種寫法都對抽象 α 編譯通過（`probe/I1.lean`） |
| **實作層** | ❌ 實務上不能 | `swap!` 展開成 `getElem!` → `failed to synthesize Inhabited α`；改用非 bang `swap` 則 polymorphic 下的界內證明無法自動導出 |
| **證明層** | ❌ **決定性** | `Array.multiset_swap [Inhabited α]` 是每一條 preservation invariant 都要用的 `[grind]` 引理，**它自己就要求 `Inhabited`**。要拿掉就得在 Velvet 之外重證一份。 |

**結論**：代價是「重證 Velvet Std 的核心陣列引理 + 與所有官方範例分岔」，不是低成本改動。
依判準保留 `Inhabited`，並把上表那條**條件式**論證寫進 Notes。

> ⚠ **不要只看語法層。** 表上若只寫「因為 `a[i]!`」，
> 下一個人會以為換個索引寫法就能拿掉 `Inhabited`，然後撞上證明層的牆。
> **證明層才是硬的那一層。**

---

## 自動化屬性預算表（`@[grind]` / `@[simp]`）

> **正本在 [`AttributeBudget.md`](AttributeBudget.md)。** 動任何全域屬性之前先去那裡加一列（R15）。
> 這裡只留下這張表付過紅利的那一次教訓，因為它是本專案的核心方法論之一。

> ★ **第 04 次加了一條*正確無誤*的引理 `tick_step` 並標上 `@[grind]`，
> 結果 `loom_solve!` 開始在完全不相關的平凡目標上失敗**（`⊢ SameElements arrOld arrOld`，
> 那是 `rfl`）。拿掉屬性、引理不動，立刻恢復。
> **一條正確的引理也可能是一條壞的自動化提示。** 詳見 `Opt04_Notes.md` §6.1。

**目前宣告了 0 個 `@[simp]`。** 決定 (二) 的教訓：
`and_comm` 之類的 permutative lemma 一旦進 simp set 就會跟後續宣告互相干擾，
term-level 直接套用則沒有這個問題。**能用 term-level 就不要進 simp set。**

### ★ `@[grind]` 於具名 predicate：這是第 03 次能不能存在的前提

```
ensures Sorted arr 沒有 @[grind]
  → loom_solve! 卡住
  → 規格只能「就地展開」，不能引用具名 predicate
  → 沒有具名 predicate
  → 第 03 次的 interface 抽象不成立
```

這不是一條 API 差異，是一條**依賴鏈**。詳見 `Opt02_Notes.md` §7.1。

> ✅ **第 03 次已經印證這條鏈**：`SortImpl.spec` 的欄位型別是
> `∀ a, triple True (sort a) (fun r => SortSpec a r.2)`，**直接引用具名的 `SortSpec`**。
> 若第 02 次沒把 `Sorted`/`SameElements` 標成 `@[grind]`，這個欄位就只能寫成一大串就地展開的式子，
> 「審查者只讀 3 行」的賣點也就沒了。
> **這條鏈現在是已發生的事實，不是推論的前提。**

---

## 硬性規則（違反即視為未完成）

| # | 規則 |
|---|---|
| R1 | 只新建 `SortRubric/`（例外：`lakefile.lean` 末尾追加 `lean_lib SortRubric`）。不得修改 Velvet 本體。 |
| R2 | 每個檔案的檔名與檔頭都要帶「第幾次優化」的編號。 |
| R3 | `.lean` 檔名一律 ASCII。中文只出現在檔案內容與 `.md`。 |
| R4 | **（修訂）** `bash SortRubric/check_build.sh` 全過：import 隔離 + `lake build SortRubric` 綠 + 全域失敗集合與 baseline 逐字相同。 |
| **R5′** | **`sorryAx` 只允許出現在 `Cheats/` 之內**，且必須同時滿足：<br>(a) 該宣告的失敗訊息由 `#guard_msgs` 釘住<br>(b) 該宣告的 `#print axioms` 輸出由第二個 `#guard_msgs` 釘成明文<br>(c) `Cheats/` 在 import 圖上是葉節點，**且沒有任何含證明的模組 import 它——包含 lake 的聚合根模組**<br>(d) (a)(b)(c) 三者各有負向測試，且每一步都跑<br><br>`Cheats/` 之外的任何宣告，`#print axioms` 必須乾淨。<br>其餘逃生門（`native_decide` / `@[implemented_by]` / `unsafe`）**維持全面禁止**。<br><br>*(c) 的現況*：本專案**沒有**聚合根模組——`lean_lib SortRubric` 用 `Glob.submodules`，各模組獨立編譯，沒有任何檔案 import 全部。`check_isolation.sh` 每步複驗「無人 import `Cheats/`」，並附負向測試。 |
| R6 | 任何「這個作弊應該失敗」的宣稱，必須附逐字錯誤訊息（含檔名:行號）。<br>**強化**：能用 `#guard_msgs` 釘進 build 的就要釘——貼上的錯誤是一次性觀察，釘住的錯誤是會自動失效的迴歸測試。 |
| R7 | 不得為了讓證明通過而弱化規格。若必須弱化，明寫弱化了什麼、放走了哪個作弊。 |
| R8 | 同一障礙嘗試 2 次未解 → 停手，`PROGRESS.md` 寫 `BLOCKED`。 |
| R9 | 指引裡的 Lean 碼都是設計稿，以 `Opt00_Recon.md` / `Opt00_GUIDE_ERRATA.md` 的真實 API 為準。 |
| **R10** | **每一步「應該通得過／應該通不過」的宣稱，都必須有一支真的跑過 `prove_correct` 的程式，不能只有 `example`。**<br>`example : Sorted #[0,0,0,0]` 只說明**那個 `Prop` 是真的**；一支通過 `ensures Sorted a` 的 method 才說明**規格擋不住程式**。只有後者是 rubric 的失效。 |
| **R11** | **要往 `α` 上加任何 typeclass，先在 typeclass 預算表加一列並論證，才能寫 code。** |
| **R12** | **否證之前先跑控制組。**<br>當一個實驗沒有出現預期的效果時，在記下「預期不成立」之前，必須先跑一個控制組，確認**實驗裝置本身是有效的**——把被測的變因換成已知會成功／已知會失敗的版本，確認裝置給出對應的結果。<br>**沒有控制組的否定結論，一律記為 `INCONCLUSIVE`，不記為「不成立」。**<br><br>鏡像的一條同樣要遵守：**一支作弊「失敗了」，不代表它是被規格殺的**——可能是語法錯誤、`unknown identifier`、timeout 或無關的 elaboration 問題。那樣的紀錄在 kill 表裡是**假陽性**。 |
| **P1** | **自動化屬性：local 優先，全域要有理由。**<br>預設用 `grind [lemma]`（局部）。同一條引理被局部使用 ≥3 處，才考慮升級成 `@[grind]`，並在預算表記錄升級理由。 |
| **P2** | **動屬性必須全量 rebuild。**<br>新增或移除任何 `@[grind]` / `@[simp]` 之後，必須重跑**全部已完成步驟**的 build，不能只跑當前步驟。<br>*理由*：一條**正確**的引理可以讓三步前的證明失敗（第 04 次實際發生過，見 `Opt04_Notes.md` §6.1）。 |
| **R13** | **型別遷移閘。**<br>每一次改 `ArraySort` 的形狀，必須在**同一個 commit** 內把所有既有 instance、所有 `Cheats/`、所有 SPOTs 一起遷移完，且 `lake build SortRubric` 綠。<br>**不接受「先改 structure，instance 下一個 commit 補」。**<br>*理由*：中間狀態下 kill 表是無效的——舊作弊可能靜默復活而沒人看得出來。 |
| **R14** | **kill 表單調性。**<br>每一步結束要**重跑全部 `Cheats/`**，並在該步 Notes 貼出「死者名單不變或增長」的證據。任何一步讓已死的作弊復活 = **該步未完成**。<br>*理由*：第 04 次的屬性燒傷讓三步前的證明失敗。屬性與型別遷移都可能靜默地放走舊作弊。 |
| **R15** | **屬性預算表是動屬性的前置條件。**<br>新增任何全域 `@[grind]` / `@[simp]` 之前，先在 [`AttributeBudget.md`](AttributeBudget.md) 加一列（屬性名、加它是為了讓哪個目標過、風險評估）；動屬性後**全量 rebuild** 並跑 R14。<br>（這是 P1／P2 的可執行版。） |
| **R16** | **測試起點隔離。**<br>`Ticks` 的任何公開起點（`Ticks.mkForTesting`）只准出現在 `Opt10_Audit.lean` 與 `*_Tests.lean`。`Cheats/` 與所有實作檔**不得 import** 它。由 `check_isolation.sh` 的 **fail-closed** 版強制。<br>*理由*：把 `Ticks.zero` 公開等於把 `ResetToOld` 直接送回來。 |

---

## 檔案導覽

| 檔案 | 內容 |
|---|---|
| [`Opt00_Recon.md`](Opt00_Recon.md) | 環境勘查報告：真實 API 逐字摘錄、四個問題的實測答案、已知環境債 |
| [`Opt00_GUIDE_ERRATA.md`](Opt00_GUIDE_ERRATA.md) | 指引勘誤表，可併回專案端指引 |
| [`PROGRESS.md`](PROGRESS.md) | 進度表 |
| [`strip_comments.py`](strip_comments.py) | 剝掉 Lean 註解，供 `check_isolation.sh` 的 R16 段只看程式碼 |
| [`AttributeBudget.md`](AttributeBudget.md) | **全域 `@[grind]` / `@[simp]` 預算表（R15 的正本）** |
| [`UPSTREAM_REPORT.md`](UPSTREAM_REPORT.md) | 上游回報：失敗的 `prove_correct` 靜默注入 `sorry`（一種模式、兩個實例、一組控制組） |
| [`check_build.sh`](check_build.sh) | 每步驗收（R4） |
| [`check_isolation.sh`](check_isolation.sh) | import 隔離的機械證明 |
| [`baseline_errors.txt`](baseline_errors.txt) | 釘住的既有環境債簽名 |
| [`Cheats/`](Cheats/) | 作弊實作，命名規則見下 |
| [`check_selftest.sh`](check_selftest.sh) | **檢查器自己的負向測試**——確認 `check_isolation` / `check_build` 真的會拒絕違規 |

---

## `Cheats/` 的命名規則

```
Cheats/
  OptNN_Cheat_*.lean    已被第 NN 次淘汰 —— 檔名是一句「已驗證」的宣稱
  Unresolved_*.lean     目前沒有任何一步淘汰得了 —— 檔名不作宣稱
```

**規則 1**：`OptNN_Cheat_*` 的語意是「在第 NN 次**被淘汰**」，也就是它在第 NN−1 次通得過。
把這個前綴套在一支沒有任何一步殺得掉的作弊上，等於**在檔名裡寫一句沒驗證過的宣稱**——
而這正是整個專案要防的事。因此改用 `Unresolved_` 前綴。

**規則 2**：一旦某一步真的殺掉某個 `Unresolved_*`，**當場改名**成 `OptNN_Cheat_*`，
並在 commit 訊息記錄是哪一步殺的。

**於是 `ls Cheats/` 本身就是一份狀態報告**——
還剩幾個 `Unresolved_`，就是這份 rubric 還剩幾個洞。

目前狀態：

| 作弊 | 被哪一步殺 | **被規格的哪一條殺** | **失敗目標** |
|---|---|---|---|
| `Opt02_Cheat_AllZeros` | Opt02 | `SameElements` | `⊢ SameElements arrOld (Array.replicate arrOld.size 0)` |
| `Opt02_Cheat_DropElements` | Opt02 | `SameElements` | `⊢ SameElements arrOld #[]` |
| `Opt02_Cheat_MinOnly` | Opt02 | `SameElements` | `⊢ SameElements arrOld #[m_1]` |
| `Opt02_Cheat_Identity` | Opt02 | **`Sorted`** | `⊢ Sorted arrOld` ←「請證明輸入本來就排好了」 |
| `Opt03_Cheat_ExtraPrecondition` | Opt03 | `spec` 的**前條件形狀** | `Type mismatch`：`{1 ≤ arr.size}` vs `{True}` |
| `Opt03_Cheat_LaunderPrecondition` | —（測我們自己的規則） | `triple_cons` 方向性 | `⊢ True ≤ (have arr := a; 1 ≤ arr.size)` |
| `Opt05_Cheat_NoCompose` | —（示範不可用，非不誠實） | 絕對界限的隱含前條件 | `⊢ i_2 = 0` ←「第一次呼叫花掉的計數要等於 0」 |
| `Opt06_Cheat_ForgeZero` | Opt06 | ★ **型別**（`Ticks` 的 `private mk`） | `Invalid ⟨...⟩ notation: Constructor for Ticks is marked as private`（四條路徑） |
| `Unresolved_ResetToOld` | — | — | —（它**通過**，而且住得進 `ArraySort (fun _ => 0)`） |
| `Unresolved_FakeCounter` | — | — | —（它**通過**） |
| `Unresolved_FakeCounterPadded` | — | — | —（它**通過**） |
| `Upstream_Contamination{A,B,Control}` | —（上游 bug 重現 + 控制組） | — | — |

**第四欄比錯誤訊息好讀，也比錯誤訊息穩定**——訊息格式會隨版本變，goal 不會。
而且它自己說明成因：`Identity` 是四支裡唯一目標只跟**輸入**有關的，因為它根本沒產生新東西。

**第三欄的用途**：十步做完之後，
**任何一條從來沒殺過任何東西的後條件，都是空洞的嫌疑犯。**
這是 §6.10 SPOTs 的窮人版，成本只有一欄。

**這一欄第一次使用就抓到東西——但抓到的不是規格的問題，是我們自己的問題。**

原本三支作弊全是 `SameElements` 殺的、`Sorted` 零紀錄。
結論不是「`Sorted` 可疑」，而是**作弊集合有偏**：
三支全是「有序但元素錯」，沒有一支是「元素對但沒排序」。
補上 `Opt02_Cheat_Identity`（恆等函數）之後，表才成立：
**`SameElements` 3 殺、`Sorted` 1 殺，兩條都是承重的，機械證明。**

這讓這一欄從**紀錄**升級成**診斷工具**——它會主動指出你漏測了什麼。
證據就在證明的形狀裡：前三支的反證是 `rintro ⟨-, h⟩`（丟掉 `Sorted`），
`Identity` 的反證是 `rintro ⟨h, -⟩`（丟掉 `SameElements`）。

**未解狀態：還剩 1 個未解根因（2 個實例）。**
兩支 `Unresolved_*` 是同一件事——計數器可被複製；
`Padded` 只是多證明了「加下界」會讓回報值從沉默變成謊言。
第 09 次要解的是**一件事**，不是兩件。
