# 第 05.5 次 Notes — rubric 層組合性

**檔案**：`Opt05b_Composition.lean`
**性質**：補驗，不防作弊
**time-box**：1 個工作段（實際用掉不到半段）
**結局**：§4.5 的第一種——**用做法 (a) 過了，不需要動 spec**

---

## 1. 這一步在補什麼

第 05 次的 `sortTwiceRel` 證的是「**method** 的界限疊得起來」。它走的是
`insertionSortRel_correct`，那條定理有**四**條 `ensures`，其中第一條是
`arr.size = arrOld.size`。

但 rubric 賣給使用者的是 `ArraySort.spec`，只有**三**項。橋接
（`insertionSortRelImpl.spec`）把四條收成三項時丟掉的，正好就是 size。
而第二次呼叫的界限是 `f a₁.size`——**需要 size**。

所以「界限可組合」這個保證在 rubric 層是懸空的。這一步把它補實。

## 2. 缺口的機械形式

不是「難證」，是 `omega` 看到兩個不同的原子：

```
 c := ↑(f a.size)
 e := ↑(f y.2.1.size)
```

這行訊息已釘進 build（`Opt05b_Composition.lean` §5 控制組 (b)）。
**缺的不是算術能力，是「兩個 `f` 的引數相等」這個事實。**

## 3. 三條做法的實測結果

| 做法 | 指引評價 | 實測 |
|---|---|---|
| **(a) local 引理 `SameElements.size_eq`** | 推薦 | ✅ **2 行**，`congrArg Multiset.card` + `simpa`。零 typeclass 需求 |
| (b) 把 size 加進 `SortSpec` | ✗ | **不必動用** |
| (c) 加進 `ArraySort.spec` | ✗ 最壞 | **不必動用** |

依 P1，`SameElements.size_eq` **不掛全域 `@[grind]`**，用到的地方就地帶入。
因此 `AttributeBudget.md` 不需要為這一步加列（R15 不觸發）。

## 4. 證明骨架

只用了 Loom 的兩條結構規則，各一次：

| 規則 | 出處 | 用途 |
|---|---|---|
| `triple_bind` | `Loom/MonadAlgebras/WP/Basic.lean:63` | 兩次呼叫接續，cut 取第一次的後條件 |
| `triple_cons` | 同檔 `:54` | 第二次呼叫：前條件 `True` 弱化、後條件轉寫 |

`triple_cons` 已經是第 02/03/04/05 次橋接用的同一條規則，這裡是第五次派上用場。
**這條規則指引從頭到尾沒提過**（已記入 `Opt00_GUIDE_ERRATA.md`）。

一個實作細節：`triple pre c post` 在 Prop lattice 上就是 `pre → wp c post`，
所以第二次呼叫可以直接 `intro y hcut` 把第一次的結論拿到手上再套 `triple_cons`。
不需要額外的 frame rule。

## 5. R12 控制組（兩組，方向相反）

結論是**肯定**的，所以控制組要證的不是「否定結論可信」，而是
「卡住的地方真的是 size，不是 `triple` 的接續本身」。

| 控制組 | 內容 | 結果 |
|---|---|---|
| **(a)** | `f` 取常數 ⇒ 兩個 `f _` beta-reduce 成同一項 | ✅ 通過。**證明骨架一字未改，只少了 `hsz` 那一行** |
| **(b)** | 拿掉 `hsz`，`f` 保持一般 | ✗ `omega` 失敗，訊息已釘住 |

兩組並排 ⇒ 骨架是好的，缺的只有 size 連結。這排除了「Velvet 的 `triple`
sequencing 本身有問題」（§4.5 的第三種結局，本來會是第三個上游發現）。

外加一組**機械反證**：把去掉 size 之後剩下的算術抽成純命題，
給反例 `f = id, a.size = 0, a₁.size = 5`。
⇒ 那個步驟**不是難證，是假的**。

## 6. 買到什麼、沒買到什麼

**買到**
- 「界限可組合」從 method 層升到 rubric 層。第 10 次的保證強度表那一列不必再附註「只在 method 層驗過」
- 一條會跟著三次型別遷移（06/07/08）走的引理，但引理本身的證明不會變

**沒買到**
- 任何防作弊能力。作弊者一樣能用假排序滿足這個組合定理——它是從 `S.spec` 推出來的，`S` 是誰不影響
- n 次組合。只做了兩次。n 次要 induction，cut 換成 `t + n * f a.size` 即可，沒做是 time-box

## 7. 回頭看第 02 次的一個決定

第 02 次決定 `SortSpec` 只講兩件事，不含 `arr.size = arrOld.size`，
理由是「不把 proof-friendly 的冗餘塞進 top-level spec」。

這一步證明那個決定是對的：**丟掉的資訊沒有真的丟掉**，
它蘊含在 `SameElements` 裡，取出來只要兩行。

> 規格該講的是「什麼是對的」，不是「怎麼證比較方便」。

## 8. 對後續步驟的影響

R13（型別遷移閘）現在多一個要遷移的對象：`Opt05b_Composition.lean` 的
兩條定理在 06/07/08 各要改一次形狀。

- **06**（`Nat → Ticks`）：`hty`／`ht` 的算術要改談 `.val`；`omega` 之前要先 `simp only [Ticks.val_bump]`（或根本不需要，因為這裡沒有 `bump`）
- **07**（多收 `iord`）：兩條定理多量化一個 `iord`，證明本體不變
- **08**（抽象 α）：`SameElements.size_eq` 要改成對抽象 α——`Array.toMultiset` 零 typeclass 需求，所以**預期照抄即可**。這是 §5.3.5 那個「`Array.toMultiset` 對抽象 α 是否可用」風險的一個早期正面訊號

## 9. R14 — kill 表單調性證據

`lake build SortRubric` 會編譯 `Cheats/` 底下**全部** 12 個檔案，
而每一支作弊的失敗宣稱都是用 `#guard_msgs` 釘住的逐字訊息或機械反證。
所以「某支作弊復活」＝「釘住的失敗訊息不再出現」＝ **build 紅燈**。
kill 表的單調性因此是 build 的一部分，不是人工核對。

本步結束的實測：

```
$ bash SortRubric/check_build.sh --with-selftest
########## [0/3] 守衛自己的負向測試 ##########   ✓
########## [1/3] import 隔離 ##########          ✓
########## [2/3] lake build SortRubric ##########  ✓ SortRubric 綠（1200 jobs）
########## [3/3] 完整 lake build，比對既有環境債 ##########
✓ 失敗集合與 baseline 逐字相同（既有環境債，非本次造成）
========== 全部通過 ==========
```

死者名單與第 05 次相同（`ZeroFill`、刪元素、只留最小值、恆等、`ExtraPrecondition`、
bogosort、`LaunderPrecondition`），**沒有增長也沒有縮減**——這一步本來就不防作弊。

## 10. R13 — 型別遷移閘

本步**沒有動 `ArraySort` 的形狀**，所以 R13 不觸發。
但它替 06/07/08 各增加了一個遷移對象，已列在 §8。
