/-!
# LeetCode 917 — Reverse Only Letters（Lean 4 版）

> 字母（A–Z / a–z）整體反轉，非字母留在原位。
> `"Test1ng-Leet=code-Q!"` → `"Qedo1ct-eeLg=ntse-T!"`

純函數解法 + 完整正確性證明。刻意不依賴任何套件（連 Velvet 和 mathlib 都不用），
所以這一檔可以單獨拿去用。

`VelvetLC917.lean` 是同一題的命令式（雙指標）版本，並用這裡的 `revOnly`
當規格——那一邊的結論是 `loom_solve` 證不出來，原因記在該檔案裡。

## 為什麼換成前向掃描就好證

雙指標從兩端往中間夾，中途陣列處於「兩端已交換、中間還沒動」的混合狀態，
要把它和「字母序列被反轉」這種**全域**性質接起來，得寫三段式的不變式。

改成「先把字母抽出來反轉，再一次前向掃描織回原位」之後，
遞迴結構和歸納結構對齊，兩次 `induction` 就做完了。
-/

def isLetter (c : Char) : Bool := c.isAlpha

/-- 把 `ls` 依序填回 `s` 中每個字母的位置，非字母原封不動地留下。 -/
def weave : List Char → List Char → List Char
  | [], _ => []
  | c :: cs, ls =>
      if isLetter c then ls.headD c :: weave cs ls.tail
      else c :: weave cs ls

/-- 解法：把字母抽出來、反轉、再織回原位。 -/
def revOnly (s : List Char) : List Char :=
  weave s ((s.filter isLetter).reverse)

def reverseOnlyLetters (s : String) : String := String.mk (revOnly s.toList)

#guard reverseOnlyLetters "ab-cd" = "dc-ba"
#guard reverseOnlyLetters "a-bC-dEf-ghIj" = "j-Ih-gfE-dCba"
#guard reverseOnlyLetters "Test1ng-Leet=code-Q!" = "Qedo1ct-eeLg=ntse-T!"
#guard reverseOnlyLetters "abc-d" = "dcb-a"

/-! ## 正確性

三條性質**合起來唯一決定答案**（不是弱規格）：長度相同 ⇒ 非字母位置逐格相同
⇒ 那些位置在結果裡也是非字母 ⇒ 剩下的位置恰好放得下 `filter` 出來的那些字母，
而順序由第三條釘死。 -/

@[simp] theorem weave_length (s ls : List Char) : (weave s ls).length = s.length := by
  induction s generalizing ls with
  | nil => rfl
  | cons c cs ih => by_cases h : isLetter c <;> simp [weave, h, ih]

/-- 非字母的位置原封不動。 -/
theorem weave_getElem?_of_not_letter (s ls : List Char) (i : Nat) (c : Char)
    (hc : s[i]? = some c) (h : isLetter c = false) : (weave s ls)[i]? = some c := by
  induction s generalizing ls i with
  | nil => simp at hc
  | cons d ds ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      simp [weave, h]
    | succ n =>
      simp only [List.getElem?_cons_succ] at hc
      by_cases hd : isLetter d <;> simp [weave, hd] <;> exact ih _ _ hc

/-- 字母位置依序被填上 `ls`——前提是 `ls` 全是字母、且個數對得上。 -/
theorem weave_filter (s ls : List Char) (hlen : (s.filter isLetter).length = ls.length)
    (hall : ∀ c ∈ ls, isLetter c) : (weave s ls).filter isLetter = ls := by
  induction s generalizing ls with
  | nil => cases ls <;> simp_all [weave]
  | cons c cs ih =>
    by_cases h : isLetter c
    · cases ls with
      | nil => simp [h] at hlen
      | cons l ls' =>
        have hl : isLetter l := hall l (by simp)
        have hlen' : (cs.filter isLetter).length = ls'.length := by
          simpa [h] using hlen
        have hall' : ∀ x ∈ ls', isLetter x := fun x hx => hall x (by simp [hx])
        simp [weave, h, hl, ih ls' hlen' hall']
    · simpa [weave, h] using ih ls (by simpa [h] using hlen) hall

/-- 規則 0：長度不變。 -/
theorem revOnly_length (s : List Char) : (revOnly s).length = s.length := by
  simp [revOnly]

/-- 規則 1：非字母留在原位。 -/
theorem revOnly_nonletter (s : List Char) (i : Nat) (c : Char)
    (hc : s[i]? = some c) (h : isLetter c = false) : (revOnly s)[i]? = some c :=
  weave_getElem?_of_not_letter _ _ _ _ hc h

/-- 規則 2：字母整體反轉。 -/
theorem revOnly_filter (s : List Char) :
    (revOnly s).filter isLetter = (s.filter isLetter).reverse := by
  refine weave_filter s _ (by simp) ?_
  intro c hc
  exact (List.mem_filter.mp (List.mem_reverse.mp hc)).2
