import Lake
open Lake DSL

require Velvet from git "https://github.com/verse-lab/velvet.git" @ "master"

package LeanPulse where
  leanOptions := #[⟨`pp.unicode.fun, true⟩]

@[default_target]
lean_lib LeanPulse where
  globs := #[Glob.submodules `LeanPulse]

-- 對應 doc/VelvetTutorial.md 的六節範例，單檔自成一個 lib
@[default_target]
lean_lib VelvetTutorial

-- LeetCode 917：純 Lean 4 解法與完整證明（不依賴 Velvet）
@[default_target]
lean_lib LeanLC917

-- 同一題的 Velvet 雙指標版，規格引用 LeanLC917 當參考實作
@[default_target]
lean_lib VelvetLC917
