import Lake
open Lake DSL

-- Velvet V1（Loom 架構，Lean v4.24.0）。上游已刪除 master 並改寫成 V2（tag v2.0，
-- Lean v4.34.0，語法不相容），所以固定在 V1 的最後一個 commit。
require Velvet from git "https://github.com/verse-lab/velvet.git" @ "d254391d5e84546f96576e5b67dfb6bafe9fc301"

package LeanPulse where
  leanOptions := #[⟨`pp.unicode.fun, true⟩]

-- LeetCode 917：純 Lean 4 解法與完整證明（不依賴 Velvet）
@[default_target]
lean_lib LeanLC917

-- 同一題的 Velvet 雙指標版，規格引用 LeanLC917 當參考實作
@[default_target]
lean_lib VelvetLC917
