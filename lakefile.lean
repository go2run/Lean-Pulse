import Lake
open Lake DSL

-- Velvet V1（Loom 架構，Lean v4.24.0）。上游已刪除 master 並改寫成 V2（tag v2.0，
-- Lean v4.34.0，語法不相容），所以固定在 V1 的最後一個 commit。
require Velvet from git "https://github.com/verse-lab/velvet.git" @ "d254391d5e84546f96576e5b67dfb6bafe9fc301"

package LeanPulse where
  leanOptions := #[⟨`pp.unicode.fun, true⟩]

-- 排序 rubric 分階段強化：十次優化（Opt01–Opt10 + 選配 Opt11）
@[default_target]
lean_lib SortRubric where
  globs := #[Glob.submodules `SortRubric]
