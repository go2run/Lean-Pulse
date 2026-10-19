import Lake
open Lake DSL

-- Velvet V2（tag v2.0，Lean v4.34.0）。V1（Loom 架構）時期的工作保留在 v1/* 分支，
-- 兩者語法不相容。
require velvet from git "https://github.com/verse-lab/velvet.git" @ "v2.0"

package LeanPulse where
  leanOptions := #[⟨`pp.unicode.fun, true⟩]

-- 根模組是 PoP.lean；PoP/ 底下的新模組在 PoP.lean 裡 import 才會進建置
@[default_target]
lean_lib PoP
