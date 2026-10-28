import Lake
open Lake DSL

-- Velvet V2（上游 lean-4.35 分支的固定 commit，Lean v4.35.0）。
-- V1（Loom 架構）時期的工作保留在 v1/* 分支，
-- 兩者語法不相容。
require velvet from git "https://github.com/verse-lab/velvet.git" @ "10744dcf1902aa29000ed4ae2b7a938376a9485b"

package LeanPulse where
  -- 同一 Lean toolchain 的專案共用編譯快取；依賴原始碼仍由各自的 manifest 鎖定。
  enableArtifactCache := true
  leanOptions := #[⟨`pp.unicode.fun, true⟩]

-- 根模組是 PoP.lean；PoP/ 底下的新模組在 PoP.lean 裡 import 才會進建置
@[default_target]
lean_lib PoP
