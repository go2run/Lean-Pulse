import Lake
open Lake DSL

-- Velvet V1（Loom 架構，Lean v4.24.0）。上游已刪除 master 並改寫成 V2（tag v2.0，
-- Lean v4.34.0，語法不相容），所以固定在 V1 的最後一個 commit。
require Velvet from git "https://github.com/verse-lab/velvet.git" @ "d254391d5e84546f96576e5b67dfb6bafe9fc301"

package LeanPulse where
  leanOptions := #[⟨`pp.unicode.fun, true⟩]

-- 對應 doc/VelvetTutorial.md 的六節範例，單檔自成一個 lib
@[default_target]
lean_lib VelvetTutorial

-- 對應 doc/VelvetExec.md：抽取可執行程式 + 編譯成原生執行檔
@[default_target]
lean_lib VelvetExec

lean_exe velvet_demo where
  root := `Main

-- 對應 doc/VelvetExec.md §8：用 @[export] 把抽取出來的程式暴露成 C 符號
-- 產出由 ffi/build.sh 連結（C 執行檔 + 共享函式庫）
lean_lib VelvetFFI
