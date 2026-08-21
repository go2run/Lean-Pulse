import VelvetExec

/--
把 `DivM` 的結果攤平成 `IO`。

`DivM.div` 代表「可能不終止」：在 partial correctness 語意下這是合法結果，
所以抽取出來的程式一定要處理它，不能假裝不存在。
-/
def runDiv [Inhabited α] (name : String) : DivM α → IO α
  | .res x => pure x
  | .div   => throw <| IO.userError s!"{name}: diverged"

def main (args : List String) : IO Unit := do
  let nums := args.filterMap (·.toInt?)
  let arr := if nums.isEmpty then #[1, 2, 3, 4] else nums.toArray

  -- 無 mut 參數：`MaximumExec : Int → Int → DivM Int`
  let m ← runDiv "Maximum" (MaximumExec 3 7)
  IO.println s!"Maximum 3 7 = {m}"

  -- 有 mut 參數：`DoubleAllExec : Array Int → DivM (Unit × Array Int)`
  -- 回傳是 (原本的回傳值, 被改動後的 mut 參數)
  let (_, doubled) ← runDiv "DoubleAll" (DoubleAllExec arr)
  IO.println s!"DoubleAll {arr} = {doubled}"

  -- tester：把 ensures 當 runtime assertion 跑
  IO.println s!"DoubleAllTester {arr} = {DoubleAllTester arr}"
