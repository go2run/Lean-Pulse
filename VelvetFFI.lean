import VelvetExec

/-- 用 `@[export]` 把抽取出來的程式暴露成 C 符號。
`UInt64` 在 Lean 的編譯器裡是 unboxed scalar，所以 C 端看到的簽名就是
`uint64_t velvet_maximum(uint64_t, uint64_t)`。 -/
@[export velvet_maximum]
def velvetMaximum (a b : UInt64) : UInt64 :=
  match MaximumExec (a.toNat : Int) (b.toNat : Int) with
  | .res r => r.toNat.toUInt64
  | .div   => 0
