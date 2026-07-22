import Lake
open Lake DSL

require Velvet from git "https://github.com/verse-lab/velvet.git" @ "master"

package LeanPulse where
  leanOptions := #[⟨`pp.unicode.fun, true⟩]

@[default_target]
lean_lib LeanPulse where
  globs := #[Glob.submodules `LeanPulse]
