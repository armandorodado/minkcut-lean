import Lake
open Lake DSL

package minkcut where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib MinKCut where
  globs := #[.submodules `MinKCut, .one `MinKCut]
