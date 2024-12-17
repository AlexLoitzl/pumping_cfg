import Lake
open Lake DSL

package «pumping_cfg» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require "leanprover-community" / "mathlib" @ git "alex-loitzl-cnf"

@[default_target]
lean_lib PumpingCfg where
  globs := #[.submodules `PumpingCfg]
