import Lake
open Lake DSL

package «leanqc» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]
  -- These are additional settings which do not affect the lake hash,
  -- so they can be enabled in CI and disabled locally or vice versa.
  -- Warning: Do not put any options here that actually change the olean files,
  -- or inconsistent behavior may result
  weakLeanArgs := if get_config? CI |>.isSome then
    #["-DwarningAsError=true"]
  else
    #[]
  -- Args for Lean-Copilot
  moreLinkArgs := #["-L./.lake/packages/LeanCopilot/.lake/build/lib", "-lctranslate2"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Leanqc» where

require Paperproof from git "https://github.com/Paper-Proof/paperproof.git"@"main"/"lean"

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"
require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot.git" @ "v1.0.0"
