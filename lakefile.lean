import Lake
open Lake DSL

package «groups-in-lean» where
  -- add any package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.3.0"
require Paperproof from git
  "https://github.com/Paper-Proof/paperproof.git"@"main"/"lean"

@[default_target]
lean_lib «GroupsInLean» where
  -- add any library configuration options here
