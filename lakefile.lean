import Lake

open Lake DSL

package lean_canny where
  version := v!"0.1.0"
  leanOptions := #[⟨`relaxedAutoImplicit, false⟩, ⟨`maxHeartbeats, 2000000⟩]

require complexitylib2 from git
  "https://github.com/SamuelSchlesinger/complexitylib2" @
  "cb1b7ce8ca0757db30ec29c8365b88d86b78c80a"

-- Pin the foundation's common CSLib/Mathlib versions.
require cslib from git
  "https://github.com/leanprover/cslib" @
  "b5f3b77d9f045ed8f2dfec05505b159c2417e1c6"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @
  "625d8914199bc567cca9b91f90e8e5afafa5ae51"

@[default_target]
lean_lib LeanCanny
