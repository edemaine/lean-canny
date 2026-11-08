import Lake

open Lake DSL

package lean_canny where
  version := v!"0.1.0"
  leanOptions := #[⟨`relaxedAutoImplicit, false⟩, ⟨`maxHeartbeats, 2000000⟩]

require complexitylib from git
  "https://github.com/cslib-community/complexitylib" @
  "393e2b13778f7ef37d173b9bbbccbf264a31450a"

-- Pin the foundation's common CSLib/Mathlib versions.
require cslib from git
  "https://github.com/leanprover/cslib" @
  "254e30e6d4299c51323aaeaf5f51a4763b375d4a"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @
  "69552756cd8a2d2d48763cf7279fd814d6a1224d"

@[default_target]
lean_lib LeanCanny

-- Optional constructions are retained without entering the default proof closure.
lean_lib LeanCannyAlternatives where
  roots := #[`LeanCanny.Alternatives]

-- Native PSPACE bounds for the original point and whole-space connectivity languages.
lean_lib LeanCannyConnectivity where
  roots := #[`LeanCanny.Connectivity]
