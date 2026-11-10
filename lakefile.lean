import Lake

open Lake DSL

package lean_canny where
  version := v!"0.1.0"
  leanOptions := #[⟨`relaxedAutoImplicit, false⟩, ⟨`maxHeartbeats, 2000000⟩]

require «cslib-frontier» from git
  "https://github.com/cslib-community/cslib-frontier" @
  "834a718bac09af5d720eafbd40974c6ecdc3f121"

-- Pin the foundation's common CSLib/Mathlib versions.
require cslib from git
  "https://github.com/leanprover/cslib" @
  "bbd24fa3168878912552ee490c57775f5013e52d"

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
