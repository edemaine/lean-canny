import Lake

open Lake DSL

package lean_canny where
  version := v!"0.1.0"
  leanOptions := #[⟨`relaxedAutoImplicit, false⟩, ⟨`maxHeartbeats, 2000000⟩]

require «cslib-frontier» from git
  "https://github.com/cslib-community/cslib-frontier" @
  "1a0acf760168bfc0eb306bfc4da5b6cece7dc479"

-- Pin the foundation's common CSLib/Mathlib versions.
require cslib from git
  "https://github.com/leanprover/cslib" @
  "ee99dd30bd1a9f466c25a51b39a5cb0bfe4d2342"

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

-- Counting-hierarchy constructions are developed separately from the PSPACE endpoint.
lean_lib LeanCannyCountingHierarchy where
  roots := #[`LeanCanny.CountingHierarchy]

-- Neutral entry point for the unified real-algebraic complexity abstract.
lean_lib RealCountingHierarchy
