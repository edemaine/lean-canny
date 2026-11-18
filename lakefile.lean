import Lake

open Lake DSL

package lean_canny where
  version := v!"0.1.0"
  leanOptions := #[⟨`relaxedAutoImplicit, false⟩, ⟨`maxHeartbeats, 2000000⟩]

require «cslib-frontier» from git
  "https://github.com/cslib-community/cslib-frontier" @
  "6a504006935b57c5a45cc64fdf597ec883724ea5"

-- Pin the foundation's common CSLib/Mathlib versions.
require cslib from git
  "https://github.com/leanprover/cslib" @
  "98f9a62ac1fafa0d5091bbd78bc24091c5923aab"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @
  "bbff2954fe5ee3b7a4b33cc26ef873a1c3277d91"

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
