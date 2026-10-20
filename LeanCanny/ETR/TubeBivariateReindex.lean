/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeBivariateSpace

/-! # Reusing tube readers with new contexts and selected exponents -/

@[expose] public section

namespace LeanCanny.ETR.TubeBivariate
open Complexity LeanCanny.Encoding LeanCanny.Computation

def directionInput (f : List Bool → List Bool) (q : List Bool) : List Bool := pair (f (pairFst q)) (pairSnd q)

theorem directionInput_mem_FP {f : List Bool → List Bool} (hf : f ∈ FP) : directionInput f ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP hf) pairSnd_mem_FP

noncomputable def Data.reindex {source active modulus inner outer : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : Data source active modulus inner outer n d ell) (f : List Bool → List Bool) (hf : f ∈ FP) :
    Data (source ∘ f) (active ∘ f) (modulus ∘ f) (inner ∘ f) (outer ∘ f)
      (fun q => n (f q)) (fun q => d (f q)) (fun q => ell (f q)) where
  coordinates := D.coordinates.precomposeUniform f hf
  bounds := D.bounds.precomposeUniform f hf
  direction := D.direction ∘ directionInput f
  sourceFP := mem_FP_comp hf D.sourceFP
  activeFP := mem_FP_comp hf D.activeFP
  modulusFP := mem_FP_comp hf D.modulusFP
  innerFP := mem_FP_comp hf D.innerFP
  outerFP := mem_FP_comp hf D.outerFP
  directionFP := mem_FP_comp (directionInput_mem_FP hf) D.directionFP
  direction_eq q i hi := by
    simp only [Function.comp_apply, directionInput, pairFst_pair, pairSnd_pair]
    exact D.direction_eq (f q) i hi

noncomputable def Data.reselect {source active modulus inner outer : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : Data source active modulus inner outer n d ell) (i o : List Bool → List Bool) (hi : i ∈ FP) (ho : o ∈ FP) :
    Data source active modulus i o n d ell where
  coordinates := D.coordinates
  bounds := D.bounds
  direction := D.direction
  sourceFP := D.sourceFP
  activeFP := D.activeFP
  modulusFP := D.modulusFP
  innerFP := hi
  outerFP := ho
  directionFP := D.directionFP
  direction_eq := D.direction_eq

end LeanCanny.ETR.TubeBivariate
