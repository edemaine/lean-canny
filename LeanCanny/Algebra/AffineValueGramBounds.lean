/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.AffineValueGramSpace

/-! # Parameter-degree bounds for native affine value certificates -/

@[expose] public section
namespace LeanCanny.Algebra.AffineValueGramBits
open LeanCanny.Encoding
open scoped Classical

theorem Family.parameter_degree_le (F : Family) (B : List Bool → ℕ)
    (hb : ∀ c i u, ((F.original c i).coeff u).natDegree ≤ B c) (c : List Bool) (k : ℕ) :
    ((F.homogeneous.annihilator c).coeff k).natDegree ≤
      ProjectiveValueGram.dimension (F.arity c) (F.width c) * B c := by
  have hh := F.homogeneous_inner_bound B hb c
  apply ProjectiveValueGram.annihilator_inner_degree
    (F.homogeneous.rows c) (F.homogeneous.test c) (fun i => F.degree c i.val) (F.testDegree c) (F.width c) (B c)
  · intro i e
    exact hh i.succ e
  · intro e
    exact hh ⟨0, F.homogeneous.positive c⟩ e

end LeanCanny.Algebra.AffineValueGramBits
