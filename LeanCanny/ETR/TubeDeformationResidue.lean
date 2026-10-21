/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeDeformationSpace

/-! # Varying-modulus access to the full tube deformation

Appending a modulus leaves all three selected exponents and the integer tube
system fixed. The complete evaluator therefore supplies residues of one integer
coefficient to the streamed CRT routines.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeDeformation
open Complexity LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open Algebra.RationalSubstitution

attribute [local irreducible] RationalSubstitutionBits.compiledTerm

theorem coefficient_precompose (source active inner middle outer f : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (q : List Bool) :
    coefficient (source ∘ f) (active ∘ f) (inner ∘ f) (middle ∘ f) (outer ∘ f)
      (fun c => n (f c)) (fun c => d (f c)) (fun c => ell (f c)) q =
        coefficient source active inner middle outer n d ell (f q) := rfl

attribute [local irreducible] coefficient

noncomputable def residueValue (source active inner middle outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) : List Bool → List Bool :=
  modularValue (source ∘ pairFst) (active ∘ pairFst) pairSnd (inner ∘ pairFst) (middle ∘ pairFst) (outer ∘ pairFst)
    (fun q => n (pairFst q)) (fun q => d (pairFst q)) (fun q => ell (pairFst q))

theorem residue_eq (source active inner middle outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (q : List Bool) :
    residueValue source active inner middle outer n d ell q =
      IntegerBits.coefficientResidue (coefficient source active inner middle outer n d ell (pairFst q)) (Nat.fromBitsLE (pairSnd q) + 1) := by
  rw [residueValue, modularValue, coefficient_precompose]

theorem residue_packet (source active inner middle outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) (m : ℕ) (hm : 0 < m) :
    residueValue source active inner middle outer n d ell (pair c (BinaryNatCode.encode (m - 1))) =
      BinaryNatCode.encode ((coefficient source active inner middle outer n d ell c : ZMod m).val) := by
  rw [residue_eq]
  simp only [pairFst_pair, pairSnd_pair, MacaulayBits.fromBits_encode, Nat.sub_add_cancel hm]
  rfl

theorem residueEvaluator {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) (outer : List Bool → List Bool) (ho : outer ∈ FP) :
    SpaceFunction (residueValue source active inner middle outer n d ell) :=
  evaluator D.withModulus (outer ∘ pairFst) (mem_FP_comp pairFst_mem_FP ho)

end LeanCanny.ETR.TubeDeformation
