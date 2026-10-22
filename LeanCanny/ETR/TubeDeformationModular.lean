/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeDeformationBudget
public import LeanCanny.Algebra.BerkowitzAffinePolynomialSpace

/-! # The actual encoded tube matrix as an affine polynomial family

The original matrix is supplied by the complete tube coefficient pipeline.
Coefficient reduction commutes with the perturbation/projection encoding.
The proved encoded degree allowance supplies the affine backend's bound.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeDeformation
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open scoped Classical

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree

noncomputable def originalFamily (source active modulus inner middle : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) : BerkowitzPolynomial.ModularFamily :=
  (TubeBivariate.family source active modulus inner middle n d ell B).encoded.determinant

noncomputable def originalAccess (source active modulus inner middle : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) :
    BerkowitzPolynomial.ModularAccess (originalFamily source active modulus inner middle n d ell B) :=
  (TubeBivariate.access source active modulus inner middle n d ell B).encoded.determinant

noncomputable def encodedOriginalMatrix (source active degree : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) :=
  Macaulay.matrix (encodedRows source active degree n d ell c) (MacaulayBits.Degrees (TubeCleared.layout source) c)
    (TubeCleared.matrixWidth (source c))

theorem original_matrix_reduction (source active modulus inner middle : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) (c : List Bool) :
    (originalFamily source active modulus inner middle n d ell B).matrix c =
      (encodedOriginalMatrix source active B.degree n d ell c).map
        (Polynomial.mapRingHom (Int.castRingHom (ZMod (Nat.fromBitsLE (modulus c) + 1)))) := by
  let φ := Int.castRingHom (ZMod (Nat.fromBitsLE (modulus c) + 1))
  have hc : (PolynomialKronecker.encode (R := ZMod (Nat.fromBitsLE (modulus c) + 1)) (radix source B.degree c)).comp
      (TubeBivariate.reduction (Nat.fromBitsLE (modulus c) + 1)) =
      (Polynomial.mapRingHom φ).comp (PolynomialKronecker.encode (radix source B.degree c)) := by
    apply RingHom.ext
    intro p
    exact PolynomialKronecker.encode_map φ _ p
  change Macaulay.matrix (fun i => ((TubeBivariate.rows source active n d ell c i).map
    (TubeBivariate.reduction (Nat.fromBitsLE (modulus c) + 1))).map
      (PolynomialKronecker.encode (radix source B.degree c))) (fun i : Fin (TubeParameter.spatialCount (source c)) => if i.val = 0 then 1 else TubeIndexed.degreeBound (source c))
        (TubeCleared.matrixWidth (source c)) =
    (Macaulay.matrix (encodedRows source active B.degree n d ell c) (fun i : Fin (TubeParameter.spatialCount (source c)) => if i.val = 0 then 1 else TubeIndexed.degreeBound (source c))
      (TubeCleared.matrixWidth (source c))).map (Polynomial.mapRingHom φ)
  rw [Macaulay.matrix_map (Polynomial.mapRingHom φ)]
  congr 1
  funext i
  simp only [encodedRows, MvPolynomial.map_map, hc]

theorem original_entry_degree (source active modulus inner middle : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) (c : List Bool)
    (r s : Fin ((originalFamily source active modulus inner middle n d ell B).dimension c)) :
    ((originalFamily source active modulus inner middle n d ell B).matrix c r s).natDegree ≤
      Nat.fromBitsLE (entryDegreeCode source B.degree c) := by
  have hm := congrFun (congrFun (original_matrix_reduction source active modulus inner middle n d ell B c) r) s
  rw [hm]
  change (((encodedOriginalMatrix source active B.degree n d ell c) r s).map
    (Int.castRingHom (ZMod (Nat.fromBitsLE (modulus c) + 1)))).natDegree ≤ _
  apply Polynomial.natDegree_map_le.trans
  exact Macaulay.polynomial_entry_degree_le _ _ _ _ (encoded_row_degree source active n d ell B c) r s

noncomputable def modularFamily (source active modulus inner middle outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) : BerkowitzAffinePolynomial.Family where
  source := originalFamily source active modulus inner middle n d ell B
  inner c := (originalFamily source active modulus inner middle n d ell B).degree c
  outer c := Nat.fromBitsLE (outer c)
  bound c := Nat.fromBitsLE (entryDegreeCode source B.degree c)
  entry_degree := original_entry_degree source active modulus inner middle n d ell B

noncomputable def modularAccess (source active modulus inner middle outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) :
    BerkowitzAffinePolynomial.Access (modularFamily source active modulus inner middle outer n d ell B) where
  original := originalAccess source active modulus inner middle n d ell B
  inner := (originalAccess source active modulus inner middle n d ell B).degree
  outer := BinaryNat.normalize ∘ outer
  bound := BinaryNat.normalize ∘ entryDegreeCode source B.degree
  inner_eq := (originalAccess source active modulus inner middle n d ell B).degree_eq
  outer_eq c := BinaryNat.normalize_eq_bits (outer c)
  bound_eq c := BinaryNat.normalize_eq_bits (entryDegreeCode source B.degree c)

end LeanCanny.ETR.TubeDeformation
