/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayFullBoxSpace
public import LeanCanny.Algebra.CertifiedPolynomial

/-! # Certified implicit matrices and determinant coefficient readers

Dimensions and inner degree allowances are binary controls. Original entry
residues retain their native space certificate, which the Kronecker and
Berkowitz evaluators include in every determinant coefficient computation.
-/

@[expose] public section
namespace LeanCanny.Algebra.CertifiedMatrix
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
set_option backward.isDefEq.respectTransparency false

/-- A selected-modulus entry certificate; no matrix or coefficient table is stored. -/
structure Bivariate (modulus : List Bool → List Bool) where
  dimension : List Bool → ℕ
  dimension_pos : ∀ c, 0 < dimension c
  dimensionFP : BinaryFn dimension
  bound : List Bool → ℕ
  boundFP : BinaryFn bound
  matrix : (c : List Bool) → Matrix (Fin (dimension c)) (Fin (dimension c)) (Polynomial (Polynomial ℤ))
  inner_bound : ∀ c i j k, ((matrix c i j).coeff k).natDegree ≤ bound c
  coefficient : List Bool → List Bool
  coefficient_eq : ∀ c (i j : Fin (dimension c)) u v,
    coefficient (pair c (pair (BinaryNatCode.encode i.val)
      (pair (BinaryNatCode.encode j.val) (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))))) =
        residueBits (((((matrix c i j).coeff v).coeff u) : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1))
  evaluator : SpaceFunction coefficient

noncomputable def Bivariate.value {modulus : List Bool → List Bool} (A : Bivariate modulus)
    (inner outer : List Bool → List Bool) (c : List Bool) : List Bool :=
  residueBits (((((A.matrix c).det.coeff (Nat.fromBitsLE (outer c))).coeff (Nat.fromBitsLE (inner c))) : ℤ) :
    ZMod (Nat.fromBitsLE (modulus c) + 1))

/-- Cast transport, normalization, and determinant assembly are derived once. -/
theorem Bivariate.determinantEvaluator {modulus : List Bool → List Bool} (A : Bivariate modulus)
    (inner outer : List Bool → List Bool) (hm : modulus ∈ FP) (hi : inner ∈ FP) (ho : outer ∈ FP) :
    SpaceFunction (A.value inner outer) := by
  let F : BivariateDeterminantBits.Family := {
    dimension := A.dimension
    dimension_pos := A.dimension_pos
    modulus c := Nat.fromBitsLE (modulus c) + 1
    modulus_ne_zero _ := by omega
    inner c := Nat.fromBitsLE (inner c)
    outer c := Nat.fromBitsLE (outer c)
    bound := A.bound
    matrix c := (A.matrix c).map (Polynomial.mapRingHom (Polynomial.mapRingHom (Int.castRingHom _)))
    inner_bound c i j k := by
      simp only [Matrix.map_apply, Polynomial.coe_mapRingHom, Polynomial.coeff_map]
      exact Polynomial.natDegree_map_le.trans (A.inner_bound c i j k) }
  have E := F.evaluator A.coefficient (fun c i j u v => by
    simpa only [F, Matrix.map_apply, Polynomial.coe_mapRingHom,
      Polynomial.coeff_map, Int.coe_castRingHom] using A.coefficient_eq c i j u v)
    A.dimensionFP ((BinaryFn.fromBits hm).add (BinaryFn.const 1)) A.boundFP
    (BinaryFn.fromBits hi) (BinaryFn.fromBits ho) A.evaluator
  refine E.congr (funext fun c => ?_)
  let phi := Polynomial.mapRingHom (Polynomial.mapRingHom (Int.castRingHom (ZMod (Nat.fromBitsLE (modulus c) + 1))))
  change residueBits (((((A.matrix c).map phi).det).coeff _).coeff _) = _
  have hd : phi ((A.matrix c).det) = ((A.matrix c).map phi).det := phi.map_det (A.matrix c)
  rw [← hd]
  simp only [phi, Polynomial.coe_mapRingHom, Polynomial.coeff_map]
  rfl

/-- Expose all coefficient/modulus queries through the polynomial-reader core. -/
noncomputable def determinantReader (N bound : List Bool → ℕ)
    (P : (c : List Bool) → Matrix (Fin (N c)) (Fin (N c)) (Polynomial (Polynomial ℤ)))
    (hN : ∀ c, 0 < N c) (hn : BinaryFn N) (hb : BinaryFn bound)
    (hP : ∀ c i j k, ((P c i j).coeff k).natDegree ≤ bound c)
    (coefficient : List Bool → List Bool) (E : SpaceFunction coefficient)
    (hc : ∀ c m (i j : Fin (N c)) u v,
      coefficient (pair (pair c m) (pair (BinaryNatCode.encode i.val)
        (pair (BinaryNatCode.encode j.val) (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))))) =
          residueBits (((((P c i j).coeff v).coeff u) : ℤ) : ZMod (Nat.fromBitsLE m + 1))) :
    CertifiedPolynomial.BivariateReader (fun c => (P c).det) := by
  let original := fun q => pairFst (pairFst q)
  let modulus := fun q => pairSnd (pairFst q)
  let input := fun q => pair (pair (original (pairFst q)) (modulus (pairFst q))) (pairSnd q)
  have horiginal : original ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hmodulus : modulus ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have hinput : input ∈ FP := mem_FP_pair
    (mem_FP_pair (mem_FP_comp (f := pairFst) (g := original) pairFst_mem_FP horiginal)
      (mem_FP_comp (f := pairFst) (g := modulus) pairFst_mem_FP hmodulus)) pairSnd_mem_FP
  let A : Bivariate modulus := {
    dimension := N ∘ original
    dimension_pos q := hN (original q)
    dimensionFP := hn.comp horiginal
    bound := bound ∘ original
    boundFP := hb.comp horiginal
    matrix q := P (original q)
    inner_bound q := hP (original q)
    coefficient := coefficient ∘ input
    coefficient_eq q i j u v := by
      simpa only [Function.comp_apply, input, original, modulus, pairFst_pair, pairSnd_pair] using
        hc (original q) (modulus q) i j u v
    evaluator := E.precompose input hinput }
  exact {
    coefficient := A.value (pairFst ∘ pairSnd) (pairSnd ∘ pairSnd)
    evaluator := A.determinantEvaluator _ _ hmodulus
      (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
    coefficient_eq q u v := by
      dsimp only [Bivariate.value, A, original, modulus, Function.comp_apply]
      apply congrArg₂ (fun (z : ℤ) (n : ℕ) => residueBits (z : ZMod n))
      · simp only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
        exact congrArg (fun c => ((P c).det.coeff v).coeff u)
          (congrArg pairFst (pairFst_pair q (pair u.bits v.bits)))
      · simp only [pairFst_pair] }

end LeanCanny.Algebra.CertifiedMatrix
