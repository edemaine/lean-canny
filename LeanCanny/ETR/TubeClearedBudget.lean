/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeClearedRows

/-! # Uniform coefficient and mass budgets for cleared spatial rows

The rank-zero coordinate bounds apply to every spatial coefficient because
the substituted coordinates are uniform over ranks. The resulting binary
budget writers do not depend on the selected row or monomial.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeCleared
open LeanCanny.Encoding LeanCanny.Algebra
open Algebra.RationalSubstitution
open scoped Classical

attribute [local irreducible] RationalSubstitutionBits.compiledTerm uniformDegree coefficientAt

noncomputable def uniformBudget (source degree bits : List Bool → List Bool) (c : List Bool) : List Bool :=
  TubeParameter.budgetCode source (degree ∘ TubeParameter.coordinateContext id) (bits ∘ TubeParameter.coordinateContext id) (pair c [])

theorem uniformBudget_mem_FP {source degree bits : List Bool → List Bool} (hs : source ∈ FP) (he : degree ∈ FP) (hb : bits ∈ FP) :
    uniformBudget source degree bits ∈ FP := by
  have hz := TubeParameter.coordinateContext_mem_FP id_mem_FP
  have h := mem_FP_comp (mem_FP_pair id_mem_FP (constFn_mem_FP []))
    (TubeParameter.budgetCode_mem_FP hs (mem_FP_comp hz he) (mem_FP_comp hz hb))
  exact mem_FP_of_eq (g := uniformBudget source degree bits) h (fun _ => by simp only [uniformBudget, Function.comp_apply, id_eq])

theorem budget_packet (source degree bits : List Bool → List Bool) (c : List Bool) (r : ℕ) :
    TubeParameter.budgetCode source (degree ∘ TubeParameter.coordinateContext id) (bits ∘ TubeParameter.coordinateContext id)
      (pair c (BinaryNatCode.encode r)) = uniformBudget source degree bits c := by
  simp only [uniformBudget, TubeParameter.budgetCode, TubeParameter.arityCode, TubeParameter.widthCode,
    TubeParameter.termsCode, TubeParameter.sourceBits, FixedWidthPolynomial.countCode_code,
    TubeParameter.coordinateContext, Function.comp_apply, pairFst_pair, id_eq]

theorem coefficientAt_bits (source active index : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) (c : List Bool) (r k : ℕ) :
    ((coefficientAt source active index n d c r).coeff k).natAbs.size ≤
      Nat.fromBitsLE (uniformBudget source B.degree B.bits c) := by
  have h := TubeParameter.polynomial_coefficient_bits source active index _ _ (B.precomposeUniform id id_mem_FP)
    (pair c (BinaryNatCode.encode r)) k
  change (((TubeParameter.family source active index (fun q => n (pairFst q)) (fun q => d (pairFst q))).polynomial
    (pair c (BinaryNatCode.encode r))).coeff k).natAbs.size ≤
      Nat.fromBitsLE (TubeParameter.budgetCode source (B.degree ∘ TubeParameter.coordinateContext id)
        (B.bits ∘ TubeParameter.coordinateContext id) (pair c (BinaryNatCode.encode r))) at h
  rw [family_packet source active index n d c r, budget_packet] at h
  exact h

theorem row_coefficient_bits (source active index : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) (c : List Bool)
    (e : TubeParameter.Spatial (source c) →₀ ℕ) (k : ℕ) :
    (((row source active index n d c).coeff e).coeff k).natAbs.size ≤
      Nat.fromBitsLE (uniformBudget source B.degree B.bits c) := by
  by_cases he : e ∈ (row source active index n d c).support
  · have hb : ∀ i, e i < 2 ^ TubeIndexed.blockWidth (source c) := fun i =>
      (support_bound (source c) _ _ (n c) (d c) e he i).trans_lt (TubeIndexed.degreeBound_lt (source c))
    obtain ⟨r, hr⟩ := CoefficientWidthBits.exists_native_rank _ _ (TubeParameter.spatialEquiv (source c)) e hb
    have h := coefficientAt_bits source active index n d B c r k
    unfold coefficientAt at h
    rw [hr] at h
    exact h
  · rw [MvPolynomial.notMem_support_iff.mp he, Polynomial.coeff_zero]
    simp

noncomputable def massBudget (source degree bits : List Bool → List Bool) (c : List Bool) : List Bool :=
  BinaryNat.add (pair (uniformBudget source degree bits c)
    (BinaryNatCode.encode (BinaryNat.succ (uniformDegree source degree c)).length))

theorem massBudget_mem_FP {source degree bits : List Bool → List Bool} (hs : source ∈ FP) (he : degree ∈ FP) (hb : bits ∈ FP) :
    massBudget source degree bits ∈ FP := by
  have hd := mem_FP_comp (uniformDegree_mem_FP hs he) BinaryNat.succ_mem_FP
  have h := mem_FP_comp (mem_FP_pair (uniformBudget_mem_FP hs he hb) (bits_mem_FP (UnaryFn.length hd))) BinaryNat.add_mem_FP
  exact mem_FP_of_eq (g := massBudget source degree bits) h (fun _ => by simp only [massBudget, Function.comp_apply, BinaryNatCode.encode])

theorem massBudget_code (source degree bits : List Bool → List Bool) (c : List Bool) :
    Nat.fromBitsLE (massBudget source degree bits c) = Nat.fromBitsLE (uniformBudget source degree bits c) +
      (Nat.fromBitsLE (uniformDegree source degree c) + 1).size := by
  simp only [massBudget, BinaryNat.add_pair, BinaryNat.succ_eq_bits, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, Nat.size_eq_bits_len]

theorem row_coefficient_mass (source active index : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) (c : List Bool)
    (e : TubeParameter.Spatial (source c) →₀ ℕ) :
    coefficientMass ((row source active index n d c).coeff e) ≤ 2 ^ Nat.fromBitsLE (massBudget source B.degree B.bits c) := by
  rw [massBudget_code]
  apply coefficientMass_le_pow_of_degree_coeff _ _ _ (row_coefficient_degree source active index n d B c e)
  intro k
  exact (Nat.size_le.mp (row_coefficient_bits source active index n d B c e k)).le

theorem renamed_coefficient_mass (source active index : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) (c : List Bool)
    (e : Fin (TubeParameter.spatialCount (source c)) →₀ ℕ) :
    coefficientMass ((MvPolynomial.rename (TubeParameter.spatialEquiv (source c)) (row source active index n d c)).coeff e) ≤
      2 ^ Nat.fromBitsLE (massBudget source B.degree B.bits c) := by
  let f := TubeParameter.spatialEquiv (source c)
  have he : (e.mapDomain f.symm).mapDomain f = e := by
    ext i
    simp only [Finsupp.mapDomain_equiv_apply, Equiv.symm_apply_apply]
  rw [← he, MvPolynomial.coeff_rename_mapDomain f f.injective]
  exact row_coefficient_mass source active index n d B c _

end LeanCanny.ETR.TubeCleared
