/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.EncodedRationalSource

/-!
# Streamed rational-substitution certificates from encoded ETR sources

The source term and arity allowance are FP. Source counting, exponents, scalar
residues, clearing width, and source bit budgets are supplied internally.
Coordinate coefficient access may use polynomial space. Coordinate degree and
coefficient bounds also give the full infinitesimal-sign certificate, whose
semantics refers to evaluation of the actual input arithmetic term.
-/

@[expose] public section

namespace LeanCanny.ETR.RationalSubstitutionBits
open Complexity
open LeanCanny.Encoding
open LeanCanny.Computation
open LeanCanny.Algebra
open Polynomial

structure Coordinates (S : Source) where
  numerator : List Bool → ℕ → ℤ[X]
  denominator : List Bool → ℕ → ℤ[X]
  numeratorCode : List Bool → List Bool
  denominatorCode : List Bool → List Bool
  numerator_eq : ∀ c i, i < Nat.fromBitsLE (S.arity c) → ∀ k m, 0 < m →
    numeratorCode (pair (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) (BinaryNatCode.encode (m - 1))) =
      MatrixPower.residueBits (((numerator c i).coeff k : ℤ) : ZMod m)
  denominator_eq : ∀ c i, i < Nat.fromBitsLE (S.arity c) → ∀ k m, 0 < m →
    denominatorCode (pair (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) (BinaryNatCode.encode (m - 1))) =
      MatrixPower.residueBits (((denominator c i).coeff k : ℤ) : ZMod m)

noncomputable def Coordinates.family {S : Source} (C : Coordinates S) : RationalSubstitution.IntegerBits.Family :=
  S.family C.numerator C.denominator

noncomputable def Coordinates.access {S : Source} (C : Coordinates S) : RationalSubstitution.IntegerBits.Access C.family :=
  S.access C.numerator C.denominator C.numeratorCode C.denominatorCode C.numerator_eq C.denominator_eq

theorem Coordinates.evaluator {S : Source} (C : Coordinates S) (hS : S.PolyTime)
    (N : SpaceFunction C.numeratorCode) (D : SpaceFunction C.denominatorCode) : SpaceFunction C.family.value :=
  C.access.evaluator (S.access_controls hS _ _ _ _ _ _)
    (SpaceFunction.ofFP _ (MonomialReader.sourceCoefficient_mem_FP hS.term)) N D

structure CoordinateBounds {S : Source} (C : Coordinates S) where
  degree : List Bool → List Bool
  coefficientBits : List Bool → List Bool
  degree_mem_FP : degree ∈ FP
  coefficientBits_mem_FP : coefficientBits ∈ FP
  numerator_degree : ∀ c i, i < Nat.fromBitsLE (S.arity c) → (C.numerator c i).natDegree ≤ Nat.fromBitsLE (degree c)
  denominator_degree : ∀ c i, i < Nat.fromBitsLE (S.arity c) → (C.denominator c i).natDegree ≤ Nat.fromBitsLE (degree c)
  numerator_coeff : ∀ c i, i < Nat.fromBitsLE (S.arity c) → ∀ k,
    ((C.numerator c i).coeff k).natAbs ≤ 2 ^ Nat.fromBitsLE (coefficientBits c)
  denominator_coeff : ∀ c i, i < Nat.fromBitsLE (S.arity c) → ∀ k,
    ((C.denominator c i).coeff k).natAbs ≤ 2 ^ Nat.fromBitsLE (coefficientBits c)

theorem Coordinates.signEvaluator {S : Source} (C : Coordinates S) (hS : S.PolyTime)
    (B : CoordinateBounds C) (N : SpaceFunction C.numeratorCode) (D : SpaceFunction C.denominatorCode) :
    SpaceFunction (fun c => InfinitesimalSign.tag (C.family.polynomial c).trailingCoeff) := by
  apply C.access.signEvaluator (S.access_controls hS _ _ _ _ _ _)
    (SpaceFunction.ofFP _ (MonomialReader.sourceCoefficient_mem_FP hS.term)) N D
    B.degree B.coefficientBits S.sizeCode B.degree_mem_FP B.coefficientBits_mem_FP (S.sizeCode_mem_FP hS)
  · intro c r _
    simp only [S.sizeCode_eq, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact (S.syntax c).monomialCoefficient_natAbs_le_pow_dataSize r
  · exact B.numerator_degree
  · exact B.denominator_degree
  · exact B.numerator_coeff
  · exact B.denominator_coeff

theorem Coordinates.sign_term {S : Source} (C : Coordinates S) (c : List Bool) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, 0 < x → x < δ →
      (∀ i, i < Nat.fromBitsLE (S.arity c) → (C.denominator c i).eval₂ (Int.castRingHom ℝ) x ≠ 0) →
      SignType.sign ((S.syntax c).eval (fun i => (C.numerator c i).eval₂ (Int.castRingHom ℝ) x /
        (C.denominator c i).eval₂ (Int.castRingHom ℝ) x)) = SignType.sign (C.family.polynomial c).trailingCoeff := by
  obtain ⟨δ, hδ, hsign⟩ := C.family.sign_substitution c (S.syntax c).toData.size rfl
  refine ⟨δ, hδ, ?_⟩
  intro x hx hxd hden
  have h := hsign x hx hxd hden
  change SignType.sign ((RationalSubstitution.Indexed.source (Nat.fromBitsLE (S.arity c))
    (S.syntax c).monomialCount (S.syntax c).monomialCoefficient (S.syntax c).monomialExponent).eval₂
      (Int.castRingHom ℝ) (fun i => (C.numerator c i.val).eval₂ (Int.castRingHom ℝ) x /
        (C.denominator c i.val).eval₂ (Int.castRingHom ℝ) x)) = _ at h
  rw [(S.syntax c).eval₂_indexed_source (fun i => (C.numerator c i).eval₂ (Int.castRingHom ℝ) x /
    (C.denominator c i).eval₂ (Int.castRingHom ℝ) x) _ (S.scope c)] at h
  exact h

end LeanCanny.ETR.RationalSubstitutionBits
