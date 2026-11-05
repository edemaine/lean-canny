/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoefficientMarkedRecordEffectiveCutoff
public import LeanCanny.Algebra.IntegralMixedBankCoordinatePolynomial

/-! # Constructed parameter polynomials for retained bank coordinates

The formal matrix and denominator come from the constructed prefix. Its
specialization uses the proved effective prefix theorem, with no supplied
characteristic source, coefficient map or bank evaluator.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordBankPolynomial
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def formal {S B m : ℕ} {I : Type}
    (F : CoefficientHistoryPrefix.Prefix ℤ[X] S B m I) (i : Fin m) : Polynomial ℤ[X] :=
  ScaledGradedReductionAnnihilator.polynomial
    (Algebra.leftMulMatrix F.basis.basis (F.bank.cleared i)) F.bank.commonDenominator 1

theorem formal_degree {S B m : ℕ} {I : Type}
    (F : CoefficientHistoryPrefix.Prefix ℤ[X] S B m I) (i : Fin m) :
    (formal F i).natDegree ≤ (2 ^ B) ^ m := by
  unfold formal ScaledGradedReductionAnnihilator.polynomial
  have HD : (C (F.bank.commonDenominator ^ 1) * X : Polynomial ℤ[X]).natDegree ≤ 1 := by
    exact Polynomial.natDegree_mul_le.trans (by simp)
  apply Polynomial.natDegree_comp_le.trans
  rw [Matrix.charpoly_natDegree_eq_dim]
  simpa only [Fintype.card_fun, Fintype.card_fin, Nat.mul_one] using
    Nat.mul_le_mul_left ((2 ^ B) ^ m) HD

private noncomputable def native {a S B m : ℕ} {P : SpatialSource a} {I : Type}
    (x : State P S B m I) (i : Fin m) : Polynomial ℤ :=
  ScaledGradedReductionAnnihilator.polynomial
    (Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.basis (cleared x i)) (commonDenominator x) 1

private theorem native_eq {a S B m : ℕ} {P : SpatialSource a} {I : Type}
    (x : State P S B m I) (i : Fin m) :
    native x i = IntegralMixedBankCoordinatePolynomial.polynomial x i := by
  unfold native IntegralMixedBankCoordinatePolynomial.polynomial IntegralMixedBankCoordinatePolynomial.matrix
    ScaledGradedReductionAnnihilator.polynomial
  apply congrArg (fun p : ℤ[X] => p.comp (C (commonDenominator x ^ 1) * X))
  have HM : Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis (cleared x i) =
      Matrix.reindex (IntegralCoordinateBasis.boxEquiv m B) (IntegralCoordinateBasis.boxEquiv m B)
        (Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.basis (cleared x i)) := by
    ext r s
    simp only [IntegralCoordinateBasis.finBasis, Algebra.leftMulMatrix_eq_repr_mul,
      Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [HM, Matrix.charpoly_reindex]

private theorem map_of_specializes {a S B m : ℕ} {P : SpatialSource a} {I J : Type}
    (F : CoefficientHistoryPrefix.Prefix ℤ[X] S B m I) (x : State P S B m J) (r : ℕ)
    (h : CoefficientHistoryPrefix.Specializes r F x) (i : Fin m) :
    (formal F i).map (evalRingHom ((2 : ℤ) ^ r)) = native x i := by
  obtain ⟨ψ, hb, hg, _, _⟩ := h
  have HM := hb.charpoly_map (F.bank.cleared i)
  rw [hg.cleared] at HM
  apply Polynomial.ext
  intro k
  rw [Polynomial.coeff_map, formal, native,
    ScaledGradedReductionAnnihilator.coefficient, ScaledGradedReductionAnnihilator.coefficient,
    map_mul, map_pow]
  have HC := congrArg (fun p : ℤ[X] => p.coeff k) HM
  rw [Polynomial.coeff_map] at HC
  rw [← HC, hg.commonDenominator]
  rfl

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
attribute [local irreducible] CoefficientMarkedRecordNative.run CoefficientMarkedRecordPrefix.build

noncomputable def polynomial (ctx : List Bool) (k : ℕ)
    (i : Fin ((CoefficientMarkedPreludeActual.indices n ctx).length + (CoefficientMarkedRecordActual.codes ctx k).length)) :
    Polynomial ℤ[X] :=
  formal (CoefficientMarkedRecordPrefix.build hn ht ha ctx (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
    (CoefficientMarkedRecordActual.codes ctx k)) i

/-- Specialization gives the actual native retained-coordinate annihilator. -/
theorem specializes (ctx : List Bool) (radius : List Bool → ℕ) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx)
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ radius ctx)
    (i : Fin ((CoefficientMarkedPreludeActual.indices n ctx).length + (CoefficientMarkedRecordActual.codes ctx k).length)) :
    (polynomial hn ht ha ctx k i).map (evalRingHom ((2 : ℤ) ^ radius ctx)) =
      IntegralMixedBankCoordinatePolynomial.polynomial
        (CoefficientMarkedRecordNative.run hn ht ha ctx radius (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
          (CoefficientMarkedRecordActual.codes ctx k) (CoefficientMarkedRecordActual.prefix_room hn ht ha ctx k hk)) i := by
  exact (map_of_specializes _ _ _
    (CoefficientMarkedRecordEffectiveCutoff.specializes_above_effective hn ht ha ctx radius k hk hR) i).trans
      (native_eq _ i)

end LeanCanny.Encoding.CoefficientMarkedRecordBankPolynomial
