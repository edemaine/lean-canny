/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordFullCutPrincipalSign
public import LeanCanny.Algebra.RealIteratedTarski
/-! # Exact infinitesimal principal signs on actual full-row curves -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFullCutLex
open LeanCanny.Algebra LeanCanny.Computation Polynomial Set
open CoefficientTarskiParameterQueries
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem encode_injective : Function.Injective InfinitesimalSign.encode := by
  intro a b h
  cases a <;> cases b <;> simp_all [InfinitesimalSign.encode]

private theorem scan_congr (a b : ℕ → ℝ) (h : ∀ i, SignType.sign (a i) = SignType.sign (b i)) (k : ℕ) :
    RealInfinitesimalSignSpace.scan a k = RealInfinitesimalSignSpace.scan b k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [RealInfinitesimalSignSpace.scan, ih, RealInfinitesimalSignSpace.tag, h k]

private theorem trailing_sign_congr (p q : ℝ[X]) (h : ∀ i, SignType.sign (p.coeff i) = SignType.sign (q.coeff i)) :
    SignType.sign p.trailingCoeff = SignType.sign q.trailingCoeff := by
  let k := max p.natDegree q.natDegree+1
  have HS := scan_congr p.coeff q.coeff h k
  rw [RealInfinitesimalSignSpace.scan_polynomial p k (by dsimp [k]; omega),
    RealInfinitesimalSignSpace.scan_polynomial q k (by dsimp [k]; omega)] at HS
  exact encode_injective HS

private theorem iterated_scan (p : (ℝ[X])[X]) (k : ℕ) (hk : p.natDegree < k) :
    RealInfinitesimalSignSpace.scan (fun i => (p.coeff i).trailingCoeff) k =
      RealInfinitesimalSignSpace.tag p.trailingCoeff.trailingCoeff := by
  by_cases hp : p = 0
  · subst p
    rw [RealInfinitesimalSignSpace.scan_zero _ _ (by simp)]
    exact ((RealInfinitesimalSignSpace.tag_nil _).mpr (by simp)).symm
  · exact RealInfinitesimalSignSpace.scan_first _ p.natTrailingDegree k
      (p.natTrailingDegree_le_natDegree.trans_lt hk)
      (Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr (Polynomial.coeff_natTrailingDegree_ne_zero.mpr hp))
      (fun i hi => by rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi, Polynomial.trailingCoeff_zero])

private theorem lex_sign_congr (p q : (ℝ[X])[X])
    (h : ∀ i j, SignType.sign ((p.coeff i).coeff j) = SignType.sign ((q.coeff i).coeff j)) :
    SignType.sign (RealIteratedTarski.lex p) = SignType.sign (RealIteratedTarski.lex q) := by
  let k := max p.natDegree q.natDegree+1
  have HS := scan_congr (fun i => (p.coeff i).trailingCoeff) (fun i => (q.coeff i).trailingCoeff)
    (fun i => trailing_sign_congr _ _ (h i)) k
  rw [iterated_scan p k (by dsimp [k]; omega), iterated_scan q k (by dsimp [k]; omega)] at HS
  exact encode_injective HS

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

/-- The scalar coordinates are the literal columns of the constructed full
sampler. Both dummy axes retain their installed order. -/
noncomputable def principal (ctx : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (index : ℕ) (negative : Bool) (j : ℕ) (beta : ℝ)
    (z : Fin (CoefficientMarkedRecordFullCutPhysical.rawData hn ht ha ctx).count → ℝ) :=
  MvTwoParameterCoefficient.evaluate (SymbolicScaledSquarefree.scalarEvaluation beta)
    (fun i : Fin (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx) =>
      CoefficientFinitePhysicalQuery.natural z (scalarAt (CoefficientMarkedRecordFullCutPhysical.rawData hn ht ha ctx) i.val))
    (castVariables (by omega : 1+(IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx+1) =
      IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx+2)
      (CoefficientMarkedRecordFullCutPrincipal.polynomial hn ht ha ctx k hk index 1 negative j))

theorem coefficient (ctx : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false)
    (index : ℕ) (negative : Bool) (j delta epsilon : ℕ) (beta : ℝ)
    (z : Fin (CoefficientMarkedRecordFullCutPhysical.rawData hn ht ha ctx).count → ℝ) :
    ((principal hn ht ha ctx k hk index negative j beta z).coeff delta).coeff epsilon =
      (CoefficientMarkedRecordFullCutPrincipalSign.polynomial hn ht ha ctx
        ⟨k, hk, hc, index, negative, j, delta, epsilon⟩).eval₂ (SymbolicScaledSquarefree.scalarEvaluation beta) z := by
  rw [principal, MvTwoParameterCoefficient.selected_coefficient]
  unfold CoefficientMarkedRecordFullCutPrincipalSign.polynomial CoefficientMarkedRecordFullCutBounds.finite
  rw [CoefficientFinitePhysicalQuery.evaluation]
  change _ = (MvPolynomial.rename _ _).eval₂ _ _
  rw [MvPolynomial.eval₂_rename]
  rfl

/-- This is the exact two-stage trailing sign, not a root-count or continuity
inference. Zero principals and either vanishing coefficient layer are allowed. -/
theorem lex_on_root_curve (ctx : List Bool) {a b : ℝ}
    (ha0 : (2 : ℝ)^CoefficientMarkedRecordFullCutPrincipalSign.cutoff hn ht ha ctx ≤ a)
    (x : C(Ioo a b, Fin (CoefficientMarkedRecordFullCutPrincipalSign.count hn ht ha ctx) → ℝ))
    (hx : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl u.val (x u))
    (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false)
    (index : ℕ) (negative : Bool) (j : ℕ) (u v : Ioo a b) :
    SignType.sign (RealIteratedTarski.lex (principal hn ht ha ctx k hk index negative j u.val (x u))) =
      SignType.sign (RealIteratedTarski.lex (principal hn ht ha ctx k hk index negative j v.val (x v))) := by
  apply lex_sign_congr
  intro delta epsilon
  rw [coefficient hn ht ha ctx k hk hc index negative j delta epsilon,
    coefficient hn ht ha ctx k hk hc index negative j delta epsilon]
  exact CoefficientMarkedRecordFullCutPrincipalSign.sign_on_root_curve hn ht ha ctx ha0 x hx
    ⟨k, hk, hc, index, negative, j, delta, epsilon⟩ u v

end LeanCanny.Encoding.CoefficientMarkedRecordFullCutLex
