/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordProperPrincipalSign
/-! # Exact Near/Rank iterated trailing signs on actual full-row curves -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordProperPrincipalLex
open LeanCanny.Algebra LeanCanny.Computation Polynomial Set
open IntegralMixedRoadmapProperRow
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
      (Polynomial.trailingCoeff_ne_zero.mpr (Polynomial.coeff_natTrailingDegree_ne_zero.mpr hp))
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

/-- The exact two-layer trailing sign follows from every literal coefficient
sign, including zero principals and both vanishing infinitesimal layers. -/
theorem near_lex_on_root_curve (right : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z)
    {a b : ℝ} (ha0 : (2 : ℝ)^CoefficientMarkedRecordProperPrincipalSign.cutoff hn ht ha false right z ≤ a)
    (x : C(Ioo a b, Fin (properPhysicalData hn ht ha false z).count → ℝ))
    (hx : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (catalogRoot n false z)
      (IntegralMixedCausalRecordPlanBits.count (catalogRoot n false z)) le_rfl u.val (x u))
    (power : Fin 3) (eta eps : Bool) (j : ℕ) (u v : Ioo a b) :
    SignType.sign (RealIteratedTarski.lex
      (CoefficientMarkedRecordProperPrincipalSeries.near hn ht ha right power eta eps z hc j u.val (x u))) =
    SignType.sign (RealIteratedTarski.lex
      (CoefficientMarkedRecordProperPrincipalSeries.near hn ht ha right power eta eps z hc j v.val (x v))) := by
  apply lex_sign_congr
  intro delta epsilon
  rw [CoefficientMarkedRecordProperPrincipalSeries.near_coefficient,
    CoefficientMarkedRecordProperPrincipalSeries.near_coefficient]
  have HS := CoefficientMarkedRecordProperPrincipalSign.sign_on_root_curve hn ht ha false right z ha0 x hx
    ⟨hc, hg, power, eta, eps, j, delta, epsilon⟩ u v
  simpa only [CoefficientMarkedRecordProperPrincipalSign.polynomial, CoefficientFinitePhysicalQuery.evaluation,
    CoefficientMarkedRecordProperPrincipalSign.naturalPolynomial, CoefficientMarkedRecordProperPrincipalSign.count, Bool.false_eq_true, ite_false] using HS

theorem rank_lex_on_root_curve (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z)
    {a b : ℝ} (ha0 : (2 : ℝ)^CoefficientMarkedRecordProperPrincipalSign.cutoff hn ht ha true false z ≤ a)
    (x : C(Ioo a b, Fin (properPhysicalData hn ht ha true z).count → ℝ))
    (hx : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (catalogRoot n true z)
      (IntegralMixedCausalRecordPlanBits.count (catalogRoot n true z)) le_rfl u.val (x u))
    (power : Fin 3) (eps : Bool) (j : ℕ) (u v : Ioo a b) :
    SignType.sign (RealIteratedTarski.lex
      (CoefficientMarkedRecordProperPrincipalSeries.rank hn ht ha power eps z hc j u.val (x u))) =
    SignType.sign (RealIteratedTarski.lex
      (CoefficientMarkedRecordProperPrincipalSeries.rank hn ht ha power eps z hc j v.val (x v))) := by
  apply lex_sign_congr
  intro delta epsilon
  rw [CoefficientMarkedRecordProperPrincipalSeries.rank_coefficient,
    CoefficientMarkedRecordProperPrincipalSeries.rank_coefficient]
  have HS := CoefficientMarkedRecordProperPrincipalSign.sign_on_root_curve hn ht ha true false z ha0 x hx
    ⟨hc, hg, power, false, eps, j, delta, epsilon⟩ u v
  simpa only [CoefficientMarkedRecordProperPrincipalSign.polynomial, CoefficientFinitePhysicalQuery.evaluation,
    CoefficientMarkedRecordProperPrincipalSign.naturalPolynomial, CoefficientMarkedRecordProperPrincipalSign.count, ite_true] using HS

end LeanCanny.Encoding.CoefficientMarkedRecordProperPrincipalLex
