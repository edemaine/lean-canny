/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralHistoryPhysicalRowMass
public import LeanCanny.Algebra.IntegralMixedExpressionBounds
/-! # Actual mixed critical births bound every retained physical row

The existing bank bound controls literal affine heights and common-scaled
normals. The actual new bank controls the final scalar equation. Older full
rows enter only through the ordinary induction hypothesis on their mass.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHistory
open MvPolynomial FlatAffineCriticalStage IntegralHistorySampler FixedWidthPolynomial IntegralCoordinateBasis
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

def physicalNormalBound (m G C : ℕ) := 2+2^(m*G+C)

omit [Fintype ι] in
theorem data_normal_bound (x : State P S B m ι) (hm : m≤S) (r : CriticalRule n)
    (G C : ℕ) (HG : x.bank.Bounds G) (hC : ∀i,(r.scales i).natAbs≤2^C)
    (j : Fin (n+2)) (i : Fin (n+1)) :
    (PhysicalPowerCriticalRows.coordinateNormals (data x hm r).objective (data x hm r).scales
      (data x hm r).free j i).natAbs≤physicalNormalBound m G C := by
  have HS : ∀i,(commonDenominator x*r.scales i).natAbs≤2^(m*G+C) := by
    intro i
    rw [Int.natAbs_mul,pow_add]
    exact Nat.mul_le_mul (commonDenominator_height x G HG) (hC i)
  refine Fin.cases ?_ (fun k=>?_) j
  · change (if i=(data x hm r).free then (2:ℤ) else 0).natAbs≤_
    by_cases hi : i=(data x hm r).free
    · rw [ite_eq_left hi]
      exact Nat.le_add_right 2 _
    · rw [ite_eq_right hi]
      exact Nat.zero_le _
  · change (if i=k then commonDenominator x*r.scales k else 0).natAbs≤_
    split_ifs
    · exact (HS k).trans (by unfold physicalNormalBound; omega)
    · simp only [Int.natAbs_zero,Nat.zero_le]

omit [Fintype ι] in
theorem data_height_matrix_bound (x : State P S B m ι) (hm : m≤S) (r : CriticalRule n)
    (G : ℕ) (HG : x.bank.Bounds G) (i : Fin (n+1)) (t : Fin (count m B)) :
    (Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis ((data x hm r).heights i)
      t (zeroFin m B)).natAbs≤2^retainedBudget m G r :=
  (expression_height x G HG (r.heights i) t (zeroFin m B)).trans
    (Nat.pow_le_pow_right (by decide) (Finset.le_sup (f:=fun i=>(r.heights i).height m G) (Finset.mem_univ i)))

noncomputable def physicalRowMassBound (_x : State P S B m ι) (r : CriticalRule n) (G C : ℕ) :=
  FlatAffineCriticalStage.massBound (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)
    (physicalNormalBound m G C) (count m B*2^retainedBudget m G r)

theorem criticalStep_full_row_mass (x : State P S B m ι) (hm : m≤S) (r : CriticalRule n)
    (G C old next : ℕ) (HG : x.bank.Bounds G) (hC : ∀i,(r.scales i).natAbs≤2^C)
    (ho : ∀i,MvMass.mass (x.sampler.rows i)≤old)
    (HN : (criticalStep x hm r).bank.Bounds next)
    (j : (ι⊕Variables (n+1))⊕Unit) :
    MvMass.mass ((criticalStep x hm r).sampler.rows j)≤
      max (max old (physicalRowMassBound x r G C))
        (2^PaddedIntegralParameterExtension.rowMassHeight m B next) := by
  apply IntegralHistorySampler.scalarStep_row_mass
    (IntegralHistorySampler.criticalStep x.sampler (data x hm r)) hm
    (criticalPolynomial x hm r) (criticalDegree x hm r)
    (max old (physicalRowMassBound x r G C)) next
  · exact IntegralHistorySampler.criticalStep_row_mass x.sampler (data x hm r) old
      (physicalNormalBound m G C) (retainedBudget m G r) ho
      (data_normal_bound x hm r G C HG hC) (data_height_matrix_bound x hm r G HG)
  · intro u v
    exact HN.numerator 0 u v

end LeanCanny.Algebra.IntegralMixedHistory
