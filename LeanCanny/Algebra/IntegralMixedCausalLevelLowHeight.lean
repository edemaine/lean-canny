/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedCausalLevelSchedule
public import LeanCanny.Algebra.FermatLevelLift
public import LeanCanny.ETR.PolynomialMass
/-! # Charging the actual changed-source LOW before its next birth

The new source is the literal level lift, with the original Fermat degree.
An original AST-size bound controls its old term; the causal binary exponent
controls its appended integer coefficient. No new coefficient evaluator or
new-bank height is assumed in this charge.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCausalLevelLowHeight
open IntegralMixedHistory MvPolynomial
open LeanCanny.Geometry.IntegralMixedCausalLevelSchedule

theorem sum_powers (T E : ℕ) : 2^T+2^E≤2^(T+E+1) := by
  calc
    _ ≤ 2^(T+E)+2^(T+E) := Nat.add_le_add
      (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
      (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))
    _ = _ := by rw [pow_succ]; omega

theorem level_mass {n : ℕ} (P : SpatialSource n) (E : ℕ) :
    MvMass.mass (FermatLevelLift.source P ((2:ℤ)^E)).low≤MvMass.mass P.low+2^E := by
  apply (MvMass.sub_le _ _).trans
  apply Nat.add_le_add (MvMass.rename_le _ _) ((MvMass.mul_le _ _).trans _)
  simp only [MvMass.C,MvMass.X,mul_one,Int.natAbs_pow]
  rfl

theorem source_coefficient {n T E F G : ℕ} (P : SpatialSource n)
    (HM : MvMass.mass P.low≤2^T) (hG : 1≤G) (hT : T≤G) (hE : E≤F*G)
    (e : Fin (n+2) →₀ ℕ) :
    (((FermatLevelLift.source P ((2:ℤ)^E)).low).coeff e).natAbs≤2^((F+2)*G) :=
  (MvMass.coeff_le _ e).trans ((level_mass P E).trans
    ((Nat.add_le_add_right HM _).trans ((sum_powers T E).trans
      (Nat.pow_le_pow_right (by decide) (source_charge hG hT hE)))))

theorem tilted_source_coefficient {n k D T E F G : ℕ} (u : Fin n) (t : ETR.Term) (ht : t.degreeBound≤D)
    (hsize : (FixedLeadingTiltedSource.lowTerm k D u.val t).toData.size≤T)
    (hG : 1≤G) (hT : T≤G) (hE : E≤F*G) (e : Fin (n+2) →₀ ℕ) :
    (((FermatLevelLift.source (FixedLeadingTiltedSource.source k D u t ht) ((2:ℤ)^E)).low).coeff e).natAbs≤
      2^((F+2)*G) := by
  apply source_coefficient _ _ hG hT hE e
  exact ((FixedLeadingTiltedSource.lowTerm k D u.val t).finitePolynomial_mass (n+1)).trans
    (Nat.pow_le_pow_right (by decide) hsize)

end LeanCanny.Algebra.IntegralMixedCausalLevelLowHeight
