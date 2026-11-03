/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNumericalSweepSpecialization
/-! # A literal scale-two mean row centers an atomic sweep at zero

The mean uses two existing bank references. It is not identified with a
single retained producer. The comparison concerns specialized polynomials.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedMeanCenteredSweep
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedNumericalSweep Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

def rule (r : Rule n) (a b : Fin m) : Rule n where
  critical:={r.critical with
    scales:=fun i=>if i=r.height then 2 else r.critical.scales i
    scales_ne_zero:=fun i=>by split_ifs;norm_num;exact r.critical.scales_ne_zero i
    heights:=fun i=>if i=r.height then .add (.reference a.val) (.reference b.val) else r.critical.heights i}
  height:=r.height
  height_frozen:=r.height_frozen
  slope:=r.slope
  slope_ne_zero:=r.slope_ne_zero

theorem normalized_at_mean (r : Rule n) (a b : Fin m) (values : Fin m→ℝ)
    (hzero : (r.critical.heights r.height).evaluate values=0)
    (hone : r.critical.scales r.height=1) (i : Fin (n+1)) :
    (normalized r values i.val).eval ((values a+values b)/2)=
      (normalized (rule r a b) values i.val).eval 0 :=by
  rw [normalized_eval,normalized_eval]
  by_cases hi : i=r.height
  · subst i
    simp only [rule,ite_true,hzero,hone,Int.cast_one,div_one,AffineExpr.evaluate,
      a.isLt,b.isLt,dite_eq_left,zero_add,add_zero,Int.cast_ofNat]
  · simp only [rule,ite_eq_right hi,add_zero]

theorem normalized_frozen (r : Rule n) (a b : Fin m) (values : Fin m→ℝ)
    (hzero : (r.critical.heights r.height).evaluate values=0)
    (hone : r.critical.scales r.height=1) :
    ∀i,i<r.critical.offset.val→
      (normalized r values i).eval ((values a+values b)/2)=
        (normalized (rule r a b) values i).eval 0 :=by
  intro i hi
  exact normalized_at_mean r a b values hzero hone ⟨i,hi.trans r.critical.offset.isLt⟩

theorem coordinateAt_mean (P : SpatialSource n) (r : Rule n) (a b : Fin m)
    (values : Fin m→ℝ)
    (hzero : (r.critical.heights r.height).evaluate values=0)
    (hone : r.critical.scales r.height=1)
    (j : Fin (n-r.critical.offset.val+1)) :
    coordinateAt P r values ((values a+values b)/2) j=
      coordinateAt P (rule r a b) values 0 j :=by
  exact coordinateAt_congr P r (rule r a b) rfl rfl values values _ _
    (normalized_frozen r a b values hzero hone) j

end LeanCanny.Algebra.IntegralMixedMeanCenteredSweep
