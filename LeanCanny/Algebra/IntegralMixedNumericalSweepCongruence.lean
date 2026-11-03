/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNumericalSweepRows
/-! # Equal numerical frozen equations give the same canonical sweep

Only the frozen slots are compared. Coordinate labels are transported by
the actual equality of offsets; no sample-word transport is used.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNumericalSweep
open IntegralMixedHistory IntegralMixedCriticalSweep Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n m l : ℕ}

theorem normalized_at (r : Rule n) (values : Fin m→ℝ) (i : Fin (n+1)) :
    normalized r values i.val=
      C ((r.critical.heights i).evaluate values/(r.critical.scales i:ℝ))+
        if i=r.height then C ((r.critical.scales i:ℝ)⁻¹)*X else 0 :=by
  unfold normalized ClearedCoordinateNormalization.normalized
  rw [dite_eq_left i.isLt]
  unfold numericalHeights
  by_cases hi : i=r.height
  · simp only [hi,ite_true,mul_add,←C_mul,div_eq_mul_inv]
    congr 1
    exact congrArg C (mul_comm _ _)
  · simp only [ite_eq_right hi,add_zero,←C_mul,div_eq_mul_inv]
    exact congrArg C (mul_comm _ _)

theorem normalized_frozen_eq_of_levels (r s : Rule n)
    (hh : r.height=s.height)
    (hscale : r.critical.scales r.height=s.critical.scales s.height)
    (values : Fin m→ℝ) (other : Fin l→ℝ)
    (H : ∀i : Fin (n+1),i.val<r.critical.offset.val→
      (r.critical.heights i).evaluate values/(r.critical.scales i:ℝ)=
        (s.critical.heights i).evaluate other/(s.critical.scales i:ℝ)) :
    ∀i,i<r.critical.offset.val→normalized r values i=normalized s other i :=by
  intro i hi
  have hfit : i<n+1:=hi.trans r.critical.offset.isLt
  let j : Fin (n+1):=⟨i,hfit⟩
  rw [show i=j.val from rfl,normalized_at r values j,normalized_at s other j,H j hi]
  by_cases hj : j=r.height
  · have hs : j=s.height:=hj.trans hh
    rw [ite_eq_left hj,ite_eq_left hs]
    rw [show r.critical.scales j=s.critical.scales j from by simpa only [hj,hh] using hscale]
  · have hs : j≠s.height:=fun h=>hj (h.trans hh.symm)
    rw [ite_eq_right hj,ite_eq_right hs]

def indexCast (r s : Rule n) (hoff : r.critical.offset=s.critical.offset)
    (j : Fin (n-r.critical.offset.val+1)) : Fin (n-s.critical.offset.val+1) :=
  Fin.cast (by rw [hoff]) j

theorem coordinate_congr (P : SpatialSource n) (r s : Rule n)
    (hoff : r.critical.offset=s.critical.offset)
    (hobj : r.critical.objective=s.critical.objective)
    (values : Fin m→ℝ) (other : Fin l→ℝ)
    (H : ∀i,i<r.critical.offset.val→normalized r values i=normalized s other i)
    (j : Fin (n-r.critical.offset.val+1)) :
    coordinate P r values j=coordinate P s other (indexCast r s hoff j) :=by
  rcases r with ⟨⟨o,b,c,sc,hsc,heights⟩,height,hheight,slope,hslope⟩
  rcases s with ⟨⟨o',b',c',sc',hsc',heights'⟩,height',hheight',slope',hslope'⟩
  dsimp only at hoff hobj
  subst o'
  subst b'
  exact ClearedCoordinateFrozenCongruence.annihilator P.degree 1 _ _ o.val
    (by dsimp only;have :=o.isLt;omega) H _ (P.leading:Polynomial ℝ) _ j

theorem row_congr (P : SpatialSource n) (r s : Rule n)
    (hoff : r.critical.offset=s.critical.offset)
    (hobj : r.critical.objective=s.critical.objective)
    (values : Fin m→ℝ) (other : Fin l→ℝ)
    (H : ∀i,i<r.critical.offset.val→normalized r values i=normalized s other i)
    (j : Fin (n-r.critical.offset.val+1)) :
    HEq (row P r values j) (row P s other (indexCast r s hoff j)) :=by
  rcases r with ⟨⟨o,b,c,sc,hsc,heights⟩,height,hheight,slope,hslope⟩
  rcases s with ⟨⟨o',b',c',sc',hsc',heights'⟩,height',hheight',slope',hslope'⟩
  dsimp only at hoff hobj
  subst o'
  subst b'
  apply heq_of_eq
  exact ClearedCoordinateFrozenCongruence.specialize P.degree 1 _ _ o.val
    (by dsimp only;have :=o.isLt;omega) H _

end LeanCanny.Algebra.IntegralMixedNumericalSweep
