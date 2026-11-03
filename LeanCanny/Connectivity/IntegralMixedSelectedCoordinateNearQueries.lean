/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedSelectedWindowStability
public import LeanCanny.Connectivity.IntegralMixedSelectedWindowQueries
public import LeanCanny.Algebra.IntegralMixedSelectedCoordinateOrderedQueries
public import LeanCanny.Algebra.DyadicTarskiSpace
/-! # Selected coordinate Near is an ordered principal-statistic test

Both parameters use the SAME old hom. Exact coordinate and seed degrees
are derived; no ordered window stabilization or root-regularity is assumed.
-/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedSelectedCoordinateNearQueries
open LeanCanny.Algebra LeanCanny.Geometry Polynomial
open IntegralMixedHistory IntegralMixedSelectedCoordinateOrderedQueries
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
variable (x : State P S B m ι) (hm : m≤S) (r : IntegralMixedCriticalSweep.Rule n)
variable (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (i : IntegralMixedSelectedGeometry.Free r)
variable (anchor : ℝ) (negativeEta : Bool) (Q : ℤ) (hQ : Q≠0) (allowance : ℕ)
variable (y scale : ℝ) (hscale : 0<scale)

noncomputable def head :=IntegralMixedSelectedCoordinateAffineDegree.head x hm r i φ anchor negativeEta Q allowance
noncomputable def degree :=PurePowerReductionBounds.dimension (n-r.critical.offset.val+1) P.degree
noncomputable def queryValue (negativeEpsilon : Bool) (e : Fin 3) :=
  IntegralMixedSelectedCoordinateOrderedQueries.value (head x hm r φ i anchor negativeEta Q allowance)
    (degree (P:=P) r) y scale negativeEpsilon e

include hQ hscale in
private theorem clear_query (ε δ : ℝ) (negativeEpsilon : Bool) (e : Fin 3) :
    RootSignQueries.tarskiQuery
      (IntegralMixedFrozenFrameSectionCode.polynomial x hm r φ
        (anchor+if negativeEta then -δ else δ) i)
      ((Polynomial.X-Polynomial.C (y+if negativeEpsilon then ε else -ε))^e.val)=
      RootSignQueries.tarskiQuery
        ((IntegralMixedSelectedCoordinateWindowDegree.head (head x hm r φ i anchor negativeEta Q allowance)).map
          (RealIteratedTarski.evaluate ε δ))
        ((IntegralMixedSelectedCoordinateWindowDegree.query y scale negativeEpsilon e).map
          (RealIteratedTarski.evaluate ε δ)) :=by
  rw [evaluated_head,evaluated_query]
  have HH : (head x hm r φ i anchor negativeEta Q allowance).map (Polynomial.evalRingHom δ)=
      Polynomial.C ((Q:ℝ)^(2*allowance))*
        IntegralMixedFrozenFrameSectionCode.polynomial x hm r φ
          (anchor+if negativeEta then -δ else δ) i :=by
    unfold head IntegralMixedSelectedCoordinateAffineDegree.head IntegralMixedFrozenFrameSectionCode.polynomial
    rw [Polynomial.map_mul,Polynomial.map_C,Polynomial.coe_evalRingHom,Polynomial.eval_C,
      Polynomial.map_map,IntegralMixedSelectedCoordinateAffineDegree.shift_evaluate]
  rw [HH]
  have HQ : Polynomial.X-Polynomial.C y+Polynomial.C (if negativeEpsilon then -ε else ε)=
      (Polynomial.X-Polynomial.C (y+if negativeEpsilon then ε else -ε) : ℝ[X]) :=by
    cases negativeEpsilon <;> simp [map_add,map_neg] <;> ring
  rw [mul_pow,←map_pow,HQ]
  exact (RootSignQueries.tarskiQuery_C_mul _ _ _ _
    (pow_ne_zero _ (Int.cast_ne_zero.mpr hQ)) (pow_pos hscale _)).symm

noncomputable def test (code : ℕ) : Prop :=
  2*queryValue x hm r φ i anchor negativeEta Q allowance y scale false 0≤2*(code:ℤ)+
    queryValue x hm r φ i anchor negativeEta Q allowance y scale false 2+
    queryValue x hm r φ i anchor negativeEta Q allowance y scale false 1 ∧
  2*(code:ℤ)<queryValue x hm r φ i anchor negativeEta Q allowance y scale true 2-
    queryValue x hm r φ i anchor negativeEta Q allowance y scale true 1

include hQ hscale in
theorem window_stable (code : ℕ) :
    ∃η : ℝ,0<η ∧ ∀ε : ℝ,0<ε→ε<η→∃ζ : ℝ,0<ζ ∧ ∀δ : ℝ,0<δ→δ<ζ→
      (IntegralMixedSelectedCoordinateWindow.Window
        (IntegralMixedFrozenFrameSectionCode.polynomial x hm r φ
          (anchor+if negativeEta then -δ else δ) i) code y ε↔
        test x hm r φ i anchor negativeEta Q allowance y scale code) :=by
  have HD : (head x hm r φ i anchor negativeEta Q allowance).natDegree=degree (P:=P) r :=
    IntegralMixedSelectedCoordinateAffineDegree.head_degree x hm r i φ anchor negativeEta Q hQ allowance
  obtain ⟨η,hη,HE⟩:=eventually_queries (head x hm r φ i anchor negativeEta Q allowance)
    (degree (P:=P) r) (pow_pos (Nat.two_pow_pos _) _) HD y scale (ne_of_gt hscale)
  refine ⟨η,hη,fun ε he heη=>?_⟩
  obtain ⟨ζ,hζ,HD⟩:=HE ε he heη
  refine ⟨ζ,hζ,fun δ hd hdζ=>?_⟩
  have HQ (negative : Bool) (e : Fin 3) :=
    (clear_query x hm r φ i anchor negativeEta Q hQ allowance y scale hscale ε δ negative e).trans
      (HD negative e δ hd hdζ)
  have H0:=HQ false 0
  have HL1:=HQ false 1
  have HL2:=HQ false 2
  have HH1:=HQ true 1
  have HH2:=HQ true 2
  simp only [Bool.false_eq_true,ite_false,ite_true,show (0 : Fin 3).val=0 from rfl,
    show (1 : Fin 3).val=1 from rfl,show (2 : Fin 3).val=2 from rfl,
    pow_zero,pow_one,←sub_eq_add_neg] at H0 HL1 HL2 HH1 HH2
  rw [IntegralMixedSelectedWindowQueries.window_iff,H0,HL1,HL2,HH1,HH2]
  rfl

include hQ hscale in
theorem near_iff {a b : ℝ} (hab : a<b) (right : Bool) (code : ℕ) :
    IntegralMixedSelectedCoordinateEndpoint.Near x hm r φ a b (if right then b else a) i code y↔
      test x hm r φ i (if right then b else a) right Q allowance y scale code :=by
  apply IntegralMixedSelectedWindowStability.selected_near_iff_of_stable x hm r φ hab right i code y _
  have H:=window_stable x hm r φ i (if right then b else a) right Q hQ allowance y scale hscale code
  simpa only [show ∀δ : ℝ,(if right then b else a)+(if right then -δ else δ)=
    (if right then b-δ else a+δ) from by intro δ;cases right <;> simp [sub_eq_add_neg]] using H

end LeanCanny.Connectivity.IntegralMixedSelectedCoordinateNearQueries
