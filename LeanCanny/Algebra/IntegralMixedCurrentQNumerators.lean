/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCurrentQCoordinateScaling
public import LeanCanny.Algebra.PurePowerAnnihilatorMap
/-! # The selected frozen numerators have the actual common Q scaling -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCurrentQCoordinateScaling
open IntegralMixedHistory IntegralMixedFullHistoryScript IntegralMixedCriticalSweep Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem map_numerators {R A : Type*} [CommRing R] [CommRing A]
    (φ : R→+*A) (scales : Fin (n+1)→ℤ) (H : Fin (n+1)→R) (i : ℕ) :
    φ (CoordinateFrozenCriticalElimination.numerators scales H i)=
      CoordinateFrozenCriticalElimination.numerators scales (fun j=>φ (H j)) i:=by
  unfold CoordinateFrozenCriticalElimination.numerators
  split_ifs <;> simp only [CommonIntegerDenominator.numerator,map_mul,map_intCast,map_zero]

theorem selected_numerators (x : State P S B m ι) (hm : m≤S) (c : Command P B) (hn : m+1≤S)
    (r : Rule n) (hr : r.slope=commonDenominator x)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (ψ : (step x hm c).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (values : Fin m→ℝ) (a : ℝ)
    (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (HN : ∀ i,ψ ((step x hm c).bank.numerator i)/((step x hm c).bank.denominator i:ℝ)=
      (Fin.cons a values : Fin (m+1)→ℝ) i) (i : ℕ) :
    (CoordinateFrozenCriticalElimination.numerators
      (data (step x hm c) hn (shiftRule x hm c r).critical).scales
      (heights (step x hm c) (shiftRule x hm c r)) i).map ψ.toRingHom=
      C ((leading x hm c:ℝ)^(n+1))*
        (CoordinateFrozenCriticalElimination.numerators (data x hm r.critical).scales (heights x r) i).map φ.toRingHom :=by
  change (Polynomial.mapRingHom ψ.toRingHom) _ = _ * (Polynomial.mapRingHom φ.toRingHom) _
  rw [map_numerators (Polynomial.mapRingHom ψ.toRingHom),map_numerators (Polynomial.mapRingHom φ.toRingHom)]
  have HS : (data (step x hm c) hn (shiftRule x hm c r).critical).scales=
      fun i=>leading x hm c*(data x hm r.critical).scales i:=by
    funext i
    exact scales x hm c hn r i
  have HH : (fun i=>(Polynomial.mapRingHom ψ.toRingHom) (heights (step x hm c) (shiftRule x hm c r) i))=
      fun i=>C (leading x hm c:ℝ)*(heights x r i).map φ.toRingHom:=by
    funext i
    exact selected_heights x hm c r hr φ ψ values a H HN i
  rw [HS,HH]
  unfold CoordinateFrozenCriticalElimination.numerators
  split_ifs with hi
  · have HL : (leading x hm c:Polynomial ℝ)=C (leading x hm c:ℝ):=(Polynomial.C_eq_intCast _).symm
    simpa only [HL,←map_pow,Polynomial.coe_mapRingHom] using numerator_scale
      (data x hm r.critical).scales (fun j=>(heights x r j).map φ.toRingHom) (leading x hm c) ⟨i,hi⟩
  · simp only [mul_zero]

omit [Fintype ι] in
theorem selected_coordinate (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) :
    selected x hm r j φ=
      ClearedCoordinateCritical.annihilator P.degree
        (CoordinateFrozenCriticalElimination.denominator (data x hm r.critical).scales:Polynomial ℝ)
        (fun i=>(CoordinateFrozenCriticalElimination.numerators (data x hm r.critical).scales (heights x r) i).map φ.toRingHom)
        r.critical.offset.val (fit r).le
        (P.low.map (Int.castRingHom (Polynomial ℝ))) (P.leading:Polynomial ℝ) (objective r) j :=by
  unfold selected coordinate CoordinateFrozenCriticalElimination.polynomial
  rw [PurePowerAnnihilatorMap.cleared]
  simp only [map_intCast]
  congr 1
  rw [MvPolynomial.map_map]
  apply congrArg (fun f : ℤ→+*Polynomial ℝ=>P.low.map f)
  exact RingHom.ext_int _ _

end LeanCanny.Algebra.IntegralMixedCurrentQCoordinateScaling
