/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedDegenerateCodeSequence
public import LeanCanny.Geometry.IntegralMixedFrozenFrameSampling
/-! # Critical-point descent and singular-safe equal-height boundary samples

Component membership is an output of the existing compact sampler, not a
primitive validity or cost premise. No regularity of the boundary fiber is
assumed.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedOptionalEndpoints
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Connectivity IntegralMixedHistory
open LeanCanny.Geometry.IntegralMixedFrozenFrame
open IntegralMixedFullHistoryScript IntegralMixedCausalRowConstructor Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
variable {x : State P S B m ι} {F : Frame n} {z : ι→ℝ}
    {φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {values : Fin m→ℝ}
    {c : ℝ} {hn : 0<n}
    {hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}

theorem parent_critical_height (HF : FreeNormal F) (h : Fin (n+1)) (hh : h∉F.frozen)
    (p : Fin (n+1)→ℝ) (HS : p∈slice P F values) (Hh : p h=c)
    (HG : ∀i,i∉F.frozen→i≠h→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) p=0) :
    c∈realCriticalValues P (line F h) values h:=
  (line_realCriticalValues_iff P F values h hh HF c).mpr ⟨p,HS,Hh,HG⟩

theorem PairResult.exists_parent_critical_degenerate_program
    (R : PairResult x F z φ values c c hn hcap)
    (charge : ℕ) (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (h : Fin (n+1)) (hfirst : h.val=F.frozen.card) (hh : h∉F.frozen)
    (g j : Fin (n+1)) (hg : g∉(line F h).frozen) (hj : j∉(line F h).frozen)
    (p : Fin (n+1)→ℝ) (HS : p∈slice P F values) (Hh : p h=c)
    (HG : ∀i,i∉F.frozen→i≠h→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) p=0)
    (hp : m+R.commands.length≤S)
    (js : List (IntegralMixedPointCompanion.Free (insert h R.frame.frozen)))
    (room : m+R.commands.length+1+js.length≤S+1)
    (hroom : m+R.commands.length+1+js.length≤S)
    (childRoom : m+R.commands.length+1+js.length+1+js.length≤S+1) :
    ∃A : R.MidpointCaptures hp h g j hg hj p js room,∀right,
      Nonempty (R.ChildCaptures hp h g j hg hj p js room A hroom right childRoom):=
  R.exists_degenerate_program charge hdegree h hfirst hh g j hg hj p HS Hh
    (critical_after_freezing h g p HG) hp js room hroom childRoom

theorem PairResult.exists_component_degenerate_program
    (R : PairResult x F z φ values c c hn hcap) (hm : m≤S)
    (charge : ℕ) (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (HF : FreeNormal F) (h : Fin (n+1)) (hfirst : h.val=F.frozen.card) (hh : h∉F.frozen)
    (g j : Fin (n+1)) (hg : g∉(line F h).frozen) (hj : j∉(line F h).frozen)
    (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (proper : IsProperMap (fun p : Fin (n+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) p))
    (y : Fin (n+1)→ℝ) (hy : y∈slice P F values) (hyh : y h=c)
    (hp : m+R.commands.length≤S)
    (js : List (IntegralMixedPointCompanion.Free (insert h R.frame.frozen)))
    (room : m+R.commands.length+1+js.length≤S+1)
    (hroom : m+R.commands.length+1+js.length≤S)
    (childRoom : m+R.commands.length+1+js.length+1+js.length≤S+1) :
    ∃p,p∈connectedComponentIn (slice P F values∩{p | p h=c}) y ∧
      ∃A : R.MidpointCaptures hp h g j hg hj p js room,∀right,
        Nonempty (R.ChildCaptures hp h g j hg hj p js room A hroom right childRoom):=by
  have HY : y∈shiftedSlice P (line F h) values h c:=by
    rw [line_slice P F h hh HF values c]
    exact ⟨hy,hyh⟩
  have Hfiber:=shiftedSlice_fiber P (line F h) values h (Finset.mem_insert_self h F.frozen) c
  have HY' : y∈slice P (coarse (line F h) h) values∩{p | projection (line F h) values h p=c}:=by
    rw [←Hfiber]
    exact HY
  obtain ⟨p,HC,Hphys⟩:=exists_component_sample x hm φ (line F h) h (Finset.mem_insert_self h F.frozen)
    g hg values H c y HY' proper
  have HE : shiftedSlice P (line F h) values h c=slice P F values∩{p | p h=c}:=
    line_slice P F h hh HF values c
  rw [←Hfiber,HE] at HC
  obtain ⟨HS,Hh,HG⟩:=selected_point_endpoint x hm φ F h hh HF g hg values H c
    (p∘FrozenCoordinateOrdering.permutation (line F h).frozen) Hphys
  have HP : (p∘FrozenCoordinateOrdering.permutation (line F h).frozen)∘
      (FrozenCoordinateOrdering.permutation (line F h).frozen).symm=p:=by
    funext i
    exact congrArg p ((FrozenCoordinateOrdering.permutation (line F h).frozen).apply_symm_apply i)
  rw [HP] at HS Hh HG
  obtain ⟨A,HA⟩:=R.exists_degenerate_program charge hdegree h hfirst hh g j hg hj p HS Hh HG
    hp js room hroom childRoom
  exact ⟨p,HC,A,HA⟩

end LeanCanny.Geometry.IntegralMixedOptionalEndpoints
