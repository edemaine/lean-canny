/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalFreshCriticalEndpoint
public import LeanCanny.Geometry.IntegralMixedMatchedOptionalAnchorCaptures
/-! # An arbitrary actual critical point realizes an atomic frame and captures

The chronological descriptor and its record bytes are fixed first. Choosing
a different critical point changes the sampled roots, not the old labels.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalFrame
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFrozenFrame
open IntegralMixedCausalRowConstructor IntegralMixedFullHistoryScript IntegralMixedChosenLocalRealization
open IntegralMixedOptionalEndpoints IntegralHistorySampler UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

noncomputable abbrev AtomicCaptures (x : State P S B m ι) (hm : m≤S)
    (d : Descriptor n m) (g : Fin (n+1)) (hg : g∉d.frame.frozen)
    (hn : 0<n) (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (z : ι→ℝ) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (old : Fin m→ℝ)
    (p : Fin (n+1)→ℝ) (js : List (IntegralMixedPointCompanion.Free d.frame.frozen))
    (room : m+1+js.length≤S+1) :=
  let data:=IntegralMixedChronologicalFrameCode.data d g g hg hg
  AnchoredCaptures x (step x hm (.critical data.rule)) (scalarLift x hm (.critical data.rule))
    ((IntegralMixedCausalUnitRecordBits.record P hn m data.code hcap).template.command
      (commonDenominator x) (commonDenominator_ne_zero x)=.critical data.rule)
    d.frame.frozen (fun _=>false) (IntegralMixedPointCompanion.shiftRows (fun i=>Row.single (d.atom i)) 1)
    ⟨g,hg⟩ z φ old p g js room hn hcap

theorem exists_atomic_captures (x : State P S B m ι) (hm : m≤S) (d : Descriptor n m)
    (g : Fin (n+1)) (hg : g∉d.frame.frozen) (hn : 0<n)
    (charge : ℕ) (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (z : ι→ℝ) (hz : ∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (old : Fin m→ℝ) (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=old i)
    (p : Fin (n+1)→ℝ) (hp : p∈slice P d.frame old)
    (hgcrit : ∀i,i∉d.frame.frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) p=0)
    (js : List (IntegralMixedPointCompanion.Free d.frame.frozen)) (room : m+1+js.length≤S+1) :
    Nonempty (AtomicCaptures x hm d g hg hn hcap z φ old p js room) :=by
  obtain ⟨_,HC,y,ψ,HY,Hold,Hphys,HR,Hψ,HV⟩:=
    PrefixFrozen.real_extend_original_point x hm hn charge hdegree hcap
      d.frame.frozen (fun _=>false) (fun i=>Row.single (d.atom i)) d.prefix_frozen g g hg hg
      z hz φ hφ old H p hp hgcrit
  let data:=IntegralMixedChronologicalFrameCode.data d g g hg hg
  let born:=step x hm (.critical data.rule)
  have HP : PrefixFrozen (originalFrame d.frame.frozen (fun _=>false)
      (IntegralMixedPointCompanion.shiftRows (fun i=>Row.single (d.atom i)) 1)):=d.prefix_frozen.retained
  have HS : p∈slice P (originalFrame d.frame.frozen (fun _=>false)
      (IntegralMixedPointCompanion.shiftRows (fun i=>Row.single (d.atom i)) 1)) (Fin.cons (p g) old):=by
    change p∈slice P (IntegralMixedPointCompanion.frame d.frame.frozen (fun _=>false)
      (fun i=>Row.single (d.atom i)) 1) (Fin.cons (p g) old)
    rw [IntegralMixedPointCompanion.frame_succ,slice_retained]
    exact hp
  obtain ⟨⟨C⟩,HD⟩:=IntegralMixedPointCompanion.exists_realized born d.frame.frozen (fun _=>false)
    (IntegralMixedPointCompanion.shiftRows (fun i=>Row.single (d.atom i)) 1) ⟨g,hg⟩
    hn charge hdegree hcap HP y HY ψ Hψ (Fin.cons (p g) old) HV p HS hgcrit js room
  exact ⟨⟨⟨HC,y,ψ,HY,Hold,Hphys,HR,Hψ,HV⟩,C,HD⟩⟩

end LeanCanny.Geometry.IntegralMixedChronologicalFrame
