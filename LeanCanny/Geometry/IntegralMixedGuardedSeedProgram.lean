/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedGuardedLocalProgram
public import LeanCanny.Encoding.IntegralMixedCanonicalPaddingSeed
/-! # Every canonical seed padding birth has a constructed correlation receipt -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedOptionalEndpoints
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFullHistoryScript
open IntegralMixedChosenLocalRealization IntegralHistorySampler UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m :ℕ} {P :SpatialSource n} {ι :Type} [Fintype ι]

theorem exists_guarded_seeds (x :State P S B m ι) (hn :0<n)
    (charge :ℕ) (hdegree :P.degree=BoundedZeroSource.powerDegree charge)
    (hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (z :ι→ℝ) (hz :∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ :∀i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values :Fin m→ℝ) (H :∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (p :Fin (n+1)→ℝ)
    (hp :(FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) p=0)
    (hg :∀i,i≠0→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂ (Int.castRingHom ℝ) p=0)
    (k :ℕ) (room :m+(List.replicate k (.critical (IntegralMixedCanonicalPaddingSeed.rule n) :Command P B)).length≤S+1) :
    ∃y,∃ψ,∃next,
      GuardedProgram x hn hcap z φ values (List.replicate k (.critical (IntegralMixedCanonicalPaddingSeed.rule n)))
        room (List.replicate k (IntegralMixedChronologicalFrameCode.code n [] 0 0)) y ψ next:=by
  induction k with
  | zero=>exact ⟨z,φ,values,GuardedProgram.nil room⟩
  | succ k ih=>
    let cs :List (Command P B):=List.replicate k (.critical (IntegralMixedCanonicalPaddingSeed.rule n))
    have HM :m+cs.length≤S:=by simp only [cs,List.length_replicate] at room ⊢;omega
    have HT :m+cs.length≤S+1:=HM.trans (Nat.le_succ _)
    obtain ⟨y,ψ,next,trace⟩:=ih HT
    let before:=continueRun x cs HT
    let d:=IntegralMixedCanonicalPaddingSeed.data n (m+cs.length)
    have HF :(data before HM d.rule).free=0:=by
      apply Fin.ext
      change 0+0%(n+1)=0
      simp only [Nat.zero_mod,Nat.add_zero]
    let w :CriticalChoice before HM ψ:={
      record:=d,charge:=charge,degree_eq:=hdegree,point:=p
      frozen:=by intro i hi;change i.val<0 at hi;omega
      zero:=hp
      gradient:=by intro i _ hi;exact hg i (fun he=>hi (he.trans HF.symm))}
    have HW :w.value before HM ψ=p 0:=by
      apply congrArg p
      apply Fin.ext
      change 0+0%(n+1)=0
      simp only [Nat.zero_mod,Nat.add_zero]
    obtain ⟨r⟩:=critical_receipt before HM hn hcap y (trace.roots hz) ψ (trace.generators hφ) next (trace.quotients H) w
    have HCODE :w.record.code=IntegralMixedChronologicalFrameCode.code n [] 0 0:=
      IntegralMixedCanonicalPaddingSeed.data_code n (m+cs.length)
    rw [HW,HCODE] at r
    obtain ⟨c,hdec,y',ψ',hy',hold,hrestrict,hgen,hvals,hguard⟩:=r
    have HC :c=(.critical (IntegralMixedCanonicalPaddingSeed.rule n) :Command P B):=
      hdec.symm.trans (IntegralMixedCanonicalPaddingSeed.command P hn hcap
        (commonDenominator before) (commonDenominator_ne_zero before))
    cases HC
    exact ⟨y',ψ',Fin.cons (p 0) next,GuardedProgram.cons trace HM (p 0)
      (IntegralMixedChronologicalFrameCode.code n [] 0 0)
      ⟨.critical (IntegralMixedCanonicalPaddingSeed.rule n),hdec,y',ψ',hy',hold,hrestrict,hgen,hvals,hguard⟩⟩

end LeanCanny.Geometry.IntegralMixedOptionalEndpoints
