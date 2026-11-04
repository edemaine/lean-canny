/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalDegenerateLevel
/-! # A retained equal-endpoint level may choose a new child-critical point

Only child criticality is required. The chosen point need not be critical
for the previous objective. Both endpoint values are the same old producer;
no fresh cut choice, proper slab or matched-branch premise is introduced.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFrozenFrame
open IntegralMixedChronologicalFrame IntegralHistorySampler UniformIntegralPowerSchedule
open IntegralMixedChosenLocalRealization IntegralMixedOptionalEndpoints IntegralMixedPointCompanion
open IntegralMixedFullHistoryScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m :ℕ} {P :SpatialSource n} {ι :Type} [Fintype ι]

noncomputable def retainedPair (x :State P S B m ι) (hm :m≤S) (hn :0<n)
    (hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (d :Descriptor n m) (z :ι→ℝ) (hz :∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ :∀i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values :Fin m→ℝ) (H :∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (u :Fin m):NativePair x d z φ values (.retained u) (.retained u) hn hcap:=by
  let R :PairResult x d.frame z φ values (values u) (values u) hn hcap:={
    commands:=[],count:=(by simp),room:=(by simp;omega),codes:=[],code_count:=rfl
    code_size:=(by intro code hc;simp only [List.not_mem_nil] at hc)
    decode:=rfl,tuple:=z,hom:=φ,roots:=hz,old_raw:=fun _=>rfl,old_hom:=(by rfl)
    generators:=hφ,nextValues:=values,quotients:=H,frame:=d.frame
    atomic:=d.atomic,prefixFrozen:=d.prefix_frozen,freeNormal:=d.free_normal
    frozen:=rfl,slice_eq:=rfl,left:=u,right:=u,left_value:=rfl,right_value:=rfl}
  refine {
    leftSpec:=IntegralMixedRoadmapEndpointSyntax.retainedSpec d u
    rightSpec:=IntegralMixedRoadmapEndpointSyntax.retainedSpec d u,result:=R
    left_good:=IntegralMixedRoadmapEndpointSyntax.retainedSpec_good d u B _ m
    right_good:=IntegralMixedRoadmapEndpointSyntax.retainedSpec_good d u B _ _
    left_fresh:=IntegralMixedRoadmapEndpointSyntax.retainedSpec_fresh d u
    right_fresh:=IntegralMixedRoadmapEndpointSyntax.retainedSpec_fresh d u
    left_producer:=IntegralMixedRoadmapEndpointSyntax.retainedSpec_producer d u
    right_producer:=IntegralMixedRoadmapEndpointSyntax.retainedSpec_producer d u
    count:=rfl,codes:=?_,frame:=rfl,left_reference:=?_,right_reference:=?_}
  · simp only [IntegralMixedRoadmapEndpointSyntax.retainedSpec_codes,List.nil_append]
    rfl
  · change u.val=m+0-1-IntegralMixedRoadmapEndpointSyntax.field
      (IntegralMixedRoadmapEndpointSyntax.retainedSpec d u) 1
    rw [IntegralMixedRoadmapEndpointSyntax.retainedSpec_producer]
    have HU:=u.isLt
    omega
  · change u.val=m+0-1-IntegralMixedRoadmapEndpointSyntax.field
      (IntegralMixedRoadmapEndpointSyntax.retainedSpec d u) 1
    rw [IntegralMixedRoadmapEndpointSyntax.retainedSpec_producer]
    have HU:=u.isLt
    omega

variable {x :State P S B m ι} {d :Descriptor n m} {z :ι→ℝ}
  {φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {values :Fin m→ℝ} {endpoint :Endpoint m}
  {hn :0<n} {hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}

theorem NativePair.exists_child_critical_level
    (R :NativePair x d z φ values endpoint endpoint hn hcap)
    (hk :d.labels.length<n+1) (g :Fin (n+1))
    (hg :g∉(line d.frame (IntegralMixedChronologicalSweepFrame.next d hk)).frozen)
    (charge :ℕ) (hdegree :P.degree=BoundedZeroSource.powerDegree charge) (HG :g.val=d.labels.length+1)
    (p :Fin (n+1)→ℝ) (HS :p∈slice P d.frame values)
    (Hh :p (IntegralMixedChronologicalSweepFrame.next d hk)=endpoint.value values)
    (Hgrad :∀i,i∉insert (IntegralMixedChronologicalSweepFrame.next d hk) d.frame.frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) p=0)
    (horizon :m+R.result.commands.length+2+2*(R.orderedFree hk).length≤S+1):
    let hp :m+R.result.commands.length≤S:=by omega
    let room :m+R.result.commands.length+1+(R.orderedFree hk).length≤S+1:=by omega
    let hroom :m+R.result.commands.length+1+(R.orderedFree hk).length≤S:=by omega
    let childRoom :m+R.result.commands.length+1+(R.orderedFree hk).length+1+(R.orderedFree hk).length≤S+1:=by omega
    ∃A :R.result.MidpointCaptures hp (IntegralMixedChronologicalSweepFrame.next d hk) g g hg hg
      p (R.orderedFree hk) room,∀side,
      ∃_E :R.LevelChildCaptures hk g hg hp p room A hroom side p childRoom,
        Decodes x hn hcap (R.levelCommands hk g hg side) (R.level_room hk g hg side childRoom)
          (R.levelCodes hk g hg side) ∧
        WordList.encode (R.levelCodes hk g hg side).reverse=IntegralMixedRoadmapLevel.compiled n (R.levelPacket side) ∧
        HEq (continueRun x (R.levelCommands hk g hg side) (R.level_room hk g hg side childRoom))
          (R.levelFinalState hk g hg hp room hroom side childRoom):=by
  dsimp only
  let h:=IntegralMixedChronologicalSweepFrame.next d hk
  have hh :h∉d.frame.frozen:=IntegralMixedChronologicalSweepFrame.next_free d hk
  have hfirst :h.val=d.frame.frozen.card:=d.frozen_card.symm
  obtain ⟨A,HE⟩:=R.result.exists_degenerate_program charge hdegree h hfirst hh g g hg hg p HS Hh Hgrad
    (by omega) (R.orderedFree hk) (by omega) (by omega) (by omega)
  refine ⟨A,?_⟩
  intro side
  obtain ⟨E⟩:=HE side
  have E' :R.LevelChildCaptures hk g hg (by omega) p (by omega) A (by omega) side p (by omega):=E
  exact ⟨E',R.level_decodes hk g hg side (R.level_room hk g hg side (by omega)),
    R.levelWord_compiled hk g hg HG side,R.level_run_heq hk g hg (by omega) (by omega) (by omega) side (by omega)⟩

end LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
