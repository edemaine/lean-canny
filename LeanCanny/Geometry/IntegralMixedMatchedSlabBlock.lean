/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedMatchedSlabEndpoints
/-! # Literal midpoint blocks and endpoint records in the matched family -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Connectivity IntegralMixedHistory IntegralMixedCriticalSweep Set
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι κ : Type} {F : Frame n}

theorem joint_midpoint_block_same_family [Fintype κ]
    (x : State P S B m ι) (hm : m≤S) (atAnchor : State P S B (m+2) κ) (ha : m+2≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (F : Frame n) (HF : FreeNormal F) (HP : PrefixFrozen F) (HA : AtomicRows F m)
    (h g j : Fin (n+1)) (hfirst : h.val=F.frozen.card) (hh : h∉F.frozen)
    (hg : g∉(line F h).frozen) (hj : j∉(line F h).frozen)
    (values : Fin m→ℝ) (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (a b anchor : ℝ) (hab : a<b)
    (z : ((κ⊕FlatAffineCriticalStage.Variables (n+1))⊕Unit)→ℝ)
    (hz : ∀i,((criticalStep atAnchor ha (midpointData HA h g j hg hj).rule).sampler.rows i).eval₂
      (Int.castRingHom ℝ) z=0)
    (ψ : (criticalStep atAnchor ha (midpointData HA h g j hg hj).rule).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hψ : ∀i,ψ ((criticalStep atAnchor ha (midpointData HA h g j hg hj).rule).sampler.scalarPrefix.basis.generator i)=
      z ((criticalStep atAnchor ha (midpointData HA h g j hg hj).rule).sampler.scalar i)^
        UniformIntegralPowerSchedule.weights S (2^B) (m+3) i)
    (HN : ∀i,ψ ((criticalStep atAnchor ha (midpointData HA h g j hg hj).rule).bank.numerator i)/
      ((criticalStep atAnchor ha (midpointData HA h g j hg hj).rule).bank.denominator i:ℝ)=
        (Fin.cons anchor (Fin.cons b (Fin.cons a values)) : Fin (m+3)→ℝ) i)
    (M : MatchedSlabInterior x hm φ (line F h) h (Finset.mem_insert_self h F.frozen)
      g hg values a b ⟨(a+b)/2,by constructor <;> linarith⟩) :
    let e:=FrozenCoordinateOrdering.permutation (line F h).frozen
    let point:=IntegralMixedCriticalReadback.point (S:=S) (B:=B) (m:=m+2) z
    ∃i,
      i.val=point∘e ∧ M.curve i ((a+b)/2)=point∘e ∧
      M.code i=IntegralMixedFrozenFrameSectionCode.word (cutSource x F h) hm
        (cutRule x F h g hg) φ ((a+b)/2) i ∧
      (∀t,t∈Icc a b→(M.interior.arc i t).val=M.curve i t∘e.symm) ∧
      (M.interior.arc i ((a+b)/2)).val=point :=by
  let e:=FrozenCoordinateOrdering.permutation (line F h).frozen
  let point:=IntegralMixedCriticalReadback.point (S:=S) (B:=B) (m:=m+2) z
  let mid : Ioo a b:=⟨(a+b)/2,by constructor <;> linarith⟩
  have HR:=midpoint_block_anchors_sweep x hm atAnchor ha φ F HF HP HA h g j hfirst hh hg hj
    values H a b anchor z hz ψ hψ HN
  let i : IntegralMixedSelectedPhysicalFiber.physical (cutSource x F h) hm
      (cutRule x F h g hg) φ mid.val:=⟨point∘e,HR⟩
  have HE : (⟨M.curve i mid.val,M.physical i mid.val (Ioo_subset_Icc_self mid.property)⟩ :
      IntegralMixedSelectedPhysicalFiber.physical (cutSource x F h) hm
        (cutRule x F h g hg) φ mid.val)=i:=Subtype.ext (M.anchor i)
  have HW:=M.code_word i mid
  change IntegralMixedFrozenFrameSectionCode.word (cutSource x F h) hm (cutRule x F h g hg) φ mid.val
    ⟨M.curve i mid.val,M.physical i mid.val (Ioo_subset_Icc_self mid.property)⟩=M.code i at HW
  rw [HE] at HW
  refine ⟨i,rfl,M.anchor i,HW.symm,M.readback i,?_⟩
  rw [M.readback i mid.val (Ioo_subset_Icc_self mid.property),M.anchor i]
  funext k
  exact congrArg point (e.apply_symm_apply k)

theorem matched_branch_endpoint_real_extend [Fintype κ]
    (x : State P S B m ι) (hm : m≤S)
    (current : State P S B (m+3) κ) (hroom : m+3≤S) (hn : 0<n)
    (charge : ℕ) (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (HF : FreeNormal F) (HA : AtomicRows F m) (HP : PrefixFrozen F)
    (h : Fin (n+1)) (hfirst : h.val=F.frozen.card) (hh : h∉F.frozen)
    (g : Fin (n+1)) (hg : g∉(line F h).frozen)
    (values : Fin m→ℝ) (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (anchor a b : ℝ) (right : Bool) (t₀ : Ioo a b)
    (M : MatchedSlabInterior x hm φ (line F h) h (Finset.mem_insert_self h F.frozen)
      g hg values a b t₀)
    (i : IntegralMixedSelectedPhysicalFiber.physical (cutSource x F h) hm (cutRule x F h g hg) φ t₀.val)
    (z : κ→ℝ) (hz : ∀i,(current.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (ψ : current.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hψ : ∀i,ψ (current.sampler.scalarPrefix.basis.generator i)=
      z (current.sampler.scalar i)^UniformIntegralPowerSchedule.weights S (2^B) (m+3) i)
    (HN : ∀i,ψ (current.bank.numerator i)/(current.bank.denominator i:ℝ)=
      (Fin.cons anchor (Fin.cons b (Fin.cons a values)) : Fin (m+3)→ℝ) i) :
    let point:=M.curve i (if right then b else a)∘(FrozenCoordinateOrdering.permutation (line F h).frozen).symm
    let E:=jointEndpointFrame HA h right
    let d:=originalPointData (insert h F.frozen) (fun _=>false)
      (referencedEndpointRows HA.retained.retained.retained h (jointEndpointIndex m right)) g g hg hg
    let born:=criticalStep current hroom d.rule
    d.rule=pointRule E g hg g hg ∧
    (IntegralMixedCausalUnitRecordBits.record P hn (m+3) d.code hcap).template.command
      (commonDenominator current) (commonDenominator_ne_zero current)=.critical d.rule ∧
    ∃y,∃χ : born.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,(born.sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0) ∧
      (∀i,y (Sum.inl (Sum.inl i))=z i) ∧
      (∀i,y (Sum.inl (FlatAffineCriticalStage.ambient i))^
        UniformIntegralPowerSchedule.physical S (2^B) (m+3)=point i) ∧
      χ.comp (AdjoinRoot.ofAlgHom ℤ _)=ψ ∧
      (∀i,χ (born.sampler.scalarPrefix.basis.generator i)=
        y (born.sampler.scalar i)^UniformIntegralPowerSchedule.weights S (2^B) (m+4) i) ∧
      ∀i,χ (born.bank.numerator i)/(born.bank.denominator i:ℝ)=
        (Fin.cons (point g) (Fin.cons anchor (Fin.cons b (Fin.cons a values))) : Fin (m+4)→ℝ) i :=by
  exact branch_endpoint_real_extend x hm current hroom hn charge hdegree hcap φ HF HA HP h hfirst hh g hg
    values H anchor a b right (t₀.property.1.trans t₀.property.2).le (M.curve i) (M.physical i) z hz ψ hψ HN

end LeanCanny.Geometry.IntegralMixedFrozenFrame
