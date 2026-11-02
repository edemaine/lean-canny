/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.CanonicalAuxiliarySeededInitial
public import LeanCanny.Geometry.CanonicalAuxiliaryClosedSampling

/-! # Actual component sampling with the native original seed

Any positive seed covering the original word budget gives n actual tagged
limit births and exact newest-first bank readback in each nonempty original
clopen piece. The source at birth zero is literally the seeded source.
-/
@[expose] public section
namespace LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
open LeanCanny.Algebra LeanCanny.ETR IntegralMixedHistory
open AuxiliaryTiltedTerm FrozenAuxiliaryComponentSampling SampleFrame CoerciveComponentSampling
open scoped Classical
attribute [local irreducible] source

theorem exists_closed_seeded_sample {n S B D : ℕ} (t : Term) (ht : (term n t).degreeBound≤D)
    (ha : t.arity≤n) (hn : n≤S)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)≤2^B)
    (G : ℕ) (hG : 1≤G) (hword : wordBudget n D t≤G)
    (C : Set (Zeros (polynomial n t))) (hC : IsClopen C) (x0 : Zeros (polynomial n t)) (hx0 : x0∈C) :
    ∃ L : SampleFrame n S B D t ht, L.frozen=n ∧ L.birth=n ∧
      SampleTrace hcap (seededInitialFrame t ht hn hcap G hG hword) n L ∧
      ∃ p : Zeros (polynomial n t), p∈C ∧
        ∀ i : Fin n, ∃ j : Fin L.birth, j.val=frontIndex n i.val ∧
          p.val i=L.hom (L.state.bank.numerator j)/(L.state.bank.denominator j:ℝ) := by
  let F := seededInitialFrame t ht hn hcap G hG hword
  let C' : Set (slice (polynomial n t) F.frozen F.parameters) :=
    zeroProjection (polynomial n t) F.frozen F.parameters ⁻¹' C
  have HC' : IsClopen C' := hC.preimage (continuous_zeroProjection _ _ _)
  let y0 : slice (polynomial n t) F.frozen F.parameters := ⟨x0.val,x0.property,by intro i hi; change i.val<0 at hi; omega⟩
  have HY : y0∈C' := hx0
  obtain ⟨L,hEnd,hTrace,p,hp,hread⟩ := complete_readback F ha hcap C' HC' y0 HY
  have HF : F.Front := by
    intro i
    have HI := i.isLt
    change i.val<0 at HI
    omega
  have HFront := hTrace.front HF
  have Hbirth : L.birth=n := by
    have H := hTrace.birth_count
    change L.birth=0+(n-0) at H
    omega
  have Htrace : SampleTrace hcap F n L := by
    change SampleTrace hcap F (n-0) L at hTrace
    simpa only [Nat.sub_zero] using hTrace
  refine ⟨L,hEnd,Hbirth,Htrace,zeroProjection _ _ _ p,hp,?_⟩
  intro i
  let j : Fin L.birth := L.selector ⟨i.val,by rw [hEnd]; exact i.isLt⟩
  refine ⟨j,?_,hread i⟩
  have H := HFront (⟨i.val,by rw [hEnd]; exact i.isLt⟩:Fin L.frozen)
  simpa only [hEnd] using H

end LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
