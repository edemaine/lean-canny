/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.CanonicalAuxiliaryInitialFrame
public import LeanCanny.Geometry.CanonicalAuxiliaryRecursiveSampling
public import LeanCanny.Geometry.CanonicalAuxiliaryTraceReadback

/-! # Actual bounded original-coordinate histories meet each closed-source piece

Starting from the empty bank, exactly n tagged limit births recover a whole
original zero in any prescribed nonempty clopen piece. The once-augmented term
and single initial spatial cap are fixed throughout. This is semantic coverage
by actual arithmetic histories; it does not assume a native component oracle or
identify the terminal source reframe with a family's default source.
-/
@[expose] public section
namespace LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
open LeanCanny.Algebra LeanCanny.ETR IntegralMixedHistory
open AuxiliaryTiltedTerm FrozenAuxiliaryComponentSampling SampleFrame CoerciveComponentSampling
open scoped Classical
attribute [local irreducible] source
variable {n S B D : ℕ} {t : Term} {ht : (term n t).degreeBound≤D}

noncomputable def zeroProjection (q : MvPolynomial (Fin n) ℝ) (k : ℕ) (a : Fin n → ℝ) :
    slice q k a → Zeros q := fun y => ⟨y.val,y.property.1⟩

theorem continuous_zeroProjection (q : MvPolynomial (Fin n) ℝ) (k : ℕ) (a : Fin n → ℝ) :
    Continuous (zeroProjection q k a) := continuous_subtype_val.subtype_mk _

theorem exists_closed_sample (t : Term) (ht : (term n t).degreeBound≤D) (ha : t.arity≤n) (hn : n≤S)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)≤2^B)
    (C : Set (Zeros (polynomial n t))) (hC : IsClopen C) (x0 : Zeros (polynomial n t)) (hx0 : x0∈C) :
    ∃ L : SampleFrame n S B D t ht, L.frozen=n ∧ L.birth=n ∧
      SampleTrace hcap (initialFrame t ht hn hcap) n L ∧
      ∃ p : Zeros (polynomial n t), p∈C ∧
        ∀ i : Fin n, ∃ j : Fin L.birth, j.val=frontIndex n i.val ∧
          p.val i=L.hom (L.state.bank.numerator j)/(L.state.bank.denominator j:ℝ) := by
  let F := initialFrame t ht hn hcap
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
    change L.birth=0+n at H
    simpa only [Nat.zero_add] using H
  have Htrace : SampleTrace hcap F n L := by
    simpa only [F,initialFrame,Nat.sub_zero] using hTrace
  refine ⟨L,hEnd,Hbirth,Htrace,zeroProjection _ _ _ p,hp,?_⟩
  intro i
  let j : Fin L.birth := L.selector ⟨i.val,by rw [hEnd]; exact i.isLt⟩
  refine ⟨j,?_,hread i⟩
  have H := HFront (⟨i.val,by rw [hEnd]; exact i.isLt⟩:Fin L.frozen)
  simpa only [hEnd] using H

end LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
