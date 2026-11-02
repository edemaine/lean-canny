/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.CanonicalAuxiliarySampleTrace

/-! # Bounded recursive sampling of each original frozen clopen piece

Each recursive call freezes one further ORIGINAL coordinate. Actual tagged
limit births derive the next bank bound and causal source first. Clopen labels
pull back through literal slice inclusions, so the terminal tuple belongs to the
initial piece. The trace has exactly n-k births; no component-cost premise,
trajectory premise, new-bank inequality or independent root lifting is used.
-/
@[expose] public section
namespace LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
open LeanCanny.Algebra LeanCanny.ETR IntegralMixedHistory
open AuxiliaryTiltedTerm FrozenAuxiliaryComponentSampling SampleFrame
open scoped Classical
attribute [local irreducible] source
variable {n S B D : ℕ} {t : Term} {ht : (term n t).degreeBound≤D}

theorem complete_exists (F : SampleFrame n S B D t ht) (ha : t.arity≤n)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)≤2^B)
    (C : Set (slice (polynomial n t) F.frozen F.parameters)) (hC : IsClopen C)
    (x0 : slice (polynomial n t) F.frozen F.parameters) (hx0 : x0∈C) :
    ∃ L : SampleFrame n S B D t ht,
      SampleTrace hcap F (n-F.frozen) L ∧ L.frozen=n ∧
      ∃ p : slice (polynomial n t) F.frozen F.parameters, p∈C ∧ L.parameters=p.val := by
  have Main : ∀ r (F : SampleFrame n S B D t ht), n-F.frozen=r →
      ∀ (C : Set (slice (polynomial n t) F.frozen F.parameters)), IsClopen C →
      ∀ x0 : slice (polynomial n t) F.frozen F.parameters, x0∈C →
      ∃ L : SampleFrame n S B D t ht,
        SampleTrace hcap F (n-F.frozen) L ∧ L.frozen=n ∧
        ∃ p : slice (polynomial n t) F.frozen F.parameters, p∈C ∧ L.parameters=p.val := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro F hrem C hC x0 hx0
      by_cases hk : F.frozen<n
      · obtain ⟨b,hb,⟨W⟩⟩ := exists_cut F hk ha C hC x0 hx0
        let G := W.frame hcap
        have HG : G.frozen=F.frozen+1 := rfl
        have Hless : n-G.frozen<r := by rw [HG]; omega
        let C' : Set (slice (polynomial n t) G.frozen G.parameters) := nextLabel b C
        let x0' : slice (polynomial n t) G.frozen G.parameters := nextPoint b
        have HC' : IsClopen C' := nextLabel_clopen b C hC
        have HX' : x0'∈C' := nextPoint_mem_nextLabel b C hb
        obtain ⟨L,hTrace,hEnd,p,hp,hpar⟩ := ih (n-G.frozen) Hless G rfl C' HC' x0' HX'
        refine ⟨L,?_,hEnd,includeNext b p,hp,hpar⟩
        have HL : n-F.frozen=(n-G.frozen)+1 := by rw [HG]; omega
        rw [HL]
        exact SampleTrace.cut hk b W hTrace
      · have HK : F.frozen=n := Nat.le_antisymm F.frozen_le (Nat.le_of_not_gt hk)
        have HT : x0.val=F.parameters := by
          funext i
          exact x0.property.2 i (by have HI := i.isLt; omega)
        refine ⟨F,?_,HK,x0,hx0,HT.symm⟩
        have HR : n-F.frozen=0 := by omega
        rw [HR]
        exact SampleTrace.nil F
  exact Main (n-F.frozen) F rfl C hC x0 hx0

theorem complete_readback (F : SampleFrame n S B D t ht) (ha : t.arity≤n)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)≤2^B)
    (C : Set (slice (polynomial n t) F.frozen F.parameters)) (hC : IsClopen C)
    (x0 : slice (polynomial n t) F.frozen F.parameters) (hx0 : x0∈C) :
    ∃ L : SampleFrame n S B D t ht, ∃ hEnd : L.frozen=n,
      SampleTrace hcap F (n-F.frozen) L ∧
      ∃ p : slice (polynomial n t) F.frozen F.parameters, p∈C ∧
        ∀ i : Fin n, p.val i=L.hom (L.state.bank.numerator (L.selector ⟨i.val,by omega⟩))/
          (L.state.bank.denominator (L.selector ⟨i.val,by omega⟩):ℝ) := by
  obtain ⟨L,hTrace,hEnd,p,hp,hpar⟩ := complete_exists F ha hcap C hC x0 hx0
  refine ⟨L,hEnd,hTrace,p,hp,?_⟩
  intro i
  have hi : i.val<L.frozen := by rw [hEnd]; exact i.isLt
  exact (congrFun hpar.symm i).trans ((L.correlated i hi).trans (L.recovers _).symm)

end LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
