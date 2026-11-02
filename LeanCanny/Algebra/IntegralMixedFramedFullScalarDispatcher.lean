/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedFullScalarSelection
public import LeanCanny.Algebra.IntegralMixedFramedFullScalarProducers
/-! # The complete six-phase native scalar routine -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedFullScalarBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def nodes (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) :=
  [node0 P a D J h, node1 P a D J h, node2 P a D J h, node3 P a D J h, node4 P a D J h, node5 P a D J h]
noncomputable def machine (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) :=
  phaseDispatch (nodes P a D J h) zero

attribute [local irreducible] denominator scalar IntegralMixedFramedScalarLeadingBits.value
  IntegralMixedFramedOldHeightBits.value IntegralMixedFramedNativeHeightBits.model

theorem nodes_distinct (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) :
    ((nodes P a D J h).map PhaseNode.code).Nodup := by
  change ([0, 1, 2, 3, 4, 5] : List ℕ).Nodup
  decide

theorem machine_selected (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) (q : List Bool) :
    (machine P a D J h).selected q = true := by
  change (_ || (_ || (_ || (_ || (_ || (_ || true)))))) = true
  simp only [Bool.or_true]

theorem model0 (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) (q : List Bool)
    (hq : selected P .originalCoefficient q = true) : (machine P a D J h).model q = IntegralMixedFramedScalarLeadingBits.value P D J q := by
  exact phaseDispatch_model_selected (nodes P a D J h) zero q (node0 P a D J h) (nodes_distinct P a D J h) (by exact List.mem_cons_self) hq

theorem model1 (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) (q : List Bool)
    (hq : selected P .derivativeCoefficient q = true) : (machine P a D J h).model q = (denominator P a D J h).model q := by
  exact phaseDispatch_model_selected (nodes P a D J h) zero q (node1 P a D J h) (nodes_distinct P a D J h) (by exact List.mem_cons_of_mem _ (List.mem_cons_self)) ((denominator_selected P a D J h q).mpr hq)

theorem model2 (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) (q : List Bool)
    (hq : selected P .clearedHeight q = true) : (machine P a D J h).model q = IntegralMixedFramedOldHeightBits.value P D J q := by
  exact phaseDispatch_model_selected (nodes P a D J h) zero q (node2 P a D J h) (nodes_distinct P a D J h) (by exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))) hq

theorem model3 (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) (q : List Bool)
    (hq : selected P .monomialFactor q = true) : (machine P a D J h).model q = (scalar P a D J h .commonLeading).model q := by
  exact phaseDispatch_model_selected (nodes P a D J h) zero q (node3 P a D J h) (nodes_distinct P a D J h) (by exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))) ((scalar_selected P a D J h .commonLeading q).mpr hq)

theorem model4 (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) (q : List Bool)
    (hq : selected P .factorPower q = true) : (machine P a D J h).model q = IntegralMixedFramedNativeHeightBits.model P D J q := by
  exact phaseDispatch_model_selected (nodes P a D J h) zero q (node4 P a D J h) (nodes_distinct P a D J h) (by exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))) hq

theorem model5 (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) (q : List Bool)
    (hq : selected P .productEntry q = true) : (machine P a D J h).model q = (scalar P a D J h .originalScale).model q := by
  exact phaseDispatch_model_selected (nodes P a D J h) zero q (node5 P a D J h) (nodes_distinct P a D J h) (by exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))) ((scalar_selected P a D J h .originalScale q).mpr hq)

structure Replies (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (answer : List Bool → List Bool) : Prop where
  physical : IntegralMixedPhysicalScalarReplyBits.Matches P (physicalFamily P D J) answer
  virtual : IntegralMixedVirtualContextScalarReplyBits.Matches P (virtualFamily P D J) answer
  height : IntegralMixedFramedHeightCurrentBits.Matches P D J answer

theorem correct (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J)
    (answer : List Bool → List Bool) (hp : IntegralMixedFramedProducerActualBits.Matches P D J answer) (he : Replies P D J answer) :
    Correct (machine P a D J h) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  apply phaseDispatch_correct _ _ answer _ (zero_correct _ _)
  intro b hb
  simp only [nodes, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact leading_correct P a D J h answer
  · exact denominator_correct P a D J h answer hp
  · exact oldHeight_correct P a D J h answer hp
  · simp only [node3]
    unfold scalar
    apply choose_correct
    · exact IntegralMixedPhysicalNativeScalarBits.correct_of_matches P a (physicalFamily P D J) (physicalInput P a D J h) .commonLeading answer he.physical
    · exact IntegralMixedVirtualContextScalarBits.correct_of_matches P a (virtualFamily P D J) (virtualInput P a D J h) .commonLeading answer he.virtual
  · exact IntegralMixedFramedHeightCurrentBits.correct P a D J h.tables h.native h.represents h.height answer hp he.height
  · simp only [node5]
    unfold scalar
    apply choose_correct
    · exact IntegralMixedPhysicalNativeScalarBits.correct_of_matches P a (physicalFamily P D J) (physicalInput P a D J h) .originalScale answer he.physical
    · exact IntegralMixedVirtualContextScalarBits.correct_of_matches P a (virtualFamily P D J) (virtualInput P a D J h) .originalScale answer he.virtual
end LeanCanny.Algebra.IntegralMixedFramedFullScalarBits
