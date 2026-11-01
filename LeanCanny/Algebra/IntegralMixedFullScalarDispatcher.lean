/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullScalarSelection
public import LeanCanny.Algebra.IntegralMixedFullScalarProducers
/-! # The complete six-phase native scalar routine -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullScalarBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def nodes (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) :=
  [node0 P a D h, node1 P a D h, node2 P a D h, node3 P a D h, node4 P a D h, node5 P a D h]
noncomputable def machine (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) :=
  phaseDispatch (nodes P a D h) zero

theorem nodes_distinct (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) :
    ((nodes P a D h).map PhaseNode.code).Nodup := by
  change ([0, 1, 2, 3, 4, 5] : List ℕ).Nodup
  decide

theorem machine_selected (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) (q : List Bool) :
    (machine P a D h).selected q = true := by
  change (_ || (_ || (_ || (_ || (_ || (_ || true)))))) = true
  simp only [Bool.or_true]

theorem model0 (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) (q : List Bool)
    (hq : selected P .originalCoefficient q = true) : (machine P a D h).model q = IntegralMixedFullScalarLeadingBits.value P D q := by
  exact phaseDispatch_model_selected (nodes P a D h) zero q (node0 P a D h) (nodes_distinct P a D h) (by exact List.mem_cons_self) hq

theorem model1 (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) (q : List Bool)
    (hq : selected P .derivativeCoefficient q = true) : (machine P a D h).model q = (denominator P a D h).model q := by
  exact phaseDispatch_model_selected (nodes P a D h) zero q (node1 P a D h) (nodes_distinct P a D h) (by exact List.mem_cons_of_mem _ (List.mem_cons_self)) ((denominator_selected P a D h q).mpr hq)

theorem model2 (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) (q : List Bool)
    (hq : selected P .clearedHeight q = true) : (machine P a D h).model q = IntegralMixedOldHeightBits.value P D q := by
  exact phaseDispatch_model_selected (nodes P a D h) zero q (node2 P a D h) (nodes_distinct P a D h) (by exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))) hq

theorem model3 (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) (q : List Bool)
    (hq : selected P .monomialFactor q = true) : (machine P a D h).model q = (scalar P a D h .commonLeading).model q := by
  exact phaseDispatch_model_selected (nodes P a D h) zero q (node3 P a D h) (nodes_distinct P a D h) (by exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))) ((scalar_selected P a D h .commonLeading q).mpr hq)

theorem model4 (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) (q : List Bool)
    (hq : selected P .factorPower q = true) : (machine P a D h).model q = IntegralMixedNativeHeightBits.model P D q := by
  exact phaseDispatch_model_selected (nodes P a D h) zero q (node4 P a D h) (nodes_distinct P a D h) (by exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))) hq

theorem model5 (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) (q : List Bool)
    (hq : selected P .productEntry q = true) : (machine P a D h).model q = (scalar P a D h .originalScale).model q := by
  exact phaseDispatch_model_selected (nodes P a D h) zero q (node5 P a D h) (nodes_distinct P a D h) (by exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))) ((scalar_selected P a D h .originalScale q).mpr hq)

structure Replies (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (answer : List Bool → List Bool) : Prop where
  physical : IntegralMixedPhysicalScalarReplyBits.Matches P (physicalFamily P D) answer
  virtual : IntegralMixedVirtualContextScalarReplyBits.Matches P (virtualFamily P D) answer
  height : IntegralMixedHeightCurrentBits.Matches P D answer

theorem correct (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) (hp : IntegralMixedProducerActualBits.Matches P D answer) (he : Replies P D answer) :
    Correct (machine P a D h) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  apply phaseDispatch_correct _ _ answer _ (zero_correct _ _)
  intro b hb
  simp only [nodes, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact leading_correct P a D h answer
  · exact denominator_correct P a D h answer hp
  · exact oldHeight_correct P a D h answer hp
  · apply choose_correct
    · exact IntegralMixedPhysicalNativeScalarBits.correct_of_matches P a (physicalFamily P D) h.physical .commonLeading answer he.physical
    · exact IntegralMixedVirtualContextScalarBits.correct_of_matches P a (virtualFamily P D) (IntegralMixedFullHistoryFamilyBits.inputMetadata P a D h.full) .commonLeading answer he.virtual
  · exact IntegralMixedHeightCurrentBits.correct P a D h.full h.height answer hp he.height
  · apply choose_correct
    · exact IntegralMixedPhysicalNativeScalarBits.correct_of_matches P a (physicalFamily P D) h.physical .originalScale answer he.physical
    · exact IntegralMixedVirtualContextScalarBits.correct_of_matches P a (virtualFamily P D) (IntegralMixedFullHistoryFamilyBits.inputMetadata P a D h.full) .originalScale answer he.virtual
end LeanCanny.Algebra.IntegralMixedFullScalarBits
