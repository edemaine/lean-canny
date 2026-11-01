/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalFlatGenericGrid
/-! # Flat Euler controllers for arbitrary actual creating sources -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalCoordinateProductBits
open LeanCanny.Encoding LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem program_value_at (S : IntegralCriticalGradientBits.Source) (task answer : List Bool → List Bool) (p : List Bool)
    (he : FixedWidthCoordinateMulBits.positive (arity S) (width S) selected targetWord p →
      answer (task (gradientQuery (FixedWidthCoordinateMulBits.query (arity S) (width S) selected targetWord p))) =
        (IntegralCriticalGradientBits.family S).value
          (gradientQuery (FixedWidthCoordinateMulBits.query (arity S) (width S) selected targetWord p))) :
    (program S task).value answer p = value S p := by
  unfold program value
  by_cases hp : FixedWidthCoordinateMulBits.positive (arity S) (width S) selected targetWord p
  · simpa only [SingleCall.Program.value, FixedWidthCoordinateMulBits.program, FixedWidthCoordinateMulBits.value,
      hp, decide_true, ite_true, pairSnd_pair, Function.comp_apply] using he hp
  · simp only [SingleCall.Program.value, FixedWidthCoordinateMulBits.program, FixedWidthCoordinateMulBits.value,
      hp, decide_false, Bool.false_eq_true, ite_false]

end LeanCanny.Algebra.IntegralCriticalCoordinateProductBits

namespace LeanCanny.Algebra.IntegralCriticalFlatGenericEulerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalFlatEulerRowsBits IntegralCriticalFlatEulerBits
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalHistoryTask.rank IntegralCriticalHistoryTask.Tasks
noncomputable def objectiveProgram (P : IntegralCriticalHistoryTask.Parameters)
    (F : IntegralEulerBits.Source) : RecursiveFold.Program :=
  IntegralEulerBits.ObjectiveStage.program F
    (next P .frozenLower) (next P .eulerSum)

theorem objective_certificates (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : IntegralEulerBits.Source)
    (h : IntegralEulerBits.Access F) :
    (objectiveProgram P F).controller.Certificates
      (encQ := Turing.MultiTapeTM.encBits) (encS := RecursiveFold.encState) :=
  IntegralEulerBits.ObjectiveStage.certificates _ h
    _ _ (next_FP P a .frozenLower) (next_FP P a .eulerSum)

theorem objective_post_packet (S : IntegralEulerBits.Source) (c : List Bool) (x y : ZMod (S.modulus c)) :
    IntegralEulerBits.ObjectiveStage.post S (pair c (pair (residueBits x) (residueBits y))) =
      residueBits (x * (S.allowance c : ZMod (S.modulus c)) - y) := by
  unfold IntegralEulerBits.ObjectiveStage.post
  simp only [pairFst_pair, pairSnd_pair]
  rw [IntegralCriticalLeadingBits.degreePost_packet, IntegralEulerBits.subtractPost_packet]

theorem objective_value (P : IntegralCriticalHistoryTask.Parameters)
    (F : IntegralEulerBits.Source)
    (answer : List Bool → List Bool)
    (hl : ∀ c, answer (next P .frozenLower c) = F.toGradient.toFrozen.lowerValue c)
    (hs : ∀ c, answer (next P .eulerSum c) = F.sumValue c) (c : List Bool) :
    (objectiveProgram P F).value answer c = F.objectiveValue c :=
  IntegralEulerBits.ObjectiveStage.value_eq _ _ _ answer hl hs c

theorem objective_halted_after (P : IntegralCriticalHistoryTask.Parameters)
    (F : IntegralEulerBits.Source)
    (answer : List Bool → List Bool) (c : List Bool) :
    (objectiveProgram P F).controller.halted
      (((objectiveProgram P F).controller.reference answer)^[2] ((objectiveProgram P F).initial c)) = true :=
  (objectiveProgram P F).halted_after answer c

theorem objective_output_when_halted (P : IntegralCriticalHistoryTask.Parameters)
    (F : IntegralEulerBits.Source)
    (answer : List Bool → List Bool)
    (hl : ∀ c, answer (next P .frozenLower c) = F.toGradient.toFrozen.lowerValue c)
    (hs : ∀ c, answer (next P .eulerSum c) = F.sumValue c)
    (c : List Bool) (t : ℕ)
    (hh : (objectiveProgram P F).controller.halted
      (((objectiveProgram P F).controller.reference answer)^[t] ((objectiveProgram P F).initial c)) = true) :
    (objectiveProgram P F).controller.output
      (((objectiveProgram P F).controller.reference answer)^[t] ((objectiveProgram P F).initial c)) =
        F.objectiveValue c :=
  IntegralEulerBits.ObjectiveStage.output_when_halted _ _ _ answer hl hs c t hh

theorem objective_state_length (P : IntegralCriticalHistoryTask.Parameters)
    (F : IntegralEulerBits.Source)
    (answer : List Bool → List Bool)
    (hl : ∀ c, answer (next P .frozenLower c) = F.toGradient.toFrozen.lowerValue c)
    (hs : ∀ c, answer (next P .eulerSum c) = F.sumValue c)
    (c : List Bool) (t : ℕ) :
    (RecursiveFold.encState (((objectiveProgram P F).controller.reference answer)^[t]
      ((objectiveProgram P F).initial c))).length ≤
        2 * c.length + 2 * (Turing.MultiTapeTM.encNat 2).length + (BinaryNatCode.encode (F.modulus c)).length + 2 :=
  IntegralEulerBits.ObjectiveStage.state_length _ _ _ answer hl hs c t

theorem objective_requests_iff (P : IntegralCriticalHistoryTask.Parameters)
    (F : IntegralEulerBits.Source)
    (answer : List Bool → List Bool) (c child : List Bool) :
    (objectiveProgram P F).controller.Requests answer (fun _ => 2) c child ↔
      child = next P .frozenLower c ∨ child = next P .eulerSum c :=
  IntegralEulerBits.ObjectiveStage.requests_iff _ _ _ answer c child

theorem objective_requests_rank (P : IntegralCriticalHistoryTask.Parameters)
    (F : IntegralEulerBits.Source)
    (answer : List Bool → List Bool) (c child : List Bool)
    (hp : IntegralCriticalHistoryTask.isPhase .eulerObjective c)
    (hc : (objectiveProgram P F).controller.Requests answer (fun _ => 2) c child) :
    IntegralCriticalHistoryTask.rank P child < IntegralCriticalHistoryTask.rank P c := by
  rcases (IntegralEulerBits.ObjectiveStage.requests_iff _ _ _ answer c child).mp hc with rfl | rfl
  · apply next_lower_rank
    change 12 < IntegralCriticalHistoryTask.phase c
    change IntegralCriticalHistoryTask.phase c = 15 at hp
    omega
  · apply next_lower_rank
    change 14 < IntegralCriticalHistoryTask.phase c
    change IntegralCriticalHistoryTask.phase c = 15 at hp
    omega

theorem objective_requests_tasks (P : IntegralCriticalHistoryTask.Parameters)
    (F : IntegralEulerBits.Source)
    (answer : List Bool → List Bool) (r c child : List Bool) (ht : IntegralCriticalHistoryTask.Tasks P r c)
    (hc : (objectiveProgram P F).controller.Requests answer (fun _ => 2) c child) :
    IntegralCriticalHistoryTask.Tasks P r child := by
  rcases (IntegralEulerBits.ObjectiveStage.requests_iff _ _ _ answer c child).mp hc with rfl | rfl
  · exact next_tasks P .frozenLower r c ht
  · exact next_tasks P .eulerSum r c ht


noncomputable def lowerProgram (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) : SingleCall.Program :=
  IntegralEulerBits.LowerStage.program F (selected P F)
    (IntegralCriticalFlatEulerBits.next P .eulerObjective) (spatial P .clearedGridSum 1)

theorem lower_controls (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : IntegralEulerBits.Source)
    (h : IntegralEulerBits.Access F) : (lowerProgram P F).Controls :=
  IntegralEulerBits.LowerStage.controls _ h _
    (selected_binary P a _ h) _ _
    (IntegralCriticalFlatEulerBits.next_FP P a .eulerObjective) (spatial_FP P a .clearedGridSum 1)

theorem lower_value (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (answer : List Bool → List Bool)
    (ho : ∀ c, answer (IntegralCriticalFlatEulerBits.next P .eulerObjective c) = F.objectiveValue c)
    (hg : ∀ p, answer (spatial P .clearedGridSum 1 p) = (IntegralCriticalGradientBits.family F.toGradient).value p)
    (c : List Bool) : (lowerProgram P F).value answer c =
      F.lowerValue (selected P F) c :=
  IntegralEulerBits.LowerStage.value_eq _ _ _ _ answer ho hg c

theorem lower_halted_after (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (answer : List Bool → List Bool) (c : List Bool) :
    (lowerProgram P F).controller.halted
      (((lowerProgram P F).controller.reference answer)^[1] (SingleCall.Program.initial c)) = true :=
  (lowerProgram P F).halted_after answer c

theorem lower_query_rank (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (c : List Bool)
    (hp : IntegralCriticalHistoryTask.isPhase .eulerLower c) :
    IntegralCriticalHistoryTask.rank P ((lowerProgram P F).query c) < IntegralCriticalHistoryTask.rank P c := by
  change IntegralCriticalHistoryTask.rank P
    (if (selected P F c).val = IntegralEulerBits.objectiveRank F c then
      IntegralCriticalFlatEulerBits.next P .eulerObjective c else
      spatial P .clearedGridSum 1 (IntegralEulerBits.lowerGradientQuery F (selected P F) c)) < _
  split_ifs
  · apply IntegralCriticalFlatEulerBits.next_lower_rank
    change 15 < IntegralCriticalHistoryTask.phase c
    change IntegralCriticalHistoryTask.phase c = 16 at hp
    omega
  · have H : (8 : ℕ) < IntegralCriticalHistoryTask.phase
        (pairFst (IntegralEulerBits.lowerGradientQuery F (selected P F) c)) := by
      simp only [IntegralEulerBits.lowerGradientQuery, pairFst_pair]
      change IntegralCriticalHistoryTask.phase c = 16 at hp
      omega
    simpa only [IntegralEulerBits.lowerGradientQuery, pairFst_pair] using
      spatial_lower_rank P .clearedGridSum 1
        (IntegralEulerBits.lowerGradientQuery F (selected P F) c) H

theorem lower_query_tasks (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (r c : List Bool)
    (ht : IntegralCriticalHistoryTask.Tasks P r c) :
    IntegralCriticalHistoryTask.Tasks P r ((lowerProgram P F).query c) := by
  change IntegralCriticalHistoryTask.Tasks P r
    (if (selected P F c).val = IntegralEulerBits.objectiveRank F c then
      IntegralCriticalFlatEulerBits.next P .eulerObjective c else
      spatial P .clearedGridSum 1 (IntegralEulerBits.lowerGradientQuery F (selected P F) c))
  split_ifs
  · exact IntegralCriticalFlatEulerBits.next_tasks P .eulerObjective r c ht
  · apply spatial_tasks P .clearedGridSum 1 r
    simpa only [IntegralEulerBits.lowerGradientQuery, pairFst_pair] using ht

theorem lower_gradient_fields (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (c : List Bool)
    (ht : F.target c ≤ IntegralCriticalHistoryTask.numericCap P (RankedHistoryTask.root c)) :
    let w := spatial P .clearedGridSum 1
      (IntegralEulerBits.lowerGradientQuery F (selected P F) c)
    IntegralCriticalHistoryTask.get P .derivative w = (selected P F c).val ∧
      IntegralCriticalHistoryTask.get P .target w = F.target c ∧
      IntegralCriticalHistoryTask.get P .expression w = 1 := by
  have H := spatial_fields P .clearedGridSum 1 c (selected P F c).val (F.target c)
    (selected_le P _ c) ht
    (IntegralCriticalHistoryTask.numericCap_pos P _)
  simpa only [IntegralEulerBits.lowerGradientQuery] using H

theorem gradient_index_packet (S : IntegralEulerBits.Source) (c : List Bool) (j : Fin (S.free c)) (e : ℕ) :
    (IntegralCriticalGradientBits.selected S.toGradient
      (pair c (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode e)))).val = S.offset c + j.val := by
  change S.offset (pairFst _) + min (Nat.fromBitsLE (pairFst (pairSnd _))) (S.free (pairFst _) - 1) = _
  simp only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [min_eq_left (by have := j.isLt; omega)]


noncomputable def productProgram (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) : SingleCall.Program where
  request c := if (selected P F c).val = IntegralEulerBits.objectiveRank F c then false
    else (productBase P F).request (packet P F c)
  query c := (productBase P F).query (packet P F c)
  immediate _ := []
  finish := pairSnd

theorem product_controls (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : IntegralEulerBits.Source)
    (h : IntegralEulerBits.Access F) : (productProgram P F).Controls := by
  have HS : IntegralEulerBits.Access F := h
  have HB : (productBase P F).Controls :=
    IntegralCriticalCoordinateProductBits.program_controls F.toGradient HS.toGradient
      (spatial P .clearedGridSum 1) (spatial_FP P a .clearedGridSum 1)
  have HP : packet P F ∈ FP := packet_FP P a F HS
  have HE := (selected_binary P a F HS).eq HS.objective
  refine ⟨?_, ?_, constFn_mem_FP [], pairSnd_mem_FP⟩
  · have HR := HE.ite_mem_FP (constFn_mem_FP [false])
      (mem_FP_comp (f := packet P F) (g := fun p => [(productBase P F).request p]) HP HB.request)
    exact mem_FP_of_eq HR (fun c => by
      change (if _ then [false] else [_]) = [if _ then false else _]
      simp only [IntegralEulerBits.objectiveRank]
      split_ifs <;> rfl)
  · exact mem_FP_comp (f := packet P F) (g := (productBase P F).query) HP HB.query

theorem product_value_base (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (answer : List Bool → List Bool) (c : List Bool) :
    (productProgram P F).value answer c =
      if (selected P F c).val = IntegralEulerBits.objectiveRank F c then []
      else (productBase P F).value answer (packet P F c) := by
  by_cases he : (selected P F c).val = IntegralEulerBits.objectiveRank F c <;>
    simp only [SingleCall.Program.value, productProgram, he, ite_true, ite_false, Bool.false_eq_true,
      productBase, IntegralCriticalCoordinateProductBits.program, FixedWidthCoordinateMulBits.program, pairSnd_pair]

theorem product_value (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (answer : List Bool → List Bool)
    (hg : ∀ p, answer (spatial P .clearedGridSum 1 p) = (IntegralCriticalGradientBits.family F.toGradient).value p)
    (c : List Bool) : (productProgram P F).value answer c =
      if (selected P F c).val = IntegralEulerBits.objectiveRank F c then []
      else IntegralCriticalCoordinateProductBits.value F.toGradient (packet P F c) := by
  rw [product_value_base]
  split_ifs
  · rfl
  · exact IntegralCriticalCoordinateProductBits.program_value _ _ answer hg _

theorem positive_packet (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralEulerBits.Source) (c : List Bool) :
    FixedWidthCoordinateMulBits.positive (IntegralCriticalCoordinateProductBits.arity S.toGradient)
      (IntegralCriticalCoordinateProductBits.width S.toGradient) IntegralCriticalCoordinateProductBits.selected
      IntegralCriticalCoordinateProductBits.targetWord (packet P S c) ↔
      0 < FixedWidthPolynomial.entry (S.targetWidth c) (S.target c) (selected P S c).val := by
  unfold FixedWidthCoordinateMulBits.positive
  rw [FixedWidthQuery.entry, ite_eq_left (by
    simpa only [IntegralCriticalCoordinateProductBits.arity, IntegralCriticalCoordinateProductBits.selected,
      packet, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using (selected P S c).isLt)]
  rw [FixedWidthQuery.coordinate_eq_entry]
  simp only [IntegralCriticalCoordinateProductBits.width, IntegralCriticalCoordinateProductBits.selected,
    IntegralCriticalCoordinateProductBits.targetWord, packet, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem product_request_iff (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (c : List Bool) :
    (productProgram P F).request c = true ↔
      (selected P F c).val ≠ IntegralEulerBits.objectiveRank F c ∧
        0 < FixedWidthPolynomial.entry (F.targetWidth c) (F.target c)
          (selected P F c).val := by
  by_cases he : (selected P F c).val = IntegralEulerBits.objectiveRank F c
  · have H : (productProgram P F).request c = false := ite_eq_left he
    rw [H]
    constructor
    · intro hh; cases hh
    · intro hh; exact (hh.1 he).elim
  · have H : (productProgram P F).request c = true ↔
        0 < FixedWidthPolynomial.entry (F.targetWidth c) (F.target c)
          (selected P F c).val := by
      change (if _ then false else _) = true ↔ _
      rw [ite_eq_right he]
      change decide (FixedWidthCoordinateMulBits.positive _ _ _ _ (packet P F c)) = true ↔ _
      rw [decide_eq_true_eq, positive_packet]
    exact ⟨fun hh => ⟨he, H.mp hh⟩, fun hh => H.mpr hh.2⟩

theorem product_value_matrix (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (answer : List Bool → List Bool)
    (hg : ∀ p, answer (spatial P .clearedGridSum 1 p) = (IntegralCriticalGradientBits.family F.toGradient).value p)
    (c : List Bool) :
    letI := F.ring c
    (productProgram P F).value answer c =
      if (selected P F c).val = IntegralEulerBits.objectiveRank F c then [] else
        residueBits ((Algebra.leftMulMatrix (F.basis c)
          ((MvPolynomial.X (selected P F c) *
            IntegralCriticalGradientBits.polynomial F.toGradient c (selected P F c)).coeff
            (RationalSubstitution.Indexed.exponentVector (F.free c)
              (FixedWidthPolynomial.entry (F.targetWidth c) (F.target c))))
          (F.row c) (F.col c) : ℤ) : ZMod (F.modulus c)) := by
  let := F.ring c
  rw [product_value P F answer hg]
  split_ifs
  · rfl
  · exact IntegralCriticalCoordinateProductBits.packet F.toGradient c
      (selected P F c) (F.target c)

theorem product_halted_after (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (answer : List Bool → List Bool) (c : List Bool) :
    (productProgram P F).controller.halted
      (((productProgram P F).controller.reference answer)^[1] (SingleCall.Program.initial c)) = true :=
  (productProgram P F).halted_after answer c

theorem product_query (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (c : List Bool) :
    (productProgram P F).query c = spatial P .clearedGridSum 1 (productGradientQuery P F c) := rfl

theorem product_query_rank (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (c : List Bool)
    (hp : IntegralCriticalHistoryTask.isPhase .coordinateGradientProduct c) :
    IntegralCriticalHistoryTask.rank P ((productProgram P F).query c) < IntegralCriticalHistoryTask.rank P c := by
  rw [product_query]
  have H : (8 : ℕ) < IntegralCriticalHistoryTask.phase (pairFst (productGradientQuery P F c)) := by
    rw [productGradientQuery_parent]
    change IntegralCriticalHistoryTask.phase c = 13 at hp
    omega
  simpa only [productGradientQuery_parent] using spatial_lower_rank P .clearedGridSum 1 _ H

theorem product_query_tasks (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (r c : List Bool)
    (ht : IntegralCriticalHistoryTask.Tasks P r c) :
    IntegralCriticalHistoryTask.Tasks P r ((productProgram P F).query c) := by
  rw [product_query]
  exact spatial_tasks P .clearedGridSum 1 r (productGradientQuery P F c)
    (by simpa only [productGradientQuery_parent] using ht)


noncomputable def sumProgram (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) : RecursiveFold.Program :=
  IntegralEulerBits.SumStage.program F (sumTask P F)

theorem sum_certificates (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : IntegralEulerBits.Source)
    (h : IntegralEulerBits.Access F) :
    (sumProgram P F).controller.Certificates
      (encQ := Turing.MultiTapeTM.encBits) (encS := RecursiveFold.encState) :=
  IntegralEulerBits.SumStage.certificates F h (sumTask P F)
    (sumTask_FP P a F h)

theorem sum_partial_value (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (answer : List Bool → List Bool)
    (he : ∀ c i, i < F.free c →
      answer (sumTask P F (pair c (BinaryNatCode.encode i))) =
        residueBits (F.summand c i : ZMod (F.modulus c)))
    (c : List Bool) (k : ℕ) (hk : k ≤ F.free c) :
    (sumProgram P F).partialValue answer c k =
      residueBits (∑ i ∈ Finset.range k, (F.summand c i : ZMod (F.modulus c))) :=
  ModularFold.RecursiveStage.sum_partialValueWithModulus F.free
    (fun c => BinaryNatCode.encode (F.modulus c)) (sumTask P F) answer
    F.modulus (funext (fun _ => Nat.fromBitsLE_bits _)) c
    (fun i => (F.summand c i : ZMod (F.modulus c)))
    (Nat.pos_of_ne_zero (F.modulus_ne_zero c)) (he c) k hk

theorem sum_value (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (answer : List Bool → List Bool)
    (he : ∀ c i, i < F.free c →
      answer (sumTask P F (pair c (BinaryNatCode.encode i))) =
        residueBits (F.summand c i : ZMod (F.modulus c)))
    (c : List Bool) : (sumProgram P F).value answer c = F.sumValue c :=
  (sum_partial_value P F answer he c _ le_rfl).trans (IntegralEulerBits.sum_value F c)

theorem sum_halted_after (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (answer : List Bool → List Bool) (c : List Bool) :
    (sumProgram P F).controller.halted
      (((sumProgram P F).controller.reference answer)^[F.free c] ((sumProgram P F).initial c)) = true :=
  (sumProgram P F).halted_after answer c

theorem sum_output_when_halted (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (answer : List Bool → List Bool)
    (he : ∀ c i, i < F.free c →
      answer (sumTask P F (pair c (BinaryNatCode.encode i))) =
        residueBits (F.summand c i : ZMod (F.modulus c)))
    (c : List Bool) (t : ℕ)
    (hh : (sumProgram P F).controller.halted
      (((sumProgram P F).controller.reference answer)^[t] ((sumProgram P F).initial c)) = true) :
    (sumProgram P F).controller.output
      (((sumProgram P F).controller.reference answer)^[t] ((sumProgram P F).initial c)) =
        F.sumValue c :=
  ((sumProgram P F).output_when_halted answer c t hh).trans (sum_value P F answer he c)

theorem sum_state_length (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (answer : List Bool → List Bool)
    (he : ∀ c i, i < F.free c →
      answer (sumTask P F (pair c (BinaryNatCode.encode i))) =
        residueBits (F.summand c i : ZMod (F.modulus c)))
    (c : List Bool) (t : ℕ) :
    (RecursiveFold.encState (((sumProgram P F).controller.reference answer)^[t]
      ((sumProgram P F).initial c))).length ≤
        2 * c.length + 2 * (Turing.MultiTapeTM.encNat (F.free c)).length +
          (BinaryNatCode.encode (F.modulus c)).length + 2 := by
  apply (sumProgram P F).orbit_length
  intro k hk
  rw [sum_partial_value P F answer he c k hk]
  let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
  apply ModularFold.bits_length_le (fun c => BinaryNatCode.encode (F.modulus c)) c
  simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits] using ZMod.val_lt
    (∑ i ∈ Finset.range k, (F.summand c i : ZMod (F.modulus c)))

theorem sum_requests_iff (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (answer : List Bool → List Bool) (c child : List Bool) :
    (sumProgram P F).controller.Requests answer F.free c child ↔
      ∃ i < F.free c, child = sumTask P F (pair c (BinaryNatCode.encode i)) :=
  IntegralEulerBits.SumStage.requests_iff F (sumTask P F) answer c child

theorem sum_requests_rank (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (answer : List Bool → List Bool) (c child : List Bool)
    (hp : IntegralCriticalHistoryTask.isPhase .eulerSum c)
    (hc : (sumProgram P F).controller.Requests answer F.free c child) :
    IntegralCriticalHistoryTask.rank P child < IntegralCriticalHistoryTask.rank P c := by
  obtain ⟨i, _, he⟩ := (sum_requests_iff P F answer c child).mp hc
  rw [he]
  exact sumTask_rank P F c i hp

theorem sum_requests_tasks (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (answer : List Bool → List Bool) (r c child : List Bool)
    (ht : IntegralCriticalHistoryTask.Tasks P r c)
    (hc : (sumProgram P F).controller.Requests answer F.free c child) :
    IntegralCriticalHistoryTask.Tasks P r child := by
  obtain ⟨i, _, he⟩ := (sum_requests_iff P F answer c child).mp hc
  rw [he]
  exact sumTask_tasks P F r c i ht


theorem sum_partial_value_at (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (answer : List Bool → List Bool)
    (c : List Bool)
    (he : ∀ i, i < F.free c →
      answer (sumTask P F (pair c (BinaryNatCode.encode i))) =
        residueBits (F.summand c i : ZMod (F.modulus c)))
    (k : ℕ) (hk : k ≤ F.free c) :
    (sumProgram P F).partialValue answer c k =
      residueBits (∑ i ∈ Finset.range k, (F.summand c i : ZMod (F.modulus c))) :=
  ModularFold.RecursiveStage.sum_partialValueWithModulus F.free
    (fun c => BinaryNatCode.encode (F.modulus c)) (sumTask P F) answer
    F.modulus (funext (fun _ => Nat.fromBitsLE_bits _)) c
    (fun i => (F.summand c i : ZMod (F.modulus c)))
    (Nat.pos_of_ne_zero (F.modulus_ne_zero c)) he k hk

theorem sum_value_at (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (answer : List Bool → List Bool)
    (c : List Bool)
    (he : ∀ i, i < F.free c →
      answer (sumTask P F (pair c (BinaryNatCode.encode i))) =
        residueBits (F.summand c i : ZMod (F.modulus c)))
    : (sumProgram P F).value answer c = F.sumValue c :=
  (sum_partial_value_at P F answer c he _ le_rfl).trans (IntegralEulerBits.sum_value F c)

theorem sum_output_when_halted_at (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (answer : List Bool → List Bool)
    (c : List Bool)
    (he : ∀ i, i < F.free c →
      answer (sumTask P F (pair c (BinaryNatCode.encode i))) =
        residueBits (F.summand c i : ZMod (F.modulus c)))
    (t : ℕ)
    (hh : (sumProgram P F).controller.halted
      (((sumProgram P F).controller.reference answer)^[t] ((sumProgram P F).initial c)) = true) :
    (sumProgram P F).controller.output
      (((sumProgram P F).controller.reference answer)^[t] ((sumProgram P F).initial c)) =
        F.sumValue c :=
  ((sumProgram P F).output_when_halted answer c t hh).trans (sum_value_at P F answer c he)

theorem sum_state_length_at (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source) (answer : List Bool → List Bool)
    (c : List Bool)
    (he : ∀ i, i < F.free c →
      answer (sumTask P F (pair c (BinaryNatCode.encode i))) =
        residueBits (F.summand c i : ZMod (F.modulus c)))
    (t : ℕ) :
    (RecursiveFold.encState (((sumProgram P F).controller.reference answer)^[t]
      ((sumProgram P F).initial c))).length ≤
        2 * c.length + 2 * (Turing.MultiTapeTM.encNat (F.free c)).length +
          (BinaryNatCode.encode (F.modulus c)).length + 2 := by
  apply (sumProgram P F).orbit_length
  intro k hk
  rw [sum_partial_value_at P F answer c he k hk]
  let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
  apply ModularFold.bits_length_le (fun c => BinaryNatCode.encode (F.modulus c)) c
  simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits] using ZMod.val_lt
    (∑ i ∈ Finset.range k, (F.summand c i : ZMod (F.modulus c)))

theorem lower_value_at (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source)
    (answer : List Bool → List Bool) (c : List Bool)
    (ho : (selected P F c).val = IntegralEulerBits.objectiveRank F c →
      answer (next P .eulerObjective c) = F.objectiveValue c)
    (hg : (selected P F c).val ≠ IntegralEulerBits.objectiveRank F c →
      answer (spatial P .clearedGridSum 1 (IntegralEulerBits.lowerGradientQuery F (selected P F) c)) =
        (IntegralCriticalGradientBits.family F.toGradient).value (IntegralEulerBits.lowerGradientQuery F (selected P F) c)) :
    (lowerProgram P F).value answer c = F.lowerValue (selected P F) c := by
  simp only [SingleCall.Program.value, lowerProgram, IntegralEulerBits.LowerStage.program, ite_true, pairSnd_pair]
  split_ifs with h
  · rw [ho h]
    simpa only [h, ite_true] using IntegralEulerBits.lower_value F (selected P F) c
  · rw [hg h]
    simpa only [h, ite_false] using IntegralEulerBits.lower_value F (selected P F) c

noncomputable def lowerStateBound (F : IntegralEulerBits.Source) (c : List Bool) : ℕ :=
  2 * c.length + 4 + (F.modulus c).size
theorem lowerStateBound_unary (F : IntegralEulerBits.Source) (h : IntegralEulerBits.Access F) : UnaryFn (lowerStateBound F) := by
  have HM : UnaryFn (fun c => (F.modulus c).size) :=
    (UnaryFn.length h.modulus.bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)
  exact (((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add (UnaryFn.const 4)).add HM

theorem lower_state_length_at (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source)
    (answer : List Bool → List Bool) (c : List Bool)
    (ho : (selected P F c).val = IntegralEulerBits.objectiveRank F c →
      answer (next P .eulerObjective c) = F.objectiveValue c)
    (hg : (selected P F c).val ≠ IntegralEulerBits.objectiveRank F c →
      answer (spatial P .clearedGridSum 1 (IntegralEulerBits.lowerGradientQuery F (selected P F) c)) =
        (IntegralCriticalGradientBits.family F.toGradient).value (IntegralEulerBits.lowerGradientQuery F (selected P F) c)) (t : ℕ) :
    (SingleCall.encState (((lowerProgram P F).controller.reference answer)^[t]
      (SingleCall.Program.initial c))).length ≤ lowerStateBound F c := by
  apply (lowerProgram P F).state_length_of_bound answer c t (F.modulus c).size
  intro hr
  have HV := lower_value_at P F answer c ho hg
  rw [SingleCall.Program.value, hr, ite_eq_left rfl] at HV
  have HF : (lowerProgram P F).finish = pairSnd := rfl
  rw [HF, pairSnd_pair] at HV
  rw [HV]
  let := F.ring c
  have : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
  unfold IntegralEulerBits.Source.lowerValue
  exact residueBits_length_le _ _

theorem lower_output_when_halted_at (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source)
    (answer : List Bool → List Bool) (c : List Bool)
    (ho : (selected P F c).val = IntegralEulerBits.objectiveRank F c →
      answer (next P .eulerObjective c) = F.objectiveValue c)
    (hg : (selected P F c).val ≠ IntegralEulerBits.objectiveRank F c →
      answer (spatial P .clearedGridSum 1 (IntegralEulerBits.lowerGradientQuery F (selected P F) c)) =
        (IntegralCriticalGradientBits.family F.toGradient).value (IntegralEulerBits.lowerGradientQuery F (selected P F) c))
    (t : ℕ) (hh : (lowerProgram P F).controller.halted (((lowerProgram P F).controller.reference answer)^[t]
      (SingleCall.Program.initial c)) = true) :
    (lowerProgram P F).controller.output (((lowerProgram P F).controller.reference answer)^[t]
      (SingleCall.Program.initial c)) = F.lowerValue (selected P F) c :=
  ((lowerProgram P F).output_when_halted answer c t hh).trans (lower_value_at P F answer c ho hg)

theorem objective_value_at (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source)
    (answer : List Bool → List Bool) (c : List Bool)
    (hl : answer (next P .frozenLower c) = F.toGradient.toFrozen.lowerValue c)
    (hs : answer (next P .eulerSum c) = F.sumValue c) :
    (objectiveProgram P F).value answer c = F.objectiveValue c := by
  change (TwoCall.program _ _ (IntegralEulerBits.ObjectiveStage.post F)).value answer c = _
  rw [TwoCall.value_eq, hl, hs]
  unfold IntegralEulerBits.ObjectiveStage.post
  simp only [pairFst_pair, pairSnd_pair]
  exact IntegralEulerBits.objective_value F c

theorem objective_output_when_halted_at (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source)
    (answer : List Bool → List Bool) (c : List Bool)
    (hl : answer (next P .frozenLower c) = F.toGradient.toFrozen.lowerValue c)
    (hs : answer (next P .eulerSum c) = F.sumValue c) (t : ℕ)
    (hh : (objectiveProgram P F).controller.halted (((objectiveProgram P F).controller.reference answer)^[t]
      ((objectiveProgram P F).initial c)) = true) :
    (objectiveProgram P F).controller.output (((objectiveProgram P F).controller.reference answer)^[t]
      ((objectiveProgram P F).initial c)) = F.objectiveValue c :=
  ((objectiveProgram P F).output_when_halted answer c t hh).trans (objective_value_at P F answer c hl hs)

theorem objective_state_length_at (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source)
    (answer : List Bool → List Bool) (c : List Bool)
    (hl : answer (next P .frozenLower c) = F.toGradient.toFrozen.lowerValue c)
    (hs : answer (next P .eulerSum c) = F.sumValue c) (t : ℕ) :
    (RecursiveFold.encState (((objectiveProgram P F).controller.reference answer)^[t]
      ((objectiveProgram P F).initial c))).length ≤
        2 * c.length + 2 * (Turing.MultiTapeTM.encNat 2).length + (BinaryNatCode.encode (F.modulus c)).length + 2 := by
  have : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
  have HB (x : ZMod (F.modulus c)) : (residueBits x).length ≤ (BinaryNatCode.encode (F.modulus c)).length := by
    apply ModularFold.bits_length_le (fun _ => BinaryNatCode.encode (F.modulus c)) c x.val
    simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits] using ZMod.val_lt x
  have HL : (F.toGradient.toFrozen.lowerValue c).length ≤ (BinaryNatCode.encode (F.modulus c)).length := by
    unfold IntegralFrozenPowerBits.Source.lowerValue
    exact HB _
  have HO : (F.objectiveValue c).length ≤ (BinaryNatCode.encode (F.modulus c)).length := by
    unfold IntegralEulerBits.Source.objectiveValue
    exact HB _
  have HP : IntegralEulerBits.ObjectiveStage.post F
      (pair c (pair (F.toGradient.toFrozen.lowerValue c) (F.sumValue c))) = F.objectiveValue c := by
    unfold IntegralEulerBits.ObjectiveStage.post
    simp only [pairFst_pair, pairSnd_pair]
    exact IntegralEulerBits.objective_value F c
  have H := TwoCall.state_length (next P .frozenLower) (next P .eulerSum)
    (IntegralEulerBits.ObjectiveStage.post F) answer c t
  rw [hl, hs, HP] at H
  exact H.trans (by omega)

theorem product_value_at (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source)
    (answer : List Bool → List Bool) (c : List Bool)
    (hg : (productProgram P F).request c = true → answer ((productProgram P F).query c) =
      (IntegralCriticalGradientBits.family F.toGradient).value (productGradientQuery P F c)) :
    (productProgram P F).value answer c =
      if (selected P F c).val = IntegralEulerBits.objectiveRank F c then []
      else IntegralCriticalCoordinateProductBits.value F.toGradient (packet P F c) := by
  rw [product_value_base]
  split_ifs with ho
  · rfl
  · apply IntegralCriticalCoordinateProductBits.program_value_at F.toGradient
      (spatial P .clearedGridSum 1) answer (packet P F c)
    intro hp
    have HR : (productProgram P F).request c = true := by
      simp only [productProgram, ho, ite_false, productBase, IntegralCriticalCoordinateProductBits.program,
        FixedWidthCoordinateMulBits.program, decide_eq_true_eq]
      exact hp
    simpa only [productProgram, productBase, IntegralCriticalCoordinateProductBits.program,
      FixedWidthCoordinateMulBits.program, productGradientQuery, Function.comp_apply] using hg HR

theorem product_output_when_halted_at (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source)
    (answer : List Bool → List Bool) (c : List Bool)
    (hg : (productProgram P F).request c = true → answer ((productProgram P F).query c) =
      (IntegralCriticalGradientBits.family F.toGradient).value (productGradientQuery P F c))
    (t : ℕ) (hh : (productProgram P F).controller.halted (((productProgram P F).controller.reference answer)^[t]
      (SingleCall.Program.initial c)) = true) :
    (productProgram P F).controller.output (((productProgram P F).controller.reference answer)^[t]
      (SingleCall.Program.initial c)) =
      if (selected P F c).val = IntegralEulerBits.objectiveRank F c then []
      else IntegralCriticalCoordinateProductBits.value F.toGradient (packet P F c) :=
  ((productProgram P F).output_when_halted answer c t hh).trans (product_value_at P F answer c hg)

theorem product_value_matrix_at (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source)
    (answer : List Bool → List Bool) (c : List Bool)
    (hg : (productProgram P F).request c = true → answer ((productProgram P F).query c) =
      (IntegralCriticalGradientBits.family F.toGradient).value (productGradientQuery P F c)) :
    letI := F.ring c
    (productProgram P F).value answer c =
      if (selected P F c).val = IntegralEulerBits.objectiveRank F c then [] else
        residueBits ((Algebra.leftMulMatrix (F.basis c)
          ((MvPolynomial.X (selected P F c) * IntegralCriticalGradientBits.polynomial F.toGradient c (selected P F c)).coeff
            (RationalSubstitution.Indexed.exponentVector (F.free c) (FixedWidthPolynomial.entry (F.targetWidth c) (F.target c))))
          (F.row c) (F.col c) : ℤ) : ZMod (F.modulus c)) := by
  let := F.ring c
  rw [product_value_at P F answer c hg]
  split_ifs
  · rfl
  · exact IntegralCriticalCoordinateProductBits.packet F.toGradient c (selected P F c) (F.target c)

theorem gradient_value_length (F : IntegralEulerBits.Source) (p : List Bool) :
    ((IntegralCriticalGradientBits.family F.toGradient).value p).length ≤ (F.modulus (pairFst p)).size := by
  have H : ((IntegralCriticalGradientBits.family F.toGradient).value p).length ≤
      ((IntegralCriticalGradientBits.family F.toGradient).modulus p).size := by
    let := (IntegralCriticalGradientBits.family F.toGradient).ring p
    have : NeZero ((IntegralCriticalGradientBits.family F.toGradient).modulus p) :=
      ⟨(IntegralCriticalGradientBits.family F.toGradient).modulus_ne_zero p⟩
    unfold IntegralClearedCoefficientBits.Source.value
    exact residueBits_length_le _ _
  exact H.trans_eq (congrArg Nat.size (show
    (IntegralCriticalGradientBits.family F.toGradient).modulus p = F.modulus (pairFst p) from rfl))

theorem product_state_length_at (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralEulerBits.Source)
    (answer : List Bool → List Bool) (c : List Bool)
    (hg : (productProgram P F).request c = true → answer ((productProgram P F).query c) =
      (IntegralCriticalGradientBits.family F.toGradient).value (productGradientQuery P F c)) (t : ℕ) :
    (SingleCall.encState (((productProgram P F).controller.reference answer)^[t]
      (SingleCall.Program.initial c))).length ≤ lowerStateBound F c := by
  apply (productProgram P F).state_length_of_bound answer c t (F.modulus c).size
  intro hr
  rw [hg hr]
  simpa only [productGradientQuery_parent] using gradient_value_length F (productGradientQuery P F c)

noncomputable def scanStateBound (F : IntegralEulerBits.Source) (n : List Bool → ℕ) (c : List Bool) : ℕ :=
  2 * c.length + 2 * (n c).size + (F.modulus c).size + 2

theorem scanStateBound_unary (F : IntegralEulerBits.Source) (h : IntegralEulerBits.Access F)
    (n : List Bool → ℕ) (hn : BinaryFn n) : UnaryFn (scanStateBound F n) := by
  have HN : UnaryFn (fun c => (n c).size) :=
    (UnaryFn.length hn.bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)
  have HM : UnaryFn (fun c => (F.modulus c).size) :=
    (UnaryFn.length h.modulus.bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)
  exact ((((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add ((UnaryFn.const 2).mul HN)).add HM).add (UnaryFn.const 2)

theorem sum_stateBound_unary (F : IntegralEulerBits.Source) (h : IntegralEulerBits.Access F) :
    UnaryFn (scanStateBound F F.free) := scanStateBound_unary F h F.free (BinaryFn.ofUnary h.free)
theorem objective_stateBound_unary (F : IntegralEulerBits.Source) (h : IntegralEulerBits.Access F) :
    UnaryFn (scanStateBound F (fun _ => 2)) := scanStateBound_unary F h _ (BinaryFn.const 2)

end LeanCanny.Algebra.IntegralCriticalFlatGenericEulerBits
