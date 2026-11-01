/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalFlatGridSource
public import LeanCanny.Algebra.IntegralCriticalFlatMatrixQuery

/-! # Flat original-grid sums and masked monomial requests

The sum streams the actual original spatial grid. Each child stores its
grid index and copies the target, derivative rank, source kind, and old
basis query. The masked term stage then asks for the actual monomial
product at the lower product-power phase.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatGridBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalHistoryTask.rank IntegralCriticalHistoryTask.Tasks

def reader (P : IntegralCriticalHistoryTask.Parameters) (z : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairSnd z) = IntegralCriticalHistoryTask.Field.sourceIndex.code then pairSnd (pairFst z)
  else IntegralCriticalFlatMatrixQuery.saved P z

theorem reader_FP (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P) : reader P ∈ FP := by
  have HI : BinaryFn (fun z => Nat.fromBitsLE (pairSnd z)) := BinaryFn.fromBits pairSnd_mem_FP
  have HK := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have HC := IntegralCriticalFlatEulerRowsBits.copyReader_FP P a
  exact (HI.eq (BinaryFn.const 7)).ite_mem_FP HK HC

def writer (P : IntegralCriticalHistoryTask.Parameters) (p : IntegralCriticalHistoryTask.Phase) : List Bool → List Bool :=
  IntegralCriticalHistoryTask.child P pairFst (IntegralCriticalHistoryTask.birth P ∘ pairFst) p (reader P)

theorem writer_FP (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (p : IntegralCriticalHistoryTask.Phase) : writer P p ∈ FP :=
  IntegralCriticalHistoryTask.child_FP P a pairFst pairFst_mem_FP _
    ((BinaryFn.ofUnary (RankedHistoryTask.birth_unary _ (IntegralCriticalHistoryTask.birthCap_unary P a))).comp pairFst_mem_FP)
    p _ (reader_FP P a)

theorem reader_packet (P : IntegralCriticalHistoryTask.Parameters) (p : List Bool) (i : ℕ) :
    reader P (pair p (BinaryNatCode.encode i)) =
      if i = 7 then pairSnd p else BinaryNatCode.encode
        (RankedHistoryFields.get (IntegralCriticalHistoryTask.numericCap P) 16 (pairFst p) i) := by
  have HI : Nat.fromBitsLE (BinaryNatCode.encode i) = i := Nat.fromBitsLE_bits i
  simp only [reader, IntegralCriticalFlatMatrixQuery.saved, pairFst_pair, pairSnd_pair, HI,
    IntegralCriticalHistoryTask.Field.code]
  rw [RankedHistoryFields.read_packet]

theorem writer_get (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase)
    (p : List Bool) (f : IntegralCriticalHistoryTask.Field) :
    IntegralCriticalHistoryTask.get P f (writer P phase p) =
      if f = .sourceIndex then min (Nat.fromBitsLE (pairSnd p))
        (IntegralCriticalHistoryTask.numericCap P (RankedHistoryTask.root (pairFst p)))
      else IntegralCriticalHistoryTask.get P f (pairFst p) := by
  have H := IntegralCriticalHistoryTask.get_le P f (pairFst p)
  rw [writer, IntegralCriticalHistoryTask.child_get, reader_packet]
  cases f <;> norm_num only [IntegralCriticalHistoryTask.Field.code, reduceCtorEq, ite_true, ite_false,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  all_goals exact min_eq_left H

theorem writer_index (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase)
    (c : List Bool) (k : ℕ) (hk : k ≤ IntegralCriticalHistoryTask.numericCap P (RankedHistoryTask.root c)) :
    IntegralCriticalHistoryTask.get P .sourceIndex (writer P phase (pair c (BinaryNatCode.encode k))) = k := by
  rw [writer_get]
  simp only [ite_true, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact min_eq_left hk

theorem writer_other (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase)
    (p : List Bool) (f : IntegralCriticalHistoryTask.Field) (hf : f ≠ .sourceIndex) :
    IntegralCriticalHistoryTask.get P f (writer P phase p) = IntegralCriticalHistoryTask.get P f (pairFst p) := by
  rw [writer_get, ite_eq_right hf]

theorem writer_root (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase) (p : List Bool) :
    RankedHistoryTask.root (writer P phase p) = RankedHistoryTask.root (pairFst p) :=
  IntegralCriticalHistoryTask.child_root P _ _ _ _ p

theorem writer_birth (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase) (p : List Bool) :
    IntegralCriticalHistoryTask.birth P (writer P phase p) = IntegralCriticalHistoryTask.birth P (pairFst p) := by
  unfold writer IntegralCriticalHistoryTask.child
  rw [RankedHistoryFields.flatten_eq_pack]
  exact RankedHistoryTask.birth_pack _ _ _ _ _ (min_le_right _ _)

theorem writer_phase (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase) (p : List Bool) :
    IntegralCriticalHistoryTask.phase (writer P phase p) = phase.code := by
  unfold writer IntegralCriticalHistoryTask.child
  rw [RankedHistoryFields.flatten_eq_pack]
  exact RankedHistoryTask.phase_pack _ _ _ _ _ phase.code_lt

theorem writer_modulus (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase) (p : List Bool) :
    IntegralCriticalHistoryTask.modulus P (writer P phase p) = IntegralCriticalHistoryTask.modulus P (pairFst p) := by
  unfold IntegralCriticalHistoryTask.modulus
  rw [writer_other P phase p .modulus (by decide)]

theorem writer_lower_rank (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase) (p : List Bool)
    (hp : phase.code < IntegralCriticalHistoryTask.phase (pairFst p)) :
    IntegralCriticalHistoryTask.rank P (writer P phase p) < IntegralCriticalHistoryTask.rank P (pairFst p) :=
  IntegralCriticalHistoryTask.child_lower_phase P pairFst _ phase _ p rfl hp

theorem writer_tasks (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase) (r p : List Bool)
    (ht : IntegralCriticalHistoryTask.Tasks P r (pairFst p)) : IntegralCriticalHistoryTask.Tasks P r (writer P phase p) :=
  IntegralCriticalHistoryTask.child_tasks P pairFst _ phase _ r p ht (min_le_right _ _)

theorem writer_length (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase) (p : List Bool) :
    (writer P phase p).length ≤ IntegralCriticalHistoryTask.wordBudget P (pairFst p) :=
  IntegralCriticalHistoryTask.child_length P pairFst _ phase _ p (min_le_right _ _)

noncomputable def source (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) := IntegralCriticalFlatGridSourceBits.actual P F q

noncomputable def access (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : IntegralCriticalScriptGeneratorBits.Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q) : IntegralClearedCoefficientBits.Access (source P F q) :=
  IntegralCriticalFlatGridSourceBits.actualAccess P a F q h

theorem source_arity (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (c : List Bool) :
    (source P F q).arity c = F.ambient c + 1 := rfl

theorem source_free (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (c : List Bool) :
    (source P F q).free c = F.ambient c - (IntegralCriticalScript.chosen (F.rules c) (F.selected c)).offset.val + 1 := rfl

theorem source_offset (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (c : List Bool) :
    (source P F q).offset c = (IntegralCriticalScript.chosen (F.rules c) (F.selected c)).offset.val := rfl

theorem source_sourceWidth (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (c : List Bool) :
    (source P F q).sourceWidth c = F.sourceWidth c := rfl

theorem source_targetWidth (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (c : List Bool) :
    (source P F q).targetWidth c = PurePowerReductionBounds.width ((source P F q).free c)
      (IntegralCriticalScript.chosen (F.rules c) (F.selected c)).degree := rfl

theorem source_target (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (c : List Bool) :
    (source P F q).target c = IntegralCriticalHistoryTask.get P .target c := rfl

attribute [local irreducible] source

noncomputable def program (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) : RecursiveFold.Program :=
  IntegralClearedCoefficientBits.RecursiveStage.program (source P F q) (writer P .originalGridTerm)

noncomputable def budget (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) := IntegralClearedCoefficientBits.RecursiveStage.count (source P F q)

theorem budget_eq (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (c : List Bool) :
    budget P F q c = FixedWidthPolynomial.count (F.ambient c + 1) (F.sourceWidth c) := by
  unfold budget IntegralClearedCoefficientBits.RecursiveStage.count source
  rfl

theorem budget_binary (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : IntegralCriticalScriptGeneratorBits.Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q) : BinaryFn (budget P F q) :=
  IntegralClearedCoefficientBits.RecursiveStage.count_binary (source P F q) (access P a F q h)

theorem certificates (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : IntegralCriticalScriptGeneratorBits.Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q) :
    (program P F q).controller.Certificates (encQ := Turing.MultiTapeTM.encBits) (encS := RecursiveFold.encState) :=
  IntegralClearedCoefficientBits.RecursiveStage.certificates (source P F q) (access P a F q h)
    (writer P .originalGridTerm) (writer_FP P a .originalGridTerm)

theorem partial_value (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (answer : List Bool → List Bool)
    (he : ∀ c i, i < budget P F q c → answer (writer P .originalGridTerm (pair c (BinaryNatCode.encode i))) =
      IntegralClearedCoefficientBits.maskedProgram (source P F q) (pair c (BinaryNatCode.encode i)))
    (c : List Bool) (k : ℕ) (hk : k ≤ budget P F q c) :
    (program P F q).partialValue answer c k = residueBits
      (∑ i ∈ Finset.range k, ((source P F q).summand c i : ZMod ((source P F q).modulus c))) :=
  ModularFold.RecursiveStage.sum_partialValueWithModulus (budget P F q)
    (fun c => BinaryNatCode.encode ((source P F q).modulus c)) (writer P .originalGridTerm) answer
    (source P F q).modulus (funext (fun _ => Nat.fromBitsLE_bits _)) c
    (fun i => ((source P F q).summand c i : ZMod ((source P F q).modulus c)))
    (Nat.pos_of_ne_zero ((source P F q).modulus_ne_zero c))
    (fun i hi => (he c i hi).trans (IntegralClearedCoefficientBits.masked_packet (source P F q) c i hi)) k hk

theorem value (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (answer : List Bool → List Bool)
    (he : ∀ c i, i < budget P F q c → answer (writer P .originalGridTerm (pair c (BinaryNatCode.encode i))) =
      IntegralClearedCoefficientBits.maskedProgram (source P F q) (pair c (BinaryNatCode.encode i)))
    (c : List Bool) : (program P F q).value answer c = (source P F q).value c :=
  (partial_value P F q answer he c _ le_rfl).trans (IntegralClearedCoefficientBits.sum_value (source P F q) c)

theorem halted_after (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (answer : List Bool → List Bool) (c : List Bool) :
    (program P F q).controller.halted
      (((program P F q).controller.reference answer)^[budget P F q c] ((program P F q).initial c)) = true :=
  (program P F q).halted_after answer c

noncomputable def stateBound (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (c : List Bool) : ℕ :=
  2 * c.length + 2 * (budget P F q c).size + ((source P F q).modulus c).size + 2

theorem stateBound_unary (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : IntegralCriticalScriptGeneratorBits.Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q) : UnaryFn (stateBound P F q) := by
  have HB : UnaryFn (fun c => (budget P F q c).size) :=
    (UnaryFn.length (budget_binary P a F q h).bits_mem_FP).of_eq (fun c => BinaryNatCode.length_encode _)
  have HM : UnaryFn (fun c => ((source P F q).modulus c).size) :=
    (UnaryFn.length (access P a F q h).modulus.bits_mem_FP).of_eq (fun c => BinaryNatCode.length_encode _)
  exact (((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add ((UnaryFn.const 2).mul HB)).add HM |>.add (UnaryFn.const 2)

theorem state_length (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (answer : List Bool → List Bool)
    (he : ∀ c i, i < budget P F q c → answer (writer P .originalGridTerm (pair c (BinaryNatCode.encode i))) =
      IntegralClearedCoefficientBits.maskedProgram (source P F q) (pair c (BinaryNatCode.encode i)))
    (c : List Bool) (t : ℕ) :
    (RecursiveFold.encState (((program P F q).controller.reference answer)^[t]
      ((program P F q).initial c))).length ≤ stateBound P F q c := by
  have H : (RecursiveFold.encState (((program P F q).controller.reference answer)^[t]
      ((program P F q).initial c))).length ≤
      2 * c.length + 2 * (Turing.MultiTapeTM.encNat (budget P F q c)).length +
        (BinaryNatCode.encode ((source P F q).modulus c)).length + 2 := by
    apply (program P F q).orbit_length
    intro k hk
    rw [partial_value P F q answer he c k hk]
    let : NeZero ((source P F q).modulus c) := ⟨(source P F q).modulus_ne_zero c⟩
    apply ModularFold.bits_length_le (fun c => BinaryNatCode.encode ((source P F q).modulus c)) c
    simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits] using ZMod.val_lt
      (∑ i ∈ Finset.range k, ((source P F q).summand c i : ZMod ((source P F q).modulus c)))
  simpa only [stateBound, Turing.MultiTapeTM.encNat_apply, Nat.size_eq_bits_len, BinaryNatCode.length_encode] using H

theorem requests_iff (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (answer : List Bool → List Bool) (c child : List Bool) :
    (program P F q).controller.Requests answer (budget P F q) c child ↔
      ∃ i < budget P F q c, child = writer P .originalGridTerm (pair c (BinaryNatCode.encode i)) :=
  IntegralClearedCoefficientBits.RecursiveStage.requests_iff (source P F q) (writer P .originalGridTerm) answer c child

theorem requests_rank (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (answer : List Bool → List Bool) (c child : List Bool)
    (hp : IntegralCriticalHistoryTask.isPhase .clearedGridSum c)
    (hc : (program P F q).controller.Requests answer (budget P F q) c child) :
    IntegralCriticalHistoryTask.rank P child < IntegralCriticalHistoryTask.rank P c := by
  obtain ⟨i, _, he⟩ := (requests_iff P F q answer c child).mp hc
  rw [he]
  have H : (7 : ℕ) < IntegralCriticalHistoryTask.phase (pairFst (pair c (BinaryNatCode.encode i))) := by
    simp only [pairFst_pair]
    change IntegralCriticalHistoryTask.phase c = 8 at hp
    omega
  simpa only [pairFst_pair] using writer_lower_rank P .originalGridTerm (pair c (BinaryNatCode.encode i)) H

theorem requests_tasks (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (answer : List Bool → List Bool) (r c child : List Bool)
    (ht : IntegralCriticalHistoryTask.Tasks P r c)
    (hc : (program P F q).controller.Requests answer (budget P F q) c child) :
    IntegralCriticalHistoryTask.Tasks P r child := by
  obtain ⟨i, _, he⟩ := (requests_iff P F q answer c child).mp hc
  rw [he]
  exact writer_tasks P .originalGridTerm r (pair c (BinaryNatCode.encode i)) (by simpa only [pairFst_pair] using ht)

def termInput (P : IntegralCriticalHistoryTask.Parameters) (c : List Bool) : List Bool :=
  pair c (BinaryNatCode.encode (IntegralCriticalHistoryTask.get P .sourceIndex c))

theorem termInput_FP (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P) : termInput P ∈ FP :=
  mem_FP_pair id_mem_FP (IntegralCriticalHistoryTask.get_binary P a .sourceIndex).bits_mem_FP

theorem termInput_parent (P : IntegralCriticalHistoryTask.Parameters) (c : List Bool) : pairFst (termInput P c) = c := by
  simp only [termInput, pairFst_pair]

theorem term_child_index (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase) (c : List Bool) :
    IntegralCriticalHistoryTask.get P .sourceIndex (writer P phase (termInput P c)) =
      IntegralCriticalHistoryTask.get P .sourceIndex c := by
  unfold termInput
  exact writer_index P phase c _ (IntegralCriticalHistoryTask.get_le P .sourceIndex c)

theorem term_child_other (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase)
    (c : List Bool) (f : IntegralCriticalHistoryTask.Field) (hf : f ≠ .sourceIndex) :
    IntegralCriticalHistoryTask.get P f (writer P phase (termInput P c)) = IntegralCriticalHistoryTask.get P f c := by
  rw [writer_other P phase _ f hf, termInput_parent]

theorem mask_packet (S : IntegralClearedCoefficientBits.Source) (c : List Bool) (k : ℕ) :
    ClearedCoordinateExponentBits.mask (IntegralClearedCoefficientBits.maskLayout S) (pair c (BinaryNatCode.encode k)) ↔
      ∀ i < S.free c, FixedWidthPolynomial.entry (S.sourceWidth c) k (S.offset c + i) =
        FixedWidthPolynomial.entry (S.targetWidth c) (S.target c) i := by
  simp only [ClearedCoordinateExponentBits.mask, IntegralClearedCoefficientBits.maskLayout,
    FixedWidthQuery.entry, FixedWidthQuery.coordinate_eq_entry, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  constructor
  · intro h i hi
    have hs : S.offset c + i < S.arity c := by have := S.fit c; omega
    simpa only [ite_eq_left hs, ite_eq_left hi] using h i hi
  · intro h i hi
    have hs : S.offset c + i < S.arity c := by have := S.fit c; omega
    simpa only [ite_eq_left hs, ite_eq_left hi] using h i hi

noncomputable def termProgram (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) : SingleCall.Program :=
  IntegralClearedCoefficientBits.RecursiveStage.term (source P F q) (writer P .productPower)

noncomputable def termController (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) :=
  (termProgram P F q).controller.prepare (termInput P)

theorem term_controls (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : IntegralCriticalScriptGeneratorBits.Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q) : (termProgram P F q).Controls :=
  IntegralClearedCoefficientBits.RecursiveStage.term_controls (source P F q) (access P a F q h)
    (writer P .productPower) (writer_FP P a .productPower)

theorem term_request_iff (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (c : List Bool) :
    (termProgram P F q).request (termInput P c) = true ↔
      ClearedCoordinateExponentBits.mask (IntegralClearedCoefficientBits.maskLayout (source P F q)) (termInput P c) := by
  change decide (ClearedCoordinateExponentBits.mask (IntegralClearedCoefficientBits.maskLayout (source P F q)) (termInput P c)) = true ↔ _
  simp only [decide_eq_true_eq]

theorem term_certificates (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : IntegralCriticalScriptGeneratorBits.Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q) :
    (termController P F q).Certificates (encQ := Turing.MultiTapeTM.encBits) (encS := SingleCall.encState) :=
  (termProgram P F q).controller.prepare_certificates (termInput P)
    ((termProgram P F q).certificates (term_controls P a F q h)) (FP.computable (termInput_FP P a))

noncomputable def termValue (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (c : List Bool) :=
  IntegralClearedCoefficientBits.maskedProgram (source P F q) (termInput P c)

theorem term_value (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (answer : List Bool → List Bool)
    (he : ∀ c, ClearedCoordinateExponentBits.mask (IntegralClearedCoefficientBits.maskLayout (source P F q)) (termInput P c) →
      answer (writer P .productPower (termInput P c)) =
        (IntegralClearedCoefficientBits.termSource (source P F q)).value (termInput P c))
    (c : List Bool) : (termProgram P F q).value answer (termInput P c) = termValue P F q c := by
  by_cases hm : ClearedCoordinateExponentBits.mask (IntegralClearedCoefficientBits.maskLayout (source P F q)) (termInput P c)
  · simpa only [SingleCall.Program.value, termProgram, IntegralClearedCoefficientBits.RecursiveStage.term,
      termValue, IntegralClearedCoefficientBits.maskedProgram, hm, decide_true, ite_true, pairSnd_pair] using he c hm
  · simp only [SingleCall.Program.value, termProgram, IntegralClearedCoefficientBits.RecursiveStage.term,
      termValue, IntegralClearedCoefficientBits.maskedProgram, hm, decide_false, Bool.false_eq_true, ite_false]

theorem term_halted_after (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (answer : List Bool → List Bool) (c : List Bool) :
    (termController P F q).halted
      (((termController P F q).reference answer)^[1] ((termController P F q).initial c)) = true :=
  (termProgram P F q).halted_after answer (termInput P c)

theorem term_output_when_halted (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (answer : List Bool → List Bool)
    (he : ∀ c, ClearedCoordinateExponentBits.mask (IntegralClearedCoefficientBits.maskLayout (source P F q)) (termInput P c) →
      answer (writer P .productPower (termInput P c)) =
        (IntegralClearedCoefficientBits.termSource (source P F q)).value (termInput P c))
    (c : List Bool) (t : ℕ)
    (hh : (termController P F q).halted
      (((termController P F q).reference answer)^[t] ((termController P F q).initial c)) = true) :
    (termController P F q).output
      (((termController P F q).reference answer)^[t] ((termController P F q).initial c)) = termValue P F q c :=
  ((termProgram P F q).output_when_halted answer (termInput P c) t hh).trans (term_value P F q answer he c)

theorem monomial_value_length (S : IntegralClearedCoefficientBits.Source) (p : List Bool) :
    ((IntegralClearedCoefficientBits.termSource S).value p).length ≤ (S.modulus (pairFst p)).size := by
  let := S.ring (pairFst p)
  let : NeZero (S.modulus (pairFst p)) := ⟨S.modulus_ne_zero (pairFst p)⟩
  rw [IntegralClearedCoefficientBits.term_value]
  exact residueBits_length_le _ _

noncomputable def termStateBound (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (c : List Bool) : ℕ :=
  2 * (termInput P c).length + 4 + ((source P F q).modulus c).size

theorem termStateBound_unary (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : IntegralCriticalScriptGeneratorBits.Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q) : UnaryFn (termStateBound P F q) := by
  have HM : UnaryFn (fun c => ((source P F q).modulus c).size) :=
    (UnaryFn.length (access P a F q h).modulus.bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)
  exact (((UnaryFn.const 2).mul (UnaryFn.length (termInput_FP P a))).add (UnaryFn.const 4)).add HM

theorem term_state_length (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (answer : List Bool → List Bool)
    (he : ∀ c, ClearedCoordinateExponentBits.mask (IntegralClearedCoefficientBits.maskLayout (source P F q)) (termInput P c) →
      answer (writer P .productPower (termInput P c)) =
        (IntegralClearedCoefficientBits.termSource (source P F q)).value (termInput P c))
    (c : List Bool) (t : ℕ) :
    (SingleCall.encState (((termController P F q).reference answer)^[t] ((termController P F q).initial c))).length ≤
      termStateBound P F q c := by
  apply (termProgram P F q).state_length_of_bound answer (termInput P c) t
  intro hr
  have hm : ClearedCoordinateExponentBits.mask (IntegralClearedCoefficientBits.maskLayout (source P F q)) (termInput P c) :=
    of_decide_eq_true hr
  change (answer (writer P .productPower (termInput P c))).length ≤ _
  rw [he c hm]
  simpa only [termInput_parent] using monomial_value_length (source P F q) (termInput P c)

theorem term_requests_iff (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (answer : List Bool → List Bool) (c child : List Bool) :
    (termController P F q).Requests answer (fun _ => 1) c child ↔
      ClearedCoordinateExponentBits.mask (IntegralClearedCoefficientBits.maskLayout (source P F q)) (termInput P c) ∧
        child = writer P .productPower (termInput P c) := by
  rw [termController, RecursiveController.Controller.prepare_requests_iff]
  exact IntegralClearedCoefficientBits.RecursiveStage.term_requests_iff (source P F q)
    (writer P .productPower) answer (fun _ => 1) (termInput P c) child

theorem term_requests_rank (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (answer : List Bool → List Bool) (c child : List Bool)
    (hp : IntegralCriticalHistoryTask.isPhase .originalGridTerm c)
    (hc : (termController P F q).Requests answer (fun _ => 1) c child) :
    IntegralCriticalHistoryTask.rank P child < IntegralCriticalHistoryTask.rank P c := by
  obtain ⟨_, he⟩ := (term_requests_iff P F q answer c child).mp hc
  rw [he]
  have H : (6 : ℕ) < IntegralCriticalHistoryTask.phase (pairFst (termInput P c)) := by
    rw [termInput_parent]
    change IntegralCriticalHistoryTask.phase c = 7 at hp
    omega
  simpa only [termInput_parent] using writer_lower_rank P .productPower (termInput P c) H

theorem term_requests_tasks (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (answer : List Bool → List Bool) (r c child : List Bool)
    (ht : IntegralCriticalHistoryTask.Tasks P r c)
    (hc : (termController P F q).Requests answer (fun _ => 1) c child) : IntegralCriticalHistoryTask.Tasks P r child := by
  obtain ⟨_, he⟩ := (term_requests_iff P F q answer c child).mp hc
  rw [he]
  exact writer_tasks P .productPower r (termInput P c) (by simpa only [termInput_parent] using ht)

end LeanCanny.Algebra.IntegralCriticalFlatGridBits
