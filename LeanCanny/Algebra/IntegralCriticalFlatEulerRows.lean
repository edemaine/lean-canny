/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalFlatEuler

/-! # Flat Euler rows, sums, and coordinate-gradient terms

The source decoder changes query fields only. Spatial child writers replace
the target and free derivative rank, mark derivative sources explicitly,
and copy the remaining bounded fields into a fresh root-preserving task.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatEulerRowsBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalHistoryTask.rank IntegralCriticalHistoryTask.Tasks

def row (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralEulerBits.Source) (c : List Bool) : Fin (S.rank c) :=
  ⟨IntegralCriticalHistoryTask.get P .row c % S.rank c,
    Nat.mod_lt _ ((Nat.zero_le (S.row c).val).trans_lt (S.row c).isLt)⟩
def col (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralEulerBits.Source) (c : List Bool) : Fin (S.rank c) :=
  ⟨IntegralCriticalHistoryTask.get P .col c % S.rank c,
    Nat.mod_lt _ ((Nat.zero_le (S.col c).val).trans_lt (S.col c).isLt)⟩

noncomputable def decoded (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralEulerBits.Source) : IntegralEulerBits.Source :=
  S.requery id (IntegralCriticalHistoryTask.get P .target) (row P S) (col P S)

noncomputable def decodedAccess (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (S : IntegralEulerBits.Source) (h : IntegralEulerBits.Access S) : IntegralEulerBits.Access (decoded P S) :=
  h.requery S id _ _ _ id_mem_FP (IntegralCriticalHistoryTask.get_binary P a .target)
    ((IntegralCriticalHistoryTask.get_binary P a .row).mod h.rank)
    ((IntegralCriticalHistoryTask.get_binary P a .col).mod h.rank)

theorem decoded_lower (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralEulerBits.Source)
    (c : List Bool) (i : Fin (S.free c)) :
    letI := S.ring c
    (decoded P S).lowerPolynomial c i = S.lowerPolynomial c i := rfl

theorem decoded_gradient (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralEulerBits.Source)
    (c : List Bool) (i : Fin (S.free c)) :
    letI := S.ring c
    IntegralCriticalGradientBits.polynomial (decoded P S).toGradient c i =
      IntegralCriticalGradientBits.polynomial S.toGradient c i := rfl

theorem decoded_sum (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralEulerBits.Source) (c : List Bool) :
    letI := S.ring c
    (decoded P S).sumPolynomial c = S.sumPolynomial c := rfl

def selected (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralEulerBits.Source) (c : List Bool) : Fin (S.free c) :=
  ⟨IntegralCriticalHistoryTask.get P .derivative c % S.free c, Nat.mod_lt _ (S.free_pos c)⟩

theorem selected_binary (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (S : IntegralEulerBits.Source) (h : IntegralEulerBits.Access S) : BinaryFn (fun c => (selected P S c).val) :=
  (IntegralCriticalHistoryTask.get_binary P a .derivative).mod (BinaryFn.ofUnary h.free)

def coordinateWord (p : List Bool) := pairFst (pairSnd p)
def targetWord (p : List Bool) := pairSnd (pairSnd p)
theorem coordinateWord_FP : coordinateWord ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem targetWord_FP : targetWord ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP

def copyReader (P : IntegralCriticalHistoryTask.Parameters) (z : List Bool) : List Bool :=
  RankedHistoryFields.read (IntegralCriticalHistoryTask.numericCap P) 16
    (pair (pairFst (pairFst z)) (pairSnd z))

theorem copyReader_FP (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P) : copyReader P ∈ FP :=
  mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)
    (RankedHistoryFields.read_FP _ _ (IntegralCriticalHistoryTask.numericCap_binary P a))

def spatialReader (P : IntegralCriticalHistoryTask.Parameters) (expression : ℕ) (z : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairSnd z) = 4 then targetWord (pairFst z)
  else if Nat.fromBitsLE (pairSnd z) = 6 then coordinateWord (pairFst z)
  else if Nat.fromBitsLE (pairSnd z) = 5 then BinaryNatCode.encode expression
  else copyReader P z

theorem spatialReader_FP (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P) (expression : ℕ) :
    spatialReader P expression ∈ FP := by
  have HI : BinaryFn (fun z => Nat.fromBitsLE (pairSnd z)) := BinaryFn.fromBits pairSnd_mem_FP
  exact (HI.eq (BinaryFn.const 4)).ite_mem_FP (mem_FP_comp (f := pairFst) (g := targetWord) pairFst_mem_FP targetWord_FP)
    ((HI.eq (BinaryFn.const 6)).ite_mem_FP (mem_FP_comp (f := pairFst) (g := coordinateWord) pairFst_mem_FP coordinateWord_FP)
      ((HI.eq (BinaryFn.const 5)).ite_mem_FP (constFn_mem_FP _) (copyReader_FP P a)))

def spatial (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase)
    (expression : ℕ) : List Bool → List Bool :=
  IntegralCriticalHistoryTask.child P pairFst (IntegralCriticalHistoryTask.birth P ∘ pairFst) phase (spatialReader P expression)

theorem spatial_FP (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (phase : IntegralCriticalHistoryTask.Phase) (expression : ℕ) : spatial P phase expression ∈ FP :=
  IntegralCriticalHistoryTask.child_FP P a pairFst pairFst_mem_FP _
    ((BinaryFn.ofUnary (RankedHistoryTask.birth_unary _ (IntegralCriticalHistoryTask.birthCap_unary P a))).comp pairFst_mem_FP)
    phase _ (spatialReader_FP P a expression)

theorem spatial_root (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase)
    (expression : ℕ) (p : List Bool) : RankedHistoryTask.root (spatial P phase expression p) = RankedHistoryTask.root (pairFst p) :=
  IntegralCriticalHistoryTask.child_root P _ _ _ _ p

theorem spatial_birth (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase)
    (expression : ℕ) (p : List Bool) :
    IntegralCriticalHistoryTask.birth P (spatial P phase expression p) = IntegralCriticalHistoryTask.birth P (pairFst p) := by
  unfold spatial IntegralCriticalHistoryTask.child
  rw [RankedHistoryFields.flatten_eq_pack]
  exact RankedHistoryTask.birth_pack _ _ _ _ _ (min_le_right _ _)

theorem spatial_phase (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase)
    (expression : ℕ) (p : List Bool) : IntegralCriticalHistoryTask.phase (spatial P phase expression p) = phase.code := by
  unfold spatial IntegralCriticalHistoryTask.child
  rw [RankedHistoryFields.flatten_eq_pack]
  exact RankedHistoryTask.phase_pack _ _ _ _ _ phase.code_lt

theorem spatial_get (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase)
    (expression : ℕ) (p : List Bool) (f : IntegralCriticalHistoryTask.Field) :
    IntegralCriticalHistoryTask.get P f (spatial P phase expression p) =
      min (if f.code = 4 then Nat.fromBitsLE (targetWord p) else if f.code = 6 then Nat.fromBitsLE (coordinateWord p)
        else if f.code = 5 then expression else IntegralCriticalHistoryTask.get P f (pairFst p))
        (IntegralCriticalHistoryTask.numericCap P (RankedHistoryTask.root (pairFst p))) := by
  rw [spatial, IntegralCriticalHistoryTask.child_get]
  simp only [spatialReader, copyReader, pairFst_pair, pairSnd_pair,
    show Nat.fromBitsLE (BinaryNatCode.encode f.code) = f.code from Nat.fromBitsLE_bits _]
  split_ifs
  · rfl
  · rfl
  · simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
  · rw [RankedHistoryFields.read_packet]
    change min (Nat.fromBitsLE (BinaryNatCode.encode (IntegralCriticalHistoryTask.get P f (pairFst p)))) _ = _
    rw [BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem spatial_other (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase)
    (expression : ℕ) (p : List Bool) (f : IntegralCriticalHistoryTask.Field)
    (h4 : f.code ≠ 4) (h5 : f.code ≠ 5) (h6 : f.code ≠ 6) :
    IntegralCriticalHistoryTask.get P f (spatial P phase expression p) = IntegralCriticalHistoryTask.get P f (pairFst p) := by
  rw [spatial_get, ite_eq_right h4, ite_eq_right h6, ite_eq_right h5]
  exact min_eq_left (IntegralCriticalHistoryTask.get_le P f _)

theorem spatial_modulus (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase)
    (expression : ℕ) (p : List Bool) :
    IntegralCriticalHistoryTask.modulus P (spatial P phase expression p) = IntegralCriticalHistoryTask.modulus P (pairFst p) := by
  unfold IntegralCriticalHistoryTask.modulus
  rw [spatial_other P phase expression p .modulus (by decide) (by decide) (by decide)]

theorem spatial_fields (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase)
    (expression : ℕ) (c : List Bool) (j e : ℕ)
    (hj : j ≤ IntegralCriticalHistoryTask.numericCap P (RankedHistoryTask.root c))
    (he : e ≤ IntegralCriticalHistoryTask.numericCap P (RankedHistoryTask.root c))
    (hx : expression ≤ IntegralCriticalHistoryTask.numericCap P (RankedHistoryTask.root c)) :
    let w := spatial P phase expression (pair c (pair (BinaryNatCode.encode j) (BinaryNatCode.encode e)))
    IntegralCriticalHistoryTask.get P .derivative w = j ∧ IntegralCriticalHistoryTask.get P .target w = e ∧
      IntegralCriticalHistoryTask.get P .expression w = expression := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [spatial_get]
    simpa [IntegralCriticalHistoryTask.Field.code, coordinateWord, BinaryNatCode.encode, Nat.fromBitsLE_bits] using min_eq_left hj
  · rw [spatial_get]
    simpa [IntegralCriticalHistoryTask.Field.code, targetWord, BinaryNatCode.encode, Nat.fromBitsLE_bits] using min_eq_left he
  · rw [spatial_get]
    simpa [IntegralCriticalHistoryTask.Field.code] using min_eq_left hx

theorem spatial_lower_rank (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase)
    (expression : ℕ) (p : List Bool) (h : phase.code < IntegralCriticalHistoryTask.phase (pairFst p)) :
    IntegralCriticalHistoryTask.rank P (spatial P phase expression p) < IntegralCriticalHistoryTask.rank P (pairFst p) :=
  IntegralCriticalHistoryTask.child_lower_phase P pairFst _ phase _ p rfl h

theorem spatial_tasks (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase)
    (expression : ℕ) (r p : List Bool) (h : IntegralCriticalHistoryTask.Tasks P r (pairFst p)) :
    IntegralCriticalHistoryTask.Tasks P r (spatial P phase expression p) :=
  IntegralCriticalHistoryTask.child_tasks P pairFst _ phase _ r p h (min_le_right _ _)

noncomputable def source (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) : IntegralEulerBits.Source :=
  decoded P (IntegralCriticalScriptEulerBits.source F q)

noncomputable def access (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : IntegralCriticalScriptGeneratorBits.Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q) : IntegralEulerBits.Access (source P F q) :=
  decodedAccess P a _ (IntegralCriticalScriptEulerBits.access F q h)

theorem source_target (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (c : List Bool) :
    (source P F q).target c = IntegralCriticalHistoryTask.get P .target c := rfl

theorem source_free (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (c : List Bool) :
    (source P F q).free c = F.ambient c - (IntegralCriticalScript.chosen (F.rules c) (F.selected c)).offset.val + 1 := rfl

theorem source_width (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (c : List Bool) :
    (source P F q).targetWidth c = PurePowerReductionBounds.width ((source P F q).free c)
      (IntegralCriticalScript.chosen (F.rules c) (F.selected c)).degree := rfl

theorem source_objective (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (c : List Bool) :
    IntegralEulerBits.objectiveRank (source P F q) c =
      (IntegralCriticalScript.chosen (F.rules c) (F.selected c)).objective % (source P F q).free c := rfl

theorem source_rank (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (c : List Bool) :
    (source P F q).rank c = count (IntegralCriticalScript.older (F.rules c) (F.selected c)).length (F.width c) := rfl

theorem source_row (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (c : List Bool) :
    ((source P F q).row c).val = IntegralCriticalHistoryTask.get P .row c % (source P F q).rank c := rfl

theorem source_col (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (c : List Bool) :
    ((source P F q).col c).val = IntegralCriticalHistoryTask.get P .col c % (source P F q).rank c := rfl

theorem source_offset (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (c : List Bool) :
    (source P F q).offset c = (IntegralCriticalScript.chosen (F.rules c) (F.selected c)).offset.val := rfl

theorem source_modulus (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (c : List Bool) :
    (source P F q).modulus c = F.modulus c := rfl

theorem selected_val (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralEulerBits.Source) (c : List Bool) :
    (selected P S c).val = IntegralCriticalHistoryTask.get P .derivative c % S.free c := rfl

theorem source_lower (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (c : List Bool) (i : Fin ((source P F q).free c)) :
    letI := (source P F q).ring c
    (source P F q).lowerPolynomial c i = (IntegralCriticalScriptEulerBits.source F q).lowerPolynomial c i := rfl

theorem source_gradient (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (c : List Bool) (i : Fin ((source P F q).free c)) :
    letI := (source P F q).ring c
    IntegralCriticalGradientBits.polynomial (source P F q).toGradient c i =
      IntegralCriticalGradientBits.polynomial (IntegralCriticalScriptEulerBits.source F q).toGradient c i := rfl

theorem source_birth_lower (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (c : List Bool) (i : Fin ((source P F q).free c)) :
    letI := (source P F q).ring c
    (source P F q).lowerPolynomial c i =
      (IntegralHistoryCriticalBits.source (IntegralCriticalScriptGeneratorBits.birthSource F c)).toEuler.lowerPolynomial [] i := rfl

theorem source_birth_gradient (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (c : List Bool) (i : Fin ((source P F q).free c)) :
    letI := (source P F q).ring c
    IntegralCriticalGradientBits.polynomial (source P F q).toGradient c i =
      IntegralCriticalGradientBits.polynomial
        (IntegralHistoryCriticalBits.source (IntegralCriticalScriptGeneratorBits.birthSource F c)).toEuler.toGradient [] i := rfl

theorem selected_le (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralEulerBits.Source) (c : List Bool) :
    (selected P S c).val ≤ IntegralCriticalHistoryTask.numericCap P (RankedHistoryTask.root c) :=
  (Nat.mod_le _ _).trans (IntegralCriticalHistoryTask.get_le P .derivative c)

attribute [local irreducible] source

noncomputable def lowerProgram (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) : SingleCall.Program :=
  IntegralEulerBits.LowerStage.program (source P F q) (selected P (source P F q))
    (IntegralCriticalFlatEulerBits.next P .eulerObjective) (spatial P .clearedGridSum 1)

theorem lower_controls (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : IntegralCriticalScriptGeneratorBits.Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q) : (lowerProgram P F q).Controls :=
  IntegralEulerBits.LowerStage.controls _ (access P a F q h) _
    (selected_binary P a _ (access P a F q h)) _ _
    (IntegralCriticalFlatEulerBits.next_FP P a .eulerObjective) (spatial_FP P a .clearedGridSum 1)

theorem lower_value (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (answer : List Bool → List Bool)
    (ho : ∀ c, answer (IntegralCriticalFlatEulerBits.next P .eulerObjective c) = (source P F q).objectiveValue c)
    (hg : ∀ p, answer (spatial P .clearedGridSum 1 p) = (IntegralCriticalGradientBits.family (source P F q).toGradient).value p)
    (c : List Bool) : (lowerProgram P F q).value answer c =
      (source P F q).lowerValue (selected P (source P F q)) c :=
  IntegralEulerBits.LowerStage.value_eq _ _ _ _ answer ho hg c

theorem lower_halted_after (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (answer : List Bool → List Bool) (c : List Bool) :
    (lowerProgram P F q).controller.halted
      (((lowerProgram P F q).controller.reference answer)^[1] (SingleCall.Program.initial c)) = true :=
  (lowerProgram P F q).halted_after answer c

theorem lower_query_rank (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (c : List Bool)
    (hp : IntegralCriticalHistoryTask.isPhase .eulerLower c) :
    IntegralCriticalHistoryTask.rank P ((lowerProgram P F q).query c) < IntegralCriticalHistoryTask.rank P c := by
  change IntegralCriticalHistoryTask.rank P
    (if (selected P (source P F q) c).val = IntegralEulerBits.objectiveRank (source P F q) c then
      IntegralCriticalFlatEulerBits.next P .eulerObjective c else
      spatial P .clearedGridSum 1 (IntegralEulerBits.lowerGradientQuery (source P F q) (selected P (source P F q)) c)) < _
  split_ifs
  · apply IntegralCriticalFlatEulerBits.next_lower_rank
    change 15 < IntegralCriticalHistoryTask.phase c
    change IntegralCriticalHistoryTask.phase c = 16 at hp
    omega
  · have H : (8 : ℕ) < IntegralCriticalHistoryTask.phase
        (pairFst (IntegralEulerBits.lowerGradientQuery (source P F q) (selected P (source P F q)) c)) := by
      simp only [IntegralEulerBits.lowerGradientQuery, pairFst_pair]
      change IntegralCriticalHistoryTask.phase c = 16 at hp
      omega
    simpa only [IntegralEulerBits.lowerGradientQuery, pairFst_pair] using
      spatial_lower_rank P .clearedGridSum 1
        (IntegralEulerBits.lowerGradientQuery (source P F q) (selected P (source P F q)) c) H

theorem lower_query_tasks (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (r c : List Bool)
    (ht : IntegralCriticalHistoryTask.Tasks P r c) :
    IntegralCriticalHistoryTask.Tasks P r ((lowerProgram P F q).query c) := by
  change IntegralCriticalHistoryTask.Tasks P r
    (if (selected P (source P F q) c).val = IntegralEulerBits.objectiveRank (source P F q) c then
      IntegralCriticalFlatEulerBits.next P .eulerObjective c else
      spatial P .clearedGridSum 1 (IntegralEulerBits.lowerGradientQuery (source P F q) (selected P (source P F q)) c))
  split_ifs
  · exact IntegralCriticalFlatEulerBits.next_tasks P .eulerObjective r c ht
  · apply spatial_tasks P .clearedGridSum 1 r
    simpa only [IntegralEulerBits.lowerGradientQuery, pairFst_pair] using ht

theorem lower_gradient_fields (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (c : List Bool) :
    let w := spatial P .clearedGridSum 1
      (IntegralEulerBits.lowerGradientQuery (source P F q) (selected P (source P F q)) c)
    IntegralCriticalHistoryTask.get P .derivative w = (selected P (source P F q) c).val ∧
      IntegralCriticalHistoryTask.get P .target w = IntegralCriticalHistoryTask.get P .target c ∧
      IntegralCriticalHistoryTask.get P .expression w = 1 := by
  have H := spatial_fields P .clearedGridSum 1 c (selected P (source P F q) c).val ((source P F q).target c)
    (selected_le P _ c) (by rw [source_target]; exact IntegralCriticalHistoryTask.get_le P .target c)
    (IntegralCriticalHistoryTask.numericCap_pos P _)
  simpa only [IntegralEulerBits.lowerGradientQuery, source_target] using H

theorem gradient_index_packet (S : IntegralEulerBits.Source) (c : List Bool) (j : Fin (S.free c)) (e : ℕ) :
    (IntegralCriticalGradientBits.selected S.toGradient
      (pair c (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode e)))).val = S.offset c + j.val := by
  change S.offset (pairFst _) + min (Nat.fromBitsLE (pairFst (pairSnd _))) (S.free (pairFst _) - 1) = _
  simp only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [min_eq_left (by have := j.isLt; omega)]

def packet (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralEulerBits.Source) (c : List Bool) : List Bool :=
  pair c (pair (BinaryNatCode.encode (selected P S c).val) (BinaryNatCode.encode (S.target c)))

theorem packet_FP (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (S : IntegralEulerBits.Source) (h : IntegralEulerBits.Access S) : packet P S ∈ FP :=
  mem_FP_pair id_mem_FP (mem_FP_pair (selected_binary P a S h).bits_mem_FP h.target.bits_mem_FP)

def productGradientQuery (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralEulerBits.Source) (c : List Bool) : List Bool :=
  IntegralCriticalCoordinateProductBits.gradientQuery
    (FixedWidthCoordinateMulBits.query (IntegralCriticalCoordinateProductBits.arity S.toGradient)
      (IntegralCriticalCoordinateProductBits.width S.toGradient) IntegralCriticalCoordinateProductBits.selected
      IntegralCriticalCoordinateProductBits.targetWord (packet P S c))

theorem productGradientQuery_parent (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralEulerBits.Source) (c : List Bool) :
    pairFst (productGradientQuery P S c) = c := by
  simp only [productGradientQuery, IntegralCriticalCoordinateProductBits.gradientQuery,
    FixedWidthCoordinateMulBits.query, packet, pairFst_pair]

def loweredTarget (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralEulerBits.Source) (c : List Bool) : ℕ :=
  Nat.fromBitsLE (FixedWidthCoordinateMulBits.packed (IntegralCriticalCoordinateProductBits.arity S.toGradient)
    (IntegralCriticalCoordinateProductBits.width S.toGradient) IntegralCriticalCoordinateProductBits.selected
    IntegralCriticalCoordinateProductBits.targetWord (packet P S c))

theorem loweredTarget_eq (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralEulerBits.Source) (c : List Bool) :
    loweredTarget P S c = Nat.fromBitsLE (FixedWidthNatVector.encode (S.free c) (S.targetWidth c)
      (fun i => (if i < S.free c then FixedWidthPolynomial.entry (S.targetWidth c) (S.target c) i else 0) -
        if i = (selected P S c).val then 1 else 0)) := by
  have HL : FixedWidthCoordinateMulBits.lowered (IntegralCriticalCoordinateProductBits.arity S.toGradient)
      (IntegralCriticalCoordinateProductBits.width S.toGradient) IntegralCriticalCoordinateProductBits.selected
      IntegralCriticalCoordinateProductBits.targetWord (packet P S c) =
      (fun i => (if i < S.free c then FixedWidthPolynomial.entry (S.targetWidth c) (S.target c) i else 0) -
        if i = (selected P S c).val then 1 else 0) := by
    funext i
    simp only [FixedWidthCoordinateMulBits.lowered, FixedWidthQuery.entry, FixedWidthQuery.coordinate_eq_entry,
      IntegralCriticalCoordinateProductBits.arity, IntegralCriticalCoordinateProductBits.width,
      IntegralCriticalCoordinateProductBits.selected, IntegralCriticalCoordinateProductBits.targetWord,
      packet, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  unfold loweredTarget FixedWidthCoordinateMulBits.packed
  rw [HL]
  simp only [IntegralCriticalCoordinateProductBits.arity, IntegralCriticalCoordinateProductBits.width, packet, pairFst_pair]

theorem loweredTarget_lt (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralEulerBits.Source) (c : List Bool) :
    loweredTarget P S c < FixedWidthPolynomial.count (S.free c) (S.targetWidth c) := by
  have H := Nat.fromBitsLE_lt_pow_length
    (FixedWidthCoordinateMulBits.packed (IntegralCriticalCoordinateProductBits.arity S.toGradient)
      (IntegralCriticalCoordinateProductBits.width S.toGradient) IntegralCriticalCoordinateProductBits.selected
      IntegralCriticalCoordinateProductBits.targetWord (packet P S c))
  simpa only [loweredTarget, FixedWidthCoordinateMulBits.packed, FixedWidthNatVector.length_encode,
    IntegralCriticalCoordinateProductBits.arity, IntegralCriticalCoordinateProductBits.width,
    packet, pairFst_pair, FixedWidthPolynomial.count, ← pow_mul, Nat.mul_comm] using H

theorem productGradientQuery_eq (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralEulerBits.Source) (c : List Bool) :
    productGradientQuery P S c = pair c (pair (BinaryNatCode.encode (selected P S c).val)
      (BinaryNatCode.encode (loweredTarget P S c))) := by
  simp only [productGradientQuery, IntegralCriticalCoordinateProductBits.gradientQuery,
    FixedWidthCoordinateMulBits.query, packet, pairFst_pair, pairSnd_pair,
    loweredTarget, BinaryNat.normalize_eq_bits, BinaryNatCode.encode]

theorem product_gradient_fields (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralEulerBits.Source)
    (c : List Bool) (he : loweredTarget P S c ≤ IntegralCriticalHistoryTask.numericCap P (RankedHistoryTask.root c)) :
    let w := spatial P .clearedGridSum 1 (productGradientQuery P S c)
    IntegralCriticalHistoryTask.get P .derivative w = (selected P S c).val ∧
      IntegralCriticalHistoryTask.get P .target w = loweredTarget P S c ∧
      IntegralCriticalHistoryTask.get P .expression w = 1 := by
  rw [productGradientQuery_eq]
  exact spatial_fields P .clearedGridSum 1 c _ _ (selected_le P S c) he (IntegralCriticalHistoryTask.numericCap_pos P _)

theorem product_gradient_fields_of_grid (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralEulerBits.Source)
    (c : List Bool) (hgrid : FixedWidthPolynomial.count (S.free c) (S.targetWidth c) ≤
      IntegralCriticalHistoryTask.numericCap P (RankedHistoryTask.root c)) :
    let w := spatial P .clearedGridSum 1 (productGradientQuery P S c)
    IntegralCriticalHistoryTask.get P .derivative w = (selected P S c).val ∧
      IntegralCriticalHistoryTask.get P .target w = loweredTarget P S c ∧
      IntegralCriticalHistoryTask.get P .expression w = 1 :=
  product_gradient_fields P S c ((loweredTarget_lt P S c).le.trans hgrid)

noncomputable def productBase (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralEulerBits.Source) : SingleCall.Program :=
  IntegralCriticalCoordinateProductBits.program S.toGradient (spatial P .clearedGridSum 1)

noncomputable def productProgram (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) : SingleCall.Program where
  request c := if (selected P (source P F q) c).val = IntegralEulerBits.objectiveRank (source P F q) c then false
    else (productBase P (source P F q)).request (packet P (source P F q) c)
  query c := (productBase P (source P F q)).query (packet P (source P F q) c)
  immediate _ := []
  finish := pairSnd

theorem product_controls (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : IntegralCriticalScriptGeneratorBits.Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q) : (productProgram P F q).Controls := by
  have HS : IntegralEulerBits.Access (source P F q) := access P a F q h
  have HB : (productBase P (source P F q)).Controls :=
    IntegralCriticalCoordinateProductBits.program_controls (source P F q).toGradient HS.toGradient
      (spatial P .clearedGridSum 1) (spatial_FP P a .clearedGridSum 1)
  have HP : packet P (source P F q) ∈ FP := packet_FP P a (source P F q) HS
  have HE := (selected_binary P a (source P F q) HS).eq HS.objective
  refine ⟨?_, ?_, constFn_mem_FP [], pairSnd_mem_FP⟩
  · have HR := HE.ite_mem_FP (constFn_mem_FP [false])
      (mem_FP_comp (f := packet P (source P F q)) (g := fun p => [(productBase P (source P F q)).request p]) HP HB.request)
    exact mem_FP_of_eq HR (fun c => by
      change (if _ then [false] else [_]) = [if _ then false else _]
      simp only [IntegralEulerBits.objectiveRank]
      split_ifs <;> rfl)
  · exact mem_FP_comp (f := packet P (source P F q)) (g := (productBase P (source P F q)).query) HP HB.query

theorem product_value_base (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (answer : List Bool → List Bool) (c : List Bool) :
    (productProgram P F q).value answer c =
      if (selected P (source P F q) c).val = IntegralEulerBits.objectiveRank (source P F q) c then []
      else (productBase P (source P F q)).value answer (packet P (source P F q) c) := by
  by_cases he : (selected P (source P F q) c).val = IntegralEulerBits.objectiveRank (source P F q) c <;>
    simp only [SingleCall.Program.value, productProgram, he, ite_true, ite_false, Bool.false_eq_true,
      productBase, IntegralCriticalCoordinateProductBits.program, FixedWidthCoordinateMulBits.program, pairSnd_pair]

theorem product_value (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (answer : List Bool → List Bool)
    (hg : ∀ p, answer (spatial P .clearedGridSum 1 p) = (IntegralCriticalGradientBits.family (source P F q).toGradient).value p)
    (c : List Bool) : (productProgram P F q).value answer c =
      if (selected P (source P F q) c).val = IntegralEulerBits.objectiveRank (source P F q) c then []
      else IntegralCriticalCoordinateProductBits.value (source P F q).toGradient (packet P (source P F q) c) := by
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

theorem product_request_iff (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (c : List Bool) :
    (productProgram P F q).request c = true ↔
      (selected P (source P F q) c).val ≠ IntegralEulerBits.objectiveRank (source P F q) c ∧
        0 < FixedWidthPolynomial.entry ((source P F q).targetWidth c) ((source P F q).target c)
          (selected P (source P F q) c).val := by
  by_cases he : (selected P (source P F q) c).val = IntegralEulerBits.objectiveRank (source P F q) c
  · have H : (productProgram P F q).request c = false := ite_eq_left he
    rw [H]
    constructor
    · intro hh; cases hh
    · intro hh; exact (hh.1 he).elim
  · have H : (productProgram P F q).request c = true ↔
        0 < FixedWidthPolynomial.entry ((source P F q).targetWidth c) ((source P F q).target c)
          (selected P (source P F q) c).val := by
      change (if _ then false else _) = true ↔ _
      rw [ite_eq_right he]
      change decide (FixedWidthCoordinateMulBits.positive _ _ _ _ (packet P (source P F q) c)) = true ↔ _
      rw [decide_eq_true_eq, positive_packet]
    exact ⟨fun hh => ⟨he, H.mp hh⟩, fun hh => H.mpr hh.2⟩

theorem product_value_matrix (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (answer : List Bool → List Bool)
    (hg : ∀ p, answer (spatial P .clearedGridSum 1 p) = (IntegralCriticalGradientBits.family (source P F q).toGradient).value p)
    (c : List Bool) :
    letI := (source P F q).ring c
    (productProgram P F q).value answer c =
      if (selected P (source P F q) c).val = IntegralEulerBits.objectiveRank (source P F q) c then [] else
        residueBits ((Algebra.leftMulMatrix ((source P F q).basis c)
          ((MvPolynomial.X (selected P (source P F q) c) *
            IntegralCriticalGradientBits.polynomial (source P F q).toGradient c (selected P (source P F q) c)).coeff
            (RationalSubstitution.Indexed.exponentVector ((source P F q).free c)
              (FixedWidthPolynomial.entry ((source P F q).targetWidth c) ((source P F q).target c))))
          ((source P F q).row c) ((source P F q).col c) : ℤ) : ZMod ((source P F q).modulus c)) := by
  let := (source P F q).ring c
  rw [product_value P F q answer hg]
  split_ifs
  · rfl
  · exact IntegralCriticalCoordinateProductBits.packet (source P F q).toGradient c
      (selected P (source P F q) c) ((source P F q).target c)

theorem product_halted_after (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (answer : List Bool → List Bool) (c : List Bool) :
    (productProgram P F q).controller.halted
      (((productProgram P F q).controller.reference answer)^[1] (SingleCall.Program.initial c)) = true :=
  (productProgram P F q).halted_after answer c

theorem product_query (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (c : List Bool) :
    (productProgram P F q).query c = spatial P .clearedGridSum 1 (productGradientQuery P (source P F q) c) := rfl

theorem product_query_rank (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (c : List Bool)
    (hp : IntegralCriticalHistoryTask.isPhase .coordinateGradientProduct c) :
    IntegralCriticalHistoryTask.rank P ((productProgram P F q).query c) < IntegralCriticalHistoryTask.rank P c := by
  rw [product_query]
  have H : (8 : ℕ) < IntegralCriticalHistoryTask.phase (pairFst (productGradientQuery P (source P F q) c)) := by
    rw [productGradientQuery_parent]
    change IntegralCriticalHistoryTask.phase c = 13 at hp
    omega
  simpa only [productGradientQuery_parent] using spatial_lower_rank P .clearedGridSum 1 _ H

theorem product_query_tasks (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (r c : List Bool)
    (ht : IntegralCriticalHistoryTask.Tasks P r c) :
    IntegralCriticalHistoryTask.Tasks P r ((productProgram P F q).query c) := by
  rw [product_query]
  exact spatial_tasks P .clearedGridSum 1 r (productGradientQuery P (source P F q) c)
    (by simpa only [productGradientQuery_parent] using ht)

def sumTask (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralEulerBits.Source) (p : List Bool) : List Bool :=
  spatial P .coordinateGradientProduct 0 (IntegralEulerBits.termQuery S p)

theorem sumTask_FP (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (S : IntegralEulerBits.Source) (h : IntegralEulerBits.Access S) : sumTask P S ∈ FP :=
  mem_FP_comp (IntegralEulerBits.termQuery_FP S h) (spatial_FP P a .coordinateGradientProduct 0)

theorem sum_fields (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (c : List Bool) (i : ℕ)
    (hi : i ≤ IntegralCriticalHistoryTask.numericCap P (RankedHistoryTask.root c)) :
    let w := sumTask P (source P F q) (pair c (BinaryNatCode.encode i))
    IntegralCriticalHistoryTask.get P .derivative w = i ∧
      IntegralCriticalHistoryTask.get P .target w = IntegralCriticalHistoryTask.get P .target c ∧
      IntegralCriticalHistoryTask.get P .expression w = 0 := by
  have H := spatial_fields P .coordinateGradientProduct 0 c i ((source P F q).target c) hi
    (by rw [source_target]; exact IntegralCriticalHistoryTask.get_le P .target c) (Nat.zero_le _)
  simpa only [sumTask, IntegralEulerBits.termQuery, pairFst_pair, pairSnd_pair, source_target] using H

theorem sumTask_rank (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralEulerBits.Source)
    (c : List Bool) (i : ℕ) (hp : IntegralCriticalHistoryTask.isPhase .eulerSum c) :
    IntegralCriticalHistoryTask.rank P (sumTask P S (pair c (BinaryNatCode.encode i))) < IntegralCriticalHistoryTask.rank P c := by
  unfold sumTask
  have H : (13 : ℕ) < IntegralCriticalHistoryTask.phase
      (pairFst (IntegralEulerBits.termQuery S (pair c (BinaryNatCode.encode i)))) := by
    simp only [IntegralEulerBits.termQuery, pairFst_pair]
    change IntegralCriticalHistoryTask.phase c = 14 at hp
    omega
  have HE : pairFst (IntegralEulerBits.termQuery S (pair c (BinaryNatCode.encode i))) = c := by
    simp only [IntegralEulerBits.termQuery, pairFst_pair]
  simpa only [HE] using
    spatial_lower_rank P .coordinateGradientProduct 0 (IntegralEulerBits.termQuery S (pair c (BinaryNatCode.encode i))) H

theorem sumTask_tasks (P : IntegralCriticalHistoryTask.Parameters) (S : IntegralEulerBits.Source)
    (r c : List Bool) (i : ℕ) (ht : IntegralCriticalHistoryTask.Tasks P r c) :
    IntegralCriticalHistoryTask.Tasks P r (sumTask P S (pair c (BinaryNatCode.encode i))) := by
  unfold sumTask
  exact spatial_tasks P .coordinateGradientProduct 0 r (IntegralEulerBits.termQuery S (pair c (BinaryNatCode.encode i)))
    (by simpa only [IntegralEulerBits.termQuery, pairFst_pair] using ht)

noncomputable def sumProgram (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) : RecursiveFold.Program :=
  IntegralEulerBits.SumStage.program (source P F q) (sumTask P (source P F q))

theorem sum_certificates (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : IntegralCriticalScriptGeneratorBits.Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q) :
    (sumProgram P F q).controller.Certificates
      (encQ := Turing.MultiTapeTM.encBits) (encS := RecursiveFold.encState) :=
  IntegralEulerBits.SumStage.certificates (source P F q) (access P a F q h) (sumTask P (source P F q))
    (sumTask_FP P a (source P F q) (access P a F q h))

theorem sum_partial_value (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (answer : List Bool → List Bool)
    (he : ∀ c i, i < (source P F q).free c →
      answer (sumTask P (source P F q) (pair c (BinaryNatCode.encode i))) =
        residueBits ((source P F q).summand c i : ZMod ((source P F q).modulus c)))
    (c : List Bool) (k : ℕ) (hk : k ≤ (source P F q).free c) :
    (sumProgram P F q).partialValue answer c k =
      residueBits (∑ i ∈ Finset.range k, ((source P F q).summand c i : ZMod ((source P F q).modulus c))) :=
  ModularFold.RecursiveStage.sum_partialValueWithModulus (source P F q).free
    (fun c => BinaryNatCode.encode ((source P F q).modulus c)) (sumTask P (source P F q)) answer
    (source P F q).modulus (funext (fun _ => Nat.fromBitsLE_bits _)) c
    (fun i => ((source P F q).summand c i : ZMod ((source P F q).modulus c)))
    (Nat.pos_of_ne_zero ((source P F q).modulus_ne_zero c)) (he c) k hk

theorem sum_value (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (answer : List Bool → List Bool)
    (he : ∀ c i, i < (source P F q).free c →
      answer (sumTask P (source P F q) (pair c (BinaryNatCode.encode i))) =
        residueBits ((source P F q).summand c i : ZMod ((source P F q).modulus c)))
    (c : List Bool) : (sumProgram P F q).value answer c = (source P F q).sumValue c :=
  (sum_partial_value P F q answer he c _ le_rfl).trans (IntegralEulerBits.sum_value (source P F q) c)

theorem sum_halted_after (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (answer : List Bool → List Bool) (c : List Bool) :
    (sumProgram P F q).controller.halted
      (((sumProgram P F q).controller.reference answer)^[(source P F q).free c] ((sumProgram P F q).initial c)) = true :=
  (sumProgram P F q).halted_after answer c

theorem sum_output_when_halted (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (answer : List Bool → List Bool)
    (he : ∀ c i, i < (source P F q).free c →
      answer (sumTask P (source P F q) (pair c (BinaryNatCode.encode i))) =
        residueBits ((source P F q).summand c i : ZMod ((source P F q).modulus c)))
    (c : List Bool) (t : ℕ)
    (hh : (sumProgram P F q).controller.halted
      (((sumProgram P F q).controller.reference answer)^[t] ((sumProgram P F q).initial c)) = true) :
    (sumProgram P F q).controller.output
      (((sumProgram P F q).controller.reference answer)^[t] ((sumProgram P F q).initial c)) =
        (source P F q).sumValue c :=
  ((sumProgram P F q).output_when_halted answer c t hh).trans (sum_value P F q answer he c)

theorem sum_state_length (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (answer : List Bool → List Bool)
    (he : ∀ c i, i < (source P F q).free c →
      answer (sumTask P (source P F q) (pair c (BinaryNatCode.encode i))) =
        residueBits ((source P F q).summand c i : ZMod ((source P F q).modulus c)))
    (c : List Bool) (t : ℕ) :
    (RecursiveFold.encState (((sumProgram P F q).controller.reference answer)^[t]
      ((sumProgram P F q).initial c))).length ≤
        2 * c.length + 2 * (Turing.MultiTapeTM.encNat ((source P F q).free c)).length +
          (BinaryNatCode.encode ((source P F q).modulus c)).length + 2 := by
  apply (sumProgram P F q).orbit_length
  intro k hk
  rw [sum_partial_value P F q answer he c k hk]
  let : NeZero ((source P F q).modulus c) := ⟨(source P F q).modulus_ne_zero c⟩
  apply ModularFold.bits_length_le (fun c => BinaryNatCode.encode ((source P F q).modulus c)) c
  simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits] using ZMod.val_lt
    (∑ i ∈ Finset.range k, ((source P F q).summand c i : ZMod ((source P F q).modulus c)))

theorem sum_requests_iff (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (answer : List Bool → List Bool) (c child : List Bool) :
    (sumProgram P F q).controller.Requests answer (source P F q).free c child ↔
      ∃ i < (source P F q).free c, child = sumTask P (source P F q) (pair c (BinaryNatCode.encode i)) :=
  IntegralEulerBits.SumStage.requests_iff (source P F q) (sumTask P (source P F q)) answer c child

theorem sum_requests_rank (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (answer : List Bool → List Bool) (c child : List Bool)
    (hp : IntegralCriticalHistoryTask.isPhase .eulerSum c)
    (hc : (sumProgram P F q).controller.Requests answer (source P F q).free c child) :
    IntegralCriticalHistoryTask.rank P child < IntegralCriticalHistoryTask.rank P c := by
  obtain ⟨i, _, he⟩ := (sum_requests_iff P F q answer c child).mp hc
  rw [he]
  exact sumTask_rank P (source P F q) c i hp

theorem sum_requests_tasks (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (answer : List Bool → List Bool) (r c child : List Bool)
    (ht : IntegralCriticalHistoryTask.Tasks P r c)
    (hc : (sumProgram P F q).controller.Requests answer (source P F q).free c child) :
    IntegralCriticalHistoryTask.Tasks P r child := by
  obtain ⟨i, _, he⟩ := (sum_requests_iff P F q answer c child).mp hc
  rw [he]
  exact sumTask_tasks P (source P F q) r c i ht

end LeanCanny.Algebra.IntegralCriticalFlatEulerRowsBits
