/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalHistoryTask
public import LeanCanny.Algebra.IntegralCriticalScriptQuery
public import LeanCanny.Algebra.IntegralCriticalScriptFP

/-! # Flat companion requests for actual critical coefficients

A legacy coefficient packet is flattened into the common task format.
The root and birth are preserved, the phase decreases from companion to
critical coefficient, and every numeric field is bounded by the root cap.
Controller certification uses original metadata and never assumes a
polynomial-coefficient evaluator.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatCompanionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

/-- The input is `pair parent (pair coefficient (pair row col))`. -/
def fieldValue (F : IntegralCriticalHistoryTask.Parameters) (p : List Bool) (i : ℕ) : ℕ :=
  if i = 0 then IntegralCriticalHistoryTask.modulus F (pairFst p)
  else if i = 1 then Nat.fromBitsLE (IntegralPowerProductBits.rowWord p)
  else if i = 2 then Nat.fromBitsLE (IntegralPowerProductBits.colWord p)
  else if i = 3 then Nat.fromBitsLE (IntegralPowerProductBits.factorWord p)
  else 0

def reader (F : IntegralCriticalHistoryTask.Parameters) (z : List Bool) : List Bool :=
  BinaryNatCode.encode (fieldValue F (pairFst z) (Nat.fromBitsLE (pairSnd z)))

theorem reader_FP (F : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access F) : reader F ∈ FP := by
  have HI : BinaryFn (fun z => Nat.fromBitsLE (pairSnd z)) := BinaryFn.fromBits pairSnd_mem_FP
  have HM := (IntegralCriticalHistoryTask.modulus_binary F a).comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  have HR := (BinaryFn.fromBits IntegralPowerProductBits.rowWord_FP).comp pairFst_mem_FP
  have HC := (BinaryFn.fromBits IntegralPowerProductBits.colWord_FP).comp pairFst_mem_FP
  have HK := (BinaryFn.fromBits IntegralPowerProductBits.factorWord_FP).comp pairFst_mem_FP
  exact (BinaryFn.ite (HI.eq (BinaryFn.const 0)) HM
    (BinaryFn.ite (HI.eq (BinaryFn.const 1)) HR
      (BinaryFn.ite (HI.eq (BinaryFn.const 2)) HC
        (BinaryFn.ite (HI.eq (BinaryFn.const 3)) HK (BinaryFn.const 0))))).bits_mem_FP

def writer (F : IntegralCriticalHistoryTask.Parameters) : List Bool → List Bool :=
  IntegralCriticalHistoryTask.child F pairFst (IntegralCriticalHistoryTask.birth F ∘ pairFst) .criticalCoefficient (reader F)

theorem writer_FP (F : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access F) : writer F ∈ FP :=
  IntegralCriticalHistoryTask.child_FP F a pairFst pairFst_mem_FP _
    ((BinaryFn.ofUnary (RankedHistoryTask.birth_unary _ (IntegralCriticalHistoryTask.birthCap_unary F a))).comp pairFst_mem_FP)
    .criticalCoefficient _ (reader_FP F a)

theorem writer_root (F : IntegralCriticalHistoryTask.Parameters) (p : List Bool) :
    RankedHistoryTask.root (writer F p) = RankedHistoryTask.root (pairFst p) :=
  IntegralCriticalHistoryTask.child_root F _ _ _ _ p

theorem writer_birth (F : IntegralCriticalHistoryTask.Parameters) (p : List Bool) :
    IntegralCriticalHistoryTask.birth F (writer F p) = IntegralCriticalHistoryTask.birth F (pairFst p) := by
  unfold writer IntegralCriticalHistoryTask.child
  rw [RankedHistoryFields.flatten_eq_pack]
  exact RankedHistoryTask.birth_pack _ _ _ _ _ (min_le_right _ _)

theorem writer_phase (F : IntegralCriticalHistoryTask.Parameters) (p : List Bool) :
    IntegralCriticalHistoryTask.phase (writer F p) = IntegralCriticalHistoryTask.Phase.criticalCoefficient.code := by
  unfold writer IntegralCriticalHistoryTask.child
  rw [RankedHistoryFields.flatten_eq_pack]
  exact RankedHistoryTask.phase_pack _ _ _ _ _ IntegralCriticalHistoryTask.Phase.criticalCoefficient.code_lt

theorem writer_get (F : IntegralCriticalHistoryTask.Parameters) (p : List Bool) (f : IntegralCriticalHistoryTask.Field) :
    IntegralCriticalHistoryTask.get F f (writer F p) = min (fieldValue F p f.code) (IntegralCriticalHistoryTask.numericCap F (RankedHistoryTask.root (pairFst p))) := by
  rw [writer, IntegralCriticalHistoryTask.child_get]
  simp only [reader, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem writer_packet_get (F : IntegralCriticalHistoryTask.Parameters) (c : List Bool) (k r t : ℕ)
    (f : IntegralCriticalHistoryTask.Field) :
    IntegralCriticalHistoryTask.get F f (writer F (pair c (pair (BinaryNatCode.encode k)
      (pair (BinaryNatCode.encode r) (BinaryNatCode.encode t))))) =
      min (if f.code = 0 then IntegralCriticalHistoryTask.modulus F c else if f.code = 1 then r
        else if f.code = 2 then t else if f.code = 3 then k else 0)
        (IntegralCriticalHistoryTask.numericCap F (RankedHistoryTask.root c)) := by
  rw [writer_get]
  simp only [fieldValue, IntegralPowerProductBits.factorWord, IntegralPowerProductBits.rowWord,
    IntegralPowerProductBits.colWord, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem writer_packet_fields (F : IntegralCriticalHistoryTask.Parameters) (c : List Bool) (k r t : ℕ)
    (hr : r ≤ IntegralCriticalHistoryTask.numericCap F (RankedHistoryTask.root c))
    (ht : t ≤ IntegralCriticalHistoryTask.numericCap F (RankedHistoryTask.root c))
    (hk : k ≤ IntegralCriticalHistoryTask.numericCap F (RankedHistoryTask.root c)) :
    let p := writer F (pair c (pair (BinaryNatCode.encode k) (pair (BinaryNatCode.encode r) (BinaryNatCode.encode t))))
    IntegralCriticalHistoryTask.get F .row p = r ∧ IntegralCriticalHistoryTask.get F .col p = t ∧
      IntegralCriticalHistoryTask.get F .coefficient p = k := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [writer_packet_get]; exact min_eq_left hr
  · rw [writer_packet_get]; exact min_eq_left ht
  · rw [writer_packet_get]; exact min_eq_left hk

theorem writer_get_eq (F : IntegralCriticalHistoryTask.Parameters) (p : List Bool) (f : IntegralCriticalHistoryTask.Field)
    (h : fieldValue F p f.code ≤ IntegralCriticalHistoryTask.numericCap F (RankedHistoryTask.root (pairFst p))) :
    IntegralCriticalHistoryTask.get F f (writer F p) = fieldValue F p f.code := by
  rw [writer_get, min_eq_left h]

theorem modulus_le (F : IntegralCriticalHistoryTask.Parameters) (q : List Bool) : IntegralCriticalHistoryTask.modulus F q ≤ IntegralCriticalHistoryTask.numericCap F (RankedHistoryTask.root q) := by
  have H := IntegralCriticalHistoryTask.get_le F .modulus q
  have HP := IntegralCriticalHistoryTask.numericCap_pos F (RankedHistoryTask.root q)
  unfold IntegralCriticalHistoryTask.modulus
  split_ifs <;> omega

theorem writer_modulus (F : IntegralCriticalHistoryTask.Parameters) (p : List Bool) :
    IntegralCriticalHistoryTask.modulus F (writer F p) = IntegralCriticalHistoryTask.modulus F (pairFst p) := by
  have HG : IntegralCriticalHistoryTask.get F .modulus (writer F p) = IntegralCriticalHistoryTask.modulus F (pairFst p) :=
    writer_get_eq F p .modulus (modulus_le F _)
  unfold IntegralCriticalHistoryTask.modulus
  rw [HG]
  exact ite_eq_right (IntegralCriticalHistoryTask.modulus_ne_zero F _)

theorem writer_lower_rank (F : IntegralCriticalHistoryTask.Parameters) (p : List Bool) (hp : IntegralCriticalHistoryTask.isPhase .companion (pairFst p)) :
    IntegralCriticalHistoryTask.rank F (writer F p) < IntegralCriticalHistoryTask.rank F (pairFst p) := by
  apply IntegralCriticalHistoryTask.child_lower_phase F pairFst (IntegralCriticalHistoryTask.birth F ∘ pairFst) .criticalCoefficient (reader F) p rfl
  change 25 < IntegralCriticalHistoryTask.phase (pairFst p)
  change IntegralCriticalHistoryTask.phase (pairFst p) = 26 at hp
  omega

theorem writer_tasks (F : IntegralCriticalHistoryTask.Parameters) (r p : List Bool) (h : IntegralCriticalHistoryTask.Tasks F r (pairFst p)) :
    IntegralCriticalHistoryTask.Tasks F r (writer F p) :=
  IntegralCriticalHistoryTask.child_tasks F pairFst _ .criticalCoefficient (reader F) r p h (min_le_right _ _)

/-- The script source for the primitive metadata certificate. -/
noncomputable def metadata (F : IntegralCriticalScriptGeneratorBits.Queries) : IntegralCriticalScriptFP.Family where
  ambient := F.ambient
  sourceWidth := F.sourceWidth
  degreeBound := F.degreeBound
  height := F.height
  rules := F.rules
  modulus := F.modulus
  modulus_ne_zero := F.modulus_ne_zero

/-- A semantic matrix reader; controller certification does not assume its cost. -/
noncomputable def coefficientAt (F : IntegralCriticalScriptGeneratorBits.Queries) (c : List Bool) (k r t : ℕ) : List Bool :=
  residueBits ((IntegralCriticalScriptGeneratorBits.generatorFamily F).coefficient c k
    ⟨r % count ((IntegralCriticalScript.older (F.rules c) (F.selected c)).length) (F.width c),
      Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩
    ⟨t % count ((IntegralCriticalScript.older (F.rules c) (F.selected c)).length) (F.width c),
      Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩)

noncomputable def coefficient (F : IntegralCriticalScriptGeneratorBits.Queries) (p : List Bool) : List Bool :=
  coefficientAt F (pairFst p) (Nat.fromBitsLE (IntegralPowerProductBits.factorWord p))
    (Nat.fromBitsLE (IntegralPowerProductBits.rowWord p)) (Nat.fromBitsLE (IntegralPowerProductBits.colWord p))

theorem coefficient_packet (F : IntegralCriticalScriptGeneratorBits.Queries) (c : List Bool) (k : ℕ)
    (r t : Fin (count ((IntegralCriticalScript.older (F.rules c) (F.selected c)).length) (F.width c))) :
    coefficient F (pair c (pair (BinaryNatCode.encode k) (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) =
      residueBits ((IntegralCriticalScriptGeneratorBits.generatorFamily F).coefficient c k r t) := by
  simp only [coefficient, IntegralPowerProductBits.factorWord, IntegralPowerProductBits.rowWord,
    IntegralPowerProductBits.colWord, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  simp only [coefficientAt, Nat.mod_eq_of_lt r.isLt, Nat.mod_eq_of_lt t.isLt]
  rfl

noncomputable def program (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries) := IntegralCriticalScriptGeneratorBits.program F (writer P)

theorem program_controls (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (h : IntegralCriticalScriptGeneratorBits.Controls F) (n : IntegralCriticalScriptFP.Access (metadata F)) : (program P F).Controls :=
  IntegralCriticalScriptGeneratorBits.program_controls F h (IntegralCriticalScriptFP.access (metadata F) n) (coefficient F) (coefficient_packet F) (writer P) (writer_FP P a)

noncomputable def coefficientQueries (F : IntegralCriticalScriptGeneratorBits.Queries) :
    IntegralCriticalScriptQueryBits.GeneratorQueries F where
  coefficientIndex := IntegralScalarGeneratorBits.index (IntegralCriticalScriptGeneratorBits.scalarFamily F)
  target _ := 0
  row c := (IntegralCriticalScriptGeneratorBits.scalarFamily F).oldRow c
  col c := (IntegralCriticalScriptGeneratorBits.scalarFamily F).oldCol c

/-- The local companion request reads the deterministic creating polynomial. -/
theorem coefficient_source_value (F : IntegralCriticalScriptGeneratorBits.Queries) (c : List Bool) :
    (IntegralCriticalScriptQueryBits.generatorSource F (coefficientQueries F)).value c =
      residueBits ((IntegralCriticalScriptGeneratorBits.scalarFamily F).coefficient c
        (IntegralScalarGeneratorBits.index (IntegralCriticalScriptGeneratorBits.scalarFamily F) c)
        ((IntegralCriticalScriptGeneratorBits.scalarFamily F).oldRow c)
        ((IntegralCriticalScriptGeneratorBits.scalarFamily F).oldCol c)) := rfl

theorem program_value (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (answer : List Bool → List Bool)
    (ha : ∀ c, IntegralScalarGeneratorBits.request (IntegralCriticalScriptGeneratorBits.scalarFamily F) c →
      answer ((program P F).query c) = (IntegralCriticalScriptQueryBits.generatorSource F (coefficientQueries F)).value c)
    (c : List Bool) : (program P F).value answer c = (IntegralCriticalScriptGeneratorBits.generatorFamily F).value c := by
  apply IntegralCriticalScriptGeneratorBits.program_value F (writer P) answer
  intro q hq
  exact (ha q hq).trans (coefficient_source_value F q)

theorem program_query_modulus (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (c : List Bool) (h : F.modulus c = IntegralCriticalHistoryTask.modulus P c) :
    IntegralCriticalHistoryTask.modulus P ((program P F).query c) = F.modulus c := by
  change IntegralCriticalHistoryTask.modulus P
    (writer P (IntegralScalarGeneratorBits.coefficientQuery (IntegralCriticalScriptGeneratorBits.scalarFamily F) c)) = _
  rw [writer_modulus]
  simpa only [IntegralScalarGeneratorBits.coefficientQuery, pairFst_pair] using h.symm

theorem program_lower_rank (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries) (c : List Bool) (hp : IntegralCriticalHistoryTask.isPhase .companion c) :
    IntegralCriticalHistoryTask.rank P ((program P F).query c) < IntegralCriticalHistoryTask.rank P c := by
  change IntegralCriticalHistoryTask.rank P (writer P (IntegralScalarGeneratorBits.coefficientQuery (IntegralCriticalScriptGeneratorBits.scalarFamily F) c)) < _
  have HH : IntegralCriticalHistoryTask.isPhase .companion
      (pairFst (IntegralScalarGeneratorBits.coefficientQuery (IntegralCriticalScriptGeneratorBits.scalarFamily F) c)) := by
    simpa only [IntegralScalarGeneratorBits.coefficientQuery, pairFst_pair] using hp
  simpa only [IntegralScalarGeneratorBits.coefficientQuery, pairFst_pair] using
    writer_lower_rank P (IntegralScalarGeneratorBits.coefficientQuery (IntegralCriticalScriptGeneratorBits.scalarFamily F) c) HH

end LeanCanny.Algebra.IntegralCriticalFlatCompanionBits
