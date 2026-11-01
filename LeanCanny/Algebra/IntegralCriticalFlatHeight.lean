/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalHistoryTask
public import LeanCanny.Algebra.IntegralCriticalScriptHeight
public import LeanCanny.Algebra.IntegralCriticalCreatingValue
public import LeanCanny.Computation.PolyTimeBinaryArithmetic

/-! # Flat earlier-birth requests for actual retained generators

A retained numerator is lifted from its deterministic creating command.
Equal low radix digits select one creating companion entry; unequal digits
and missing bank indices give zero without a recursive request. The child
preserves the root and caller modulus and stores only quotient indices.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial UniformIntegralPrefix
open IntegralCriticalScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Scripts extends IntegralCriticalHistoryTask.Parameters where
  rules : ∀ r, List (Command (ambient r) (sourceWidth r) (degree r) (height r))
  length_le : ∀ r, (rules r).length ≤ cap r + 1
  scalar_bound : ∀ r, PurePowerReductionBounds.dimension (ambient r + 1) (degree r) ≤ 2 ^ width r

structure Access (F : Scripts) : Prop extends IntegralCriticalHistoryTask.Access F.toParameters where
  count : UnaryFn (fun r => (F.rules r).length)

def root := RankedHistoryTask.root

def length (F : Scripts) (q : List Bool) : ℕ := (past (F.rules (root q)) (IntegralCriticalHistoryTask.birth F.toParameters q)).length

def index (F : Scripts) (q : List Bool) : ℕ := min (IntegralCriticalHistoryTask.get F.toParameters .sourceIndex q) (length F q)

def radix (F : Scripts) (q : List Bool) : ℕ := count (index F q) (F.width (root q))

def dimension (F : Scripts) (q : List Bool) : ℕ := count (length F q) (F.width (root q))

def row (F : Scripts) (q : List Bool) : ℕ := IntegralCriticalHistoryTask.get F.toParameters .row q % dimension F q

def col (F : Scripts) (q : List Bool) : ℕ := IntegralCriticalHistoryTask.get F.toParameters .col q % dimension F q

def childBirth (F : Scripts) (q : List Bool) : ℕ := length F q - 1 - index F q

def valid (F : Scripts) (q : List Bool) : Prop := IntegralCriticalHistoryTask.get F.toParameters .sourceIndex q < length F q

instance (F : Scripts) (q : List Bool) : Decidable (valid F q) := inferInstanceAs (Decidable (_ < _))

def request (F : Scripts) (q : List Bool) : Prop := valid F q ∧ row F q % radix F q = col F q % radix F q

instance (F : Scripts) (q : List Bool) : Decidable (request F q) := inferInstanceAs (Decidable (_ ∧ _))

theorem length_le_birth (F : Scripts) (q : List Bool) : length F q ≤ IntegralCriticalHistoryTask.birth F.toParameters q := by
  rw [length, past_length]
  exact min_le_left _ _

theorem length_le_full (F : Scripts) (q : List Bool) : length F q ≤ (F.rules (root q)).length := by
  rw [length, past_length]
  exact min_le_right _ _

theorem length_le_cap (F : Scripts) (q : List Bool) : length F q ≤ IntegralCriticalHistoryTask.birthCap F.toParameters (root q) :=
  (length_le_birth F q).trans (min_le_right _ _)

theorem length_unary (F : Scripts) (a : Access F) : UnaryFn (length F) := by
  have H := UnaryFn.fromBitsLE_min
    (BinaryFn.ofUnary (RankedHistoryTask.birth_unary _ (IntegralCriticalHistoryTask.birthCap_unary _ a.toAccess))).bits_mem_FP
    (a.count.comp RankedHistoryTask.root_FP)
  exact H.of_eq (fun q => by rw [BinaryNatCode.encode, Nat.fromBitsLE_bits]; exact (past_length _ _).symm)

theorem index_unary (F : Scripts) (a : Access F) : UnaryFn (index F) :=
  (UnaryFn.fromBitsLE_min (IntegralCriticalHistoryTask.get_binary _ a.toAccess .sourceIndex).bits_mem_FP (length_unary F a)).of_eq
    (fun _ => by rw [BinaryNatCode.encode, Nat.fromBitsLE_bits]; rfl)

theorem radix_binary (F : Scripts) (a : Access F) : BinaryFn (radix F) :=
  ((BinaryFn.const 2).powUnary (a.width.comp RankedHistoryTask.root_FP)).powUnary (index_unary F a)

theorem dimension_binary (F : Scripts) (a : Access F) : BinaryFn (dimension F) :=
  ((BinaryFn.const 2).powUnary (a.width.comp RankedHistoryTask.root_FP)).powUnary (length_unary F a)

theorem row_binary (F : Scripts) (a : Access F) : BinaryFn (row F) :=
  (IntegralCriticalHistoryTask.get_binary _ a.toAccess .row).mod (dimension_binary F a)

theorem col_binary (F : Scripts) (a : Access F) : BinaryFn (col F) :=
  (IntegralCriticalHistoryTask.get_binary _ a.toAccess .col).mod (dimension_binary F a)

theorem childBirth_binary (F : Scripts) (a : Access F) : BinaryFn (childBirth F) :=
  ((BinaryFn.ofUnary (length_unary F a)).sub (BinaryFn.const 1)).sub (BinaryFn.ofUnary (index_unary F a))

theorem request_FP (F : Scripts) (a : Access F) : FPPred (request F) :=
  ((IntegralCriticalHistoryTask.get_binary _ a.toAccess .sourceIndex).lt (BinaryFn.ofUnary (length_unary F a))).and
    (((row_binary F a).mod (radix_binary F a)).eq ((col_binary F a).mod (radix_binary F a)))

def reader (F : Scripts) (p : List Bool) : List Bool :=
  let q := pairFst p
  let k := Nat.fromBitsLE (pairSnd p)
  if k = IntegralCriticalHistoryTask.Field.modulus.code then BinaryNatCode.encode (IntegralCriticalHistoryTask.modulus F.toParameters q) else
  if k = IntegralCriticalHistoryTask.Field.row.code then BinaryNatCode.encode (row F q / radix F q) else
  if k = IntegralCriticalHistoryTask.Field.col.code then BinaryNatCode.encode (col F q / radix F q) else []

theorem reader_FP (F : Scripts) (a : Access F) : reader F ∈ FP := by
  have HI := BinaryFn.fromBits pairSnd_mem_FP
  have HM : BinaryFn (fun p => IntegralCriticalHistoryTask.modulus F.toParameters (pairFst p)) := (IntegralCriticalHistoryTask.modulus_binary _ a.toAccess).comp pairFst_mem_FP
  have HR : BinaryFn (fun p => row F (pairFst p) / radix F (pairFst p)) := ((row_binary F a).div (radix_binary F a)).comp pairFst_mem_FP
  have HC : BinaryFn (fun p => col F (pairFst p) / radix F (pairFst p)) := ((col_binary F a).div (radix_binary F a)).comp pairFst_mem_FP
  exact (HI.eq (BinaryFn.const IntegralCriticalHistoryTask.Field.modulus.code)).ite_mem_FP HM.bits_mem_FP
    ((HI.eq (BinaryFn.const IntegralCriticalHistoryTask.Field.row.code)).ite_mem_FP HR.bits_mem_FP
      ((HI.eq (BinaryFn.const IntegralCriticalHistoryTask.Field.col.code)).ite_mem_FP HC.bits_mem_FP (constFn_mem_FP [])))

def child (F : Scripts) : List Bool → List Bool :=
  IntegralCriticalHistoryTask.child F.toParameters id (childBirth F) .companion (reader F)

theorem child_FP (F : Scripts) (a : Access F) : child F ∈ FP :=
  IntegralCriticalHistoryTask.child_FP _ a.toAccess id id_mem_FP _ (childBirth_binary F a) .companion _ (reader_FP F a)

theorem child_root (F : Scripts) (q : List Bool) : root (child F q) = root q := IntegralCriticalHistoryTask.child_root _ _ _ _ _ _

theorem childBirth_lt (F : Scripts) (q : List Bool) (hv : valid F q) : childBirth F q < IntegralCriticalHistoryTask.birth F.toParameters q := by
  have HL := length_le_birth F q
  unfold valid at hv
  unfold childBirth
  omega

theorem child_rank (F : Scripts) (q : List Bool) (hv : valid F q) :
    IntegralCriticalHistoryTask.rank F.toParameters (child F q) < IntegralCriticalHistoryTask.rank F.toParameters q :=
  IntegralCriticalHistoryTask.child_lower_birth _ id (childBirth F) .companion _ q (childBirth_lt F q hv)

theorem child_length (F : Scripts) (q : List Bool) :
    (child F q).length ≤ IntegralCriticalHistoryTask.wordBudget F.toParameters q :=
  IntegralCriticalHistoryTask.child_length _ id (childBirth F) .companion _ q ((Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans (length_le_cap F q)))

theorem dimension_pos (F : Scripts) (q : List Bool) : 0 < dimension F q := pow_pos (Nat.two_pow_pos _) _

theorem radix_pos (F : Scripts) (q : List Bool) : 0 < radix F q := pow_pos (Nat.two_pow_pos _) _

theorem row_lt (F : Scripts) (q : List Bool) : row F q < dimension F q := Nat.mod_lt _ (dimension_pos F q)

theorem col_lt (F : Scripts) (q : List Bool) : col F q < dimension F q := Nat.mod_lt _ (dimension_pos F q)

theorem dimension_le_cap (F : Scripts) (q : List Bool) :
    dimension F q ≤ IntegralCriticalHistoryTask.numericCap F.toParameters (root q) :=
  IntegralCriticalHistoryTask.born_rank_le _ _ (length_le_cap F q)

theorem modulus_le_cap (F : Scripts) (q : List Bool) :
    IntegralCriticalHistoryTask.modulus F.toParameters q ≤ IntegralCriticalHistoryTask.numericCap F.toParameters (root q) := by
  unfold IntegralCriticalHistoryTask.modulus
  split_ifs
  · exact IntegralCriticalHistoryTask.numericCap_pos _ _
  · exact IntegralCriticalHistoryTask.get_le _ _ _

theorem child_row (F : Scripts) (q : List Bool) :
    IntegralCriticalHistoryTask.get F.toParameters .row (child F q) = row F q / radix F q := by
  unfold child
  rw [IntegralCriticalHistoryTask.child_get]
  simp only [reader, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    IntegralCriticalHistoryTask.Field.code, Nat.reduceEqDiff, ite_false, ite_true, id_eq]
  exact min_eq_left ((Nat.div_le_self _ _).trans ((row_lt F q).le.trans (dimension_le_cap F q)))

theorem child_col (F : Scripts) (q : List Bool) :
    IntegralCriticalHistoryTask.get F.toParameters .col (child F q) = col F q / radix F q := by
  unfold child
  rw [IntegralCriticalHistoryTask.child_get]
  simp only [reader, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    IntegralCriticalHistoryTask.Field.code, Nat.reduceEqDiff, ite_false, ite_true, id_eq]
  exact min_eq_left ((Nat.div_le_self _ _).trans ((col_lt F q).le.trans (dimension_le_cap F q)))

theorem child_modulus (F : Scripts) (q : List Bool) :
    IntegralCriticalHistoryTask.modulus F.toParameters (child F q) = IntegralCriticalHistoryTask.modulus F.toParameters q := by
  have HG : IntegralCriticalHistoryTask.get F.toParameters .modulus (child F q) = IntegralCriticalHistoryTask.modulus F.toParameters q := by
    unfold child
    rw [IntegralCriticalHistoryTask.child_get]
    simp only [reader, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
      IntegralCriticalHistoryTask.Field.code, ite_true, id_eq]
    exact min_eq_left (modulus_le_cap F q)
  unfold IntegralCriticalHistoryTask.modulus at ⊢
  rw [HG, ite_eq_right (IntegralCriticalHistoryTask.modulus_ne_zero _ _)]
  rfl

theorem child_birth (F : Scripts) (q : List Bool) :
    IntegralCriticalHistoryTask.birth F.toParameters (child F q) = childBirth F q := by
  unfold child IntegralCriticalHistoryTask.child
  rw [RankedHistoryFields.flatten_eq_pack]
  exact RankedHistoryTask.birth_pack _ _ _ _ _ ((Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans (length_le_cap F q)))

theorem child_phase (F : Scripts) (q : List Bool) :
    IntegralCriticalHistoryTask.phase (child F q) = IntegralCriticalHistoryTask.Phase.companion.code := by
  unfold child IntegralCriticalHistoryTask.child IntegralCriticalHistoryTask.phase
  rw [RankedHistoryFields.flatten_eq_pack]
  exact RankedHistoryTask.phase_pack _ _ _ _ _ (IntegralCriticalHistoryTask.Phase.code_lt _)

noncomputable def heightQueries (F : Scripts) : IntegralCriticalScriptHeightBits.Queries where
  cap q := F.cap (root q)
  width q := F.width (root q)
  ambient q := F.ambient (root q)
  sourceWidth q := F.sourceWidth (root q)
  degreeBound q := F.degree (root q)
  height q := F.height (root q)
  rules q := F.rules (root q)
  length_le q := F.length_le (root q)
  scalar_bound q := F.scalar_bound (root q)
  prefixLength := length F
  selector q _ := IntegralCriticalHistoryTask.get F.toParameters .sourceIndex q
  coordinate _ := 0
  modulus := IntegralCriticalHistoryTask.modulus F.toParameters
  modulus_ne_zero := IntegralCriticalHistoryTask.modulus_ne_zero F.toParameters
  row q := ⟨row F q, by
    rw [past_length, min_eq_left (length_le_full F q)]
    exact row_lt F q⟩
  col q := ⟨col F q, by
    rw [past_length, min_eq_left (length_le_full F q)]
    exact col_lt F q⟩

theorem heightControls (F : Scripts) (a : Access F) : IntegralCriticalScriptHeightBits.Controls (heightQueries F) where
  ambient := a.ambient.comp RankedHistoryTask.root_FP
  prefixLength := BinaryFn.ofUnary (length_unary F a)
  selector := (IntegralCriticalHistoryTask.get_binary _ a.toAccess .sourceIndex).comp pairFst_mem_FP
  coordinate := BinaryFn.const 0
  modulus := IntegralCriticalHistoryTask.modulus_binary _ a.toAccess
  row := row_binary F a
  col := col_binary F a

noncomputable def rawValue (F : Scripts) : List Bool → List Bool := (IntegralCriticalScriptHeightBits.source (heightQueries F)).rawValue

noncomputable def creatingAt (F : Scripts) (r : List Bool) (j : ℕ) (h : j < (F.rules r).length) : IntegralHistoryCriticalBits.Family :=
  birthFamily (F.rules r) (F.length_le r) (F.scalar_bound r)
    ⟨(F.rules r).length - 1 - j, by omega⟩

noncomputable def creatingFamily (F : Scripts) (q : List Bool)
    (h : IntegralCriticalHistoryTask.birth F.toParameters q < (F.rules (root q)).length) : IntegralHistoryCriticalBits.Family :=
  creatingAt F (root q) (IntegralCriticalHistoryTask.birth F.toParameters q) h

noncomputable def companionValue (F : Scripts) (q : List Bool) : List Bool :=
  if h : IntegralCriticalHistoryTask.birth F.toParameters q < (F.rules (root q)).length then
    IntegralCriticalCreatingBits.value (creatingFamily F q h)
      (IntegralCriticalHistoryTask.get F.toParameters .row q) (IntegralCriticalHistoryTask.get F.toParameters .col q)
      (IntegralCriticalHistoryTask.modulus F.toParameters q) else []

end LeanCanny.Algebra.IntegralCriticalFlatHeightBits
