/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalFlatClearedHeightSource

/-! # Native internal raw-height packets for common clearing

Retargeting replaces only the retained raw index. It is an internal local
computation, not a recursive call. The recursive writer continues directly
to the earlier creating companion and keeps the original root and modulus.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatClearedHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalScript IntegralCriticalFlatHeightBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def rawReader (F : Scripts) (p : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairSnd p) = IntegralCriticalHistoryTask.Field.sourceIndex.code then
    BinaryNatCode.encode (selected F (pairFst p))
  else RankedHistoryFields.read (IntegralCriticalHistoryTask.numericCap F.toParameters) 16 p

theorem rawReader_FP (F : Scripts) (a : Access F) (n : IntegralCriticalScriptFP.Access (metadata F)) : rawReader F ∈ FP := by
  have HS : BinaryFn (fun p => selected F (pairFst p)) := (selected_binary F a n).comp pairFst_mem_FP
  exact ((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const IntegralCriticalHistoryTask.Field.sourceIndex.code)).ite_mem_FP
    HS.bits_mem_FP (RankedHistoryFields.read_FP _ _ (IntegralCriticalHistoryTask.numericCap_binary _ a.toAccess))

def rawTask (F : Scripts) : List Bool → List Bool :=
  IntegralCriticalHistoryTask.child F.toParameters id (IntegralCriticalHistoryTask.birth F.toParameters) .clearedHeight (rawReader F)

theorem rawTask_FP (F : Scripts) (a : Access F) (n : IntegralCriticalScriptFP.Access (metadata F)) : rawTask F ∈ FP :=
  IntegralCriticalHistoryTask.child_FP _ a.toAccess id id_mem_FP _
    (BinaryFn.ofUnary (RankedHistoryTask.birth_unary _ (IntegralCriticalHistoryTask.birthCap_unary _ a.toAccess)))
    .clearedHeight _ (rawReader_FP F a n)

theorem rawTask_root (F : Scripts) (q : List Bool) : root (rawTask F q) = root q :=
  IntegralCriticalHistoryTask.child_root _ _ _ _ _ _

theorem rawTask_birth (F : Scripts) (q : List Bool) :
    IntegralCriticalHistoryTask.birth F.toParameters (rawTask F q) = IntegralCriticalHistoryTask.birth F.toParameters q := by
  unfold rawTask IntegralCriticalHistoryTask.child
  rw [RankedHistoryFields.flatten_eq_pack]
  exact RankedHistoryTask.birth_pack _ _ _ _ _ (min_le_right _ _)

theorem rawTask_get (F : Scripts) (q : List Bool) (f : IntegralCriticalHistoryTask.Field) :
    IntegralCriticalHistoryTask.get F.toParameters f (rawTask F q) =
      if f = .sourceIndex then min (selected F q) (IntegralCriticalHistoryTask.numericCap F.toParameters (root q))
      else IntegralCriticalHistoryTask.get F.toParameters f q := by
  unfold rawTask
  rw [IntegralCriticalHistoryTask.child_get]
  have HI : Nat.fromBitsLE (BinaryNatCode.encode f.code) = f.code := Nat.fromBitsLE_bits _
  simp only [rawReader, pairSnd_pair, pairFst_pair, HI, id_eq]
  have HE : f.code = IntegralCriticalHistoryTask.Field.sourceIndex.code ↔ f = .sourceIndex := by
    cases f <;> decide
  by_cases hs : f = .sourceIndex
  · subst f
    simp only [ite_true, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    rfl
  · have hc : f.code ≠ IntegralCriticalHistoryTask.Field.sourceIndex.code := fun h => hs (HE.mp h)
    simp only [ite_eq_right hc, ite_eq_right hs]
    rw [RankedHistoryFields.read_packet, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact min_eq_left (IntegralCriticalHistoryTask.get_le _ _ _)

theorem rawTask_modulus (F : Scripts) (q : List Bool) :
    IntegralCriticalHistoryTask.modulus F.toParameters (rawTask F q) = IntegralCriticalHistoryTask.modulus F.toParameters q := by
  unfold IntegralCriticalHistoryTask.modulus
  rw [rawTask_get]
  rfl

theorem rawTask_length (F : Scripts) (q : List Bool) : length F (rawTask F q) = length F q := by
  unfold length
  rw [rawTask_root, rawTask_birth]

theorem rawTask_dimension (F : Scripts) (q : List Bool) : dimension F (rawTask F q) = dimension F q := by
  unfold dimension
  rw [rawTask_length, rawTask_root]

theorem rawTask_row (F : Scripts) (q : List Bool) : row F (rawTask F q) = row F q := by
  unfold row
  rw [rawTask_get, rawTask_dimension]
  rfl

theorem rawTask_col (F : Scripts) (q : List Bool) : col F (rawTask F q) = col F q := by
  unfold col
  rw [rawTask_get, rawTask_dimension]
  rfl

theorem rawTask_index (F : Scripts) (q : List Bool) :
    IntegralCriticalFlatHeightBits.index F (rawTask F q) = min (selected F q) (length F q) := by
  unfold IntegralCriticalFlatHeightBits.index
  rw [rawTask_get, rawTask_length]
  change min (min (selected F q) _) _ = _
  have HC : length F q ≤ IntegralCriticalHistoryTask.numericCap F.toParameters (root q) :=
    (length_le_cap F q).trans (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).1
  rw [min_assoc, min_eq_right HC]

theorem rawTask_valid (F : Scripts) (q : List Bool) :
    valid F (rawTask F q) ↔ selected F q < length F q := by
  unfold valid
  rw [rawTask_get, rawTask_length]
  change min (selected F q) (IntegralCriticalHistoryTask.numericCap F.toParameters (root q)) < length F q ↔ _
  have HC : length F q ≤ IntegralCriticalHistoryTask.numericCap F.toParameters (root q) :=
    (length_le_cap F q).trans (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).1
  omega

def earlierChild (F : Scripts) (q : List Bool) : List Bool := child F (rawTask F q)

theorem earlierChild_FP (F : Scripts) (a : Access F) (n : IntegralCriticalScriptFP.Access (metadata F)) : earlierChild F ∈ FP :=
  mem_FP_comp (rawTask_FP F a n) (child_FP F a)

theorem earlierChild_root (F : Scripts) (q : List Bool) : root (earlierChild F q) = root q :=
  (child_root _ _).trans (rawTask_root _ _)

theorem earlierChild_birth_lt (F : Scripts) (q : List Bool) (h : valid F (rawTask F q)) :
    IntegralCriticalHistoryTask.birth F.toParameters (earlierChild F q) < IntegralCriticalHistoryTask.birth F.toParameters q := by
  exact ((child_birth F (rawTask F q)).trans_lt (childBirth_lt F (rawTask F q) h)).trans_eq (rawTask_birth F q)

theorem earlierChild_rank (F : Scripts) (q : List Bool) (h : valid F (rawTask F q)) :
    IntegralCriticalHistoryTask.rank F.toParameters (earlierChild F q) < IntegralCriticalHistoryTask.rank F.toParameters q := by
  unfold earlierChild IntegralCriticalFlatHeightBits.child IntegralCriticalHistoryTask.child
  rw [RankedHistoryFields.flatten_eq_pack]
  have HR : RankedHistoryTask.root (id (rawTask F q)) = RankedHistoryTask.root q := rawTask_root F q
  rw [HR]
  apply RankedHistoryTask.lower_birth
  · exact (childBirth_lt F (rawTask F q) h).trans_eq (rawTask_birth F q)
  · exact IntegralCriticalHistoryTask.Phase.code_lt _

theorem earlierChild_length (F : Scripts) (q : List Bool) :
    (earlierChild F q).length ≤ IntegralCriticalHistoryTask.wordBudget F.toParameters q := by
  exact (child_length F (rawTask F q)).trans_eq
    (IntegralCriticalHistoryTask.wordBudget_eq _ (rawTask_root F q))

end LeanCanny.Algebra.IntegralCriticalFlatClearedHeightBits
