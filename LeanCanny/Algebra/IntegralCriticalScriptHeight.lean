/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CommonHeightResidueFP
public import LeanCanny.Algebra.IntegralDenominatorRequeryFP
public import LeanCanny.Algebra.IntegralCriticalScript

/-! # Actual common-cleared retained heights in critical script prefixes

Coordinate scales come from the interpreted prefix bank. Their common
product and omitted-coordinate products are computed by native modular
passes. Only the selected raw bank numerator entry is recursive.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalScriptHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower UniformIntegralPrefix FixedWidthPolynomial
open IntegralCriticalScript
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

structure Queries where
  cap : List Bool → ℕ
  width : List Bool → ℕ
  ambient : List Bool → ℕ
  sourceWidth : List Bool → ℕ
  degreeBound : List Bool → ℕ
  height : List Bool → ℕ
  rules : ∀ c, List (Command (ambient c) (sourceWidth c) (degreeBound c) (height c))
  length_le : ∀ c, (rules c).length ≤ cap c + 1
  scalar_bound : ∀ c, PurePowerReductionBounds.dimension (ambient c + 1) (degreeBound c) ≤ 2 ^ width c
  prefixLength : List Bool → ℕ
  selector : List Bool → ℕ → ℕ
  coordinate : List Bool → ℕ
  modulus : List Bool → ℕ
  modulus_ne_zero : ∀ c, modulus c ≠ 0
  row : ∀ c, Fin (count (past (rules c) (prefixLength c)).length (width c))
  col : ∀ c, Fin (count (past (rules c) (prefixLength c)).length (width c))

noncomputable def state (F : Queries) (c : List Bool) :=
  stateAt (F.rules c) (F.length_le c) (F.scalar_bound c) (F.prefixLength c)

def select (F : Queries) (c : List Bool) (i : ℕ) : Option (Fin (past (F.rules c) (F.prefixLength c)).length) :=
  if h : F.selector c i < (past (F.rules c) (F.prefixLength c)).length then some ⟨F.selector c i, h⟩ else none

noncomputable def scales (F : Queries) (c : List Bool) (i : ℕ) : ℤ :=
  (state F c).bank.selectedDenominator (select F c i)

noncomputable def scalars (F : Queries) : CommonHeightBits.Scalars where
  count c := F.ambient c + 1
  modulus := F.modulus
  modulus_ne_zero := F.modulus_ne_zero
  scale := scales F
  selected := F.coordinate

structure Controls (F : Queries) : Prop where
  ambient : UnaryFn F.ambient
  prefixLength : BinaryFn F.prefixLength
  selector : BinaryFn (fun p => F.selector (pairFst p) (Nat.fromBitsLE (pairSnd p)))
  coordinate : BinaryFn F.coordinate
  modulus : BinaryFn F.modulus
  row : BinaryFn (fun c => (F.row c).val)
  col : BinaryFn (fun c => (F.col c).val)

abbrev DenominatorAccess (F : Queries) := IntegralDenominatorPass.Access
  (IntegralCriticalDenominatorScript.program (fun c => instructions (F.rules c)) F.modulus F.modulus_ne_zero)

theorem prefixLength_binary (F : Queries) (h : Controls F) (a : DenominatorAccess F) :
    BinaryFn (fun c => (past (F.rules c) (F.prefixLength c)).length) := by
  have HC : UnaryFn (fun c => (F.rules c).length) := a.count.of_eq (fun c => instructions_length (F.rules c))
  have HL := BinaryFn.ofUnary HC
  exact (BinaryFn.ite (h.prefixLength.le HL) h.prefixLength HL).of_eq (fun c => by
    rw [← min_def]
    exact (past_length (F.rules c) (F.prefixLength c)).symm)

theorem scales_FP (F : Queries) (h : Controls F) (a : DenominatorAccess F) :
    (fun p => residueBits (scales F (pairFst p) (Nat.fromBitsLE (pairSnd p)) : ZMod (F.modulus (pairFst p)))) ∈ FP := by
  have HA := a.requery _ pairFst pairFst_mem_FP
  have HR := bank_prefix_denominator_reader_FP
    (fun p => F.cap (pairFst p)) (fun p => F.width (pairFst p)) (fun p => F.ambient (pairFst p))
    (fun p => F.sourceWidth (pairFst p)) (fun p => F.degreeBound (pairFst p)) (fun p => F.height (pairFst p))
    (fun p => F.rules (pairFst p)) (fun p => F.length_le (pairFst p)) (fun p => F.scalar_bound (pairFst p))
    (fun p => F.modulus (pairFst p)) (fun p => F.modulus_ne_zero (pairFst p)) HA
    (fun p => F.prefixLength (pairFst p)) (h.prefixLength.comp pairFst_mem_FP)
    (fun p => F.selector (pairFst p) (Nat.fromBitsLE (pairSnd p))) h.selector
  have HP : BinaryFn (fun p => (past (F.rules (pairFst p)) (F.prefixLength (pairFst p))).length) :=
    (prefixLength_binary F h a).comp pairFst_mem_FP
  have HM : BinaryFn (fun p => F.modulus (pairFst p)) := h.modulus.comp pairFst_mem_FP
  have HO : (fun p => ArithmeticBits.one (BinaryNatCode.encode (F.modulus (pairFst p)))) ∈ FP :=
    mem_FP_comp (g := ArithmeticBits.one) HM.bits_mem_FP ArithmeticBits.one_mem_FP
  refine mem_FP_of_eq ((h.selector.lt HP).ite_mem_FP HR HO) (fun p => ?_)
  unfold scales select
  split_ifs with hi
  · simp only [HeightBank.selectedDenominator]
    simp only [state, List.getElem?_ofFn, hi, dite_true, Option.getD_some]
  · simp only [HeightBank.selectedDenominator]
    simpa only [Int.cast_one] using ArithmeticBits.one_residueBits (F.modulus (pairFst p))

noncomputable def access (F : Queries) (h : Controls F) (a : DenominatorAccess F) : CommonHeightBits.Access (scalars F) where
  count := h.ambient.add (UnaryFn.const 1)
  modulus := h.modulus
  selected := h.coordinate
  scalar p := residueBits (scales F (pairFst p) (Nat.fromBitsLE (pairSnd p)) : ZMod (F.modulus (pairFst p)))
  scalar_FP := scales_FP F h a
  scalar_eq c i _ := by
    rw [pairFst_pair, pairSnd_pair]
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    rfl

noncomputable def rawNumerator (F : Queries) (c : List Bool) : (state F c).scalarPrefix.carrier :=
  if F.coordinate c < F.ambient c + 1 then (state F c).bank.selectedNumerator (select F c (F.coordinate c)) else 0

noncomputable def source (F : Queries) : CommonHeightBits.Source where
  toScalars := scalars F
  rank c := count (past (F.rules c) (F.prefixLength c)).length (F.width c)
  carrier c := (state F c).scalarPrefix.carrier
  ring c := (state F c).scalarPrefix.ring
  basis c := (state F c).scalarPrefix.basis.finBasis
  numerator := rawNumerator F
  row := F.row
  col := F.col

noncomputable def cleared (F : Queries) (c : List Bool) : (state F c).scalarPrefix.carrier :=
  CoordinateFrozenCriticalElimination.numerators (fun i : Fin (F.ambient c + 1) => scales F c i.val)
    (fun i => (state F c).bank.selectedNumerator (select F c i.val)) (F.coordinate c)

theorem cleared_eq (F : Queries) (c : List Bool) :
    cleared F c = rawNumerator F c * ((scalars F).cofactor c : (state F c).scalarPrefix.carrier) := by
  unfold cleared CoordinateFrozenCriticalElimination.numerators rawNumerator
  split_ifs with hi
  · unfold CommonIntegerDenominator.numerator
    congr 1
    exact congrArg (fun z : ℤ => (z : (state F c).scalarPrefix.carrier))
      (CommonHeightBits.cofactor_eq_erase (F.ambient c + 1) (scales F c) ⟨F.coordinate c, hi⟩).symm
  · rw [zero_mul]

noncomputable def present (F : Queries) (c : List Bool) : Bool :=
  decide (F.coordinate c < F.ambient c + 1 ∧
    F.selector c (F.coordinate c) < (past (F.rules c) (F.prefixLength c)).length)

theorem rawValue_eq (F : Queries) (c : List Bool) (hc : F.coordinate c < F.ambient c + 1) :
    (source F).rawValue c = residueBits
      ((Algebra.leftMulMatrix (state F c).scalarPrefix.basis.finBasis
        ((state F c).bank.selectedNumerator (select F c (F.coordinate c)))
        (F.row c) (F.col c) : ℤ) : ZMod (F.modulus c)) := by
  unfold CommonHeightBits.Source.rawValue
  dsimp only [source, rawNumerator]
  rw [ite_eq_left hc]

theorem numerator_zero (F : Queries) (c : List Bool) (h : present F c = false) : rawNumerator F c = 0 := by
  change (if F.coordinate c < F.ambient c + 1 then _ else 0) = 0
  by_cases hc : F.coordinate c < F.ambient c + 1
  · rw [ite_eq_left hc]
    have HS : ¬ F.selector c (F.coordinate c) < (past (F.rules c) (F.prefixLength c)).length := by
      intro hs
      have : present F c = true := by simp only [present, hc, hs, and_self, decide_true]
      rw [this] at h
      contradiction
    simp only [select, dite_eq_right HS, HeightBank.selectedNumerator]
  · exact ite_eq_right hc

noncomputable def program (F : Queries) (task : List Bool → List Bool) : SingleCall.Program :=
  CommonHeightBits.program (source F) (present F) task

theorem present_FP (F : Queries) (h : Controls F) (a : DenominatorAccess F) :
    (fun c => [present F c]) ∈ FP := by
  have HQ := mem_FP_pair id_mem_FP h.coordinate.bits_mem_FP
  have HS : BinaryFn (fun c => F.selector c (F.coordinate c)) :=
    BinaryFn.of_eq (h.selector.comp HQ) (fun c => by
      simp only [Function.comp_apply, id_eq, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits])
  exact ((h.coordinate.lt (BinaryFn.ofUnary (h.ambient.add (UnaryFn.const 1)))).and
    (HS.lt (prefixLength_binary F h a))).flag_mem_FP

theorem program_controls (F : Queries) (h : Controls F) (a : DenominatorAccess F)
    (task : List Bool → List Bool) (ht : task ∈ FP) : (program F task).Controls :=
  CommonHeightBits.controls (source F) (access F h a) (present F) (present_FP F h a) task ht

theorem denominator_FP (F : Queries) (h : Controls F) (a : DenominatorAccess F) :
    (fun c => residueBits (CoordinateFrozenCriticalElimination.denominator
      (fun i : Fin (F.ambient c + 1) => scales F c i.val) : ZMod (F.modulus c))) ∈ FP := by
  refine mem_FP_of_eq (CommonHeightBits.denominator_FP (scalars F) (access F h a)) (fun c => ?_)
  change residueBits (((∏ i ∈ Finset.range (F.ambient c + 1), scales F c i) : ℤ) : ZMod (F.modulus c)) = _
  rw [Finset.prod_range]
  rfl

theorem cofactor_FP (F : Queries) (h : Controls F) (a : DenominatorAccess F) :
    (fun c => residueBits ((scalars F).cofactor c : ZMod (F.modulus c))) ∈ FP :=
  CommonHeightBits.cofactor_FP _ (access F h a)

def rawQuery (F : Queries) (c : List Bool) : List Bool :=
  pair c (pair (BinaryNatCode.encode (F.selector c (F.coordinate c)))
    (pair (BinaryNatCode.encode (F.row c).val) (BinaryNatCode.encode (F.col c).val)))

theorem rawQuery_FP (F : Queries) (h : Controls F) : rawQuery F ∈ FP := by
  have HQ := mem_FP_pair id_mem_FP h.coordinate.bits_mem_FP
  have HS : BinaryFn (fun c => F.selector c (F.coordinate c)) :=
    BinaryFn.of_eq (h.selector.comp HQ) (fun c => by
      simp only [Function.comp_apply, id_eq, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits])
  exact mem_FP_pair id_mem_FP (mem_FP_pair HS.bits_mem_FP (mem_FP_pair h.row.bits_mem_FP h.col.bits_mem_FP))

theorem program_value (F : Queries) (task answer : List Bool → List Bool)
    (he : ∀ c, present F c = true → answer (task c) = (source F).rawValue c) (c : List Bool) :
    (program F task).value answer c = residueBits
      ((Algebra.leftMulMatrix (state F c).scalarPrefix.basis.finBasis (cleared F c) (F.row c) (F.col c) : ℤ) : ZMod (F.modulus c)) := by
  rw [show program F task = CommonHeightBits.program (source F) (present F) task from rfl,
    CommonHeightBits.program_value _ _ _ _ he (numerator_zero F)]
  unfold CommonHeightBits.Source.value
  dsimp only [source]
  rw [← cleared_eq]

theorem requests_iff (F : Queries) (task answer : List Bool → List Bool)
    (budget : List Bool → ℕ) (c child : List Bool) :
    (program F task).controller.Requests answer budget c child ↔ present F c = true ∧ child = task c :=
  CommonHeightBits.requests_iff (source F) (present F) task answer budget c child

end LeanCanny.Algebra.IntegralCriticalScriptHeightBits
