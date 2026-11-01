/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalScriptOrigin
public import LeanCanny.Algebra.IntegralScalarGeneratorController

/-! # Actual creating-generator sources for critical scripts

A selected command supplies its exact older algebra, coefficient polynomial,
and integer leading coefficient. The scalar companion family therefore
reads the actual generator at that birth. Its leading residue is obtained
from the metadata-only denominator pass for the interpreted script.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalScriptGeneratorBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralCriticalScript
open scoped Classical
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
  selected : ∀ c, Fin (rules c).length
  modulus : List Bool → ℕ
  modulus_ne_zero : ∀ c, modulus c ≠ 0
  row : ∀ c, Fin (count ((older (rules c) (selected c)).length + 1) (width c))
  col : ∀ c, Fin (count ((older (rules c) (selected c)).length + 1) (width c))

noncomputable def oldState (F : Queries) (c : List Bool) :=
  birthState (F.rules c) (F.length_le c) (F.scalar_bound c) (F.selected c)

noncomputable def birthSource (F : Queries) (c : List Bool) :=
  birthFamily (F.rules c) (F.length_le c) (F.scalar_bound c) (F.selected c)

noncomputable def generatorFamily (F : Queries) : PaddedIntegralGeneratorFinBits.Family where
  arity c := (older (F.rules c) (F.selected c)).length
  width := F.width
  carrier c := (oldState F c).scalarPrefix.carrier
  ring c := (oldState F c).scalarPrefix.ring
  nontrivial c := by
    let := (oldState F c).scalarPrefix.ring
    exact nontrivial_of_ne _ _ ((oldState F c).scalarPrefix.basis.finBasis.ne_zero
      ⟨0, by change 0 < (2 ^ F.width c) ^ (older (F.rules c) (F.selected c)).length; exact pow_pos (Nat.two_pow_pos _) _⟩)
  basis c := (oldState F c).scalarPrefix.basis
  polynomial c := (IntegralHistoryCriticalBits.source (birthSource F c)).annihilator []
  degree c := IntegralScalarRootHistoryBounds.degree (birthSource F c) []
  modulus := F.modulus
  modulus_ne_zero := F.modulus_ne_zero
  row := F.row
  col := F.col

noncomputable def leading (F : Queries) (c : List Bool) : ℤ :=
  IntegralClearedCriticalLeadingBits.integer (IntegralHistoryCriticalBits.source (birthSource F c)) []

theorem leading_eq (F : Queries) (c : List Bool) :
    letI := (generatorFamily F).ring c
    ((generatorFamily F).polynomial c).coeff ((generatorFamily F).degree c) = (leading F c : (generatorFamily F).carrier c) :=
  IntegralClearedCriticalLeadingBits.coefficient _ []

theorem value (F : Queries) (c : List Bool) :
    (generatorFamily F).value c = residueBits
      ((Algebra.leftMulMatrix (birthStep (F.rules c) (F.length_le c) (F.scalar_bound c) (F.selected c)).scalarPrefix.basis.finBasis
        (AdjoinRoot.root _) (F.row c) (F.col c) : ℤ) : ZMod (F.modulus c)) := rfl

theorem leading_FP (F : Queries)
    (a : IntegralDenominatorPass.Access (IntegralCriticalDenominatorScript.program
      (fun c => instructions (F.rules c)) F.modulus F.modulus_ne_zero))
    (hi : BinaryFn (fun c => (F.selected c).val)) :
    (fun c => residueBits (leading F c : ZMod (F.modulus c))) ∈ FP := by
  have H := bank_denominator_reader_FP F.cap F.width F.ambient F.sourceWidth F.degreeBound F.height F.rules
    F.length_le F.scalar_bound F.modulus F.modulus_ne_zero a (fun c => (F.selected c).val) hi
  refine mem_FP_of_eq H (fun c => ?_)
  have HG := (origin (F.rules c) (F.scalar_bound c) (F.length_le c) (F.selected c)).denominator_eq
  have HV : ((List.ofFn (run (F.rules c) (F.length_le c) (F.scalar_bound c)).bank.denominator)[(F.selected c).val]?).getD 0 =
      (run (F.rules c) (F.length_le c) (F.scalar_bound c)).bank.denominator (F.selected c) := by simp
  rw [HV, HG]
  rfl

structure Controls (F : Queries) : Prop where
  count : UnaryFn (fun c => (F.rules c).length)
  selected : BinaryFn (fun c => (F.selected c).val)
  width : UnaryFn F.width
  ambient : UnaryFn F.ambient
  offset : BinaryFn (fun c => (chosen (F.rules c) (F.selected c)).offset.val)
  degree : BinaryFn (fun c => (chosen (F.rules c) (F.selected c)).degree)
  modulus : BinaryFn F.modulus
  row : BinaryFn (fun c => (F.row c).val)
  col : BinaryFn (fun c => (F.col c).val)

theorem selected_unary (F : Queries) (h : Controls F) : UnaryFn (fun c => (F.selected c).val) :=
  (UnaryFn.fromBitsLE_of_le h.selected.bits_mem_FP h.count
    (fun c => by rw [BinaryNatCode.encode, Nat.fromBitsLE_bits]; exact (F.selected c).isLt.le)).of_eq
    (fun _ => Nat.fromBitsLE_bits _)

theorem arity_unary (F : Queries) (h : Controls F) : UnaryFn (generatorFamily F).arity :=
  ((h.count.sub (UnaryFn.const 1)).sub (selected_unary F h)).of_eq
    (fun c => (older_length (F.rules c) (F.selected c)).symm)

theorem offset_unary (F : Queries) (h : Controls F) : UnaryFn (fun c => (chosen (F.rules c) (F.selected c)).offset.val) :=
  (UnaryFn.fromBitsLE_of_le h.offset.bits_mem_FP (h.ambient.add (UnaryFn.const 1))
    (fun c => by rw [BinaryNatCode.encode, Nat.fromBitsLE_bits]; exact (chosen (F.rules c) (F.selected c)).offset.isLt.le)).of_eq
    (fun _ => Nat.fromBitsLE_bits _)

theorem degree_binary (F : Queries) (h : Controls F) : BinaryFn (generatorFamily F).degree :=
  PurePowerReductionBounds.dimension_binary ((h.ambient.sub (offset_unary F h)).add (UnaryFn.const 1)) h.degree

noncomputable def access (F : Queries) (h : Controls F) (entry : List Bool → List Bool)
    (he : ∀ c k (r t : Fin (count ((older (F.rules c) (F.selected c)).length) (F.width c))),
      entry (pair c (pair (BinaryNatCode.encode k) (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) =
        residueBits ((generatorFamily F).coefficient c k r t)) : PaddedIntegralGeneratorFinBits.Access (generatorFamily F) where
  arity := arity_unary F h
  width := h.width
  degree := degree_binary F h
  modulus := h.modulus
  row := h.row
  col := h.col
  entry := entry
  entry_eq := he

noncomputable def scalarFamily (F : Queries) : IntegralScalarGeneratorBits.Family :=
  IntegralScalarGeneratorBits.finFamily (generatorFamily F) (leading F) (leading_eq F)

noncomputable def program (F : Queries) (task : List Bool → List Bool) : SingleCall.Program :=
  IntegralScalarGeneratorBits.program (scalarFamily F) task

theorem program_controls (F : Queries) (h : Controls F)
    (a : IntegralDenominatorPass.Access (IntegralCriticalDenominatorScript.program
      (fun c => instructions (F.rules c)) F.modulus F.modulus_ne_zero))
    (entry : List Bool → List Bool)
    (he : ∀ c k (r t : Fin (count ((older (F.rules c) (F.selected c)).length) (F.width c))),
      entry (pair c (pair (BinaryNatCode.encode k) (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) =
        residueBits ((generatorFamily F).coefficient c k r t))
    (task : List Bool → List Bool) (ht : task ∈ FP) : (program F task).Controls :=
  IntegralScalarGeneratorBits.program_controls _
    (IntegralScalarGeneratorBits.finAccess (generatorFamily F) (access F h entry he) (leading F) (leading_eq F)
      (fun c => residueBits (leading F c : ZMod (F.modulus c))) (fun _ => rfl))
    (leading_FP F a h.selected) task ht

theorem program_value (F : Queries) (task answer : List Bool → List Bool)
    (ha : ∀ c, IntegralScalarGeneratorBits.request (scalarFamily F) c →
      answer (task (IntegralScalarGeneratorBits.coefficientQuery (scalarFamily F) c)) =
        residueBits ((scalarFamily F).coefficient c (IntegralScalarGeneratorBits.index (scalarFamily F) c)
          ((scalarFamily F).oldRow c) ((scalarFamily F).oldCol c))) (c : List Bool) :
    (program F task).value answer c = (generatorFamily F).value c :=
  IntegralScalarGeneratorBits.fin_program_value (generatorFamily F) (leading F) (leading_eq F) task answer ha c


end LeanCanny.Algebra.IntegralCriticalScriptGeneratorBits
