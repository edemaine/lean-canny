/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.ControllerRequests
public import LeanCanny.Algebra.IntegralScalarGeneratorSpace
public import LeanCanny.Algebra.ModularScalarFP

/-! # A resumable one-coefficient reader for scalar companion roots

Shift and padding entries are local. A nontrivial last-column entry asks
for one original coefficient matrix entry, then multiplies by a power of
the integer leading residue. All local controls are FP when that scalar
residue is FP; no coefficient evaluator is assumed by the controller.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralScalarGeneratorBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def index (F : Family) (c : List Bool) : ℕ := (F.row c).val - (F.scalarDegree c - F.selectedDegree c)
def power (F : Family) (c : List Bool) : ℕ := F.selectedDegree c - 1 - index F c

def request (F : Family) (c : List Bool) : Prop :=
  ¬((F.col c).val + 1 < F.scalarDegree c) ∧
    F.selectedDegree c ≤ F.scalarDegree c ∧ F.scalarDegree c - F.selectedDegree c ≤ (F.row c).val

def immediate (F : Family) (c : List Bool) : List Bool :=
  residueBits (if (F.col c).val + 1 < F.scalarDegree c ∧ (F.row c).val = (F.col c).val + 1 ∧
    (F.oldRow c).val = (F.oldCol c).val then (1 : ZMod (F.modulus c)) else 0)

def finishValue (F : Family) (c : List Bool) (v : List Bool) : List Bool :=
  residueBits (-((Nat.fromBitsLE v : ZMod (F.modulus c)) * F.leading c ^ power F c))

def finish (F : Family) (z : List Bool) : List Bool := finishValue F (pairFst z) (pairSnd z)

theorem request_FP (F : Family) (a : Access F) : FPPred (request F) :=
  (((a.col.add (BinaryFn.const 1)).lt a.scalarDegree).not).and
    ((a.selectedDegree.le a.scalarDegree).and ((a.scalarDegree.sub a.selectedDegree).le a.row))

theorem immediate_FP (F : Family) (a : Access F) : immediate F ∈ FP := by
  have HP := ((a.col.add (BinaryFn.const 1)).lt a.scalarDegree).and
    ((a.row.eq (a.col.add (BinaryFn.const 1))).and (a.oldRow.eq a.oldCol))
  have HO := ModularScalarFP.natCast a.modulus (fun _ => 1) (BinaryFn.const 1)
  have HZ : (fun c => residueBits (0 : ZMod (F.modulus c))) ∈ FP :=
    mem_FP_of_eq (constFn_mem_FP []) (fun c => ArithmeticBits.zero_residueBits _)
  exact mem_FP_of_eq (HP.ite_mem_FP HO HZ) (fun c => by
    simp only [immediate]; split_ifs <;> simp only [Nat.cast_one])

attribute [local irreducible] ArithmeticBits.negate

theorem finish_FP (F : Family) (a : Access F) (hL : a.leading ∈ FP) : finish F ∈ FP := by
  have HM : BinaryFn (fun z => F.modulus (pairFst z)) := a.modulus.comp pairFst_mem_FP
  have HE : BinaryFn (fun z => power F (pairFst z)) :=
    ((a.selectedDegree.sub (BinaryFn.const 1)).sub (a.row.sub (a.scalarDegree.sub a.selectedDegree))).comp pairFst_mem_FP
  have HL : (fun z => residueBits (F.leading (pairFst z))) ∈ FP :=
    mem_FP_of_eq (mem_FP_comp pairFst_mem_FP hL) (fun z => a.leading_eq (pairFst z))
  have HP := ModularScalarFP.pow HM (fun z => F.modulus_ne_zero (pairFst z)) _ HE _ HL
  have HR := ModularScalarFP.natCast HM (fun z => Nat.fromBitsLE (pairSnd z)) (BinaryFn.fromBits pairSnd_mem_FP)
  have HX := ModularScalarFP.mul HM _ _ HR HP
  have H := mem_FP_comp (mem_FP_pair HM.bits_mem_FP HX) ArithmeticBits.negate_mem_FP
  refine mem_FP_of_eq H (fun z => ?_)
  let : NeZero (F.modulus (pairFst z)) := ⟨F.modulus_ne_zero _⟩
  exact ArithmeticBits.negate_residueBits _ _

def coefficientQuery (F : Family) (c : List Bool) : List Bool :=
  pair c (pair (BinaryNatCode.encode (index F c))
    (pair (BinaryNatCode.encode (F.oldRow c).val) (BinaryNatCode.encode (F.oldCol c).val)))

theorem coefficientQuery_FP (F : Family) (a : Access F) : coefficientQuery F ∈ FP :=
  mem_FP_pair id_mem_FP (mem_FP_pair (a.row.sub (a.scalarDegree.sub a.selectedDegree)).bits_mem_FP
    (mem_FP_pair a.oldRow.bits_mem_FP a.oldCol.bits_mem_FP))

noncomputable def program (F : Family) (task : List Bool → List Bool) : SingleCall.Program where
  request c := decide (request F c)
  query c := task (coefficientQuery F c)
  immediate := immediate F
  finish := finish F

theorem program_controls (F : Family) (a : Access F) (hL : a.leading ∈ FP)
    (task : List Bool → List Bool) (ht : task ∈ FP) : (program F task).Controls where
  request := (request_FP F a).flag_mem_FP
  query := mem_FP_comp (f := coefficientQuery F) (g := task) (coefficientQuery_FP F a) ht
  immediate := immediate_FP F a
  finish := finish_FP F a hL

theorem finishValue_residue (F : Family) (c : List Bool) (x : ZMod (F.modulus c)) :
    finishValue F c (residueBits x) = residueBits (-(x * F.leading c ^ power F c)) := by
  let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
  simp only [finishValue, residueBits, BinaryNatCode.encode, Nat.fromBitsLE_bits, ZMod.natCast_zmod_val]

theorem program_value (F : Family) (task answer : List Bool → List Bool)
    (ha : ∀ c, request F c → answer (task (coefficientQuery F c)) =
      residueBits (F.coefficient c (index F c) (F.oldRow c) (F.oldCol c))) (c : List Bool) :
    (program F task).value answer c = F.toFamily.value c := by
  have H := IntegralScalarNormalizationBits.scalar_entry (normalizationFamily F) c
  change (F.coefficient c (index F c) * F.coefficient c (F.selectedDegree c) ^ power F c)
    (F.oldRow c) (F.oldCol c) =
    F.coefficient c (index F c) (F.oldRow c) (F.oldCol c) * F.leading c ^ power F c at H
  by_cases hs : (F.col c).val + 1 < F.scalarDegree c
  · simp only [SingleCall.Program.value, program, request, hs, not_true_eq_false, false_and,
      decide_false, Bool.false_eq_true, ite_false, immediate, true_and,
      PaddedIntegralGeneratorBits.Family.value, ite_true, Fin.ext_iff]
    split_ifs <;> first | rfl | omega
  · by_cases hv : F.selectedDegree c ≤ F.scalarDegree c ∧
        F.scalarDegree c - F.selectedDegree c ≤ (F.row c).val
    · have hr : request F c := ⟨hs, hv⟩
      simp only [SingleCall.Program.value, program, show decide (request F c) = true from decide_eq_true hr,
        ite_true]
      rw [ha c hr]
      simp only [finish, pairFst_pair, pairSnd_pair, finishValue_residue,
        PaddedIntegralGeneratorBits.Family.value, hs, ite_false, hv]
      exact congrArg (fun x => residueBits (-x)) H.symm
    · simp only [SingleCall.Program.value, program, request, hs, not_false_eq_true, true_and, hv,
        decide_false, Bool.false_eq_true, ite_false, immediate, false_and,
        PaddedIntegralGeneratorBits.Family.value]

theorem program_requests_iff (F : Family) (task answer : List Bool → List Bool)
    (budget : List Bool → ℕ) (c child : List Bool) :
    (program F task).controller.Requests answer budget c child ↔
      request F c ∧ child = task (coefficientQuery F c) := by
  rw [SingleCall.Program.requests_iff]
  simp only [program, decide_eq_true_eq]

theorem fin_program_value (F : PaddedIntegralGeneratorFinBits.Family) (z : List Bool → ℤ)
    (hz : ∀ c, letI := F.ring c; (F.polynomial c).coeff (F.degree c) = (z c : F.carrier c))
    (task answer : List Bool → List Bool)
    (ha : ∀ c, request (finFamily F z hz) c → answer (task (coefficientQuery (finFamily F z hz) c)) =
      residueBits ((finFamily F z hz).coefficient c (index (finFamily F z hz) c)
        ((finFamily F z hz).oldRow c) ((finFamily F z hz).oldCol c))) (c : List Bool) :
    (program (finFamily F z hz) task).value answer c = F.value c :=
  (program_value (finFamily F z hz) task answer ha c).trans
    (congrFun (PaddedIntegralGeneratorFinBits.value_eq F) c)

end LeanCanny.Algebra.IntegralScalarGeneratorBits
