/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedOldBankCofactor
/-! # Fresh native earlier-companion queries for mixed old-height entries -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedOldHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedOldBankCofactorBits (Routing RoutingAccess)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def index (P : Parameters) (q : List Bool) := min (get P .sourceIndex q) (birth P q)
def radix (P : Parameters) (q : List Bool) := FixedWidthPolynomial.count (index P q) (P.width (RankedHistoryTask.root q))
def dimension (P : Parameters) (q : List Bool) := FixedWidthPolynomial.count (birth P q) (P.width (RankedHistoryTask.root q))
def producerBirth (P : Parameters) (q : List Bool) := birth P q - 1 - index P q

def valid (P : Parameters) (q : List Bool) : Prop :=
  get P .sourceIndex q < birth P q ∧ get P .row q < dimension P q ∧ get P .col q < dimension P q

def request (P : Parameters) (q : List Bool) : Prop :=
  valid P q ∧ get P .row q % radix P q = get P .col q % radix P q

theorem birth_unary (P : Parameters) (a : Access P) : UnaryFn (birth P) :=
  RankedHistoryTask.birth_unary _ (birthCap_unary P a)

theorem index_unary (P : Parameters) (a : Access P) : UnaryFn (index P) :=
  (UnaryFn.fromBitsLE_min (get_binary P a .sourceIndex).bits_mem_FP (birth_unary P a)).of_eq
    (fun _ => by rw [BinaryNatCode.encode, Nat.fromBitsLE_bits]; rfl)

theorem radix_binary (P : Parameters) (a : Access P) : BinaryFn (radix P) :=
  ((BinaryFn.const 2).powUnary (a.width.comp RankedHistoryTask.root_FP)).powUnary (index_unary P a)

theorem dimension_binary (P : Parameters) (a : Access P) : BinaryFn (dimension P) :=
  ((BinaryFn.const 2).powUnary (a.width.comp RankedHistoryTask.root_FP)).powUnary (birth_unary P a)

theorem producerBirth_binary (P : Parameters) (a : Access P) : BinaryFn (producerBirth P) :=
  ((BinaryFn.ofUnary (birth_unary P a)).sub (BinaryFn.const 1)).sub (BinaryFn.ofUnary (index_unary P a))

theorem request_FP (P : Parameters) (a : Access P) : FPPred (request P) :=
  (((get_binary P a .sourceIndex).lt (BinaryFn.ofUnary (birth_unary P a))).and
    (((get_binary P a .row).lt (dimension_binary P a)).and ((get_binary P a .col).lt (dimension_binary P a)))).and
    (((get_binary P a .row).mod (radix_binary P a)).eq ((get_binary P a .col).mod (radix_binary P a)))

def packet (P : Parameters) (q : List Bool) :=
  pair q (pair (BinaryNatCode.encode (producerBirth P q)) (BinaryNatCode.encode (index P q)))

theorem packet_FP (P : Parameters) (a : Access P) : packet P ∈ FP :=
  mem_FP_pair id_mem_FP (mem_FP_pair (producerBirth_binary P a).bits_mem_FP (BinaryFn.ofUnary (index_unary P a)).bits_mem_FP)

def reader (P : Parameters) (R : Routing) (z : List Bool) : List Bool :=
  let q := pairFst z
  let k := Nat.fromBitsLE (pairSnd z)
  if k = Field.modulus.code then BinaryNatCode.encode (get P .modulus q) else
  if k = Field.row.code then BinaryNatCode.encode (get P .row q / radix P q) else
  if k = Field.col.code then BinaryNatCode.encode (get P .col q / radix P q) else
  if k = Field.slot13.code then BinaryNatCode.encode (R.coordinate (packet P q)) else
  if k = Field.slot14.code then BinaryNatCode.encode 6 else
  if k = Field.slot15.code then BinaryNatCode.encode (R.context (packet P q)) else []

theorem reader_FP (P : Parameters) (a : Access P) (R : Routing) (hr : RoutingAccess R) : reader P R ∈ FP := by
  have HI := BinaryFn.fromBits pairSnd_mem_FP
  have HM : BinaryFn (fun z => get P .modulus (pairFst z)) := (get_binary P a .modulus).comp pairFst_mem_FP
  have HR : BinaryFn (fun z => get P .row (pairFst z) / radix P (pairFst z)) := ((get_binary P a .row).div (radix_binary P a)).comp pairFst_mem_FP
  have HT : BinaryFn (fun z => get P .col (pairFst z) / radix P (pairFst z)) := ((get_binary P a .col).div (radix_binary P a)).comp pairFst_mem_FP
  have HJ : BinaryFn (fun z => R.coordinate (packet P (pairFst z))) := (hr.coordinate.comp (packet_FP P a)).comp pairFst_mem_FP
  have HX : BinaryFn (fun z => R.context (packet P (pairFst z))) := (hr.context.comp (packet_FP P a)).comp pairFst_mem_FP
  exact (HI.eq (BinaryFn.const Field.modulus.code)).ite_mem_FP HM.bits_mem_FP
    ((HI.eq (BinaryFn.const Field.row.code)).ite_mem_FP HR.bits_mem_FP
      ((HI.eq (BinaryFn.const Field.col.code)).ite_mem_FP HT.bits_mem_FP
        ((HI.eq (BinaryFn.const Field.slot13.code)).ite_mem_FP HJ.bits_mem_FP
          ((HI.eq (BinaryFn.const Field.slot14.code)).ite_mem_FP (constFn_mem_FP (BinaryNatCode.encode 6))
            ((HI.eq (BinaryFn.const Field.slot15.code)).ite_mem_FP HX.bits_mem_FP (constFn_mem_FP []))))))

def writer (P : Parameters) (R : Routing) := IntegralCriticalHistoryTask.child P id (producerBirth P) .companion (reader P R)

theorem writer_FP (P : Parameters) (a : Access P) (R : Routing) (hr : RoutingAccess R) : writer P R ∈ FP :=
  child_FP P a id id_mem_FP _ (producerBirth_binary P a) .companion _ (reader_FP P a R hr)

theorem producerBirth_bound (P : Parameters) (q : List Bool) : producerBirth P q ≤ birthCap P (RankedHistoryTask.root q) :=
  (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans (min_le_right _ _))

theorem producerBirth_lt (P : Parameters) (q : List Bool) (hr : request P q) : producerBirth P q < birth P q := by
  have HI := hr.1.1
  unfold producerBirth index
  rw [min_eq_left HI.le]
  omega

theorem writer_root (P : Parameters) (R : Routing) (q : List Bool) :
    RankedHistoryTask.root (writer P R q) = RankedHistoryTask.root q := child_root P id _ .companion _ q

theorem writer_birth (P : Parameters) (R : Routing) (q : List Bool) : birth P (writer P R q) = producerBirth P q := by
  unfold writer child
  rw [RankedHistoryFields.flatten_eq_pack]
  exact RankedHistoryTask.birth_pack _ _ _ _ _ (producerBirth_bound P q)

theorem writer_phase (P : Parameters) (R : Routing) (q : List Bool) : phase (writer P R q) = 26 :=
  IntegralCriticalFlatMatrixQuery.child_phase P id _ .companion _ q

theorem writer_frame (P : Parameters) (R : Routing) (q : List Bool) (hr : request P q) :
    IntegralMixedRoutineTaskBits.Frame P q (writer P R q) :=
  ⟨writer_root P R q, child_length P id _ .companion _ q (producerBirth_bound P q),
    IntegralMixedRoutineTaskBits.lower_birth P q _ ((writer_birth P R q).trans_lt (producerBirth_lt P q hr))⟩
end LeanCanny.Algebra.IntegralMixedOldHeightBits
