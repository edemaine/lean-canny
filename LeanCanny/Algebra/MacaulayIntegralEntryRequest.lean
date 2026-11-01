/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayFullBoxEntryCorrect
public import LeanCanny.Computation.SingleCallController
public import LeanCanny.Computation.ControllerRequests

/-! # Native full-box entries over an integral coefficient basis

The shift and padding guards use the existing binary Macaulay metadata.
An active source row requests one actual system coefficient. Padding is
the identity multiplication matrix, so its two integral basis indices
must agree; they need not be zero. Invalid rectangular labels give zero.
-/

@[expose] public section
namespace LeanCanny.Algebra.MacaulayIntegralEntryRequest
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open MacaulayFullBoxBits
open scoped Classical
attribute [local irreducible] ArithmeticBits.one

def valid (L : Layout) (p : List Bool) : Prop :=
  Nat.fromBitsLE (idx p) < Nat.fromBitsLE (rowCut L (ctx p)) ∧
    Nat.fromBitsLE (shift p) < Nat.fromBitsLE (columnsCode L (ctx p))

def request (L : Layout) (p : List Bool) : Prop := valid L p ∧ isSource L p ∧
  active L (rawSourceInput L p) ∧ admissible L (rawSourceInput L p)

instance (L : Layout) (p : List Bool) : Decidable (valid L p) := inferInstanceAs (Decidable (_ ∧ _))
instance (L : Layout) (p : List Bool) : Decidable (request L p) := inferInstanceAs (Decidable (_ ∧ _))

def query (L : Layout) (p : List Bool) : List Bool := sourceInput L (rawSourceInput L p)

def diagonal (p : List Bool) : Prop :=
  Nat.fromBitsLE (pairFst (uv p)) = Nat.fromBitsLE (pairSnd (uv p))
instance (p : List Bool) : Decidable (diagonal p) := inferInstanceAs (Decidable (_ = _))

def immediate (L : Layout) (modulus : List Bool → ℕ) (p : List Bool) : List Bool :=
  if valid L p ∧ ¬isSource L p ∧ isPadding L p ∧ diagonal p then
    ArithmeticBits.one (BinaryNatCode.encode (modulus (ctx p))) else []

def program (L : Layout) (modulus : List Bool → ℕ) : SingleCall.Program where
  request p := decide (request L p)
  query := query L
  immediate := immediate L modulus
  finish := pairSnd

theorem valid_FP (L : Layout) (h : L.Controls) : FPPred (valid L) :=
  (BinaryNat.lt_fppred idx_FP (mem_FP_comp ctx_FP (rowCut_FP h))).and
    (BinaryNat.lt_fppred shift_FP (mem_FP_comp ctx_FP (columnsCode_FP h)))

theorem request_FP (L : Layout) (h : L.Controls) : FPPred (request L) :=
  (valid_FP L h).and ((isSource_FP h).and
    (((active_FP h).comp (rawSourceInput_FP h)).and ((admissible_FP h).comp (rawSourceInput_FP h))))

theorem query_FP (L : Layout) (h : L.Controls) : query L ∈ FP :=
  mem_FP_comp (rawSourceInput_FP h) (sourceInput_FP h)

theorem diagonal_FP : FPPred diagonal :=
  BinaryNat.eq_fppred (mem_FP_comp uv_FP pairFst_mem_FP) (mem_FP_comp uv_FP pairSnd_mem_FP)

theorem immediate_FP (L : Layout) (h : L.Controls) (modulus : List Bool → ℕ) (hm : BinaryFn modulus) :
    immediate L modulus ∈ FP := by
  have HM : BinaryFn (fun p => modulus (ctx p)) := hm.comp ctx_FP
  exact ((valid_FP L h).and ((isSource_FP h).not.and ((isPadding_FP h).and diagonal_FP))).ite_mem_FP
    (mem_FP_comp HM.bits_mem_FP ArithmeticBits.one_mem_FP) (constFn_mem_FP [])

attribute [local irreducible] valid request query immediate

theorem controls (L : Layout) (h : L.Controls) (modulus : List Bool → ℕ) (hm : BinaryFn modulus) :
    (program L modulus).Controls :=
  ⟨(request_FP L h).flag_mem_FP, query_FP L h, immediate_FP L h modulus hm, pairSnd_mem_FP⟩

theorem requests_iff (L : Layout) (reply : List Bool → List Bool)
    (m : List Bool → ℕ) (budget : List Bool → ℕ) (p child : List Bool) :
    (program L m).controller.Requests reply budget p child ↔ request L p ∧ child = query L p := by
  rw [SingleCall.Program.requests_iff]
  simp only [program, decide_eq_true_eq]

theorem value (L : Layout) (modulus : List Bool → ℕ) (reply : List Bool → List Bool) (p : List Bool) :
    (program L modulus).value reply p =
      if valid L p then
        if isSource L p then shifted L reply (rawSourceInput L p)
        else if isPadding L p ∧ diagonal p then
          ArithmeticBits.one (BinaryNatCode.encode (modulus (ctx p))) else []
      else [] := by
  by_cases HV : valid L p <;> by_cases HS : isSource L p <;>
    simp only [SingleCall.Program.value, program, request, immediate, HV, HS, false_and, true_and,
      not_true_eq_false, not_false_eq_true, and_false, decide_false,
      Bool.false_eq_true, ite_false, ite_true, shifted, query, pairSnd_pair]
  simp only [decide_eq_true_eq]

theorem valid_packet (L : Layout) (c : List Bool)
    (a : MacaulayFullBox.Row (L.arity c) (L.width c))
    (b : MacaulayFullBox.Column (L.arity c) (L.width c)) (r t : ℕ) :
    valid L (entryPacket c (rowNumber _ _ a) b.val r t) := by
  simp only [valid, ctx_entryPacket, idx_entryPacket, shift_entryPacket, rowCut_eq, columnsCode_eq,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact ⟨rowNumber_lt _ _ a, b.isLt⟩

theorem source_value {A : Type*} [CommRing A] (L : Layout) (modulus : List Bool → ℕ)
    (reply : List Bool → List Bool) (c : List Bool)
    (p : Fin (L.arity c) → MvPolynomial (Fin (L.arity c)) A)
    (enc : A → List Bool) (hz : enc 0 = [])
    (hlevel : L.level c = Macaulay.level (fun i : Fin (L.arity c) => L.degree c i.val))
    (r t : ℕ) (ha : ∀ (i : Fin (L.arity c)) k, reply
      (pair c (pair (BinaryNatCode.encode i.val) (pair (BinaryNatCode.encode k)
        (pair (BinaryNatCode.encode r) (BinaryNatCode.encode t))))) =
      enc ((p i).coeff (RationalSubstitution.Indexed.exponentVector (L.arity c)
        (FixedWidthPolynomial.entry (L.width c) k))))
    (i : Fin (L.arity c)) (a b : MacaulayFullBox.Column (L.arity c) (L.width c)) :
    (program L modulus).value reply (entryPacket c (rowNumber _ _ (.inl (i, a))) b.val r t) =
      enc (MacaulayFullBox.matrix p (fun i => L.degree c i.val) (L.width c) (.inl (i, a)) b) := by
  have HS : isSource L (entryPacket c (rowNumber _ _ (.inl (i, a))) b.val r t) := by
    simp only [isSource, idx_entryPacket, ctx_entryPacket, sourceCut_eq, BinaryNatCode.encode,
      Nat.fromBitsLE_bits, rowNumber]
    have H := Nat.mul_le_mul_right (FixedWidthPolynomial.count (L.arity c) (L.width c)) i.isLt
    rw [Nat.succ_mul] at H
    have HA := a.isLt
    omega
  rw [value, ite_eq_left (valid_packet L c (.inl (i, a)) b r t), ite_eq_left HS]
  rw [rowNumber, rawSourceInput_packet L c i.val a.val b.val r t a.isLt,
    shifted_packet L c r t p enc reply hz ha]
  change (if _ then _ else []) = enc (if _ then _ else 0)
  rw [← hlevel]
  split_ifs <;> simp only [hz]

theorem padding_value {A : Type*} [CommRing A] {M : ℕ} (basis : Module.Basis (Fin M) ℤ A)
    (L : Layout) (modulus : List Bool → ℕ) (reply : List Bool → List Bool) (c : List Bool)
    (p : Fin (L.arity c) → MvPolynomial (Fin (L.arity c)) A)
    (hlevel : L.level c = Macaulay.level (fun i : Fin (L.arity c) => L.degree c i.val))
    (hm : 0 < modulus c)
    (a b : MacaulayFullBox.Column (L.arity c) (L.width c)) (r t : Fin M) :
    (program L modulus).value reply (entryPacket c (rowNumber _ _ (.inr a)) b.val r.val t.val) =
      residueBits ((Algebra.leftMulMatrix basis
        (MacaulayFullBox.matrix p (fun i => L.degree c i.val) (L.width c) (.inr a) b) r t : ℤ) :
          ZMod (modulus c)) := by
  let : NeZero (modulus c) := ⟨hm.ne'⟩
  have HS : ¬isSource L (entryPacket c (rowNumber _ _ (.inr a)) b.val r.val t.val) := by
    simp only [isSource, rowNumber, ctx_entryPacket, idx_entryPacket, sourceCut_eq,
      BinaryNatCode.encode, Nat.fromBitsLE_bits]
    omega
  have HP : isPadding L (entryPacket c (rowNumber _ _ (.inr a)) b.val r.val t.val) ↔
      (FixedWidthPolynomial.vector _ _ a).degree ≠ L.level c ∧ a = b := by
    unfold isPadding
    rw [rowNumber, rawPaddingInput_packet]
    simp only [ctx_entryPacket, idx_entryPacket, shift_entryPacket, sourceCut_eq,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.add_sub_cancel_left, ne_eq, total_packet_iff, Fin.ext_iff]
  have HD : diagonal (entryPacket c (rowNumber _ _ (.inr a)) b.val r.val t.val) ↔ r = t := by
    simp only [diagonal, uv_entryPacket, pairFst_pair, pairSnd_pair, BinaryNatCode.encode,
      Nat.fromBitsLE_bits, Fin.ext_iff]
  rw [value, ite_eq_left (valid_packet L c (.inr a) b r.val t.val), ite_eq_right HS]
  simp only [HP, HD, ctx_entryPacket, MacaulayFullBox.matrix, ← hlevel]
  by_cases HE : (FixedWidthPolynomial.vector _ _ a).degree = L.level c <;>
    by_cases HAB : a = b <;> by_cases HRT : r = t <;>
    simp_all [residueBits, BinaryNatCode.encode]
  exact ArithmeticBits.one_residueBits _

theorem actual_value {A : Type*} [CommRing A] {M : ℕ} (basis : Module.Basis (Fin M) ℤ A)
    (L : Layout) (modulus : List Bool → ℕ) (reply : List Bool → List Bool) (c : List Bool)
    (p : Fin (L.arity c) → MvPolynomial (Fin (L.arity c)) A)
    (hlevel : L.level c = Macaulay.level (fun i : Fin (L.arity c) => L.degree c i.val))
    (hm : 0 < modulus c) (r t : Fin M)
    (ha : ∀ (i : Fin (L.arity c)) k, reply
      (pair c (pair (BinaryNatCode.encode i.val) (pair (BinaryNatCode.encode k)
        (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val))))) =
      residueBits ((Algebra.leftMulMatrix basis
        ((p i).coeff (RationalSubstitution.Indexed.exponentVector (L.arity c)
          (FixedWidthPolynomial.entry (L.width c) k))) r t : ℤ) : ZMod (modulus c)))
    (a : MacaulayFullBox.Row (L.arity c) (L.width c))
    (b : MacaulayFullBox.Column (L.arity c) (L.width c)) :
    (program L modulus).value reply (entryPacket c (rowNumber _ _ a) b.val r.val t.val) =
      residueBits ((Algebra.leftMulMatrix basis
        (MacaulayFullBox.matrix p (fun i => L.degree c i.val) (L.width c) a b) r t : ℤ) : ZMod (modulus c)) := by
  rcases a with ⟨i, a⟩ | a
  · exact source_value L modulus reply c p
      (fun z => residueBits ((Algebra.leftMulMatrix basis z r t : ℤ) : ZMod (modulus c)))
      (by simp only [map_zero, Matrix.zero_apply, Int.cast_zero, residueBits, ZMod.val_zero,
        BinaryNatCode.encode, Nat.zero_bits]) hlevel r.val t.val ha i a b
  · exact padding_value basis L modulus reply c p hlevel hm a b r t

end LeanCanny.Algebra.MacaulayIntegralEntryRequest
