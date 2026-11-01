/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayIntegralEntryRequest
public import LeanCanny.Algebra.IntegralReciprocalEntry
public import LeanCanny.Algebra.ModularNegFP

/-! # Native selection of the second nilpotent digit

Packets retain the source, reciprocal-system row and homogeneous target.
The only coefficient request deletes the second nilpotent digit from the
two basis indices. Invalid labels are rejected before this request. The
constant chart term is the negative identity matrix, including at any
equal nonzero old basis indices.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralReciprocalEntryRequest
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open MacaulayFullBoxBits
attribute [local irreducible] ArithmeticBits.one ArithmeticBits.negate

structure Parameters where
  free : List Bool → ℕ
  width : List Bool → ℕ
  digit : List Bool → ℕ
  oldRank : List Bool → ℕ
  degree : List Bool → ℕ
  modulus : List Bool → ℕ

structure Controls (F : Parameters) where
  free : UnaryFn F.free
  width : UnaryFn F.width
  digit : BinaryFn F.digit
  oldRank : BinaryFn F.oldRank
  degree : BinaryFn F.degree
  modulus : BinaryFn F.modulus

def row (p : List Bool) : ℕ := Nat.fromBitsLE (idx p)
def target (p : List Bool) : ℕ := Nat.fromBitsLE (shift p)
def basisRow (p : List Bool) : ℕ := Nat.fromBitsLE (pairFst (uv p))
def basisCol (p : List Bool) : ℕ := Nat.fromBitsLE (pairSnd (uv p))
def oldRow (F : Parameters) (p : List Bool) : ℕ := basisRow p / F.digit (ctx p)
def oldCol (F : Parameters) (p : List Bool) : ℕ := basisCol p / F.digit (ctx p)
def rowDigit (F : Parameters) (p : List Bool) : ℕ := basisRow p % F.digit (ctx p)
def colDigit (F : Parameters) (p : List Bool) : ℕ := basisCol p % F.digit (ctx p)

def valid (F : Parameters) (p : List Bool) : Prop :=
  row p < F.free (ctx p) + 1 ∧ target p < count (F.free (ctx p) + 1) (F.width (ctx p)) ∧
    basisRow p < F.oldRank (ctx p) * F.digit (ctx p) ∧ basisCol p < F.oldRank (ctx p) * F.digit (ctx p)

def request (F : Parameters) (p : List Bool) : Prop :=
  valid F p ∧ colDigit F p ≤ rowDigit F p ∧
    ((row p = 0 ∧ rowDigit F p - colDigit F p = 1) ∨
      (0 < row p ∧ rowDigit F p = colDigit F p))

def chart (F : Parameters) (p : List Bool) : Prop :=
  valid F p ∧ row p = 0 ∧ rowDigit F p = colDigit F p ∧
    oldRow F p = oldCol F p ∧ target p = F.degree (ctx p)

instance (F : Parameters) (p : List Bool) : Decidable (valid F p) := inferInstanceAs (Decidable (_ ∧ _))
instance (F : Parameters) (p : List Bool) : Decidable (request F p) := inferInstanceAs (Decidable (_ ∧ _))
instance (F : Parameters) (p : List Bool) : Decidable (chart F p) := inferInstanceAs (Decidable (_ ∧ _))

def query (F : Parameters) (p : List Bool) : List Bool :=
  pair (ctx p) (pair (idx p) (pair (shift p)
    (pair (BinaryNatCode.encode (oldRow F p)) (BinaryNatCode.encode (oldCol F p)))))

def immediate (F : Parameters) (p : List Bool) : List Bool :=
  if chart F p then
    ArithmeticBits.negate (pair (BinaryNatCode.encode (F.modulus (ctx p)))
      (ArithmeticBits.one (BinaryNatCode.encode (F.modulus (ctx p))))) else []

def program (F : Parameters) : SingleCall.Program where
  request p := decide (request F p)
  query := query F
  immediate := immediate F
  finish := pairSnd

theorem row_binary : BinaryFn row := BinaryFn.fromBits idx_FP
theorem target_binary : BinaryFn target := BinaryFn.fromBits shift_FP
theorem basisRow_binary : BinaryFn basisRow := BinaryFn.fromBits (mem_FP_comp uv_FP pairFst_mem_FP)
theorem basisCol_binary : BinaryFn basisCol := BinaryFn.fromBits (mem_FP_comp uv_FP pairSnd_mem_FP)
theorem oldRow_binary (F : Parameters) (a : Controls F) : BinaryFn (oldRow F) :=
  basisRow_binary.div (a.digit.comp ctx_FP)
theorem oldCol_binary (F : Parameters) (a : Controls F) : BinaryFn (oldCol F) :=
  basisCol_binary.div (a.digit.comp ctx_FP)
theorem rowDigit_binary (F : Parameters) (a : Controls F) : BinaryFn (rowDigit F) :=
  basisRow_binary.mod (a.digit.comp ctx_FP)
theorem colDigit_binary (F : Parameters) (a : Controls F) : BinaryFn (colDigit F) :=
  basisCol_binary.mod (a.digit.comp ctx_FP)

theorem valid_FP (F : Parameters) (a : Controls F) : FPPred (valid F) := by
  have HN : BinaryFn (fun p => F.free (ctx p) + 1) :=
    ((BinaryFn.ofUnary a.free).add (BinaryFn.const 1)).comp ctx_FP
  have HC : BinaryFn (fun p => count (F.free (ctx p) + 1) (F.width (ctx p))) :=
    (((BinaryFn.const 2).powUnary a.width).powUnary (a.free.add (UnaryFn.const 1))).comp ctx_FP
  have HR : BinaryFn (fun p => F.oldRank (ctx p) * F.digit (ctx p)) := (a.oldRank.mul a.digit).comp ctx_FP
  exact (row_binary.lt HN).and ((target_binary.lt HC).and ((basisRow_binary.lt HR).and (basisCol_binary.lt HR)))

theorem request_FP (F : Parameters) (a : Controls F) : FPPred (request F) :=
  (valid_FP F a).and (((colDigit_binary F a).le (rowDigit_binary F a)).and
    (((row_binary.eq (BinaryFn.const 0)).and (((rowDigit_binary F a).sub (colDigit_binary F a)).eq (BinaryFn.const 1))).or
      (((BinaryFn.const 0).lt row_binary).and ((rowDigit_binary F a).eq (colDigit_binary F a)))))

theorem chart_FP (F : Parameters) (a : Controls F) : FPPred (chart F) :=
  (valid_FP F a).and ((row_binary.eq (BinaryFn.const 0)).and
    (((rowDigit_binary F a).eq (colDigit_binary F a)).and
      (((oldRow_binary F a).eq (oldCol_binary F a)).and (target_binary.eq (a.degree.comp ctx_FP)))))

theorem query_FP (F : Parameters) (a : Controls F) : query F ∈ FP :=
  mem_FP_pair ctx_FP (mem_FP_pair idx_FP (mem_FP_pair shift_FP
    (mem_FP_pair (oldRow_binary F a).bits_mem_FP (oldCol_binary F a).bits_mem_FP)))

theorem immediate_FP (F : Parameters) (a : Controls F) : immediate F ∈ FP := by
  have HM : BinaryFn (fun p => F.modulus (ctx p)) := a.modulus.comp ctx_FP
  have HO := mem_FP_comp HM.bits_mem_FP ArithmeticBits.one_mem_FP
  exact (chart_FP F a).ite_mem_FP
    (mem_FP_comp (mem_FP_pair HM.bits_mem_FP HO) ArithmeticBits.negate_mem_FP) (constFn_mem_FP [])

attribute [local irreducible] valid request chart query immediate

theorem controls (F : Parameters) (a : Controls F) : (program F).Controls :=
  ⟨(request_FP F a).flag_mem_FP, query_FP F a, immediate_FP F a, pairSnd_mem_FP⟩

theorem requests_iff (F : Parameters) (reply : List Bool → List Bool) (budget : List Bool → ℕ)
    (p child : List Bool) : (program F).controller.Requests reply budget p child ↔
      request F p ∧ child = query F p := by
  rw [SingleCall.Program.requests_iff]
  simp only [program, decide_eq_true_eq]

theorem query_context (F : Parameters) (p : List Bool) : ctx (query F p) = ctx p := by
  simp only [query, ctx, pairFst_pair]
theorem query_row (F : Parameters) (p : List Bool) : idx (query F p) = idx p := by
  simp only [query, idx, pairFst_pair, pairSnd_pair]
theorem query_target (F : Parameters) (p : List Bool) : shift (query F p) = shift p := by
  simp only [query, shift, pairFst_pair, pairSnd_pair]

theorem request_not_chart (F : Parameters) (p : List Bool) (h : request F p) : ¬chart F p := by
  unfold request at h
  unfold chart
  rintro ⟨_, HZ, HE, _, _⟩
  rcases h.2.2 with ⟨_, H⟩ | ⟨H, _⟩ <;> omega

theorem value (F : Parameters) (reply : List Bool → List Bool) (p : List Bool)
    [NeZero (F.modulus (ctx p))] (x : ZMod (F.modulus (ctx p)))
    (ha : request F p → reply (query F p) = residueBits x) :
    (program F).value reply p =
      residueBits (if request F p then x else if chart F p then -1 else 0) := by
  by_cases HR : request F p
  · simp only [SingleCall.Program.value, program, HR, decide_true, ite_true, pairSnd_pair, ha HR]
  · simp only [SingleCall.Program.value, program, HR, decide_false, Bool.false_eq_true, ite_false, immediate]
    by_cases HC : chart F p
    · rw [ite_eq_left HC, ite_eq_left HC, ArithmeticBits.one_residueBits, ArithmeticBits.negate_residueBits]
    · simp only [HC, ite_false, residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits]

theorem query_packet (F : Parameters) (c : List Bool) (j k r t : ℕ) :
    query F (entryPacket c j k r t) = entryPacket c j k (r / F.digit c) (t / F.digit c) := by
  simp only [query, oldRow, oldCol, basisRow, basisCol, ctx_entryPacket, idx_entryPacket,
    shift_entryPacket, uv_entryPacket, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rfl

end LeanCanny.Algebra.IntegralReciprocalEntryRequest
