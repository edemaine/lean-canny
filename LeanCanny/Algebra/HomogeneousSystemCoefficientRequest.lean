/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralReciprocalEntryRequest
public import LeanCanny.Algebra.HomogenizationBinarySpace
public import LeanCanny.Algebra.DiagonalPolynomialParameterSpace

/-! # Native homogeneous-system requests to original or coordinate rows

System row zero requests one restored original-row coefficient. A positive
row requests one coefficient of its own coordinate polynomial, after a
homogeneous-degree test and rejection of exponents in other coordinates.
The source and the two old basis indices are copied literally.
-/

@[expose] public section
namespace LeanCanny.Algebra.HomogeneousSystemCoefficientRequest
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial
open MacaulayFullBoxBits

structure Parameters where
  free : List Bool → ℕ
  width : List Bool → ℕ
  degree : List Bool → ℕ
  coordinateDegree : List Bool → ℕ
  rank : List Bool → ℕ

structure Controls (F : Parameters) where
  free : UnaryFn F.free
  width : UnaryFn F.width
  degree : BinaryFn F.degree
  coordinateDegree : BinaryFn F.coordinateDegree
  rank : BinaryFn F.rank

def row := IntegralReciprocalEntryRequest.row
def target := IntegralReciprocalEntryRequest.target
def basisRow := IntegralReciprocalEntryRequest.basisRow
def basisCol := IntegralReciprocalEntryRequest.basisCol
def homogeneousPacket (p : List Bool) : List Bool := pair p (shift p)
def stripped (F : Parameters) (p : List Bool) : List Bool := BinaryNat.normalize ((shift p).drop (F.width (ctx p)))
def freePacket (F : Parameters) (p : List Bool) : List Bool := pair p (stripped F p)
def polynomialDegree (F : Parameters) (p : List Bool) : ℕ :=
  if row p = 0 then F.degree (ctx p) else F.coordinateDegree (ctx p)
def total (F : Parameters) (p : List Bool) : ℕ :=
  HomogenizationBits.total (F.free ∘ ctx) (F.free ∘ ctx) (F.width ∘ ctx) (polynomialDegree F) (homogeneousPacket p)
def outsideZero (F : Parameters) (p : List Bool) : Prop :=
  DiagonalParameterBits.outsideZero (F.free ∘ ctx) (F.width ∘ ctx) (fun p => row p - 1) (freePacket F p)

def valid (F : Parameters) (p : List Bool) : Prop := row p < F.free (ctx p) + 1 ∧
  target p < count (F.free (ctx p) + 1) (F.width (ctx p)) ∧ basisRow p < F.rank (ctx p) ∧ basisCol p < F.rank (ctx p)
def request (F : Parameters) (p : List Bool) : Prop :=
  valid F p ∧ total F p = polynomialDegree F p ∧ (row p = 0 ∨ outsideZero F p)
instance (F : Parameters) (p : List Bool) : Decidable (outsideZero F p) := inferInstanceAs (Decidable (∀ i < _, _))
instance (F : Parameters) (p : List Bool) : Decidable (valid F p) := inferInstanceAs (Decidable (_ ∧ _))
instance (F : Parameters) (p : List Bool) : Decidable (request F p) := inferInstanceAs (Decidable (_ ∧ _))

def coefficient (F : Parameters) (p : List Bool) : ℕ :=
  FixedWidthQuery.entry (fun p => F.free (ctx p) + 1) (F.width ∘ ctx) shift p (row p)

/-- Tag zero carries the free exponent word; tag one carries coordinate and degree. -/
def query (F : Parameters) (p : List Bool) : List Bool :=
  if row p = 0 then pair (ctx p) (pair [] (pair (stripped F p) (uv p))) else
    pair (ctx p) (pair [true] (pair (BinaryNatCode.encode (row p - 1))
      (pair (BinaryNatCode.encode (coefficient F p)) (uv p))))

def program (F : Parameters) : SingleCall.Program where
  request p := decide (request F p)
  query := query F
  immediate _ := []
  finish := pairSnd

theorem row_binary : BinaryFn row := IntegralReciprocalEntryRequest.row_binary
theorem target_binary : BinaryFn target := IntegralReciprocalEntryRequest.target_binary
theorem basisRow_binary : BinaryFn basisRow := IntegralReciprocalEntryRequest.basisRow_binary
theorem basisCol_binary : BinaryFn basisCol := IntegralReciprocalEntryRequest.basisCol_binary
theorem homogeneousPacket_FP : homogeneousPacket ∈ FP := mem_FP_pair id_mem_FP shift_FP
theorem stripped_FP (F : Parameters) (a : Controls F) : stripped F ∈ FP :=
  mem_FP_comp (drop_mem_FP shift_FP (a.width.comp ctx_FP)) BinaryNat.normalize_mem_FP
theorem freePacket_FP (F : Parameters) (a : Controls F) : freePacket F ∈ FP :=
  mem_FP_pair id_mem_FP (stripped_FP F a)
theorem polynomialDegree_binary (F : Parameters) (a : Controls F) : BinaryFn (polynomialDegree F) :=
  BinaryFn.ite (row_binary.eq (BinaryFn.const 0)) (a.degree.comp ctx_FP) (a.coordinateDegree.comp ctx_FP)
theorem total_binary (F : Parameters) (a : Controls F) : BinaryFn (total F) :=
  (HomogenizationBits.total_binary (a.free.comp ctx_FP) (a.free.comp ctx_FP) (a.width.comp ctx_FP)
    (polynomialDegree_binary F a)).comp homogeneousPacket_FP
theorem outsideZero_FP (F : Parameters) (a : Controls F) : FPPred (outsideZero F) :=
  (DiagonalParameterBits.outsideZero_FP (a.free.comp ctx_FP) (a.width.comp ctx_FP)
    (row_binary.sub (BinaryFn.const 1))).comp (freePacket_FP F a)
theorem valid_FP (F : Parameters) (a : Controls F) : FPPred (valid F) := by
  have HC : BinaryFn (fun p => count (F.free (ctx p) + 1) (F.width (ctx p))) :=
    (((BinaryFn.const 2).powUnary a.width).powUnary (a.free.add (UnaryFn.const 1))).comp ctx_FP
  have HN : BinaryFn (fun p => F.free (ctx p) + 1) :=
    ((BinaryFn.ofUnary a.free).add (BinaryFn.const 1)).comp ctx_FP
  have HR : BinaryFn (fun p => F.rank (ctx p)) := a.rank.comp ctx_FP
  exact (row_binary.lt HN).and ((target_binary.lt HC).and ((basisRow_binary.lt HR).and (basisCol_binary.lt HR)))
theorem request_FP (F : Parameters) (a : Controls F) : FPPred (request F) :=
  (valid_FP F a).and (((total_binary F a).eq (polynomialDegree_binary F a)).and
    ((row_binary.eq (BinaryFn.const 0)).or (outsideZero_FP F a)))

theorem coefficient_binary (F : Parameters) (a : Controls F) : BinaryFn (coefficient F) := by
  have HR : (fun p => FixedWidthQuery.read (fun p => F.free (ctx p) + 1) (F.width ∘ ctx) shift
      (pair p (BinaryNatCode.encode (row p)))) ∈ FP :=
    mem_FP_comp (mem_FP_pair id_mem_FP row_binary.bits_mem_FP)
      (FixedWidthQuery.read_mem_FP ((a.free.add (UnaryFn.const 1)).comp ctx_FP) (a.width.comp ctx_FP) shift_FP)
  exact (BinaryFn.fromBits HR).of_eq (fun p => by rw [FixedWidthQuery.read_packet]; exact Nat.fromBitsLE_bits _)

theorem query_FP (F : Parameters) (a : Controls F) : query F ∈ FP :=
  (row_binary.eq (BinaryFn.const 0)).ite_mem_FP
    (mem_FP_pair ctx_FP (mem_FP_pair (constFn_mem_FP []) (mem_FP_pair (stripped_FP F a) uv_FP)))
    (mem_FP_pair ctx_FP (mem_FP_pair (constFn_mem_FP [true])
      (mem_FP_pair (row_binary.sub (BinaryFn.const 1)).bits_mem_FP (mem_FP_pair (coefficient_binary F a).bits_mem_FP uv_FP))))

attribute [local irreducible] request query
theorem controls (F : Parameters) (a : Controls F) : (program F).Controls :=
  ⟨(request_FP F a).flag_mem_FP, query_FP F a, constFn_mem_FP [], pairSnd_mem_FP⟩
theorem requests_iff (F : Parameters) (reply : List Bool → List Bool) (budget : List Bool → ℕ)
    (p child : List Bool) : (program F).controller.Requests reply budget p child ↔
      request F p ∧ child = query F p := by
  rw [SingleCall.Program.requests_iff]
  simp only [program, decide_eq_true_eq]
theorem query_context (F : Parameters) (p : List Bool) : pairFst (query F p) = ctx p := by
  unfold query
  split_ifs <;> exact pairFst_pair _ _

theorem coefficient_eq (F : Parameters) (p : List Bool) (hr : row p < F.free (ctx p) + 1) :
    coefficient F p = entry (F.width (ctx p)) (target p) (row p) := by
  rw [coefficient, FixedWidthQuery.entry, ite_eq_left hr]
  change Nat.fromBitsLE (((shift p).drop (row p * F.width (ctx p))).take (F.width (ctx p))) =
    entry (F.width (ctx p)) (Nat.fromBitsLE (shift p)) (row p)
  rw [entry_eq_digit, BinaryNat.value_take, drop_value]

theorem total_eq_iff (F : Parameters) (p : List Bool) : total F p = polynomialDegree F p ↔
    (∑ i ∈ Finset.range (F.free (ctx p) + 1), entry (F.width (ctx p)) (target p) i) = polynomialDegree F p := by
  have H := HomogenizationBits.total_eq_iff (F.free ∘ ctx) (F.free ∘ ctx) (F.width ∘ ctx)
    (polynomialDegree F) (homogeneousPacket p)
  simp only [homogeneousPacket, pairFst_pair, pairSnd_pair, Function.comp_apply] at H
  have HS : HomogenizationLayout.weightedSum (F.free (ctx p)) (F.free (ctx p)) (F.width (ctx p)) (Nat.fromBitsLE (shift p)) =
      ∑ i ∈ Finset.range (F.free (ctx p) + 1), entry (F.width (ctx p)) (Nat.fromBitsLE (shift p)) i := by
    unfold HomogenizationLayout.weightedSum
    apply Finset.sum_congr rfl
    intro i hi
    exact ite_eq_left (Finset.mem_range.mp hi)
  exact H.trans (by rw [HS]; rfl)

/-- A coordinate coefficient request stays within the fixed spatial annihilator degree. -/
theorem coefficient_le (F : Parameters) (p : List Bool) (h : request F p) :
    coefficient F p ≤ polynomialDegree F p := by
  unfold request at h
  have HR : row p < F.free (ctx p) + 1 := h.1.1
  rw [coefficient_eq F p HR]
  exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr HR)).trans_eq
    ((total_eq_iff F p).mp h.2.1)

theorem coordinate_lt (F : Parameters) (p : List Bool) (h : request F p) (hr : row p ≠ 0) :
    row p - 1 < F.free (ctx p) := by
  unfold request at h
  have H := h.1.1
  omega

theorem coefficient_le_coordinateDegree (F : Parameters) (p : List Bool) (h : request F p) (hr : row p ≠ 0) :
    coefficient F p ≤ F.coordinateDegree (ctx p) := by
  have H := coefficient_le F p h
  simpa only [polynomialDegree, hr, ite_false] using H

theorem stripped_bound (F : Parameters) (p : List Bool) (h : request F p) :
    Nat.fromBitsLE (stripped F p) < count (F.free (ctx p)) (F.width (ctx p)) := by
  unfold request at h
  rw [stripped, BinaryNat.normalize_eq_bits, Nat.fromBitsLE_bits, drop_value]
  apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
  have H := h.1.2.1
  simpa only [count, pow_succ, target, IntegralReciprocalEntryRequest.target] using H

end LeanCanny.Algebra.HomogeneousSystemCoefficientRequest
