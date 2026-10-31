/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PurePowerReductionShifts
public import LeanCanny.Algebra.PurePowerReductionCorrect
public import LeanCanny.Algebra.FixedWidthPolynomialFP

/-! # Native normal-column masks and coordinate shifts

Coordinate multiplication adds one bit-block place value to a normal
monomial's binary rank. Nonnormal columns use the zero index. The native
controls derive directly from the finite spatial layout, including for
exponentially many reduction states.
-/

@[expose] public section
namespace LeanCanny.Algebra.PurePowerReductionMatrix
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

theorem index_vector {n B : ℕ} (j : Index n B) :
    FixedWidthPolynomial.index n B (FixedWidthPolynomial.vector n B j)
      (FixedWidthPolynomial.vector_lt n B j) = j := by
  apply FixedWidthPolynomial.vector_injective n B
  rw [FixedWidthPolynomial.vector_index]

theorem shift_value {n B : ℕ} (d : Fin n → ℕ) (bound : ℕ)
    (hgrid : gridBound d + 1 ≤ bound) (hbound : bound < 2 ^ B) (r : Fin n) (j : Index n B) :
    (shift d bound hgrid hbound r j).val =
      if Normal d (FixedWidthPolynomial.vector n B j) then j.val + 2 ^ (r.val * B) else 0 := by
  have HJ : ∑ i : Fin n, FixedWidthPolynomial.vector n B j i * (2 ^ B) ^ i.val = j.val :=
    congrArg Fin.val (index_vector j)
  by_cases hj : Normal d (FixedWidthPolynomial.vector n B j)
  · rw [shift, dite_eq_left hj, ite_eq_left hj]
    change (∑ i : Fin n, ((FixedWidthPolynomial.vector n B j + Finsupp.single r 1 : Fin n →₀ ℕ) i) * (2 ^ B) ^ i.val) = _
    simp only [Finsupp.add_apply, add_mul, Finset.sum_add_distrib, HJ]
    congr 1
    simp only [Finsupp.single_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [← pow_mul, Nat.mul_comm B r.val]
  · rw [shift, dite_eq_right hj, ite_eq_right hj]
    change (∑ i : Fin n, (0 : Fin n →₀ ℕ) i * (2 ^ B) ^ i.val) = 0
    simp only [Finsupp.zero_apply, zero_mul, Finset.sum_const_zero]

end LeanCanny.Algebra.PurePowerReductionMatrix

namespace LeanCanny.Algebra.PurePowerReductionShiftBits
open LeanCanny.Encoding LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Layout extends PurePowerReductionBits.Layout where
  bound : List Bool → ℕ
  grid_le : ∀ c, PurePowerReductionMatrix.gridBound (fun i : Fin (arity c) => degree c i.val) + 1 ≤ bound c
  bound_lt : ∀ c, bound c < 2 ^ width c
  coordinate : ∀ c, Fin (arity c)

def index (L : Layout) (q : List Bool) : Fin (FixedWidthPolynomial.count (L.arity (pairFst q)) (L.width (pairFst q))) :=
  ⟨Nat.fromBitsLE (pairSnd q) % FixedWidthPolynomial.count (L.arity (pairFst q)) (L.width (pairFst q)),
    Nat.mod_lt _ (pow_pos (pow_pos (by decide : 0 < (2 : ℕ)) _) _)⟩

theorem index_binary (L : Layout) (h : L.toLayout.PolyTime) : BinaryFn (fun q => (index L q).val) := by
  have H : BinaryFn (fun c => FixedWidthPolynomial.count (L.arity c) (L.width c)) :=
    BinaryFn.of_bits (mem_FP_of_eq (FixedWidthPolynomial.countCode_mem_FP h.arity h.width)
      (fun c => FixedWidthPolynomial.countCode_code _ _ c))
  have HQ : BinaryFn (fun q => FixedWidthPolynomial.count (L.arity (pairFst q)) (L.width (pairFst q))) :=
    H.comp pairFst_mem_FP
  exact (BinaryFn.fromBits pairSnd_mem_FP).mod HQ

def normal (L : Layout) (q : List Bool) : Prop :=
  PurePowerReductionMatrix.Normal (fun i : Fin (L.arity (pairFst q)) => L.degree (pairFst q) i.val)
    (FixedWidthPolynomial.vector _ _ (index L q))

theorem normal_pair (L : Layout) (c w : List Bool) :
    normal L (pair c w) ↔ PurePowerReductionMatrix.Normal
      (fun i : Fin (L.arity c) => L.degree c i.val)
      (FixedWidthPolynomial.vector (L.arity c) (L.width c)
        ⟨Nat.fromBitsLE w % FixedWidthPolynomial.count (L.arity c) (L.width c),
          Nat.mod_lt _ (pow_pos (pow_pos (by decide : 0 < (2 : ℕ)) _) _)⟩) := by
  generalize hz : pair c w = q
  have HC : pairFst q = c := by rw [← hz, pairFst_pair]
  have HW : pairSnd q = w := by rw [← hz, pairSnd_pair]
  subst c
  have HI : index L q =
      ⟨Nat.fromBitsLE w % FixedWidthPolynomial.count (L.arity (pairFst q)) (L.width (pairFst q)),
        Nat.mod_lt _ (pow_pos (pow_pos (by decide : 0 < (2 : ℕ)) _) _)⟩ := by
    apply Fin.ext
    change Nat.fromBitsLE (pairSnd q) % _ = Nat.fromBitsLE w % _
    rw [HW]
  unfold normal
  rw [HI]

def normalQuery (L : Layout) (q : List Bool) : List Bool :=
  PurePowerReductionBits.packet q (index L q).val (index L q).val

theorem normalQuery_FP (L : Layout) (h : L.toLayout.PolyTime) : normalQuery L ∈ FP :=
  mem_FP_pair id_mem_FP
    (mem_FP_pair (index_binary L h).bits_mem_FP (index_binary L h).bits_mem_FP)

theorem normal_fppred (L : Layout) (h : L.toLayout.PolyTime) : FPPred (normal L) := by
  apply ((PurePowerReductionBits.normal_fppred h).comp (normalQuery_FP L h)).of_iff
  intro q
  exact PurePowerReductionBits.normal_packet L.toLayout q (index L q) (index L q).val

noncomputable def shiftValue (L : Layout) (q : List Bool) : ℕ :=
  (PurePowerReductionMatrix.shift (fun i : Fin (L.arity (pairFst q)) => L.degree (pairFst q) i.val)
    (L.bound (pairFst q)) (L.grid_le (pairFst q)) (L.bound_lt (pairFst q))
    (L.coordinate (pairFst q)) (index L q)).val

theorem shiftValue_pair (L : Layout) (c w : List Bool) :
    shiftValue L (pair c w) =
      (PurePowerReductionMatrix.shift (fun i : Fin (L.arity c) => L.degree c i.val)
        (L.bound c) (L.grid_le c) (L.bound_lt c) (L.coordinate c)
        ⟨Nat.fromBitsLE w % FixedWidthPolynomial.count (L.arity c) (L.width c),
          Nat.mod_lt _ (pow_pos (pow_pos (by decide : 0 < (2 : ℕ)) _) _)⟩).val := by
  generalize hz : pair c w = q
  have HC : pairFst q = c := by rw [← hz, pairFst_pair]
  have HW : pairSnd q = w := by rw [← hz, pairSnd_pair]
  subst c
  have HI : index L q =
      ⟨Nat.fromBitsLE w % FixedWidthPolynomial.count (L.arity (pairFst q)) (L.width (pairFst q)),
        Nat.mod_lt _ (pow_pos (pow_pos (by decide : 0 < (2 : ℕ)) _) _)⟩ := by
    apply Fin.ext
    change Nat.fromBitsLE (pairSnd q) % _ = Nat.fromBitsLE w % _
    rw [HW]
  unfold shiftValue
  rw [HI]

theorem shiftValue_binary (L : Layout) (h : L.toLayout.PolyTime)
    (hc : UnaryFn (fun c => (L.coordinate c).val)) : BinaryFn (shiftValue L) := by
  have HW : UnaryFn (fun q => L.width (pairFst q)) := h.width.comp pairFst_mem_FP
  have HC : UnaryFn (fun q => (L.coordinate (pairFst q)).val) := hc.comp pairFst_mem_FP
  have HP := (BinaryFn.const 2).powUnary (HC.mul HW)
  refine BinaryFn.of_eq (BinaryFn.ite (normal_fppred L h) ((index_binary L h).add HP) (BinaryFn.const 0)) (fun q => ?_)
  exact (PurePowerReductionMatrix.shift_value _ _ _ _ _ _).symm

end LeanCanny.Algebra.PurePowerReductionShiftBits
