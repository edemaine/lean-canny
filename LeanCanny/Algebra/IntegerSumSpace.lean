/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SignStatisticSpace
public import LeanCanny.Computation.SpaceFunctionChain
public import Cslib.Foundations.Data.Polynomial.Monotone
import Mathlib.Tactic.Ring

/-! # Streaming signed sums with space-bounded integer evaluators

Two unsigned accumulators retain positive and negative parts. They need only
the summands' bit length plus the binary length of the number of summands.
-/

@[expose] public section

namespace LeanCanny.Algebra.IntegerSumBits

open LeanCanny.Encoding
open LeanCanny.Computation
open scoped BigOperators

def positive (a : ℕ → ℤ) (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, (a i).toNat
def negative (a : ℕ → ℤ) (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, (-a i).toNat

def query (p : List Bool) : List Bool := pair (pairFst p) (BoundedFold.counter p)
def finish (z : List Bool) : List Bool :=
  pair (BinaryNat.add (pair (pairFst (BoundedFold.accumulator (pairFst z))) (pairFst (pairSnd z))))
    (BinaryNat.add (pair (pairSnd (BoundedFold.accumulator (pairFst z))) (pairSnd (pairSnd z))))
def update (f : List Bool → List Bool) (p : List Bool) : List Bool := finish (pair p (f (query p)))

theorem query_mem_FP : query ∈ FP := mem_FP_pair pairFst_mem_FP BoundedFold.counter_mem_FP
theorem finish_mem_FP : finish ∈ FP := by
  have ha := mem_FP_comp pairFst_mem_FP BoundedFold.accumulator_mem_FP
  have hp := mem_FP_comp (mem_FP_pair (mem_FP_comp ha pairFst_mem_FP)
    (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)) BinaryNat.add_mem_FP
  have hn := mem_FP_comp (mem_FP_pair (mem_FP_comp ha pairSnd_mem_FP)
    (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)) BinaryNat.add_mem_FP
  have h := mem_FP_pair hp hn
  refine mem_FP_of_eq (g := finish) h ?_
  intro z
  simp only [finish, Function.comp_apply]

theorem updateEvaluator {f : List Bool → List Bool} (E : SpaceFunction f) :
    SpaceFunction (update f) := by
  let Q := (E.precompose query query_mem_FP).withInput.postcompose finish finish_mem_FP
  refine Q.congr (funext fun p => ?_)
  simp only [update, Function.comp_apply]

theorem fold_eq_parts (f : List Bool → List Bool) (c : List Bool) (a : ℕ → ℤ)
    (hf : ∀ i, f (pair c (BinaryNatCode.encode i)) = SignStatisticBits.integerCode (a i)) (n : ℕ) :
    BoundedFold.fold (update f) (fun _ => pair [] []) c n =
      pair (BinaryNatCode.encode (positive a n)) (BinaryNatCode.encode (negative a n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [BoundedFold.fold, ih]
    simp only [update, query, finish, pairFst_pair, pairSnd_pair, BoundedFold.counter_packet,
      BoundedFold.context_packet, BoundedFold.accumulator_packet, hf, SignStatisticBits.integerCode]
    simp only [positive, negative, Finset.sum_range_succ,
      BinaryNat.add_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

def difference (v : List Bool) : List Bool :=
  pair (BinaryNat.sub (pair (pairFst v) (pairSnd v))) (BinaryNat.sub (pair (pairSnd v) (pairFst v)))

theorem difference_mem_FP : difference ∈ FP := by
  have hp := mem_FP_comp (mem_FP_pair pairFst_mem_FP pairSnd_mem_FP) BinaryNat.sub_mem_FP
  have hn := mem_FP_comp (mem_FP_pair pairSnd_mem_FP pairFst_mem_FP) BinaryNat.sub_mem_FP
  have h := mem_FP_pair hp hn
  refine mem_FP_of_eq (g := difference) h ?_
  intro v
  simp only [difference, Function.comp_apply]

theorem difference_parts (p n : ℕ) : difference (pair (BinaryNatCode.encode p) (BinaryNatCode.encode n)) =
    SignStatisticBits.integerCode ((p : ℤ) - n) := by
  simp only [difference, pairFst_pair, pairSnd_pair, BinaryNat.sub_pair, SignStatisticBits.integerCode,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  congr 2 <;> omega

theorem parts_value (a : ℕ → ℤ) (n : ℕ) : (positive a n : ℤ) - negative a n = ∑ i ∈ Finset.range n, a i := by
  simp only [positive, negative, Nat.cast_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  omega

def multiply (v : List Bool) : List Bool := difference
  (pair
    (BinaryNat.add (pair
      (BinaryNat.mul (pair (pairFst (pairFst v)) (pairFst (pairSnd v))))
      (BinaryNat.mul (pair (pairSnd (pairFst v)) (pairSnd (pairSnd v))))))
    (BinaryNat.add (pair
      (BinaryNat.mul (pair (pairFst (pairFst v)) (pairSnd (pairSnd v))))
      (BinaryNat.mul (pair (pairSnd (pairFst v)) (pairFst (pairSnd v)))))))

theorem multiply_mem_FP : multiply ∈ FP := by
  have ha := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hb := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have hc := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hd := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have hpp := mem_FP_comp (mem_FP_pair ha hc) BinaryNat.mul_mem_FP
  have hnn := mem_FP_comp (mem_FP_pair hb hd) BinaryNat.mul_mem_FP
  have hpn := mem_FP_comp (mem_FP_pair ha hd) BinaryNat.mul_mem_FP
  have hnp := mem_FP_comp (mem_FP_pair hb hc) BinaryNat.mul_mem_FP
  have hp := mem_FP_comp (mem_FP_pair hpp hnn) BinaryNat.add_mem_FP
  have hn := mem_FP_comp (mem_FP_pair hpn hnp) BinaryNat.add_mem_FP
  have h := mem_FP_comp (mem_FP_pair hp hn) difference_mem_FP
  refine mem_FP_of_eq (g := multiply) h ?_
  intro v
  simp only [multiply, Function.comp_apply]

theorem multiply_codes (x y : ℤ) :
    multiply (pair (SignStatisticBits.integerCode x) (SignStatisticBits.integerCode y)) =
      SignStatisticBits.integerCode (x * y) := by
  have hx : (x.toNat : ℤ) - (-x).toNat = x := by omega
  have hy : (y.toNat : ℤ) - (-y).toNat = y := by omega
  simp only [multiply, SignStatisticBits.integerCode, pairFst_pair, pairSnd_pair, BinaryNat.mul_pair,
    BinaryNat.add_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [show difference (pair
      (x.toNat * y.toNat + (-x).toNat * (-y).toNat).bits
      (x.toNat * (-y).toNat + (-x).toNat * y.toNat).bits) =
      SignStatisticBits.integerCode
        (((x.toNat * y.toNat + (-x).toNat * (-y).toNat : ℕ) : ℤ) -
          (x.toNat * (-y).toNat + (-x).toNat * y.toNat)) from difference_parts _ _]
  change SignStatisticBits.integerCode _ = SignStatisticBits.integerCode (x * y)
  congr 1
  simp only [Nat.cast_add, Nat.cast_mul]
  calc
    _ = ((x.toNat : ℤ) - (-x).toNat) * ((y.toNat : ℤ) - (-y).toNat) := by ring
    _ = x * y := by rw [hx, hy]

theorem parts_length_le (a : ℕ → ℤ) (k N M : ℕ) (hk : k ≤ N)
    (ha : ∀ i < k, (SignStatisticBits.integerCode (a i)).length ≤ M) :
    (pair (BinaryNatCode.encode (positive a k)) (BinaryNatCode.encode (negative a k))).length ≤
      3 * (N.size + M) + 2 := by
  have hi (i : ℕ) (hi : i < k) : (a i).toNat.size ≤ M ∧ (-a i).toNat.size ≤ M := by
    have h := ha i hi
    simp only [SignStatisticBits.integerCode, pair_length, BinaryNatCode.length_encode] at h
    omega
  have hb (g : ℕ → ℕ) (hg : ∀ i < k, (g i).size ≤ M) :
      (∑ i ∈ Finset.range k, g i).size ≤ N.size + M := by
    apply Nat.size_le.mpr
    calc
      _ ≤ ∑ _i ∈ Finset.range k, 2 ^ M := Finset.sum_le_sum fun i hi =>
        (Nat.size_le.mp (hg i (Finset.mem_range.mp hi))).le
      _ = k * 2 ^ M := by simp
      _ ≤ N * 2 ^ M := Nat.mul_le_mul_right _ hk
      _ < 2 ^ N.size * 2 ^ M := Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self N) (pow_pos (by decide) M)
      _ = 2 ^ (N.size + M) := (pow_add _ _ _).symm
  have hp := hb (fun i => (a i).toNat) (fun i h => (hi i h).1)
  have hn := hb (fun i => (-a i).toNat) (fun i h => (hi i h).2)
  simp only [pair_length, BinaryNatCode.length_encode, positive, negative]
  omega

/-- A binary FP count permits exponentially many summands. The child evaluator's
polynomial output bound supplies the accumulator bound; all child work is charged. -/
theorem evaluator {f : List Bool → List Bool} (E : SpaceFunction f)
    (count : List Bool → List Bool) (hc : count ∈ FP) (a : List Bool → ℕ → ℤ)
    (hf : ∀ c i, f (pair c (BinaryNatCode.encode i)) = SignStatisticBits.integerCode (a c i)) :
    SpaceFunction (fun c => SignStatisticBits.integerCode (∑ i ∈ Finset.range (Nat.fromBitsLE (count c)), a c i)) := by
  let q := Classical.choose (output_length_poly_of_mem_FP hc)
  have hq : ∀ c, (count c).length ≤ q.eval c.length := Classical.choose_spec (output_length_poly_of_mem_FP hc)
  let p := Classical.choose E.exists_output_length_poly
  have hp : ∀ x, (f x).length ≤ p.eval x.length := Classical.choose_spec E.exists_output_length_poly
  let u := 2 * Polynomial.X + q + 2
  have hN (c : List Bool) : (Nat.fromBitsLE (count c)).size ≤ q.eval c.length :=
    (Nat.size_le.mpr (Nat.fromBitsLE_lt_pow_length (count c))).trans (hq c)
  let Q := BoundedFold.evaluator (updateEvaluator E) count (fun _ => pair [] []) hc (constFn_mem_FP _)
    (3 * (q + p.comp u) + 2) (by
      intro c k hk
      rw [fold_eq_parts f c (a c) (hf c)]
      have ha (i : ℕ) (hi : i < k) : (SignStatisticBits.integerCode (a c i)).length ≤ (p.comp u).eval c.length := by
        have hsize := (Nat.size_le_size (show i ≤ Nat.fromBitsLE (count c) by omega)).trans (hN c)
        have hquery : (pair c (BinaryNatCode.encode i)).length ≤ u.eval c.length := by
          simp only [pair_length, BinaryNatCode.length_encode, u, Polynomial.eval_add, Polynomial.eval_mul,
            Polynomial.eval_ofNat, Polynomial.eval_X]
          omega
        have h := hp (pair c (BinaryNatCode.encode i))
        rw [hf c i] at h
        simpa only [Polynomial.eval_comp] using h.trans (p.eval_mono hquery)
      have h := parts_length_le (a c) k _ _ hk ha
      have hn := hN c
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
      exact h.trans (by omega))
  let R := Q.postcompose difference difference_mem_FP
  refine R.congr (funext fun c => ?_)
  simp only [Function.comp_apply]
  rw [fold_eq_parts f c (a c) (hf c), difference_parts, parts_value]

end LeanCanny.Algebra.IntegerSumBits
