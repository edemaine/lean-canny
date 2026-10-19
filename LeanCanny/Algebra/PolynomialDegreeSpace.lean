/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.BoundedFoldSpace
public import LeanCanny.Encoding.BinaryNatFP
public import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! # Actual polynomial degrees from suspended coefficient-zero tests

The accumulator is zero for the zero prefix, otherwise one plus the largest
nonzero coefficient index seen. One binary word records both the degree and
the zero-polynomial flag. An FP upper-bound writer permits exponential degrees.
-/

@[expose] public section

namespace LeanCanny.Algebra.PolynomialDegreeBits
open Complexity Polynomial
open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation

def scan (a : ℕ → ℤ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => if a k = 0 then scan a k else k + 1

theorem scan_le (a : ℕ → ℤ) (k : ℕ) : scan a k ≤ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [scan]; split_ifs <;> omega

theorem scan_zero (k : ℕ) : scan (fun _ => 0) k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [scan, ih]

theorem scan_of_last (a : ℕ → ℤ) (n k : ℕ) (hn : n < k) (ha : a n ≠ 0)
    (hz : ∀ i, n < i → i < k → a i = 0) : scan a k = n + 1 := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases he : n = k
    · subst k
      rw [scan, ite_eq_right ha]
    · have hnk : n < k := by omega
      rw [scan, ite_eq_left (hz k (by omega) (by omega))]
      exact ih hnk (fun i hi hik => hz i hi (by omega))

theorem scan_eq_degree (p : ℤ[X]) (k : ℕ) (hk : p.natDegree < k) :
    scan p.coeff k = if p = 0 then 0 else p.natDegree + 1 := by
  by_cases hp : p = 0
  · subst p
    simp only [ite_true]
    have hz : (fun i => (0 : ℤ[X]).coeff i) = (fun _ => 0) := by funext i; exact coeff_zero i
    change scan (fun i => (0 : ℤ[X]).coeff i) k = 0
    rw [hz]
    exact scan_zero k
  · rw [ite_eq_right hp]
    apply scan_of_last p.coeff p.natDegree k hk
    · rw [coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr hp
    · intro i hi _
      exact coeff_eq_zero_of_natDegree_lt hi

def query (p : List Bool) : List Bool := pair (pairFst p) (BoundedFold.counter p)
def finish (z : List Bool) : List Bool :=
  if pairSnd z = [] then BoundedFold.accumulator (pairFst z)
  else BinaryNat.succ (BoundedFold.counter (pairFst z))
def update (f : List Bool → List Bool) (p : List Bool) : List Bool :=
  finish (pair p (f (query p)))

theorem query_mem_FP : query ∈ FP := mem_FP_pair pairFst_mem_FP BoundedFold.counter_mem_FP
theorem finish_mem_FP : finish ∈ FP := by
  have ha := mem_FP_comp pairFst_mem_FP BoundedFold.accumulator_mem_FP
  have hc := mem_FP_comp (mem_FP_comp pairFst_mem_FP BoundedFold.counter_mem_FP) BinaryNat.succ_mem_FP
  have h := (stringEq_fppred pairSnd_mem_FP (constFn_mem_FP [])).ite_mem_FP ha hc
  refine mem_FP_of_eq (g := finish) h ?_
  intro z
  simp only [finish, Function.comp_apply]

noncomputable def updateEvaluator {f : List Bool → List Bool} (E : SpaceFunction f) :
    SpaceFunction (update f) := by
  let Q := ((E.precompose query query_mem_FP).withInput).postcompose finish finish_mem_FP
  refine Q.congr (funext fun p => ?_)
  simp only [update, Function.comp_apply]

theorem fold_eq_scan (f : List Bool → List Bool) (c : List Bool) (a : ℕ → ℤ)
    (hf : ∀ i, f (pair c (BinaryNatCode.encode i)) = [] ↔ a i = 0) (k : ℕ) :
    BoundedFold.fold (update f) (fun _ => []) c k = BinaryNatCode.encode (scan a k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [BoundedFold.fold, ih]
    simp only [update, finish, query, pairFst_pair, pairSnd_pair, BoundedFold.context_packet,
      BoundedFold.counter_packet, BoundedFold.accumulator_packet]
    by_cases ha : a k = 0
    · rw [ite_eq_left ((hf k).mpr ha), scan, ite_eq_left ha]
    · rw [ite_eq_right (fun hz => ha ((hf k).mp hz)), scan, ite_eq_right ha]
      simp only [BinaryNat.succ_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits]

noncomputable def offsetEvaluator {f : List Bool → List Bool} (E : SpaceFunction f)
    (degree : List Bool → List Bool) (hd : degree ∈ FP) (p : List Bool → ℤ[X])
    (hdegree : ∀ c, (p c).natDegree ≤ Nat.fromBitsLE (degree c))
    (hzero : ∀ c i, f (pair c (BinaryNatCode.encode i)) = [] ↔ (p c).coeff i = 0) :
    SpaceFunction (fun c => BinaryNatCode.encode (if p c = 0 then 0 else (p c).natDegree + 1)) := by
  have hb := mem_FP_comp hd BinaryNat.succ_mem_FP
  let count := BinaryNat.succ ∘ degree
  let s := Classical.choose (Cobham.output_length_poly_of_mem_FP hb)
  have hs : ∀ c, (count c).length ≤ s.eval c.length :=
    Classical.choose_spec (Cobham.output_length_poly_of_mem_FP hb)
  let Q := BoundedFold.evaluator (updateEvaluator E) count (fun _ => []) hb (constFn_mem_FP []) s (by
    intro c k hk
    rw [fold_eq_scan f c (p c).coeff (hzero c), BinaryNatCode.length_encode]
    exact ((Nat.size_le_size (scan_le (p c).coeff k)).trans
      ((Nat.size_le_size hk).trans (Nat.size_le.mpr (Nat.fromBitsLE_lt_pow_length (count c))))).trans (hs c))
  refine Q.congr (funext fun c => ?_)
  rw [fold_eq_scan f c (p c).coeff (hzero c)]
  have hk : (p c).natDegree < Nat.fromBitsLE (count c) := by
    simp only [count, Function.comp_apply, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits]
    have := hdegree c
    omega
  rw [scan_eq_degree _ _ hk]

/-- The natural degree, with Mathlib's value zero for the zero polynomial. -/
noncomputable def degreeEvaluator {f : List Bool → List Bool} (E : SpaceFunction f)
    (degree : List Bool → List Bool) (hd : degree ∈ FP) (p : List Bool → ℤ[X])
    (hdegree : ∀ c, (p c).natDegree ≤ Nat.fromBitsLE (degree c))
    (hzero : ∀ c i, f (pair c (BinaryNatCode.encode i)) = [] ↔ (p c).coeff i = 0) :
    SpaceFunction (fun c => BinaryNatCode.encode (p c).natDegree) := by
  let Q := (offsetEvaluator E degree hd p hdegree hzero).postcompose BinaryNat.pred BinaryNat.pred_mem_FP
  refine Q.congr (funext fun c => ?_)
  simp only [Function.comp_apply, BinaryNat.pred_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  by_cases hp : p c = 0 <;> simp [hp]

end LeanCanny.Algebra.PolynomialDegreeBits
