/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.BoundedFoldSpace
public import LeanCanny.Encoding.BinarySubFP
public import LeanCanny.Algebra.InfinitesimalSign

/-! # Finding a lowest nonzero coefficient with space-bounded zero tests

The accumulator stores the first nonzero index plus one, with zero denoting
no index yet. A final predecessor returns the polynomial's natural trailing
degree, including the zero polynomial convention. Binary degree bounds allow
exponentially many calls while the saved index retains polynomial length.
-/

@[expose] public section

namespace LeanCanny.Algebra.LowestCoefficientBits
open LeanCanny.Encoding LeanCanny.Computation
open LeanCanny.Encoding.Brackets
open scoped Classical

def scan (zero : ℕ → Bool) : ℕ → List Bool
  | 0 => []
  | k + 1 => if scan zero k = [] then if zero k then [] else BinaryNatCode.encode (k + 1) else scan zero k

theorem scan_zero_prefix (zero : ℕ → Bool) (k : ℕ) (hz : ∀ i < k, zero i = true) : scan zero k = [] := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [scan, ih (fun i hi => hz i (by omega)), ite_true, hz k (by omega)]

theorem scan_of_first_nonzero (zero : ℕ → Bool) (n k : ℕ) (hn : n < k) (ha : zero n = false)
    (hz : ∀ i < n, zero i = true) : scan zero k = BinaryNatCode.encode (n + 1) := by
  have he : BinaryNatCode.encode (n + 1) ≠ [] := by
    intro h
    have h' := congrArg Nat.fromBitsLE h
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits] at h'
    change n + 1 = 0 at h'
    omega
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk : n = k
    · subst n
      simp only [scan, scan_zero_prefix zero k hz, ite_true, ha, Bool.false_eq_true, ite_false]
    · rw [scan, ih (by omega), ite_eq_right he]

theorem scan_length_le (zero : ℕ → Bool) (k : ℕ) : (scan zero k).length ≤ k.size := by
  induction k with
  | zero => simp [scan]
  | succ k ih =>
    rw [scan]
    split_ifs
    · simp
    · simp only [BinaryNatCode.length_encode]
      exact le_rfl
    · exact ih.trans (Nat.size_le_size (by omega))

theorem scan_eq_trailingDegree {R : Type*} [Semiring R] (p : Polynomial R) (k : ℕ) (hk : p.natDegree < k) :
    BinaryNat.pred (scan (fun i => decide (p.coeff i = 0)) k) = BinaryNatCode.encode p.natTrailingDegree := by
  by_cases hp : p = 0
  · subst p
    rw [scan_zero_prefix _ k (by simp)]
    rfl
  · rw [scan_of_first_nonzero _ p.natTrailingDegree k (p.natTrailingDegree_le_natDegree.trans_lt hk)
      (by simp [Polynomial.coeff_natTrailingDegree_ne_zero.mpr hp])
      (by intro i hi; simp [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi])]
    simp only [BinaryNat.pred_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.add_sub_cancel]

def query (p : List Bool) : List Bool := BoundedFold.query p

def finish (z : List Bool) : List Bool :=
  if BoundedFold.accumulator (pairFst z) = [] then
    if pairSnd z = [true] then [] else BinaryNat.succ (BoundedFold.counter (pairFst z))
  else BoundedFold.accumulator (pairFst z)

def update (f : List Bool → List Bool) (p : List Bool) : List Bool :=
  BoundedFold.update finish f p

theorem query_mem_FP : query ∈ FP := BoundedFold.query_mem_FP

theorem finish_mem_FP : finish ∈ FP := by
  have ha := mem_FP_comp pairFst_mem_FP BoundedFold.accumulator_mem_FP
  have hc := mem_FP_comp (mem_FP_comp pairFst_mem_FP BoundedFold.counter_mem_FP) BinaryNat.succ_mem_FP
  have hi := (stringEq_fppred pairSnd_mem_FP (constFn_mem_FP [true])).ite_mem_FP (constFn_mem_FP []) hc
  have h := (stringEq_fppred ha (constFn_mem_FP [])).ite_mem_FP hi ha
  exact mem_FP_of_eq (g := finish) h (fun _ => by simp only [finish, Function.comp_apply])

theorem updateEvaluator {f : List Bool → List Bool} (E : SpaceFunction f) : SpaceFunction (update f) := by
  exact BoundedFold.updateEvaluator E finish finish_mem_FP

theorem fold_eq_scan (f : List Bool → List Bool) (c : List Bool) (zero : ℕ → Bool)
    (hf : ∀ k, f (pair c (BinaryNatCode.encode k)) = [zero k]) (k : ℕ) :
    BoundedFold.fold (update f) (fun _ => []) c k = scan zero k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [BoundedFold.fold, ih]
    simp only [update, BoundedFold.update, finish, BoundedFold.query, pairFst_pair, pairSnd_pair, BoundedFold.context_packet,
      BoundedFold.counter_packet, BoundedFold.accumulator_packet, hf, scan, List.cons.injEq, and_true]
    split_ifs <;> simp only [BinaryNat.succ_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem evaluator {R : Type*} [Semiring R] {f : List Bool → List Bool} (E : SpaceFunction f)
    (degree : List Bool → List Bool) (hd : degree ∈ FP) (p : List Bool → Polynomial R)
    (hdegree : ∀ c, (p c).natDegree ≤ Nat.fromBitsLE (degree c))
    (hcoeff : ∀ c i, f (pair c (BinaryNatCode.encode i)) = [decide ((p c).coeff i = 0)]) :
    SpaceFunction (fun c => BinaryNatCode.encode (p c).natTrailingDegree) := by
  have hb := mem_FP_comp hd BinaryNat.succ_mem_FP
  have Q := BoundedFold.evaluator_eq (updateEvaluator E) (BinaryNat.succ ∘ degree) (fun _ => [])
    hb (constFn_mem_FP []) (fun c k => scan (fun i => decide ((p c).coeff i = 0)) k)
    (fun c k _ => fold_eq_scan f c (fun i => decide ((p c).coeff i = 0)) (hcoeff c) k)
    (B := fun c => (BinaryNat.succ (degree c)).length)
    (by simpa only [Turing.MultiTapeTM.encBits_apply, Function.comp_apply]
      using (FP.computable hb).polyBounded_length)
    (by
      intro c i hi
      exact (scan_length_le _ i).trans ((Nat.size_le_size hi).trans
        (Nat.size_le.mpr (Nat.fromBitsLE_lt_pow_length _))))
  have F := Q.postcompose BinaryNat.pred BinaryNat.pred_mem_FP
  refine F.congr (funext fun c => ?_)
  simp only [Function.comp_apply, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits]
  exact scan_eq_trailingDegree (p c) _ (by have := hdegree c; omega)

end LeanCanny.Algebra.LowestCoefficientBits
