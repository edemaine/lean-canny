/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.InfinitesimalSign
public import LeanCanny.Computation.BoundedFoldSpace

/-!
# Space-bounded infinitesimal signs from coefficient signs

The scan keeps the first nonzero coefficient sign. An FP binary degree bound
allows exponentially many coefficients, while the accumulator has at most two
bits. Coefficient evaluation runs as a space-bounded child, with its workspace
included. The output is the sign on a sufficiently small positive interval.
-/

@[expose] public section

namespace LeanCanny.Algebra.InfinitesimalSign
open Polynomial

open LeanCanny.Computation
open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets

def encode : SignType → List Bool
  | .zero => []
  | .neg => [true]
  | .pos => [false, true]

def tag (z : ℤ) : List Bool := if z = 0 then [] else if z < 0 then [true] else [false, true]

theorem tag_eq_encode (z : ℤ) : tag z = encode (SignType.sign z) := by
  by_cases hz : z = 0
  · simp [tag, hz, encode]
  · by_cases hn : z < 0
    · simp [tag, hz, hn, sign_neg hn, encode]
    · have hp : 0 < z := by omega
      simp [tag, hz, hn, sign_pos hp, encode]

theorem tag_eq_nil (z : ℤ) : tag z = [] ↔ z = 0 := by
  by_cases hz : z = 0 <;> by_cases hn : z < 0 <;> simp [tag, hz, hn]

theorem tag_length_le (z : ℤ) : (tag z).length ≤ 2 := by
  unfold tag
  split_ifs <;> decide

def scan (a : ℕ → ℤ) : ℕ → List Bool
  | 0 => []
  | k + 1 => if scan a k = [] then tag (a k) else scan a k

theorem scan_zero_prefix (a : ℕ → ℤ) (k : ℕ) (hz : ∀ i < k, a i = 0) : scan a k = [] := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [scan, ih (fun i hi => hz i (by omega)), ↓reduceIte, hz k (by omega), tag]

theorem scan_of_first_nonzero (a : ℕ → ℤ) (n k : ℕ) (hn : n < k) (ha : a n ≠ 0)
    (hz : ∀ i < n, a i = 0) : scan a k = tag (a n) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases he : n = k
    · subst n
      simp only [scan, scan_zero_prefix a k hz, ↓reduceIte]
    · have hlt : n < k := by omega
      rw [scan, ih hlt, ite_eq_right ((tag_eq_nil _).not.mpr ha)]

theorem scan_length_le (a : ℕ → ℤ) (k : ℕ) : (scan a k).length ≤ 2 := by
  induction k with
  | zero => simp [scan]
  | succ k ih =>
    rw [scan]
    split_ifs
    · exact tag_length_le _
    · exact ih

theorem scan_eq_trailingCoeff (p : ℤ[X]) (k : ℕ) (hk : p.natDegree < k) :
    scan p.coeff k = tag p.trailingCoeff := by
  by_cases hp : p = 0
  · subst p
    rw [scan_zero_prefix (0 : ℤ[X]).coeff k (by simp)]
    rfl
  · exact scan_of_first_nonzero p.coeff p.natTrailingDegree k
      (p.natTrailingDegree_le_natDegree.trans_lt hk)
      (Polynomial.coeff_natTrailingDegree_ne_zero.mpr hp)
      (fun i hi => Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi)

def query (p : List Bool) : List Bool := pair (pairFst p) (BoundedFold.counter p)
def finish (z : List Bool) : List Bool :=
  if BoundedFold.accumulator (pairFst z) = [] then pairSnd z else BoundedFold.accumulator (pairFst z)
def update (f : List Bool → List Bool) (p : List Bool) : List Bool := finish (pair p (f (query p)))

theorem query_mem_FP : query ∈ FP := mem_FP_pair pairFst_mem_FP BoundedFold.counter_mem_FP
theorem finish_mem_FP : finish ∈ FP := by
  have ha := mem_FP_comp pairFst_mem_FP BoundedFold.accumulator_mem_FP
  have h := (stringEq_fppred ha (constFn_mem_FP [])).ite_mem_FP pairSnd_mem_FP ha
  exact mem_FP_of_eq h (fun _ => rfl)

theorem updateEvaluator {f : List Bool → List Bool} (E : SpaceFunction f) : SpaceFunction (update f) := by
  let Q := ((E.precompose query query_mem_FP).withInput).postcompose finish finish_mem_FP
  refine Q.congr (funext fun p => ?_)
  simp only [Function.comp_apply, update]

theorem fold_eq_scan (f : List Bool → List Bool) (c : List Bool) (a : ℕ → ℤ)
    (hf : ∀ k, f (pair c (BinaryNatCode.encode k)) = tag (a k)) (k : ℕ) :
    BoundedFold.fold (update f) (fun _ => []) c k = scan a k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [BoundedFold.fold, ih]
    simp only [update, finish, query, pairFst_pair, pairSnd_pair, BoundedFold.context_packet,
      BoundedFold.counter_packet, BoundedFold.accumulator_packet, hf, scan]

theorem evaluator {f : List Bool → List Bool} (E : SpaceFunction f)
    (degree : List Bool → List Bool) (hd : degree ∈ FP) (p : List Bool → ℤ[X])
    (hdegree : ∀ c, (p c).natDegree ≤ Nat.fromBitsLE (degree c))
    (hcoeff : ∀ c i, f (pair c (BinaryNatCode.encode i)) = tag ((p c).coeff i)) :
    SpaceFunction (fun c => tag (p c).trailingCoeff) := by
  have hb := mem_FP_comp hd BinaryNat.succ_mem_FP
  let Q := BoundedFold.evaluator (updateEvaluator E) (BinaryNat.succ ∘ degree) (fun _ => [])
    hb (constFn_mem_FP []) 2 (by
      intro c i _
      rw [fold_eq_scan f c (p c).coeff (hcoeff c)]
      simpa only [Polynomial.eval_ofNat] using scan_length_le (p c).coeff i)
  refine Q.congr (funext fun c => ?_)
  simp only [Function.comp_apply, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits]
  rw [fold_eq_scan f c (p c).coeff (hcoeff c)]
  exact scan_eq_trailingCoeff (p c) _ (by have := hdegree c; omega)

theorem tag_eventually_correct (p : ℤ[X]) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, 0 < x → x < δ →
      tag p.trailingCoeff = encode (SignType.sign (p.eval₂ (Int.castRingHom ℝ) x)) := by
  obtain ⟨δ, hδ, hs⟩ := integer_sign_eval_eq_trailingCoeff p
  exact ⟨δ, hδ, fun x hx hxd => by rw [hs x hx hxd, tag_eq_encode]⟩

end LeanCanny.Algebra.InfinitesimalSign
