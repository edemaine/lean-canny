/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FixedWidthQuery
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Algebra.BigOperators.Fin

/-! # Short records for sparse feature products

Each fixed-width slot is zero for a unit factor, or one plus a feature index.
Large raw codes are clamped to the final feature. Every monomial of total
exponent at most A has a record with A slots; duplicates encode powers.
-/

@[expose] public section
namespace LeanCanny.Encoding.SparseFeatureRecords
open scoped Classical BigOperators

def coordinate (W : ℕ) (r : List Bool) (i : ℕ) : ℕ := Nat.fromBitsLE ((r.drop (i * W)).take W)

def pick {n : ℕ} (hn : 0 < n) (k : ℕ) : Fin n :=
  ⟨min (k - 1) (n - 1), lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt hn (by decide))⟩

def factor {n : ℕ} {M : Type*} [One M] (hn : 0 < n) (v : Fin n → M) (k : ℕ) : M :=
  if k = 0 then 1 else v (pick hn k)

theorem factor_zero {n : ℕ} {M : Type*} [One M] (hn : 0 < n) (v : Fin n → M) :
    factor hn v 0 = 1 := ite_eq_left rfl

theorem factor_succ {n : ℕ} {M : Type*} [One M] (hn : 0 < n) (v : Fin n → M) (i : Fin n) :
    factor hn v (i.val + 1) = v i := by
  simp only [factor, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
  congr 1
  apply Fin.ext
  simp only [pick, Nat.add_sub_cancel, Nat.min_eq_left (by omega : i.val ≤ n - 1)]

def value {n : ℕ} {M : Type*} [CommMonoid M] (hn : 0 < n) (A W : ℕ)
    (v : Fin n → M) (r : List Bool) : M :=
  ∏ i ∈ Finset.range A, factor hn v (coordinate W r i)

theorem coordinate_append_left (A W : ℕ) (r s : List Bool) (hr : r.length = A * W)
    (i : ℕ) (hi : i < A) : coordinate W (r ++ s) i = coordinate W r i := by
  have hb : i * W + W ≤ A * W := by
    simpa only [Nat.succ_mul] using Nat.mul_le_mul_right W (Nat.succ_le_of_lt hi)
  have hi' : i * W ≤ r.length := by omega
  have ht : W ≤ (r.drop (i * W)).length := by rw [List.length_drop, hr]; omega
  unfold coordinate
  rw [List.drop_append_of_le_length hi', List.take_append_of_le_length ht]

theorem coordinate_append_right (A W : ℕ) (r s : List Bool) (hr : r.length = A * W) (i : ℕ) :
    coordinate W (r ++ s) (A + i) = coordinate W s i := by
  have he : (A + i) * W = r.length + i * W := by rw [Nat.add_mul, hr]
  unfold coordinate
  rw [he, List.drop_append]
  simp only [List.drop_eq_nil_of_le (Nat.le_add_right r.length (i * W)),
    List.nil_append, Nat.add_sub_cancel_left]

theorem value_append {n : ℕ} {M : Type*} [CommMonoid M] (hn : 0 < n) (A B W : ℕ)
    (v : Fin n → M) (r s : List Bool) (hr : r.length = A * W) :
    value hn (A + B) W v (r ++ s) = value hn A W v r * value hn B W v s := by
  unfold value
  rw [Finset.prod_range_add]
  congr 1
  · exact Finset.prod_congr rfl (fun i hi => congrArg (factor hn v)
      (coordinate_append_left A W r s hr i (Finset.mem_range.mp hi)))
  · exact Finset.prod_congr rfl (fun i _ => congrArg (factor hn v) (coordinate_append_right A W r s hr i))

theorem exists_record {n : ℕ} {M : Type*} [CommMonoid M] (hn : 0 < n) (A W : ℕ)
    (hfit : n < 2 ^ W) (d : Fin n →₀ ℕ) (hd : d.sum (fun _ k => k) ≤ A) :
    ∃ r : List Bool, r.length = A * W ∧ ∀ v : Fin n → M, value hn A W v r = d.prod (fun i k => v i ^ k) := by
  let l := d.toMultiset.toList
  have hlen : l.length ≤ A := by
    rw [Multiset.length_toList, Finsupp.card_toMultiset]
    exact hd
  let e : ℕ → ℕ := fun j => if hj : j < l.length then l[j].val + 1 else 0
  have hefit (j : ℕ) : e j < 2 ^ W := by
    dsimp only [e]
    split_ifs with hj
    · exact (Nat.succ_le_of_lt l[j].isLt).trans_lt hfit
    · exact Nat.two_pow_pos _
  let r := FixedWidthNatVector.encode A W e
  have hread (i : ℕ) (hi : i < A) : coordinate W r i = e i :=
    FixedWidthNatVector.decode_block A W e i hi (hefit i)
  refine ⟨r, FixedWidthNatVector.length_encode A W e, ?_⟩
  intro v
  change (∏ i ∈ Finset.range A, factor hn v (coordinate W r i)) = _
  have hr : (∏ i ∈ Finset.range A, factor hn v (coordinate W r i)) =
      ∏ i ∈ Finset.range A, factor hn v (e i) :=
    Finset.prod_congr rfl (fun i hi => congrArg (factor hn v) (hread i (Finset.mem_range.mp hi)))
  rw [hr]
  have hp : (∏ i ∈ Finset.range A, factor hn v (e i)) =
      ∏ i ∈ Finset.range l.length, factor hn v (e i) := by
    symm
    apply Finset.prod_subset (Finset.range_mono hlen)
    intro i _ hi
    have hnot : ¬ i < l.length := by simpa only [Finset.mem_range] using hi
    simp only [e, dite_eq_right hnot, factor_zero]
  rw [hp, ← Fin.prod_univ_eq_prod_range]
  have hp' : (∏ i : Fin l.length, factor hn v (e i.val)) = ∏ i : Fin l.length, v l[i.val] := by
    apply Finset.prod_congr rfl
    intro i _
    simp only [e, dite_eq_left i.isLt, factor_succ]
  rw [hp', Fin.prod_univ_fun_getElem]
  have hm : (l.map v).prod = (d.toMultiset.map v).prod := by
    change ((l : Multiset (Fin n)).map v).prod = _
    rw [show (l : Multiset (Fin n)) = d.toMultiset from Multiset.coe_toList _]
  rw [hm, Finset.prod_multiset_map_count]
  simp only [Finsupp.toFinset_toMultiset, Finsupp.count_toMultiset, Finsupp.prod]

theorem total_exponent_le {ι : Type*} (d : ι →₀ ℕ) (w : ℕ)
    (hs : d.support.card ≤ w) (he : ∀ i, d i ≤ 2) : d.sum (fun _ k => k) ≤ 2 * w := by
  calc
    _ ≤ ∑ _i ∈ d.support, 2 := Finset.sum_le_sum (fun i _ => he i)
    _ = d.support.card * 2 := by simp
    _ ≤ _ := by omega

end LeanCanny.Encoding.SparseFeatureRecords
