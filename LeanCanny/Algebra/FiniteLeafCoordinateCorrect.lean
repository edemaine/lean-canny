/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FiniteLeafCoordinateSpace
public import LeanCanny.Algebra.BalancedLeafPath
public import LeanCanny.Algebra.FiniteAnnihilatorCoefficientSpace

/-! # Computed finite-leaf coordinates recover the original decoder

At every parameter root, all denominators on the selected path are nonzero.
The whole-path coordinate equals the existing balanced decoder and hence
recovers a root of the selected original finite-family polynomial.
-/

@[expose] public section

namespace LeanCanny.Algebra.FiniteLeafCoordinateBits
open Polynomial UnivariateRational
open LeanCanny.Encoding LeanCanny.Computation
open SeparableBits (Family)
open FiniteLeafPathContext

theorem ancestor_lt (N h j : ℕ) (hh : h ≤ N) (hj : j < 2 ^ N) : j / 2 ^ h < 2 ^ (N - h) := by
  apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos h)).mpr
  calc
    j < 2 ^ N := hj
    _ = 2 ^ (N - h) * 2 ^ h := by rw [← pow_add, Nat.sub_add_cancel hh]

variable (B : Family) (count D b : List Bool → ℕ)
variable (hne : ∀ c i, i < count c → B.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0)
variable (hdegree : ∀ c i, i < count c → (B.polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ D c)
variable (hheight : ∀ c i, i < count c → B.height (pair c (BinaryNatCode.encode i)) ≤ b c)

theorem stage_eq (u : List Bool) (s : ℕ) (hs : s < depth count u) :
    (source B count D b hne).inner u s =
      BalancedLeafPath.step (PaddedAnnihilatorPreparation.leaves B count hne (pairFst u)) (leafIndex count u) s := by
  let j := leafIndex count u
  have hh : s + 1 ≤ (count (pairFst u)).size := by exact hs
  have hi : BalancedLeafPath.ancestor j (s + 1) < 2 ^ ((count (pairFst u)).size - (s + 1)) :=
    ancestor_lt _ _ _ hh (leafIndex_lt count u)
  have hp : parent count (pair u (BinaryNatCode.encode s)) =
      BalancedParameterContext.packet (pairFst u) (s + 1) (BalancedLeafPath.ancestor j (s + 1)) := by
    simp only [parent, position, stage_packet count u s hs.le, pairFst_pair]
    change BalancedParameterContext.packet (pairFst u) (s + 1) (BalancedLeafPath.ancestor j s / 2) = _
    rw [← BalancedLeafPath.ancestor_succ]
  have hr : right count (pair u (BinaryNatCode.encode s)) ↔ BalancedLeafPath.ancestor j s % 2 = 1 := by
    simp only [right, position, stage_packet count u s hs.le, pairFst_pair]
    rfl
  simp only [source, rawCoordinate, hp, hr,
    CanonicalPairBits.left_packet B count hne (pairFst u) s _ hh hi,
    CanonicalPairBits.right_packet B count hne (pairFst u) s _ hh hi, BalancedLeafPath.step]
  split_ifs <;> rfl

include hdegree hheight in
theorem coordinate_spec {K : Type*} [Field K] [CharZero K] (u : List Bool) (theta : K)
    (ht : (BalancedPrimitiveTree.node (PaddedAnnihilatorPreparation.leaves B count hne (pairFst u))
      (depth count u) 0).polynomial.eval₂ (Int.castRingHom K) theta = 0) :
    (coordinate B count D b hne u).denominator.eval₂ (Int.castRingHom K) theta ≠ 0 ∧
    (coordinate B count D b hne u).eval theta = BalancedPrimitiveTree.coordinate (depth count u)
      (BalancedPrimitiveTree.decode (PaddedAnnihilatorPreparation.leaves B count hne (pairFst u)) (depth count u) 0 theta) (leafIndex count u) := by
  let F := source B count D b hne
  let L := PaddedAnnihilatorPreparation.leaves B count hne (pairFst u)
  let j := leafIndex count u
  let N := depth count u
  have hj : j < 2 ^ N := leafIndex_lt count u
  have ha : BalancedLeafPath.ancestor j N = 0 := Nat.div_eq_of_lt hj
  have ht' : (BalancedPrimitiveTree.node L N (BalancedLeafPath.ancestor j N)).polynomial.eval₂ (Int.castRingHom K) theta = 0 := by
    rw [ha]; exact ht
  have W := BalancedLeafPath.walk_spec L j N theta ht'
  have C := RationalCoordinatePath.trace_congr (F.inner u) (BalancedLeafPath.step L j) N
    (fun s hs => stage_eq B count D b hne u s hs) theta
  have H := RationalCoordinatePath.path_spec (degreeControl count D b u) (F.inner u)
    (fun s => (stage_bounds B count D b hne hdegree hheight u s).1) N theta (C.1.mpr W.1)
  refine ⟨H.1, H.2.trans (C.2.trans ?_)⟩
  simpa only [ha, Nat.mod_eq_of_lt hj] using W.2

include hdegree hheight in
theorem finite_decode_spec {K : Type*} [Field K] [CharZero K] (c : List Bool) (i : Fin (count c)) (theta : K)
    (ht : (FiniteAnnihilatorBits.finiteParameter B count hne c).eval₂ (Int.castRingHom K) theta = 0) :
    (coordinate B count D b hne (pair c (BinaryNatCode.encode i.val))).denominator.eval₂ (Int.castRingHom K) theta ≠ 0 ∧
    (coordinate B count D b hne (pair c (BinaryNatCode.encode i.val))).eval theta =
      FiniteAnnihilatorTree.decode (fun j => B.polynomial (pair c (BinaryNatCode.encode j))) (count c) (hne c) theta i := by
  have hj : i.val < 2 ^ (count c).size := i.isLt.trans (Nat.lt_size_self (count c))
  have hd : depth count (pair c (BinaryNatCode.encode i.val)) = (count c).size := by
    simp only [depth, pairFst_pair]
  have hl : PaddedAnnihilatorPreparation.leaves B count hne (pairFst (pair c (BinaryNatCode.encode i.val))) =
      PaddedAnnihilatorPreparation.leaves B count hne c := by rw [pairFst_pair]
  have H := coordinate_spec B count D b hne hdegree hheight (pair c (BinaryNatCode.encode i.val)) theta
    (by rw [hd, hl]; exact ht)
  rw [hd, hl, leafIndex_packet count c i.val hj] at H
  exact H

include hdegree hheight in
theorem original_root {K : Type*} [Field K] [CharZero K] (c : List Bool) (i : Fin (count c)) (theta : K)
    (ht : (FiniteAnnihilatorBits.finiteParameter B count hne c).eval₂ (Int.castRingHom K) theta = 0) :
    (B.polynomial (pair c (BinaryNatCode.encode i.val))).eval₂ (Int.castRingHom K)
      ((coordinate B count D b hne (pair c (BinaryNatCode.encode i.val))).eval theta) = 0 := by
  rw [(finite_decode_spec B count D b hne hdegree hheight c i theta ht).2]
  exact FiniteAnnihilatorTree.decode_root _ _ _ theta ht i

include hdegree hheight in
theorem eval_eq_flat {K : Type*} [Field K] [CharZero K] (c : List Bool) (i : Fin (count c)) (theta : K)
    (ht : (FiniteAnnihilatorBits.finiteParameter B count hne c).eval₂ (Int.castRingHom K) theta = 0) :
    (coordinate B count D b hne (pair c (BinaryNatCode.encode i.val))).eval theta =
      (FiniteAnnihilatorTree.rationalCoordinate (fun j => B.polynomial (pair c (BinaryNatCode.encode j))) (count c) (hne c) i).eval theta :=
  (finite_decode_spec B count D b hne hdegree hheight c i theta ht).2.trans
    (FiniteAnnihilatorTree.coordinate_spec _ _ _ theta ht i).2.symm

include hdegree hheight in
theorem coordinate_at_solution {K : Type*} [Field K] [CharZero K] (c : List Bool) (x : Fin (count c) → K)
    (hx : ∀ i, (B.polynomial (pair c (BinaryNatCode.encode i.val))).eval₂ (Int.castRingHom K) (x i) = 0) (i : Fin (count c)) :
    (coordinate B count D b hne (pair c (BinaryNatCode.encode i.val))).denominator.eval₂ (Int.castRingHom K)
      (FiniteAnnihilatorTree.encode (fun j => B.polynomial (pair c (BinaryNatCode.encode j))) (count c) (hne c) x) ≠ 0 ∧
    (coordinate B count D b hne (pair c (BinaryNatCode.encode i.val))).eval
      (FiniteAnnihilatorTree.encode (fun j => B.polynomial (pair c (BinaryNatCode.encode j))) (count c) (hne c) x) = x i := by
  have ht := FiniteAnnihilatorTree.encode_root (fun j => B.polynomial (pair c (BinaryNatCode.encode j))) (count c) (hne c) x hx
  have H := finite_decode_spec B count D b hne hdegree hheight c i _ ht
  exact ⟨H.1, H.2.trans (congrFun (FiniteAnnihilatorTree.decode_encode _ _ _ x hx) i)⟩

end LeanCanny.Algebra.FiniteLeafCoordinateBits
