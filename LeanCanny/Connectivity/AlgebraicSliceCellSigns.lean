/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.AlgebraicSliceCellLabels
public import LeanCanny.Connectivity.AlgebraicSliceCellSignGeometry
public import LeanCanny.Encoding.BoundedAlgebraicSliceRootProductPointSign

/-! # Native factor-sign access on every real cell

Input pairs a base query with a factor index and a cell label. A native
root count selects point evaluation, either one-sided sign, or evaluation
at zero in a rootless fiber. No real sample is supplied or stored.
-/

@[expose] public section
namespace LeanCanny.Connectivity.AlgebraicSliceCellSigns
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation
open BoundedFullWriter BoundedAlgebraicSlice AlgebraicSliceCellCover
open scoped Classical

def factorQuery (q : List Bool) : List Bool := pair (pairFst q) (pairFst (pairSnd q))
theorem factorQuery_FP : factorQuery ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)

def rootQuery (z : List Bool) : List Bool :=
  let n := Nat.fromBitsLE (pairSnd z)
  let c := Nat.fromBitsLE (pairSnd (pairSnd (pairFst z)))
  pair (pairFst (pairFst z)) (pair (pairFst (pairSnd (pairFst z)))
    (BinaryNatCode.encode (if c < n then c else c - n - 1)))

theorem rootQuery_FP : rootQuery ∈ FP := by
  have hn := BinaryFn.fromBits pairSnd_mem_FP
  have hq := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have hc := BinaryFn.fromBits (mem_FP_comp hq pairSnd_mem_FP)
  have hr := BinaryFn.ite (hc.lt hn) hc ((hc.sub hn).sub (BinaryFn.const 1))
  exact mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
    (mem_FP_pair (mem_FP_comp hq pairFst_mem_FP) hr.bits_mem_FP)

noncomputable def read (P : Readers) (Q : BivariateQueryProductBits.Family) (z : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairSnd z) = 0 then
    BoundedAlgebraicSliceRootProductPointSign.zeroValue P Q (factorQuery (pairFst z))
  else if Nat.fromBitsLE (pairSnd (pairSnd (pairFst z))) < Nat.fromBitsLE (pairSnd z) then
    BoundedAlgebraicSliceRootProductPointSign.value P Q (rootQuery z)
  else if Nat.fromBitsLE (pairSnd (pairSnd (pairFst z))) = Nat.fromBitsLE (pairSnd z) then
    BoundedAlgebraicSliceRootProductQueries.value P Q true (rootQuery z)
  else BoundedAlgebraicSliceRootProductQueries.value P Q false (rootQuery z)

private theorem branchProp {p : List Bool → Prop} [DecidablePred p] (hp : FPPred p)
    {f g : List Bool → List Bool} (F : SpaceFunction f) (G : SpaceFunction g) :
    SpaceFunction (fun z => if p z then f z else g z) := by
  have E := SpaceFunction.branch (fun z => decide (p z)) hp.flag_mem_FP F G
  exact E.congr (funext fun z => by simp only [decide_eq_true_eq])

attribute [local irreducible] BoundedAlgebraicSliceRootProductPointSign.value
  BoundedAlgebraicSliceRootProductPointSign.zeroValue BoundedAlgebraicSliceRootProductQueries.value

theorem read_evaluator {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (read P Q) := by
  have hn := BinaryFn.fromBits pairSnd_mem_FP
  have hc := BinaryFn.fromBits (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP)
  have Z := (BoundedAlgebraicSliceRootProductPointSign.zeroEvaluator h A ha).precompose
    (factorQuery ∘ pairFst) (mem_FP_comp pairFst_mem_FP factorQuery_FP)
  have V := (BoundedAlgebraicSliceRootProductPointSign.evaluator h A ha).precompose rootQuery rootQuery_FP
  have L := (BoundedAlgebraicSliceRootProductQueries.evaluator h A ha true).precompose rootQuery rootQuery_FP
  have R := (BoundedAlgebraicSliceRootProductQueries.evaluator h A ha false).precompose rootQuery rootQuery_FP
  have E := branchProp (hn.eq (BinaryFn.const 0)) Z (branchProp (hc.lt hn) V (branchProp (hc.eq hn) L R))
  exact E

noncomputable def value (P : Readers) (Q : BivariateQueryProductBits.Family) (q : List Bool) : List Bool :=
  read P Q (pair q (BinaryNatCode.encode (BoundedAlgebraicSliceRootProduct.count P Q (pairFst q))))

theorem evaluator {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (value P Q) := by
  have N := (BoundedAlgebraicSliceRootProduct.count_evaluator h A ha).precompose pairFst pairFst_mem_FP
  exact N.withInput.chain (read_evaluator h A ha)

theorem root_value (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool)
    (r : Fin (BoundedAlgebraicSliceRootProduct.count P Q u)) :
    (BoundedAlgebraicSliceRootProductQueries.root P Q u r).val = Geometry.OrderedRealCells.root (roots P Q u) r := rfl

theorem value_packet (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (i : ℕ)
    (c : Index P Q u) :
    value P Q (pair u (pair (BinaryNatCode.encode i) (AlgebraicSliceCellLabels.label P Q u c))) =
      InfinitesimalSign.encode (AlgebraicSliceCellSignGeometry.sign P Q u i c) := by
  have hb (n : ℕ) : Nat.fromBitsLE (BinaryNatCode.encode n) = n := Nat.fromBitsLE_bits n
  have hcount : BoundedAlgebraicSliceRootProduct.count P Q u = (roots P Q u).card := rfl
  cases c with
  | inl r =>
    have hn : (roots P Q u).card ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt r.isLt)
    simp only [value, read, rootQuery, pairFst_pair, pairSnd_pair, hb, hcount,
      AlgebraicSliceCellLabels.label_value, Geometry.OrderedRealCells.code, hn, r.isLt, ite_false, ite_true]
    rw [BoundedAlgebraicSliceRootProductPointSign.packet P Q u i r]
    rfl
  | inr k =>
    by_cases hn : (roots P Q u).card = 0
    · simp only [value, read, factorQuery, pairFst_pair, pairSnd_pair, hb, hcount, hn, ite_true]
      rw [BoundedAlgebraicSliceRootProductPointSign.zeroPacket]
      simp only [AlgebraicSliceCellSignGeometry.sign, hn, dite_eq_left]
    · have hlt : ¬ (roots P Q u).card + k.val < (roots P Q u).card := by omega
      by_cases hk : k.val = 0
      · simp only [value, read, rootQuery, pairFst_pair, pairSnd_pair, hb, hcount,
          AlgebraicSliceCellLabels.label_value, Geometry.OrderedRealCells.code, hn, hk, Nat.add_zero,
          lt_self_iff_false, Nat.sub_self, Nat.zero_sub, ite_false, ite_true]
        rw [BoundedAlgebraicSliceRootProductQueries.packet P Q u i ⟨0, by change 0 < (roots P Q u).card; omega⟩ true]
        simp only [ite_true, root_value, AlgebraicSliceCellSignGeometry.sign, hn, hk, ↓reduceDIte]
        rfl
      · have he : (roots P Q u).card + k.val ≠ (roots P Q u).card := by omega
        have hr : (roots P Q u).card + k.val - (roots P Q u).card - 1 = k.val - 1 := by omega
        simp only [value, read, rootQuery, pairFst_pair, pairSnd_pair, hb, hcount,
          AlgebraicSliceCellLabels.label_value, Geometry.OrderedRealCells.code, hn, hlt, he, hr, ite_false]
        rw [BoundedAlgebraicSliceRootProductQueries.packet P Q u i
          ⟨k.val - 1, by change k.val - 1 < (roots P Q u).card; have := k.isLt; omega⟩ false]
        simp only [Bool.false_eq_true, ite_false, root_value, AlgebraicSliceCellSignGeometry.sign, hn, hk, ↓reduceDIte]
        rfl

theorem packet (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (hu : u ∈ valid P)
    (i : Fin (Q.count (pairFst u))) (c : Index P Q u) (y : ℝ) (hy : y ∈ piece P Q u c) :
    value P Q (pair u (pair (BinaryNatCode.encode i.val) (AlgebraicSliceCellLabels.label P Q u c))) =
      InfinitesimalSign.encode (SignType.sign ((BoundedAlgebraicSliceIndexed.value P Q u i.val).eval y)) := by
  rw [value_packet, AlgebraicSliceCellSignGeometry.packet P Q u hu i c y hy]

end LeanCanny.Connectivity.AlgebraicSliceCellSigns
