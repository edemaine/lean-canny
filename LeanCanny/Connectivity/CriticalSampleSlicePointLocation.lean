/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.CriticalSampleSliceCellLabels
public import LeanCanny.Geometry.OrderedRealCellLocation

/-! # Native cell location over an actual sample parameter

A comparison polynomial with the signs of `t - a` counts roots below `a`
and detects equality. Both counts are native; the output is the unique
fixed-width label of the cell containing the endpoint. The evaluator needs
only the original coefficient readers. Its semantic packet supplies the
comparison-polynomial identity separately.
-/

@[expose] public section
namespace LeanCanny.Connectivity.CriticalSampleSlicePointLocation
open Set LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation
open BoundedFullWriter BoundedCriticalSampleSlice CriticalSampleSliceCellCover
open BoundedAlgebraicSlice (Family)
open scoped Classical

noncomputable def below (P : Readers) (Q : BivariateQueryProductBits.Family) (F : Family) (u : List Bool) : ℕ :=
  RootCount.signCount P (BoundedCriticalSampleSliceRootProduct.family P Q) (F.comp dropRecord) .neg
    (BoundedCriticalSampleSliceRootProduct.lift u)

noncomputable def equalCount (P : Readers) (Q : BivariateQueryProductBits.Family) (F : Family) (u : List Bool) : ℕ :=
  RootCount.signCount P (BoundedCriticalSampleSliceRootProduct.family P Q) (F.comp dropRecord) 0
    (BoundedCriticalSampleSliceRootProduct.lift u)

theorem below_evaluator {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) {F : Family} (B : F.Access)
    (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun u => BinaryNatCode.encode (below P Q F u)) :=
  (RootCount.signCount_evaluator h (BoundedCriticalSampleSliceRootProduct.access h A ha)
    (B.comp dropRecord dropRecord_FP) ha .neg).precompose
      BoundedCriticalSampleSliceRootProduct.lift BoundedCriticalSampleSliceRootProduct.lift_FP

theorem equalCount_evaluator {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) {F : Family} (B : F.Access)
    (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun u => BinaryNatCode.encode (equalCount P Q F u)) :=
  (RootCount.signCount_evaluator h (BoundedCriticalSampleSliceRootProduct.access h A ha)
    (B.comp dropRecord dropRecord_FP) ha 0).precompose
      BoundedCriticalSampleSliceRootProduct.lift BoundedCriticalSampleSliceRootProduct.lift_FP

noncomputable def code (P : Readers) (Q : BivariateQueryProductBits.Family) (F : Family) (u : List Bool) : ℕ :=
  if 0 < equalCount P Q F u then below P Q F u
    else BoundedCriticalSampleSliceRootProduct.count P Q u + below P Q F u

noncomputable def locate (P : Readers) (Q : BivariateQueryProductBits.Family) (F : Family) (u : List Bool) : List Bool :=
  ImplicitGraph.word (labelWidth Q u) (code P Q F u)

def finish (Q : BivariateQueryProductBits.Family) (z : List Bool) : List Bool :=
  ImplicitGraph.word (labelWidth Q (pairFst z))
    (if 0 < Nat.fromBitsLE (pairSnd (pairSnd (pairSnd z))) then Nat.fromBitsLE (pairFst (pairSnd z))
      else Nat.fromBitsLE (pairFst (pairSnd (pairSnd z))) + Nat.fromBitsLE (pairFst (pairSnd z)))

theorem finish_FP {Q : BivariateQueryProductBits.Family} (A : BivariateQueryProductBits.Access Q) : finish Q ∈ FP := by
  have hl : BinaryFn (fun z => Nat.fromBitsLE (pairFst (pairSnd z))) :=
    BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
  have hn : BinaryFn (fun z => Nat.fromBitsLE (pairFst (pairSnd (pairSnd z)))) :=
    BinaryFn.fromBits (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP)
  have he : BinaryFn (fun z => Nat.fromBitsLE (pairSnd (pairSnd (pairSnd z)))) :=
    BinaryFn.fromBits (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP)
  exact ImplicitGraph.word_computable ((labelWidth_unary A).comp pairFst_mem_FP)
    (BinaryFn.ite ((BinaryFn.const 0).lt he) hl (hn.add hl))

theorem evaluator {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) {F : Family} (B : F.Access)
    (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (locate P Q F) := by
  have E := ((below_evaluator h A B ha).pairOutputs
    ((BoundedCriticalSampleSliceRootProduct.count_evaluator h A ha).pairOutputs (equalCount_evaluator h A B ha))).withInput
  apply (E.postcompose (finish Q) (finish_FP A)).congr
  funext u
  simp only [Function.comp_apply, finish, locate, code, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem counts_packet (P : Readers) (Q : BivariateQueryProductBits.Family) (F : Family) (u : List Bool) (a : ℝ)
    (hF : ∀ t : ℝ, SignType.sign ((specialized P F u).eval t) = SignType.sign (t - a)) :
    below P Q F u = Geometry.OrderedRealCells.lowerCount (roots P Q u) a ∧
      (0 < equalCount P Q F u ↔ a ∈ roots P Q u) := by
  have hs : specialized P (F.comp dropRecord) (BoundedCriticalSampleSliceRootProduct.lift u) = specialized P F u :=
    specialized_attach P F u u
  have hn (t : ℝ) : SignType.sign ((specialized P F u).eval t) = .neg ↔ t < a := by
    rw [hF]
    simpa only [SignType.neg_eq_neg_one, sub_neg] using
      (sign_eq_neg_one_iff : SignType.sign (t - a) = -1 ↔ t - a < 0)
  have hz (t : ℝ) : SignType.sign ((specialized P F u).eval t) = 0 ↔ t = a := by
    rw [hF, sign_eq_zero_iff, sub_eq_zero]
  constructor
  · unfold below RootCount.signCount RootSignQueries.singleSignCount
    rw [hs]
    change ((roots P Q u).filter _).card = _
    simp only [hn]
    rfl
  · unfold equalCount RootCount.signCount RootSignQueries.singleSignCount
    rw [hs]
    change 0 < ((roots P Q u).filter _).card ↔ _
    simp only [hz, Finset.card_pos, Finset.filter_nonempty_iff, exists_eq_right]

theorem packet (P : Readers) (Q : BivariateQueryProductBits.Family) (F : Family) (u : List Bool) (a : ℝ)
    (hF : ∀ t : ℝ, SignType.sign ((specialized P F u).eval t) = SignType.sign (t - a))
    (i : Index P Q u) (hi : a ∈ piece P Q u i) :
    locate P Q F u = CriticalSampleSliceCellLabels.label P Q u i := by
  have H := counts_packet P Q F u a hF
  simp only [locate, CriticalSampleSliceCellLabels.label, code, H.1, H.2,
    Geometry.OrderedRealCells.code_of_mem_piece (roots P Q u) a i hi]
  rfl

theorem locate_length (P : Readers) (Q : BivariateQueryProductBits.Family) (F : Family) (u : List Bool) :
    (locate P Q F u).length = labelWidth Q u := ImplicitGraph.length_word _ _

end LeanCanny.Connectivity.CriticalSampleSlicePointLocation
