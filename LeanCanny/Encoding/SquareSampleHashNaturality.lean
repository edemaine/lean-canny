/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.SquareSampleRankNaturality
/-! # Deterministic hash choices preserve exact parameter data -/
@[expose] public section
namespace LeanCanny.Encoding.SquareSampleHashNaturality
open LeanCanny.Algebra LeanCanny.Computation SquareSampleInput SquareSampleRankNaturality
open scoped Classical
attribute [local irreducible] SquareSampleRecords.length SquareSampleThom.labelWidth
  SquareSampleCoordinates.parameterDegree SquareSampleCoordinates.baseHeight SquareSampleCoordinates.parameter
  SquareSampleQueries.roots SquareSampleRegularCount.count

def rootEquiv (P Q : Inputs) (c d : List Bool)
    (hR : SquareSampleQueries.roots P c=SquareSampleQueries.roots Q d) :
    SquareSampleRecordSpan.Root P c≃SquareSampleRecordSpan.Root Q d where
  toFun x:=⟨x.val,by rw [←hR];exact x.property⟩
  invFun x:=⟨x.val,by rw [hR];exact x.property⟩
  left_inv _:=rfl
  right_inv _:=rfl

theorem integerValue_injective_iff (P Q : Inputs) (c d : List Bool)
    (hD : SquareSampleCoordinates.parameterDegree P c=SquareSampleCoordinates.parameterDegree Q d)
    (hp : SquareSampleCoordinates.parameter P c=SquareSampleCoordinates.parameter Q d)
    (hR : SquareSampleQueries.roots P c=SquareSampleQueries.roots Q d) (p t : ℕ) :
    Function.Injective (SquareSampleRootHash.integerValue P c p t)↔
      Function.Injective (SquareSampleRootHash.integerValue Q d p t) :=by
  let e:=rootEquiv P Q c d hR
  constructor
  · intro HI x y H
    have HE:=HI ((integerValue_congr P Q c d hD hp hR p t (e.symm x) x rfl).trans
      (H.trans (integerValue_congr P Q c d hD hp hR p t (e.symm y) y rfl).symm))
    exact congrArg e HE
  · intro HI x y H
    have HE:=HI ((integerValue_congr P Q c d hD hp hR p t x (e x) rfl).symm.trans
      (H.trans (integerValue_congr P Q c d hD hp hR p t y (e y) rfl)))
    exact e.injective HE

theorem index_congr (P Q : Inputs) (c d : List Bool)
    (hD : SquareSampleCoordinates.parameterDegree P c=SquareSampleCoordinates.parameterDegree Q d)
    (hp : SquareSampleCoordinates.parameter P c=SquareSampleCoordinates.parameter Q d)
    (hR : SquareSampleQueries.roots P c=SquareSampleQueries.roots Q d) :
    SquareSampleHashChoice.index P (pair c (BinaryNatCode.encode (SquareSampleRegularCount.count P c)))=
      SquareSampleHashChoice.index Q (pair d (BinaryNatCode.encode (SquareSampleRegularCount.count Q d))) :=by
  have HB : SquareSampleHashChoice.bound P (pair c (BinaryNatCode.encode (SquareSampleRegularCount.count P c)))=
      SquareSampleHashChoice.bound Q (pair d (BinaryNatCode.encode (SquareSampleRegularCount.count Q d))):=by
    simp only [SquareSampleHashChoice.bound,SquareSampleHashChoice.width,SquareSampleRootHash.bitWidth,
      SquareSampleThom.labelWidth,SquareSampleParameters.labelWidth,pairFst_pair,hD]
  unfold SquareSampleHashChoice.index
  rw [HB]
  congr 1
  apply BoundedChoice.search_congr
  intro k _hk
  let u:=pair c (BinaryNatCode.encode (SquareSampleRegularCount.count P c))
  let v:=pair d (BinaryNatCode.encode (SquareSampleRegularCount.count Q d))
  have HM : SquareSampleHashChoice.modulusWord P (pair u (BinaryNatCode.encode k))=
      SquareSampleHashChoice.modulusWord Q (pair v (BinaryNatCode.encode k)):=by
    simp only [SquareSampleHashChoice.modulusWord,SquareSampleHashChoice.word,SquareSampleHashChoice.width,
      SquareSampleRootHash.bitWidth,SquareSampleThom.labelWidth,SquareSampleParameters.labelWidth,
      u,v,pairFst_pair,pairSnd_pair,hD]
  have HT : SquareSampleHashChoice.parameterWord P (pair u (BinaryNatCode.encode k))=
      SquareSampleHashChoice.parameterWord Q (pair v (BinaryNatCode.encode k)):=by
    simp only [SquareSampleHashChoice.parameterWord,SquareSampleHashChoice.word,SquareSampleHashChoice.width,
      SquareSampleRootHash.bitWidth,SquareSampleThom.labelWidth,SquareSampleParameters.labelWidth,
      u,v,pairFst_pair,pairSnd_pair,hD]
  change SquareSampleHashChoice.candidate P (pair u (BinaryNatCode.encode k))∈SquareSamplePencilRootCount.language P↔
    SquareSampleHashChoice.candidate Q (pair v (BinaryNatCode.encode k))∈SquareSamplePencilRootCount.language Q
  rw [SquareSampleHashChoice.candidate_context,SquareSampleHashChoice.candidate_context]
  simp only [u,v,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  rw [SquareSamplePencilRootCount.language_packet,SquareSamplePencilRootCount.language_packet]
  simp only [u,v,BinaryNatCode.encode] at HM HT
  rw [HM,HT]
  exact integerValue_injective_iff P Q c d hD hp hR _ _

theorem hash_congr (P Q : Inputs) (c d : List Bool)
    (hD : SquareSampleCoordinates.parameterDegree P c=SquareSampleCoordinates.parameterDegree Q d)
    (hp : SquareSampleCoordinates.parameter P c=SquareSampleCoordinates.parameter Q d)
    (hR : SquareSampleQueries.roots P c=SquareSampleQueries.roots Q d)
    (x : SquareSampleRecordSpan.Root P c) (y : SquareSampleRecordSpan.Root Q d) (hxy : x.val=y.val) :
    SquareSampleHashChoice.hash P c x=SquareSampleHashChoice.hash Q d y :=by
  have HI:=index_congr P Q c d hD hp hR
  have HM : SquareSampleWeightedMoments.modulus (SquareSampleHashChoice.value P c)=
      SquareSampleWeightedMoments.modulus (SquareSampleHashChoice.value Q d):=by
    simp only [SquareSampleHashChoice.value,SquareSampleHashChoice.selected,SquareSampleHashChoice.prepare,
      SquareSampleHashChoice.candidate,SquareSampleWeightedMoments.modulus,pairFst_pair,pairSnd_pair]
    simp only [SquareSampleHashChoice.modulusWord,SquareSampleHashChoice.word,SquareSampleHashChoice.width,
      SquareSampleRootHash.bitWidth,SquareSampleThom.labelWidth,SquareSampleParameters.labelWidth,
      pairFst_pair,pairSnd_pair,HI,hD]
  have HT : SquareSampleWeightedMoments.parameter (SquareSampleHashChoice.value P c)=
      SquareSampleWeightedMoments.parameter (SquareSampleHashChoice.value Q d):=by
    simp only [SquareSampleHashChoice.value,SquareSampleHashChoice.selected,SquareSampleHashChoice.prepare,
      SquareSampleHashChoice.candidate,SquareSampleWeightedMoments.parameter,pairFst_pair,pairSnd_pair]
    simp only [SquareSampleHashChoice.parameterWord,SquareSampleHashChoice.word,SquareSampleHashChoice.width,
      SquareSampleRootHash.bitWidth,SquareSampleThom.labelWidth,SquareSampleParameters.labelWidth,
      pairFst_pair,pairSnd_pair,HI,hD]
  unfold SquareSampleHashChoice.hash
  rw [HM,HT]
  exact integerValue_congr P Q c d hD hp hR _ _ x y hxy

theorem values_congr (P Q : Inputs) (c d : List Bool)
    (hD : SquareSampleCoordinates.parameterDegree P c=SquareSampleCoordinates.parameterDegree Q d)
    (hp : SquareSampleCoordinates.parameter P c=SquareSampleCoordinates.parameter Q d)
    (hR : SquareSampleQueries.roots P c=SquareSampleQueries.roots Q d) :
    SquareSampleHashRoots.values P c=SquareSampleHashRoots.values Q d :=by
  ext z
  rw [SquareSampleHashRoots.mem_values,SquareSampleHashRoots.mem_values]
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨rootEquiv P Q c d hR x,(hash_congr P Q c d hD hp hR _ _ rfl).symm.trans hx⟩
  · rintro ⟨y,hy⟩
    exact ⟨(rootEquiv P Q c d hR).symm y,(hash_congr P Q c d hD hp hR _ _ rfl).trans hy⟩

end LeanCanny.Encoding.SquareSampleHashNaturality
