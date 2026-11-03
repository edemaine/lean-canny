/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.SquareSampleParameterNaturality
/-! # The selected sign basis depends on its literal parameter data -/
@[expose] public section
namespace LeanCanny.Encoding.SquareSampleRankNaturality
open LeanCanny.Algebra LeanCanny.Computation SquareSampleInput
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

private noncomputable def rowAt (slots width D : ℕ) (p : Polynomial ℤ) (r : List Bool) (x : ℝ) : ℚ:=
  SparseFeatureRecords.value (Nat.succ_pos D) slots width
    (fun i=>((ThomEncoding.signature (p.map (Int.castRingHom ℝ)) D x i):ℚ)) r

private noncomputable def gramAt (L slots width D : ℕ) (p : Polynomial ℤ) (R : Finset ℝ) (k : ℕ) :
    Matrix (Fin (2^L)) (Fin (2^L)) ℚ:=
  fun i j=>∑x∈R,
    (if i.val<k then rowAt slots width D p (ImplicitGraph.word L i.val) x else 0)*
    (if j.val<k then rowAt slots width D p (ImplicitGraph.word L j.val) x else 0)

private noncomputable def rankAt (L slots width D : ℕ) (p : Polynomial ℤ) (R : Finset ℝ) (k : ℕ) : ℕ:=
  (gramAt L slots width D p R k).rank

private theorem prefixRank_eq (P : Inputs) (c : List Bool) (k : ℕ) :
    SquareSamplePrefixRank.prefixRank P c k=rankAt (SquareSampleRecords.length P c)
      (SquareSampleRecords.slots P c) (SquareSampleRecords.width P c)
      (SquareSampleCoordinates.parameterDegree P c) (SquareSampleCoordinates.parameter P c)
      (SquareSampleQueries.roots P c) k :=by
  unfold SquareSamplePrefixRank.prefixRank rankAt
  congr 1
  ext i j
  simp only [Matrix.mul_apply,Matrix.transpose_apply,SquareSamplePrefixRank.prefixRows,
    SquareSampleRecordSpan.matrix,Matrix.of_apply,SquareSampleRecordSpan.row_apply,
    gramAt,rowAt,SquareSampleThom.signature]
  exact Finset.sum_coe_sort (SquareSampleQueries.roots P c) (fun theta=>
    (if i.val<k then rowAt (SquareSampleRecords.slots P c) (SquareSampleRecords.width P c)
      (SquareSampleCoordinates.parameterDegree P c) (SquareSampleCoordinates.parameter P c)
      (ImplicitGraph.word (SquareSampleRecords.length P c) i.val) theta else 0)*
    (if j.val<k then rowAt (SquareSampleRecords.slots P c) (SquareSampleRecords.width P c)
      (SquareSampleCoordinates.parameterDegree P c) (SquareSampleCoordinates.parameter P c)
      (ImplicitGraph.word (SquareSampleRecords.length P c) j.val) theta else 0))

theorem prefixRank_congr (P Q : Inputs) (c d : List Bool)
    (hD : SquareSampleCoordinates.parameterDegree P c=SquareSampleCoordinates.parameterDegree Q d)
    (hp : SquareSampleCoordinates.parameter P c=SquareSampleCoordinates.parameter Q d)
    (hR : SquareSampleQueries.roots P c=SquareSampleQueries.roots Q d) (k : ℕ) :
    SquareSamplePrefixRank.prefixRank P c k=SquareSamplePrefixRank.prefixRank Q d k :=by
  simp only [prefixRank_eq,SquareSampleRecords.length,SquareSampleRecords.slots,SquareSampleRecords.width,
    SquareSampleThom.labelWidth,SquareSampleParameters.labelWidth,hD,hp,hR]

theorem chosen_congr (P Q : Inputs) (c d : List Bool)
    (hD : SquareSampleCoordinates.parameterDegree P c=SquareSampleCoordinates.parameterDegree Q d)
    (hp : SquareSampleCoordinates.parameter P c=SquareSampleCoordinates.parameter Q d)
    (hR : SquareSampleQueries.roots P c=SquareSampleQueries.roots Q d) (r : ℕ) :
    SquareSampleRankBasis.chosen P c r=SquareSampleRankBasis.chosen Q d r :=by
  have HW : SquareSamplePrefixRank.dimension P (pair c (BinaryNatCode.encode r))=
      SquareSamplePrefixRank.dimension Q (pair d (BinaryNatCode.encode r)):=by
    simp only [SquareSamplePrefixRank.dimension,pairFst_pair,SquareSampleRecords.length,
      SquareSampleRecords.slots,SquareSampleRecords.width,SquareSampleThom.labelWidth,
      SquareSampleParameters.labelWidth,hD]
  unfold SquareSampleRankBasis.chosen SquareSampleRankChoice.index
  rw [HW]
  congr 1
  apply BoundedChoice.search_congr
  intro k _hk
  simp only [SquareSampleRankChoice.language,Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair,
    BinaryNatCode.encode,Nat.fromBitsLE_bits,prefixRank_congr P Q c d hD hp hR]

theorem count_congr (P Q : Inputs) (c d : List Bool)
    (hR : SquareSampleQueries.roots P c=SquareSampleQueries.roots Q d) :
    SquareSampleRegularCount.count P c=SquareSampleRegularCount.count Q d :=by
  rw [←SquareSampleQueries.roots_card,←SquareSampleQueries.roots_card,hR]

private noncomputable def integerSummand (D : ℕ) (p : Polynomial ℤ) (x : ℝ)
    (choose : ℕ→ℕ) (modulus parameter r : ℕ) : ℤ:=
  (SparseFeatureRecords.value (M:=SignType) (Nat.succ_pos D) (2*(D+1).size) (D.size+2)
    (ThomEncoding.signature (p.map (Int.castRingHom ℝ)) D x)
    (ImplicitGraph.word (2*(D+1).size*(D.size+2)) (choose r)) : ℤ)*(parameter^r%modulus : ℕ)

private noncomputable def integerAt (D : ℕ) (p : Polynomial ℤ) (x : ℝ)
    (choose : ℕ→ℕ) (count modulus parameter : ℕ) : ℤ:=
  ∑r∈Finset.range count,integerSummand D p x choose modulus parameter r

private theorem integerValue_eq (P : Inputs) (c : List Bool) (p t : ℕ)
    (x : SquareSampleRecordSpan.Root P c) :
    SquareSampleRootHash.integerValue P c p t x=integerAt (SquareSampleCoordinates.parameterDegree P c)
      (SquareSampleCoordinates.parameter P c) x.val (SquareSampleRankBasis.chosen P c)
      (SquareSampleRegularCount.count P c) p t :=by
  change (∑r : Fin (SquareSampleRegularCount.count P c),integerSummand
    (SquareSampleCoordinates.parameterDegree P c) (SquareSampleCoordinates.parameter P c) x.val
    (SquareSampleRankBasis.chosen P c) p t r.val)=_
  exact Fin.sum_univ_eq_sum_range (integerSummand (SquareSampleCoordinates.parameterDegree P c)
    (SquareSampleCoordinates.parameter P c) x.val (SquareSampleRankBasis.chosen P c) p t) _

theorem integerValue_congr (P Q : Inputs) (c d : List Bool)
    (hD : SquareSampleCoordinates.parameterDegree P c=SquareSampleCoordinates.parameterDegree Q d)
    (hp : SquareSampleCoordinates.parameter P c=SquareSampleCoordinates.parameter Q d)
    (hR : SquareSampleQueries.roots P c=SquareSampleQueries.roots Q d)
    (p t : ℕ) (x : SquareSampleRecordSpan.Root P c) (y : SquareSampleRecordSpan.Root Q d)
    (hxy : x.val=y.val) :
    SquareSampleRootHash.integerValue P c p t x=SquareSampleRootHash.integerValue Q d p t y :=by
  have hC:=count_congr P Q c d hR
  have hchoose : SquareSampleRankBasis.chosen P c=SquareSampleRankBasis.chosen Q d:=
    funext (chosen_congr P Q c d hD hp hR)
  rw [integerValue_eq,integerValue_eq,hD,hp,hC,hxy,hchoose]

end LeanCanny.Encoding.SquareSampleRankNaturality
