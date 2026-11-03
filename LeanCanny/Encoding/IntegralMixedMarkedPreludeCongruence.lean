/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalOriginalSource
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedOldInterpretation
public import LeanCanny.Algebra.IntegralMixedFramedSlackSibling
/-! # Literal marked integer leaves survive outer record replacement

The old candidate packet stays fixed. The old source and birth stay fixed,
while the old saved auxiliary context changes honestly. The radius reads
only the original input. No complete sample words are transported.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedPreludeCongruence
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryMarkedIntegerSource (candidate original number oldKey tail)
open IntegralMixedOriginalRegularSource (radius)
open IntegralMixedAuxiliaryRecipeRoot (planAt dataAt)
open IntegralMixedAuxiliarySlackSource (syntaxInput inputs)
open IntegralMixedAuxiliarySlackMatrix (parameters count charge degree)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  (R0 : List Bool→ℕ) (cL cR : List Bool) (hc : candidate cL=candidate cR)

include hc in
theorem original_eq : original cL=original cR:=congrArg pairFst hc
include hc in
theorem number_eq : number n cL=number n cR:=congrArg n (original_eq cL cR hc)
include hc in
theorem radius_eq : radius R0 cL=radius R0 cR:=congrArg R0 (original_eq cL cR hc)

include hc in
theorem old_root : pairFst (oldKey n t cL)=pairFst (oldKey n t cR) :=by
  simp only [oldKey,IntegralMixedFramedHistoryFamilyBits.keyAt_root]
  exact congrArg (IntegralMixedAuxiliaryCandidate.source n t) hc
include hc in
theorem old_birth : IntegralMixedFramedHistoryFamilyBits.prefixLength (parameters n t) (oldKey n t cL)=
    IntegralMixedFramedHistoryFamilyBits.prefixLength (parameters n t) (oldKey n t cR) :=by
  rw [IntegralMixedAuxiliaryMarkedOldInterpretation.old_prefix,IntegralMixedAuxiliaryMarkedOldInterpretation.old_prefix,
    number_eq cL cR hc]
include hc in
theorem old_count : count n (oldKey n t cL)=count n (oldKey n t cR) :=by
  rw [IntegralMixedAuxiliaryMarkedOldInterpretation.count_at,IntegralMixedAuxiliaryMarkedOldInterpretation.count_at,
    number_eq cL cR hc]
include hc in
theorem old_charge : charge t (oldKey n t cL)=charge t (oldKey n t cR) :=by
  rw [IntegralMixedAuxiliaryMarkedOldInterpretation.charge_at,IntegralMixedAuxiliaryMarkedOldInterpretation.charge_at,
    original_eq cL cR hc]
include hc in
theorem old_radius : ((radius R0)∘tail) (oldKey n t cL)=((radius R0)∘tail) (oldKey n t cR) :=by
  simp only [Function.comp_apply,IntegralMixedAuxiliaryMarkedIntegerSource.oldKey_tail]
  exact radius_eq R0 cL cR hc

include hc in
theorem sphere_polynomial :
    (IntegralMixedAuxiliaryParametricSlackSource.sphereSource hn ht ha ((radius R0)∘tail)).polynomial (oldKey n t cL)=
      (IntegralMixedAuxiliaryParametricSlackSource.sphereSource hn ht ha ((radius R0)∘tail)).polynomial (oldKey n t cR) :=
  IntegralMixedFramedSlackSibling.sphere_polynomial (parameters n t) (planAt hn ht ha) (dataAt hn ht ha) _ _
    (old_root cL cR hc) (old_birth cL cR hc) (syntaxInput hn ht ha) (inputs hn ht ha) _ _
    (old_count cL cR hc) (old_radius R0 cL cR hc)

include hc in
theorem regularization_eq :
    IntegralMixedAuxiliaryParametricSlackSource.regularizationAt n t ((radius R0)∘tail) (oldKey n t cL)=
      IntegralMixedAuxiliaryParametricSlackSource.regularizationAt n t ((radius R0)∘tail) (oldKey n t cR) :=by
  unfold IntegralMixedAuxiliaryParametricSlackSource.regularizationAt
  rw [old_count cL cR hc,old_charge cL cR hc,old_radius R0 cL cR hc]
include hc in
theorem penalty_eq :
    IntegralMixedAuxiliaryParametricSlackSource.penaltyAt n t ((radius R0)∘tail) (oldKey n t cL)=
      IntegralMixedAuxiliaryParametricSlackSource.penaltyAt n t ((radius R0)∘tail) (oldKey n t cR) :=by
  unfold IntegralMixedAuxiliaryParametricSlackSource.penaltyAt
  rw [old_count cL cR hc,old_charge cL cR hc,old_radius R0 cL cR hc]
include hc in
theorem beta_eq :
    IntegralMixedAuxiliaryMarkedIntegerSource.beta n t ((radius R0)∘tail) (oldKey n t cL)=
      IntegralMixedAuxiliaryMarkedIntegerSource.beta n t ((radius R0)∘tail) (oldKey n t cR) :=by
  unfold IntegralMixedAuxiliaryMarkedIntegerSource.beta
  rw [old_count cL cR hc,old_charge cL cR hc,old_radius R0 cL cR hc]

include hc in
theorem regular_polynomial :
    (IntegralMixedAuxiliaryParametricSlackSource.regularSource hn ht ha ((radius R0)∘tail)).polynomial (oldKey n t cL)=
      (IntegralMixedAuxiliaryParametricSlackSource.regularSource hn ht ha ((radius R0)∘tail)).polynomial (oldKey n t cR) :=by
  apply IntegralMixedFramedSlackSibling.regular_polynomial (parameters n t) (planAt hn ht ha) (dataAt hn ht ha) _ _
    (old_root cL cR hc) (old_birth cL cR hc) (syntaxInput hn ht ha) (inputs hn ht ha)
  · exact old_count cL cR hc
  · exact congrArg LeanCanny.Geometry.BoundedZeroSource.powerDegree (old_charge cL cR hc)
  · exact old_radius R0 cL cR hc
  · exact regularization_eq R0 cL cR hc
  · exact penalty_eq R0 cL cR hc

include hc in
theorem coordinate_degree : IntegralMixedAuxiliaryMarkedIntegerSource.coordinateDegree hn ht ha cL=
    IntegralMixedAuxiliaryMarkedIntegerSource.coordinateDegree hn ht ha cR :=by
  unfold IntegralMixedAuxiliaryMarkedIntegerSource.coordinateDegree
  rw [hc]
include hc in
theorem sphere_degree : IntegralMixedAuxiliaryMarkedIntegerSource.sphereDegree hn ht ha cL=
    IntegralMixedAuxiliaryMarkedIntegerSource.sphereDegree hn ht ha cR :=by
  change IntegralMixedFramedClearedMatrixBits.rank (parameters n t) (planAt hn ht ha) (dataAt hn ht ha) (oldKey n t cL)*2=
    IntegralMixedFramedClearedMatrixBits.rank (parameters n t) (planAt hn ht ha) (dataAt hn ht ha) (oldKey n t cR)*2
  rw [IntegralMixedFramedSlackSibling.rank_eq _ _ _ _ _ (old_root cL cR hc) (old_birth cL cR hc)]
include hc in
theorem regular_degree : IntegralMixedAuxiliaryMarkedIntegerSource.regularDegree hn ht ha cL=
    IntegralMixedAuxiliaryMarkedIntegerSource.regularDegree hn ht ha cR :=by
  change IntegralMixedFramedClearedMatrixBits.rank (parameters n t) (planAt hn ht ha) (dataAt hn ht ha) (oldKey n t cL)*degree t (oldKey n t cL)=
    IntegralMixedFramedClearedMatrixBits.rank (parameters n t) (planAt hn ht ha) (dataAt hn ht ha) (oldKey n t cR)*degree t (oldKey n t cR)
  rw [IntegralMixedFramedSlackSibling.rank_eq _ _ _ _ _ (old_root cL cR hc) (old_birth cL cR hc)]
  unfold degree
  rw [old_charge cL cR hc]
include hc in
theorem degree_bound : IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound hn ht ha cL=
    IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound hn ht ha cR :=by
  unfold IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound
  rw [coordinate_degree hn ht ha cL cR hc,sphere_degree hn ht ha cL cR hc,regular_degree hn ht ha cL cR hc]

include hc in
theorem polynomial (i : ℕ) :
    (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha (radius R0)).polynomial (pair cL (BinaryNatCode.encode i))=
      (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha (radius R0)).polynomial (pair cR (BinaryNatCode.encode i)) :=by
  have HQ : IntegralMixedAuxiliaryMarkedIntegerSource.coordinateQuery n (pair cL (BinaryNatCode.encode i))=
      IntegralMixedAuxiliaryMarkedIntegerSource.coordinateQuery n (pair cR (BinaryNatCode.encode i)) :=by
    simp only [IntegralMixedAuxiliaryMarkedIntegerSource.coordinateQuery,pairFst_pair,pairSnd_pair,
      IntegralMixedAuxiliaryMarkedIntegerSource.tag,BinaryNatCode.encode,Nat.fromBitsLE_bits]
    rw [hc,number_eq cL cR hc]
  simp only [BinaryNatCode.encode] at HQ
  simp only [IntegralMixedAuxiliaryMarkedIntegerSource.source,IntegerPolynomialSourceChoice.choose,
    IntegerPolynomialSourceChoice.reindex,PowerIntegerPolynomial.source,IntegerPolynomialZeroRootSource.source,
    Function.comp_apply,pairFst_pair,IntegralMixedAuxiliaryMarkedIntegerSource.tag,pairSnd_pair,
    BinaryNatCode.encode,Nat.fromBitsLE_bits]
  rw [HQ,sphere_polynomial hn ht ha R0 cL cR hc,regular_polynomial hn ht ha R0 cL cR hc,
    regularization_eq R0 cL cR hc,penalty_eq R0 cL cR hc,beta_eq R0 cL cR hc,number_eq cL cR hc,
    radius_eq R0 cL cR hc]
end LeanCanny.Encoding.IntegralMixedMarkedPreludeCongruence
