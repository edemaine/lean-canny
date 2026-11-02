/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryParametricSlackSources
public import LeanCanny.Algebra.IntegerPolynomialSourceChoice
public import LeanCanny.Algebra.IntegerPolynomialZeroRootSource
public import LeanCanny.Algebra.PowerIntegerPolynomialSpace
/-! # A radius-parametric original integer bank for a marked candidate

The context pairs the old candidate packet with original outer metadata.
A source query pairs that context with a chronological bank index. The bank
contains old coordinates, u,0,v,0,r,lambda,beta,kappa in that order. The old
saved algebra retains the entire context only in its auxiliary tail.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryPreparedRoot (dimension term dimension_unary term_FP)
open IntegralMixedAuxiliarySlackMatrix (count charge degree)
open IntegralMixedAuxiliaryParametricSlackSource (regularizationAt penaltyAt)
open IntegerPolynomialSourceChoice
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def candidate (context : List Bool) := pairFst context
def original (context : List Bool) := pairFst (candidate context)
def number (n : List Bool → ℕ) (context : List Bool) := n (original context)
def tag (q : List Bool) := Nat.fromBitsLE (pairSnd q)
def tail (key : List Bool) := pairSnd (pairSnd key)

noncomputable def oldKey (n : List Bool → ℕ) (t : List Bool → Term) (context : List Bool) :=
  IntegralMixedFramedHistoryFamilyBits.keyAt
    (IntegralMixedAuxiliaryCandidate.source n t (candidate context)) (number n context+1) context

theorem number_unary {n : List Bool → ℕ} (hn : UnaryFn n) : UnaryFn (number n) :=
  hn.comp (mem_FP_comp (f:=pairFst) (g:=pairFst) pairFst_mem_FP pairFst_mem_FP)
theorem tail_FP : tail∈FP := mem_FP_comp (f:=pairSnd) (g:=pairSnd) pairSnd_mem_FP pairSnd_mem_FP

theorem oldKey_FP {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) : oldKey n t∈FP :=
  mem_FP_pair (mem_FP_comp (f:=candidate) (g:=IntegralMixedAuxiliaryCandidate.source n t)
    pairFst_mem_FP (IntegralMixedAuxiliaryCandidate.source_FP hn ht))
    (mem_FP_pair (BinaryFn.ofUnary ((number_unary hn).add (UnaryFn.const 1))).bits_mem_FP id_mem_FP)

theorem oldKey_tail (n : List Bool → ℕ) (t : List Bool → Term) (context : List Bool) :
    tail (oldKey n t context)=context := by simp only [tail,oldKey,IntegralMixedFramedHistoryFamilyBits.keyAt,pairSnd_pair]

def coordinateQuery (n : List Bool → ℕ) (q : List Bool) :=
  pair (candidate (pairFst q)) (BinaryNatCode.encode (number n (pairFst q)-tag q))
theorem coordinateQuery_FP {n : List Bool → ℕ} (hn : UnaryFn n) : coordinateQuery n∈FP := by
  have HN : BinaryFn (fun q=>number n (pairFst q)) := (BinaryFn.ofUnary (number_unary hn)).comp pairFst_mem_FP
  exact mem_FP_pair (mem_FP_comp (f:=pairFst) (g:=pairFst) pairFst_mem_FP pairFst_mem_FP)
    (HN.sub (BinaryFn.fromBits pairSnd_mem_FP)).bits_mem_FP

def beta (n : List Bool → ℕ) (t : List Bool → Term) (R : List Bool → ℕ) (key : List Bool) :=
  LeanCanny.Geometry.BoundedZeroSource.perturbationExponent (count n key) (charge t key) (charge t key) (R key)
theorem beta_binary {n : List Bool → ℕ} {t : List Bool → Term} {R : List Bool → ℕ}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (hR : BinaryFn R) : BinaryFn (beta n t R) :=
  BoundedZeroControls.perturbationExponent_binary (IntegralMixedAuxiliarySlackMatrix.count_unary hn)
    (BinaryFn.ofUnary (IntegralMixedAuxiliarySlackMatrix.charge_unary ht))
    (BinaryFn.ofUnary (IntegralMixedAuxiliarySlackMatrix.charge_unary ht)) hR

noncomputable def source {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (R : List Bool → ℕ) : IntegerPolynomialRootQueriesBits.Source :=
  let saved := oldKey n t ∘ pairFst
  let radius := R ∘ tail
  let unitPower := fun e => PowerIntegerPolynomial.source (fun _=>False) e
  choose (fun q=>tag q<number n (pairFst q))
    (reindex (IntegralMixedAuxiliaryCandidateCoordinate.source hn ht ha) (coordinateQuery n))
  (choose (fun q=>tag q=number n (pairFst q))
    (reindex (IntegralMixedAuxiliaryParametricSlackSource.sphereSource hn ht ha radius) saved)
  (choose (fun q=>tag q=number n (pairFst q)+2)
    (reindex (IntegralMixedAuxiliaryParametricSlackSource.regularSource hn ht ha radius) saved)
  (choose (fun q=>tag q=number n (pairFst q)+4) (unitPower (R ∘ pairFst))
  (choose (fun q=>tag q=number n (pairFst q)+5) (unitPower (regularizationAt n t radius ∘ saved))
  (choose (fun q=>tag q=number n (pairFst q)+6) (unitPower (beta n t radius ∘ saved))
  (choose (fun q=>tag q=number n (pairFst q)+7) (unitPower (penaltyAt n t radius ∘ saved))
    IntegerPolynomialZeroRootSource.source))))))

theorem access {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    {R : List Bool → ℕ} (hR : BinaryFn R) : IntegerPolynomialRootQueriesBits.Access (source hn ht ha R) := by
  have HS : oldKey n t ∘ pairFst∈FP := mem_FP_comp (f:=pairFst) (g:=oldKey n t) pairFst_mem_FP (oldKey_FP hn ht)
  have HR : BinaryFn (R ∘ tail) := hR.comp tail_FP
  have HN : BinaryFn (fun q=>number n (pairFst q)) := (BinaryFn.ofUnary (number_unary hn)).comp pairFst_mem_FP
  have HI : BinaryFn tag := BinaryFn.fromBits pairSnd_mem_FP
  have HP : FPPred (fun _ : List Bool=>False) := FPPred.const False
  unfold source
  exact choose_access (HI.lt HN) _ _
    (reindex_access _ (IntegralMixedAuxiliaryCandidateCoordinate.native_access hn ht ha) (coordinateQuery_FP hn))
    (choose_access (HI.eq HN) _ _
      (reindex_access _ (IntegralMixedAuxiliaryParametricSlackSource.sphere_access hn ht ha HR) HS)
    (choose_access (HI.eq (HN.add (BinaryFn.const 2))) _ _
      (reindex_access _ (IntegralMixedAuxiliaryParametricSlackSource.regular_access hn ht ha HR) HS)
    (choose_access (HI.eq (HN.add (BinaryFn.const 4))) _ _ (PowerIntegerPolynomial.access HP (hR.comp pairFst_mem_FP))
    (choose_access (HI.eq (HN.add (BinaryFn.const 5))) _ _
      (PowerIntegerPolynomial.access HP ((IntegralMixedAuxiliaryParametricSlackSource.regularizationAt_binary hn ht HR).comp HS))
    (choose_access (HI.eq (HN.add (BinaryFn.const 6))) _ _ (PowerIntegerPolynomial.access HP ((beta_binary hn ht HR).comp HS))
    (choose_access (HI.eq (HN.add (BinaryFn.const 7))) _ _
      (PowerIntegerPolynomial.access HP ((IntegralMixedAuxiliaryParametricSlackSource.penaltyAt_binary hn ht HR).comp HS))
      IntegerPolynomialZeroRootSource.access))))))

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerSource
