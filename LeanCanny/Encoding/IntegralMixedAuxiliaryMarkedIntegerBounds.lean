/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerProperties
/-! # A radius-independent degree ceiling for every marked integer leaf -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegerPolynomialSourceChoice
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def coordinateDegree {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) (c : List Bool) :=
  (IntegralMixedAuxiliaryCandidateCoordinate.source hn ht ha).degree (pair (candidate c) [])
noncomputable def sphereDegree {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) (c : List Bool) :=
  (IntegralMixedAuxiliaryParametricSlackSource.sphereSource hn ht ha (fun _=>0)).degree (oldKey n t c)
noncomputable def regularDegree {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) (c : List Bool) :=
  (IntegralMixedAuxiliaryParametricSlackSource.regularSource hn ht ha (fun _=>0)).degree (oldKey n t c)
noncomputable def degreeBound {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) (c : List Bool) :=
  coordinateDegree hn ht ha c+sphereDegree hn ht ha c+regularDegree hn ht ha c+1

theorem degreeBound_binary {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) :
    BinaryFn (degreeBound hn ht ha) := by
  have HC : BinaryFn (coordinateDegree hn ht ha) :=
    (IntegralMixedAuxiliaryCandidateCoordinate.native_access hn ht ha).degree.comp
      (mem_FP_pair pairFst_mem_FP (constFn_mem_FP []))
  have HS : BinaryFn (sphereDegree hn ht ha) :=
    (IntegralMixedAuxiliaryParametricSlackSource.sphere_access hn ht ha (BinaryFn.const 0)).degree.comp (oldKey_FP hn ht)
  have HV : BinaryFn (regularDegree hn ht ha) :=
    (IntegralMixedAuxiliaryParametricSlackSource.regular_access hn ht ha (BinaryFn.const 0)).degree.comp (oldKey_FP hn ht)
  exact ((HC.add HS).add HV).add (BinaryFn.const 1)

private theorem coordinate_degree {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) (q : List Bool) :
    (IntegralMixedAuxiliaryCandidateCoordinate.source hn ht ha).degree (coordinateQuery n q)=coordinateDegree hn ht ha (pairFst q) := by
  simp only [coordinateDegree,coordinateQuery,IntegralMixedAuxiliaryCandidateCoordinate.source,
    IntegralMixedAuxiliaryCandidateCoordinate.requerySource,IntegralMixedAuxiliaryCandidateCoordinate.oldSource,
    IntegralMixedFramedCoordinateCharacteristicBits.rootSource,
    IntegralMixedFramedCoordinateCharacteristicBits.dimension,IntegralMixedFramedCoordinateCharacteristicBits.count,
    IntegralMixedFramedCoordinateCharacteristicBits.key,IntegralMixedAuxiliaryCandidateCoordinate.sourceContext,
    pairFst_pair]

private theorem sphere_degree {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool → ℕ) (q : List Bool) :
    (IntegralMixedAuxiliaryParametricSlackSource.sphereSource hn ht ha (R∘tail)).degree (oldKey n t q)=sphereDegree hn ht ha q := rfl
private theorem regular_degree {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool → ℕ) (q : List Bool) :
    (IntegralMixedAuxiliaryParametricSlackSource.regularSource hn ht ha (R∘tail)).degree (oldKey n t q)=regularDegree hn ht ha q := rfl

attribute [local irreducible] coordinateDegree sphereDegree regularDegree

theorem degree_le {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool → ℕ) (q : List Bool) : (source hn ht ha R).degree q≤degreeBound hn ht ha (pairFst q) := by
  simp only [source,choose,reindex,Function.comp_apply]
  rw [coordinate_degree,sphere_degree,regular_degree]
  unfold degreeBound
  split_ifs <;> first | omega | (change 1≤_; omega)

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerSource
