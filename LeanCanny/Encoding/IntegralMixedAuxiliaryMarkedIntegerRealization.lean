/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerPlan
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerVector
/-! # A correlated prescribed realization of the actual marked prelude

The root conditions refer to literal native sources. One joint tuple realizes
all old coordinates, marked slacks and power parameters simultaneously.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerPlan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryMarkedIntegerSource (number candidate oldKey tail values)
open IntegralMixedAuxiliaryParametricSlackSource (sphereSource regularSource)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem realizes_prescribed {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool → ℕ) (context : List Bool) (x : ℕ → ℝ) (u v : ℝ)
    (hx : ∀i<number n context,
      ((IntegralMixedAuxiliaryCandidateCoordinate.source hn ht ha).polynomial
        (pair (candidate context) (BinaryNatCode.encode (number n context-i)))).eval₂ (Int.castRingHom ℝ) (x i)=0)
    (hu : ((sphereSource hn ht ha (R∘tail)).polynomial (oldKey n t context)).eval₂ (Int.castRingHom ℝ) u=0)
    (hv : ((regularSource hn ht ha (R∘tail)).polynomial (oldKey n t context)).eval₂ (Int.castRingHom ℝ) v=0) :
    IntegralMixedIntegerRealization.Realizes
      (IntegralMixedFramedHistoryScript.run
        (IntegralMixedFramedHistoryFamilyBits.initial (parameters hn ht ha) (plan hn ht ha R) context)
        ((plan hn ht ha R).rules context) (by have H:=(plan hn ht ha R).room context; omega))
      (fun j=>values n t R context x u v (number n context+8-1-j)) := by
  let P:=parameters hn ht ha
  let D:=plan hn ht ha R
  let hq:=fun c=>(IntegralMixedFramedHistoryFamilyBits.initial P D c).critical_cap
  exact IntegralMixedSourceIntegerPrelude.realizes P (spatial n t R) hq
    (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R) (fun c=>number n c+8)
    (IntegralMixedAuxiliaryMarkedIntegerSource.nonzero hn ht ha R) (source_degree_cap hn ht ha R) context
    (IntegralMixedFramedHistoryFamilyBits.initial P D context) (fun i:Fin 0=>Fin.elim0 i)
    (fun i=>Fin.elim0 i) _ (values n t R context x u v)
    (fun i _=>IntegralMixedAuxiliaryMarkedIntegerSource.roots hn ht ha R context x u v hx hu hv i)

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerPlan
