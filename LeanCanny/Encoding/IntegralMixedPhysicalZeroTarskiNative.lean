/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedZeroTarskiStatisticSpace
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedNative
public import LeanCanny.Encoding.IntegralMixedPhysicalTraceCutTest
public import LeanCanny.Encoding.OrderedWindowStatisticFP
/-! # Original-only constant-head epsilon-window statistics

Each statistic uses the same marked or signed-outer context and full word.
The five-statistic recognizer checks the exact integer window inequalities.
Its geometric rank interpretation requires the separate same-tuple model.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalZeroTarski
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedPhysicalMarkedPlan (bank native tables tables_native represents)
open IntegralMixedPhysicalTraceCutTest (factor_positive fallback probeControls probeBounds)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] bank native tables IntegralMixedPhysicalMarkedPlan.controls
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)
  (parent : List Bool→List Bool) (selected : List Bool→ℕ)

noncomputable def value (power : Fin 3) (negative : Bool) (z : List Bool) : ℤ :=
  let B:=bank hn ht ha hR outer
  IntegralFramedZeroTarskiStatistic.value B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds
    parent B.key selected B.positive (factor_positive hn ht ha hR outer) (fallback hn ht ha hR outer)
    power negative (pair z [])

theorem evaluator (hp : parent∈FP) (hj : BinaryFn selected) (power : Fin 3) (negative : Bool) :
    SpaceFunction (fun z=>SignStatisticBits.integerCode (value hn ht ha hR outer parent selected power negative z)) :=by
  let B:=bank hn ht ha hR outer
  let A:=native hn ht ha hR outer
  let I:=IntegralMixedFramedCriticalBits.virtualInput B.parameters A.parameters B.plan B.data
    (IntegralMixedPhysicalMarkedPlan.controls hn ht ha hR outer).critical
  have E:=IntegralFramedZeroTarskiStatistic.evaluator B.parameters B.plan B.data
    B.nodes B.factor B.seed B.bounds parent B.key selected B.positive A.parameters A.nodes A.factor A.seed I
    (probeControls hn ht ha hR outer) (probeBounds hn ht ha hR outer)
    A.liftedData A.controls A.bounds (tables hn ht ha hR outer) (tables_native hn ht ha hR outer)
    (represents hn ht ha hR outer) hp A.key hj (IntegralMixedPhysicalMarkedNative.access hn ht ha hR outer)
    (factor_positive hn ht ha hR outer) (fallback hn ht ha hR outer) power negative
  exact E.precompose (fun z=>pair z []) (mem_FP_pair id_mem_FP (constFn_mem_FP []))

noncomputable def packet (code : List Bool→ℕ) (z : List Bool) :=
  OrderedWindowStatisticBits.pack (BinaryNatCode.encode (code (pairFst z)))
    (SignStatisticBits.integerCode (value hn ht ha hR outer parent selected 0 false z))
    (SignStatisticBits.integerCode (value hn ht ha hR outer parent selected 2 false z))
    (SignStatisticBits.integerCode (value hn ht ha hR outer parent selected 1 false z))
    (SignStatisticBits.integerCode (value hn ht ha hR outer parent selected 2 true z))
    (SignStatisticBits.integerCode (value hn ht ha hR outer parent selected 1 true z))

theorem packet_evaluator (hp : parent∈FP) (hj : BinaryFn selected) (code : List Bool→ℕ) (hc : BinaryFn code) :
    SpaceFunction (packet hn ht ha hR outer parent selected code) :=by
  have EC : SpaceFunction (fun z=>BinaryNatCode.encode (code (pairFst z))) :=
    ⟨Turing.MultiTapeTM.ComputableTidilyInPolySpace.of_polyTime (FP.computable (mem_FP_comp pairFst_mem_FP hc.bits_mem_FP))⟩
  exact EC.pairOutputs ((evaluator hn ht ha hR outer parent selected hp hj 0 false).pairOutputs
    ((evaluator hn ht ha hR outer parent selected hp hj 2 false).pairOutputs
      ((evaluator hn ht ha hR outer parent selected hp hj 1 false).pairOutputs
        ((evaluator hn ht ha hR outer parent selected hp hj 2 true).pairOutputs
          (evaluator hn ht ha hR outer parent selected hp hj 1 true)))))

noncomputable def language (code : List Bool→ℕ) : Language :=
  {z|OrderedWindowStatisticBits.Accept (packet hn ht ha hR outer parent selected code z)}

theorem decider (hp : parent∈FP) (hj : BinaryFn selected) (code : List Bool→ℕ) (hc : BinaryFn code) :
    SpaceDecider (language hn ht ha hR outer parent selected code) :=
  (packet_evaluator hn ht ha hR outer parent selected hp hj code hc).decider
    (fun z=>decide (OrderedWindowStatisticBits.Accept z)) OrderedWindowStatisticBits.accept_fppred.flag_mem_FP
    (fun _=>by simp only [language,Set.mem_ofPred_eq,decide_eq_true_eq])

theorem packet_iff (code : List Bool→ℕ) (z : List Bool) :
    z∈language hn ht ha hR outer parent selected code↔
      2*value hn ht ha hR outer parent selected 0 false z≤2*(code (pairFst z):ℤ)+
        value hn ht ha hR outer parent selected 2 false z+value hn ht ha hR outer parent selected 1 false z ∧
      2*(code (pairFst z):ℤ)<value hn ht ha hR outer parent selected 2 true z-
        value hn ht ha hR outer parent selected 1 true z :=
  OrderedWindowStatisticBits.packet _ _ _ _ _ _
end LeanCanny.Encoding.IntegralMixedPhysicalZeroTarski
