/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCompanionQueryValue
public import LeanCanny.Algebra.IntegralMixedFramedNativeSpace
/-! # Native creating-companion readback at representable moduli

The guard states the two restrictions of a fixed task layout: an active birth
and a modulus within its numeric cap. Both are native original-packet tests.
The arithmetic evaluator comes from the complete changing-source controller.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCompanionQueryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical

def Representable (P : Parameters) (q : List Bool) : Prop :=
  sourceBirth P q<P.cap (root q) ∧ callerModulus q≤numericCap P (root q)

theorem representable_FP (P : Parameters) (a : Access P) : FPPred (Representable P) :=
  (((BinaryFn.ofUnary (sourceBirth_unary P a)).lt ((BinaryFn.ofUnary a.cap).comp root_FP)).and
    (callerModulus_binary.le ((numericCap_binary P a).comp root_FP)))

noncomputable def guardedValue (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (q : List Bool) : List Bool :=
  if Representable P q then PaddedIntegralGeneratorSource.value (IntegralMixedFramedCompanionBits.source P D H) q else []

noncomputable def finish (P : Parameters) (z : List Bool) : List Bool :=
  if Representable P (pairFst z) then pairSnd z else []

theorem finish_FP (P : Parameters) (a : Access P) : finish P∈FP :=
  ((representable_FP P a).comp pairFst_mem_FP).ite_mem_FP pairSnd_mem_FP (constFn_mem_FP [])

theorem guarded_evaluator (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : IntegralMixedFramedNativeBits.Controls P D H)
    (E : SpaceFunction (IntegralMixedFramedNativeBits.machine P a D H h).model) :
    SpaceFunction (guardedValue P D H) := by
  have HE := E.call (query P D) (finish P)
    (query_FP P a D H h.producer.tables h.producer.native h.producer.represents) (finish_FP P a)
  exact HE.congr (funext fun q => by
    simp only [finish,pairFst_pair,pairSnd_pair,guardedValue]
    split_ifs with hg
    · exact model_query_value P a D H h q hg.1 hg.2
    · rfl)

theorem evaluator (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : IntegralMixedFramedNativeBits.Controls P D H)
    (hb : IntegralMixedFramedNativeBits.Bounds P D H h) : SpaceFunction (guardedValue P D H) :=
  guarded_evaluator P a D H h (IntegralMixedFramedNativeBits.model_space P a D H h hb)

theorem guarded_value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (q : List Bool) (hq : Representable P q) :
    guardedValue P D H q=PaddedIntegralGeneratorSource.value (IntegralMixedFramedCompanionBits.source P D H) q :=
  ite_eq_left hq

end LeanCanny.Algebra.IntegralMixedFramedCompanionQueryBits
