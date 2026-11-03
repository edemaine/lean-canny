/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerData
public import LeanCanny.Algebra.BoundedRegularIntegerCurrentQOriginal
public import LeanCanny.Algebra.IntegralMixedSourceIntegerZeroRules
/-! # Concrete original syntax for rebuilding marked-prelude caller-modulus costs -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerPlan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryMarkedIntegerSource (number original)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def originalSyntax {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool → ℕ} (hR : BinaryFn R) :
    BoundedRegularIntegerCurrentQBits.Original (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R) where
  regular:=savedReaders n t R
  native:=savedReaders_native hn ht hR
  scope key:=by simpa only [savedReaders,BoundedFullWriter.Readers.comp,BoundedRegularLowCoefficient.readers,
    Function.comp_apply,TermView.term_toBits,number] using ha (original (pairFst key))
  snapshot:=snapshot hn ht ha R
  zero:=IntegralMixedSourceIntegerPrelude.zeroRules _ _ _ _ _ _ _ _ _ _ _
  integer:=IntegralMixedSourceIntegerPrelude.source (parameters hn ht ha)
    (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R) (fun c=>number n c+8)
  integer_native:=IntegralMixedSourceIntegerPrelude.native_access (parameters hn ht ha) (access hn ht ha)
    (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R) (IntegralMixedAuxiliaryMarkedIntegerSource.access hn ht ha hR)
    ((IntegralMixedAuxiliaryMarkedIntegerSource.number_unary hn).add (UnaryFn.const 8))
  query:=id
  query_FP:=id_mem_FP
  integer_eq:=IntegralMixedSourceIntegerPrelude.polynomial _ _ _ _ _ _ _ _ _

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerPlan
