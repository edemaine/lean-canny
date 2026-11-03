/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerData
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerHeight
public import LeanCanny.Algebra.IntegralMixedSourceIntegerCurrentQControls
/-! # Original n/t/R supplies every marked-prelude current-Q control -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerPlan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryMarkedIntegerSource (number original)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def controls {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool → ℕ} (hR : BinaryFn R) :
    IntegralMixedFramedCurrentQNativeBits.Controls (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R) :=
  IntegralMixedSourceIntegerPrelude.currentQControls (parameters hn ht ha) (access hn ht ha)
    (spatial n t R) (spatial_degree n t R) (IntegralMixedSourceIntegerPrelude.source_cap _ _ _ _)
    (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R) (IntegralMixedAuxiliaryMarkedIntegerSource.access hn ht ha hR)
    (fun c=>number n c+8) ((IntegralMixedAuxiliaryMarkedIntegerSource.number_unary hn).add (UnaryFn.const 8))
    (IntegralMixedAuxiliaryMarkedIntegerSource.nonzero hn ht ha R) (source_degree_cap hn ht ha R)
    (fun context=>by change number n context+8+2≤number n context+8+2+1; omega)
    (fun context=>by change 0<number n context+3; omega) (fun _=>le_rfl)
    (savedReaders n t R) (savedReaders_native hn ht hR)
    (fun key=>by
      simpa only [savedReaders,BoundedFullWriter.Readers.comp,BoundedRegularLowCoefficient.readers,
        Function.comp_apply,TermView.term_toBits,number] using ha (original (pairFst key)))
    (snapshot hn ht ha R) (fun _=>1) (fun _=>1) (seed hn ht ha hR)
    (BinaryFn.const 1) (BinaryFn.const 1) (seed_binary hn ht ha hR)

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerPlan
