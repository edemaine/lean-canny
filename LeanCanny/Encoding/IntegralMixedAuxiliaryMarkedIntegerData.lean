/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerPlan
public import LeanCanny.Algebra.IntegralMixedSourceIntegerHeaders
public import LeanCanny.Algebra.BoundedRegularFramedOriginal
/-! # Exact total marked-prelude data and native original header provenance -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerPlan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedAuxiliaryMarkedIntegerSource (number original)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def data {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) (R : List Bool → ℕ) :=
  IntegralMixedSourceIntegerPrelude.data (parameters hn ht ha) (spatial n t R) (spatial_degree n t R)
    (IntegralMixedSourceIntegerPrelude.source_cap _ _ _ _)
    (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R) (fun c=>number n c+8)
    (IntegralMixedAuxiliaryMarkedIntegerSource.nonzero hn ht ha R) (source_degree_cap hn ht ha R)
    (fun context=>by change number n context+8+2≤number n context+8+2+1; omega)
    (fun context=>by change 0<number n context+3; omega) (fun _=>le_rfl)

noncomputable def tables {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) :=
  IntegralMixedSourceIntegerPrelude.tables (parameters hn ht ha) (fun c=>number n c+8)

theorem tables_native {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) :
    IntegralMixedHeaderTablesBits.Access (tables hn ht ha) :=
  IntegralMixedSourceIntegerPrelude.tables_native (parameters hn ht ha) (access hn ht ha)
    ((IntegralMixedAuxiliaryMarkedIntegerSource.number_unary hn).add (UnaryFn.const 8))

theorem tables_represents {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) (R : List Bool → ℕ) :
    IntegralMixedFramedHeaderBits.Represents (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R) (tables hn ht ha) :=
  IntegralMixedSourceIntegerPrelude.tables_represents _ _ _ _ _ _ _ _ _ _ _

theorem instruction_source {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (R : List Bool → ℕ) (key : List Bool) :
    (IntegralMixedFramedHistoryFamilyBits.instruction (parameters hn ht ha) (plan hn ht ha R) key).source=spatial n t R (pairFst key) :=
  IntegralMixedSourceIntegerPrelude.instruction_source _ _ _ _ _ _ _ _ _ key

noncomputable def savedReaders (n : List Bool → ℕ) (t : List Bool → Term) (R : List Bool → ℕ) :=
  (BoundedRegularLowCoefficient.readers (number n) (t∘original) R).comp pairFst

theorem savedReaders_native {n : List Bool → ℕ} {t : List Bool → Term} {R : List Bool → ℕ}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (hR : BinaryFn R) : (savedReaders n t R).PolyTime :=
  (BoundedRegularLowCoefficient.readers_native (IntegralMixedAuxiliaryMarkedIntegerSource.number_unary hn)
    (mem_FP_comp original_FP ht) hR).comp pairFst_mem_FP

theorem snapshot {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) (R : List Bool → ℕ) :
    BoundedRegularFramedOriginalBits.Snapshot (parameters hn ht ha) (plan hn ht ha R) (savedReaders n t R) where
  ambient _:=rfl
  source key:=by rw [instruction_source]; rfl

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerPlan
