/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryEmptyFamilyInputs
public import LeanCanny.Algebra.IntegralMixedFramedRowMassControls

/-! # Original-only row mass for the actual empty auxiliary family

Original dimension, term syntax and arity scope supply the source/script
bounds. Their actual framed runs consequently satisfy this native row-mass
ceiling; no row-mass, bank-height or coefficient-matrix oracle remains.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryEmptyPlan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedFramedStepHeight IntegralMixedAuxiliaryParameters IntegralMixedAuxiliarySchedule
open scoped Classical

noncomputable def rowMass (n : List Bool→ℕ) (t : List Bool→Term) : List Bool→ℕ :=
  familyRowMass (parameters n t) (fun _=>1) (factor n t) (seed n t)

theorem rowMass_binary {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun root=>(t root).toData.toBits)∈FP) : BinaryFn (rowMass n t) :=
  familyRowMass_binary (parameters n t) (IntegralMixedAuxiliaryParameters.access hn ht)
    (BinaryFn.const 1) (factor_binary hn ht) (seed_binary hn ht)

theorem row_mass {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun root=>(t root).toData.toBits)∈FP) (ha : ∀ root,(t root).arity≤n root)
    (key : List Bool)
    (i : Fin ((IntegralMixedFramedHistoryFamilyBits.family (parameters n t) (plan hn ht ha) (data hn ht ha)).birth key)) :
    MvMass.mass (((IntegralMixedFramedHistoryFamilyBits.family (parameters n t) (plan hn ht ha) (data hn ht ha)).state key).sampler.scalarPrefix.rows i)≤
      2^rowMass n t (pairFst key) :=
  family_row_mass (parameters n t) (plan hn ht ha) (data hn ht ha) (fun _=>1) (factor n t) (seed n t)
    (familyInputs hn ht ha) key i

end LeanCanny.Encoding.IntegralMixedAuxiliaryEmptyPlan
