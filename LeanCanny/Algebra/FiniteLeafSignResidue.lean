/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FiniteLeafSignSpace
public import LeanCanny.Algebra.FiniteLeafSignPrepared
public import LeanCanny.Algebra.FiniteSourceDegreePreparation

/-! # Finite algebraic sign feasibility from original residues alone

Compute a bounded table of original degrees in native space, then feed its
checked family to the finite-leaf sign procedure. Only original coefficient
residues and degree/mass upper bounds are required; exact degrees and every
intermediate rational-coordinate reader are constructed internally.
-/

@[expose] public section

namespace LeanCanny.Algebra.FiniteLeafSignBits
open Polynomial LeanCanny.Encoding LeanCanny.Computation
open SeparableBits (Family)
open scoped Classical

theorem reindexed_language_iff (F B : Family) (count : List Bool → ℕ) (S : Source count)
    (u c : List Bool) (hu : pairFst u = c)
    (hpoly : ∀ i, i < count c → F.polynomial (pair u (BinaryNatCode.encode i)) =
      B.polynomial (pair c (BinaryNatCode.encode i))) :
    u ∈ finiteSignLanguage F (count ∘ pairFst) (S.precompose pairFst) ↔
      c ∈ finiteSignLanguage B count S := by
  subst c
  simp only [finiteSignLanguage, Set.mem_ofPred_eq, Source.precompose, Source.polynomial, Function.comp_apply]
  apply exists_congr
  intro x
  apply and_congr
  · apply forall_congr'
    intro i
    rw [hpoly i.val i.isLt]
  · rfl

variable (B : Family) (count D b : List Bool → ℕ)
variable (hne : ∀ c i, i < count c → B.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0)
variable (hdegree : ∀ c i, i < count c → (B.polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ D c)
variable (hmass : ∀ c i, i < count c → coefficientMass (B.polynomial (pair c (BinaryNatCode.encode i))) ≤ 2 ^ b c)

include hdegree hmass in
theorem prepared_language_iff (S : Source count) (c : List Bool) :
    FiniteSourceDegreePreparation.prepare B count D c ∈
      finiteSignLanguage (FiniteSourceDegreePreparation.family B count D b hmass)
        (count ∘ pairFst) (S.precompose pairFst) ↔ c ∈ finiteSignLanguage B count S := by
  exact reindexed_language_iff _ B count S _ c (FiniteSourceDegreePreparation.prepare_source B count D c)
    (FiniteSourceDegreePreparation.prepared_polynomial B count D b hdegree hmass c)

include hne hdegree hmass in
theorem finiteSignLanguage_mem_PSPACE_from_residues (S : Source count) (A : S.Access)
    (hn : UnaryFn count) (hD : BinaryFn D) (hb : BinaryFn b)
    (E : SpaceFunction (PrimitivePairBits.coefficient B.polynomial)) :
    finiteSignLanguage B count S ∈ PSPACE := by
  let F := FiniteSourceDegreePreparation.family B count D b hmass
  have R := FiniteSourceDegreePreparation.readers B count D b hdegree hmass hn hD hb E
  have hz : ∀ c i, i < (count ∘ pairFst) c → F.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0 :=
    fun c i _ => FiniteSourceDegreePreparation.family_nonzero B count D b hmass hne _
  have hd : ∀ c i, i < (count ∘ pairFst) c →
      (F.polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤
        (FiniteSourceDegreePreparation.degreeBudget D ∘ pairFst) c :=
    fun c i _ => (FiniteSourceDegreePreparation.family_degree B count D b hmass c i).le
  have hh : ∀ c i, i < (count ∘ pairFst) c → F.height (pair c (BinaryNatCode.encode i)) ≤ (b ∘ pairFst) c := by
    intro c i _
    rw [FiniteSourceDegreePreparation.family_height, pairFst_pair]
    exact le_rfl
  have H := finiteSignLanguage_mem_PSPACE F (count ∘ pairFst)
    (FiniteSourceDegreePreparation.degreeBudget D ∘ pairFst) (b ∘ pairFst) hz hd hh
    (S.precompose pairFst) (A.precompose pairFst pairFst_mem_FP) R
    (hn.comp pairFst_mem_FP) ((FiniteSourceDegreePreparation.degreeBudget_binary hD).comp pairFst_mem_FP)
    (hb.comp pairFst_mem_FP)
  have P := FiniteSourceDegreePreparation.prepareEvaluator B count D b hdegree hmass hn hD hb E
  apply SpaceDecider.mem_PSPACE
  apply SpaceDecider.of_computable ((SpaceDecider.ofPSPACE H).computable.comp P.computable)
  intro c
  simp only [decide_eq_true_eq]
  exact (prepared_language_iff B count D b hdegree hmass S c).symm

end LeanCanny.Algebra.FiniteLeafSignBits
