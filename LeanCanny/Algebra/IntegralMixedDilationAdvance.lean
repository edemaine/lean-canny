/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FermatLevelLift
public import LeanCanny.Algebra.IntegralMixedSourceReframe
public import LeanCanny.Algebra.IntegralMixedCanonicalDilationRoot
/-! # Changing the frozen original-coordinate count over a correlated bank

The new source recomputes the partial homogenization at k+1. It has the same
original Fermat degree and reuses the entire retained sampler and hom. The
level coefficient can change to accommodate newly frozen coordinate heights. The
newly retained scalar is an original x coordinate, so it becomes an unscaled
parameter of the new source. It is not substituted as a constant old Y value.
This is a changing-source continuation, not a single immutable-source script.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedDilationAdvance
open IntegralMixedHistory IntegralMixedCriticalSweep
open scoped Classical
variable {n k D S B m : ℕ} {u : Fin n} {t : ETR.Term} {ht : t.degreeBound ≤ D} {A : ℤ} {ι : Type}

noncomputable def advance
    (x : State (FermatLevelLift.source (FixedLeadingTiltedSource.source k D u t ht) A) S B m ι)
    (nextObjective : Fin n) (nextLevelCoefficient : ℤ) :
    State (FermatLevelLift.source (FixedLeadingTiltedSource.source (k+1) D nextObjective t ht) nextLevelCoefficient) S B m ι :=
  reframeDegree x _ rfl

theorem advance_sampler
    (x : State (FermatLevelLift.source (FixedLeadingTiltedSource.source k D u t ht) A) S B m ι)
    (nextObjective : Fin n) (nextLevelCoefficient : ℤ) : (advance x nextObjective nextLevelCoefficient).sampler=x.sampler := rfl

theorem advance_bank
    (x : State (FermatLevelLift.source (FixedLeadingTiltedSource.source k D u t ht) A) S B m ι)
    (nextObjective : Fin n) (nextLevelCoefficient : ℤ) : (advance x nextObjective nextLevelCoefficient).bank=x.bank := rfl

def nextSelector (select : Fin k → Fin m) : Fin (k+1) → Fin (m+1) :=
  Fin.snoc (fun j => (select j).succ) 0

theorem nextSelector_old (select : Fin k → Fin m) (j : Fin k) :
    nextSelector select j.castSucc=(select j).succ := Fin.snoc_castSucc _ _ _

theorem nextSelector_new (select : Fin k → Fin m) : nextSelector select (Fin.last k)=0 :=
  Fin.snoc_last _ _

theorem next_parameters (hkn : k<n) (select : Fin k → Fin m) (values : Fin m → ℝ)
    (a : ℝ) (old : Fin n → ℝ)
    (Hparam : ∀ i : Fin n, ∀ hi : i.val<k, old i=values (select ⟨i.val,hi⟩))
    (Ha : old ⟨k,hkn⟩=a) :
    ∀ i : Fin n, ∀ hi : i.val<k+1,
      old i=(Fin.cons a values : Fin (m+1) → ℝ) (nextSelector select ⟨i.val,hi⟩) := by
  intro i hi
  by_cases h : i.val<k
  · have HE : (⟨i.val,hi⟩:Fin (k+1))=(⟨i.val,h⟩:Fin k).castSucc := Fin.ext rfl
    rw [HE,nextSelector_old,Fin.cons_succ]
    exact Hparam i h
  · have HE : (⟨i.val,hi⟩:Fin (k+1))=Fin.last k := Fin.ext (by simp only [Fin.val_last]; omega)
    have HI : i=(⟨k,hkn⟩:Fin n) := by
      apply Fin.ext
      change i.val=k
      omega
    rw [HE,nextSelector_new,Fin.cons_zero,HI,Ha]

theorem advanced_parameter
    (x : State (FermatLevelLift.source (FixedLeadingTiltedSource.source k D u t ht) A) S B (m+1) ι)
    (nextObjective : Fin n) (nextLevelCoefficient : ℤ) (hkn : k<n)
    (select : Fin k → Fin m) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (values : Fin m → ℝ) (a : ℝ)
    (H : ∀ i, φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=(Fin.cons a values : Fin (m+1) → ℝ) i) (eta : ℝ) :
    heightValue (advance x nextObjective nextLevelCoefficient)
      (IntegralMixedCanonicalDilation.rule (by omega : k+1≤n) (nextSelector select)) φ eta
      (⟨k,hkn⟩:Fin n).succ.castSucc=(commonDenominator x:ℝ)*a := by
  have HE := IntegralMixedCanonicalDilation.value_parameter (advance x nextObjective nextLevelCoefficient)
    (by omega : k+1≤n) (nextSelector select) φ (Fin.cons a values : Fin (m+1) → ℝ) H eta
    (⟨k,hkn⟩:Fin n) (by exact Nat.lt_succ_self k)
  have HL : (⟨k,Nat.lt_succ_self k⟩:Fin (k+1))=Fin.last k := Fin.ext rfl
  rw [HL,nextSelector_new,Fin.cons_zero] at HE
  exact HE

theorem advanced_frozen
    (x : State (FermatLevelLift.source (FixedLeadingTiltedSource.source k D u t ht) A) S B (m+1) ι)
    (nextObjective : Fin n) (nextLevelCoefficient : ℤ) (hm : m+1 ≤ S) (hkn : k<n)
    (select : Fin k → Fin m) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (values : Fin m → ℝ) (a : ℝ)
    (H : ∀ i, φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=(Fin.cons a values : Fin (m+1) → ℝ) i)
    (eta : ℝ) (old : Fin n → ℝ) (v : ℝ)
    (Hparam : ∀ i : Fin n, ∀ hi : i.val<k, old i=values (select ⟨i.val,hi⟩))
    (Ha : old ⟨k,hkn⟩=a) :
    ∀ i, i.val<(IntegralMixedCanonicalDilation.rule (by omega : k+1≤n) (nextSelector select)).critical.offset.val →
      ((data (advance x nextObjective nextLevelCoefficient) hm (IntegralMixedCanonicalDilation.rule (by omega : k+1≤n)
        (nextSelector select)).critical).scales i:ℝ)*
        IntegralMixedCanonicalDilation.point (k:=k+1) (advance x nextObjective nextLevelCoefficient) eta old v i =
      heightValue (advance x nextObjective nextLevelCoefficient) (IntegralMixedCanonicalDilation.rule (by omega : k+1≤n)
        (nextSelector select)) φ eta i :=
  IntegralMixedCanonicalDilation.frozen (advance x nextObjective nextLevelCoefficient) hm (by omega) (nextSelector select) φ
    (Fin.cons a values : Fin (m+1) → ℝ) H eta old v (next_parameters hkn select values a old Hparam Ha)

end LeanCanny.Algebra.IntegralMixedDilationAdvance
