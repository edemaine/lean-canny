/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedHistoryContinuation
public import LeanCanny.Algebra.IntegralMixedRelativeCuts
public import LeanCanny.Algebra.IntegralMixedNilpotentScalar

/-! # Actual retained numerators are the prefix generators

The initial integer bank and every supported mixed extension preserve the
literal generator invariant. This includes normalized relative cuts and
the formal nilpotent constructor. Old-height matrix leaves therefore
request actual retained generators, without a new numerator oracle.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHistory
open IntegralHistorySampler UniformIntegralPrefix IntegralMixedHistoryScript
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

def Canonical (x : State P S B m ι) : Prop :=
  ∀ i, x.bank.numerator i = x.sampler.scalarPrefix.basis.generator i

theorem base_canonical (F : Sampler S (2 ^ B) 0 ι)
    (h : PurePowerReductionBounds.dimension (n + 1) P.degree ≤ 2 ^ B) : Canonical (base P F h) :=
  fun i => Fin.elim0 i

variable [Fintype ι]

theorem integerStep_canonical (x : State P S B m ι) (H : Canonical x) (hm : m ≤ S)
    (p : Polynomial ℤ) (hp : p ≠ 0) (hd : p.natDegree ≤ 2 ^ B) :
    Canonical (integerStep x hm p hp hd) :=
  x.bank.rootStep_generators hm _ _ _ H

theorem criticalStep_canonical (x : State P S B m ι) (H : Canonical x) (hm : m ≤ S) (r : CriticalRule n) :
    Canonical (criticalStep x hm r) :=
  x.bank.rootStep_generators hm _ _ _ H

theorem normalizedScalarStep_canonical (x : State P S B m ι) (H : Canonical x) (hm : m ≤ S)
    (p : Polynomial x.sampler.scalarPrefix.carrier) (d : ℕ) :
    Canonical (normalizedScalarStep x hm p d) :=
  x.bank.rootStep_generators hm _ _ _ H

theorem cutStep_canonical (x : State P S B m ι) (H : Canonical x) (hm : m ≤ S)
    (r : IntegralMixedCriticalSweep.Rule n) (c : IntegralMixedRelativeCuts.Kind P r) (d : ℕ) :
    Canonical (IntegralMixedRelativeCuts.step x hm r c d) :=
  normalizedScalarStep_canonical x H hm _ d

theorem nilpotentStep_canonical (x : State P S B m ι) (H : Canonical x) (hm : m ≤ S) :
    Canonical (nilpotentStep x hm) :=
  x.bank.rootStep_generators hm _ _ _ H

theorem commandStep_canonical (x : State P S B m ι) (H : Canonical x) (hm : m ≤ S)
    (c : Command n B) : Canonical (IntegralMixedHistoryScript.step x hm c) := by
  cases c with
  | integer p hp hd => exact integerStep_canonical x H hm p hp hd
  | critical r => exact criticalStep_canonical x H hm r

theorem continueRun_canonical (x : State P S B m ι) (H : Canonical x)
    (cs : List (Command n B)) (hcs : m + cs.length ≤ S + 1) : Canonical (continueRun x cs hcs) := by
  induction cs with
  | nil => exact H
  | cons c cs ih => exact commandStep_canonical _ (ih (by simp only [List.length_cons] at hcs; omega)) _ c

theorem integerBank_canonical (F : Sampler S (2 ^ B) 0 ι) :
    ∀ (m : ℕ) (p : Fin m → Polynomial ℤ) (hp : ∀ i, p i ≠ 0) (hm : m ≤ S + 1),
      ∀ i, (IntegralIntegerRootBank.run F m p hp hm).bank.numerator i =
        (IntegralIntegerRootBank.run F m p hp hm).sampler.scalarPrefix.basis.generator i := by
  intro m
  induction m with
  | zero => intro p hp hm i; exact Fin.elim0 i
  | succ m ih =>
    intro p hp hm i
    exact (IntegralIntegerRootBank.run F m (fun j => p j.succ) (fun j => hp j.succ) (by omega)).bank.rootStep_generators
      (by omega) _ _ _ (ih (fun j => p j.succ) (fun j => hp j.succ) (by omega)) i

theorem retainedIntegerBank_canonical (F : Sampler S (2 ^ B) 0 ι)
    (m : ℕ) (p : Fin m → Polynomial ℤ) (hp : ∀ i, p i ≠ 0) (hm : m ≤ S + 1)
    (hcap : PurePowerReductionBounds.dimension (n + 1) P.degree ≤ 2 ^ B) :
    Canonical (retainIntegerBank (P := P) (IntegralIntegerRootBank.run F m p hp hm) hcap) :=
  integerBank_canonical F m p hp hm

end LeanCanny.Algebra.IntegralMixedHistory
