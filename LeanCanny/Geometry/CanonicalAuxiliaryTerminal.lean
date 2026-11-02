/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.FrozenSliceInclusion
public import LeanCanny.Algebra.IntegralMixedDilationAdvance

/-! # Terminal original-coordinate recovery in the retained newest-first bank

After k original coordinate births, original coordinate i has raw bank index
k-1-i. Advancing the existing selector implements exactly this ordering. Once
all n coordinates are frozen, every point of the terminal slice is the tuple
recovered under the same interpreting hom, including its original denominators.
-/
@[expose] public section
namespace LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory IntegralMixedDilationAdvance
open FrozenAuxiliaryComponentSampling
open scoped Classical

def frontIndex (k i : ℕ) : ℕ := k-1-i

def frontSelector (k m : ℕ) : Fin k → Fin (m+k) := fun i =>
  ⟨frontIndex k i.val,by have H:=i.isLt; unfold frontIndex; omega⟩

theorem frontSelector_injective (k m : ℕ) : Function.Injective (frontSelector k m) := by
  intro i j h
  have H := congrArg Fin.val h
  have HI := i.isLt
  have HJ := j.isLt
  apply Fin.ext
  change k-1-i.val=k-1-j.val at H
  omega

theorem nextSelector_front (k m : ℕ) : nextSelector (frontSelector k m)=frontSelector (k+1) m := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [nextSelector_new]
    apply Fin.ext
    change 0=(k+1)-1-k
    omega
  · rw [nextSelector_old]
    apply Fin.ext
    change (k-1-j.val)+1=(k+1)-1-j.val
    have H := j.isLt
    omega

theorem frontIndex_binary {K I : List Bool → ℕ} (hK : BinaryFn K) (hI : BinaryFn I) :
    BinaryFn (fun q => frontIndex (K q) (I q)) := (hK.sub (BinaryFn.const 1)).sub hI

theorem terminal_values {n m : ℕ} {q : MvPolynomial (Fin n) ℝ} (a : Fin n → ℝ)
    (x : slice q n a) (values : Fin m → ℝ) (select : Fin n → Fin m)
    (Hparam : ∀ i, a i=values (select i)) : ∀ i, x.val i=values (select i) := by
  intro i
  rw [terminal_value a x]
  exact Hparam i

theorem terminal_quotients {n p S B m : ℕ} {P : SpatialSource p} {ι : Type}
    {q : MvPolynomial (Fin n) ℝ} (a : Fin n → ℝ) (x : slice q n a)
    (bank : State P S B m ι) (φ : bank.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (values : Fin m → ℝ) (H : ∀ i, φ (bank.bank.numerator i)/(bank.bank.denominator i:ℝ)=values i)
    (select : Fin n → Fin m) (Hparam : ∀ i, a i=values (select i)) :
    ∀ i, x.val i=φ (bank.bank.numerator (select i))/(bank.bank.denominator (select i):ℝ) := by
  intro i
  exact (terminal_values a x values select Hparam i).trans (H (select i)).symm

end LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
