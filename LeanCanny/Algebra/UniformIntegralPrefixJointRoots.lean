/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.UniformIntegralPrefix
/-! # One joint tuple supplies every retained parent root

Natural coordinates avoid changing the tuple when prefix lengths are
identified. The new head is omitted only by a literal one-place shift.
-/
@[expose] public section
namespace LeanCanny.Algebra.UniformIntegralPrefix
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def RootsAt {S N m : ℕ} (P : Prefix S N m) (z : ℕ→ℝ) : Prop :=
  ∀ i,(P.rows i).eval₂ (Int.castRingHom ℝ) (fun j=>z j.val)=0

theorem rootsAt_heq {S N m S' N' m' : ℕ} (P : Prefix S N m) (Q : Prefix S' N' m')
    (hS : S=S') (hN : N=N') (hm : m=m') (hP : HEq P Q) (z : ℕ→ℝ) : RootsAt P z ↔ RootsAt Q z := by
  cases hS
  cases hN
  cases hm
  have he:=eq_of_heq hP
  cases he
  rfl

theorem rootsAt_parent {S N m : ℕ} (P : Prefix S N m) (hm : m≤S) (hN : 0<N)
    (p : Polynomial P.carrier) (d : ℕ) (z : ℕ→ℝ)
    (hz : RootsAt (step P hm hN p d) z) : RootsAt P (fun i=>z (i+1)) := by
  intro i
  have HR:=hz i.succ
  simp only [step,UniformIntegralPrefixRows.rows,Fin.cons_succ,MvPolynomial.eval₂_rename] at HR
  change (P.rows i).eval₂ (Int.castRingHom ℝ) (fun j=>z (j.val+1))=0 at HR
  exact HR

theorem exists_parent_interpretation {S N m : ℕ} (P : Prefix S N m) (hm : m≤S) (hN : 0<N)
    (p : Polynomial P.carrier) (d : ℕ) (z : ℕ→ℝ)
    (hz : RootsAt (step P hm hN p d) z) :
    ∃ φ : P.carrier→ₐ[ℤ]ℝ,∀ i,φ (P.basis.generator i)=
      z (i.val+1)^UniformIntegralPowerSchedule.weights S N m i :=
  P.interpret ℝ (fun i=>z (i.val+1)) (rootsAt_parent P hm hN p d z hz)

end LeanCanny.Algebra.UniformIntegralPrefix
