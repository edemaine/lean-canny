/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.PhysicalPowerCriticalAppend
public import LeanCanny.Algebra.EmbeddedCoefficient
public import LeanCanny.Algebra.CoordinatePowerCoefficients
/-! # Literal coefficient branches of the full physical critical block

Only original source coefficients, original normal scalars and actual height
representative coefficients occur. Positive powers reduce to one divided
exponent query with a divisibility guard.
-/
@[expose] public section
namespace LeanCanny.Algebra.PhysicalPowerCriticalRows
open MvPolynomial FlatAffineCriticalStage
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
variable {ι R : Type*} {n : ℕ} [Fintype ι] [CommRing R]

noncomputable def rowCoefficient (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n+1)→Fin n→R) (H : Fin n→MvPolynomial ι R)
    (j : Variables n) (e : (ι⊕Variables n)→₀ℕ) : R :=
  match j with
  | .inl i => EmbeddedCoefficient.derivative ambient (fun _ _ h=>Sum.inl.inj (Sum.inr.inj h)) p i e -
      ∑ k,a k i*(if Finsupp.single (multiplier k) 1=e then 1 else 0)
  | .inr k => Fin.cases
      (EmbeddedCoefficient.value ambient (fun _ _ h=>Sum.inl.inj (Sum.inr.inj h)) p e)
      (fun i=>if i∈s then
        (∑ k,a i.succ k*(if Finsupp.single (ambient k) 1=e then 1 else 0))-
          EmbeddedCoefficient.value Sum.inl Sum.inl_injective (H i) e
        else if Finsupp.single (multiplier i.succ) 1=e then 1 else 0) k

omit [Fintype ι] in
theorem unpowered_coefficient (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n+1)→Fin n→R) (H : Fin n→MvPolynomial ι R)
    (j : Variables n) (e : (ι⊕Variables n)→₀ℕ) :
    (FlatAffineCriticalStage.row p s a H j).coeff e=rowCoefficient p s a H j e := by
  cases j with
  | inl i =>
    simp only [FlatAffineCriticalStage.row,gradient,coeff_sub,coeff_sum,coeff_C_mul,coeff_X,rowCoefficient]
    rw [EmbeddedCoefficient.coeff_rename_pderiv]
  | inr k =>
    refine Fin.cases ?_ (fun i=>?_) k
    · exact EmbeddedCoefficient.coeff_rename ambient (fun _ _ h=>Sum.inl.inj (Sum.inr.inj h)) p e
    · simp only [FlatAffineCriticalStage.row,Fin.cases_succ,rowCoefficient]
      by_cases hi : i∈s
      · rw [ite_eq_left hi,ite_eq_left hi]
        simp only [coeff_sub,AffineHeightPolynomial.polynomial,coeff_sum,coeff_C_mul,coeff_X]
        rw [EmbeddedCoefficient.coeff_rename Sum.inl Sum.inl_injective]
      · simp only [ite_eq_right hi,coeff_X]

theorem powered_coefficient (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n+1)→Fin n→R) (H : Fin n→MvPolynomial ι R) (w : ι→ℕ) (D W : ℕ)
    (hw : ∀i,0<w i) (hD : 2≤D) (hW : 0<W)
    (j : Variables n) (e : (ι⊕Variables n)→₀ℕ) :
    (rows p s a H w D W j).coeff e=
      if ∀i,e i % powers w D W i=0 then
        rowCoefficient p s a H j (CoordinatePowerSubstitution.quotientExponent (powers w D W) e) else 0 := by
  have hp : ∀i : ι⊕Variables n,0<powers w D W i := by
    intro i
    rcases i with i|i
    · exact hw i
    · rcases i with i|i
      · exact hW
      · exact Nat.mul_pos (by omega) hW
  rw [rows,CoordinatePowerSubstitution.coefficient _ hp,unpowered_coefficient]

end LeanCanny.Algebra.PhysicalPowerCriticalRows
