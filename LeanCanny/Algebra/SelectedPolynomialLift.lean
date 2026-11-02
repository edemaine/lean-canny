/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.PseudoRemainderQuery
public import LeanCanny.Algebra.IntegralCoordinateEvaluation
/-! # Polynomial representatives retain one selected coefficient hom

A representative chooser need not preserve products. Its evaluation at the
selected joint point is a ring hom, so principal determinants and Tarski
seeds specialize correctly. Degree bounds apply AFTER selection, allowing
leading coefficients on other components to survive or disappear.
-/
@[expose] public section
namespace LeanCanny.Algebra.SelectedPolynomialLift
open Polynomial PrincipalSubresultant
open scoped Classical
variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

noncomputable def lift (p : Polynomial A) (representative : A→B) (d : ℕ) : Polynomial B :=
  ∑ k∈Finset.range (d+1),Polynomial.monomial k (representative (p.coeff k))

theorem coefficient (p : Polynomial A) (representative : A→B) (d k : ℕ) :
    (lift p representative d).coeff k=if k≤d then representative (p.coeff k) else 0 := by
  simp [lift,Polynomial.coeff_monomial]

theorem map_lift_coefficients (p : Polynomial A) (representative : A→B) (d : ℕ)
    (select : A→+*C) (evaluate : B→+*C)
    (he : ∀ k≤d,evaluate (representative (p.coeff k))=select (p.coeff k))
    (hd : (p.map select).natDegree≤d) :
    (lift p representative d).map evaluate=p.map select := by
  ext k
  rw [Polynomial.coeff_map,coefficient]
  by_cases hk : k≤d
  · rw [ite_eq_left hk,he k hk,Polynomial.coeff_map]
  · rw [ite_eq_right hk,map_zero]
    exact (Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hd (Nat.lt_of_not_ge hk))).symm

theorem map_lift (p : Polynomial A) (representative : A→B) (d : ℕ) (select : A→+*C) (evaluate : B→+*C)
    (he : ∀ a,evaluate (representative a)=select a) (hd : (p.map select).natDegree≤d) :
    (lift p representative d).map evaluate=p.map select :=
  map_lift_coefficients p representative d select evaluate (fun k _=>he (p.coeff k)) hd

theorem seed_map_lift (p f : Polynomial A) (representative : A→B) (d e D : ℕ) (select : A→+*C) (evaluate : B→+*C)
    (he : ∀ a,evaluate (representative a)=select a)
    (hp : (p.map select).natDegree≤d) (hf : (f.map select).natDegree≤e) :
    (PseudoRemainder.seed (lift p representative d) (lift f representative e) d D).map evaluate=
      PseudoRemainder.seed (p.map select) (f.map select) d D := by
  rw [←PseudoRemainder.seed_map,map_lift p representative d select evaluate he hp,
    map_lift f representative e select evaluate he hf]

theorem principal_map_lift (p f : Polynomial A) (representative : A→B) (d e D s j : ℕ)
    (select : A→+*C) (evaluate : B→+*C) (he : ∀ a,evaluate (representative a)=select a)
    (hp : (p.map select).natDegree≤d) (hf : (f.map select).natDegree≤e) :
    evaluate (signedPsc (lift p representative d)
      (PseudoRemainder.seed (lift p representative d) (lift f representative e) d D) d s j)=
      signedPsc (p.map select) (PseudoRemainder.seed (p.map select) (f.map select) d D) d s j := by
  rw [←signedPsc_map_map,map_lift p representative d select evaluate he hp,
    seed_map_lift p f representative d e D select evaluate he hp hf]

/-- Canonical representatives supply the evaluation property without any
multiplicativity assumption on representative selection. -/
theorem canonical (m N : ℕ) (basis : IntegralCoordinateBasis A m N) (φ : A→ₐ[ℤ]C)
    (p : Polynomial A) (d : ℕ) (hd : (p.map φ.toRingHom).natDegree≤d) :
    (lift p basis.representative d).map (MvPolynomial.aeval (fun i=>φ (basis.generator i))).toRingHom=p.map φ.toRingHom :=
  map_lift p basis.representative d φ.toRingHom _ (fun a=>basis.representative_eval_algHom a φ) hd

end LeanCanny.Algebra.SelectedPolynomialLift
