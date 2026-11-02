/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.SelectedPolynomialLift
/-! # Two polynomial axes retain the selected old coefficient field

The bounded representative in the parameter axis is chosen coefficient by
coefficient. Its symbolic degree can exceed its degree after selection.
Products and determinants use evaluation, never a multiplicative claim for
the representative chooser.
-/
@[expose] public section
namespace LeanCanny.Algebra.SelectedParameterPolynomialLift
open Polynomial PrincipalSubresultant
variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

noncomputable def lift (p : Polynomial (Polynomial A)) (representative : A→B) (d e : ℕ) : Polynomial (Polynomial B) :=
  SelectedPolynomialLift.lift p (fun q=>SelectedPolynomialLift.lift q representative e) d

theorem map_lift (p : Polynomial (Polynomial A)) (representative : A→B) (d e : ℕ)
    (select : A→+*C) (evaluate : B→+*C) (he : ∀ a,evaluate (representative a)=select a)
    (hd : (p.map (Polynomial.mapRingHom select)).natDegree≤d)
    (hp : ∀ i≤d,((p.coeff i).map select).natDegree≤e) :
    (lift p representative d e).map (Polynomial.mapRingHom evaluate)=p.map (Polynomial.mapRingHom select) := by
  apply SelectedPolynomialLift.map_lift_coefficients
  · intro i hi
    exact SelectedPolynomialLift.map_lift (p.coeff i) representative e select evaluate he (hp i hi)
  · exact hd

theorem seed (p f : Polynomial (Polynomial A)) (representative : A→B) (d e u v D : ℕ)
    (select : A→+*C) (evaluate : B→+*C) (he : ∀ a,evaluate (representative a)=select a)
    (hd : (p.map (Polynomial.mapRingHom select)).natDegree≤d)
    (hp : ∀ i≤d,((p.coeff i).map select).natDegree≤e)
    (hu : (f.map (Polynomial.mapRingHom select)).natDegree≤u)
    (hf : ∀ i≤u,((f.coeff i).map select).natDegree≤v) :
    (PseudoRemainder.seed (lift p representative d e) (lift f representative u v) d D).map
      (Polynomial.mapRingHom evaluate)=
      PseudoRemainder.seed (p.map (Polynomial.mapRingHom select)) (f.map (Polynomial.mapRingHom select)) d D := by
  rw [←PseudoRemainder.seed_map,map_lift p representative d e select evaluate he hd hp,
    map_lift f representative u v select evaluate he hu hf]

theorem principal (p f : Polynomial (Polynomial A)) (representative : A→B) (d e u v D s j : ℕ)
    (select : A→+*C) (evaluate : B→+*C) (he : ∀ a,evaluate (representative a)=select a)
    (hd : (p.map (Polynomial.mapRingHom select)).natDegree≤d)
    (hp : ∀ i≤d,((p.coeff i).map select).natDegree≤e)
    (hu : (f.map (Polynomial.mapRingHom select)).natDegree≤u)
    (hf : ∀ i≤u,((f.coeff i).map select).natDegree≤v) :
    (signedPsc (lift p representative d e) (PseudoRemainder.seed (lift p representative d e)
      (lift f representative u v) d D) d s j).map evaluate=
      signedPsc (p.map (Polynomial.mapRingHom select))
        (PseudoRemainder.seed (p.map (Polynomial.mapRingHom select)) (f.map (Polynomial.mapRingHom select)) d D) d s j := by
  change (Polynomial.mapRingHom evaluate) (signedPsc _ _ _ _ _)=_
  rw [←signedPsc_map_map,map_lift p representative d e select evaluate he hd hp,
    seed p f representative d e u v D select evaluate he hd hp hu hf]

end LeanCanny.Algebra.SelectedParameterPolynomialLift
