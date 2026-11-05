/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.CoefficientHeightBank
public import LeanCanny.Algebra.PurePowerAnnihilatorMap
public import LeanCanny.Algebra.IntegralMixedCriticalRoot
/-! # The actual mixed critical polynomial over a coefficient ring

The native rule and bank determine all scales and frozen numerators. The
existing pure-power constructor supplies the polynomial, and its coefficient
maps give exact specialization without an independently supplied matrix.
-/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientMixedCriticalPolynomial
open IntegralMixedHistory
open scoped Classical BigOperators
variable {R S A B :Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra S B] {n m :ℕ}

noncomputable def scales (x :CoefficientHeightBank R A m) (r :CriticalRule n)
    (i :Fin (n+1)) :R:=x.commonDenominator*(r.scales i:R)

noncomputable def denominator (x :CoefficientHeightBank R A m) (r :CriticalRule n) :R:=
  ∏i,scales x r i

noncomputable def numerators (x :CoefficientHeightBank R A m) (r :CriticalRule n) (i :ℕ) :A:=
  if hi :i<n+1 then
    x.expression (r.heights ⟨i,hi⟩)*algebraMap R A (∏j ∈Finset.univ.erase ⟨i,hi⟩,scales x r j)
  else 0

noncomputable def polynomial (x :CoefficientHeightBank R A m)
    (low :MvPolynomial (Fin (n+1)) R) (leading :R) (D :ℕ) (r :CriticalRule n) :Polynomial A:=
  ClearedCoordinateCritical.annihilator D (algebraMap R A (denominator x r))
    (numerators x r) r.offset.val (IntegralMixedCriticalRoot.fit r).le
    (low.map (algebraMap R A)) (algebraMap R A leading)
    (IntegralMixedCriticalRoot.objective r) (IntegralMixedCriticalRoot.coordinate r)

noncomputable def leadingValue (x :CoefficientHeightBank R A m) (a :R) (D :ℕ)
    (r :CriticalRule n) :R:=
  ((a*denominator x r^D)*(D:R))^
    ((PurePowerReductionBounds.bound (n-r.offset.val+1) D+1)*
      PurePowerReductionBounds.dimension (n-r.offset.val+1) D)

variable {φ :R→+*S} {ψ :A→+*B} {x :CoefficientHeightBank R A m} {y :CoefficientHeightBank S B m}

theorem scales_map (H :CoefficientHeightBank.Specializes φ ψ x y) (r :CriticalRule n)
    (i :Fin (n+1)) :φ (scales x r i)=scales y r i:=by
  simp only [scales,map_mul,H.commonDenominator,map_intCast]

theorem denominator_map (H :CoefficientHeightBank.Specializes φ ψ x y) (r :CriticalRule n) :
    φ (denominator x r)=denominator y r:=by
  simp only [denominator,map_prod,scales_map H]

theorem numerators_map (H :CoefficientHeightBank.Specializes φ ψ x y) (r :CriticalRule n) (i :ℕ) :
    ψ (numerators x r i)=numerators y r i:=by
  unfold numerators
  split_ifs
  · simp only [map_mul,H.expression,H.coefficients,map_prod,scales_map H]
  · exact map_zero ψ

theorem polynomial_map (H :CoefficientHeightBank.Specializes φ ψ x y)
    (low :MvPolynomial (Fin (n+1)) R) (leading :R) (D :ℕ) (r :CriticalRule n) :
    (polynomial x low leading D r).map ψ=polynomial y (low.map φ) (φ leading) D r:=by
  have HC :ψ.comp (algebraMap R A)=(algebraMap S B).comp φ:=by
    ext a
    exact H.coefficients a
  have HL :(low.map (algebraMap R A)).map ψ=(low.map φ).map (algebraMap S B):=by
    rw [MvPolynomial.map_map,MvPolynomial.map_map,HC]
  unfold polynomial
  rw [PurePowerAnnihilatorMap.cleared]
  simp only [H.coefficients,denominator_map H,numerators_map H,HL]

theorem leadingValue_map (H :CoefficientHeightBank.Specializes φ ψ x y)
    (a :R) (D :ℕ) (r :CriticalRule n) :
    φ (leadingValue x a D r)=leadingValue y (φ a) D r:=by
  simp only [leadingValue,map_pow,map_mul,denominator_map H,map_natCast]

 theorem scales_ofState {cap width :ℕ} {P :SpatialSource n} {ι :Type}
    (x :State P cap width m ι) (hm :m≤cap) (r :CriticalRule n) :
    scales (CoefficientHeightBank.ofState x) r=(data x hm r).scales:=rfl

 theorem denominator_ofState {cap width :ℕ} {P :SpatialSource n} {ι :Type}
    (x :State P cap width m ι) (hm :m≤cap) (r :CriticalRule n) :
    denominator (CoefficientHeightBank.ofState x) r=
      CoordinateFrozenCriticalElimination.denominator (data x hm r).scales:=rfl

 theorem numerators_ofState {cap width :ℕ} {P :SpatialSource n} {ι :Type}
    (x :State P cap width m ι) (hm :m≤cap) (r :CriticalRule n) (i :ℕ) :
    numerators (CoefficientHeightBank.ofState x) r i=
      CoordinateFrozenCriticalElimination.numerators (data x hm r).scales (data x hm r).heights i:=by
  unfold numerators CoordinateFrozenCriticalElimination.numerators
  split_ifs
  · rw [CoefficientHeightBank.expression_ofState]
    rfl
  · rfl

/-- This is the polynomial of the actual native critical command. -/
theorem polynomial_ofState {cap width :ℕ} {P :SpatialSource n} {ι :Type}
    (x :State P cap width m ι) (hm :m≤cap) (r :CriticalRule n) :
    polynomial (CoefficientHeightBank.ofState x) P.low P.leading P.degree r=
      criticalPolynomial x hm r:=by
  rw [IntegralMixedCriticalRoot.equation]
  unfold polynomial CoordinateFrozenCriticalElimination.polynomial
  rw [denominator_ofState x hm r]
  congr 1
  funext i
  exact numerators_ofState x hm r i

theorem leadingValue_ofState {cap width :ℕ} {P :SpatialSource n} {ι :Type}
    (x :State P cap width m ι) (hm :m≤cap) (r :CriticalRule n) :
    leadingValue (CoefficientHeightBank.ofState x) P.leading P.degree r=
      criticalLeading x hm r:=rfl

end LeanCanny.Algebra.CoefficientMixedCriticalPolynomial
