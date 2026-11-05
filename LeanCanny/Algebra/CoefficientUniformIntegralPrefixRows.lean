/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.CoefficientCoordinateBasisSpecialization
public import LeanCanny.Algebra.UniformIntegralPrefixRows
/-! # Actual globally powered scalar rows over a generic coefficient ring

The equation, layout and powers are constructed exactly as for the native
integer prefix. Coefficient specialization is derived from the actual basis
and padded normalization, with only the old-row induction invariant as input.
-/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientUniformIntegralPrefixRows
open MvPolynomial UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {R A :Type*} [CommRing R] [CommRing A] [Algebra R A] {m N :ℕ}

abbrev layout:=UniformIntegralPrefixRows.layout
abbrev degrees:=@UniformIntegralPrefixRows.degrees

def base (R :Type*) [CommRing R] :Fin 0→MvPolynomial (Fin 0) R:=Fin.elim0

noncomputable def equation (b :CoefficientCoordinateBasis R A m N) (p :Polynomial A) (d :ℕ) :
    Polynomial (MvPolynomial (Fin m) R):=b.polynomial (PaddedIntegralNormalization.polynomial p d N)

noncomputable def rows (S :ℕ) (q :Fin m→MvPolynomial (Fin m) R)
    (b :CoefficientCoordinateBasis R A m N) (p :Polynomial A) (d :ℕ) :
    Fin (m+1)→MvPolynomial (Fin (m+1)) R:=
  Fin.cons (rename (layout m) (MonicParameterRows.row
    (equation b p d) N (weights S N m) (birth S N m)))
    (fun i=>rename Fin.succ (q i))

section Maps
variable {T B :Type*} [CommRing T] [CommRing B] [Algebra T B]

private theorem substitute_map {σ :Type*} (φ :R→+*T) (w :σ→ℕ) (p :MvPolynomial σ R) :
    MvPolynomial.map φ (CoordinatePowerSubstitution.substitute w p)=
      CoordinatePowerSubstitution.substitute w (MvPolynomial.map φ p):=by
  simpa only [CoordinatePowerSubstitution.substitute,map_pow,MvPolynomial.map_X] using
    MvPolynomial.map_bind₁ φ (fun i=>(X i :MvPolynomial σ R)^w i) p

private theorem parameter_row_map {σ :Type*} (φ :R→+*T)
    (p :Polynomial (MvPolynomial σ R)) (d :ℕ) (w :σ→ℕ) (W :ℕ) :
    MvPolynomial.map φ (MonicParameterRows.row p d w W)=
      MonicParameterRows.row (p.map (MvPolynomial.map φ)) d w W:=by
  simp only [MonicParameterRows.row,MonicParameterRows.lower,map_add,map_pow,MvPolynomial.map_X,
    map_sum,map_mul,MvPolynomial.map_rename,substitute_map,MonicParameterRows.coefficient,Polynomial.coeff_map]

variable {φ :R→+*T} {ψ :A→+*B} {b :CoefficientCoordinateBasis R A m N}
  {c :CoefficientCoordinateBasis T B m N}

theorem equation_map (H :CoefficientCoordinateBasis.Specializes φ ψ b c) (p :Polynomial A) (d :ℕ) :
    (equation b p d).map (MvPolynomial.map φ)=equation c (p.map ψ) d:=by
  unfold equation
  rw [H.polynomial_map,PaddedIntegralNormalization.map]

theorem rows_map (H :CoefficientCoordinateBasis.Specializes φ ψ b c) (S :ℕ)
    (q :Fin m→MvPolynomial (Fin m) R) (q' :Fin m→MvPolynomial (Fin m) T)
    (HQ :∀i,MvPolynomial.map φ (q i)=q' i) (p :Polynomial A) (d :ℕ) :
    (fun i=>MvPolynomial.map φ (rows S q b p d i))=rows S q' c (p.map ψ) d:=by
  funext i
  refine Fin.cases ?_ (fun j=>?_) i
  · simp only [rows,Fin.cons_zero,MvPolynomial.map_rename,parameter_row_map,equation_map H]
  · simp only [rows,Fin.cons_succ,MvPolynomial.map_rename,HQ]

theorem base_map (φ :R→+*T) :∀i,MvPolynomial.map φ (base R i)=base T i:=by
  intro i
  exact Fin.elim0 i

end Maps

theorem coefficient_degree (S :ℕ) (hm :m≤S) (b :CoefficientCoordinateBasis R A m N)
    (p :Polynomial A) (d i :ℕ) :
    (CoordinatePowerSubstitution.substitute (weights S N m) ((equation b p d).coeff i)).totalDegree≤
      coefficientBound S N m:=by
  have HD :((equation b p d).coeff i).totalDegree≤m*(N-1):=b.polynomial_coefficient_degree _ i
  by_cases hz :m=0
  · subst m
    rw [coefficientBound,ite_eq_left rfl]
    apply (CoordinatePowerSubstitution.degree_le _ _ 0 (fun i=>Fin.elim0 i)).trans
    simp
  · rw [coefficientBound,ite_eq_right hz]
    exact (CoordinatePowerSubstitution.degree_le _ _ _ (weights_le S N m)).trans
      (Nat.mul_le_mul_left _ (HD.trans (cap_le S N m hm)))

theorem scalar_lower_degree (S :ℕ) (hm :m≤S) (hN :0<N)
    (b :CoefficientCoordinateBasis R A m N) (p :Polynomial A) (d :ℕ) :
    (MonicParameterRows.lower (equation b p d) N (weights S N m) (birth S N m)).totalDegree<
      N*birth S N m:=
  MonicParameterRows.lower_degree _ N (coefficientBound S N m) _ _ hN (dominates S N m)
    (coefficient_degree S hm b p d)

theorem row_degree (S :ℕ) (hm :m≤S) (hN :0<N)
    (q :Fin m→MvPolynomial (Fin m) R) (e :Fin m→ℕ) (hq :∀i,(q i).totalDegree≤e i)
    (b :CoefficientCoordinateBasis R A m N) (p :Polynomial A) (d :ℕ) (j :Fin (m+1)) :
    (rows S q b p d j).totalDegree≤degrees S N e j:=by
  refine Fin.cases ?_ (fun i=>?_) j
  · apply (totalDegree_rename_le _ _).trans
    apply (totalDegree_add _ _).trans
    apply max_le ?_ (scalar_lower_degree S hm hN b p d).le
    simpa only [Nat.one_mul] using
      ((isHomogeneous_X (R:=R) (Sum.inr () :Fin m⊕Unit)).pow (N*birth S N m)).totalDegree_le
  · exact (totalDegree_rename_le _ _).trans (hq i)

theorem equation_ofIntegral (b :IntegralCoordinateBasis A m N) (p :Polynomial A) (d :ℕ) :
    equation (CoefficientCoordinateBasis.ofIntegral b) p d=PaddedIntegralParameterExtension.equation b p d:=rfl

theorem rows_ofIntegral (S :ℕ) (q :Fin m→MvPolynomial (Fin m) ℤ)
    (b :IntegralCoordinateBasis A m N) (p :Polynomial A) (d :ℕ) :
    rows S q (CoefficientCoordinateBasis.ofIntegral b) p d=UniformIntegralPrefixRows.rows S q b p d:=rfl

end LeanCanny.Algebra.CoefficientUniformIntegralPrefixRows
