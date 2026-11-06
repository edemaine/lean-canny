/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralPolynomialWindowTarskiSource
public import LeanCanny.Algebra.PseudoRemainderQuery
/-! # Finite coefficient guards select actual-source window Tarski degrees

Zero pseudo-seeds are included explicitly. The resulting query identity
uses actual formal principal polynomials at the same endpoint/center tuple.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralPolynomialWindowTarski
open LeanCanny.Algebra LeanCanny.Computation Polynomial MvPolynomial PrincipalSubresultant
open IntegralFramedBankPolynomialModel (Source)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] seed head query arity width inputBound outputBound degree seedDegree bound
variable (S:Source) (N:List Bool→ℕ) (hd:∀c,S.arity c=N c+1)

private theorem degree_of_coefficients (p:ℝ[X]) (N d:ℕ) (HN:p.natDegree ≤ N)
    (HC:p.coeff d ≠ 0) (HZ:∀i,d < i → i ≤ N → p.coeff i=0):p.natDegree=d:=by
  apply le_antisymm
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    by_cases hN:i ≤ N
    · exact HZ i hi hN
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  · exact Polynomial.le_natDegree_of_ne_zero HC

noncomputable def realHead (c:List Bool) (v:Fin (arity N c) → ℝ):ℝ[X]:=
  (head S N hd c).map (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) v)
noncomputable def realQuery (c:List Bool) (v:Fin (arity N c) → ℝ):ℝ[X]:=
  (query N c).map (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) v)
noncomputable def realSeed (c:List Bool) (v:Fin (arity N c) → ℝ):ℝ[X]:=
  (seed S N hd c).map (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) v)

noncomputable def HeadSelected (c:List Bool) (v:Fin (arity N c) → ℝ):Prop:=
  (realHead S N hd c v).coeff (degree S c) ≠ 0 ∧∀i,degree S c < i → i ≤ inputBound S c → (realHead S N hd c v).coeff i=0
noncomputable def SeedSelected (c:List Bool) (v:Fin (arity N c) → ℝ):Prop:=
  (seedDegree S c=0 ∧∀i,i < degree S c → (realSeed S N hd c v).coeff i=0) ∨
  ((realSeed S N hd c v).coeff (seedDegree S c) ≠ 0 ∧∀i,seedDegree S c < i → i < degree S c → (realSeed S N hd c v).coeff i=0)
noncomputable def Selected (c:List Bool) (v:Fin (arity N c) → ℝ):Prop:=HeadSelected S N hd c v∧SeedSelected S N hd c v

theorem head_value (c:List Bool) (v:Fin (arity N c) → ℝ) (i:ℕ):
    (realHead S N hd c v).coeff i=((head S N hd c).coeff i).eval₂ (Int.castRingHom ℝ) v:=Polynomial.coeff_map _ _
theorem seed_value (c:List Bool) (v:Fin (arity N c) → ℝ) (i:ℕ):
    (realSeed S N hd c v).coeff i=((seed S N hd c).coeff i).eval₂ (Int.castRingHom ℝ) v:=Polynomial.coeff_map _ _

theorem real_head_degree (c:List Bool) (v:Fin (arity N c) → ℝ):(realHead S N hd c v).natDegree ≤ inputBound S c:=
  Polynomial.natDegree_map_le.trans (head_degree S N hd c)
theorem real_seed_degree (c:List Bool) (v:Fin (arity N c) → ℝ):(realSeed S N hd c v).natDegree < degree S c:=
  Polynomial.natDegree_map_le.trans_lt (seed_degree S N hd c)

theorem head_selected_iff (c:List Bool) (v:Fin (arity N c) → ℝ):
    HeadSelected S N hd c v↔(realHead S N hd c v).natDegree=degree S c:=by
  constructor
  · rintro ⟨HC,HZ⟩
    exact degree_of_coefficients _ _ _ (real_head_degree S N hd c v) HC HZ
  · intro HD
    constructor
    · rw [←HD,Polynomial.coeff_natDegree]
      apply Polynomial.leadingCoeff_ne_zero.mpr
      intro H0
      have Hpos:0 < degree S c:=(family S N hd).degree_pos c
      rw [H0,Polynomial.natDegree_zero] at HD
      omega
    · intro i hi _
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

theorem seed_selected_iff (c:List Bool) (v:Fin (arity N c) → ℝ):
    SeedSelected S N hd c v↔(realSeed S N hd c v).natDegree=seedDegree S c:=by
  have HB:=real_seed_degree S N hd c v
  constructor
  · rintro (⟨HS,HZ⟩|⟨HC,HZ⟩)
    · have HE:realSeed S N hd c v=0:=by
        ext i
        rw [Polynomial.coeff_zero]
        by_cases hi:i < degree S c
        · exact HZ i hi
        · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [HE,Polynomial.natDegree_zero,HS]
    · exact degree_of_coefficients _ (degree S c-1) _ (by omega) HC (fun i hi hD=>HZ i hi (by omega))
  · intro HS
    by_cases HE:realSeed S N hd c v=0
    · left
      rw [HE,Polynomial.natDegree_zero] at HS
      exact ⟨HS.symm,fun i _=>by rw [HE,Polynomial.coeff_zero]⟩
    · right
      constructor
      · rw [←HS,Polynomial.coeff_natDegree]
        exact Polynomial.leadingCoeff_ne_zero.mpr HE
      · intro i hi _
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

theorem selected_iff (c:List Bool) (v:Fin (arity N c) → ℝ):Selected S N hd c v↔
    (realHead S N hd c v).natDegree=degree S c∧(realSeed S N hd c v).natDegree=seedDegree S c:=
  and_congr (head_selected_iff S N hd c v) (seed_selected_iff S N hd c v)

noncomputable def statistic (c:List Bool) (v:Fin (arity N c) → ℝ):ℤ:=
  permanencesMinusVariations ((List.range (degree S c+1)).reverse.map
    (fun j=>(FixedWidthTarskiPrincipalBits.polynomial (family S N hd) c j).eval₂ (Int.castRingHom ℝ) v))

theorem tarski_eq_statistic (c:List Bool) (v:Fin (arity N c) → ℝ) (H:Selected S N hd c v):
    RootSignQueries.tarskiQuery (realHead S N hd c v) (realQuery N c v)=statistic S N hd c v:=by
  obtain ⟨HP,HS⟩:=(selected_iff S N hd c v).mp H
  have HI:((realQuery N c v)*(realHead S N hd c v).derivative).natDegree ≤ bound S c:=by
    rw [realQuery,realHead,Polynomial.derivative_map,←Polynomial.map_mul]
    exact Polynomial.natDegree_map_le.trans (input_degree S N hd c)
  rw [RootSignQueries.tarskiQuery_eq_pseudoPrincipalQuery _ _ _ _ HP ((family S N hd).degree_pos c) HI,
    PseudoRemainder.principalQuery]
  have HE:PseudoRemainder.seed (realHead S N hd c v) (realQuery N c v) (degree S c) (bound S c)=realSeed S N hd c v:=
    by
      unfold realHead realQuery realSeed seed
      exact PseudoRemainder.seed_map _ _ _ _ _
  rw [HE,HS]
  apply congrArg permanencesMinusVariations
  apply List.map_congr_left
  intro j _
  have HJ:=(FixedWidthTarskiPrincipalBits.selected (family S N hd) c j (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) v)).symm
  change signedPsc (realHead S N hd c v)
    (PseudoRemainder.seed (realHead S N hd c v) (realQuery N c v) (degree S c) (bound S c)) (degree S c) (seedDegree S c) j=
      (FixedWidthTarskiPrincipalBits.polynomial (family S N hd) c j).eval₂ (Int.castRingHom ℝ) v at HJ
  rw [HE] at HJ
  exact HJ

/-- The constant nonzero head branch has no interval root, without a degree oracle. -/
theorem constant_head_no_roots (c:List Bool) (v:Fin (arity N c) → ℝ)
    (HC:(realHead S N hd c v).coeff 0 ≠ 0)
    (HZ:∀i,0 < i → i ≤ inputBound S c → (realHead S N hd c v).coeff i=0) (r:ℝ):
    (realHead S N hd c v).eval r ≠ 0:=by
  have HD:=degree_of_coefficients _ _ 0 (real_head_degree S N hd c v) HC HZ
  rw [Polynomial.eq_C_of_natDegree_eq_zero HD,Polynomial.eval_C]
  exact HC

end LeanCanny.Encoding.IntegralPolynomialWindowTarski
