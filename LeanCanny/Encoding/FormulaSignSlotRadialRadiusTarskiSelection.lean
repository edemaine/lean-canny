/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialRadiusTarskiSelectionSource
public import LeanCanny.Algebra.PseudoRemainderQuery
/-! # Finite actual coefficient guards select the Tarski degrees

Zero pseudo-seeds are included explicitly. The resulting query identity
uses actual formal principal polynomials at the same endpoint/center tuple.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialRadiusTarskiFamily
open LeanCanny.Algebra LeanCanny.Computation Polynomial MvPolynomial PrincipalSubresultant
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] seed head query arity width inputBound outputBound degree seedDegree bound

private theorem degree_of_coefficients (p:ℝ[X]) (N d:ℕ) (HN:p.natDegree ≤ N)
    (HC:p.coeff d ≠ 0) (HZ:∀i,d < i → i ≤ N → p.coeff i=0):p.natDegree=d:=by
  apply le_antisymm
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    by_cases hN:i ≤ N
    · exact HZ i hi hN
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  · exact Polynomial.le_natDegree_of_ne_zero HC

noncomputable def realHead (c:List Bool) (v:Fin (arity c) → ℝ):ℝ[X]:=
  (head c).map (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) v)
noncomputable def realQuery (c:List Bool) (v:Fin (arity c) → ℝ):ℝ[X]:=
  (query c).map (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) v)
noncomputable def realSeed (c:List Bool) (v:Fin (arity c) → ℝ):ℝ[X]:=
  (seed c).map (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) v)

noncomputable def HeadSelected (c:List Bool) (v:Fin (arity c) → ℝ):Prop:=
  (realHead c v).coeff (degree c) ≠ 0 ∧∀i,degree c < i → i ≤ inputBound c → (realHead c v).coeff i=0
noncomputable def SeedSelected (c:List Bool) (v:Fin (arity c) → ℝ):Prop:=
  (seedDegree c=0 ∧∀i,i < degree c → (realSeed c v).coeff i=0) ∨
  ((realSeed c v).coeff (seedDegree c) ≠ 0 ∧∀i,seedDegree c < i → i < degree c → (realSeed c v).coeff i=0)
noncomputable def Selected (c:List Bool) (v:Fin (arity c) → ℝ):Prop:=HeadSelected c v∧SeedSelected c v

theorem head_value (c:List Bool) (v:Fin (arity c) → ℝ) (i:ℕ):
    (realHead c v).coeff i=((head c).coeff i).eval₂ (Int.castRingHom ℝ) v:=Polynomial.coeff_map _ _
theorem seed_value (c:List Bool) (v:Fin (arity c) → ℝ) (i:ℕ):
    (realSeed c v).coeff i=((seed c).coeff i).eval₂ (Int.castRingHom ℝ) v:=Polynomial.coeff_map _ _

theorem real_head_degree (c:List Bool) (v:Fin (arity c) → ℝ):(realHead c v).natDegree ≤ inputBound c:=
  Polynomial.natDegree_map_le.trans (head_degree c)
theorem real_seed_degree (c:List Bool) (v:Fin (arity c) → ℝ):(realSeed c v).natDegree < degree c:=
  Polynomial.natDegree_map_le.trans_lt (seed_degree c)

theorem head_selected_iff (c:List Bool) (v:Fin (arity c) → ℝ):
    HeadSelected c v↔(realHead c v).natDegree=degree c:=by
  constructor
  · rintro ⟨HC,HZ⟩
    exact degree_of_coefficients _ _ _ (real_head_degree c v) HC HZ
  · intro HD
    constructor
    · rw [←HD,Polynomial.coeff_natDegree]
      apply Polynomial.leadingCoeff_ne_zero.mpr
      intro H0
      have Hpos:0 < degree c:=family.degree_pos c
      rw [H0,Polynomial.natDegree_zero] at HD
      omega
    · intro i hi _
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

theorem seed_selected_iff (c:List Bool) (v:Fin (arity c) → ℝ):
    SeedSelected c v↔(realSeed c v).natDegree=seedDegree c:=by
  have HB:=real_seed_degree c v
  constructor
  · rintro (⟨HS,HZ⟩|⟨HC,HZ⟩)
    · have HE:realSeed c v=0:=by
        ext i
        rw [Polynomial.coeff_zero]
        by_cases hi:i < degree c
        · exact HZ i hi
        · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [HE,Polynomial.natDegree_zero,HS]
    · exact degree_of_coefficients _ (degree c-1) _ (by omega) HC (fun i hi hD=>HZ i hi (by omega))
  · intro HS
    by_cases HE:realSeed c v=0
    · left
      rw [HE,Polynomial.natDegree_zero] at HS
      exact ⟨HS.symm,fun i _=>by rw [HE,Polynomial.coeff_zero]⟩
    · right
      constructor
      · rw [←HS,Polynomial.coeff_natDegree]
        exact Polynomial.leadingCoeff_ne_zero.mpr HE
      · intro i hi _
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

theorem selected_iff (c:List Bool) (v:Fin (arity c) → ℝ):Selected c v↔
    (realHead c v).natDegree=degree c∧(realSeed c v).natDegree=seedDegree c:=
  and_congr (head_selected_iff c v) (seed_selected_iff c v)

noncomputable def statistic (c:List Bool) (v:Fin (arity c) → ℝ):ℤ:=
  permanencesMinusVariations ((List.range (degree c+1)).reverse.map
    (fun j=>(FixedWidthTarskiPrincipalBits.polynomial family c j).eval₂ (Int.castRingHom ℝ) v))

theorem tarski_eq_statistic (c:List Bool) (v:Fin (arity c) → ℝ) (H:Selected c v):
    RootSignQueries.tarskiQuery (realHead c v) (realQuery c v)=statistic c v:=by
  obtain ⟨HP,HS⟩:=(selected_iff c v).mp H
  have HI:((realQuery c v)*(realHead c v).derivative).natDegree ≤ bound c:=by
    rw [realQuery,realHead,Polynomial.derivative_map,←Polynomial.map_mul]
    exact Polynomial.natDegree_map_le.trans (input_degree c)
  rw [RootSignQueries.tarskiQuery_eq_pseudoPrincipalQuery _ _ _ _ HP (family.degree_pos c) HI,
    PseudoRemainder.principalQuery]
  have HE:PseudoRemainder.seed (realHead c v) (realQuery c v) (degree c) (bound c)=realSeed c v:=
    by
      unfold realHead realQuery realSeed seed
      exact PseudoRemainder.seed_map _ _ _ _ _
  rw [HE,HS]
  apply congrArg permanencesMinusVariations
  apply List.map_congr_left
  intro j _
  have HJ:=(FixedWidthTarskiPrincipalBits.selected family c j (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) v)).symm
  change signedPsc (realHead c v)
    (PseudoRemainder.seed (realHead c v) (realQuery c v) (degree c) (bound c)) (degree c) (seedDegree c) j=
      (FixedWidthTarskiPrincipalBits.polynomial family c j).eval₂ (Int.castRingHom ℝ) v at HJ
  rw [HE] at HJ
  exact HJ

/-- The constant nonzero head branch has no interval root, without a degree oracle. -/
theorem constant_head_no_roots (c:List Bool) (v:Fin (arity c) → ℝ)
    (HC:(realHead c v).coeff 0 ≠ 0)
    (HZ:∀i,0 < i → i ≤ inputBound c → (realHead c v).coeff i=0) (r:ℝ):
    (realHead c v).eval r ≠ 0:=by
  have HD:=degree_of_coefficients _ _ 0 (real_head_degree c v) HC HZ
  rw [Polynomial.eq_C_of_natDegree_eq_zero HD,Polynomial.eval_C]
  exact HC

end LeanCanny.Encoding.FormulaSignSlotRadialRadiusTarskiFamily
