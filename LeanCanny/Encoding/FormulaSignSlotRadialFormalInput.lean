/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialFormalSyntax
/-! # The native term is exactly the frozen full integer formal radial input

The numeric blocks are spatial, formal center, and formal radius. This binds
the input term only, without identifying an eliminant or coefficient reader.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialFormalInput
open ETR LeanCanny.Computation LeanCanny.Connectivity LeanCanny.Geometry LeanCanny.Algebra MvPolynomial
open FormulaSignSlotCenteredRadialGraph FormulaSignSlotCenteredRadialLimits
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

def unitEquiv :Unit≃Fin 1 where
  toFun _:=0
  invFun _:=()
  left_inv x:=by cases x;rfl
  right_inv _:=Subsingleton.elim _ _

noncomputable def layout (c :List Bool):FormulaSignSlotRadialFormalBounds.Variables c≃Fin (dimension c):=
  (Equiv.sumCongr (Equiv.refl _) ((Equiv.sumCongr (Equiv.refl _) unitEquiv).trans finSumFinEquiv)).trans finSumFinEquiv
noncomputable def spatialIndex (c :List Bool) (i :Fin (spatial c)):Fin (dimension c):=Fin.castAdd (d c+1) i
noncomputable def formalCenterIndex (c :List Bool) (i :Fin (d c)):Fin (dimension c):=
  Fin.natAdd (spatial c) (Fin.castAdd 1 i)
noncomputable def formalRadiusIndex (c :List Bool):Fin (dimension c):=Fin.natAdd (spatial c) (Fin.last (d c))

theorem layout_spatial (c :List Bool) (i :Fin (spatial c)):
    layout c (FormulaSignSlotRadialFormalBounds.spatialVar c i)=spatialIndex c i:=rfl
theorem layout_center (c :List Bool) (i :Fin (d c)):
    layout c (FormulaSignSlotRadialFormalBounds.centerVar c i)=formalCenterIndex c i:=rfl
theorem layout_radius (c :List Bool):
    layout c (FormulaSignSlotRadialFormalBounds.radiusVar c)=formalRadiusIndex c:=rfl

private theorem difference_finite (A left right :ℕ) (hl :left<A) (hr :right<A):
    (difference left right).finitePolynomial A=X ⟨left,hl⟩-X ⟨right,hr⟩:=by
  simp [difference,Term.finitePolynomial,hl,hr,sub_eq_add_neg]

theorem centerDifference_finite (c :List Bool) (i :Fin (d c)):
    (centerDifference c i.val).finitePolynomial (dimension c)=
      (X (spatialIndex c (centerIndex c i))-X (formalCenterIndex c i):MvPolynomial (Fin (dimension c)) ℤ):=by
  have HL:N c+i.val<dimension c:=by have H:=i.isLt;dsimp only [dimension,spatial];omega
  have HR:spatial c+i.val<dimension c:=by have H:=i.isLt;dsimp only [dimension];omega
  exact difference_finite (dimension c) _ _ HL HR

theorem radiusDifference_finite (c :List Bool):
    (radiusDifference c).finitePolynomial (dimension c)=
      (X (spatialIndex c (radiusIndex c))-X (formalRadiusIndex c):MvPolynomial (Fin (dimension c)) ℤ):=by
  have HL:N c+d c<dimension c:=by dsimp only [dimension,spatial];omega
  have HR:spatial c+d c<dimension c:=by dsimp only [dimension];omega
  exact difference_finite (dimension c) _ _ HL HR

private theorem sum_range {α :Type*} [AddCommMonoid α] (n :ℕ) (f :ℕ→α):
    ((List.range n).map f).sum=∑i :Fin n,f i.val:=by
  have H:((List.range n).map f).sum=∑i∈Finset.range n,f i:=by
    induction n with
    | zero=>simp
    | succ n ih=>simp [List.range_succ,Finset.sum_range_succ,ih]
  exact H.trans (Fin.sum_univ_eq_sum_range f n).symm

theorem centerSquares_finite (c :List Bool):
    (centerSquares c).finitePolynomial (dimension c)=
      ∑i :Fin (d c),(X (spatialIndex c (centerIndex c i))-X (formalCenterIndex c i):
        MvPolynomial (Fin (dimension c)) ℤ)^2:=by
  rw [centerSquares,SumSquares.finitePolynomial_accumulate]
  simp only [Term.finitePolynomial,C_0,zero_add,centerTerms,List.map_map,Function.comp_def]
  rw [sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [centerDifference_finite]

noncomputable def polynomial (c :List Bool):MvPolynomial (Fin (dimension c)) ℤ:=
  rename (layout c) (FormulaSignSlotRadialFormalBounds.flatten c (FormulaSignSlotRadialFormalCenter.polynomial c))

theorem base_finitePolynomial (c :List Bool):rename (spatialIndex c)
      ((FormulaSignSlotCenteredRadialSource.equation c).finitePolynomial (spatial c))=
      (FormulaSignSlotCenteredRadialSource.equation c).finitePolynomial (dimension c):=
    Term.rename_finitePolynomial _ _ _ (FormulaSignSlotCenteredRadialSource.scope c)
      (Nat.le_add_right (spatial c) (d c+1))

theorem finitePolynomial_eq (c :List Bool):(equation c).finitePolynomial (dimension c)=polynomial c:=by
  have HS:(layout c)∘FormulaSignSlotRadialFormalBounds.spatialVar c=spatialIndex c:=funext (layout_spatial c)
  unfold polynomial
  rw [FormulaSignSlotRadialFormalBounds.flatten_equation]
  simp only [map_add,map_sum,map_pow,map_sub,rename_rename,rename_X,layout_spatial,layout_center,layout_radius,HS]
  change (equation c).finitePolynomial (dimension c)=
    rename (spatialIndex c) ((FormulaSignSlotCenteredRadialSource.equation c).finitePolynomial (spatial c))+
      (∑i :Fin (d c),(X (spatialIndex c (centerIndex c i))-X (formalCenterIndex c i))^2)+
      (X (spatialIndex c (radiusIndex c))-X (formalRadiusIndex c))^2
  rw [base_finitePolynomial]
  simp only [equation,Term.finitePolynomial,Term.finitePolynomial_square,centerSquares_finite,radiusDifference_finite]

theorem polynomial_degree (c :List Bool):(polynomial c).totalDegree≤degreeBudget c:=
  (totalDegree_rename_le _ _).trans (FormulaSignSlotRadialFormalBounds.total_degree c)
theorem polynomial_mass (c :List Bool):MvMass.mass (polynomial c)≤
    2^(FormulaSignSlotCenteredRadialSource.equation c).toData.size+4*d c+4:=
  (MvMass.rename_le _ _).trans (FormulaSignSlotRadialFormalBounds.mass c)

noncomputable def variableMap (c :List Bool) (a :Fin (d c)→ℝ) (r :ℝ)
    (i :Fin (dimension c)):MvPolynomial (Fin (spatial c)) ℝ:=
  match (layout c).symm i with
  | .inl j=>X j
  | .inr (.inl j)=>C (a j)
  | .inr (.inr _)=>C r
noncomputable def specialize (c :List Bool) (a :Fin (d c)→ℝ) (r :ℝ):
    MvPolynomial (Fin (dimension c)) ℤ→+*MvPolynomial (Fin (spatial c)) ℝ:=
  eval₂Hom (C.comp (Int.castRingHom ℝ)) (variableMap c a r)

private theorem specialize_base (c :List Bool) (a :Fin (d c)→ℝ) (r :ℝ)
    (p :MvPolynomial (Fin (spatial c)) ℤ):
    specialize c a r (rename (spatialIndex c) p)=p.map (Int.castRingHom ℝ):=by
  have HS:(variableMap c a r)∘spatialIndex c=fun j=>X j:=by
    funext j
    change variableMap c a r (spatialIndex c j)=X j
    rw [←layout_spatial]
    simp only [variableMap,Equiv.symm_apply_apply,FormulaSignSlotRadialFormalBounds.spatialVar]
  unfold specialize
  rw [eval₂Hom_rename,HS]
  rw [←map_eq_eval₂Hom_C_comp]

theorem specialize_spatial (c :List Bool) (a :Fin (d c)→ℝ) (r :ℝ) (i :Fin (spatial c)):
    specialize c a r (X (spatialIndex c i))=X i:=by
  simp only [specialize,MvPolynomial.eval₂Hom_X']
  rw [←layout_spatial]
  simp only [variableMap,Equiv.symm_apply_apply,FormulaSignSlotRadialFormalBounds.spatialVar]

theorem specialize_center (c :List Bool) (a :Fin (d c)→ℝ) (r :ℝ) (i :Fin (d c)):
    specialize c a r (X (formalCenterIndex c i))=C (a i):=by
  simp only [specialize,MvPolynomial.eval₂Hom_X']
  rw [←layout_center]
  simp only [variableMap,Equiv.symm_apply_apply,FormulaSignSlotRadialFormalBounds.centerVar]

theorem specialize_radius (c :List Bool) (a :Fin (d c)→ℝ) (r :ℝ):
    specialize c a r (X (formalRadiusIndex c))=C r:=by
  simp only [specialize,MvPolynomial.eval₂Hom_X']
  rw [←layout_radius]
  simp only [variableMap,Equiv.symm_apply_apply,FormulaSignSlotRadialFormalBounds.radiusVar]

theorem specialization (c :List Bool) (a :Fin (d c)→ℝ) (r :ℝ):
    specialize c a r ((equation c).finitePolynomial (dimension c))=
      FormulaSignSlotCenteredRadialLimits.polynomial c a r:=by
  rw [equation,Term.finitePolynomial,Term.finitePolynomial,Term.finitePolynomial_square,
    centerSquares_finite,radiusDifference_finite,←base_finitePolynomial]
  simp only [map_add,map_sum,map_pow,map_sub,specialize_base,specialize_spatial,specialize_center,
    specialize_radius,FormulaSignSlotCenteredRadialLimits.polynomial]
  rfl

end LeanCanny.Encoding.FormulaSignSlotRadialFormalInput
