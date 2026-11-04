/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialFormalCenter
public import LeanCanny.Algebra.MvCoefficientMass
/-! # Integer full-variable degree and mass of the formal radial spatial model

Centers and radius remain formal variables. These bounds concern the input
polynomial, not its eliminant, selected coefficients, or a native descriptor.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialFormalBounds
open ETR LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Algebra LeanCanny.Computation
open FormulaSignSlotCenteredRadialGraph FormulaSignSlotCenteredRadialLimits
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev Variables (c :List Bool):=Fin (N c+d c+1)⊕(Fin (d c)⊕Unit)
def spatialVar (c :List Bool) (i :Fin (N c+d c+1)):Variables c:=Sum.inl i
def centerVar (c :List Bool) (i :Fin (d c)):Variables c:=Sum.inr (Sum.inl i)
def radiusVar (c :List Bool):Variables c:=Sum.inr (Sum.inr ())
noncomputable def coefficientMap (c :List Bool):FormulaSignSlotRadialFormalCenter.Radius c→+*MvPolynomial (Variables c) ℤ:=
  Polynomial.eval₂RingHom (MvPolynomial.rename (R:=ℤ) (centerVar c)).toRingHom (MvPolynomial.X (radiusVar c))
noncomputable def flatten (c :List Bool):
    MvPolynomial (Fin (N c+d c+1)) (FormulaSignSlotRadialFormalCenter.Radius c)→+*MvPolynomial (Variables c) ℤ:=
  MvPolynomial.eval₂Hom (coefficientMap c) (fun i=>MvPolynomial.X (spatialVar c i))

private theorem flatten_base (c :List Bool) (p :MvPolynomial (Fin (N c+d c+1)) ℤ):
    flatten c (p.map (FormulaSignSlotRadialFormalCenter.constants c))=MvPolynomial.rename (spatialVar c) p:=by
  induction p using MvPolynomial.induction_on with
  | C z=>simp [flatten,coefficientMap,FormulaSignSlotRadialFormalCenter.constants]
  | add p q hp hq=>simp only [map_add,hp,hq]
  | mul_X p i hp=>
    simp only [map_mul,MvPolynomial.map_X,MvPolynomial.rename_X,hp]
    simp [flatten]

theorem flatten_equation (c :List Bool):flatten c (FormulaSignSlotRadialFormalCenter.polynomial c)=
    MvPolynomial.rename (spatialVar c)
      ((FormulaSignSlotCenteredRadialSource.equation c).finitePolynomial (N c+d c+1))+
    (∑i,(MvPolynomial.X (spatialVar c (centerIndex c i))-MvPolynomial.X (centerVar c i))^2)+
    (MvPolynomial.X (spatialVar c (radiusIndex c))-MvPolynomial.X (radiusVar c))^2:=by
  simp only [FormulaSignSlotRadialFormalCenter.polynomial,map_add,map_pow,map_sub,map_sum,flatten_base]
  simp [flatten,coefficientMap]

private theorem square_degree {ι :Type*} (i j :ι):
    ((MvPolynomial.X i-MvPolynomial.X j :MvPolynomial ι ℤ)^2).totalDegree≤2:=by
  apply (MvPolynomial.totalDegree_pow _ _).trans
  have H:(MvPolynomial.X i-MvPolynomial.X j :MvPolynomial ι ℤ).totalDegree≤1:=
    (MvPolynomial.totalDegree_sub _ _).trans (by simp)
  exact Nat.mul_le_mul_left 2 H

theorem total_degree (c :List Bool):
    (flatten c (FormulaSignSlotRadialFormalCenter.polynomial c)).totalDegree≤degreeBudget c:=by
  have H2:2≤degreeBudget c:=by unfold degreeBudget;omega
  rw [flatten_equation]
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le
    · exact (MvPolynomial.totalDegree_rename_le _ _).trans
        ((Term.totalDegree_finitePolynomial _ _).trans ((Term.degreeBound_le_dataSize _).trans (Nat.le_add_right _ 2)))
    · exact (MvPolynomial.totalDegree_finsetSum_le (fun i _=>square_degree
        (spatialVar c (centerIndex c i)) (centerVar c i))).trans H2
  · exact (square_degree (spatialVar c (radiusIndex c)) (radiusVar c)).trans H2

private theorem square_mass {ι :Type*} (i j :ι):
    MvMass.mass ((MvPolynomial.X i-MvPolynomial.X j :MvPolynomial ι ℤ)^2)≤4:=by
  have H:MvMass.mass (MvPolynomial.X i-MvPolynomial.X j :MvPolynomial ι ℤ)≤2:=by
    simpa only [MvMass.X] using MvMass.sub_le (MvPolynomial.X i) (MvPolynomial.X j)
  exact (MvMass.pow_le _ 2).trans (by nlinarith)

/-- Both the coefficient height charge and all variables are formal. In
particular, no absolute-value or algebraic-height bound on a real center is used. -/
theorem mass (c :List Bool):MvMass.mass (flatten c (FormulaSignSlotRadialFormalCenter.polynomial c))≤
    2^(FormulaSignSlotCenteredRadialSource.equation c).toData.size+4*d c+4:=by
  rw [flatten_equation]
  have HB:MvMass.mass (MvPolynomial.rename (spatialVar c)
      ((FormulaSignSlotCenteredRadialSource.equation c).finitePolynomial (N c+d c+1)))≤
      2^(FormulaSignSlotCenteredRadialSource.equation c).toData.size:=
    (MvMass.rename_le _ _).trans (Term.finitePolynomial_mass _ _)
  have HS:MvMass.mass (∑i :Fin (d c),
      (MvPolynomial.X (spatialVar c (centerIndex c i))-MvPolynomial.X (centerVar c i))^2)≤4*d c:=by
    apply (MvMass.sum_le Finset.univ _).trans
    apply (Finset.sum_le_sum (fun i _=>square_mass (spatialVar c (centerIndex c i)) (centerVar c i))).trans_eq
    simp [Nat.mul_comm]
  exact (MvMass.add_le _ _).trans (Nat.add_le_add
    ((MvMass.add_le _ _).trans (Nat.add_le_add HB HS)) (square_mass _ _))

/-- The proved input-model mass ceiling has an original-only binary reader. -/
theorem mass_bound_binary:BinaryFn (fun c=>
    2^(FormulaSignSlotCenteredRadialSource.equation c).toData.size+4*d c+4):=by
  have HS:UnaryFn (fun c=>(FormulaSignSlotCenteredRadialSource.equation c).toData.size):=
    (UnaryFn.length FormulaSignSlotCenteredRadialSource.equation_FP).of_eq
      (fun c=>Data.length_toBits (FormulaSignSlotCenteredRadialSource.equation c).toData)
  have HD:BinaryFn d:=BinaryFn.ofUnary FormulaSignSlotSource.dimension_unary
  exact (((BinaryFn.const 2).powUnary HS).add ((BinaryFn.const 4).mul HD)).add (BinaryFn.const 4)

end LeanCanny.Connectivity.FormulaSignSlotRadialFormalBounds
