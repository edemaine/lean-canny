/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.ImplicitSourceCoerciveRows
/-! # Canonical bivariate coercive Gram readers for an implicit source -/
@[expose] public section
namespace LeanCanny.Encoding.ImplicitSourceCoerciveBoxGram
open LeanCanny.Algebra LeanCanny.Computation Polynomial MatrixPower FixedWidthPolynomial
open IntegralFramedBankPolynomialModel (Source)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def polynomialAt (S : Source) (u : List Bool) (i : ℕ) : (ℤ[X])[X] :=
  if hi : i<S.arity u then CoerciveBoxGramEliminant.polynomial (S.polynomial u) (S.degree u) ⟨i,hi⟩ else 1
noncomputable def original (S : Source) (z : List Bool) : (ℤ[X])[X] := polynomialAt S (pairFst z) (Nat.fromBitsLE (pairSnd z))
theorem original_packet (S : Source) (u : List Bool) (i : ℕ) :
    original S (pair u (BinaryNatCode.encode i))=polynomialAt S u i := by
  simp only [original,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]

theorem original_ne_zero (S : Source) (z : List Bool) : original S z ≠ 0 := by
  unfold original polynomialAt
  split_ifs
  · exact CoerciveBoxGramEliminant.ne_zero _ _ (S.polynomial_degree _) _
  · exact one_ne_zero

theorem original_degree (S : Source) (z : List Bool) : (original S z).natDegree ≤ degreeBound S (pairFst z) := by
  unfold original polynomialAt
  split_ifs
  · exact CoerciveBoxGramEliminant.outer_degree _ _ (S.polynomial_degree _) _
  · simp only [natDegree_one, Nat.zero_le]

theorem original_inner_degree (S : Source) (z : List Bool) (k : ℕ) :
    ((original S z).coeff k).natDegree ≤ degreeBound S (pairFst z) := by
  unfold original polynomialAt
  split_ifs
  · exact CoerciveBoxGramEliminant.inner_degree _ _ (S.polynomial_degree _) _ _
  · rw [coeff_one]; split_ifs <;> simp only [natDegree_one, natDegree_zero, Nat.zero_le]

theorem original_mass (S : Source) (z : List Bool) :
    NestedMass.mass (original S z) ≤ 2^massExponent S (pairFst z) := by
  unfold original polynomialAt
  split_ifs
  · exact CoerciveBoxGramEliminant.mass_le_pow _ _ _ (S.polynomial_degree _) (S.polynomial_mass _) _
  · change NestedMass.mass (Polynomial.C (Polynomial.C (1 : ℤ))) ≤ _
    simpa only [NestedMass.C, coefficientMass_C, Int.natAbs_one] using Nat.one_le_two_pow (n := massExponent S (pairFst z))

namespace Determinant
def layout (S : Source) (input : List Bool → List Bool) : MacaulayFullBoxBits.Layout where
  arity c := S.arity (input c)+1
  width c := rowWidth S (input c)
  level c := S.arity (input c)*(2*S.degree (input c))+1
  degree c i := if i=0 then 1 else 2*S.degree (input c)+1

theorem controls (S : Source) (A : IntegralFramedBankPolynomialModel.Access S)
    (input : List Bool → List Bool) (hi : input ∈ FP) : (layout S input).Controls := by
  have HN := A.arity.comp hi
  have HD : BinaryFn (S.degree ∘ input) := A.degree.comp hi
  refine ⟨HN.add (UnaryFn.const 1), (rowWidth_unary S A).comp hi,
    ((BinaryFn.ofUnary HN).mul ((BinaryFn.const 2).mul HD)).add (BinaryFn.const 1), ?_⟩
  exact BinaryFn.ite ((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 0)) (BinaryFn.const 1)
    ((((BinaryFn.const 2).mul HD).add (BinaryFn.const 1)).comp pairFst_mem_FP)

theorem degrees (S : Source) (input : List Bool → List Bool) (c : List Bool) :
    (fun i : Fin ((layout S input).arity c) => (layout S input).degree c i.val) =
      CoerciveCriticalHomogenization.finDegree (n := S.arity (input c)) (S.degree (input c)) := by
  funext i
  exact (CoerciveHomogeneousLayout.finDegree_eq _ i).symm

theorem level_eq (S : Source) (input : List Bool → List Bool) (c : List Bool) :
    (layout S input).level c = Macaulay.level (fun i : Fin ((layout S input).arity c) => (layout S input).degree c i.val) := by
  rw [degrees]
  change S.arity (input c)*(2*S.degree (input c))+1 =
    Macaulay.level (CoerciveCriticalHomogenization.finDegree (n := S.arity (input c)) (S.degree (input c)))
  unfold Macaulay.level CoerciveCriticalHomogenization.finDegree CoerciveCriticalHomogenization.nativeDegree
  rw [← Equiv.sum_comp CoerciveCriticalHomogenization.layout]
  simp only [Equiv.symm_apply_apply, Fintype.sum_option, Nat.sub_self, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.add_sub_cancel, zero_add]

noncomputable def family (S : Source) (input : List Bool → List Bool) (coordinate : List Bool → ℕ) (c : List Bool) :
    Fin ((layout S input).arity c) → MvPolynomial (Fin ((layout S input).arity c)) CoerciveCriticalHomogenization.Coefficient :=
  if hc : coordinate c<S.arity (input c) then
    CoerciveCriticalHomogenization.finSystem (S.polynomial (input c)) (S.degree (input c)) ⟨coordinate c,hc⟩ else fun _ => 0

theorem family_inner_degree (S : Source) (input : List Bool → List Bool) (coordinate : List Bool → ℕ)
    (c : List Bool) (i : Fin ((layout S input).arity c)) (e) (k : ℕ) :
    ((((family S input coordinate c i).coeff e).coeff k).natDegree) ≤ 1 := by
  unfold family
  split_ifs
  · exact (CoerciveCriticalBounds.finSystem_entryBounds _ _ (S.polynomial_degree _) _ i e).innerDegree k
  · simp

theorem coefficient_packet (S : Source) (input modulus : List Bool → List Bool) (coordinate : List Bool → ℕ)
    (c : List Bool) (j : Fin ((layout S input).arity c)) (r u v : ℕ) :
    Rows.program S input modulus coordinate (Rows.packet c j.val r u v) =
      MacaulayFullBoxBits.scalar modulus c u v ((family S input coordinate c j).coeff
        (RationalSubstitution.Indexed.exponentVector ((layout S input).arity c)
          (FixedWidthPolynomial.entry ((layout S input).width c) r))) := by
  by_cases hc : coordinate c<S.arity (input c)
  · unfold family
    rw [dite_eq_left hc]
    exact Rows.program_packet S input modulus coordinate c hc j r u v
  · have HV : ¬Rows.valid S input coordinate (Rows.packet c j.val r u v) := by
      simp only [Rows.valid,Rows.context,Rows.packet,pairFst_pair,not_and]
      exact fun H => False.elim (hc H)
    rw [Rows.program,ite_eq_right HV,family,dite_eq_right hc]
    exact (MacaulayFullBoxBits.scalar_zero modulus c u v).symm

theorem determinant_eq (S : Source) (input : List Bool → List Bool) (coordinate : List Bool → ℕ)
    (c : List Bool) (hc : coordinate c<S.arity (input c)) :
    ProjectiveBoxGramEliminant.polynomial (family S input coordinate c)
      (fun i => (layout S input).degree c i.val) ((layout S input).width c) =
      CoerciveBoxGramEliminant.polynomial (S.polynomial (input c)) (S.degree (input c)) ⟨coordinate c,hc⟩ := by
  rw [family,dite_eq_left hc,degrees]
  rfl
end Determinant

noncomputable def residueAt (S : Source) (u : List Bool) (i : ℕ) (modulus : List Bool) (inner outer : ℕ) :=
  residueBits ((((polynomialAt S u i).coeff outer).coeff inner : ℤ) : ZMod (Nat.fromBitsLE modulus+1))

noncomputable def coefficient (S : Source) (input : List Bool → List Bool)
    (coordinate inner outer : List Bool → ℕ) (modulus : List Bool → List Bool) (c : List Bool) :=
  residueAt S (input c) (coordinate c) (modulus c) (inner c) (outer c)

private theorem one_coefficient (u v : ℕ) : (((1 : (ℤ[X])[X]).coeff v).coeff u) =
    if u=0 ∧ v=0 then 1 else 0 := by
  by_cases hv : v=0
  · subst v
    rw [Polynomial.coeff_one_zero,Polynomial.coeff_one]
    simp only [and_true]
  · rw [Polynomial.coeff_one,ite_eq_right hv,Polynomial.coeff_zero]
    simp only [hv,and_false,ite_false]

theorem coefficient_evaluator (S : Source) (A : IntegralFramedBankPolynomialModel.Access S)
    (input : List Bool → List Bool) (coordinate inner outer : List Bool → ℕ) (modulus : List Bool → List Bool)
    (hi : input ∈ FP) (hc : BinaryFn coordinate) (hu : BinaryFn inner) (hv : BinaryFn outer) (hm : modulus ∈ FP) :
    SpaceFunction (coefficient S input coordinate inner outer modulus) := by
  have E := MacaulayFullBoxBits.determinantEvaluator (Determinant.layout S input) (Determinant.controls S A input hi)
    modulus (fun c => BinaryNatCode.encode (inner c)) (fun c => BinaryNatCode.encode (outer c))
    (fun _ => BinaryNatCode.encode 1) (Rows.program S input modulus coordinate)
    (Determinant.family S input coordinate) (Determinant.level_eq S input)
    (by intro c i e k; change _ ≤ 1; exact Determinant.family_inner_degree S input coordinate c i e k)
    (fun c i r u v => Determinant.coefficient_packet S input modulus coordinate c i r u v)
    (Rows.program_evaluator S A input modulus coordinate hi hm hc) hm hu.bits_mem_FP hv.bits_mem_FP (constFn_mem_FP _)
  have HG := hc.lt ((BinaryFn.ofUnary A.arity).comp hi)
  let one := fun c => if inner c=0 ∧ outer c=0 then ArithmeticBits.one (BinaryNat.succ (modulus c)) else []
  have HS : (fun c => BinaryNat.succ (modulus c)) ∈ FP := mem_FP_comp (f := modulus) (g := BinaryNat.succ) hm BinaryNat.succ_mem_FP
  have EO : one ∈ FP := ((hu.eq (BinaryFn.const 0)).and (hv.eq (BinaryFn.const 0))).ite_mem_FP
    (mem_FP_comp (f := fun c => BinaryNat.succ (modulus c)) (g := ArithmeticBits.one) HS ArithmeticBits.one_mem_FP) (constFn_mem_FP [])
  refine (SpaceFunction.branch (fun c => decide (coordinate c<S.arity (input c))) HG.flag_mem_FP E
    (SpaceFunction.ofFP one EO)).congr (funext fun c => ?_)
  unfold coefficient residueAt
  by_cases H : coordinate c<S.arity (input c)
  · simp only [H,decide_true,ite_true]
    rw [MacaulayFullBoxBits.determinantValue_eq,Determinant.determinant_eq S input coordinate c H]
    simp only [polynomialAt,BinaryNatCode.encode,Nat.fromBitsLE_bits,dite_eq_left H,
      MacaulayFullBoxBits.scalar]
  · simp only [H,decide_false,Bool.false_eq_true,ite_false,one]
    rw [polynomialAt,dite_eq_right H,one_coefficient]
    by_cases hz : inner c=0 ∧ outer c=0
    · rw [ite_eq_left hz,ite_eq_left hz]
      change ArithmeticBits.one (BinaryNat.succ (modulus c)) = residueBits (1 : ZMod (Nat.fromBitsLE (modulus c)+1))
      rw [BinaryNat.succ_eq_bits]
      exact ArithmeticBits.one_residueBits _
    · simp only [hz,ite_false,Int.cast_zero,residueBits,ZMod.val_zero,BinaryNatCode.encode,Nat.zero_bits]

noncomputable def reader (S : Source) (A : IntegralFramedBankPolynomialModel.Access S) : CertifiedPolynomial.BivariateReader (original S) where
  coefficient := coefficient S (fun q => pairFst (pairFst (pairFst q)))
    (fun q => Nat.fromBitsLE (pairSnd (pairFst (pairFst q))))
    (fun q => Nat.fromBitsLE (pairFst (pairSnd q))) (fun q => Nat.fromBitsLE (pairSnd (pairSnd q)))
    (fun q => pairSnd (pairFst q))
  evaluator := coefficient_evaluator S A _ _ _ _ _ (by polytime) (BinaryFn.fromBits (by polytime))
    (BinaryFn.fromBits (by polytime)) (BinaryFn.fromBits (by polytime)) (by polytime)
  coefficient_eq q u v := by
    let z := pair q (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))
    change residueAt S (pairFst (pairFst (pairFst z)))
      (Nat.fromBitsLE (pairSnd (pairFst (pairFst z)))) (pairSnd (pairFst z))
      (Nat.fromBitsLE (pairFst (pairSnd z))) (Nat.fromBitsLE (pairSnd (pairSnd z))) =
      residueAt S (pairFst (pairFst q)) (Nat.fromBitsLE (pairSnd (pairFst q))) (pairSnd q) u v
    simp only [z,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]

end LeanCanny.Encoding.ImplicitSourceCoerciveBoxGram
