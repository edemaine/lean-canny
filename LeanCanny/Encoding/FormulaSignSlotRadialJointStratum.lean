/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointCoefficientCatalogue
public import LeanCanny.Encoding.FormulaSignSlotRadialJointCore
public import LeanCanny.Encoding.SquareFeatureProductSource
public import LeanCanny.Algebra.SquareFeatureProductEvaluation
public import LeanCanny.ETR.FinitePolynomialPadding
/-! # The actual implicit joint coefficient stratum

Context is pair original joint header binary zero-count. One last variable
is adjoined for the reciprocal-square witness; all joint columns stay fixed.
The binary feature product is never emitted as a Term.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointStratum
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation LeanCanny.ETR MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "F" => FormulaSignSlotRadialJointCoefficientCatalogue.family

def header (c : List Bool) := pairFst c
def selected (c : List Bool) := Nat.fromBitsLE (pairSnd c)
def packet (u : List Bool) (K : ℕ) := pair u (BinaryNatCode.encode K)
noncomputable abbrev oldArity (c : List Bool) := FormulaSignSlotRadialJointLayout.dimension (header c)
noncomputable abbrev arity (c : List Bool) := oldArity c+1
noncomputable def core (c : List Bool) : MvPolynomial (Fin (arity c)) ℤ :=
  (FormulaSignSlotRadialJointCore.equation (header c)).finitePolynomial (arity c)
noncomputable def coefficient (c : List Bool) (K : ℕ) : MvPolynomial (Fin (arity c)) ℤ :=
  MvPolynomial.rename Fin.castSucc (SquareFeatureCoefficientReader.coefficient F (header c) K)
noncomputable def lower (c : List Bool) := if selected c=0 then 0 else coefficient c (selected c-1)
noncomputable def upper (c : List Bool) := coefficient c (selected c)
noncomputable def reciprocalRow (c : List Bool) := upper c * (MvPolynomial.X (Fin.last (oldArity c)))^2-1
noncomputable def polynomial (c : List Bool) := core c^2+lower c^2+reciprocalRow c^2
noncomputable def productDegree (c : List Bool) := SquareFeatureProductFamily.degree F (header c)
noncomputable def productMass (c : List Bool) := SquareFeatureProductFamily.mass F (header c)
noncomputable def coreBudget (c : List Bool) := FormulaSignSlotRadialJointCore.budget (header c)
noncomputable def degree (c : List Bool) := max (2*coreBudget c) (2*productDegree c+4)
noncomputable def baseMass (c : List Bool) := max (coreBudget c) (productMass c)
noncomputable def mass (c : List Bool) := 2*(baseMass c+1)+2
noncomputable def width (c : List Bool) := (degree c+1).size

theorem core_degree (c : List Bool) : (core c).totalDegree ≤ coreBudget c :=
  (Term.totalDegree_finitePolynomial _ _).trans (Term.degreeBound_le_dataSize _)
theorem core_mass (c : List Bool) : MvMass.mass (core c) ≤ 2^coreBudget c := Term.finitePolynomial_mass _ _
theorem coefficient_degree (c : List Bool) (K : ℕ) : (coefficient c K).totalDegree ≤ productDegree c :=
  (MvPolynomial.totalDegree_rename_le _ _).trans (SquareFeatureCoefficientReader.coefficient_degree F (header c) K)
theorem coefficient_mass (c : List Bool) (K : ℕ) : MvMass.mass (coefficient c K) ≤ 2^productMass c :=
  (MvMass.rename_le _ _).trans (SquareFeatureCoefficientReader.coefficient_mass F (header c) K)
theorem lower_degree (c : List Bool) : (lower c).totalDegree ≤ productDegree c := by
  unfold lower
  split_ifs
  · simp
  · exact coefficient_degree c _
theorem lower_mass (c : List Bool) : MvMass.mass (lower c) ≤ 2^productMass c := by
  unfold lower
  split_ifs
  · simp
  · exact coefficient_mass c _
theorem reciprocal_degree (c : List Bool) : (reciprocalRow c).totalDegree ≤ productDegree c+2 := by
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · apply (MvPolynomial.totalDegree_mul _ _).trans
    apply Nat.add_le_add (coefficient_degree c _) ?_
    simp
  · simp

theorem polynomial_degree (c : List Bool) : (polynomial c).totalDegree ≤ degree c := by
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le
    · exact ((MvPolynomial.totalDegree_pow _ 2).trans (Nat.mul_le_mul_left 2 (core_degree c))).trans (le_max_left _ _)
    · exact ((MvPolynomial.totalDegree_pow _ 2).trans (Nat.mul_le_mul_left 2 (lower_degree c))).trans
        ((by omega : 2*productDegree c ≤ 2*productDegree c+4).trans (le_max_right _ _))
  · have H := (MvPolynomial.totalDegree_pow (reciprocalRow c) 2).trans (Nat.mul_le_mul_left 2 (reciprocal_degree c))
    exact H.trans (by unfold degree; omega)

theorem reciprocal_mass (c : List Bool) : MvMass.mass (reciprocalRow c) ≤ 2^(baseMass c+1) := by
  have HM := (MvMass.mul_le (upper c) ((MvPolynomial.X (Fin.last (oldArity c)))^2)).trans
    (Nat.mul_le_mul (coefficient_mass c _) (MvMass.pow_le _ 2))
  simp only [MvMass.X,one_pow,Nat.mul_one] at HM
  have HL : 2^productMass c ≤ 2^baseMass c := Nat.pow_le_pow_right (by decide) (le_max_right _ _)
  have HS0 := MvMass.sub_le (upper c * (MvPolynomial.X (Fin.last (oldArity c)))^2) 1
  simp only [MvMass.one] at HS0
  have HS := HS0.trans (Nat.add_le_add_right (HM.trans HL) 1)
  have H1 : 1 ≤ 2^baseMass c := Nat.one_le_two_pow
  exact HS.trans (by rw [pow_succ]; omega)

theorem polynomial_mass (c : List Bool) : MvMass.mass (polynomial c) ≤ 2^mass c := by
  let B := baseMass c+1
  have HC : MvMass.mass (core c) ≤ 2^B := (core_mass c).trans
    (Nat.pow_le_pow_right (by decide) (by dsimp [B,baseMass]; omega))
  have HL : MvMass.mass (lower c) ≤ 2^B := (lower_mass c).trans
    (Nat.pow_le_pow_right (by decide) (by dsimp [B,baseMass]; omega))
  have HR : MvMass.mass (reciprocalRow c) ≤ 2^B := reciprocal_mass c
  have HS (p : MvPolynomial (Fin (arity c)) ℤ) (H : MvMass.mass p ≤ 2^B) :
      MvMass.mass (p^2) ≤ 2^(2*B) := by
    apply (MvMass.pow_le p 2).trans
    simpa only [←pow_mul,Nat.mul_comm B 2] using Nat.pow_le_pow_left H 2
  have HA := (MvMass.add_le (core c^2+lower c^2) (reciprocalRow c^2)).trans
    (Nat.add_le_add (MvMass.add_le _ _) (HS _ HR))
  have HB := HA.trans (Nat.add_le_add (Nat.add_le_add (HS _ HC) (HS _ HL)) le_rfl)
  change MvMass.mass (polynomial c) ≤ _ at HB
  have Hsum : 2^(2*B)+2^(2*B)+2^(2*B) ≤ 2^(2*B+2) := by
    rw [pow_add]
    norm_num
    omega
  exact HB.trans Hsum

theorem header_FP : header ∈ FP := pairFst_mem_FP
theorem selected_binary : BinaryFn selected := BinaryFn.fromBits pairSnd_mem_FP
theorem oldArity_unary : UnaryFn oldArity := FormulaSignSlotRadialJointLayout.dimension_unary.comp header_FP
theorem arity_unary : UnaryFn arity := oldArity_unary.add (UnaryFn.const 1)
theorem coreBudget_unary : UnaryFn coreBudget := FormulaSignSlotRadialJointCore.budget_unary.comp header_FP
theorem productDegree_binary : BinaryFn productDegree :=
  (SquareFeatureProductFamily.degree_binary F FormulaSignSlotRadialJointCoefficientCatalogue.access).comp header_FP
theorem productMass_binary : BinaryFn productMass :=
  (SquareFeatureProductFamily.mass_binary F FormulaSignSlotRadialJointCoefficientCatalogue.access).comp header_FP
theorem degree_binary : BinaryFn degree := by
  have HC := (BinaryFn.const 2).mul (BinaryFn.ofUnary coreBudget_unary)
  have HP := ((BinaryFn.const 2).mul productDegree_binary).add (BinaryFn.const 4)
  exact (BinaryFn.ite (HC.le HP) HP HC).of_eq (fun _ => Nat.max_def.symm)
theorem baseMass_binary : BinaryFn baseMass :=
  (BinaryFn.ite ((BinaryFn.ofUnary coreBudget_unary).le productMass_binary)
    productMass_binary (BinaryFn.ofUnary coreBudget_unary)).of_eq (fun _ => Nat.max_def.symm)
theorem mass_binary : BinaryFn mass := ((BinaryFn.const 2).mul (baseMass_binary.add (BinaryFn.const 1))).add (BinaryFn.const 2)
theorem width_unary : UnaryFn width :=
  (UnaryFn.length (degree_binary.add (BinaryFn.const 1)).bits_mem_FP).of_eq
    (fun _ => BinaryNatCode.length_encode _)
theorem degree_fit (c : List Bool) : degree c < 2^width c := (Nat.lt_succ_self _).trans (Nat.lt_size_self _)
noncomputable def source : IntegralFramedBankPolynomialModel.Source where
  arity := arity
  width := width
  degree := degree
  mass := mass
  polynomial := polynomial
  fit c i := (MvPolynomial.degreeOf_le_totalDegree _ i).trans_lt ((polynomial_degree c).trans_lt (degree_fit c))
  polynomial_degree := polynomial_degree
  polynomial_mass := polynomial_mass

noncomputable def oldPoint (c : List Bool) (y : Fin (arity c) → ℝ) : Fin (oldArity c) → ℝ :=
  fun i => y i.castSucc
noncomputable def values (c : List Bool) (y : Fin (arity c) → ℝ) :=
  SquareFeatureProductEvaluation.values F (header c) (oldPoint c y)

theorem eval_castSucc {n : ℕ} (p : MvPolynomial (Fin n) ℤ) (y : Fin (n+1) → ℝ) :
    (MvPolynomial.rename Fin.castSucc p).eval₂ (Int.castRingHom ℝ) y=
      p.eval₂ (Int.castRingHom ℝ) (fun i => y i.castSucc) := by
  rw [MvPolynomial.eval₂_rename]
  rfl

theorem coefficient_eval (c : List Bool) (K : ℕ) (y : Fin (arity c) → ℝ) :
    (coefficient c K).eval₂ (Int.castRingHom ℝ) y=(SquareFeatureProduct.polynomial (values c y)).coeff K :=
  (eval_castSucc (SquareFeatureCoefficientReader.coefficient F (header c) K) y).trans
    (SquareFeatureProductEvaluation.coefficient F (header c) (oldPoint c y) K)

theorem core_eval (c : List Bool) (y : Fin (arity c) → ℝ) :
    (core c).eval₂ (Int.castRingHom ℝ) y=
      (FormulaSignSlotRadialJointCore.equation (header c)).eval (Formula.extend (oldPoint c y)) := by
  rw [core,Term.eval_finitePolynomial]
  apply Term.eval_congr
  intro i hi
  have HI := hi.trans_le (FormulaSignSlotRadialJointCore.scope (header c))
  have HJ : i<arity c := HI.trans_le (Nat.le_succ _)
  simp only [Formula.extend,dite_eq_left HI,dite_eq_left HJ,oldPoint]
  congr 1

theorem zero_iff (c : List Bool) (y : Fin (arity c) → ℝ) :
    (polynomial c).eval₂ (Int.castRingHom ℝ) y=0 ↔
      (FormulaSignSlotRadialJointCore.equation (header c)).eval (Formula.extend (oldPoint c y))=0 ∧
        SquareFeatureProduct.Certificate (values c y) (selected c) (y (Fin.last (oldArity c))) := by
  have HC := core_eval c y
  have HL : (lower c).eval₂ (Int.castRingHom ℝ) y=
      if selected c=0 then 0 else (SquareFeatureProduct.polynomial (values c y)).coeff (selected c-1) := by
    unfold lower
    split_ifs <;> simp only [MvPolynomial.eval₂_zero,coefficient_eval]
  have HU := coefficient_eval c (selected c) y
  change (core c^2+lower c^2+reciprocalRow c^2).eval₂ _ _=0 ↔ _
  simp only [MvPolynomial.eval₂_add,MvPolynomial.eval₂_pow,reciprocalRow,MvPolynomial.eval₂_sub,
    MvPolynomial.eval₂_mul,MvPolynomial.eval₂_X,MvPolynomial.eval₂_one,upper,HC,HL,HU]
  rw [show _+_+_=((FormulaSignSlotRadialJointCore.equation (header c)).eval (Formula.extend (oldPoint c y)))^2+
      SquareFeatureProduct.equation (values c y) (selected c) (y (Fin.last (oldArity c))) by
        unfold SquareFeatureProduct.equation; ring]
  rw [add_eq_zero_iff_of_nonneg (sq_nonneg _) (by unfold SquareFeatureProduct.equation; positivity),
    sq_eq_zero_iff,SquareFeatureProduct.equation_zero_iff]

end LeanCanny.Encoding.FormulaSignSlotRadialJointStratum
