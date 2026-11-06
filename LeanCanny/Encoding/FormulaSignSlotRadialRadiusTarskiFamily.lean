/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialRadiusHeadReader
public import LeanCanny.Algebra.MultivariateTarskiDegreeBounds
/-! # Actual formal-center/radius-window principal input

Context is pair radiusHeadContext (pair positiveDegreeMinusOne
(pair seedDegree momentWord)). Degrees are finite original-box choices;
this module does not assert that they are the specialized exact degrees.
The first coefficient variable is the upper interval endpoint, followed by
all unchanged center variables. The head never depends on the endpoint.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialRadiusTarskiFamily
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation Polynomial MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def original (c : List Bool) := pairFst c
def degreeWord (c : List Bool) := pairFst (pairSnd c)
def seedWord (c : List Bool) := pairFst (pairSnd (pairSnd c))
def momentWord (c : List Bool) := pairSnd (pairSnd (pairSnd c))
noncomputable def inputBound (c : List Bool) := FormulaSignSlotRadialRadiusHeadReader.degree (original c)
noncomputable def arity (c : List Bool) := FormulaSignSlotRadialRadiusHeadReader.arity (original c)+1
noncomputable def degree (c : List Bool) := min (Nat.fromBitsLE (degreeWord c)) (inputBound c)+1
noncomputable def seedDegree (c : List Bool) := min (Nat.fromBitsLE (seedWord c)) (inputBound c)
def moment (c : List Bool) := if momentWord c=[] then 1 else 2
noncomputable def bound (c : List Bool) := inputBound c+5
noncomputable def outputBound (c : List Bool) :=
  MultivariateTarskiDegreeBounds.principalDegreeBound (degree c) (seedDegree c) (bound c) (inputBound c) 2
noncomputable def width (c : List Bool) := (outputBound c+inputBound c+1).size
local instance radiusTarskiArityNeZero (c : List Bool) : NeZero (arity c) := ⟨by unfold arity; omega⟩
noncomputable def head (c : List Bool) : Polynomial (MvPolynomial (Fin (arity c)) ℤ) :=
  (FormulaSignSlotRadialRadiusHeadReader.polynomial (original c)).map (MvPolynomial.rename Fin.succ).toRingHom
noncomputable def window (c : List Bool) : Polynomial (MvPolynomial (Fin (arity c)) ℤ) :=
  Polynomial.X*(Polynomial.C (MvPolynomial.X 0)-Polynomial.X)
noncomputable def query (c : List Bool) := (window c)^(moment c)

theorem original_FP : original ∈ FP := pairFst_mem_FP
theorem degreeWord_FP : degreeWord ∈ FP := mem_FP_comp (f := pairSnd) (g := pairFst) pairSnd_mem_FP pairFst_mem_FP
theorem seedWord_FP : seedWord ∈ FP := mem_FP_comp (f := fun c => pairSnd (pairSnd c)) (g := pairFst)
  (mem_FP_comp (f := pairSnd) (g := pairSnd) pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP
theorem momentWord_FP : momentWord ∈ FP := mem_FP_comp (f := fun c => pairSnd (pairSnd c)) (g := pairSnd)
  (mem_FP_comp (f := pairSnd) (g := pairSnd) pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP
theorem inputBound_binary : BinaryFn inputBound := FormulaSignSlotRadialEliminantFormalMass.degree_binary.comp
  (mem_FP_comp (f := original) (g := pairFst) original_FP pairFst_mem_FP)
theorem arity_unary : UnaryFn arity :=
  (FormulaSignSlotSource.dimension_unary.comp (mem_FP_comp
    (mem_FP_comp (f := original) (g := pairFst) original_FP pairFst_mem_FP) pairFst_mem_FP)).add (UnaryFn.const 1)
private theorem binary_min {f g : List Bool → ℕ} (hf : BinaryFn f) (hg : BinaryFn g) : BinaryFn (fun c => min (f c) (g c)) :=
  (BinaryFn.ite (hf.le hg) hf hg).of_eq (fun _ => Nat.min_def.symm)
theorem degree_binary : BinaryFn degree :=
  (binary_min (BinaryFn.fromBits degreeWord_FP) inputBound_binary).add (BinaryFn.const 1)
theorem seedDegree_binary : BinaryFn seedDegree := binary_min (BinaryFn.fromBits seedWord_FP) inputBound_binary
theorem moment_binary : BinaryFn moment :=
  BinaryFn.ite ((FPPred.eq (UnaryFn.length momentWord_FP) (UnaryFn.const 0)).of_iff
    (fun _ => List.length_eq_zero_iff)) (BinaryFn.const 1) (BinaryFn.const 2)
theorem bound_binary : BinaryFn bound := inputBound_binary.add (BinaryFn.const 5)
theorem outputBound_binary : BinaryFn outputBound := by
  have HS := (((BinaryFn.const 2).mul (bound_binary.add (BinaryFn.const 1))).mul inputBound_binary).add
    ((BinaryFn.const 2).add inputBound_binary)
  exact ((degree_binary.add seedDegree_binary).add (BinaryFn.const 1)).mul ((BinaryFn.ite (inputBound_binary.le HS) HS inputBound_binary).of_eq (fun _ => Nat.max_def.symm))
theorem width_unary : UnaryFn width :=
  (UnaryFn.length ((outputBound_binary.add inputBound_binary).add (BinaryFn.const 1)).bits_mem_FP).of_eq
    (fun _ => BinaryNatCode.length_encode _)

private theorem radius_degree (c : List Bool) :
    (FormulaSignSlotRadialRadiusHeadReader.polynomial c).natDegree ≤ FormulaSignSlotRadialRadiusHeadReader.degree c := by
  change (MvPolynomial.finSuccEquiv ℤ _ (FormulaSignSlotRadialRadiusHead.polynomial _ _ _)).natDegree ≤ _
  rw [MvPolynomial.natDegree_finSuccEquiv]
  exact (MvPolynomial.degreeOf_le_totalDegree _ _).trans (FormulaSignSlotRadialRadiusHead.degree _ _ _)

theorem head_degree (c : List Bool) : (head c).natDegree ≤ inputBound c :=
  Polynomial.natDegree_map_le.trans (radius_degree (original c))
theorem window_degree (c : List Bool) : (window c).natDegree ≤ 2 := by
  unfold window
  apply Polynomial.natDegree_mul_le.trans
  have HC : (Polynomial.C (MvPolynomial.X (0 : Fin (arity c))) : Polynomial (MvPolynomial (Fin (arity c)) ℤ)).natDegree=0 := Polynomial.natDegree_C _
  have HD := Polynomial.natDegree_sub_le (Polynomial.C (MvPolynomial.X (0 : Fin (arity c))) : Polynomial (MvPolynomial (Fin (arity c)) ℤ)) Polynomial.X
  rw [HC,Polynomial.natDegree_X] at HD
  rw [Polynomial.natDegree_X]
  omega

theorem moment_le (c : List Bool) : moment c ≤ 2 := by unfold moment; split_ifs <;> omega
theorem query_degree (c : List Bool) : (query c).natDegree ≤ 4 :=
  calc
    _ ≤ moment c*(window c).natDegree := Polynomial.natDegree_pow_le
    _ ≤ 2*2 := Nat.mul_le_mul (moment_le c) (window_degree c)
    _ = 4 := by decide
theorem input_degree (c : List Bool) : ((query c)*(head c).derivative).natDegree ≤ bound c := by
  have HD := (Polynomial.natDegree_derivative_le (head c)).trans (Nat.sub_le _ _)
  have H := Polynomial.natDegree_mul_le.trans (Nat.add_le_add (query_degree c) (HD.trans (head_degree c)))
  unfold bound
  omega

noncomputable def family : FixedWidthTarskiPrincipalBits.Family where
  arity := arity
  width := width
  head := head
  query := query
  degree := degree
  bound := bound
  seedDegree := seedDegree
  degree_pos _ := Nat.zero_lt_succ _
  degree_le c := by have H := Nat.min_le_right (Nat.fromBitsLE (degreeWord c)) (inputBound c); unfold degree bound; omega
  input_degree := input_degree

private theorem rename_coefficient_degree {n : ℕ} (p : Polynomial (MvPolynomial (Fin n) ℤ))
    (D : ℕ) (H : ∀i,(p.coeff i).totalDegree ≤ D) (i : ℕ) :
    ((p.map (MvPolynomial.rename Fin.succ).toRingHom).coeff i).totalDegree ≤ D := by
  rw [Polynomial.coeff_map]
  exact (MvPolynomial.totalDegree_rename_le _ _).trans (H i)

theorem head_coefficient_degree (c : List Bool) (i : ℕ) : ((head c).coeff i).totalDegree ≤ inputBound c :=
  rename_coefficient_degree _ _ (fun i => FormulaSignSlotRadialRadiusHeadReader.radiusHeadReaderCoefficientDegree
    (FormulaSignSlotRadialRadiusHeadReader.original (original c))
    (Nat.fromBitsLE (FormulaSignSlotRadialRadiusHeadReader.tau (original c)))
    (Nat.fromBitsLE (FormulaSignSlotRadialRadiusHeadReader.eta (original c))) i) i

private theorem window_as_monomials (c : List Bool) : window c=
    Polynomial.monomial 1 (MvPolynomial.X (0 : Fin (arity c))) - Polynomial.monomial 2 1 := by
  simp only [window,←Polynomial.C_mul_X_pow_eq_monomial,pow_one,map_one,one_mul]
  ring

theorem window_coefficient_degree (c : List Bool) (i : ℕ) : ((window c).coeff i).totalDegree ≤ 1 := by
  rw [window_as_monomials,Polynomial.coeff_sub,Polynomial.coeff_monomial,Polynomial.coeff_monomial]
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · split_ifs <;> simp
  · split_ifs <;> simp

theorem query_coefficient_degree (c : List Bool) (i : ℕ) : ((query c).coeff i).totalDegree ≤ 2 := by
  unfold query moment
  split_ifs
  · simpa only [pow_one] using (window_coefficient_degree c i).trans (by omega : 1 ≤ 2)
  · rw [pow_two]
    exact MultivariateTarskiDegreeBounds.mul_coefficient (window c) (window c) 1 1
      (window_coefficient_degree c) (window_coefficient_degree c) i

theorem polynomial_degree (c : List Bool) (j : ℕ) :
    (FixedWidthTarskiPrincipalBits.polynomial family c j).totalDegree ≤ outputBound c :=
  MultivariateTarskiDegreeBounds.principal_seed _ _ _ _ _ _ _ _
    (head_coefficient_degree c) (query_coefficient_degree c)

end LeanCanny.Encoding.FormulaSignSlotRadialRadiusTarskiFamily
