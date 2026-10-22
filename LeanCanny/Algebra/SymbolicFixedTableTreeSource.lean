/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicFixedTableMixedSource
public import LeanCanny.Algebra.SymbolicFixedTableScalarMatrix

/-! # The actual symbolic supplied-table determinant family

The family is total on arbitrary metadata words. Large alpha selections take
an explicit zero branch. Leaves are one-dimensional matrices and internal
nodes are the actual encoded shifted Sylvester matrices.
-/

@[expose] public section

namespace LeanCanny.Algebra.SymbolicFixedTableTreeSource
open LeanCanny.Encoding LeanCanny.Computation
open Polynomial SymbolicScaledSquarefree SymbolicFixedTable
open SymbolicFixedTableEntryBits SymbolicFixedTableTaskRouting
open SymbolicFixedTablePolynomialTree
open BerkowitzPolynomial.TaskDispatch

attribute [local irreducible] Matrix.det shiftFamily BalancedMetadataTable.read

variable (L : List Bool → Polynomial Coefficient) (E : List Bool → ℕ)

def leftOrder (s : List Bool) : ℕ := BalancedMetadataTable.order (BalancedParameterContext.child false (pairFst s))
def rightOrder (s : List Bool) : ℕ := BalancedMetadataTable.order (BalancedParameterContext.child true (pairFst s))

noncomputable def source : Family where
  left s := node L (BalancedParameterContext.child false (pairFst s))
  right s := node L (BalancedParameterContext.child true (pairFst s))
  leftOrder := leftOrder
  rightOrder := rightOrder
  direction s := BalancedMetadataTable.direction (pairFst s)

def sourceBound (s : List Bool) : ℕ := nodeBound E (pairFst s)
def radix (q : List Bool) : ℕ := nodeBound E (nodeContext q) + 1
def alpha (q : List Bool) : ℕ := Nat.fromBitsLE (pairFst (pairSnd (pairFst q)))
def theta (q : List Bool) : ℕ := Nat.fromBitsLE (pairSnd (pairSnd (pairFst q)))
def degree (q : List Bool) : ℕ := alpha q + radix E q * theta q
def high (q : List Bool) : Bool := decide (radix E q ≤ alpha q)

def leafInput (s : List Bool) : List Bool := pair (BalancedParameterContext.original (pairFst s))
  (BinaryNatCode.encode (BalancedParameterContext.index (pairFst s)))
noncomputable def leafPolynomial (s : List Bool) : Polynomial Coefficient := L (leafInput s)

theorem child_bound (right : Bool) (p : List Bool) : nodeBound E (BalancedParameterContext.child right p) ≤ nodeBound E p := by
  unfold nodeBound innerBound
  rw [BalancedParameterContext.original_child, BalancedParameterContext.height_child]
  apply Nat.mul_le_mul_left
  exact Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)

theorem source_inner (hL : ∀ c i k, ((L (pair c (BinaryNatCode.encode i))).coeff k).natDegree ≤ E c)
    (right : Bool) (s : List Bool) (k : ℕ) :
    ((node L (BalancedParameterContext.child right (pairFst s))).coeff k).natDegree ≤ sourceBound E s :=
  (node_inner_degree L E hL _ k).trans (child_bound E right _)

theorem leaf_inner (hL : ∀ c i k, ((L (pair c (BinaryNatCode.encode i))).coeff k).natDegree ≤ E c)
    (q : List Bool) (k : ℕ) : ((leafPolynomial L (pairFst q)).coeff k).natDegree < radix E q := by
  have hp : E (BalancedParameterContext.original (nodeContext q)) ≤ nodeBound E (nodeContext q) := by
    unfold nodeBound innerBound
    exact Nat.le_mul_of_pos_right _ (by positivity)
  exact ((hL _ _ k).trans hp).trans_lt (Nat.lt_succ_self _)

theorem radix_binary (hE : BinaryFn E) : BinaryFn (radix E) := by
  have h : BinaryFn (fun q => nodeBound E (nodeContext q)) := (nodeBound_binary E hE).comp nodeContext_FP
  exact h.add (BinaryFn.const 1)

theorem alpha_binary : BinaryFn alpha := BinaryFn.fromBits
  (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairFst_mem_FP)
theorem theta_binary : BinaryFn theta := BinaryFn.fromBits
  (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP)
theorem degree_binary (hE : BinaryFn E) : BinaryFn (degree E) := alpha_binary.add ((radix_binary E hE).mul theta_binary)
theorem high_FP (hE : BinaryFn E) : (fun q => [high E q]) ∈ FP := by
  refine mem_FP_of_eq
    (BinaryNat.le_fppred (radix_binary E hE).bits_mem_FP alpha_binary.bits_mem_FP).flag_mem_FP ?_
  intro q
  simp only [high, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem leftOrder_binary : BinaryFn leftOrder := BinaryFn.fromBits
  (mem_FP_comp (mem_FP_comp pairFst_mem_FP (BalancedParameterContext.child_FP false)) (BalancedMetadataTable.read_FP false))
theorem rightOrder_binary : BinaryFn rightOrder := BinaryFn.fromBits
  (mem_FP_comp (mem_FP_comp pairFst_mem_FP (BalancedParameterContext.child_FP true)) (BalancedMetadataTable.read_FP false))
theorem direction_binary : BinaryFn (source L).direction := BinaryFn.fromBits
  (mem_FP_comp pairFst_mem_FP (BalancedMetadataTable.read_FP true))

noncomputable def pairAccess
    (hL : ∀ c i k, ((L (pair c (BinaryNatCode.encode i))).coeff k).natDegree ≤ E c) :=
  (source L).encodedMatrixAccess (radix E) (degree E) (sourceBound E)
    (source_inner L E hL false) (source_inner L E hL true) (fun _ => Nat.lt_succ_self _)

noncomputable def leafAccess
    (hL : ∀ c i k, ((L (pair c (BinaryNatCode.encode i))).coeff k).natDegree ≤ E c) :=
  SymbolicFixedTableScalarMatrix.access (leafPolynomial L) (radix E) (degree E) (leaf_inner L E hL)

noncomputable def zeroFamily : BerkowitzPolynomial.ModularFamily where
  dimension _ := 1
  modulus q := Nat.fromBitsLE (pairSnd q) + 1
  degree _ := 0
  matrix _ := 0
  modulus_ne_zero _ := by omega

noncomputable def zeroAccess : BerkowitzPolynomial.ModularAccess zeroFamily where
  dimension _ := [true]
  modulus q := BinaryNatCode.encode (Nat.fromBitsLE (pairSnd q) + 1)
  degree _ := []
  entry _ := []
  dimension_eq _ := by simp only [zeroFamily, BinaryNatCode.encode, Nat.one_bits]
  modulus_eq _ := rfl
  degree_eq _ := rfl
  entry_eq q _ _ d := by
    change [] = MatrixPower.residueBits (((0 : Polynomial (ZMod (Nat.fromBitsLE (pairSnd q) + 1)))).coeff d)
    rw [Polynomial.coeff_zero]
    rfl

noncomputable def family : BerkowitzPolynomial.ModularFamily :=
  BerkowitzPolynomial.ModularFamily.branch (high E) zeroFamily
    (BerkowitzPolynomial.ModularFamily.branch isLeaf
      (SymbolicFixedTableScalarMatrix.family (leafPolynomial L) (radix E) (degree E))
      ((source L).encodedMatrixFamily (radix E) (degree E)))

noncomputable def access
    (hL : ∀ c i k, ((L (pair c (BinaryNatCode.encode i))).coeff k).natDegree ≤ E c) :
    BerkowitzPolynomial.ModularAccess (family L E) :=
  BerkowitzPolynomial.ModularAccess.branch (high E) zeroAccess
    (BerkowitzPolynomial.ModularAccess.branch isLeaf (leafAccess L E hL) (pairAccess L E hL))

noncomputable def nodeValue (q : List Bool) : List Bool := integerResidue
  (((node L (nodeContext q)).coeff (theta q)).coeff (alpha q)) (Nat.fromBitsLE (pairSnd q) + 1)

theorem family_value
    (hL : ∀ c i k, ((L (pair c (BinaryNatCode.encode i))).coeff k).natDegree ≤ E c)
    (q : List Bool) : (family L E).value q = nodeValue L q := by
  rw [family, BerkowitzPolynomial.ModularFamily.branch_value, BerkowitzPolynomial.ModularFamily.branch_value]
  by_cases hh : high E q = true
  · simp only [hh, ite_true]
    have hg : nodeBound E (nodeContext q) < alpha q := by
      have := of_decide_eq_true hh
      dsimp only [radix] at this
      omega
    have hz := Polynomial.coeff_eq_zero_of_natDegree_lt ((node_inner_degree L E hL _ (theta q)).trans_lt hg)
    simp only [nodeValue, hz, integerResidue]
    change MatrixPower.residueBits (m := Nat.fromBitsLE (pairSnd q) + 1)
      ((Matrix.det (0 : Matrix (Fin 1) (Fin 1) (Polynomial (ZMod (Nat.fromBitsLE (pairSnd q) + 1))))).coeff 0) = _
    rw [Matrix.det_zero, Polynomial.coeff_zero]
    rw [Int.cast_zero]
  · have hf : high E q = false := Bool.eq_false_iff.mpr hh
    have ha : alpha q < radix E q := by simpa only [high, decide_eq_false_iff_not, not_le] using hf
    simp only [hf, Bool.false_eq_true, ite_false]
    have hc := PolynomialKronecker.coefficient (radix E q) (node L (nodeContext q))
      (fun k => (node_inner_degree L E hL _ k).trans_lt (Nat.lt_succ_self _)) (alpha q) (theta q) ha
    by_cases hs : isLeaf q = true
    · simp only [hs, ite_true]
      rw [SymbolicFixedTableScalarMatrix.value_eq]
      have hz : BalancedParameterContext.height (nodeContext q) = 0 := by
        have hw : BalancedParameterContext.heightWord (nodeContext q) = [] := List.isEmpty_iff.mp hs
        change (BalancedParameterContext.heightWord (nodeContext q)).length = 0
        rw [hw]
        rfl
      rw [node_zero L _ hz] at hc
      unfold nodeValue
      rw [node_zero L _ hz]
      exact congrArg (fun z => integerResidue z (Nat.fromBitsLE (pairSnd q) + 1)) hc
    · have hsf := Bool.eq_false_iff.mpr hs
      simp only [hsf, Bool.false_eq_true, ite_false]
      rw [(source L).encodedMatrix_value]
      rw [node_children L _ ((isLeaf_false_iff q).mp hsf)] at hc
      unfold nodeValue
      rw [node_children L _ ((isLeaf_false_iff q).mp hsf)]
      exact congrArg (fun z => integerResidue z (Nat.fromBitsLE (pairSnd q) + 1)) hc

theorem leafInput_FP : leafInput ∈ FP := by
  have hi : BinaryFn (fun s => BalancedParameterContext.index (pairFst s)) := BinaryFn.fromBits
    (mem_FP_comp (f := pairFst) (g := BalancedParameterContext.indexWord)
      pairFst_mem_FP BalancedParameterContext.indexWord_FP)
  exact mem_FP_pair (mem_FP_comp pairFst_mem_FP BalancedParameterContext.original_FP) hi.bits_mem_FP

def leafCoefficientQuery (q : List Bool) : List Bool :=
  pair (pair (leafInput (pairFst (pairFst q))) (pairSnd (pairFst q))) (pairSnd q)

theorem leafCoefficientQuery_FP : leafCoefficientQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) leafInput_FP)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)) pairSnd_mem_FP

theorem leaf_coefficient_space (A : SpaceFunction (coefficient L)) :
    SpaceFunction (coefficient (leafPolynomial L)) := by
  refine (A.precompose leafCoefficientQuery leafCoefficientQuery_FP).congr (funext fun q => ?_)
  simp only [Function.comp_apply, leafCoefficientQuery, coefficient, leafPolynomial, pairFst_pair, pairSnd_pair]

theorem controls
    (hL : ∀ c i k, ((L (pair c (BinaryNatCode.encode i))).coeff k).natDegree ≤ E c)
    (hE : BinaryFn E) : (access L E hL).ControlsPolyTime := by
  have hp := (source L).encodedMatrix_controls (radix E) (degree E) (sourceBound E)
    (source_inner L E hL false) (source_inner L E hL true) (fun _ => Nat.lt_succ_self _)
    leftOrder_binary rightOrder_binary (degree_binary E hE)
  have hl := SymbolicFixedTableScalarMatrix.controls (leafPolynomial L) (radix E) (degree E)
    (leaf_inner L E hL) (degree_binary E hE)
  have hz : zeroAccess.ControlsPolyTime := by
    refine ⟨constFn_mem_FP [true], ?_, constFn_mem_FP []⟩
    exact mem_FP_comp (f := pairSnd) (g := fun c => BinaryNatCode.encode (Nat.fromBitsLE c + 1))
      pairSnd_mem_FP ((BinaryFn.fromBits id_mem_FP).add (BinaryFn.const 1)).bits_mem_FP
  exact BerkowitzPolynomial.ModularAccess.branch_controls _ _ _ (high_FP E hE) hz
    (BerkowitzPolynomial.ModularAccess.branch_controls _ _ _ isLeaf_FP hl hp)

noncomputable def program
    (hL : ∀ c i k, ((L (pair c (BinaryNatCode.encode i))).coeff k).natDegree ≤ E c) : SingleCall.Program :=
  SymbolicFixedTableMixedSource.program (source L) (fun q => BinaryNatCode.encode (radix E q))
    (high E) (leafAccess L E hL).entry

theorem program_certificates
    (hL : ∀ c i k, ((L (pair c (BinaryNatCode.encode i))).coeff k).natDegree ≤ E c)
    (hE : BinaryFn E) (A : SpaceFunction (coefficient L)) :
    (program L E hL).controller.Certificates (encQ := Turing.MultiTapeTM.encBits) (encS := SingleCall.encState) := by
  exact SymbolicFixedTableMixedSource.certificates (source L) _ _ _ leftOrder_binary rightOrder_binary
    (direction_binary L) (radix_binary E hE).bits_mem_FP (high_FP E hE)
    (SymbolicFixedTableScalarMatrix.entry_space (leafPolynomial L) (radix E) (degree E)
      (leaf_inner L E hL) (radix_binary E hE) (leaf_coefficient_space L A))

theorem child_answer
    (hL : ∀ c i k, ((L (pair c (BinaryNatCode.encode i))).coeff k).natDegree ≤ E c)
    (right : Bool) (p : List Bool) :
    answer (access L E hL) (coefficientTask right p) =
      (if right then (source L).access.rightCoefficient p else (source L).access.leftCoefficient p) := by
  rw [coefficientTask, Function.comp_apply, answer_determinant, family_value L E hL]
  cases right <;> simp only [Bool.false_eq_true, ite_false, ite_true, nodeValue, childInput, matrixPacket,
    nodeContext, theta, alpha, sourceNode, sourceAlpha, pairFst_pair, pairSnd_pair,
    Family.access, Function.comp_apply, coefficient, sliceCoefficientQuery, source]

theorem program_correct
    (hL : ∀ c i k, ((L (pair c (BinaryNatCode.encode i))).coeff k).natDegree ≤ E c) (p : List Bool) :
    (program L E hL).value (answer (access L E hL)) p = (access L E hL).entry p := by
  have hl := child_answer L E hL false
  have hr := child_answer L E hL true
  change (SymbolicFixedTableMixedSource.program _ _ _ _).value _ _ = _
  rw [SymbolicFixedTableMixedSource.value_eq _ _ _ _ _ hl hr]
  rfl

theorem source_levels
    (hL : ∀ c i k, ((L (pair c (BinaryNatCode.encode i))).coeff k).natDegree ≤ E c)
    (tasks : List Bool → List Bool → Prop) :
    SourceLevels (access L E hL) (program L E hL).controller (fun _ => 1) tasks level :=
  SymbolicFixedTableMixedSource.source_levels _ _ _ _ _ tasks

end LeanCanny.Algebra.SymbolicFixedTableTreeSource
