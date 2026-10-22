/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.PolynomialDeterminantInteger
public import LeanCanny.Algebra.ScaledPolynomialQuotientSpace
public import LeanCanny.Algebra.SymbolicFixedTableEntrySpace

/-! # Native symbolic scaled quotient coefficients

The Cramer determinant remains over ℤ[alpha]. Its entry readers select a single
alpha coefficient of a divisor or dividend. Each original reader's workspace
is retained by native composition.
-/
@[expose] public section
namespace LeanCanny.Algebra.SymbolicScaledQuotientBits
open Polynomial SymbolicFixedTable
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
attribute [local irreducible] Matrix.det
set_option backward.isDefEq.respectTransparency false

structure Family where
  divisor : List Bool → Polynomial (Polynomial ℤ)
  dividend : List Bool → Polynomial (Polynomial ℤ)
  divisorDegree : List Bool → ℕ
  quotientDegree : List Bool → ℕ

noncomputable abbrev coefficient := SymbolicFixedTableEntryBits.coefficient

def original (q : List Bool) : List Bool := pairFst (pairFst q)
def modulus (q : List Bool) : List Bool := pairSnd (pairFst q)
def alpha (q : List Bool) : List Bool := pairFst (pairSnd q)
def target (q : List Bool) : List Bool := pairSnd (pairSnd q)
theorem original_FP : original ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem modulus_FP : modulus ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
theorem alpha_FP : alpha ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem target_FP : target ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP

noncomputable def Family.sliced (F : Family) : ScaledQuotientBits.Family where
  divisor c := slice (F.divisor (pairFst c)) (Nat.fromBitsLE (pairSnd c))
  dividend c := slice (F.dividend (pairFst c)) (Nat.fromBitsLE (pairSnd c))
  divisorDegree c := F.divisorDegree (pairFst c)
  quotientDegree c := F.quotientDegree (pairFst c)

noncomputable def Family.access (F : Family) : ScaledQuotientBits.Access F.sliced where
  divisorDegree c := BinaryNatCode.encode (F.divisorDegree (pairFst c))
  quotientDegree c := BinaryNatCode.encode (F.quotientDegree (pairFst c))
  divisorCoefficient := coefficient F.divisor ∘ SymbolicFixedTableEntryBits.sliceCoefficientQuery
  dividendCoefficient := coefficient F.dividend ∘ SymbolicFixedTableEntryBits.sliceCoefficientQuery
  divisorDegree_eq _ := rfl
  quotientDegree_eq _ := rfl
  divisor_eq q k := by
    simp only [Function.comp_apply, coefficient, SymbolicFixedTableEntryBits.coefficient,
      SymbolicFixedTableEntryBits.sliceCoefficientQuery, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, Family.sliced, slice_coeff]
    rfl
  dividend_eq q k := by
    simp only [Function.comp_apply, coefficient, SymbolicFixedTableEntryBits.coefficient,
      SymbolicFixedTableEntryBits.sliceCoefficientQuery, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, Family.sliced, slice_coeff]
    rfl

theorem Family.access_controls (F : Family) (hd : BinaryFn F.divisorDegree)
    (hL : BinaryFn F.quotientDegree) : F.access.ControlsPolyTime :=
  ⟨mem_FP_comp (f := pairFst) (g := fun c => BinaryNatCode.encode (F.divisorDegree c)) pairFst_mem_FP hd.bits_mem_FP,
    mem_FP_comp (f := pairFst) (g := fun c => BinaryNatCode.encode (F.quotientDegree c)) pairFst_mem_FP hL.bits_mem_FP⟩

/-- `q / row / column / alpha degree` becomes an integer entry query on one
coefficient slice. The requested quotient coefficient stays in the context. -/
def entryQuery (y : List Bool) : List Bool :=
  let q := pairFst y
  let source := pair (original q) (pairSnd (pairSnd (pairSnd y)))
  let request := pair (pair source (modulus q)) (target q)
  pair request (pair (pairFst (pairSnd y)) (pairFst (pairSnd (pairSnd y))))

theorem entryQuery_FP : entryQuery ∈ FP := by
  have hq := pairFst_mem_FP
  have ha := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP
  exact mem_FP_pair
    (mem_FP_pair (mem_FP_pair (mem_FP_pair (mem_FP_comp (f := pairFst) (g := original) hq original_FP) ha)
      (mem_FP_comp (f := pairFst) (g := modulus) hq modulus_FP)) (mem_FP_comp (f := pairFst) (g := target) hq target_FP))
    (mem_FP_pair (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
      (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP))

noncomputable def Family.entry (F : Family) : List Bool → List Bool :=
  ScaledQuotientBits.Access.entry F.access ∘ entryQuery

theorem Family.entryEvaluator (F : Family) (hd : BinaryFn F.divisorDegree) (hL : BinaryFn F.quotientDegree)
    (P : SpaceFunction (coefficient F.divisor)) (Q : SpaceFunction (coefficient F.dividend)) :
    SpaceFunction F.entry :=
  (ScaledQuotientBits.Access.entryEvaluator F.access (F.access_controls hd hL)
    (P.precompose _ SymbolicFixedTableEntryBits.sliceCoefficientQuery_FP)
    (Q.precompose _ SymbolicFixedTableEntryBits.sliceCoefficientQuery_FP)).precompose _ entryQuery_FP

noncomputable def Family.matrix (F : Family) (q : List Bool) :
    Matrix (Fin (F.quotientDegree (original q)+1)) (Fin (F.quotientDegree (original q)+1)) (Polynomial ℤ) :=
  (ScaledPolynomialQuotient.matrix (F.divisor (original q)) (F.divisorDegree (original q))
    (F.quotientDegree (original q))).updateCol
      ⟨min (Nat.fromBitsLE (target q)) (F.quotientDegree (original q)), Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
      (ScaledPolynomialQuotient.input (F.dividend (original q)) (F.divisorDegree (original q))
        (F.quotientDegree (original q)))

theorem Family.entry_correct (F : Family) (q : List Bool)
    (i j : Fin (F.quotientDegree (original q)+1)) (u : ℕ) :
    F.entry (pair q (pair (BinaryNatCode.encode i.val) (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode u)))) =
      residueBits ((((F.matrix q i j).coeff u) : ℤ) : ZMod (Nat.fromBitsLE (modulus q)+1)) := by
  let z := pair (pair (pair (original q) (BinaryNatCode.encode u)) (modulus q)) (target q)
  let i' : Fin (F.sliced.quotientDegree (ScaledQuotientBits.context z)+1) :=
    ⟨i.val, by simpa only [z, Family.sliced, ScaledQuotientBits.context, pairFst_pair] using i.isLt⟩
  let j' : Fin (F.sliced.quotientDegree (ScaledQuotientBits.context z)+1) :=
    ⟨j.val, by simpa only [z, Family.sliced, ScaledQuotientBits.context, pairFst_pair] using j.isLt⟩
  have h := ScaledQuotientBits.Access.entry_packet F.access z i' j'
  let M := (ScaledPolynomialQuotient.matrix (F.sliced.divisor (ScaledQuotientBits.context z))
    (F.sliced.divisorDegree (ScaledQuotientBits.context z)) (F.sliced.quotientDegree (ScaledQuotientBits.context z))).updateCol
      (ScaledQuotientBits.selected F.sliced z)
      (ScaledPolynomialQuotient.input (F.sliced.dividend (ScaledQuotientBits.context z))
        (F.sliced.divisorDegree (ScaledQuotientBits.context z)) (F.sliced.quotientDegree (ScaledQuotientBits.context z)))
  change _ = PrincipalCoefficientBits.integerResidue (M i' j') (ScaledQuotientBits.modulus z) at h
  dsimp only [M] at h
  rw [ScaledPolynomialQuotient.selected_entry] at h
  simp only [ScaledQuotientBits.selected, Fin.ext_iff, Family.sliced, slice_coeff,
    z, ScaledQuotientBits.context, ScaledQuotientBits.modulus, ScaledQuotientBits.modulusWord,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, i', j'] at h
  unfold Family.entry
  simp only [Function.comp_apply]
  have hquery : entryQuery (pair q (pair (BinaryNatCode.encode i.val)
      (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode u)))) =
      pair z (pair (BinaryNatCode.encode i'.val) (BinaryNatCode.encode j'.val)) := by
    simp only [entryQuery, pairFst_pair, pairSnd_pair, z, i', j']
  rw [hquery]
  simp only [z, i', j', BinaryNatCode.encode]
  rw [h]
  change residueBits ((_ : ℤ) : ZMod (Nat.fromBitsLE (modulus q)+1)) = _
  rw [Family.matrix, ScaledPolynomialQuotient.selected_entry]
  simp only [Fin.ext_iff]
  split_ifs <;> simp only [coeff_zero]

noncomputable def Family.value (F : Family) : List Bool → List Bool :=
  coefficient (fun c => ScaledPolynomialQuotient.quotient (F.divisor c) (F.dividend c)
    (F.divisorDegree c) (F.quotientDegree c))

theorem Family.evaluator (F : Family) (B : List Bool → ℕ)
    (hP : ∀ c k, ((F.divisor c).coeff k).natDegree ≤ B c)
    (hQ : ∀ c k, ((F.dividend c).coeff k).natDegree ≤ B c)
    (hd : BinaryFn F.divisorDegree) (hL : BinaryFn F.quotientDegree) (hB : BinaryFn B)
    (P : SpaceFunction (coefficient F.divisor)) (Q : SpaceFunction (coefficient F.dividend)) :
    SpaceFunction F.value := by
  let N := fun q => F.quotientDegree (original q)+1
  let bound := fun q => BinaryNatCode.encode (B (original q))
  have hmat q (i j : Fin (N q)) : (F.matrix q i j).natDegree ≤ Nat.fromBitsLE (bound q) := by
    simp only [bound, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    rw [Family.matrix, ScaledPolynomialQuotient.selected_entry]
    split_ifs
    · exact hQ _ _
    · exact hP _ _
    · simp
  have E := PolynomialDeterminantBits.evaluator N modulus alpha bound F.entry F.matrix
    (fun _ => Nat.succ_pos _) hmat F.entry_correct (F.entryEvaluator hd hL P Q)
    (mem_FP_comp (f := original) (g := fun c => BinaryNatCode.encode (F.quotientDegree c+1)) original_FP (hL.add (BinaryFn.const 1)).bits_mem_FP) modulus_FP alpha_FP
    (mem_FP_comp (f := original) (g := fun c => BinaryNatCode.encode (B c)) original_FP hB.bits_mem_FP)
  have hwithin := BinaryNat.le_fppred target_FP (mem_FP_comp (f := original) (g := fun c => BinaryNatCode.encode (F.quotientDegree c)) original_FP hL.bits_mem_FP)
  have R := SpaceFunction.branch (fun q => decide (Nat.fromBitsLE (target q) ≤ F.quotientDegree (original q)))
    (hwithin.of_iff (fun q => by simp only [Function.comp_apply, BinaryNatCode.encode, Nat.fromBitsLE_bits])).flag_mem_FP E
    (SpaceFunction.ofFP _ (constFn_mem_FP []))
  refine R.congr (funext fun q => ?_)
  simp only [decide_eq_true_eq, Family.value, coefficient, SymbolicFixedTableEntryBits.coefficient]
  change (if Nat.fromBitsLE (target q) ≤ F.quotientDegree (original q) then
    PolynomialDeterminantBits.value N modulus alpha F.matrix q else []) =
      SymbolicFixedTableEntryBits.integerResidue
        (((ScaledPolynomialQuotient.quotient (F.divisor (original q)) (F.dividend (original q))
          (F.divisorDegree (original q)) (F.quotientDegree (original q))).coeff
            (Nat.fromBitsLE (target q))).coeff (Nat.fromBitsLE (alpha q)))
        (Nat.fromBitsLE (modulus q)+1)
  rw [ScaledPolynomialQuotient.quotient_coeff]
  by_cases hv : Nat.fromBitsLE (target q) ≤ F.quotientDegree (original q)
  · rw [ite_eq_left hv, dite_eq_left (by omega)]
    unfold PolynomialDeterminantBits.value
    congr 3
    unfold Family.matrix
    simp only [min_eq_left hv]
  · rw [ite_eq_right hv, dite_eq_right (by omega)]
    simp only [coeff_zero, SymbolicFixedTableEntryBits.integerResidue, residueBits,
      Int.cast_zero, ZMod.val_zero, BinaryNatCode.encode]
    rfl

end LeanCanny.Algebra.SymbolicScaledQuotientBits
