/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.SymbolicScaledQuotientSpace
public import LeanCanny.Algebra.SubresultantAccessFP
public import LeanCanny.Algebra.CoefficientMinorSpace

/-! # Native alpha coefficients of subresultant coefficient forms

Terminal orders are retained. Only an entry is sliced before the determinant;
the determinant itself stays over ℤ[alpha].
-/
@[expose] public section
namespace LeanCanny.Algebra.SymbolicCoefficientFormBits
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open SymbolicScaledQuotientBits (original modulus alpha target coefficient original_FP modulus_FP alpha_FP target_FP)
open scoped Classical
attribute [local irreducible] Matrix.det
set_option backward.isDefEq.respectTransparency false

structure Family where
  left : List Bool → Polynomial (Polynomial ℤ)
  right : List Bool → Polynomial (Polynomial ℤ)
  leftDegree : List Bool → ℕ
  rightDegree : List Bool → ℕ
  order : List Bool → ℕ
  order_left : ∀ c, order c ≤ leftDegree c
  order_right : ∀ c, order c ≤ rightDegree c
  dimension_pos : ∀ c, 0 < (leftDegree c-order c)+(rightDegree c-order c)

def sourceQuery (z : List Bool) : List Bool :=
  pair (pair (original (pairFst z)) (modulus (pairFst z)))
    (pair (pairSnd (pairSnd z)) (pairFst (pairSnd z)))

theorem sourceQuery_FP : sourceQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp (f := pairFst) (g := original) pairFst_mem_FP original_FP)
    (mem_FP_comp (f := pairFst) (g := modulus) pairFst_mem_FP modulus_FP))
    (mem_FP_pair (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP))

noncomputable def Family.access (F : Family) : SubresultantBits.Access where
  base := {
    leftDegree q := BinaryNatCode.encode (F.leftDegree (original q))
    rightDegree q := BinaryNatCode.encode (F.rightDegree (original q))
    modulus q := BinaryNat.succ (modulus q)
    degree := alpha
    leftCoefficient := coefficient F.left ∘ sourceQuery
    rightCoefficient := coefficient F.right ∘ sourceQuery }
  order q := BinaryNatCode.encode (F.order (original q))
  coefficient q := PrincipalCoefficientBits.minimum (target q) (BinaryNatCode.encode (F.order (original q)))

theorem Family.access_controls (F : Family) (hm : BinaryFn F.leftDegree)
    (hn : BinaryFn F.rightDegree) (hk : BinaryFn F.order) : F.access.ControlsPolyTime := by
  have hM := mem_FP_comp (f := original) (g := fun c => BinaryNatCode.encode (F.leftDegree c)) original_FP hm.bits_mem_FP
  have hN := mem_FP_comp (f := original) (g := fun c => BinaryNatCode.encode (F.rightDegree c)) original_FP hn.bits_mem_FP
  have hK := mem_FP_comp (f := original) (g := fun c => BinaryNatCode.encode (F.order c)) original_FP hk.bits_mem_FP
  exact ⟨⟨hM, hN, mem_FP_comp (f := modulus) (g := BinaryNat.succ) modulus_FP BinaryNat.succ_mem_FP, alpha_FP⟩, hK,
    PrincipalCoefficientBits.minimum_mem_FP target_FP hK⟩

noncomputable def Family.entry (F : Family) : List Bool → List Bool :=
  F.access.base.entry ∘ F.access.query

theorem Family.entryEvaluator (F : Family) (hm : BinaryFn F.leftDegree)
    (hn : BinaryFn F.rightDegree) (hk : BinaryFn F.order)
    (L : SpaceFunction (coefficient F.left)) (R : SpaceFunction (coefficient F.right)) :
    SpaceFunction F.entry :=
  (F.access.base.entryEvaluator (F.access_controls hm hn hk).base
    (L.precompose sourceQuery sourceQuery_FP) (R.precompose sourceQuery sourceQuery_FP)).precompose
      F.access.query (F.access.query_mem_FP (F.access_controls hm hn hk))

noncomputable def Family.matrix (F : Family) (q : List Bool) :
    Matrix (Fin ((F.leftDegree (original q)-F.order (original q))+(F.rightDegree (original q)-F.order (original q))))
      (Fin ((F.leftDegree (original q)-F.order (original q))+(F.rightDegree (original q)-F.order (original q))))
      (Polynomial ℤ) :=
  Subresultant.minor (F.left (original q)) (F.right (original q)) (F.leftDegree (original q))
    (F.rightDegree (original q)) (F.order (original q)) (min (Nat.fromBitsLE (target q)) (F.order (original q)))

theorem Family.entry_correct (F : Family) (q : List Bool)
    (i j : Fin ((F.leftDegree (original q)-F.order (original q))+(F.rightDegree (original q)-F.order (original q)))) (u : ℕ) :
    F.entry (pair q (pair (BinaryNatCode.encode i.val) (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode u)))) =
      residueBits ((((F.matrix q i j).coeff u) : ℤ) : ZMod (Nat.fromBitsLE (modulus q)+1)) := by
  let m := F.leftDegree (original q)
  let n := F.rightDegree (original q)
  let k := F.order (original q)
  let r := min (Nat.fromBitsLE (target q)) k
  let enc : Polynomial ℤ → List Bool := fun p =>
    SymbolicFixedTableEntryBits.integerResidue (p.coeff u) (Nat.fromBitsLE (modulus q)+1)
  have hm : F.access.base.leftDegree q = BinaryNatCode.encode m := rfl
  have hn : F.access.base.rightDegree q = BinaryNatCode.encode n := rfl
  have hk : F.access.order q = BinaryNatCode.encode k := rfl
  have hr : F.access.coefficient q = BinaryNatCode.encode r := by
    simp only [Family.access, PrincipalCoefficientBits.minimum_eq, BinaryNatCode.encode, Nat.fromBitsLE_bits, r, k]
  have hleft (v : ℕ) : F.access.base.leftCoefficient (pair q (pair (BinaryNatCode.encode v) (BinaryNatCode.encode u))) =
      enc ((F.left (original q)).coeff v) := by
    simp only [Family.access, Function.comp_apply, sourceQuery, coefficient, SymbolicFixedTableEntryBits.coefficient,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, enc]
  have hright (v : ℕ) : F.access.base.rightCoefficient (pair q (pair (BinaryNatCode.encode v) (BinaryNatCode.encode u))) =
      enc ((F.right (original q)).coeff v) := by
    simp only [Family.access, Function.comp_apply, sourceQuery, coefficient, SymbolicFixedTableEntryBits.coefficient,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, enc]
  have hz : enc 0 = [] := by simp [enc, SymbolicFixedTableEntryBits.integerResidue, residueBits, BinaryNatCode.encode]
  have h := F.access.base.entry_correct q (F.left (original q)) (F.right (original q)) m n u
    (fun a : ℤ => SymbolicFixedTableEntryBits.integerResidue a (Nat.fromBitsLE (modulus q)+1))
    hm hn hleft hright hz
    (CoefficientMinor.row m n k r (F.order_left _) (F.order_right _) (Nat.min_le_right _ _) i)
    (PrincipalMinor.col m n k (F.order_left _) (F.order_right _) j)
  have he := congrArg enc (CoefficientMinor.minor_apply (F.left (original q)) (F.right (original q)) m n k r
    (F.order_left _) (F.order_right _) (Nat.min_le_right _ _) i j)
  unfold Family.entry
  simp only [Function.comp_apply]
  rw [F.access.query_packet q m k r i.val j.val u hm hk hr]
  refine Eq.trans ?_ he.symm
  simpa only [CoefficientMinor.row, PrincipalMinor.col] using h

noncomputable def Family.value (F : Family) : List Bool → List Bool :=
  coefficient (fun c => PrincipalSubresultant.coefficientForm (F.left c) (F.right c)
    (F.leftDegree c) (F.rightDegree c) (F.order c))

theorem Family.evaluator (F : Family) (B : List Bool → ℕ)
    (hP : ∀ c k, ((F.left c).coeff k).natDegree ≤ B c)
    (hQ : ∀ c k, ((F.right c).coeff k).natDegree ≤ B c)
    (hm : BinaryFn F.leftDegree) (hn : BinaryFn F.rightDegree) (hk : BinaryFn F.order) (hB : BinaryFn B)
    (P : SpaceFunction (coefficient F.left)) (Q : SpaceFunction (coefficient F.right)) :
    SpaceFunction F.value := by
  let N := fun q => (F.leftDegree (original q)-F.order (original q))+(F.rightDegree (original q)-F.order (original q))
  let bound := fun q => BinaryNatCode.encode (B (original q))
  have hmat q (i j : Fin (N q)) : (F.matrix q i j).natDegree ≤ Nat.fromBitsLE (bound q) := by
    simp only [bound, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    rw [Family.matrix, Subresultant.minor_apply]
    split_ifs <;> rw [Subresultant.band] <;> split_ifs
    · exact hQ _ _
    · simp
    · exact hP _ _
    · simp
  have hdim : (fun q => BinaryNatCode.encode (N q)) ∈ FP :=
    mem_FP_of_eq (F.access.dimension_mem_FP (F.access_controls hm hn hk)) (fun q =>
      F.access.dimension_code q _ _ _ rfl rfl rfl)
  have E := PolynomialDeterminantBits.evaluator N modulus alpha bound F.entry F.matrix
    (fun q => F.dimension_pos (original q)) hmat F.entry_correct (F.entryEvaluator hm hn hk P Q)
    hdim modulus_FP alpha_FP
    (mem_FP_comp (f := original) (g := fun c => BinaryNatCode.encode (B c)) original_FP hB.bits_mem_FP)
  have hwithin := BinaryNat.le_fppred target_FP
    (mem_FP_comp (f := original) (g := fun c => BinaryNatCode.encode (F.order c)) original_FP hk.bits_mem_FP)
  have R := SpaceFunction.branch (fun q => decide (Nat.fromBitsLE (target q) ≤ F.order (original q)))
    (hwithin.of_iff (fun q => by simp only [Function.comp_apply, BinaryNatCode.encode, Nat.fromBitsLE_bits])).flag_mem_FP E
    (SpaceFunction.ofFP _ (constFn_mem_FP []))
  refine R.congr (funext fun q => ?_)
  simp only [decide_eq_true_eq, Family.value, coefficient, SymbolicFixedTableEntryBits.coefficient]
  change (if Nat.fromBitsLE (target q) ≤ F.order (original q) then
    PolynomialDeterminantBits.value N modulus alpha F.matrix q else []) =
      SymbolicFixedTableEntryBits.integerResidue
        (((PrincipalSubresultant.coefficientForm (F.left (original q)) (F.right (original q))
          (F.leftDegree (original q)) (F.rightDegree (original q)) (F.order (original q))).coeff
            (Nat.fromBitsLE (target q))).coeff (Nat.fromBitsLE (alpha q))) (Nat.fromBitsLE (modulus q)+1)
  rw [PrincipalSubresultant.coefficientForm_coeff]
  by_cases hv : Nat.fromBitsLE (target q) ≤ F.order (original q)
  · rw [ite_eq_left hv, ite_eq_left hv, PrincipalSubresultant.subresultantCoeff_eq_minor_det]
    unfold PolynomialDeterminantBits.value Family.matrix
    rw [min_eq_left hv]
    rfl
  · rw [ite_eq_right hv, ite_eq_right hv]
    simp only [coeff_zero, SymbolicFixedTableEntryBits.integerResidue, residueBits,
      Int.cast_zero, ZMod.val_zero, BinaryNatCode.encode]
    rfl

end LeanCanny.Algebra.SymbolicCoefficientFormBits
