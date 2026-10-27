/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PolynomialPrincipalMinorSpace
public import LeanCanny.Algebra.PrincipalCoefficientSpace

/-! # Native parameter coefficients of signed principal subresultants

The principal order is clamped only in the auxiliary determinant family.
Above the principal range the retained input coefficient or zero is used.
All parameter coefficients come from the original modular bivariate readers.
-/

@[expose] public section
namespace LeanCanny.Algebra.PolynomialPrincipalCoefficientBits
open Polynomial LeanCanny.Encoding LeanCanny.Computation MatrixPower PrincipalSubresultant

structure Family where
  left : List Bool → (ℤ[X])[X]
  right : List Bool → (ℤ[X])[X]
  leftDegree : List Bool → ℕ
  rightDegree : List Bool → ℕ

structure Access (F : Family) where
  left : CertifiedPolynomial.BivariateReader F.left
  right : CertifiedPolynomial.BivariateReader F.right
  leftDegree : BinaryFn F.leftDegree
  rightDegree : BinaryFn F.rightDegree

def minor (F : Family) : PolynomialPrincipalMinorBits.Family where
  left r := F.left (pairFst r)
  right r := F.right (pairFst r)
  leftDegree r := F.leftDegree (pairFst r)
  rightDegree r := F.rightDegree (pairFst r)
  order r := min (Nat.fromBitsLE (pairSnd r)) (min (F.leftDegree (pairFst r)) (F.rightDegree (pairFst r)))
  order_left _ := (Nat.min_le_right _ _).trans (Nat.min_le_left _ _)
  order_right _ := (Nat.min_le_right _ _).trans (Nat.min_le_right _ _)

def sourceQuery (t : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst (pairFst t))) (pairSnd (pairFst t))) (pairSnd t)
theorem sourceQuery_FP : sourceQuery ∈ FP := by polytime [sourceQuery]

def reindexReader {p : List Bool → (ℤ[X])[X]} (A : CertifiedPolynomial.BivariateReader p) :
    CertifiedPolynomial.BivariateReader (p ∘ pairFst) where
  coefficient := A.coefficient ∘ sourceQuery
  evaluator := A.evaluator.precompose sourceQuery sourceQuery_FP
  coefficient_eq q u v := by
    simp only [Function.comp_apply, sourceQuery, pairFst_pair, pairSnd_pair]
    have H := A.coefficient_eq (pair (pairFst (pairFst q)) (pairSnd q)) u v
    simp only [pairFst_pair] at H
    refine H.trans ?_
    exact congrArg₂ (fun (a : ℤ) (m : ℕ) => residueBits (a : ZMod m)) rfl
      (by rw [pairSnd_pair])

theorem minimum_binary {f g : List Bool → ℕ} (hf : BinaryFn f) (hg : BinaryFn g) :
    BinaryFn (fun c => min (f c) (g c)) :=
  (BinaryFn.ite (hf.le hg) hf hg).of_eq (fun c =>
    (Nat.min_def : min (f c) (g c) = if f c ≤ g c then f c else g c).symm)

def minorAccess {F : Family} (A : Access F) : PolynomialPrincipalMinorBits.Access (minor F) where
  left := reindexReader A.left
  right := reindexReader A.right
  leftDegree := A.leftDegree.comp pairFst_mem_FP
  rightDegree := A.rightDegree.comp pairFst_mem_FP
  order := minimum_binary (BinaryFn.fromBits pairSnd_mem_FP)
    (minimum_binary (A.leftDegree.comp pairFst_mem_FP) (A.rightDegree.comp pairFst_mem_FP))

noncomputable def polynomial (F : Family) (r : List Bool) : ℤ[X] :=
  signedPsc (F.left (pairFst r)) (F.right (pairFst r))
    (F.leftDegree (pairFst r)) (F.rightDegree (pairFst r)) (Nat.fromBitsLE (pairSnd r))

noncomputable def minorDet (p q : (ℤ[X])[X]) (m n k : ℕ) : ℤ[X] :=
  (Subresultant.minor p q m n k k).det

def baseContext (z : List Bool) : List Bool := pairFst (PolynomialPrincipalMinorBits.origin z)
def order (z : List Bool) : ℕ := Nat.fromBitsLE (pairSnd (PolynomialPrincipalMinorBits.origin z))
def parameter (z : List Bool) : ℕ := Nat.fromBitsLE (pairSnd (pairFst z))
theorem baseContext_FP : baseContext ∈ FP := by polytime [baseContext, PolynomialPrincipalMinorBits.origin]

def gap (F : Family) (z : List Bool) : ℕ := F.leftDegree (baseContext z) - order z
def positiveWeight (F : Family) (z : List Bool) : Prop := Even ((gap F z).choose 2)
instance (F : Family) (z : List Bool) : Decidable (positiveWeight F z) := inferInstanceAs (Decidable (Even _))

theorem positiveWeight_fppred {F : Family} (A : Access F) : FPPred (positiveWeight F) := by
  have hl := mem_FP_comp baseContext_FP A.leftDegree.bits_mem_FP
  have hk := mem_FP_comp PolynomialPrincipalMinorBits.origin_FP pairSnd_mem_FP
  have hg := mem_FP_comp (mem_FP_pair hl hk) BinaryNat.sub_mem_FP
  have hc := mem_FP_comp hg SignStatisticBits.chooseTwo_mem_FP
  refine (SignStatisticBits.evenWord_fppred.comp hc).of_iff (fun z => ?_)
  simp only [Function.comp_apply, BinaryNat.sub_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    SignStatisticBits.chooseTwo_code, SignStatisticBits.evenWord_iff, positiveWeight, gap, order]

noncomputable def normalizeSign (F : Family) (t : List Bool) : List Bool :=
  if positiveWeight F (pairFst t) then pairSnd t
  else ArithmeticBits.negate (pair (BinaryNat.succ (pairSnd (pairFst t))) (pairSnd t))
theorem normalizeSign_FP {F : Family} (A : Access F) : normalizeSign F ∈ FP := by
  have hm := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.succ_mem_FP
  have H := ((positiveWeight_fppred A).comp pairFst_mem_FP).ite_mem_FP pairSnd_mem_FP
    (mem_FP_comp (mem_FP_pair hm pairSnd_mem_FP) ArithmeticBits.negate_mem_FP)
  refine mem_FP_of_eq (g := normalizeSign F) H ?_
  intro z
  simp only [normalizeSign, Function.comp_apply]

theorem normalizeSign_pair (F : Family) (z : List Bool) (x : ZMod (PolynomialPrincipalMinorBits.modulus z)) :
    normalizeSign F (pair z (residueBits x)) = residueBits ((-1) ^ (gap F z).choose 2 * x) := by
  let : NeZero (PolynomialPrincipalMinorBits.modulus z) := ⟨by simp [PolynomialPrincipalMinorBits.modulus]⟩
  have hm : BinaryNat.succ (pairSnd z) = BinaryNatCode.encode (PolynomialPrincipalMinorBits.modulus z) :=
    BinaryNat.succ_eq_bits _
  simp only [normalizeSign, pairFst_pair, pairSnd_pair, hm, positiveWeight]
  by_cases he : Even ((gap F z).choose 2)
  · simp only [he, ite_true, he.neg_one_pow, one_mul]
  · rw [ite_eq_right he, ArithmeticBits.negate_residueBits]
    simp only [neg_one_pow_eq_ite, he, ite_false, neg_one_mul]

def within (F : Family) (z : List Bool) : Prop :=
  order z ≤ F.leftDegree (baseContext z) ∧ order z ≤ F.rightDegree (baseContext z)
instance (F : Family) (z : List Bool) : Decidable (within F z) := inferInstanceAs (Decidable (_ ∧ _))
theorem within_fppred {F : Family} (A : Access F) : FPPred (within F) := by
  have hk := BinaryFn.fromBits (mem_FP_comp PolynomialPrincipalMinorBits.origin_FP pairSnd_mem_FP)
  exact (hk.le (A.leftDegree.comp baseContext_FP)).and (hk.le (A.rightDegree.comp baseContext_FP))

def directQuery (z : List Bool) : List Bool :=
  pair (pair (baseContext z) (pairSnd z))
    (pair (BinaryNat.normalize (pairSnd (pairFst z)))
      (BinaryNat.normalize (pairSnd (PolynomialPrincipalMinorBits.origin z))))
theorem directQuery_FP : directQuery ∈ FP := by polytime [directQuery, baseContext, PolynomialPrincipalMinorBits.origin]

noncomputable def residueValue {F : Family} (A : Access F) (z : List Bool) : List Bool :=
  if within F z then normalizeSign F (pair z ((PolynomialPrincipalMinorBits.modular (minor F)).value z))
  else if order z = F.leftDegree (baseContext z) then A.left.coefficient (directQuery z)
  else if order z = F.rightDegree (baseContext z) then A.right.coefficient (directQuery z)
  else []

theorem residueValue_eq {F : Family} (A : Access F) (z : List Bool) :
    residueValue A z = residueBits (((polynomial F (PolynomialPrincipalMinorBits.origin z)).coeff (parameter z) : ℤ) :
      ZMod (PolynomialPrincipalMinorBits.modulus z)) := by
  have hl : A.left.coefficient (pair (pair (baseContext z) (pairSnd z))
      (pair (BinaryNatCode.encode (parameter z)) (BinaryNatCode.encode (order z)))) =
      residueBits ((((F.left (baseContext z)).coeff (order z)).coeff (parameter z) : ℤ) :
        ZMod (PolynomialPrincipalMinorBits.modulus z)) := by
    have H := A.left.coefficient_eq (pair (baseContext z) (pairSnd z)) (parameter z) (order z)
    simp only [pairFst_pair] at H
    refine H.trans ?_
    exact congrArg₂ (fun (a : ℤ) (m : ℕ) => residueBits (a : ZMod m)) rfl
      (by rw [pairSnd_pair]; rfl)
  have hr : A.right.coefficient (pair (pair (baseContext z) (pairSnd z))
      (pair (BinaryNatCode.encode (parameter z)) (BinaryNatCode.encode (order z)))) =
      residueBits ((((F.right (baseContext z)).coeff (order z)).coeff (parameter z) : ℤ) :
        ZMod (PolynomialPrincipalMinorBits.modulus z)) := by
    have H := A.right.coefficient_eq (pair (baseContext z) (pairSnd z)) (parameter z) (order z)
    simp only [pairFst_pair] at H
    refine H.trans ?_
    exact congrArg₂ (fun (a : ℤ) (m : ℕ) => residueBits (a : ZMod m)) rfl
      (by rw [pairSnd_pair]; rfl)
  have hd : directQuery z = pair (pair (baseContext z) (pairSnd z))
      (pair (BinaryNatCode.encode (parameter z)) (BinaryNatCode.encode (order z))) := by
    simp only [directQuery, parameter, order, BinaryNat.normalize_eq_bits, BinaryNatCode.encode]
  by_cases hw : within F z
  · have hk : order z ≤ min (F.leftDegree (baseContext z)) (F.rightDegree (baseContext z)) :=
      Nat.le_min.mpr hw
    rw [residueValue, ite_eq_left hw, PolynomialPrincipalMinorBits.value_eq, normalizeSign_pair]
    change residueBits ((-1 : ZMod (PolynomialPrincipalMinorBits.modulus z)) ^ (gap F z).choose 2 *
      (((PolynomialPrincipalMinorBits.determinant (minor F) (PolynomialPrincipalMinorBits.origin z)).coeff (parameter z) : ℤ) :
        ZMod (PolynomialPrincipalMinorBits.modulus z))) = _
    have hm : min (order z) (min (F.leftDegree (baseContext z)) (F.rightDegree (baseContext z))) = order z := Nat.min_eq_left hk
    have hdet : PolynomialPrincipalMinorBits.determinant (minor F) (PolynomialPrincipalMinorBits.origin z) =
        minorDet (F.left (baseContext z)) (F.right (baseContext z))
          (F.leftDegree (baseContext z)) (F.rightDegree (baseContext z)) (order z) := by
      change minorDet (F.left (baseContext z)) (F.right (baseContext z))
        (F.leftDegree (baseContext z)) (F.rightDegree (baseContext z))
        (min (order z) (min (F.leftDegree (baseContext z)) (F.rightDegree (baseContext z)))) = _
      rw [hm]
    rw [hdet]
    unfold polynomial
    change _ = residueBits (((signedPsc (F.left (baseContext z)) (F.right (baseContext z))
      (F.leftDegree (baseContext z)) (F.rightDegree (baseContext z)) (order z)).coeff (parameter z) : ℤ) :
        ZMod (PolynomialPrincipalMinorBits.modulus z))
    rw [signedPsc_eq_minor _ _ _ _ _ hk]
    simp only [← Polynomial.C_neg, ← Polynomial.C_1, ← Polynomial.C_pow, Polynomial.coeff_C_mul,
      Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, gap, minorDet]
  · have hk : min (F.leftDegree (baseContext z)) (F.rightDegree (baseContext z)) < order z := by
      unfold within at hw
      omega
    rw [residueValue, ite_eq_right hw, hd, hl, hr, polynomial]
    change _ = residueBits (((signedPsc (F.left (baseContext z)) (F.right (baseContext z))
      (F.leftDegree (baseContext z)) (F.rightDegree (baseContext z)) (order z)).coeff (parameter z) : ℤ) :
        ZMod (PolynomialPrincipalMinorBits.modulus z))
    rw [signedPsc_of_lt _ _ hk]
    split_ifs with hm hn
    · rw [hm]
    · rw [hn]
    · simp [residueBits, BinaryNatCode.encode]

theorem evaluator {F : Family} (A : Access F) : SpaceFunction (residueValue A) := by
  have M := (PolynomialPrincipalMinorBits.evaluator (minorAccess A)).withInput.postcompose
    (normalizeSign F) (normalizeSign_FP A)
  have L := A.left.evaluator.precompose directQuery directQuery_FP
  have R := A.right.evaluator.precompose directQuery directQuery_FP
  have hk := BinaryFn.fromBits (mem_FP_comp PolynomialPrincipalMinorBits.origin_FP pairSnd_mem_FP)
  have E := SpaceFunction.branch (fun z => decide (within F z)) (within_fppred A).flag_mem_FP M
    (SpaceFunction.branch (fun z => decide (order z = F.leftDegree (baseContext z)))
      (hk.eq (A.leftDegree.comp baseContext_FP)).flag_mem_FP L
      (SpaceFunction.branch (fun z => decide (order z = F.rightDegree (baseContext z)))
        (hk.eq (A.rightDegree.comp baseContext_FP)).flag_mem_FP R (SpaceFunction.ofFP _ (constFn_mem_FP []))))
  exact E.congr (funext fun z => by simp only [residueValue, Function.comp_apply, decide_eq_true_eq])

end LeanCanny.Algebra.PolynomialPrincipalCoefficientBits
