/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.MacaulayIntegerPolynomialSpace
public import LeanCanny.Algebra.MacaulayExtraneousControl
/-! # The actual extraneous padded matrix reuses the original entry program

The extraneous-index mask is computed from declared source degrees. Omitted
rows are literal identity rows, including their exact parameter coefficient.
No new coefficient reader or determinant nonvanishing premise is introduced.
-/
@[expose] public section
namespace LeanCanny.Algebra.MacaulayPaddedExtraneousPolynomialBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower MacaulayBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ArithmeticBits.one BinaryNat.succ

def maskQuery (q : List Bool) : List Bool := pair (pairFst (pairFst q)) (pairSnd q)
def row (q : List Bool) : List Bool := pairFst (pairSnd q)
def col (q : List Bool) : List Bool := pairFst (pairSnd (pairSnd q))
def target (q : List Bool) : List Bool := pairSnd (pairSnd (pairSnd q))
def modulus (q : List Bool) : List Bool := pairSnd (pairFst q)

theorem maskQuery_FP : maskQuery ∈ FP := by polytime [maskQuery]
theorem row_FP : row ∈ FP := by polytime [row]
theorem col_FP : col ∈ FP := by polytime [col]
theorem target_FP : target ∈ FP := by polytime [target]
theorem modulus_FP : modulus ∈ FP := by polytime [modulus]

def identityValue (q : List Bool) : List Bool :=
  if Nat.fromBitsLE (row q) = Nat.fromBitsLE (col q) ∧ Nat.fromBitsLE (target q) = 0
  then ArithmeticBits.one (BinaryNat.succ (modulus q)) else []

theorem identityValue_FP : identityValue ∈ FP := by
  have HG := ((BinaryFn.fromBits row_FP).eq (BinaryFn.fromBits col_FP)).and
    ((BinaryFn.fromBits target_FP).eq (BinaryFn.const 0))
  have HO := mem_FP_comp (mem_FP_comp modulus_FP BinaryNat.succ_mem_FP) ArithmeticBits.one_mem_FP
  exact mem_FP_of_eq (HG.ite_mem_FP HO (constFn_mem_FP [])) (fun _ => rfl)

noncomputable def entry (L : Layout) (source : List Bool → List Bool) (q : List Bool) : List Bool :=
  if extraneousEntry L (maskQuery q) then source q else identityValue q

theorem entry_evaluator (L : Layout) (hL : L.PolyTime) (source : List Bool → List Bool)
    (S : SpaceFunction source) : SpaceFunction (entry L source) := by
  have HG := (extraneousEntry_fppred hL).comp maskQuery_FP
  have E := SpaceFunction.branch (fun q => decide (extraneousEntry L (maskQuery q)))
    HG.flag_mem_FP S (SpaceFunction.ofFP _ identityValue_FP)
  exact E.congr (funext fun q => by simp only [entry, decide_eq_true_eq])

theorem entry_packet (L : Layout)
    (Q : (c : List Bool) → Fin (L.arity c) → MvPolynomial (Fin (L.arity c)) (Polynomial ℤ))
    (source : List Bool → List Bool)
    (hc : ∀ c m (i j : Fin (MacaulayIntegerPolynomialBits.dimension L c)) u,
      source (pair (pair c m) (pair (BinaryNatCode.encode i.val)
        (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode u)))) =
          residueBits ((((MacaulayIntegerPolynomialBits.matrix L Q c i j).coeff u) : ℤ) :
            ZMod (Nat.fromBitsLE m + 1)))
    (c m : List Bool) (i j : Fin (MacaulayIntegerPolynomialBits.dimension L c)) (u : ℕ) :
    entry L source (pair (pair c m) (pair (BinaryNatCode.encode i.val)
      (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode u)))) =
        residueBits ((((Macaulay.extraneousPadded (Q c) (Degrees L c) (L.width c) i j).coeff u) : ℤ) :
          ZMod (Nat.fromBitsLE m + 1)) := by
  have HQ : maskQuery (pair (pair c m) (pair (BinaryNatCode.encode i.val)
      (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode u)))) =
        PolynomialAffineEntryBits.packet c i.val j.val u := by
    simp only [maskQuery, pairFst_pair, pairSnd_pair, PolynomialAffineEntryBits.packet]
  have HG := extraneousEntry_packet L c i j.val u
  unfold entry
  rw [HQ]
  by_cases HI : i ∈ Macaulay.extraneousIndices (Degrees L c) (L.width c)
  · rw [ite_eq_left (HG.mpr HI), hc]
    simp only [Macaulay.extraneousPadded, PrincipalPadding.matrix, HI, ite_true]
    rfl
  · rw [ite_eq_right (fun H => HI (HG.mp H))]
    simp only [Macaulay.extraneousPadded, PrincipalPadding.matrix, HI, ite_false, Matrix.one_apply]
    simp only [identityValue, row, col, target, modulus, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits]
    by_cases HE : i = j
    · subst j
      simp only [ite_true, true_and]
      by_cases HU : u = 0
      · subst u
        simp only [ite_true, Polynomial.coeff_one_zero, Int.cast_one, BinaryNat.succ_eq_bits]
        change ArithmeticBits.one (BinaryNatCode.encode (Nat.fromBitsLE m + 1)) = _
        exact ArithmeticBits.one_residueBits _
      · rw [ite_eq_right HU, Polynomial.coeff_one, ite_eq_right HU, Int.cast_zero]
        rfl
    · have HV : i.val ≠ j.val := fun H => HE (Fin.ext H)
      simp only [HV, false_and, ite_false, HE, Polynomial.coeff_zero, Int.cast_zero]
      rfl

end LeanCanny.Algebra.MacaulayPaddedExtraneousPolynomialBits
