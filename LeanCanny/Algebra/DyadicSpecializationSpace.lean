/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.DyadicSpecialization
public import LeanCanny.Algebra.ModularSumSpace
public import LeanCanny.Algebra.IntegerSignumSpace
public import LeanCanny.Algebra.InfinitesimalSignSpace

/-! # Streamed dyadic specialization of integer polynomial coefficients

FP binary metadata gives the parameter degree, dyadic exponent, and mass bound.
Original coefficient residues may use polynomial space. Modular powers clear
the denominator while a space-bounded sum avoids materializing the resulting integer.
-/

@[expose] public section

namespace LeanCanny.Algebra.DyadicBits
open Polynomial
open LeanCanny.Encoding
open LeanCanny.Computation
open MatrixPower

noncomputable def integerResidue (z : ℤ) (m : ℕ) : List Bool := residueBits (z : ZMod m)

structure Family where
  polynomial : List Bool → ℤ[X]
  degree : List Bool → List Bool
  exponent : List Bool → List Bool
  mass : List Bool → List Bool
  polynomial_degree : ∀ c, (polynomial c).natDegree ≤ Nat.fromBitsLE (degree c)
  polynomial_mass : ∀ c, coefficientMass (polynomial c) ≤ 2 ^ Nat.fromBitsLE (mass c)

structure ControlsPolyTime (F : Family) : Prop where
  degree : F.degree ∈ FP
  exponent : F.exponent ∈ FP
  mass : F.mass ∈ FP

noncomputable def Family.value (F : Family) (c : List Bool) : ℤ :=
  DyadicSpecialization.numerator (F.polynomial c) (Nat.fromBitsLE (F.degree c)) (Nat.fromBitsLE (F.exponent c))

def mValue (q : List Bool) : ℕ := Nat.fromBitsLE (pairSnd q) + 1
def modulusCode (q : List Bool) : List Bool := BinaryNat.succ (pairSnd q)
def countCode (F : Family) (q : List Bool) : List Bool := BinaryNat.succ (F.degree (pairFst q))
def original (p : List Bool) : List Bool := pairFst (pairFst p)
def sourceQuery (p : List Bool) : List Bool :=
  pair (pair (original p) (pairSnd p)) (BinaryNat.normalize (pairSnd (pairFst p)))
def powerExponent (F : Family) (p : List Bool) : List Bool :=
  BinaryNat.mul (pair (F.exponent (original p)) (BinaryNat.sub (pair (F.degree (original p)) (pairSnd p))))
def power (F : Family) (p : List Bool) : List Bool :=
  BinaryNat.powMod (pair (BinaryNatCode.encode 2) (pair (powerExponent F p) (pairSnd (pairFst p))))
def finish (F : Family) (z : List Bool) : List Bool :=
  BinaryNat.mulMod (pair (modulusCode (pairFst (pairFst z))) (pair (pairSnd z) (power F (pairFst z))))

theorem original_mem_FP : original ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem modulusCode_mem_FP : modulusCode ∈ FP := by
  have h := mem_FP_comp pairSnd_mem_FP BinaryNat.succ_mem_FP
  refine mem_FP_of_eq (g := modulusCode) h ?_
  intro q
  simp only [modulusCode, Function.comp_apply]
theorem countCode_mem_FP (F : Family) (hF : ControlsPolyTime F) : countCode F ∈ FP := by
  have h := mem_FP_comp (mem_FP_comp pairFst_mem_FP hF.degree) BinaryNat.succ_mem_FP
  refine mem_FP_of_eq (g := countCode F) h ?_
  intro q
  simp only [countCode, Function.comp_apply]
theorem sourceQuery_mem_FP : sourceQuery ∈ FP := by
  have hm := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.normalize_mem_FP
  have h := mem_FP_pair (mem_FP_pair original_mem_FP pairSnd_mem_FP) hm
  refine mem_FP_of_eq (g := sourceQuery) h ?_
  intro p
  simp only [sourceQuery, Function.comp_apply]
theorem powerExponent_mem_FP (F : Family) (hF : ControlsPolyTime F) : powerExponent F ∈ FP := by
  have hd := mem_FP_comp original_mem_FP hF.degree
  have hs := mem_FP_comp original_mem_FP hF.exponent
  have hi := mem_FP_comp (mem_FP_pair hd pairSnd_mem_FP) BinaryNat.sub_mem_FP
  have h := mem_FP_comp (mem_FP_pair hs hi) BinaryNat.mul_mem_FP
  refine mem_FP_of_eq (g := powerExponent F) h ?_
  intro p
  simp only [powerExponent, Function.comp_apply]
theorem power_mem_FP (F : Family) (hF : ControlsPolyTime F) : power F ∈ FP := by
  have hm := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have h := mem_FP_comp (mem_FP_pair (constFn_mem_FP (BinaryNatCode.encode 2))
    (mem_FP_pair (powerExponent_mem_FP F hF) hm)) BinaryNat.powMod_mem_FP
  refine mem_FP_of_eq (g := power F) h ?_
  intro p
  simp only [power, Function.comp_apply]
theorem finish_mem_FP (F : Family) (hF : ControlsPolyTime F) : finish F ∈ FP := by
  have hm := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) modulusCode_mem_FP
  have hp := mem_FP_comp pairFst_mem_FP (power_mem_FP F hF)
  have h := mem_FP_comp (mem_FP_pair hm (mem_FP_pair pairSnd_mem_FP hp)) BinaryNat.mulMod_mem_FP
  refine mem_FP_of_eq (g := finish F) h ?_
  intro z
  simp only [finish, Function.comp_apply]

structure Access (F : Family) where
  coefficient : List Bool → List Bool
  coefficient_eq : ∀ c i m, 0 < m → coefficient
    (pair (pair c (BinaryNatCode.encode i)) (BinaryNatCode.encode (m - 1))) =
      integerResidue ((F.polynomial c).coeff i) m

def term {F : Family} (a : Access F) (p : List Bool) : List Bool :=
  finish F (pair p (a.coefficient (sourceQuery p)))

theorem termEvaluator {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (P : SpaceFunction a.coefficient) : SpaceFunction (term a) := by
  let E := (P.precompose sourceQuery sourceQuery_mem_FP).withInput.postcompose (finish F) (finish_mem_FP F hF)
  refine E.congr (funext fun p => ?_)
  simp only [term, Function.comp_apply]

theorem term_packet {F : Family} (a : Access F) (q : List Bool) (i : ℕ) :
    term a (pair q (BinaryNatCode.encode i)) = residueBits
      (((F.polynomial (pairFst q)).coeff i : ZMod (mValue q)) *
        (((2 ^ (Nat.fromBitsLE (F.exponent (pairFst q)) * (Nat.fromBitsLE (F.degree (pairFst q)) - i)) : ℕ)) : ZMod (mValue q))) := by
  let : NeZero (mValue q) := ⟨by dsimp [mValue]; omega⟩
  have hc : a.coefficient (sourceQuery (pair q (BinaryNatCode.encode i))) =
      integerResidue ((F.polynomial (pairFst q)).coeff i) (mValue q) := by
    have h := a.coefficient_eq (pairFst q) i (mValue q) (by dsimp [mValue]; omega)
    simpa only [sourceQuery, original, pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits,
      mValue, Nat.add_sub_cancel, BinaryNatCode.encode] using h
  unfold term
  rw [hc]
  simp only [finish, power, powerExponent, original, pairFst_pair, pairSnd_pair,
    modulusCode, BinaryNat.succ_eq_bits, BinaryNat.powMod_eq_bits, BinaryNat.sub_pair,
    BinaryNat.mul_pair, BinaryNat.mulMod_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  unfold integerResidue residueBits
  rw [ZMod.val_mul, ZMod.val_natCast]
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, mValue]

noncomputable def Family.residue (F : Family) (q : List Bool) : List Bool :=
  integerResidue (F.value (pairFst q)) (mValue q)

theorem residueEvaluator {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (P : SpaceFunction a.coefficient) : SpaceFunction F.residue := by
  have hm : (fun q => Nat.fromBitsLE (modulusCode q)) = mValue := by
    funext q
    simp only [modulusCode, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits, mValue]
  let E := ModularSum.evaluatorWithModulus (termEvaluator a hF P) (countCode F) modulusCode
    (countCode_mem_FP F hF) modulusCode_mem_FP mValue hm
    (fun q i => ((F.polynomial (pairFst q)).coeff i : ZMod (mValue q)) *
      (((2 ^ (Nat.fromBitsLE (F.exponent (pairFst q)) * (Nat.fromBitsLE (F.degree (pairFst q)) - i)) : ℕ)) : ZMod (mValue q)))
    (fun q => by dsimp [mValue]; omega) (fun q i _ => term_packet a q i)
  refine E.congr (funext fun q => ?_)
  simp only [Family.residue, Family.value, integerResidue, DyadicSpecialization.numerator,
    countCode, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits, Int.cast_sum, Int.cast_mul,
    Int.cast_pow, Int.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat]

def budgetCode (F : Family) (c : List Bool) : List Bool :=
  BinaryNat.succ (BinaryNat.add (pair (F.mass c) (BinaryNat.mul (pair (F.exponent c) (F.degree c)))))

theorem budgetCode_mem_FP (F : Family) (hF : ControlsPolyTime F) : budgetCode F ∈ FP := by
  have hp := mem_FP_comp (mem_FP_pair hF.exponent hF.degree) BinaryNat.mul_mem_FP
  have h := mem_FP_comp (mem_FP_comp (mem_FP_pair hF.mass hp) BinaryNat.add_mem_FP) BinaryNat.succ_mem_FP
  refine mem_FP_of_eq (g := budgetCode F) h ?_
  intro c
  simp only [budgetCode, Function.comp_apply]

theorem budgetCode_value (F : Family) (c : List Bool) : Nat.fromBitsLE (budgetCode F c) =
    Nat.fromBitsLE (F.mass c) + Nat.fromBitsLE (F.exponent c) * Nat.fromBitsLE (F.degree c) + 1 := by
  simp only [budgetCode, BinaryNat.succ_eq_bits, BinaryNat.add_pair, BinaryNat.mul_pair, Nat.fromBitsLE_bits]

theorem value_size (F : Family) (c : List Bool) : (F.value c).natAbs.size ≤ Nat.fromBitsLE (budgetCode F c) := by
  rw [budgetCode_value]
  exact DyadicSpecialization.numerator_size_le _ _ _ _ (F.polynomial_degree c) (F.polynomial_mass c)

theorem signEvaluator {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (P : SpaceFunction a.coefficient) : SpaceFunction (fun c => InfinitesimalSign.tag (F.value c)) := by
  apply IntegerSignumBits.evaluator (residueEvaluator a hF P) (budgetCode F) (budgetCode_mem_FP F hF)
    F.value (value_size F)
  intro c m hm
  rw [Family.residue]
  simp only [pairFst_pair, pairSnd_pair, mValue, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    Nat.sub_add_cancel (by omega : 1 ≤ m)]
  rfl

theorem smallParameterSignEvaluator {F : Family} (a : Access F) (hF : ControlsPolyTime F)
    (P : SpaceFunction a.coefficient) (hs : ∀ c, Nat.fromBitsLE (F.mass c) < Nat.fromBitsLE (F.exponent c)) :
    SpaceFunction (fun c => InfinitesimalSign.encode (SignType.sign (F.polynomial c).trailingCoeff)) := by
  refine (signEvaluator a hF P).congr (funext fun c => ?_)
  rw [InfinitesimalSign.tag_eq_encode]
  exact congrArg InfinitesimalSign.encode (DyadicSpecialization.numerator_sign _ _ _ _
    (F.polynomial_degree c) (F.polynomial_mass c) (hs c))

end LeanCanny.Algebra.DyadicBits
