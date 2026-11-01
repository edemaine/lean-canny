/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FixedWidthPowerMonomial
public import LeanCanny.Algebra.IntegralMixedVirtualOriginalRows
public import LeanCanny.Algebra.IntegralMixedVirtualNativeAccess
public import LeanCanny.Algebra.CoefficientWidthBinarySpace

/-! # Native Fermat multipliers and guarded low-row widths

The equation restores its free Fermat terms; a nonobjective row restores
one derivative monomial. The two integer scalar sources remain distinct:
`a*Q^D` and `a*Q^D*D`. The incoming homogeneous-system width is retained
for the monomial tests. Low rows use a guarded canonical-width query.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullRowMultiplier
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial MatrixPower
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedCutSource
open IntegralMixedVirtualSweepSource IntegralMixedVirtualNativeBits IntegralMixedVirtualOriginalRows
open scoped Classical

abbrev free (F : Family) (q : List Bool) : ℕ := F.ambient q - (F.rule q).critical.offset.val + 1
abbrev degree (F : Family) (q : List Bool) : ℕ := (F.spatial q).degree
def target (F : Family) (I : Indices F) (q : List Bool) : List Bool := BinaryNatCode.encode (I.target q)
def selected (F : Family) (I : Indices F) (q : List Bool) : ℕ := (I.coordinate q).val
def isEquation (F : Family) (I : Indices F) (q : List Bool) : Prop := I.coordinate q = objective (F.rule q)
instance (F : Family) (I : Indices F) (q : List Bool) : Decidable (isEquation F I q) := inferInstanceAs (Decidable (_ = _))

noncomputable def exponent (F : Family) (I : Indices F) (W : List Bool → ℕ) (q : List Bool) :=
  nativeExponent (Equiv.refl (Fin (free F q))) (W q) (I.target q)

def highMultiplicity (F : Family) (I : Indices F) (W : List Bool → ℕ) (q : List Bool) : ℕ :=
  if isEquation F I q then FixedWidthPowerMonomial.multiplicity (free F) W (degree F) (target F I) q
  else if FixedWidthPowerMonomial.Matches (free F) W (fun q => degree F q - 1) (selected F I) (target F I) q then 1 else 0

def multiplier (F : Family) (I : Indices F) (W : List Bool → ℕ) (q : List Bool) : ℕ :=
  if I.row q = I.col q then highMultiplicity F I W q else 0

noncomputable def low (F : Family) (I : Indices F) (q : List Bool) :
    MvPolynomial (Fin (free F q)) (Coefficient F q) :=
  if isEquation F I q then frozen F I q else gradient F I q (I.coordinate q)

noncomputable def scalar (F : Family) (I : Indices F) (q : List Bool) : ℤ :=
  if isEquation F I q then originalScale F q else originalScale F q * (F.spatial q).degree

def canonicalWidth (F : Family) (q : List Bool) : ℕ := PurePowerReductionBounds.width (free F q) (degree F q)
def packet (F : Family) (I : Indices F) (q : List Bool) : List Bool := pair q (target F I q)
noncomputable def lowFits (F : Family) (I : Indices F) (W : List Bool → ℕ) (q : List Bool) : Prop :=
  CoefficientWidthBits.Fits (free F) W (fun q => degree F q - 1) (packet F I q)
noncomputable instance (F : Family) (I : Indices F) (W : List Bool → ℕ) (q : List Bool) :
    Decidable (lowFits F I W q) := inferInstanceAs (Decidable (CoefficientWidthBits.Fits _ _ _ _))
def lowTarget (F : Family) (I : Indices F) (W : List Bool → ℕ) (q : List Bool) : ℕ :=
  Nat.fromBitsLE (CoefficientWidthBits.packed (free F) W (canonicalWidth F) (packet F I q))

theorem isEquation_FP (F : Family) (I : Indices F) (h : Metadata F I) : FPPred (isEquation F I) :=
  (h.coordinate.eq (h.objective.mod (BinaryFn.ofUnary (free_unary F I h)))).of_iff
    (fun q => by simp only [isEquation, objective, Fin.ext_iff])

theorem highMultiplicity_binary (F : Family) (I : Indices F) (W : List Bool → ℕ)
    (h : Metadata F I) (hW : UnaryFn W) : BinaryFn (highMultiplicity F I W) :=
  BinaryFn.ite (isEquation_FP F I h)
    (FixedWidthPowerMonomial.multiplicity_binary (free F) W (degree F) (target F I)
      (free_unary F I h) hW h.degree h.target.bits_mem_FP)
    (BinaryFn.ite (FixedWidthPowerMonomial.matches_FP (free F) W (fun q => degree F q - 1) (selected F I)
      (target F I) (free_unary F I h) hW (h.degree.sub (BinaryFn.const 1)) h.coordinate h.target.bits_mem_FP)
      (BinaryFn.const 1) (BinaryFn.const 0))

theorem multiplier_binary (F : Family) (I : Indices F) (W : List Bool → ℕ)
    (h : Metadata F I) (hW : UnaryFn W) : BinaryFn (multiplier F I W) :=
  BinaryFn.ite ((h.row.eq h.col).of_iff (fun _ => Fin.val_inj))
    (highMultiplicity_binary F I W h hW) (BinaryFn.const 0)

theorem packet_FP (F : Family) (I : Indices F) (h : Metadata F I) : packet F I ∈ FP :=
  mem_FP_pair id_mem_FP h.target.bits_mem_FP

theorem canonicalWidth_unary (F : Family) (I : Indices F) (h : Metadata F I) : UnaryFn (canonicalWidth F) :=
  PurePowerReductionBounds.width_unary (free_unary F I h) h.degree

theorem lowFits_FP (F : Family) (I : Indices F) (W : List Bool → ℕ) (h : Metadata F I) (hW : UnaryFn W) :
    FPPred (lowFits F I W) :=
  (CoefficientWidthBits.fits_binary_fppred (free_unary F I h) hW (h.degree.sub (BinaryFn.const 1))).comp (packet_FP F I h)

theorem lowTarget_binary (F : Family) (I : Indices F) (W : List Bool → ℕ) (h : Metadata F I) (hW : UnaryFn W) :
    BinaryFn (lowTarget F I W) :=
  BinaryFn.fromBits (mem_FP_comp (packet_FP F I h)
    (CoefficientWidthBits.packed_mem_FP (free_unary F I h) hW (canonicalWidth_unary F I h)))

theorem low_support (F : Family) (I : Indices F) (q : List Bool)
    (e : Fin (free F q) →₀ ℕ) (he : e ∈ (low F I q).support) (j : Fin (free F q)) : e j ≤ degree F q - 1 := by
  have H : (low F I q).totalDegree < degree F q := by
    by_cases HQ : isEquation F I q
    · simp only [low, HQ]
      exact frozen_degree F I q
    · simp only [low, HQ]
      exact (gradient_degree F I q (I.coordinate q)).trans_le (Nat.sub_le _ _)
  have HE := (MvPolynomial.monomial_le_degreeOf j he).trans (MvPolynomial.degreeOf_le_totalDegree _ _)
  exact HE.trans (Nat.le_pred_of_lt H)

theorem canonicalWidth_lt (F : Family) (q : List Bool) : degree F q - 1 < 2 ^ canonicalWidth F q := by
  have HM : degree F q - 1 ≤ free F q * (degree F q - 1) :=
    (Nat.one_mul _).symm.trans_le (Nat.mul_le_mul_right _ (by unfold free; omega))
  exact (HM.trans (Nat.le_succ _)).trans_lt (PurePowerReductionBounds.bound_lt _ _)

theorem low_coefficient (F : Family) (I : Indices F) (W : List Bool → ℕ) (q : List Bool) :
    (if lowFits F I W q then
      (low F I q).coeff (nativeExponent (Equiv.refl (Fin (free F q))) (canonicalWidth F q) (lowTarget F I W q))
    else 0) = (low F I q).coeff (exponent F I W q) := by
  by_cases HF : lowFits F I W q
  · rw [ite_eq_left HF]
    exact congrArg (fun e : Fin (free F q) →₀ ℕ => (low F I q).coeff e)
      (CoefficientWidthBits.native_packed (free F) W (canonicalWidth F) (fun q => degree F q - 1)
        q (Equiv.refl _) (I.target q) HF (canonicalWidth_lt F q))
  · rw [ite_eq_right HF]
    symm
    apply MvPolynomial.notMem_support_iff.mp
    intro HE
    apply HF
    apply (CoefficientWidthBits.fits_packet (free F) W (fun q => degree F q - 1) q (I.target q)).mpr
    intro i hi
    have H := low_support F I q _ HE ⟨i, hi⟩
    exact H

end LeanCanny.Algebra.IntegralMixedFullRowMultiplier
