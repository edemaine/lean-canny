/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CannyResultantResidue
public import LeanCanny.Algebra.SubresultantPolynomialSpace
public import LeanCanny.Algebra.SubresultantRecovery

/-!
# Certified residues of Canny's coordinate-recovery coefficients

The selected coefficient of the first symbolic subresultant is reduced modulo
the positive modulus supplied in the query. Selection zero gives the numerator;
selection one gives the denominator. The original coefficient-residue routines,
FP source metadata, and an FP selection writer suffice. Source degrees remain
fixed through modular degree drops.
-/

@[expose] public section

namespace LeanCanny.Algebra.CannySubresultantBits

open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation
open MatrixPower
open Polynomial
open CannyResultantBits (mValue)

structure Family where
  source : CannyResultantBits.Family
  coefficient : List Bool → ℕ

noncomputable def Family.integerCoefficient (F : Family) (c : List Bool) : ℤ :=
  ((recoverySubresultant (F.source.left c) (F.source.right c) (F.source.direction c)).coeff
    (F.coefficient c)).coeff (F.source.degree c)

theorem Family.integerCoefficient_eq_numerator (F : Family) (c : List Bool) (h : F.coefficient c = 0) :
    F.integerCoefficient c =
      (subresultantNumerator (F.source.left c) (F.source.right c) (F.source.direction c)).coeff (F.source.degree c) := by
  simp only [integerCoefficient, h, subresultantNumerator]

theorem Family.integerCoefficient_eq_denominator (F : Family) (c : List Bool) (h : F.coefficient c = 1) :
    F.integerCoefficient c =
      (subresultantDenominator (F.source.left c) (F.source.right c) (F.source.direction c)).coeff (F.source.degree c) := by
  simp only [integerCoefficient, h, subresultantDenominator]

noncomputable def Family.value (F : Family) (q : List Bool) : List Bool :=
  residueBits (F.integerCoefficient (pairFst q) : ZMod (mValue q))

def Family.zeroLanguage (F : Family) : Language :=
  {q | (F.integerCoefficient (pairFst q) : ZMod (mValue q)) = 0}

noncomputable def Family.modular (F : Family) : SubresultantPolynomial.ModularFamily where
  modulus := mValue
  left := F.source.modular.left
  right := F.source.modular.right
  leftDegree := F.source.modular.leftDegree
  rightDegree := F.source.modular.rightDegree
  order := fun _ => 1
  coefficient := F.coefficient ∘ pairFst
  degree := F.source.modular.degree
  modulus_ne_zero := F.source.modular.modulus_ne_zero

set_option backward.isDefEq.respectTransparency false in
theorem Family.modular_value (F : Family) (q : List Bool) : F.modular.value q = F.value q := by
  simp only [SubresultantPolynomial.ModularFamily.value, Family.modular, CannyResultantBits.Family.modular, CannyResultantBits.Family.modularWithDegrees,
    Subresultant.polynomial_map, Polynomial.coeff_map, Polynomial.coe_mapRingHom]
  rfl

structure Access (F : Family) where
  source : CannyResultantBits.Access F.source
  coefficient : List Bool → List Bool
  coefficient_eq : ∀ c, coefficient c = BinaryNatCode.encode (F.coefficient c)

structure Access.PolyTime {F : Family} (a : Access F) : Prop where
  source : a.source.PolyTime
  coefficient : a.coefficient ∈ FP

namespace Access

set_option backward.isDefEq.respectTransparency false in
noncomputable def modular {F : Family} (a : Access F) : SubresultantPolynomial.ModularAccess F.modular where
  bits := {
    base := a.source.modular.bits
    order := fun _ => BinaryNatCode.encode 1
    coefficient := a.coefficient ∘ pairFst }
  leftDegree_eq := a.source.modular.leftDegree_eq
  rightDegree_eq := a.source.modular.rightDegree_eq
  modulus_eq := a.source.modular.modulus_eq
  degree_eq := a.source.modular.degree_eq
  order_eq := fun _ => rfl
  coefficient_eq := fun q => a.coefficient_eq (pairFst q)
  leftCoefficient_eq := a.source.modular.leftCoefficient_eq
  rightCoefficient_eq := a.source.modular.rightCoefficient_eq

theorem modular_controls {F : Family} (a : Access F) (ha : a.PolyTime) : a.modular.bits.ControlsPolyTime := by
  have hb := a.source.modular_controls ha.source
  have hc := mem_FP_comp pairFst_mem_FP ha.coefficient
  constructor
  · simpa only [modular] using hb
  · exact constFn_mem_FP _
  · simpa only [modular] using hc

theorem evaluator {F : Family} (a : Access F) (ha : a.PolyTime) : SpaceFunction F.value := by
  have L := ShiftCoefficientBits.certified a.source.shiftAccess (a.source.shift_polyTime ha.source)
    F.source.shiftSource a.source.shift_represents
  have R := SpaceFunction.ofFP a.source.constantCoefficient (a.source.constantCoefficient_mem_FP ha.source)
  have E := SubresultantPolynomial.ModularAccess.evaluator a.modular (modular_controls a ha) L R
  exact E.congr (funext F.modular_value)

theorem decider {F : Family} (a : Access F) (ha : a.PolyTime) : SpaceDecider F.zeroLanguage := by
  have hflag : (fun w : List Bool => [decide (w = [])]) ∈ FP :=
    (stringEq_fppred id_mem_FP (constFn_mem_FP [])).flag_mem_FP
  apply (evaluator a ha).decider (fun w => decide (w = [])) hflag
  intro q
  let : NeZero (mValue q) := ⟨by simp only [mValue]; omega⟩
  have hz : residueBits (0 : ZMod (mValue q)) = [] := by simp [residueBits, BinaryNatCode.encode]
  change _ = 0 ↔ decide (residueBits _ = []) = true
  rw [decide_eq_true_eq, ← hz, (residueBits_injective (mValue q)).eq_iff]

theorem zeroLanguage_mem_PSPACE {F : Family} (a : Access F) (ha : a.PolyTime) : F.zeroLanguage ∈ PSPACE :=
  (decider a ha).mem_PSPACE

end Access
end LeanCanny.Algebra.CannySubresultantBits
