/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationInverseTerm
public import LeanCanny.Algebra.IntegralMixedValueFieldQuery
/-! # A bounded inverse sum requests actual phase-ten terms -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource
set_option backward.isDefEq.respectTransparency false

noncomputable def inverseTermAt (F : Family) (key : List Bool) (m k r t : ℕ) : List Bool :=
  residueBits ((((IntegralParameterInverse.inverse (top F key).charpoly).coeff k : ℤ) : ZMod m) *
    ((((top F key).map (Int.castRingHom (ZMod m))) ^ k)
      ⟨r % dimension F key, Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩
      ⟨t % dimension F key, Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩))

theorem inverseTerm_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    inverseTermValue P F q = inverseTermAt F (IntegralMixedVirtualTaskBits.saved P q)
      (modulus P q) (get P .target q) (get P .row q) (get P .col q) := rfl

def termTask (P : Parameters) :=
  IntegralMixedValueFieldQuery.query P pairFst .normalization .frozenPowerSum .target
    (fun z => Nat.fromBitsLE (pairSnd z))

theorem termTask_FP (P : Parameters) (a : Access P) : termTask P ∈ FP :=
  IntegralMixedValueFieldQuery.query_FP P a pairFst pairFst_mem_FP .normalization .frozenPowerSum .target
    _ (BinaryFn.fromBits pairSnd_mem_FP)

attribute [local irreducible] inverseTermAt

theorem termTask_value (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) (k : ℕ) (hk : k < matrixDimension P F q + 1) :
    inverseTermValue P F (termTask P (pair q (BinaryNatCode.encode k))) =
      residueBits ((((IntegralParameterInverse.inverse (top F (IntegralMixedVirtualTaskBits.saved P q)).charpoly).coeff k : ℤ) :
        ZMod (modulus P q)) * ((modularTop P F q ^ k)
          (topRow P F q) (topCol P F q))) := by
  have HK : k ≤ numericCap P (RankedHistoryTask.root q) :=
    (by omega : k ≤ matrixDimension P F q).trans (dimension_cap P F g q hv)
  unfold termTask
  rw [inverseTerm_snapshot,
    IntegralMixedValueFieldQuery.query_saved P pairFst .normalization .frozenPowerSum .target _ _ (by decide),
    IntegralMixedValueFieldQuery.query_modulus P pairFst .normalization .frozenPowerSum .target _ _ (by decide),
    IntegralMixedValueFieldQuery.query_field P pairFst .normalization .frozenPowerSum .target _ _ (by decide)
      (by simpa only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using HK),
    IntegralMixedValueFieldQuery.query_other P pairFst .normalization .frozenPowerSum .target _ _ .row (by decide) (by decide),
    IntegralMixedValueFieldQuery.query_other P pairFst .normalization .frozenPowerSum .target _ _ .col (by decide) (by decide)]
  simp only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  unfold inverseTermAt modularTop topRow topCol
  rfl

abbrev InverseTermMatches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 5 →
    isPhase .frozenPowerSum q → get P .target q ≤ matrixDimension P F q → answer q = inverseTermValue P F q

theorem termTask_reply (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (hx : InverseTermMatches P F answer) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (k : ℕ) (hk : k < matrixDimension P F q + 1) :
    answer (termTask P (pair q (BinaryNatCode.encode k))) =
      residueBits ((((IntegralParameterInverse.inverse (top F (IntegralMixedVirtualTaskBits.saved P q)).charpoly).coeff k : ℤ) :
        ZMod (modulus P q)) * ((modularTop P F q ^ k)
          (topRow P F q) (topCol P F q))) := by
  let z := pair q (BinaryNatCode.encode k)
  let c := termTask P z
  have HV : IntegralMixedVirtualCaps.valid P c := by
    unfold IntegralMixedVirtualCaps.valid c termTask
    rw [IntegralMixedValueFieldQuery.query_birth, IntegralMixedValueFieldQuery.query_root, pairFst_pair]
    exact hv
  have HR : IntegralMixedRoutineTaskBits.routine P c = 5 :=
    IntegralMixedValueFieldQuery.query_routine P pairFst .normalization .frozenPowerSum .target _ z
  have HP : isPhase .frozenPowerSum c := IntegralMixedValueFieldQuery.query_phase P pairFst .normalization .frozenPowerSum .target _ z
  have HD : matrixDimension P F c = matrixDimension P F q := by
    apply congrArg (dimension F)
    exact (IntegralMixedValueFieldQuery.query_saved P pairFst .normalization .frozenPowerSum .target _ z (by decide)).trans
      (congrArg (IntegralMixedVirtualTaskBits.saved P) (pairFst_pair _ _))
  have HI : get P .target c = k := by
    have HC := IntegralMixedValueFieldQuery.query_field P pairFst .normalization .frozenPowerSum .target
      (fun z => Nat.fromBitsLE (pairSnd z)) z (by decide)
      (by simpa only [z, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using
        ((by omega : k ≤ matrixDimension P F q).trans (dimension_cap P F g q hv)))
    simpa only [c, termTask, z, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using HC
  exact (hx c HV HR HP (by rw [HI, HD]; omega)).trans (termTask_value P F g q hv k hk)

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits
