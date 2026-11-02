/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCoordinatePackedBounds
public import LeanCanny.Algebra.SelectedMultivariatePolynomialMass
public import LeanCanny.Algebra.PaddedIntegralEquationMass
/-! # Actual full-coordinate input mass from the original framed height profile

Every parameter coefficient uses the same saved old basis. No coefficient
mass or current-bank height is supplied independently of the original script.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCoordinatePackedBits
open Polynomial LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask FixedWidthPolynomial
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

noncomputable def oldMassBound (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (key : List Bool) :=
  (family P D H).birth key*(family P D H).width key+IntegralMixedFramedRawHeight.rootCeiling P L F C (pairFst key)

theorem atContext_mass (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (hF : ∀ root,1≤F root)
    (hf : ∀ key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
    (S : ℕ) (key : List Bool) (j y k : ℕ) :
    MvMass.mass (IntegralMixedFramedCoordinateRepresentativeBits.atContext P D H S key j y k)≤
      2^oldMassBound P D H L F C key :=by
  let x:=(family P D H).state key
  let :=x.sampler.scalarPrefix.ring
  by_cases hy : y<IntegralMixedCoordinateTrailing.ChoiceBound ((family P D H).spatial key) ((family P D H).rule key)
  · have HR :=PaddedIntegralParameterExtension.representative_mass x.sampler.scalarPrefix.basis
      (((IntegralMixedCriticalSweep.coordinate x ((family P D H).birth_bound key) ((family P D H).rule key)
        (IntegralMixedCoordinateCoefficientSnapshot.coordinate (family P D H) key j)).coeff y).coeff k)
      (IntegralMixedFramedRawHeight.rootCeiling P L F C (pairFst key)) (fun r=>?_)
    · apply (CoordinatePowerSubstitution.mass_le _ _).trans
      exact HR.trans_eq (by unfold count oldMassBound; rw [←pow_mul,←pow_add,Nat.mul_comm])
    · have HX:=IntegralMixedFramedAllCoordinateBits.coefficient_root_height P D H L F C hs hF hf key j y k r
        (IntegralCoordinateBasis.zeroFin _ _)
      unfold IntegralMixedFramedAllCoordinateBits.coefficient IntegralMixedCutMatrix.coefficientMatrix
        IntegralMixedCoordinateCoefficientSnapshot.kind IntegralMixedRelativeCuts.factor IntegralMixedCoordinateTrailing.factor at HX
      simpa only [IntegralMixedCoordinateCoefficientSnapshot.choice,Nat.mod_eq_of_lt hy] using HX
  · rw [IntegralMixedFramedCoordinateIndexBits.atContext_outside P D H S key j y k
      (Or.inl (Nat.le_of_not_gt hy)),MvMass.zero]
    exact Nat.zero_le _

noncomputable def headMassBound (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (parent : List Bool→List Bool) (e : List Bool→ℕ) (q : List Bool) :=
  oldMassBound P D H L F C (IntegralMixedVirtualTaskBits.saved P (parent q))+(e q+1).size

theorem head_mass (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (hF : ∀ root,1≤F root)
    (hf : ∀ key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
    (parent : List Bool→List Bool) (d e : List Bool→ℕ) (q : List Bool) (y : ℕ) :
    MvMass.mass ((head P D H parent d e q).coeff y)≤2^headMassBound P D H L F C parent e q :=by
  let key:=IntegralMixedVirtualTaskBits.saved P (parent q)
  let x:=(family P D H).state key
  let :=x.sampler.scalarPrefix.ring
  unfold head headMassBound
  apply SelectedMultivariatePolynomialLift.coefficient_mass_pow
  intro k _
  exact atContext_mass P D H L F C hs hF hf _ key (get P .slot13 (parent q)) y k

theorem guardedHead_mass (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (hF : ∀ root,1≤F root)
    (hf : ∀ key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
    (parent : List Bool→List Bool) (d e : List Bool→ℕ) (q : List Bool) (y : ℕ) :
    MvMass.mass ((guardedHead P D H parent d e q).coeff y)≤2^headMassBound P D H L F C parent e q :=by
  unfold guardedHead
  split_ifs
  · exact head_mass P D H L F C hs hF hf parent d e q y
  · simp

theorem oldMassBound_binary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (I : IntegralMixedVirtualQueryBits.InputMetadata (family P D H)) : BinaryFn (oldMassBound P D H L F C) :=
  ((BinaryFn.ofUnary I.birth).mul (BinaryFn.ofUnary I.width)).add
    ((IntegralMixedFramedRawHeight.rootCeiling_binary P a hL hF hC).comp pairFst_mem_FP)

theorem headMassBound_binary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (I : IntegralMixedVirtualQueryBits.InputMetadata (family P D H))
    (parent : List Bool→List Bool) (hp : parent∈FP) (e : List Bool→ℕ) (he : BinaryFn e) :
    BinaryFn (headMassBound P D H L F C parent e) :=by
  have HO : BinaryFn (fun q=>oldMassBound P D H L F C (IntegralMixedVirtualTaskBits.saved P (parent q))) :=
    (oldMassBound_binary P a D H L F C hL hF hC I).comp
      (mem_FP_comp hp (IntegralMixedVirtualTaskBits.saved_FP P a))
  exact HO.add ((he.add (BinaryFn.const 1)).size)

end LeanCanny.Algebra.IntegralMixedFramedCoordinatePackedBits
