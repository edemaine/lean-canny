/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullHistoryPhysicalBridge
public import LeanCanny.Algebra.IntegralScalarGeneratorChargedPost
public import LeanCanny.Algebra.IntegralIntegerCompanionSource
/-! # Integer producer polynomials over the actual shared mixed prefix -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedIntegerProducerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFullHistoryScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def polynomial (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (key : List Bool) : Polynomial ℤ :=
  match IntegralMixedFullHistoryFamilyBits.creating P D key with
  | some (.integer p _ _) => p
  | _ => Polynomial.X

theorem polynomial_actual (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (key : List Bool)
    (p : Polynomial ℤ) (hp : p ≠ 0) (hd : p.natDegree ≤ 2 ^ P.width (pairFst key))
    (hc : IntegralMixedFullHistoryFamilyBits.creating P D key = some (.integer p hp hd)) : polynomial P D key = p := by
  unfold polynomial
  rw [hc]

theorem polynomial_ne_zero (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (key : List Bool) :
    polynomial P D key ≠ 0 := by
  unfold polynomial
  split
  · assumption
  · exact Polynomial.X_ne_zero

theorem degree_cap (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (key : List Bool) :
    (polynomial P D key).natDegree ≤ 2 ^ P.width (pairFst key) := by
  unfold polynomial
  split
  · assumption
  · rw [Polynomial.natDegree_X]
    exact Nat.one_le_two_pow

noncomputable abbrev bank (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) := IntegralMixedFullHistoryFamilyBits.family P D

noncomputable def oldRank (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) : ℕ :=
  count ((bank P D).birth (IntegralMixedVirtualTaskBits.saved P q)) ((bank P D).width (IntegralMixedVirtualTaskBits.saved P q))

noncomputable def newRank (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) : ℕ :=
  count ((bank P D).birth (IntegralMixedVirtualTaskBits.saved P q) + 1) ((bank P D).width (IntegralMixedVirtualTaskBits.saved P q))

noncomputable def family (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) : PaddedIntegralGeneratorFinBits.Family where
  arity q := (bank P D).birth (IntegralMixedVirtualTaskBits.saved P q)
  width q := (bank P D).width (IntegralMixedVirtualTaskBits.saved P q)
  carrier q := ((bank P D).state (IntegralMixedVirtualTaskBits.saved P q)).sampler.scalarPrefix.carrier
  ring q := ((bank P D).state (IntegralMixedVirtualTaskBits.saved P q)).sampler.scalarPrefix.ring
  nontrivial q := ((bank P D).state (IntegralMixedVirtualTaskBits.saved P q)).sampler.scalarPrefix.nontrivial
  basis q := ((bank P D).state (IntegralMixedVirtualTaskBits.saved P q)).sampler.scalarPrefix.basis
  polynomial q := (polynomial P D (IntegralMixedVirtualTaskBits.saved P q)).map (Int.castRingHom _)
  degree q := (polynomial P D (IntegralMixedVirtualTaskBits.saved P q)).natDegree
  modulus := modulus P
  modulus_ne_zero := modulus_ne_zero P
  row q := ⟨get P .row q % newRank P D q, Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩
  col q := ⟨get P .col q % newRank P D q, Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩

noncomputable def leadingInteger (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) : ℤ :=
  (polynomial P D (IntegralMixedVirtualTaskBits.saved P q)).leadingCoeff

theorem leading_coefficient (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    letI := (family P D).ring q
    ((family P D).polynomial q).coeff ((family P D).degree q) = (leadingInteger P D q : (family P D).carrier q) :=
  IntegralIntegerCompanionBits.leading_eq (family P D)
    (fun q => polynomial P D (IntegralMixedVirtualTaskBits.saved P q)) (fun _ => rfl) (fun _ => rfl) q

noncomputable def scalarFamily (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) : IntegralScalarGeneratorBits.Family :=
  IntegralScalarGeneratorBits.finFamily (family P D) (leadingInteger P D) (leading_coefficient P D)

end LeanCanny.Algebra.IntegralMixedIntegerProducerBits
