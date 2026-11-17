/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.CoordinateFingerprintSelection
public import LeanCanny.CountingHierarchy.Controlled

/-! # Total bounded fingerprint choices from arbitrary binary tuple entries -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM

def normalizedFingerprintModulus (D raw : ℕ) : ℕ := 3 + raw % (2 * (D ^ 3 + 2) - 2)

def normalizedFingerprintData (D r g t : ℕ) : FingerprintLabelData :=
  let mu := normalizedFingerprintModulus D r
  let mag := (t / 2) % (D * mu + 1)
  ⟨mu, g % mu, if t % 2 = 0 then (mag : ℤ) else -(mag : ℤ)⟩

theorem normalizedFingerprintData_bounded (D r g t : ℕ) :
    (normalizedFingerprintData D r g t).Bounded D := by
  change 2 < normalizedFingerprintModulus D r ∧
    normalizedFingerprintModulus D r ≤ 2 * (D ^ 3 + 2) ∧
    g % normalizedFingerprintModulus D r < normalizedFingerprintModulus D r ∧
    (if t % 2 = 0 then (((t / 2) % (D * normalizedFingerprintModulus D r + 1) : ℕ) : ℤ)
      else -(((t / 2) % (D * normalizedFingerprintModulus D r + 1) : ℕ) : ℤ)).natAbs ≤
      D * normalizedFingerprintModulus D r
  have hden : 0 < 2 * (D ^ 3 + 2) - 2 := by omega
  have hr := Nat.mod_lt r hden
  have hmu : 0 < normalizedFingerprintModulus D r := by unfold normalizedFingerprintModulus; omega
  refine ⟨by unfold normalizedFingerprintModulus; omega,
    by unfold normalizedFingerprintModulus; omega, Nat.mod_lt g hmu, ?_⟩
  have hm := Nat.mod_lt (t / 2) (by omega : 0 < D * normalizedFingerprintModulus D r + 1)
  split_ifs <;> simp only [Int.natAbs_natCast, Int.natAbs_neg] <;> omega

/-- Every allowed fingerprint has a bounded tuple preimage; normalization loses
no complete choices, while it makes all malformed tuples usable. -/
theorem exists_normalizedFingerprintData (D : ℕ) (L : FingerprintLabelData) (hL : L.Bounded D) :
    ∃ r g t : ℕ, r ≤ 2 * (D ^ 3 + 2) ∧ g ≤ 2 * (D ^ 3 + 2) ∧
      t ≤ 2 * (D * (2 * (D ^ 3 + 2))) + 1 ∧ normalizedFingerprintData D r g t = L := by
  rcases L with ⟨mu, gamma, target⟩
  change 2 < mu ∧ mu ≤ 2 * (D ^ 3 + 2) ∧ gamma < mu ∧ target.natAbs ≤ D * mu at hL
  obtain ⟨hmin, hmax, hg, htarget⟩ := hL
  have hm : normalizedFingerprintModulus D (mu - 3) = mu := by
    unfold normalizedFingerprintModulus
    rw [Nat.mod_eq_of_lt (by omega : mu - 3 < 2 * (D ^ 3 + 2) - 2)]
    omega
  have hgamma : gamma % mu = gamma := Nat.mod_eq_of_lt hg
  cases target with
  | ofNat v =>
    change v ≤ D * mu at htarget
    have hv := htarget.trans (Nat.mul_le_mul_left D hmax)
    refine ⟨mu - 3, gamma, 2 * v, by omega, by omega, by omega, ?_⟩
    have hhalf : (2 * v) / 2 = v := by omega
    have hparity : (2 * v) % 2 = 0 := by omega
    simp only [normalizedFingerprintData, hm, hgamma, hhalf, hparity, ite_true,
      Nat.mod_eq_of_lt (by omega : v < D * mu + 1)]
    rfl
  | negSucc v =>
    change v + 1 ≤ D * mu at htarget
    have hv := htarget.trans (Nat.mul_le_mul_left D hmax)
    refine ⟨mu - 3, gamma, 2 * (v + 1) + 1, by omega, by omega, by omega, ?_⟩
    have hhalf : (2 * (v + 1) + 1) / 2 = v + 1 := by omega
    have hparity : (2 * (v + 1) + 1) % 2 = 1 := by omega
    simp only [normalizedFingerprintData, hm, hgamma, hhalf, hparity, Nat.one_ne_zero, ite_false,
      Nat.mod_eq_of_lt (by omega : v + 1 < D * mu + 1)]
    rfl

@[fun_prop] theorem normalizedFingerprintModulus_polyTime {α : Type} {enc : α ↪ List Bool}
    {D raw : α → ℕ} (hD : ComputableInPolyTime D enc encNat) (hr : ComputableInPolyTime raw enc encNat) :
    ComputableInPolyTime (fun w => normalizedFingerprintModulus (D w) (raw w)) enc encNat := by
  have hden := ComputableInPolyTime.binary_sub'
    (ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const 2)
      (ComputableInPolyTime.binary_add' (ComputableInPolyTime.binary_pow' hD (.const 3)) (.const 2))) (.const 2)
  exact ComputableInPolyTime.binary_add' (.const 3) (ComputableInPolyTime.binary_mod.comp (hr.prod hden))

@[fun_prop] theorem normalizedFingerprintData_parameter_polyTime {α : Type} {enc : α ↪ List Bool}
    {D r g t : α → ℕ} (hD : ComputableInPolyTime D enc encNat) (hr : ComputableInPolyTime r enc encNat)
    (hg : ComputableInPolyTime g enc encNat) :
    ComputableInPolyTime (fun w => (normalizedFingerprintData (D w) (r w) (g w) (t w)).parameter) enc encNat :=
  ComputableInPolyTime.binary_mod.comp (hg.prod (normalizedFingerprintModulus_polyTime hD hr))

@[fun_prop] theorem normalizedFingerprintData_target_polyTime {α : Type} {enc : α ↪ List Bool}
    {D r g t : α → ℕ} (hD : ComputableInPolyTime D enc encNat) (hr : ComputableInPolyTime r enc encNat)
    (ht : ComputableInPolyTime t enc encNat) :
    ComputableInPolyTime (fun w => (normalizedFingerprintData (D w) (r w) (g w) (t w)).target) enc encIntBin := by
  have hmu := normalizedFingerprintModulus_polyTime hD hr
  have hB := ComputableInPolyTime.binary_add' (ComputableInPolyTime.binary_mul' hD hmu) (ComputableInPolyTime.const 1)
  have hhalf := ComputableInPolyTime.binary_div.comp (ht.prod (ComputableInPolyTime.const 2))
  have hmag := ComputableInPolyTime.intBin_natCast.comp
    (ComputableInPolyTime.binary_mod.comp (hhalf.prod hB))
  have hparity := ComputableInPolyTime.binary_mod.comp (ht.prod (ComputableInPolyTime.const 2))
  have hguard : ComputableInPolyTime (fun w => decide (t w % 2 = 0)) enc encBool := by
    simpa only [Function.comp_def, Nat.le_zero_eq] using
      ComputableInPolyTime.binary_le' hparity (ComputableInPolyTime.const 0)
  simpa only [normalizedFingerprintData, Function.comp_def] using
    (ComputableTidilyInPolyTime.ite_decide hguard.tidy hmag.tidy
      (ComputableInPolyTime.intBin_neg.comp hmag).tidy).computableInPolyTime

end LeanCanny.CountingHierarchy
