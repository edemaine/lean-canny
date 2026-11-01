/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralScalarRootHeightBank

/-! # A finite bank of independently retained integer-polynomial roots

Every scalar birth uses its actual integer polynomial and integer leading
coefficient. All old physical coordinates remain literally unchanged.
The resulting coefficient algebra contains integral numerators for every
chosen root, with the original integer leading coefficients as denominators.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralIntegerRootBank
open LeanCanny.Encoding LeanCanny.Computation IntegralHistorySampler UniformIntegralPrefix
open UniformIntegralPowerSchedule
open scoped Classical

def Index (ι : Type) : ℕ → Type
  | 0 => ι
  | m + 1 => Index ι m ⊕ Unit

instance indexFintype (ι : Type) [Fintype ι] : (m : ℕ) → Fintype (Index ι m)
  | 0 => inferInstanceAs (Fintype ι)
  | m + 1 => by
    change Fintype (Index ι m ⊕ Unit)
    letI := indexFintype ι m
    infer_instance

def old {ι : Type} : (m : ℕ) → ι → Index ι m
  | 0 => id
  | m + 1 => Sum.inl ∘ old m

theorem card_index {ι : Type} [Fintype ι] (m : ℕ) : Fintype.card (Index ι m) = Fintype.card ι + m := by
  induction m with
  | zero =>
    simp only [Index, Nat.add_zero]
    rfl
  | succ m ih => simp only [Index, Fintype.card_sum, Fintype.card_unique, ih, Nat.add_assoc]

structure State (S B m : ℕ) (ι : Type) where
  sampler : Sampler S (2 ^ B) m ι
  bank : HeightBank sampler.scalarPrefix
  denominator_ne_zero : ∀ i, bank.denominator i ≠ 0

noncomputable def base {S B : ℕ} {ι : Type} (F : Sampler S (2 ^ B) 0 ι) : State S B 0 ι where
  sampler := F
  bank := { numerator := Fin.elim0, denominator := Fin.elim0 }
  denominator_ne_zero := by intro i; exact Fin.elim0 i

noncomputable def step {S B m : ℕ} {ι : Type} [Fintype ι]
    (x : State S B m ι) (hm : m ≤ S) (p : Polynomial ℤ) (hp : p ≠ 0) : State S B (m + 1) (ι ⊕ Unit) where
  sampler := scalarStep x.sampler hm (Nat.two_pow_pos B) (p.map (Int.castRingHom x.sampler.scalarPrefix.carrier)) p.natDegree
  bank := x.bank.rootStep hm (p.map (Int.castRingHom x.sampler.scalarPrefix.carrier)) p.natDegree p.leadingCoeff
  denominator_ne_zero := x.bank.rootStep_denominator_ne_zero hm _ _ _ (Polynomial.leadingCoeff_ne_zero.mpr hp) x.denominator_ne_zero

noncomputable def run {S B : ℕ} {ι : Type} [Fintype ι] (F : Sampler S (2 ^ B) 0 ι) :
    (m : ℕ) → (p : Fin m → Polynomial ℤ) → (∀ i, p i ≠ 0) → m ≤ S + 1 → State S B m (Index ι m)
  | 0, _, _, _ => base F
  | m + 1, p, hp, hm =>
    step (run F m (fun i => p i.succ) (fun i => hp i.succ) (by omega)) (by omega) (p 0) (hp 0)

theorem denominator_run {S B : ℕ} {ι : Type} [Fintype ι] (F : Sampler S (2 ^ B) 0 ι)
    (m : ℕ) (p : Fin m → Polynomial ℤ) (hp : ∀ i, p i ≠ 0) (hm : m ≤ S + 1) (i : Fin m) :
    (run F m p hp hm).bank.denominator i = (p i).leadingCoeff := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    refine Fin.cases rfl (fun j => ?_) i
    exact ih (fun i => p i.succ) (fun i => hp i.succ) (by omega) j

theorem exists_realization {S B : ℕ} {ι : Type} [Fintype ι] (F : Sampler S (2 ^ B) 0 ι)
    (z : ι → ℝ) (hz : ∀ i, (F.rows i).eval₂ (Int.castRingHom ℝ) z = 0)
    (m : ℕ) (p : Fin m → Polynomial ℤ) (hp : ∀ i, p i ≠ 0) (hm : m ≤ S + 1)
    (hcap : ∀ i, (p i).natDegree ≤ 2 ^ B) (t : Fin m → ℝ)
    (ht : ∀ i, (p i).eval₂ (Int.castRingHom ℝ) (t i) = 0) :
    ∃ y : Index ι m → ℝ,
      ∃ φ : (run F m p hp hm).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ,
        (∀ i, ((run F m p hp hm).sampler.rows i).eval₂ (Int.castRingHom ℝ) y = 0) ∧
        (∀ i, y (old m i) = z i) ∧
        (∀ i, φ ((run F m p hp hm).sampler.scalarPrefix.basis.generator i) =
          y ((run F m p hp hm).sampler.scalar i) ^ weights S (2 ^ B) m i) ∧
        ∀ i, φ ((run F m p hp hm).bank.numerator i) /
          ((run F m p hp hm).bank.denominator i : ℝ) = t i := by
  induction m with
  | zero =>
    simp only [run, base, old]
    obtain ⟨φ, hφ⟩ := F.interpret ℝ z hz
    exact ⟨z, φ, hz, (fun _ => rfl), hφ, fun i => Fin.elim0 i⟩
  | succ m ih =>
    let x := run F m (fun i => p i.succ) (fun i => hp i.succ) (by omega : m ≤ S + 1)
    obtain ⟨w, φ, hw, hold, hφ, hvalues⟩ := ih (fun i => p i.succ) (fun i => hp i.succ) (by omega)
      (fun i => hcap i.succ) (fun i => t i.succ) (fun i => ht i.succ)
    let q : Polynomial x.sampler.scalarPrefix.carrier := (p 0).map (Int.castRingHom _)
    have hmap : q.map φ.toRingHom = (p 0).map (Int.castRingHom ℝ) := by
      dsimp only [q]
      rw [Polynomial.map_map]
      congr 1
      exact RingHom.ext_int _ _
    have HC : φ.toRingHom.comp (Int.castRingHom x.sampler.scalarPrefix.carrier) = Int.castRingHom ℝ := RingHom.ext_int _ _
    have hroot : q.eval₂ φ.toRingHom (t 0) = 0 := by
      dsimp only [q]
      rw [Polynomial.eval₂_map, HC]
      exact ht 0
    have hdegree : (q.map φ.toRingHom).natDegree = (p 0).natDegree := by
      rw [hmap]
      exact Polynomial.natDegree_map_eq_of_injective (Int.cast_injective (α := ℝ)) _
    have hpos : 1 ≤ (p 0).natDegree := Polynomial.natDegree_pos_of_eval₂_root (hp 0)
      (Int.castRingHom ℝ) (ht 0) (by intro a ha; exact Int.cast_eq_zero.mp ha)
    have hcoeff : q.coeff (p 0).natDegree = ((p 0).leadingCoeff : x.sampler.scalarPrefix.carrier) := by
      dsimp only [q]
      rw [Polynomial.coeff_map, Polynomial.coeff_natDegree]
      rfl
    obtain ⟨y, hy, htail, hhead⟩ := scalarStep_real_extend_recover_root_integer x.sampler (by omega : m ≤ S)
      (Nat.two_pow_pos B) q (p 0).natDegree (hcap 0) (p 0).leadingCoeff
      (Polynomial.leadingCoeff_ne_zero.mpr (hp 0)) hcoeff w hw φ hφ (t 0) hdegree hpos hroot
    obtain ⟨ψ, hψ⟩ := (step x (by omega : m ≤ S) (p 0) (hp 0)).sampler.interpret ℝ y hy
    have hrestrict : ψ.comp (AdjoinRoot.ofAlgHom ℤ _) = φ := by
      apply x.sampler.scalarPrefix.basis.algHom_ext
      intro i
      have H := hψ i.succ
      change ψ (AdjoinRoot.of _ (x.sampler.scalarPrefix.basis.generator i)) =
        y (Sum.inl (x.sampler.scalar i)) ^ weights S (2 ^ B) (m + 1) i.succ at H
      rw [UniformIntegralPowerSchedule.old, htail] at H
      exact H.trans (hφ i).symm
    refine ⟨y, ψ, hy, ?_, hψ, ?_⟩
    · intro i
      exact (htail (old m i)).trans (hold i)
    · intro i
      refine Fin.cases (hhead ψ hψ) (fun j => ?_) i
      change ψ (AdjoinRoot.of _ (x.bank.numerator j)) / (x.bank.denominator j : ℝ) = t j.succ
      have HE : ψ (AdjoinRoot.of _ (x.bank.numerator j)) = φ (x.bank.numerator j) :=
        congrArg (fun χ => χ (x.bank.numerator j)) hrestrict
      rw [HE]
      exact hvalues j

end LeanCanny.Algebra.IntegralIntegerRootBank
