/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedHistoryScript
public import LeanCanny.Algebra.IntegralMixedIntegerRealization
public import LeanCanny.Algebra.IntegralIntegerRootBank
/-! # Re-adjoining prescribed real integer roots in an actual mixed prefix

The target sampler, scalar width and physical carrier are independent of any
previous realization of these roots. Integer leading coefficients are retained
literally; interpreting the target bank recovers the prescribed roots.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedIntegerRealization
open IntegralMixedHistory IntegralHistorySampler
open IntegralMixedFramedHistoryScript
open IntegralMixedIntegerRealization (Root Realizes)
open UniformIntegralPrefix UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem exists_realization (initial : State P S B 0 ι) (z : ι → ℝ)
    (hz : ∀ i, (initial.sampler.rows i).eval₂ (Int.castRingHom ℝ) z = 0)
    (cs : List (Instruction n B)) (hc : cs.length ≤ S+1) (t : Fin cs.length → ℝ)
    (ht : ∀ i, Root cs[i].command (t i)) :
    ∃ y : Index ι cs → ℝ,
      ∃ φ : (run initial cs hc).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ,
        (∀ i, ((run initial cs hc).sampler.rows i).eval₂ (Int.castRingHom ℝ) y = 0) ∧
        (∀ i, φ ((run initial cs hc).sampler.scalarPrefix.basis.generator i) =
          y ((run initial cs hc).sampler.scalar i) ^ weights S (2^B) cs.length i) ∧
        ∀ i, φ ((run initial cs hc).bank.numerator i) /
          ((run initial cs hc).bank.denominator i:ℝ) = t i := by
  induction cs with
  | nil =>
    obtain ⟨φ,hφ⟩ := initial.sampler.interpret ℝ z hz
    exact ⟨z,φ,hz,hφ,fun i => Fin.elim0 i⟩
  | cons c cs ih =>
    obtain ⟨Q,hQ,c⟩ := c
    cases c with
    | critical r => exact False.elim (ht 0)
    | cut r k d ha hd => exact False.elim (ht 0)
    | integer p hp hd =>
      let x := reframe (run initial cs (by simp only [List.length_cons] at hc; omega : cs.length ≤ S+1)) Q hQ
      obtain ⟨w,φ,hw,hφ,hvalues⟩ := ih (by simp only [List.length_cons] at hc; omega)
        (fun i => t i.succ) (fun i => ht i.succ)
      let q : Polynomial x.sampler.scalarPrefix.carrier := p.map (Int.castRingHom _)
      have HC : φ.toRingHom.comp (Int.castRingHom x.sampler.scalarPrefix.carrier) = Int.castRingHom ℝ :=
        RingHom.ext_int _ _
      have hmap : q.map φ.toRingHom = p.map (Int.castRingHom ℝ) := by
        dsimp only [q]
        rw [Polynomial.map_map,HC]
      have hroot : q.eval₂ φ.toRingHom (t 0) = 0 := by
        dsimp only [q]
        rw [Polynomial.eval₂_map,HC]
        exact ht 0
      have hdegree : (q.map φ.toRingHom).natDegree = p.natDegree := by
        rw [hmap]
        exact Polynomial.natDegree_map_eq_of_injective (Int.cast_injective (α:=ℝ)) _
      have hpos : 1 ≤ p.natDegree := Polynomial.natDegree_pos_of_eval₂_root hp
        (Int.castRingHom ℝ) (ht 0) (by intro a ha; exact Int.cast_eq_zero.mp ha)
      have hcoeff : q.coeff p.natDegree = (p.leadingCoeff:x.sampler.scalarPrefix.carrier) := by
        dsimp only [q]
        rw [Polynomial.coeff_map,Polynomial.coeff_natDegree]
        rfl
      obtain ⟨y,hy,htail,hhead⟩ := scalarStep_real_extend_recover_root_integer x.sampler
        (by simp only [List.length_cons] at hc; omega : cs.length ≤ S) (Nat.two_pow_pos B)
        q p.natDegree hd p.leadingCoeff (Polynomial.leadingCoeff_ne_zero.mpr hp) hcoeff
        w hw φ hφ (t 0) hdegree hpos hroot
      obtain ⟨ψ,hψ⟩ := (integerStep x (by simp only [List.length_cons] at hc; omega) p hp hd).sampler.interpret ℝ y hy
      have hrestrict : ψ.comp (AdjoinRoot.ofAlgHom ℤ _) = φ := by
        apply x.sampler.scalarPrefix.basis.algHom_ext
        intro i
        have H := hψ i.succ
        change ψ (AdjoinRoot.of _ (x.sampler.scalarPrefix.basis.generator i)) =
          y (Sum.inl (x.sampler.scalar i)) ^ weights S (2^B) (cs.length+1) i.succ at H
        rw [UniformIntegralPowerSchedule.old,htail] at H
        exact H.trans (hφ i).symm
      refine ⟨y,ψ,hy,hψ,?_⟩
      intro i
      refine Fin.cases (hhead ψ hψ) (fun j => ?_) i
      change ψ (AdjoinRoot.of _ (x.bank.numerator j))/(x.bank.denominator j:ℝ)=t j.succ
      have HE : ψ (AdjoinRoot.of _ (x.bank.numerator j))=φ (x.bank.numerator j) :=
        congrArg (fun χ => χ (x.bank.numerator j)) hrestrict
      rw [HE]
      exact hvalues j

theorem realizes (initial : State P S B 0 ι) (z : ι → ℝ)
    (hz : ∀ i, (initial.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (cs : List (Instruction n B)) (hc : cs.length ≤ S+1) (t : ℕ → ℝ)
    (ht : ∀ i : Fin cs.length, Root cs[i].command (t i.val)) :
    Realizes (run initial cs hc) t := exists_realization initial z hz cs hc (fun i => t i.val) ht

end LeanCanny.Algebra.IntegralMixedFramedIntegerRealization
