/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralRelativePaddedRootGuard
public import LeanCanny.Algebra.UniformIntegralPrefix
public import LeanCanny.Algebra.IntegralCoordinateBasisFin
/-! # The cut root guard at one complete successor joint root

The parent homomorphism interprets the tail of the same joint tuple. The
new quotient is its actual powered head divided by the nonzero integer
normalization leading. No independently chosen parent root appears.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralRelativeTruncation
open Polynomial UniformIntegralPowerSchedule
open scoped Classical
variable {S B m : ℕ}

noncomputable def jointQuotient (P : UniformIntegralPrefix.Prefix S (2^B) m)
    (p : Polynomial P.carrier) (d : ℕ) (z : Fin (m+1)→ℝ) : ℝ :=
  z 0^birth S (2^B) m /
    (IntegralRelativeLeadingNormalization.denominator P.basis.finBasis ((truncate p d).coeff d) : ℝ)

theorem joint_root_guard (P : UniformIntegralPrefix.Prefix S (2^B) m)
    (p : Polynomial P.carrier) (d : ℕ) (hdN : d≤2^B)
    (φ : P.carrier→ₐ[ℤ]ℝ) (z : Fin (m+1)→ℝ)
    (hφ : ∀ i,φ (P.basis.generator i)=z i.succ^weights S (2^B) m i)
    (hz : ∀ i, (UniformIntegralPrefixRows.rows S P.rows P.basis (normalized P.basis.finBasis p d) d i).eval₂
      (Int.castRingHom ℝ) z=0)
    (hp : p.map φ.toRingHom≠0) (hd : (p.map φ.toRingHom).natDegree=d) :
    p.eval₂ φ.toRingHom (jointQuotient P p d z)=0 ↔
      jointQuotient P p d z≠0 ∨ φ.toRingHom (p.coeff 0)=0 := by
  have HR:=hz 0
  simp only [UniformIntegralPrefixRows.rows,Fin.cons_zero,MvPolynomial.eval₂_rename] at HR
  have HC := PaddedIntegralParameterExtension.powered_row_root_at_evaluation P.basis
    (normalized P.basis.finBasis p d) d (Nat.two_pow_pos B) φ (weights S (2^B) m) (birth S (2^B) m)
    (z∘UniformIntegralPrefixRows.layout m) (by
      intro i
      simpa only [Function.comp_apply,UniformIntegralPrefixRows.layout,Sum.elim_inl] using hφ i) HR
  have HE := P.basis.polynomial_eval
    (PaddedIntegralNormalization.polynomial (normalized P.basis.finBasis p d) d (2^B)) φ (z 0^birth S (2^B) m)
  have HZ : (PaddedIntegralNormalization.polynomial (normalized P.basis.finBasis p d) d (2^B)).eval₂ φ.toRingHom
      (z 0^birth S (2^B) m)=0 := by
    apply HE.symm.trans
    simpa only [PaddedIntegralParameterExtension.equation,Function.comp_apply,UniformIntegralPrefixRows.layout,Sum.elim_inr] using HC
  have HD : φ ((normalized P.basis.finBasis p d).coeff d)=
      (IntegralRelativeLeadingNormalization.denominator P.basis.finBasis ((truncate p d).coeff d) : ℝ) := by
    rw [normalized,IntegralRelativeLeadingNormalization.coefficient,map_intCast]
  have Hden : (IntegralRelativeLeadingNormalization.denominator P.basis.finBasis ((truncate p d).coeff d) : ℝ)≠0 :=
    Int.cast_ne_zero.mpr (IntegralRelativeLeadingNormalization.denominator_ne_zero _ _)
  apply padded_root_guard P.basis.finBasis p d (2^B) φ hp hd hdN (jointQuotient P p d z)
  rw [HD,jointQuotient,mul_div_cancel₀ _ Hden]
  exact HZ

/-- Every complete successor root supplies its parent interpretation from
its own tail. The finite degree/nonzero tests refer to that same hom. -/
theorem exists_joint_parent (P : UniformIntegralPrefix.Prefix S (2^B) m)
    (p : Polynomial P.carrier) (d : ℕ) (hdN : d≤2^B) (z : Fin (m+1)→ℝ)
    (hz : ∀ i, (UniformIntegralPrefixRows.rows S P.rows P.basis (normalized P.basis.finBasis p d) d i).eval₂
      (Int.castRingHom ℝ) z=0) :
    ∃ φ : P.carrier→ₐ[ℤ]ℝ,
      (∀ i,φ (P.basis.generator i)=z i.succ^weights S (2^B) m i) ∧
      (p.map φ.toRingHom≠0 → (p.map φ.toRingHom).natDegree=d →
        (p.eval₂ φ.toRingHom (jointQuotient P p d z)=0 ↔
          jointQuotient P p d z≠0 ∨ φ.toRingHom (p.coeff 0)=0)) := by
  have hold : ∀ i,(P.rows i).eval₂ (Int.castRingHom ℝ) (z∘Fin.succ)=0 := by
    intro i
    have HI:=hz i.succ
    simpa only [UniformIntegralPrefixRows.rows,Fin.cons_succ,MvPolynomial.eval₂_rename] using HI
  obtain ⟨φ,hφ⟩:=P.interpret ℝ (z∘Fin.succ) hold
  refine ⟨φ,hφ,fun hp hd=>joint_root_guard P p d hdN φ z hφ hz hp hd⟩

end LeanCanny.Algebra.IntegralRelativeTruncation
