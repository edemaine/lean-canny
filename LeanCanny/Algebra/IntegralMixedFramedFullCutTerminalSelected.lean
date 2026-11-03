/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedFullCutTerminalHead
/-! # Exact selected-parent specialization of the terminal full-factor head

The unused parameter changes no coefficient. The old raw coordinates are
literally the suffix of the same terminal tuple, with their original powers.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedFullCutTerminalHead
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedFullCutHead (arity head saved degree)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent terminal : List Bool→List Bool) (d : List Bool→ℕ)

theorem embedding_eq (c : List Bool) (hc : Valid P D H parent terminal c) (i : Fin (arity P D H parent c)) :
    Fin.cast (arity_eq P D H parent terminal c hc)
      (FixedWidthSuffixLiftBits.shift (newer P D H parent terminal c) i)=
        (UniformIntegralPowerSchedule.embed hc i).succ :=by
  apply Fin.ext
  simp only [Fin.val_cast,FixedWidthSuffixLiftBits.shift,Fin.val_succ,UniformIntegralPowerSchedule.embed,newer]
  omega

theorem evaluation (c : List Bool) (hc : Valid P D H parent terminal c)
    (ha : IntegralMixedFramedFullCutProbeBits.Active P (parent c))
    (z : Fin (count P D H terminal c)→ℝ) (δ : ℝ)
    (φ : ((family P D H).state (saved P parent c)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀i,φ (((family P D H).state (saved P parent c)).sampler.scalarPrefix.basis.generator i)=
      z (UniformIntegralPowerSchedule.embed hc i)^UniformIntegralPowerSchedule.weights
        (P.cap (pairFst (saved P parent c))+1) (2^(family P D H).width (saved P parent c))
        ((family P D H).birth (saved P parent c)) i) :
    (polynomial P D H parent terminal d c).map (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (Fin.cons δ z))=
      (IntegralRelativeTruncation.truncate
        (IntegralMixedRelativeCuts.factor ((family P D H).state (saved P parent c)) ((family P D H).birth_bound _)
          ((family P D H).rule _) ((family P D H).kind _)) (degree P parent d c)).map φ.toRingHom :=by
  have HE:=IntegralMixedFramedFullCutHead.head_evaluation P D H parent d c ha
    (fun i=>z (UniformIntegralPowerSchedule.embed hc i)) φ hφ
  ext k
  have HK:=congrArg (fun q : Polynomial ℝ=>q.coeff k) HE
  rw [Polynomial.coeff_map] at HK
  rw [Polynomial.coeff_map,polynomial,dite_eq_left hc,castHead,Polynomial.coeff_map,
    FixedWidthBivariateSuffixBits.coefficient]
  change (MvPolynomial.rename (Fin.cast (arity_eq P D H parent terminal c hc))
    (MvPolynomial.rename (FixedWidthSuffixLiftBits.shift (newer P D H parent terminal c))
      ((head P D H parent d c).coeff k))).eval₂ (Int.castRingHom ℝ) (Fin.cons δ z)=_
  rw [MvPolynomial.eval₂_rename,MvPolynomial.eval₂_rename]
  have HF : (fun i : Fin (arity P D H parent c)=>(Fin.cons δ z : Fin (count P D H terminal c+1)→ℝ) (Fin.cast (arity_eq P D H parent terminal c hc)
      (FixedWidthSuffixLiftBits.shift (newer P D H parent terminal c) i)))=
        (fun i=>z (UniformIntegralPowerSchedule.embed hc i)) :=by
    funext i
    rw [embedding_eq P D H parent terminal c hc i]
    rfl
  change ((head P D H parent d c).coeff k).eval₂ (Int.castRingHom ℝ)
    (fun i : Fin (arity P D H parent c)=>(Fin.cons δ z : Fin (count P D H terminal c+1)→ℝ)
      (Fin.cast (arity_eq P D H parent terminal c hc)
        (FixedWidthSuffixLiftBits.shift (newer P D H parent terminal c) i)))=_
  rw [HF]
  exact HK

theorem selected_evaluation (c : List Bool) (hc : Valid P D H parent terminal c)
    (ha : IntegralMixedFramedFullCutProbeBits.Active P (parent c))
    (z : Fin (count P D H terminal c)→ℝ) (δ : ℝ)
    (φ : ((family P D H).state (saved P parent c)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀i,φ (((family P D H).state (saved P parent c)).sampler.scalarPrefix.basis.generator i)=
      z (UniformIntegralPowerSchedule.embed hc i)^UniformIntegralPowerSchedule.weights
        (P.cap (pairFst (saved P parent c))+1) (2^(family P D H).width (saved P parent c))
        ((family P D H).birth (saved P parent c)) i)
    (hd : ((IntegralMixedRelativeCuts.factor ((family P D H).state (saved P parent c)) ((family P D H).birth_bound _)
      ((family P D H).rule _) ((family P D H).kind _)).map φ.toRingHom).natDegree≤degree P parent d c) :
    (polynomial P D H parent terminal d c).map (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (Fin.cons δ z))=
      (IntegralMixedRelativeCuts.factor ((family P D H).state (saved P parent c)) ((family P D H).birth_bound _)
        ((family P D H).rule _) ((family P D H).kind _)).map φ.toRingHom :=
  (evaluation P D H parent terminal d c hc ha z δ φ hφ).trans (IntegralRelativeTruncation.map_eq _ _ φ hd)

end LeanCanny.Algebra.IntegralMixedFramedFullCutTerminalHead
