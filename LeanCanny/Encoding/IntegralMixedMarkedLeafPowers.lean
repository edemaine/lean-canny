/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedLeafScan
/-! # Untruncated leaf roots fix the retained large power parameters -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedLeafPowers
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegerPolynomialSourceChoice
open IntegralMixedAuxiliaryMarkedIntegerSource (number source tag oldKey tail beta)
open IntegralMixedAuxiliaryParametricSlackSource (regularizationAt penaltyAt)
open IntegralMixedCandidateReplayNew (input sampleContext)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
  (R : List Bool→ℕ)

attribute [local irreducible] oldKey beta regularizationAt penaltyAt PowerIntegerPolynomial.polynomial

theorem polynomial_radius (ctx : List Bool) :
    (source hn ht ha R).polynomial (pair ctx (BinaryNatCode.encode (number n ctx+4)))=
      PowerIntegerPolynomial.polynomial False (R ctx) := by
  simp only [IntegralMixedAuxiliaryMarkedIntegerSource.source,choose,reindex,Function.comp_apply,tag,
    pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,PowerIntegerPolynomial.source]
  split_ifs <;> first | omega | rfl

theorem polynomial_regularization (ctx : List Bool) :
    (source hn ht ha R).polynomial (pair ctx (BinaryNatCode.encode (number n ctx+5)))=
      PowerIntegerPolynomial.polynomial False (regularizationAt n t (R∘tail) (oldKey n t ctx)) := by
  simp only [IntegralMixedAuxiliaryMarkedIntegerSource.source,choose,reindex,Function.comp_apply,tag,
    pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,PowerIntegerPolynomial.source]
  split_ifs <;> first | omega | rfl

theorem polynomial_perturbation (ctx : List Bool) :
    (source hn ht ha R).polynomial (pair ctx (BinaryNatCode.encode (number n ctx+6)))=
      PowerIntegerPolynomial.polynomial False (beta n t (R∘tail) (oldKey n t ctx)) := by
  simp only [IntegralMixedAuxiliaryMarkedIntegerSource.source,choose,reindex,Function.comp_apply,tag,
    pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,PowerIntegerPolynomial.source]
  split_ifs <;> first | omega | rfl

theorem polynomial_penalty (ctx : List Bool) :
    (source hn ht ha R).polynomial (pair ctx (BinaryNatCode.encode (number n ctx+7)))=
      PowerIntegerPolynomial.polynomial False (penaltyAt n t (R∘tail) (oldKey n t ctx)) := by
  simp only [IntegralMixedAuxiliaryMarkedIntegerSource.source,choose,reindex,Function.comp_apply,tag,
    pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,PowerIntegerPolynomial.source]
  split_ifs <;> first | omega | rfl

private theorem power_root (E : ℕ) (v : ℝ) :
    (PowerIntegerPolynomial.polynomial False E).eval₂ (Int.castRingHom ℝ) v=0 ↔ v=(2:ℝ)^E := by
  rw [PowerIntegerPolynomial.root_iff]
  simp only [PowerIntegerPolynomial.value,ite_false,Int.cast_pow,Int.cast_ofNat]

variable {R} (hR : BinaryFn R)
  (ctx w : List Bool)
  (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR) (sampleContext ctx) w)
  (h : ∀ i<number n ctx+8,((source hn ht ha R).polynomial (pair ctx (BinaryNatCode.encode i))).eval₂
    (Int.castRingHom ℝ) (IntegralMixedMarkedLeafTest.point hn ht ha hR ctx w hv i)=0)

include h in
theorem radius : IntegralMixedMarkedLeafTest.point hn ht ha hR ctx w hv (number n ctx+4)=(2:ℝ)^(R ctx) := by
  have H:=h (number n ctx+4) (by omega)
  rw [polynomial_radius] at H
  exact (power_root _ _).mp H

include h in
theorem regularization : IntegralMixedMarkedLeafTest.point hn ht ha hR ctx w hv (number n ctx+5)=(2:ℝ)^(regularizationAt n t (R∘tail) (oldKey n t ctx)) := by
  have H:=h (number n ctx+5) (by omega)
  rw [polynomial_regularization] at H
  exact (power_root _ _).mp H

include h in
theorem perturbation : IntegralMixedMarkedLeafTest.point hn ht ha hR ctx w hv (number n ctx+6)=(2:ℝ)^(beta n t (R∘tail) (oldKey n t ctx)) := by
  have H:=h (number n ctx+6) (by omega)
  rw [polynomial_perturbation] at H
  exact (power_root _ _).mp H

include h in
theorem penalty : IntegralMixedMarkedLeafTest.point hn ht ha hR ctx w hv (number n ctx+7)=(2:ℝ)^(penaltyAt n t (R∘tail) (oldKey n t ctx)) := by
  have H:=h (number n ctx+7) (by omega)
  rw [polynomial_penalty] at H
  exact (power_root _ _).mp H

end LeanCanny.Encoding.IntegralMixedMarkedLeafPowers
