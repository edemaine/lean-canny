/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedTerminalCutSource
public import LeanCanny.Algebra.IntegralMixedCutCoefficientPolynomialKey
/-! # Full terminal cut probes specialize through one selected parent

Every finite coefficient/choice query preserves the literal parent key.
The terminal suffix supplies one common generator interpretation for all
queries; no coefficient-dependent choice of old roots is allowed.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedTerminalCutTest
open LeanCanny.Algebra IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

private theorem query_eq (P : Parameters) (c d : List Bool) :
    IntegralFramedCutCoefficientTest.query P (pair c d)=IntegralMixedCutCoefficientQueryBits.query P (pair c d) := by
  simp only [IntegralFramedCutCoefficientTest.query,pairFst_pair,pairSnd_pair]

private theorem query_saved (P : Parameters) (c d : List Bool) :
    IntegralMixedVirtualTaskBits.saved P (IntegralFramedCutCoefficientTest.query P (pair c d))=
      IntegralMixedVirtualTaskBits.saved P c := by
  rw [query_eq]
  exact (IntegralMixedCutCoefficientQueryBits.query_saved P (pair c d)).trans
    (congrArg (IntegralMixedVirtualTaskBits.saved P) (pairFst_pair c d))

private theorem polynomial_query_congr (P : Parameters) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (u v : List Bool) (hu : u=v) :
    HEq (IntegralMixedFramedChoiceProbeSourceBits.polynomial P D H u)
      (IntegralMixedFramedChoiceProbeSourceBits.polynomial P D H v) := by
  cases hu
  rfl

private theorem evaluation_heq {a b : ℕ} (p : MvPolynomial (Fin a) ℤ) (q : MvPolynomial (Fin b) ℤ)
    (hd : a=b) (hp : HEq p q) (z : ℕ→ℝ) :
    p.eval₂ (Int.castRingHom ℝ) (fun i=>z i.val)=q.eval₂ (Int.castRingHom ℝ) (fun i=>z i.val) := by
  cases hd
  have HE:=eq_of_heq hp
  cases HE
  rfl

theorem oldArity_parent (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c d : List Bool) : oldArity P D H c d=(family P D H).birth (IntegralMixedVirtualTaskBits.saved P c) := by
  change (family P D H).birth (IntegralMixedVirtualTaskBits.saved P (IntegralFramedCutCoefficientTest.query P (pair c d)))=_
  exact congrArg (family P D H).birth (query_saved P c d)

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (key : List Bool→List Bool) (c : List Bool) (e k : ℕ)
local notation "G" => family P D H
local notation "parent" => IntegralMixedVirtualTaskBits.saved P c
local notation "old" => IntegralMixedCutSource.Family.state G parent
local notation "rule" => IntegralMixedCutSource.Family.rule G parent
local notation "kind" => IntegralMixedCutSource.Family.kind G parent
local notation "bound" => IntegralMixedCutSource.Family.birth_bound G parent
local notation "indices" => pair (BinaryNatCode.encode e) (BinaryNatCode.encode k)
local notation "delta" => count P D H key c-arity P D H key c indices

theorem polynomial_evaluation (ha : IntegralMixedFramedFullCutProbeBits.Active P c)
    (he : e≤2^P.width (RankedHistoryTask.root c)) (hk : k≤2^P.width (RankedHistoryTask.root c))
    (hfit : oldArity P D H c indices≤count P D H key c)
    (z : ℕ→ℝ) (φ : (old).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀ i,φ ((old).sampler.scalarPrefix.basis.generator i)=z (i.val+delta)^
      UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P c)
        (2^(G).width parent) ((G).birth parent) i) :
    (polynomial P D H key c indices).eval₂ (Int.castRingHom ℝ) (fun i=>z (i.val+delta))=
      φ ((IntegralMixedRelativeCuts.factor old bound rule (IntegralMixedRelativeCuts.atChoice rule kind k)).coeff e) := by
  have HP:=(polynomial_query_congr P D H _ _ (query_eq P c indices)).trans
    (IntegralMixedCutCoefficientPolynomialKey.packet P D H c e k ha he hk)
  have HD:=oldArity_parent P D H c indices
  have HE:=evaluation_heq _ _ HD HP (fun i=>z (i+delta))
  unfold polynomial
  rw [dite_eq_left hfit]
  refine (MvPolynomial.eval₂_rename (Int.castRingHom ℝ) (Fin.cast (Nat.min_eq_left hfit).symm)
    (fun i : Fin (arity P D H key c indices)=>z (i.val+delta))
    (IntegralMixedFramedChoiceProbeSourceBits.polynomial P D H (IntegralFramedCutCoefficientTest.query P (pair c indices)))).trans ?_
  change (IntegralMixedFramedChoiceProbeSourceBits.polynomial P D H
    (IntegralFramedCutCoefficientTest.query P (pair c indices))).eval₂ (Int.castRingHom ℝ) (fun i=>z (i.val+delta))=_
  exact HE.trans (IntegralMixedCutCoefficientPolynomialKey.evaluation (family P D H)
    (IntegralMixedFramedChoiceProbeSourceBits.horizon P c) parent e k φ (fun i=>z (i.val+delta)) hφ)

end LeanCanny.Encoding.IntegralFramedTerminalCutTest
