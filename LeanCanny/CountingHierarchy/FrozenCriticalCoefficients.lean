/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.FrozenPolynomialEvaluation
public import LeanCanny.CountingHierarchy.RelativeCriticalSpecialization
public import LeanCanny.CountingHierarchy.ZeroCenterCoefficientCorrectness
public import LeanCanny.CountingHierarchy.SourceCriticalEvaluation

/-! # Relative characteristic coefficients from the original source evaluator -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial PurePowerResidue

namespace Controlled

variable {α : Type} {n m : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
  {P : (w : α) → MvPolynomial (Fin (n w + m w)) ℤ}

noncomputable def frozenCoefficient (C : Controlled P enc a) (p d u k : α → ℕ)
    (params : α → List ℕ) (w : α) : ℕ :=
  zeroCoefficientValue (p w) (n w) (d w) (u w) (k w)
    (fun y => C.frozenEvaluate p params (w, y))

theorem frozenCoefficient_mem (C : Controlled P enc a) (E : Decoder enc)
    (hn : ComputableInPolyTime n enc encUnary) (hm : ComputableInPolyTime m enc encUnary)
    {p d u k : α → ℕ} {params : α → List ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hd : ComputableInPolyTime d enc encNat)
    (hu : ComputableInPolyTime u enc encNat) (hk : ComputableInPolyTime k enc encNat)
    (hparams : ComputableInPolyTime params enc (encList encNat)) :
    C.frozenCoefficient p d u k params ∈ CountingFunction (a + 9) enc encNat :=
  zeroCoefficientValue_mem E hp hn hd hu hk (C.frozenEvaluate_mem hn hm hp hparams)

theorem frozenCoefficient_cast (C : Controlled P enc a) (p d u k : α → ℕ)
    (params : α → List ℕ) (w : α) (hp : (p w).Prime) (hcut : C.cutoff w < p w)
    (hd : 1 ≤ d w) (hdeg : (P w).totalDegree ≤ d w + 1)
    (hlarge : criticalCoefficientPrimeCutoff (n w) (d w) < p w) :
    (C.frozenCoefficient p d u k params w : ZMod (p w)) =
      relativeParameterEvaluation (u w : ZMod (p w))
        (fun i : Fin (m w) => ((params w)[i.val]?.getD 0 : ZMod (p w)))
        ((relativeCharacteristic (d w) (MvPolynomial.rename finSumFinEquiv.symm (P w))
          ((MvPolynomial.totalDegree_rename_le _ _).trans hdeg)).coeff (k w)) := by
  let : Fact (p w).Prime := ⟨hp⟩
  let F := MvPolynomial.rename finSumFinEquiv.symm (P w)
  let x : Fin (m w) → ZMod (p w) := fun i => ((params w)[i.val]?.getD 0 : ZMod (p w))
  have hF : F.totalDegree ≤ d w + 1 := (MvPolynomial.totalDegree_rename_le _ _).trans hdeg
  have hsource : specializeFinitePolynomial (P w) (Int.castRingHom (ZMod (p w))) x =
      relativeSpecializedSource F x := rfl
  have hsmall : (relativeSpecializedSource F x).totalDegree < p w - 1 := by
    have := (relativeSpecializedSource_degree F x).trans hF
    unfold criticalCoefficientPrimeCutoff at hlarge
    omega
  have hthree : 3 < p w := by unfold criticalCoefficientPrimeCutoff at hlarge; omega
  have hgrid : (d w + 1) * ((d w + 1) ^ n w * (d w + 2) + n w * d w + 1) + 1 < p w := by
    unfold criticalCoefficientPrimeCutoff criticalTraceDegreeBound at hlarge
    omega
  have hdim : (d w + 1) ^ n w < p w - 1 := by
    unfold criticalCoefficientPrimeCutoff at hlarge
    omega
  have hdim₂ : (d w + 1) ^ n w * (d w + 1) ^ n w < p w - 1 := by
    unfold criticalCoefficientPrimeCutoff at hlarge
    omega
  have hcoeff := zeroCoefficientValue_eq (d w) hd (relativeSpecializedSource F x)
    ((relativeSpecializedSource_degree F x).trans hF) (u w) (k w) hsmall hthree hgrid hdim hdim₂
    (fun y => C.frozenEvaluate p params (w, y))
    (fun y => hsource ▸ C.frozenEvaluate_cast p params w hp hcut y)
  have hK : ∀ j : ℕ, 1 ≤ j → j ≤ (d w + 1) ^ n w → (j : ZMod (p w)) ≠ 0 := by
    intro j hj hle
    exact (ZMod.natCast_eq_zero_iff j (p w)).not.mpr (by
      intro hdiv
      have := Nat.le_of_dvd (by omega : 0 < j) hdiv
      omega)
  have hmap := congrArg (fun Q : Polynomial (ZMod (p w)) => Q.coeff (k w))
    (relativeCharacteristic_map (d w) hd F hF (u w : ZMod (p w)) x hK)
  rw [Polynomial.coeff_map] at hmap
  rw [frozenCoefficient, hcoeff, ZMod.natCast_zmod_val]
  exact hmap.symm

end Controlled
end LeanCanny.CountingHierarchy
