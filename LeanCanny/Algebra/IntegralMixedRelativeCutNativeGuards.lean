/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedRelativeCutChoice
public import LeanCanny.Computation.FiniteCoefficientSignScan
public import LeanCanny.Encoding.SquareSampleTestSign
/-! # Native finite coefficient scans have the exact relative-cut meaning -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedRelativeCuts
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory IntegralMixedCriticalSweep
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem native_guards_iff (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (c : Kind P r) (d E : ℕ)
    (hE : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤E)
    (hK : choiceIndex r c≤E) (hD : d≤E)
    (sign head : List Bool→List Bool) (choice degree cap : List Bool→ℕ) (q : List Bool)
    (hk : choice q=choiceIndex r c) (hd : degree q=d) (he : cap q=E)
    (HE : ∀e k,e≤E→k≤E→sign (FiniteCoefficientSignScan.query q e k)=
      InfinitesimalSign.encode (SignType.sign (φ ((factor x hm r (atChoice r c k)).coeff e)))) :
    FiniteCoefficientSignScan.Guards sign head choice degree cap q ↔
      CoefficientGuards x hm r φ c d ∧
        (head q≠InfinitesimalSign.encode 0 ∨ φ ((factor x hm r c).coeff 0)=0) := by
  have HZ (e k : ℕ) (he : e≤E) (hk : k≤E) :
      FiniteCoefficientSignScan.Zero sign q e k ↔ φ ((factor x hm r (atChoice r c k)).coeff e)=0 := by
    unfold FiniteCoefficientSignScan.Zero
    rw [HE e k he hk]
    exact (SquareSampleTestSign.encode_eq_iff _ _).trans sign_eq_zero_iff
  have ZA (a : Kind P r) (e : ℕ)
      (he : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree<e) : φ ((factor x hm r a).coeff e)=0 := by
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt ((factor_degree x hm r a).trans_lt he),map_zero]
  simp only [FiniteCoefficientSignScan.Guards,hk,hd,he]
  constructor
  · rintro ⟨HL,HD,HH,HHead⟩
    refine ⟨⟨?_,?_,?_⟩,?_⟩
    · intro k hkl e hel
      have H := (HZ e k (hel.trans hE) (hkl.le.trans hK)).mp (HL k hkl e (by omega))
      rw [atChoice_lower r c k hkl] at H
      exact H
    · intro hzero
      apply HD
      apply (HZ d (choiceIndex r c) hD hK).mpr
      rw [atChoice_self]
      exact hzero
    · intro e hed hel
      have H := (HZ e (choiceIndex r c) (hel.trans hE) hK).mp (HH e (by omega) hed)
      rw [atChoice_self] at H
      exact H
    · rcases HHead with H|H
      · exact Or.inl H
      · exact Or.inr (by simpa only [atChoice_self] using (HZ 0 (choiceIndex r c) (Nat.zero_le _) hK).mp H)
  · rintro ⟨HC,HHead⟩
    refine ⟨?_,?_,?_,?_⟩
    · intro k hkl e hel
      apply (HZ e k (by omega) (hkl.le.trans hK)).mpr
      rw [atChoice_lower r c k hkl]
      by_cases haux : e≤IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree
      · exact HC.1 k hkl e haux
      · exact ZA _ e (by omega)
    · intro H
      apply HC.2.1
      have HV := (HZ d (choiceIndex r c) hD hK).mp H
      rw [atChoice_self] at HV
      exact HV
    · intro e hel hed
      apply (HZ e (choiceIndex r c) (by omega) hK).mpr
      rw [atChoice_self]
      by_cases haux : e≤IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree
      · exact HC.2.2 e hed haux
      · exact ZA _ e (by omega)
    · rcases HHead with H|H
      · exact Or.inl H
      · right
        apply (HZ 0 (choiceIndex r c) (Nat.zero_le _) hK).mpr
        rw [atChoice_self]
        exact H

end LeanCanny.Algebra.IntegralMixedRelativeCuts
