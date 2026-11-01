/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalFactorModel
public import LeanCanny.Algebra.IntegralMixedPhysicalDerivativeTransport
/-! # Finite actual coefficient leaves of physical monomial factors -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalMonomialLeafBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedPhysicalMonomialBits IntegralMixedPhysicalFactorBits
open IntegralCriticalActualLowMatrixModel
open IntegralCriticalActualFactorModel (factorMatrix)
set_option backward.isDefEq.respectTransparency false

theorem coefficient_leaf (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedPhysicalQueryBits.InputMetadata F)
    (q : List Bool) (r t : Fin ((source P F).rank q)) :
    (access P a F h).coefficient (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val))) =
      factorEntry P F q 0 r.val t.val := by
  rw [(access P a F h).coefficient_eq q r t]
  exact (entryBits_fin (factorMatrix (source P F) q 0) r t).symm

theorem factorAt_original (F : Family) (key : List Bool) (x j k m r t : ℕ) (hm : m ≠ 0) (hx : x ≠ 1)
    (hr : r < rankAt F key) (ht : t < rankAt F key) :
    factorAt F key x j k m hm 0 r t = IntegralMixedPhysicalCoefficientBits.originalAt F key k r t m hm := by
  let E := (IntegralMixedPhysicalSnapshotBits.sourceAt F key 0 0 0 0 0 m hm).toEuler
  let := E.ring []
  have HR0 : r < (monomialAt F key x j k 0 0 m hm).rank [] := hr
  have HT0 : t < (monomialAt F key x j k 0 0 m hm).rank [] := ht
  refine (entryBits_fin (factorMatrix (monomialAt F key x j k 0 0 m hm) [] 0) ⟨r, HR0⟩ ⟨t, HT0⟩).trans ?_
  unfold factorMatrix monomialAt IntegralMonomialTermBits.factor IntegralMixedPhysicalCoefficientBits.originalAt
  dsimp only
  simp only [ite_true, ite_eq_right hx]
  have HR : (⟨r % E.rank [], Nat.mod_lt _ (by change 0 < rankAt F key; unfold rankAt; exact pow_pos (Nat.two_pow_pos _) _)⟩ : Fin (E.rank [])) = ⟨r, hr⟩ :=
    Fin.ext (Nat.mod_eq_of_lt hr)
  have HT : (⟨t % E.rank [], Nat.mod_lt _ (by change 0 < rankAt F key; unfold rankAt; exact pow_pos (Nat.two_pow_pos _) _)⟩ : Fin (E.rank [])) = ⟨t, ht⟩ :=
    Fin.ext (Nat.mod_eq_of_lt ht)
  change _ = residueBits ((Algebra.leftMulMatrix (E.basis [])
    ((E.polynomial []).coeff (RationalSubstitution.Indexed.exponentVector (E.arity [])
      (FixedWidthPolynomial.entry (E.sourceWidth []) k)))
      ⟨r % E.rank [], _⟩ ⟨t % E.rank [], _⟩ : ℤ) : ZMod m)
  rw [HR, HT]
  rfl

theorem factorAt_derivative (F : Family) (key : List Bool) (j k m r t : ℕ) (hm : m ≠ 0)
    (hr : r < rankAt F key) (ht : t < rankAt F key) :
    factorAt F key 1 j k m hm 0 r t = IntegralMixedPhysicalCoefficientBits.derivativeAt F key j k r t m hm := by
  let E := (IntegralMixedPhysicalSnapshotBits.sourceAt F key 0 0 0 0 0 m hm).toEuler
  let := E.ring []
  have HR0 : r < (monomialAt F key 1 j k 0 0 m hm).rank [] := hr
  have HT0 : t < (monomialAt F key 1 j k 0 0 m hm).rank [] := ht
  refine (entryBits_fin (factorMatrix (monomialAt F key 1 j k 0 0 m hm) [] 0) ⟨r, HR0⟩ ⟨t, HT0⟩).trans ?_
  unfold factorMatrix monomialAt IntegralMonomialTermBits.factor IntegralMixedPhysicalCoefficientBits.derivativeAt
  dsimp only
  simp only [ite_true]
  have HR : (⟨r % E.rank [], Nat.mod_lt _ (by change 0 < rankAt F key; unfold rankAt; exact pow_pos (Nat.two_pow_pos _) _)⟩ : Fin (E.rank [])) = ⟨r, hr⟩ :=
    Fin.ext (Nat.mod_eq_of_lt hr)
  have HT : (⟨t % E.rank [], Nat.mod_lt _ (by change 0 < rankAt F key; unfold rankAt; exact pow_pos (Nat.two_pow_pos _) _)⟩ : Fin (E.rank [])) = ⟨t, ht⟩ :=
    Fin.ext (Nat.mod_eq_of_lt ht)
  change _ = residueBits ((Algebra.leftMulMatrix (E.basis [])
    ((MvPolynomial.pderiv (IntegralCriticalGradientBits.freeIndex E.toGradient []
      ⟨j % E.free [], Nat.mod_lt _ (E.free_pos [])⟩) (E.polynomial [])).coeff
      (RationalSubstitution.Indexed.exponentVector (E.arity []) (FixedWidthPolynomial.entry (E.sourceWidth []) k)))
      ⟨r % E.rank [], _⟩ ⟨t % E.rank [], _⟩ : ℤ) : ZMod m)
  rw [HR, HT]
  rfl

theorem factorAt_cases (F : Family) (key : List Bool) (x j k m r t : ℕ) (hm : m ≠ 0)
    (hr : r < rankAt F key) (ht : t < rankAt F key) :
    factorAt F key x j k m hm 0 r t = if x = 1 then
      IntegralMixedPhysicalCoefficientBits.derivativeAt F key j k r t m hm else IntegralMixedPhysicalCoefficientBits.originalAt F key k r t m hm := by
  by_cases hx : x = 1
  · subst x
    rw [ite_eq_left rfl]
    exact factorAt_derivative F key j k m r t hm hr ht
  · rw [ite_eq_right hx]
    exact factorAt_original F key x j k m r t hm hx hr ht

end LeanCanny.Algebra.IntegralMixedPhysicalMonomialLeafBits
