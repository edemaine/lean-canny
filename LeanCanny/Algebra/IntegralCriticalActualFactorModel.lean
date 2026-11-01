/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalActualLowMatrixModel
/-! # Actual monomial factor and factor-power entry models -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalActualFactorModel
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalTotalCompanionBits IntegralCriticalActualMonomialSnapshot IntegralCriticalActualLowMatrixModel
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily
attribute [local irreducible] IntegralCriticalHistoryTask.get IntegralCriticalHistoryTask.numericCap

noncomputable def factorMatrix (S : IntegralMonomialTermBits.Source) (q : List Bool) (s : ℕ) :
    Matrix (Fin (S.rank q)) (Fin (S.rank q)) (ZMod (S.modulus q)) := by
  let := S.ring q
  exact (Algebra.leftMulMatrix (S.basis q) (IntegralMonomialTermBits.factor S q s)).map
    (Int.castRingHom (ZMod (S.modulus q)))
noncomputable def factorPowerMatrix (S : IntegralMonomialTermBits.Source) (q : List Bool) (s : ℕ) :
    Matrix (Fin (S.rank q)) (Fin (S.rank q)) (ZMod (S.modulus q)) := by
  let := S.ring q
  exact (Algebra.leftMulMatrix (S.basis q)
    (IntegralMonomialTermBits.factor S q s ^ IntegralMonomialTermBits.factorExponent S q s)).map
    (Int.castRingHom (ZMod (S.modulus q)))
noncomputable def rank (F : Scripts) (q : List Bool) := (IntegralCriticalFlatActualLow.source F).rank q
noncomputable def rankAt (A : IntegralHistoryCriticalBits.Family) := (IntegralCriticalActualScalarModels.eulerAt A).rank []
noncomputable def factorAt (A : IntegralHistoryCriticalBits.Family) (x j k m : ℕ) (hm : m ≠ 0) (s r t : ℕ) :=
  entryBits (factorMatrix (monomialAt A x j k 0 0 m hm) [] s) r t
noncomputable def powerAt (A : IntegralHistoryCriticalBits.Family) (x j k m : ℕ) (hm : m ≠ 0) (s r t : ℕ) :=
  entryBits (factorPowerMatrix (monomialAt A x j k 0 0 m hm) [] s) r t
noncomputable def factorEntry (F : Scripts) (q : List Bool) (s r t : ℕ) :=
  entryBits (factorMatrix (IntegralCriticalFlatActualLow.source F) q s) r t
noncomputable def powerEntry (F : Scripts) (q : List Bool) (s r t : ℕ) :=
  entryBits (factorPowerMatrix (IntegralCriticalFlatActualLow.source F) q s) r t
noncomputable def monomial (F : Scripts) (q : List Bool) :=
  factorEntry F q (IntegralCriticalHistoryTask.get F.toParameters .slot8 q)
    (IntegralCriticalHistoryTask.get F.toParameters .row q % rank F q)
    (IntegralCriticalHistoryTask.get F.toParameters .col q % rank F q)
noncomputable def power (F : Scripts) (q : List Bool) :=
  powerEntry F q (IntegralCriticalHistoryTask.get F.toParameters .slot8 q)
    (IntegralCriticalHistoryTask.get F.toParameters .row q % rank F q)
    (IntegralCriticalHistoryTask.get F.toParameters .col q % rank F q)

theorem rank_snapshot (F : Scripts) (q : List Bool) : rank F q = rankAt (IntegralCriticalTotalCreatingBits.atFamily F q) := by
  change ((IntegralCriticalFlatActualLow.source F).snapshot q).rank [] = _
  rw [source_snapshot]
  rfl

theorem rank_invariance (F : Scripts) (child q : List Bool) (hr : root child = root q)
    (hb : IntegralCriticalHistoryTask.birth F.toParameters child = IntegralCriticalHistoryTask.birth F.toParameters q) :
    rank F child = rank F q := by
  rw [rank_snapshot, rank_snapshot]
  exact congrArg rankAt (IntegralCriticalTotalCreatingBits.atFamily_invariance F child q hr hb)

theorem rank_cap (F : Scripts) (q : List Bool) :
    rank F q ≤ IntegralCriticalHistoryTask.numericCap F.toParameters (RankedHistoryTask.root q) := by
  change (IntegralCriticalTotalCreatingBits.euler F).rank (pairFst (IntegralCriticalFlatGridBits.termInput F.toParameters q)) ≤ _
  rw [IntegralCriticalFlatGridBits.termInput_parent]
  exact IntegralCriticalActualFrozenTransport.rank_cap F q

theorem factor_snapshot (F : Scripts) (q : List Bool) (s r t : ℕ) :
    factorEntry F q s r t = factorAt (IntegralCriticalTotalCreatingBits.atFamily F q)
      (IntegralCriticalHistoryTask.get F.toParameters .expression q) (IntegralCriticalHistoryTask.get F.toParameters .derivative q)
      (IntegralCriticalHistoryTask.get F.toParameters .sourceIndex q)
      (IntegralCriticalHistoryTask.modulus F.toParameters q) (IntegralCriticalHistoryTask.modulus_ne_zero F.toParameters q) s r t := by
  change entryBits (factorMatrix ((IntegralCriticalFlatActualLow.source F).snapshot q) [] s) r t = _
  rw [source_snapshot]
  rfl

theorem power_snapshot (F : Scripts) (q : List Bool) (s r t : ℕ) :
    powerEntry F q s r t = powerAt (IntegralCriticalTotalCreatingBits.atFamily F q)
      (IntegralCriticalHistoryTask.get F.toParameters .expression q) (IntegralCriticalHistoryTask.get F.toParameters .derivative q)
      (IntegralCriticalHistoryTask.get F.toParameters .sourceIndex q)
      (IntegralCriticalHistoryTask.modulus F.toParameters q) (IntegralCriticalHistoryTask.modulus_ne_zero F.toParameters q) s r t := by
  change entryBits (factorPowerMatrix ((IntegralCriticalFlatActualLow.source F).snapshot q) [] s) r t = _
  rw [source_snapshot]
  rfl

theorem factorAt_congr (A B : IntegralHistoryCriticalBits.Family) (x j k m x' j' k' m' s r t : ℕ)
    (hm : m ≠ 0) (hm' : m' ≠ 0) (hA : A = B) (hx : x = x') (hj : j = j') (hk : k = k') (hmod : m = m') :
    factorAt A x j k m hm s r t = factorAt B x' j' k' m' hm' s r t := by
  subst B; subst x'; subst j'; subst k'; subst m'
  rfl

theorem powerAt_congr (A B : IntegralHistoryCriticalBits.Family) (x j k m x' j' k' m' s r t : ℕ)
    (hm : m ≠ 0) (hm' : m' ≠ 0) (hA : A = B) (hx : x = x') (hj : j = j') (hk : k = k') (hmod : m = m') :
    powerAt A x j k m hm s r t = powerAt B x' j' k' m' hm' s r t := by
  subst B; subst x'; subst j'; subst k'; subst m'
  rfl

end LeanCanny.Algebra.IntegralCriticalActualFactorModel
