/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalMonomialSnapshot
public import LeanCanny.Algebra.IntegralMixedPhysicalCaps
public import LeanCanny.Algebra.IntegralCriticalActualNaturalPower
/-! # Actual physical monomial factors and factor powers with natural selectors -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalFactorBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedPhysicalMonomialBits IntegralCriticalActualLowMatrixModel
open IntegralCriticalActualFactorModel (factorMatrix factorPowerMatrix)
set_option backward.isDefEq.respectTransparency false

noncomputable def rank (P : Parameters) (F : Family) (q : List Bool) := (source P F).rank q
noncomputable def rankAt (F : Family) (key : List Bool) := FixedWidthPolynomial.count (F.birth key) (F.width key)
noncomputable def factorAt (F : Family) (key : List Bool) (x j k m : ℕ) (hm : m ≠ 0) (s r t : ℕ) :=
  entryBits (factorMatrix (monomialAt F key x j k 0 0 m hm) [] s) r t
noncomputable def powerAt (F : Family) (key : List Bool) (x j k m : ℕ) (hm : m ≠ 0) (s r t : ℕ) :=
  entryBits (factorPowerMatrix (monomialAt F key x j k 0 0 m hm) [] s) r t
noncomputable def factorEntry (P : Parameters) (F : Family) (q : List Bool) (s r t : ℕ) :=
  entryBits (factorMatrix (source P F) q s) r t
noncomputable def powerEntry (P : Parameters) (F : Family) (q : List Bool) (s r t : ℕ) :=
  entryBits (factorPowerMatrix (source P F) q s) r t
noncomputable def monomial (P : Parameters) (F : Family) (q : List Bool) :=
  factorEntry P F q (get P .slot8 q) (get P .row q % rank P F q) (get P .col q % rank P F q)
noncomputable def power (P : Parameters) (F : Family) (q : List Bool) :=
  powerEntry P F q (get P .slot8 q) (get P .row q % rank P F q) (get P .col q % rank P F q)

theorem rank_snapshot (P : Parameters) (F : Family) (q : List Bool) : rank P F q = rankAt F (IntegralMixedPhysicalTaskBits.saved P q) := by
  change ((source P F).snapshot q).rank [] = _
  rw [source_snapshot]
  rfl

theorem rank_invariance (P : Parameters) (F : Family) (q c : List Bool)
    (hr : RankedHistoryTask.root c = RankedHistoryTask.root q) (hb : birth P c = birth P q)
    (hx : get P .slot15 c = get P .slot15 q) : rank P F c = rank P F q := by
  rw [rank_snapshot, rank_snapshot, IntegralMixedPhysicalTaskBits.saved_invariance P q c hr hb hx]

theorem rank_cap (P : Parameters) (F : Family) (g : IntegralMixedPhysicalCaps.RootGeometry P F)
    (q : List Bool) : rank P F q ≤ numericCap P (RankedHistoryTask.root q) := by
  change (IntegralMixedPhysicalTaskBits.arithmetic P F).rank (pairFst (IntegralCriticalFlatGridBits.termInput P q)) ≤ _
  rw [IntegralCriticalFlatGridBits.termInput_parent]
  exact IntegralMixedPhysicalCaps.rank_cap P F g q

theorem factor_snapshot (P : Parameters) (F : Family) (q : List Bool) (s r t : ℕ) :
    factorEntry P F q s r t = factorAt F (IntegralMixedPhysicalTaskBits.saved P q)
      (get P .expression q) (get P .derivative q) (get P .sourceIndex q) (modulus P q) (modulus_ne_zero P q) s r t := by
  change entryBits (factorMatrix ((source P F).snapshot q) [] s) r t = _
  rw [source_snapshot]
  simp only [snapshot, factorAt]
  unfold factorMatrix monomialAt
  rfl

theorem power_snapshot (P : Parameters) (F : Family) (q : List Bool) (s r t : ℕ) :
    powerEntry P F q s r t = powerAt F (IntegralMixedPhysicalTaskBits.saved P q)
      (get P .expression q) (get P .derivative q) (get P .sourceIndex q) (modulus P q) (modulus_ne_zero P q) s r t := by
  change entryBits (factorPowerMatrix ((source P F).snapshot q) [] s) r t = _
  rw [source_snapshot]
  simp only [snapshot, powerAt]
  unfold factorPowerMatrix monomialAt
  rfl

theorem factorAt_congr (F : Family) (key key' : List Bool) (x j k m x' j' k' m' s r t : ℕ)
    (hm : m ≠ 0) (hm' : m' ≠ 0) (hkey : key = key') (hx : x = x') (hj : j = j') (hk : k = k') (hmod : m = m') :
    factorAt F key x j k m hm s r t = factorAt F key' x' j' k' m' hm' s r t := by
  subst key'; subst x'; subst j'; subst k'; subst m'
  rfl

theorem powerAt_congr (F : Family) (key key' : List Bool) (x j k m x' j' k' m' s r t : ℕ)
    (hm : m ≠ 0) (hm' : m' ≠ 0) (hkey : key = key') (hx : x = x') (hj : j = j') (hk : k = k') (hmod : m = m') :
    powerAt F key x j k m hm s r t = powerAt F key' x' j' k' m' hm' s r t := by
  subst key'; subst x'; subst j'; subst k'; subst m'
  rfl
end LeanCanny.Algebra.IntegralMixedPhysicalFactorBits
