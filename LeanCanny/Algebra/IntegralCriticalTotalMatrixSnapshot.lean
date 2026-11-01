/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalTotalCreatingSnapshot
/-! # Actual integer matrix entries retained across flat output retargeting

A scalar entry wrapper separates matrix data from the caller's natural
row and column indices. Same-root, same-birth transport follows from the
actual creating family, with no source-equality premise.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalTotalSnapshotBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalTotalCompanionBits
set_option backward.isDefEq.respectTransparency false

noncomputable def integerEntry {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (r t : ℕ) : ℤ :=
  if hr : r < n then if ht : t < n then M ⟨r, hr⟩ ⟨t, ht⟩ else 0 else 0

theorem integerEntry_fin {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (r t : Fin n) : integerEntry M r.val t.val = M r t := by
  unfold integerEntry
  rw [dite_eq_left r.isLt, dite_eq_left t.isLt]

noncomputable def blockMatrix (S : IntegralBerkowitzBlockBits.Source) (q : List Bool) :
    Matrix (Fin (S.dimension q * S.rank q)) (Fin (S.dimension q * S.rank q)) ℤ := by
  let := S.ring q
  exact IntegralCoefficientBlocks.blockHom (S.basis q) (S.dimension q) (S.matrix q)

noncomputable def canonicalReductionEntry (A : IntegralHistoryCriticalBits.Family) (r t : ℕ) : ℤ :=
  integerEntry (blockMatrix (IntegralCriticalQuerySnapshotBits.canonicalReduction A).toSource []) r t
noncomputable def canonicalActionEntry (A : IntegralHistoryCriticalBits.Family) (r t : ℕ) : ℤ :=
  integerEntry (blockMatrix (IntegralCriticalQuerySnapshotBits.canonicalAction A) []) r t
noncomputable def canonicalPowerEntry (A : IntegralHistoryCriticalBits.Family) (r t : ℕ) : ℤ :=
  integerEntry ((IntegralCriticalQuerySnapshotBits.canonicalAction A).powerMatrix []) r t

noncomputable def reductionEntry (F : Scripts) (q : List Bool) (r t : ℕ) : ℤ :=
  integerEntry (blockMatrix (IntegralCriticalFlatActualSources.reduction F).toSource q) r t
noncomputable def actionEntry (F : Scripts) (q : List Bool) (r t : ℕ) : ℤ :=
  integerEntry (blockMatrix (IntegralCriticalFlatActualSources.characteristic F) q) r t
noncomputable def powerEntry (F : Scripts) (q : List Bool) (r t : ℕ) : ℤ :=
  integerEntry ((IntegralCriticalFlatActualSources.characteristic F).powerMatrix q) r t

attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily

theorem reductionEntry_snapshot (F : Scripts) (q : List Bool) (r t : ℕ) :
    reductionEntry F q r t = canonicalReductionEntry (IntegralCriticalTotalCreatingBits.atFamily F q) r t := rfl

theorem actionEntry_snapshot (F : Scripts) (q : List Bool) (r t : ℕ) :
    actionEntry F q r t = canonicalActionEntry (IntegralCriticalTotalCreatingBits.atFamily F q) r t := rfl

theorem powerEntry_snapshot (F : Scripts) (q : List Bool) (r t : ℕ) :
    powerEntry F q r t = canonicalPowerEntry (IntegralCriticalTotalCreatingBits.atFamily F q) r t := rfl

theorem reductionEntry_invariance (F : Scripts) (q c : List Bool)
    (hr : root q = root c)
    (hb : IntegralCriticalHistoryTask.birth F.toParameters q = IntegralCriticalHistoryTask.birth F.toParameters c) (r t : ℕ) :
    reductionEntry F q r t = reductionEntry F c r t := by
  rw [reductionEntry_snapshot, reductionEntry_snapshot]
  exact congrArg (fun A => canonicalReductionEntry A r t) (IntegralCriticalTotalCreatingBits.atFamily_invariance F q c hr hb)

theorem actionEntry_invariance (F : Scripts) (q c : List Bool)
    (hr : root q = root c)
    (hb : IntegralCriticalHistoryTask.birth F.toParameters q = IntegralCriticalHistoryTask.birth F.toParameters c) (r t : ℕ) :
    actionEntry F q r t = actionEntry F c r t := by
  rw [actionEntry_snapshot, actionEntry_snapshot]
  exact congrArg (fun A => canonicalActionEntry A r t) (IntegralCriticalTotalCreatingBits.atFamily_invariance F q c hr hb)

theorem powerEntry_invariance (F : Scripts) (q c : List Bool)
    (hr : root q = root c)
    (hb : IntegralCriticalHistoryTask.birth F.toParameters q = IntegralCriticalHistoryTask.birth F.toParameters c) (r t : ℕ) :
    powerEntry F q r t = powerEntry F c r t := by
  rw [powerEntry_snapshot, powerEntry_snapshot]
  exact congrArg (fun A => canonicalPowerEntry A r t) (IntegralCriticalTotalCreatingBits.atFamily_invariance F q c hr hb)

theorem rank_invariance (F : Scripts) (q c : List Bool)
    (hr : root q = root c)
    (hb : IntegralCriticalHistoryTask.birth F.toParameters q = IntegralCriticalHistoryTask.birth F.toParameters c) :
    (IntegralCriticalFlatActualSources.characteristic F).rank q = (IntegralCriticalFlatActualSources.characteristic F).rank c := by
  change FixedWidthPolynomial.count ((IntegralCriticalTotalCreatingBits.atFamily F q).birth []) ((IntegralCriticalTotalCreatingBits.atFamily F q).width []) = _
  exact congrArg (fun A : IntegralHistoryCriticalBits.Family => FixedWidthPolynomial.count (A.birth []) (A.width []))
    (IntegralCriticalTotalCreatingBits.atFamily_invariance F q c hr hb)

theorem dimension_invariance (F : Scripts) (q c : List Bool)
    (hr : root q = root c)
    (hb : IntegralCriticalHistoryTask.birth F.toParameters q = IntegralCriticalHistoryTask.birth F.toParameters c) :
    (IntegralCriticalFlatActualSources.characteristic F).dimension q = (IntegralCriticalFlatActualSources.characteristic F).dimension c := by
  change (IntegralCriticalQuerySnapshotBits.canonicalAction (IntegralCriticalTotalCreatingBits.atFamily F q)).dimension [] = _
  exact congrArg (fun A => (IntegralCriticalQuerySnapshotBits.canonicalAction A).dimension [])
    (IntegralCriticalTotalCreatingBits.atFamily_invariance F q c hr hb)

theorem powerDimension_invariance (F : Scripts) (q c : List Bool)
    (hr : root q = root c)
    (hb : IntegralCriticalHistoryTask.birth F.toParameters q = IntegralCriticalHistoryTask.birth F.toParameters c) :
    IntegralBerkowitzBlockBits.powerDimension (IntegralCriticalFlatActualSources.characteristic F) q =
      IntegralBerkowitzBlockBits.powerDimension (IntegralCriticalFlatActualSources.characteristic F) c := by
  unfold IntegralBerkowitzBlockBits.powerDimension
  rw [dimension_invariance F q c hr hb, rank_invariance F q c hr hb]

noncomputable def modularPowerEntry (F : Scripts) (q : List Bool) (r t : ℕ) : List Bool :=
  residueBits (powerEntry F q r t : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q))

theorem modularPowerEntry_invariance (F : Scripts) (q c : List Bool)
    (hr : root q = root c)
    (hb : IntegralCriticalHistoryTask.birth F.toParameters q = IntegralCriticalHistoryTask.birth F.toParameters c)
    (hm : IntegralCriticalHistoryTask.modulus F.toParameters q = IntegralCriticalHistoryTask.modulus F.toParameters c) (r t : ℕ) :
    modularPowerEntry F q r t = modularPowerEntry F c r t :=
  congrArg₂ (fun (m : ℕ) (z : ℤ) => residueBits (z : ZMod m)) hm (powerEntry_invariance F q c hr hb r t)

theorem modularPowerEntry_fin (F : Scripts) (q : List Bool)
    (r t : Fin (IntegralBerkowitzBlockBits.powerDimension (IntegralCriticalFlatActualSources.characteristic F) q)) :
    modularPowerEntry F q r.val t.val =
      residueBits (((IntegralCriticalFlatActualSources.characteristic F).powerMatrix q r t : ℤ) :
        ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q)) :=
  congrArg (fun z : ℤ => residueBits (z : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q))) (integerEntry_fin _ r t)
theorem modularPowerEntry_retarget_fin (F : Scripts) (q c : List Bool)
    (hr : root q = root c)
    (hb : IntegralCriticalHistoryTask.birth F.toParameters q = IntegralCriticalHistoryTask.birth F.toParameters c)
    (hm : IntegralCriticalHistoryTask.modulus F.toParameters q = IntegralCriticalHistoryTask.modulus F.toParameters c)
    (r t : Fin (IntegralBerkowitzBlockBits.powerDimension (IntegralCriticalFlatActualSources.characteristic F) q)) :
    modularPowerEntry F c r.val t.val = residueBits (((IntegralCriticalFlatActualSources.characteristic F).powerMatrix q r t : ℤ) :
      ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q)) :=
  (modularPowerEntry_invariance F c q hr.symm hb.symm hm.symm r.val t.val).trans (modularPowerEntry_fin F q r t)

noncomputable def modularActionEntry (F : Scripts) (q : List Bool) (r t : ℕ) : List Bool :=
  residueBits (actionEntry F q r t : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q))
noncomputable def modularReductionEntry (F : Scripts) (q : List Bool) (r t : ℕ) : List Bool :=
  residueBits (reductionEntry F q r t : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q))

theorem modularActionEntry_invariance (F : Scripts) (q c : List Bool)
    (hr : root q = root c)
    (hb : IntegralCriticalHistoryTask.birth F.toParameters q = IntegralCriticalHistoryTask.birth F.toParameters c)
    (hm : IntegralCriticalHistoryTask.modulus F.toParameters q = IntegralCriticalHistoryTask.modulus F.toParameters c) (r t : ℕ) :
    modularActionEntry F q r t = modularActionEntry F c r t :=
  congrArg₂ (fun (m : ℕ) (z : ℤ) => residueBits (z : ZMod m)) hm (actionEntry_invariance F q c hr hb r t)

theorem modularReductionEntry_invariance (F : Scripts) (q c : List Bool)
    (hr : root q = root c)
    (hb : IntegralCriticalHistoryTask.birth F.toParameters q = IntegralCriticalHistoryTask.birth F.toParameters c)
    (hm : IntegralCriticalHistoryTask.modulus F.toParameters q = IntegralCriticalHistoryTask.modulus F.toParameters c) (r t : ℕ) :
    modularReductionEntry F q r t = modularReductionEntry F c r t :=
  congrArg₂ (fun (m : ℕ) (z : ℤ) => residueBits (z : ZMod m)) hm (reductionEntry_invariance F q c hr hb r t)

theorem canonical_basis_heq (A B : IntegralHistoryCriticalBits.Family) (h : A = B) :
    HEq ((IntegralHistoryCriticalBits.source A).basis []) ((IntegralHistoryCriticalBits.source B).basis []) := by cases h; rfl

theorem canonical_polynomial_heq (A B : IntegralHistoryCriticalBits.Family) (h : A = B) :
    HEq ((IntegralHistoryCriticalBits.source A).polynomial []) ((IntegralHistoryCriticalBits.source B).polynomial []) := by cases h; rfl

theorem canonical_lower_heq (A B : IntegralHistoryCriticalBits.Family) (h : A = B) :
    HEq ((IntegralHistoryCriticalBits.source A).toEuler.lowerPolynomial []) ((IntegralHistoryCriticalBits.source B).toEuler.lowerPolynomial []) := by cases h; rfl

theorem basis_invariance (F : Scripts) (q c : List Bool)
    (hr : root q = root c)
    (hb : IntegralCriticalHistoryTask.birth F.toParameters q = IntegralCriticalHistoryTask.birth F.toParameters c) :
    HEq ((IntegralCriticalTotalCreatingBits.euler F).basis q) ((IntegralCriticalTotalCreatingBits.euler F).basis c) :=
  canonical_basis_heq _ _ (IntegralCriticalTotalCreatingBits.atFamily_invariance F q c hr hb)

theorem polynomial_invariance (F : Scripts) (q c : List Bool)
    (hr : root q = root c)
    (hb : IntegralCriticalHistoryTask.birth F.toParameters q = IntegralCriticalHistoryTask.birth F.toParameters c) :
    HEq ((IntegralCriticalTotalCreatingBits.euler F).polynomial q) ((IntegralCriticalTotalCreatingBits.euler F).polynomial c) :=
  canonical_polynomial_heq _ _ (IntegralCriticalTotalCreatingBits.atFamily_invariance F q c hr hb)

theorem lower_invariance (F : Scripts) (q c : List Bool)
    (hr : root q = root c)
    (hb : IntegralCriticalHistoryTask.birth F.toParameters q = IntegralCriticalHistoryTask.birth F.toParameters c) :
    HEq ((IntegralCriticalTotalCreatingBits.euler F).lowerPolynomial q) ((IntegralCriticalTotalCreatingBits.euler F).lowerPolynomial c) :=
  canonical_lower_heq _ _ (IntegralCriticalTotalCreatingBits.atFamily_invariance F q c hr hb)

end LeanCanny.Algebra.IntegralCriticalTotalSnapshotBits
