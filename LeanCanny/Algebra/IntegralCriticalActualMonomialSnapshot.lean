/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalFlatActualLow
public import LeanCanny.Algebra.IntegralCriticalActualGradientSnapshot
/-! # Canonical actual monomial data with natural query selectors -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMonomialTermBits
open LeanCanny.Encoding
noncomputable def Source.snapshot (S : Source) (q : List Bool) : Source where
  arity _ := S.arity q
  rank _ := S.rank q
  carrier _ := S.carrier q
  ring _ := S.ring q
  basis _ := S.basis q
  coefficient _ := S.coefficient q
  denominator _ := S.denominator q
  height _ := S.height q
  exponent _ := S.exponent q
  allowance _ := S.allowance q
  offset _ := S.offset q
  free _ := S.free q
  row _ := S.row q
  col _ := S.col q
  modulus _ := S.modulus q
  modulus_ne_zero _ := S.modulus_ne_zero q

theorem snapshot_requery (S : Source) (input : List Bool → List Bool) (q : List Bool) :
    (S.requery input).snapshot q = S.snapshot (input q) := rfl

theorem snapshot_value (S : Source) (q : List Bool) : (S.snapshot q).value [] = S.value q := rfl
end LeanCanny.Algebra.IntegralMonomialTermBits

namespace LeanCanny.Algebra.IntegralCriticalActualMonomialSnapshot
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalTotalCompanionBits
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily
attribute [local irreducible] IntegralCriticalHistoryTask.get IntegralCriticalHistoryTask.numericCap

noncomputable def monomialAt (A : IntegralHistoryCriticalBits.Family) (x j k r t m : ℕ) (hm : m ≠ 0) :
    IntegralMonomialTermBits.Source := by
  let E := IntegralCriticalActualScalarModels.eulerAt (IntegralCriticalActualGradientSnapshot.queried A 0 r t m hm)
  let := E.ring []
  let p := if x = 1 then MvPolynomial.pderiv
    (IntegralCriticalGradientBits.freeIndex E.toGradient []
      (IntegralCriticalActualScalarModels.selectedAt (IntegralCriticalActualGradientSnapshot.queried A 0 r t m hm) j []))
      (E.polynomial []) else E.polynomial []
  exact {
    arity _ := E.arity []
    rank _ := E.rank []
    carrier _ := E.carrier []
    ring _ := E.ring []
    basis _ := E.basis []
    coefficient _ := p.coeff (RationalSubstitution.Indexed.exponentVector (E.arity [])
      (FixedWidthPolynomial.entry (E.sourceWidth []) k))
    denominator _ := E.denominator []
    height _ := E.height []
    exponent _ i := if i < E.arity [] then FixedWidthPolynomial.entry (E.sourceWidth []) k i else 0
    allowance _ := E.allowance []
    offset _ := E.offset []
    free _ := E.free []
    row _ := E.row []
    col _ := E.col []
    modulus _ := m
    modulus_ne_zero _ := hm }

noncomputable def snapshot (F : Scripts) (q : List Bool) :=
  monomialAt (IntegralCriticalTotalCreatingBits.atFamily F q)
    (IntegralCriticalHistoryTask.get F.toParameters .expression q)
    (IntegralCriticalHistoryTask.get F.toParameters .derivative q)
    (IntegralCriticalHistoryTask.get F.toParameters .sourceIndex q)
    (IntegralCriticalHistoryTask.get F.toParameters .row q) (IntegralCriticalHistoryTask.get F.toParameters .col q)
    (IntegralCriticalHistoryTask.modulus F.toParameters q) (IntegralCriticalHistoryTask.modulus_ne_zero F.toParameters q)

noncomputable def packetSnapshot (F : Scripts) (p : List Bool) :=
  monomialAt (IntegralCriticalTotalCreatingBits.atFamily F (pairFst p))
    (IntegralCriticalHistoryTask.get F.toParameters .expression (pairFst p))
    (IntegralCriticalHistoryTask.get F.toParameters .derivative (pairFst p))
    (Nat.fromBitsLE (pairSnd p))
    (IntegralCriticalHistoryTask.get F.toParameters .row (pairFst p)) (IntegralCriticalHistoryTask.get F.toParameters .col (pairFst p))
    (IntegralCriticalHistoryTask.modulus F.toParameters (pairFst p)) (IntegralCriticalHistoryTask.modulus_ne_zero F.toParameters (pairFst p))

theorem term_snapshot (F : Scripts) (p : List Bool) :
    (IntegralClearedCoefficientBits.termSource
      (IntegralCriticalFlatGenericGridBits.source F.toParameters (IntegralCriticalTotalCreatingBits.euler F))).snapshot p =
        packetSnapshot F p := by
  unfold packetSnapshot
  unfold IntegralMonomialTermBits.Source.snapshot IntegralClearedCoefficientBits.termSource monomialAt
  dsimp only
  have HE : FixedWidthQuery.entry
      (fun z => (IntegralCriticalFlatGenericGridBits.source F.toParameters (IntegralCriticalTotalCreatingBits.euler F)).arity (pairFst z))
      (fun z => (IntegralCriticalFlatGenericGridBits.source F.toParameters (IntegralCriticalTotalCreatingBits.euler F)).sourceWidth (pairFst z))
      pairSnd p = fun i =>
        if i < (IntegralCriticalFlatGenericGridBits.source F.toParameters (IntegralCriticalTotalCreatingBits.euler F)).arity (pairFst p)
        then FixedWidthPolynomial.entry
          ((IntegralCriticalFlatGenericGridBits.source F.toParameters (IntegralCriticalTotalCreatingBits.euler F)).sourceWidth (pairFst p))
          (Nat.fromBitsLE (pairSnd p)) i else 0 := by
    funext i
    rw [FixedWidthQuery.entry, FixedWidthQuery.coordinate_eq_entry]
  rw [HE]
  rfl

theorem packet_value_snapshot (F : Scripts) (p : List Bool) :
    (IntegralClearedCoefficientBits.termSource
      (IntegralCriticalFlatGenericGridBits.source F.toParameters (IntegralCriticalTotalCreatingBits.euler F))).value p =
        (packetSnapshot F p).value [] := by
  rw [← term_snapshot]
  exact (IntegralMonomialTermBits.snapshot_value _ p).symm

theorem source_snapshot (F : Scripts) (q : List Bool) :
    (IntegralCriticalFlatActualLow.source F).snapshot q = snapshot F q := by
  unfold IntegralCriticalFlatActualLow.source IntegralCriticalFlatGenericGridBits.monomialSource
  rw [IntegralMonomialTermBits.snapshot_requery]
  generalize hp : IntegralCriticalFlatGridBits.termInput F.toParameters q = p
  have HO : pairFst p = q := by rw [← hp, IntegralCriticalFlatGridBits.termInput_parent]
  have HK : Nat.fromBitsLE (pairSnd p) = IntegralCriticalHistoryTask.get F.toParameters .sourceIndex q := by
    rw [← hp, IntegralCriticalFlatGridBits.termInput, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  subst q
  unfold snapshot
  rw [← HK]
  unfold IntegralMonomialTermBits.Source.snapshot IntegralClearedCoefficientBits.termSource monomialAt
  dsimp only
  have HE : FixedWidthQuery.entry
      (fun z => (IntegralCriticalFlatGenericGridBits.source F.toParameters (IntegralCriticalTotalCreatingBits.euler F)).arity (pairFst z))
      (fun z => (IntegralCriticalFlatGenericGridBits.source F.toParameters (IntegralCriticalTotalCreatingBits.euler F)).sourceWidth (pairFst z))
      pairSnd p = fun i =>
        if i < (IntegralCriticalFlatGenericGridBits.source F.toParameters (IntegralCriticalTotalCreatingBits.euler F)).arity (pairFst p)
        then FixedWidthPolynomial.entry
          ((IntegralCriticalFlatGenericGridBits.source F.toParameters (IntegralCriticalTotalCreatingBits.euler F)).sourceWidth (pairFst p))
          (Nat.fromBitsLE (pairSnd p)) i else 0 := by
    funext i
    rw [FixedWidthQuery.entry, FixedWidthQuery.coordinate_eq_entry]
  rw [HE]
  rfl

theorem value_snapshot (F : Scripts) (q : List Bool) :
    (IntegralCriticalFlatActualLow.source F).value q = (snapshot F q).value [] := by
  rw [← source_snapshot]
  exact (IntegralMonomialTermBits.snapshot_value _ q).symm

theorem monomialAt_congr (A B : IntegralHistoryCriticalBits.Family)
    (x j k r t m x' j' k' r' t' m' : ℕ) (hm : m ≠ 0) (hm' : m' ≠ 0)
    (hA : A = B) (hx : x = x') (hj : j = j') (hk : k = k') (hr : r = r') (ht : t = t') (hmod : m = m') :
    monomialAt A x j k r t m hm = monomialAt B x' j' k' r' t' m' hm' := by
  subst B; subst x'; subst j'; subst k'; subst r'; subst t'; subst m'
  rfl

theorem snapshot_invariance (F : Scripts) (child q : List Bool)
    (hroot : root child = root q)
    (hbirth : IntegralCriticalHistoryTask.birth F.toParameters child = IntegralCriticalHistoryTask.birth F.toParameters q)
    (hmod : IntegralCriticalHistoryTask.modulus F.toParameters child = IntegralCriticalHistoryTask.modulus F.toParameters q)
    (hx : IntegralCriticalHistoryTask.get F.toParameters .expression child = IntegralCriticalHistoryTask.get F.toParameters .expression q)
    (hj : IntegralCriticalHistoryTask.get F.toParameters .derivative child = IntegralCriticalHistoryTask.get F.toParameters .derivative q)
    (hk : IntegralCriticalHistoryTask.get F.toParameters .sourceIndex child = IntegralCriticalHistoryTask.get F.toParameters .sourceIndex q)
    (hr : IntegralCriticalHistoryTask.get F.toParameters .row child = IntegralCriticalHistoryTask.get F.toParameters .row q)
    (ht : IntegralCriticalHistoryTask.get F.toParameters .col child = IntegralCriticalHistoryTask.get F.toParameters .col q) :
    snapshot F child = snapshot F q := by
  exact monomialAt_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (IntegralCriticalTotalCreatingBits.atFamily_invariance F child q hroot hbirth) hx hj hk hr ht hmod

end LeanCanny.Algebra.IntegralCriticalActualMonomialSnapshot
