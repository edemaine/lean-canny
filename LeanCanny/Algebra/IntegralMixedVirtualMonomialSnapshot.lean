/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalActualMonomialSnapshot
public import LeanCanny.Algebra.IntegralMixedVirtualSpatialModel
/-! # Canonical actual monomial snapshots of the virtual source -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualMonomialBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualSnapshotBits
set_option backward.isDefEq.respectTransparency false

noncomputable def source (P : Parameters) (F : Family) :=
  IntegralCriticalFlatGenericGridBits.monomialSource P (IntegralMixedVirtualTaskBits.arithmetic P F)
noncomputable def access (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) :=
  IntegralCriticalFlatGenericGridBits.monomialAccess P a (IntegralMixedVirtualTaskBits.arithmetic P F) (IntegralMixedVirtualTaskBits.access P a F h).toEuler

noncomputable def monomialAt (F : Family) (key : List Bool) (x j k r t m : ℕ) (hm : m ≠ 0) :
    IntegralMonomialTermBits.Source := by
  let E := (sourceAt F key 0 0 0 r t m hm).toEuler
  let := E.ring []
  let p := if x = 1 then MvPolynomial.pderiv
    (IntegralCriticalGradientBits.freeIndex E.toGradient [] ⟨j % E.free [], Nat.mod_lt _ (E.free_pos [])⟩)
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

noncomputable def snapshot (P : Parameters) (F : Family) (q : List Bool) :=
  monomialAt F (IntegralMixedVirtualTaskBits.saved P q) (get P .expression q) (get P .derivative q)
    (get P .sourceIndex q) (get P .row q) (get P .col q) (modulus P q) (modulus_ne_zero P q)
noncomputable def packetSnapshot (P : Parameters) (F : Family) (p : List Bool) :=
  monomialAt F (IntegralMixedVirtualTaskBits.saved P (pairFst p)) (get P .expression (pairFst p)) (get P .derivative (pairFst p))
    (Nat.fromBitsLE (pairSnd p)) (get P .row (pairFst p)) (get P .col (pairFst p))
      (modulus P (pairFst p)) (modulus_ne_zero P (pairFst p))

theorem term_snapshot (P : Parameters) (F : Family) (p : List Bool) :
    (IntegralClearedCoefficientBits.termSource
      (IntegralCriticalFlatGenericGridBits.source P (IntegralMixedVirtualTaskBits.arithmetic P F))).snapshot p =
        packetSnapshot P F p := by
  unfold packetSnapshot IntegralMonomialTermBits.Source.snapshot IntegralClearedCoefficientBits.termSource monomialAt
  dsimp only
  have HE : FixedWidthQuery.entry
      (fun z => (IntegralCriticalFlatGenericGridBits.source P (IntegralMixedVirtualTaskBits.arithmetic P F)).arity (pairFst z))
      (fun z => (IntegralCriticalFlatGenericGridBits.source P (IntegralMixedVirtualTaskBits.arithmetic P F)).sourceWidth (pairFst z)) pairSnd p =
      fun i => if i < (IntegralCriticalFlatGenericGridBits.source P (IntegralMixedVirtualTaskBits.arithmetic P F)).arity (pairFst p)
        then FixedWidthPolynomial.entry ((IntegralCriticalFlatGenericGridBits.source P (IntegralMixedVirtualTaskBits.arithmetic P F)).sourceWidth (pairFst p))
          (Nat.fromBitsLE (pairSnd p)) i else 0 := by
    funext i
    rw [FixedWidthQuery.entry, FixedWidthQuery.coordinate_eq_entry]
  rw [HE]
  rfl

theorem source_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    (source P F).snapshot q = snapshot P F q := by
  unfold source IntegralCriticalFlatGenericGridBits.monomialSource
  rw [IntegralMonomialTermBits.snapshot_requery]
  generalize hp : IntegralCriticalFlatGridBits.termInput P q = p
  have HO : pairFst p = q := by rw [← hp, IntegralCriticalFlatGridBits.termInput_parent]
  have HK : Nat.fromBitsLE (pairSnd p) = get P .sourceIndex q := by
    rw [← hp]
    simp only [IntegralCriticalFlatGridBits.termInput, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  subst q
  unfold snapshot
  rw [← HK]
  unfold IntegralMonomialTermBits.Source.snapshot IntegralClearedCoefficientBits.termSource monomialAt
  dsimp only
  have HE : FixedWidthQuery.entry
      (fun z => (IntegralCriticalFlatGenericGridBits.source P (IntegralMixedVirtualTaskBits.arithmetic P F)).arity (pairFst z))
      (fun z => (IntegralCriticalFlatGenericGridBits.source P (IntegralMixedVirtualTaskBits.arithmetic P F)).sourceWidth (pairFst z)) pairSnd p =
      fun i => if i < (IntegralCriticalFlatGenericGridBits.source P (IntegralMixedVirtualTaskBits.arithmetic P F)).arity (pairFst p)
        then FixedWidthPolynomial.entry ((IntegralCriticalFlatGenericGridBits.source P (IntegralMixedVirtualTaskBits.arithmetic P F)).sourceWidth (pairFst p))
          (Nat.fromBitsLE (pairSnd p)) i else 0 := by
    funext i
    rw [FixedWidthQuery.entry, FixedWidthQuery.coordinate_eq_entry]
  rw [HE]
  rfl

theorem monomialAt_congr (F : Family) (key key' : List Bool) (x j k r t m x' j' k' r' t' m' : ℕ)
    (hm : m ≠ 0) (hm' : m' ≠ 0) (hkey : key = key') (hx : x = x') (hj : j = j') (hk : k = k')
    (hr : r = r') (ht : t = t') (hmod : m = m') :
    monomialAt F key x j k r t m hm = monomialAt F key' x' j' k' r' t' m' hm' := by
  subst key'; subst x'; subst j'; subst k'; subst r'; subst t'; subst m'
  rfl
end LeanCanny.Algebra.IntegralMixedVirtualMonomialBits
