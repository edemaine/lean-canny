/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayEntryCorrect

/-! # Macaulay entries with an arbitrary scalar encoding

The same selector applies to polynomial coefficients. Identity padding must then
encode the requested coefficient of one, which is zero at positive degrees.
No compatibility of the scalar encoding with multiplication is required.
-/

@[expose] public section

namespace LeanCanny.Algebra.MacaulayBits
open Complexity
open LeanCanny.Encoding LeanCanny.Computation

def entryWithIdentity (L : Layout) (coefficient identity : List Bool → List Bool) (p : List Bool) : List Bool :=
  if active L p then
    if admissible L p then coefficient (sourceQuery L p) else []
  else identity p

noncomputable def entryWithIdentityEvaluator {L : Layout} (h : L.PolyTime)
    {coefficient identity : List Bool → List Bool} (E : SpaceFunction coefficient) (hI : identity ∈ FP) :
    SpaceFunction (entryWithIdentity L coefficient identity) := by
  have EC := E.precompose (sourceQuery L) (sourceQuery_mem_FP h)
  have EA := SpaceFunction.branch (fun p => decide (admissible L p)) (admissible_fppred h).flag_mem_FP
    EC (SpaceFunction.ofFP _ (constFn_mem_FP []))
  have ER := SpaceFunction.branch (fun p => decide (active L p)) (active_fppred h).flag_mem_FP
    EA (SpaceFunction.ofFP _ hI)
  exact ER.congr (funext fun p => by simp only [entryWithIdentity, decide_eq_true_eq, Function.comp_apply])

theorem entryWithIdentity_packet {R : Type*} [CommRing R] (L : Layout)
    (coefficient identity : List Bool → List Bool) (q : List Bool)
    (p : Fin (L.arity (pairFst q)) → MvPolynomial (Fin (L.arity (pairFst q))) R)
    (enc : R → List Bool) (hz : enc 0 = [])
    (hc : ∀ (i : Fin (L.arity (pairFst q))) (k : ℕ), coefficient (packet q i.val k) =
      enc ((p i).coeff (RationalSubstitution.Indexed.exponentVector (L.arity (pairFst q))
        (FixedWidthPolynomial.entry (L.width (pairFst q)) k))))
    (r s : Indices L q)
    (hI : identity (packet q r.val s.val) = enc (if r.val = s.val then 1 else 0)) :
    entryWithIdentity L coefficient identity (packet q r.val s.val) =
      enc (Macaulay.matrix p (Degrees L (pairFst q)) (L.width (pairFst q)) r s) := by
  by_cases hr : (FixedWidthPolynomial.vector _ _ r).degree = Macaulay.level (Degrees L (pairFst q))
  · have ha := (active_packet L q r s.val).mpr hr
    rw [entryWithIdentity, ite_eq_left ha, Macaulay.entry_active p _ _ r s hr]
    by_cases hg : Macaulay.remainder _ _ hr ≤ FixedWidthPolynomial.vector _ _ s
    · rw [ite_eq_left ((admissible_packet L q r s hr).mpr hg), ite_eq_left hg, sourceQuery_packet,
        pivot_packet L q r s.val hr]
      rw [show pair q (pair (BinaryNatCode.encode (Macaulay.pivot _ _ hr).val)
        (BinaryNatCode.encode (Nat.fromBitsLE (differenceWord L (packet q r.val s.val))))) =
        packet q (Macaulay.pivot _ _ hr).val (Nat.fromBitsLE (differenceWord L (packet q r.val s.val))) from rfl,
        hc, difference_exponent L q r s hr]
    · rw [ite_eq_right (fun h => hg ((admissible_packet L q r s hr).mp h)), ite_eq_right hg, hz]
  · have ha : ¬active L (packet q r.val s.val) := fun h => hr ((active_packet L q r s.val).mp h)
    rw [entryWithIdentity, ite_eq_right ha, hI, Macaulay.matrix, dite_eq_right hr]
    simp only [Matrix.one_apply, Fin.ext_iff]

end LeanCanny.Algebra.MacaulayBits
