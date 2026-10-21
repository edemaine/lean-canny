/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PrimitivePairSeparation
public import LeanCanny.Computation.BoundedChoice

/-! # A canonical integer primitive-pair construction

The selected direction depends only on the two polynomials. It is the last
successful candidate in the same bounded scan used by the native readers.
-/

@[expose] public section

namespace LeanCanny.Algebra.PrimitivePair
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation

def candidateLanguage (p q : ℤ[X]) : Language :=
  {w | ((cannyResultant p q (Nat.fromBitsLE (pairSnd w))).map (Int.castRingHom ℚ)).Separable}

noncomputable def select (p q : ℤ[X]) : ℕ :=
  BoundedChoice.search (candidateLanguage p q) [] ((p.natDegree * q.natDegree) ^ 2 + 1) - 1

theorem select_spec {L : Type*} [Field L] [CharZero L] (p q : ℤ[X])
    (hp : (p.map (Int.castRingHom L)).Separable) (hq : (q.map (Int.castRingHom L)).Separable)
    (hsp : (p.map (Int.castRingHom L)).Splits) (hsq : (q.map (Int.castRingHom L)).Splits) :
    select p q ≤ (p.natDegree * q.natDegree) ^ 2 ∧
      Set.InjOn (shear (select p q))
        (rootPairs (L := L) (p.map (Int.castRingHom L)) (q.map (Int.castRingHom L)) : Set (L × L)) := by
  have hsp' : ((p.map (Int.castRingHom L)).map (algebraMap L L)).Splits := by
    simpa only [Algebra.algebraMap_self, Polynomial.map_id] using hsp
  have hsq' : ((q.map (Int.castRingHom L)).map (algebraMap L L)).Splits := by
    simpa only [Algebra.algebraMap_self, Polynomial.map_id] using hsq
  obtain ⟨k, hk, hi⟩ := exists_bounded_direction _ _ hp hq hsp' hsq'
  have hcast : Function.Injective (Int.castRingHom L) := Int.cast_injective
  rw [Polynomial.natDegree_map_eq_of_injective hcast, Polynomial.natDegree_map_eq_of_injective hcast] at hk
  have hmember (j : ℕ) : LeanCanny.pair [] (BinaryNatCode.encode j) ∈ candidateLanguage p q ↔
      Set.InjOn (shear j) (rootPairs (L := L) (p.map (Int.castRingHom L)) (q.map (Int.castRingHom L)) : Set (L × L)) := by
    simp only [candidateLanguage, Set.mem_ofPred_eq, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact integer_separable_iff_separating p q j hp hq hsp hsq
  have hw := BoundedChoice.witness (candidateLanguage p q) [] ((p.natDegree * q.natDegree) ^ 2 + 1)
    ⟨k, by omega, (hmember k).mpr hi⟩
  exact ⟨by change select p q < _ ∧ _ at hw; omega, (hmember _).mp hw.2⟩

end LeanCanny.Algebra.PrimitivePair
