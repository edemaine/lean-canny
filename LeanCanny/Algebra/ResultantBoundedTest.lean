/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ResultantSpace
public import LeanCanny.Algebra.IntegerZeroSpace
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # A total modular resultant test with pointwise integer correctness

Supplied orders and a bit budget define a native space modulus scan on every
input. Its integer-zero interpretation requires the budget only at the input
being tested. This permits partially prepared metadata tables: no global
degree, height, or consistency promise is needed to certify the scan itself.
-/

@[expose] public section

namespace LeanCanny.Algebra.ResultantBoundedTest
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation MatrixPower

variable (p q : List Bool → ℤ[X]) (m n : List Bool → ℕ)

def integerMatrix (c : List Bool) : Matrix (Fin (m c + n c)) (Fin (m c + n c)) ℤ :=
  Polynomial.sylvester (p c) (q c) (m c) (n c)

def modular : Berkowitz.ModularFamily where
  dimension c := m (pairFst c) + n (pairFst c)
  modulus c := Nat.fromBitsLE (pairSnd c) + 1
  matrix c := (integerMatrix p q m n (pairFst c)).map
    (Int.castRingHom (ZMod (Nat.fromBitsLE (pairSnd c) + 1)))
  modulus_ne_zero _ := by omega

def bits (left right : List Bool → List Bool) : SylvesterBits.Access where
  leftDegree c := BinaryNatCode.encode (m c)
  rightDegree c := BinaryNatCode.encode (n c)
  coefficientBits _ := []
  leftCoefficient := left
  rightCoefficient := right

variable (left right : List Bool → List Bool)
variable (hl : ∀ c k, left (pair c (BinaryNatCode.encode k)) =
    residueBits (((p (pairFst c)).coeff k : ℤ) : ZMod (Nat.fromBitsLE (pairSnd c) + 1)))
variable (hr : ∀ c k, right (pair c (BinaryNatCode.encode k)) =
    residueBits (((q (pairFst c)).coeff k : ℤ) : ZMod (Nat.fromBitsLE (pairSnd c) + 1)))

def access : Berkowitz.ModularAccess (modular p q m n) where
  access := {
    dimension := SylvesterBits.dimension (bits m n left right) ∘ pairFst
    modulus := BinaryNat.succ ∘ pairSnd
    entry := SylvesterBits.entry (bits m n left right) }
  correct c := {
    dimension := SylvesterBits.dimension_code (bits m n left right) (pairFst c) _ _ rfl rfl
    modulus := BinaryNat.succ_eq_bits _
    entry := by
      intro i j
      exact SylvesterBits.entry_correct (bits m n left right) c (p (pairFst c)) (q (pairFst c))
        (m (pairFst c)) (n (pairFst c))
        (fun z : ℤ => residueBits (z : ZMod (Nat.fromBitsLE (pairSnd c) + 1)))
        ⟨rfl, rfl, hl c, hr c, by simp [residueBits, BinaryNatCode.encode]⟩ i j }

theorem bits_controls (hm : BinaryFn m) (hn : BinaryFn n) : (bits m n left right).ControlsPolyTime :=
  ⟨hm.bits_mem_FP, hn.bits_mem_FP, constFn_mem_FP []⟩

theorem controls (hm : BinaryFn m) (hn : BinaryFn n) : (access p q m n left right hl hr).ControlsPolyTime := by
  have hd := mem_FP_comp pairFst_mem_FP
    (SylvesterBits.dimension_mem_FP_of_controls (bits m n left right) (bits_controls m n left right hm hn))
  have hmod := mem_FP_comp pairSnd_mem_FP BinaryNat.succ_mem_FP
  exact ⟨hd, hmod⟩

def language (budget : List Bool → ℕ) : Language :=
  BoundedScan.language (modular p q m n).zeroLanguage (fun c => 2 * budget c + 4)

include hl hr in
theorem decider (hm : BinaryFn m) (hn : BinaryFn n) (L : SpaceFunction left) (R : SpaceFunction right)
    (budget : List Bool → ℕ) (hb : BinaryFn budget) : SpaceDecider (language p q m n budget) := by
  have E := SylvesterBits.entryEvaluator (bits m n left right) (bits_controls m n left right hm hn) L R
  have D := Berkowitz.ModularAccess.deciderWithEntry (access p q m n left right hl hr)
    (controls p q m n left right hl hr hm hn) E
  exact BoundedScan.decider D (IntegerZeroBits.count (fun c => BinaryNatCode.encode (budget c)))
    (IntegerZeroBits.count_mem_FP hb.bits_mem_FP) (fun c => 2 * budget c + 4)
    (fun c => by simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits] using
      IntegerZeroBits.count_code (fun c => BinaryNatCode.encode (budget c)) c)

theorem modular_packet (c : List Bool) (k : ℕ) :
    pair c (BinaryNatCode.encode k) ∈ (modular p q m n).zeroLanguage ↔
      ((Polynomial.sylvester (p c) (q c) (m c) (n c)).map (Int.castRingHom (ZMod (k + 1)))).det = 0 := by
  change ((integerMatrix p q m n (pairFst (pair c (BinaryNatCode.encode k)))).map
    (Int.castRingHom (ZMod (Nat.fromBitsLE (pairSnd (pair c (BinaryNatCode.encode k))) + 1)))).det = 0 ↔ _
  rw [pairFst_pair, pairSnd_pair]
  rw [show Nat.fromBitsLE (BinaryNatCode.encode k) = k from Nat.fromBitsLE_bits k]
  rfl

/-- Only this input's bit bound is required. The supplied orders may differ
from the actual degrees; the conclusion uses their specified-degree resultant. -/
theorem correct_at (budget : List Bool → ℕ) (c : List Bool)
    (hb : ((p c).resultant (q c) (m c) (n c)).natAbs.size ≤ budget c) :
    c ∈ language p q m n budget ↔ (p c).resultant (q c) (m c) (n c) = 0 := by
  change (∀ k < 2 * budget c + 4, pair c (BinaryNatCode.encode k) ∈ (modular p q m n).zeroLanguage) ↔
    (Polynomial.sylvester (p c) (q c) (m c) (n c)).det = 0
  rw [IntegerModular.det_eq_zero_iff_residues _ (budget c) hb]
  constructor
  · intro h mod hm hmod
    have he := (modular_packet p q m n c (mod - 1)).mp (h (mod - 1) (by omega))
    rw [Nat.sub_add_cancel hm] at he
    exact he
  · intro h k hk
    exact (modular_packet p q m n c k).mpr (h (k + 1) (by omega) (by omega))

end LeanCanny.Algebra.ResultantBoundedTest
