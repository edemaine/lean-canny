/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegerModular
public import LeanCanny.Algebra.BerkowitzSpaceEntries
public import LeanCanny.Computation.BoundedScanPSPACE

/-!
# Polynomial-space zero testing of integer determinants

An FP binary budget bounds the determinant's magnitude bit length. Uniform FP
residue access supplies original entries modulo any positive binary modulus;
the integer entries themselves need not have polynomial-length encodings.
Scanning the moduli up to twice the budget plus four decides determinant zero.
The scan and each modular determinant call have fully accounted workspace.
-/

@[expose] public section

namespace LeanCanny.Algebra.Berkowitz

open LeanCanny.Encoding
open LeanCanny.Computation
open MatrixPower

structure IntegerFamily where
  dimension : List Bool → ℕ
  matrix : (c : List Bool) → Matrix (Fin (dimension c)) (Fin (dimension c)) ℤ
  budget : List Bool → ℕ
  determinant_bits : ∀ c, (matrix c).det.natAbs.size ≤ budget c

def IntegerFamily.zeroLanguage (F : IntegerFamily) : Language := {c | (F.matrix c).det = 0}

def IntegerFamily.modular (F : IntegerFamily) : ModularFamily where
  dimension := fun q => F.dimension (pairFst q)
  modulus := fun q => Nat.fromBitsLE (pairSnd q) + 1
  matrix := fun q => (F.matrix (pairFst q)).map
    (Int.castRingHom (ZMod (Nat.fromBitsLE (pairSnd q) + 1)))
  modulus_ne_zero := fun _ => by omega

/-- A modular context is `pair c b`, with modulus `fromBitsLE b + 1`.
The entry routine receives that context paired with the two binary indices.
Correctness and canonical field access cover every input context. -/
structure IntegerAccess (F : IntegerFamily) where
  dimension : List Bool → List Bool
  budget : List Bool → List Bool
  entry : List Bool → List Bool
  dimension_eq : ∀ c, dimension c = BinaryNatCode.encode (F.dimension c)
  budget_eq : ∀ c, budget c = BinaryNatCode.encode (F.budget c)
  entry_eq : ∀ q i j, entry (pair q
    (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      residueBits ((F.matrix (pairFst q) i j : ℤ) : ZMod (Nat.fromBitsLE (pairSnd q) + 1))

structure IntegerAccess.PolyTime {F : IntegerFamily} (a : IntegerAccess F) : Prop where
  dimension : a.dimension ∈ FP
  budget : a.budget ∈ FP
  entry : a.entry ∈ FP

namespace IntegerAccess

def modular {F : IntegerFamily} (a : IntegerAccess F) : ModularAccess F.modular where
  access := ⟨a.dimension ∘ pairFst, BinaryNat.succ ∘ pairSnd, a.entry⟩
  correct := fun q => {
    dimension := a.dimension_eq (pairFst q)
    modulus := by simp only [IntegerFamily.modular, Function.comp_apply,
      BinaryNat.succ_eq_bits, BinaryNatCode.encode]
    entry := a.entry_eq q }

theorem modular_polyTime {F : IntegerFamily} (a : IntegerAccess F) (ha : a.PolyTime) :
    a.modular.access.PolyTime := by
  have hd := mem_FP_comp pairFst_mem_FP ha.dimension
  have hm := mem_FP_comp pairSnd_mem_FP BinaryNat.succ_mem_FP
  exact ⟨hd, hm, ha.entry⟩

def bound {F : IntegerFamily} (a : IntegerAccess F) (c : List Bool) : List Bool :=
  BinaryNat.add (pair (BinaryNat.add (pair (a.budget c) (a.budget c))) (BinaryNatCode.encode 4))

theorem bound_mem_FP {F : IntegerFamily} (a : IntegerAccess F) (ha : a.PolyTime) : bound a ∈ FP := by
  have hd := mem_FP_comp (mem_FP_pair ha.budget ha.budget) BinaryNat.add_mem_FP
  have h := mem_FP_comp (mem_FP_pair hd (constFn_mem_FP (BinaryNatCode.encode 4))) BinaryNat.add_mem_FP
  refine mem_FP_of_eq (g := bound a) h ?_
  intro c
  simp only [Function.comp_apply, bound]

theorem bound_code {F : IntegerFamily} (a : IntegerAccess F) (c : List Bool) :
    bound a c = BinaryNatCode.encode (2 * F.budget c + 4) := by
  simp only [bound, BinaryNat.add_pair, a.budget_eq, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  congr 1
  omega

theorem modular_packet {F : IntegerFamily} (c : List Bool) (k : ℕ) :
    pair c (BinaryNatCode.encode k) ∈ F.modular.zeroLanguage ↔
      ((F.matrix c).map (Int.castRingHom (ZMod (k + 1)))).det = 0 := by
  change ((F.matrix (pairFst (pair c (BinaryNatCode.encode k)))).map
    (Int.castRingHom (ZMod (Nat.fromBitsLE (pairSnd (pair c (BinaryNatCode.encode k))) + 1)))).det = 0 ↔ _
  rw [pairFst_pair, pairSnd_pair]
  rw [show Nat.fromBitsLE (BinaryNatCode.encode k) = k from Nat.fromBitsLE_bits k]

theorem scan_language_eq (F : IntegerFamily) :
    BoundedScan.language F.modular.zeroLanguage (fun c => 2 * F.budget c + 4) = F.zeroLanguage := by
  ext c
  change (∀ k < 2 * F.budget c + 4, pair c (BinaryNatCode.encode k) ∈ F.modular.zeroLanguage) ↔
    (F.matrix c).det = 0
  rw [IntegerModular.det_eq_zero_iff_residues (F.matrix c) (F.budget c) (F.determinant_bits c)]
  constructor
  · intro h m hm hn
    have hr := (modular_packet (F := F) c (m - 1)).mp (h (m - 1) (by omega))
    rw [Nat.sub_add_cancel hm] at hr
    exact hr
  · intro h k hk
    apply (modular_packet (F := F) c k).mpr
    exact h (k + 1) (by omega) (by omega)

theorem decider {F : IntegerFamily} (a : IntegerAccess F) (ha : a.PolyTime) :
    SpaceDecider F.zeroLanguage := by
  rw [← scan_language_eq F]
  exact BoundedScan.decider (ModularAccess.decider a.modular (modular_polyTime a ha))
    (bound a) (bound_mem_FP a ha) (fun c => 2 * F.budget c + 4) (bound_code a)

theorem zeroLanguage_mem_PSPACE {F : IntegerFamily} (a : IntegerAccess F) (ha : a.PolyTime) :
    F.zeroLanguage ∈ PSPACE := (decider a ha).mem_PSPACE

end IntegerAccess
end LeanCanny.Algebra.Berkowitz
