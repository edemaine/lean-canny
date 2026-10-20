/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayDeformationSpace
public import LeanCanny.Algebra.MacaulayBounds

/-! # Modular coefficient evaluation for the integer deformation determinant -/

@[expose] public section

namespace LeanCanny.Algebra.MacaulayDeformationBits
open Complexity
open LeanCanny.Encoding LeanCanny.Computation
open MatrixPower

structure Family where
  source : MacaulayBits.Family
  degree : List Bool → ℕ

noncomputable def Family.polynomial (F : Family) (c : List Bool) : Polynomial ℤ :=
  (Macaulay.matrix (Macaulay.deformation (F.source.polynomial c) (MacaulayBits.Degrees F.source.layout c))
    (MacaulayBits.Degrees F.source.layout c) (F.source.layout.width c)).det

noncomputable def Family.coefficient (F : Family) (c : List Bool) : ℤ := (F.polynomial c).coeff (F.degree c)

noncomputable def Family.modular (F : Family) : BerkowitzPolynomial.ModularFamily where
  dimension := fun q => FixedWidthPolynomial.count (F.source.layout.arity (pairFst q)) (F.source.layout.width (pairFst q))
  modulus := fun q => Nat.fromBitsLE (pairSnd q) + 1
  degree := fun q => F.degree (pairFst q)
  matrix := fun q => (Macaulay.matrix
    (Macaulay.deformation (F.source.polynomial (pairFst q)) (MacaulayBits.Degrees F.source.layout (pairFst q)))
    (MacaulayBits.Degrees F.source.layout (pairFst q)) (F.source.layout.width (pairFst q))).map
      (Polynomial.mapRingHom (Int.castRingHom (ZMod (Nat.fromBitsLE (pairSnd q) + 1))))
  modulus_ne_zero := fun _ => by omega

noncomputable def Family.value (F : Family) : List Bool → List Bool := F.modular.value

structure Access (F : Family) where
  original : MacaulayBits.Access F.source
  degree : List Bool → List Bool
  degree_eq : ∀ c, degree c = BinaryNatCode.encode (F.degree c)

def Access.entry {F : Family} (a : Access F) (p : List Bool) : List Bool :=
  finish (pair p (MacaulayBits.entry F.source.layout a.original.coefficient (originalQuery p)))

noncomputable def Access.entryEvaluator {F : Family} (a : Access F) (h : F.source.layout.PolyTime)
    (E : SpaceFunction a.original.coefficient) : SpaceFunction a.entry := by
  have EO := (a.original.integer_entryEvaluator h E).precompose originalQuery originalQuery_mem_FP
  have ES := EO.withInput.postcompose finish finish_mem_FP
  exact ES.congr (funext fun p => rfl)

theorem Access.entry_correct {F : Family} (a : Access F) (q : List Bool)
    (i j : Macaulay.Index (F.source.layout.arity (pairFst q)) (F.source.layout.width (pairFst q))) (D : ℕ) :
    a.entry (packet q i.val j.val D) = residueBits ((F.modular.matrix q i j).coeff D) := by
  change a.entry (packet q i.val j.val D) = residueBits
    (((Macaulay.matrix (Macaulay.deformation (F.source.polynomial (pairFst q))
      (MacaulayBits.Degrees F.source.layout (pairFst q)))
      (MacaulayBits.Degrees F.source.layout (pairFst q)) (F.source.layout.width (pairFst q)) i j).map
        (Int.castRingHom (ZMod (Nat.fromBitsLE (pairSnd q) + 1)))).coeff D)
  rw [Access.entry, originalQuery_packet]
  have hs := MacaulayBits.entry_packet F.source.layout a.original.coefficient q (F.source.polynomial (pairFst q))
    (a.original.coefficient_eq q) i j
  rw [hs, finish_packet, Polynomial.coeff_map, Macaulay.matrix_deformation_coefficient]
  congr 1
  split_ifs <;> simp_all [Matrix.one_apply, Fin.ext_iff]

noncomputable def Access.modular {F : Family} (a : Access F) : BerkowitzPolynomial.ModularAccess F.modular where
  dimension := MacaulayBits.dimensionCode F.source.layout ∘ pairFst
  modulus := BinaryNat.succ ∘ pairSnd
  degree := a.degree ∘ pairFst
  entry := a.entry
  dimension_eq := fun q => FixedWidthPolynomial.countCode_code F.source.layout.arity F.source.layout.width (pairFst q)
  modulus_eq := fun q => by simp only [Function.comp_apply, BinaryNat.succ_eq_bits]; rfl
  degree_eq := fun q => a.degree_eq (pairFst q)
  entry_eq := a.entry_correct

theorem Access.modular_controls {F : Family} (a : Access F) (h : F.source.layout.PolyTime)
    (hd : a.degree ∈ FP) : a.modular.ControlsPolyTime := by
  have hn := mem_FP_comp pairFst_mem_FP (MacaulayBits.dimensionCode_mem_FP h)
  have hm := mem_FP_comp pairSnd_mem_FP BinaryNat.succ_mem_FP
  have ht := mem_FP_comp pairFst_mem_FP hd
  constructor
  · simpa only [Access.modular] using hn
  · simpa only [Access.modular] using hm
  · simpa only [Access.modular] using ht

noncomputable def Access.modularEntryEvaluator {F : Family} (a : Access F) (h : F.source.layout.PolyTime)
    (E : SpaceFunction a.original.coefficient) : SpaceFunction a.modular.entry := by
  have ES := a.entryEvaluator h E
  simpa only [Access.modular] using ES

noncomputable def Access.evaluator {F : Family} (a : Access F) (h : F.source.layout.PolyTime)
    (hd : a.degree ∈ FP) (E : SpaceFunction a.original.coefficient) : SpaceFunction F.value :=
  BerkowitzPolynomial.ModularAccess.evaluator a.modular (a.modular_controls h hd) (a.modularEntryEvaluator h E)

theorem Family.value_eq (F : Family) (q : List Bool) : F.value q =
    residueBits ((F.coefficient (pairFst q) : ℤ) : ZMod (Nat.fromBitsLE (pairSnd q) + 1)) := by
  have hdet : (F.modular.matrix q).det =
      (F.polynomial (pairFst q)).map (Int.castRingHom (ZMod (Nat.fromBitsLE (pairSnd q) + 1))) :=
    ((Polynomial.mapRingHom (Int.castRingHom (ZMod (Nat.fromBitsLE (pairSnd q) + 1)))).map_det _).symm
  have hc := congrArg (fun p : Polynomial (ZMod (Nat.fromBitsLE (pairSnd q) + 1)) => residueBits (p.coeff (F.degree (pairFst q)))) hdet
  rw [Polynomial.coeff_map] at hc
  exact hc

theorem Family.value_packet (F : Family) (c : List Bool) (m : ℕ) (hm : 0 < m) :
    F.value (pair c (BinaryNatCode.encode (m - 1))) = BinaryNatCode.encode ((F.coefficient c : ZMod m).val) := by
  rw [F.value_eq, pairFst_pair, pairSnd_pair, MacaulayBits.fromBits_encode,
    Nat.sub_add_cancel (by omega : 1 ≤ m)]
  rfl

end LeanCanny.Algebra.MacaulayDeformationBits
