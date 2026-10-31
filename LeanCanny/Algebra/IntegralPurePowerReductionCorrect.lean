/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralPurePowerReductionSource

/-! # Correctness of relative reduction entries from original lower coefficients -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralPurePowerReductionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralPurePowerActionBits (Source reductionSource)
open IntegralBerkowitzBlockBits (original basisRowCode basisColCode)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem residue_cast_congr {m n : ℕ} (h : m = n) (z : ℤ) :
    residueBits (z : ZMod m) = residueBits (z : ZMod n) := by subst n; rfl

noncomputable def coefficientHom {A : Type*} [CommRing A] {M : ℕ}
    (b : Module.Basis (Fin M) ℤ A) (r t : Fin M) : A →+ ℤ where
  toFun x := Algebra.leftMulMatrix b x r t
  map_zero' := by simp only [map_zero, Matrix.zero_apply]
  map_add' x y := by simp only [map_add, Matrix.add_apply]

theorem coefficientHom_int {A : Type*} [CommRing A] {M : ℕ}
    (b : Module.Basis (Fin M) ℤ A) (r t : Fin M) (z : ℤ) :
    coefficientHom b r t (z : A) = if r = t then z else 0 := by
  change Algebra.leftMulMatrix b (z : A) r t = _
  rw [map_intCast, Matrix.intCast_apply]
  simp only [Int.cast_id]

theorem lowQuery_packet (q : List Bool) (i k : ℕ) :
    lowQuery (PurePowerReductionBits.packet q i k) =
      pair (pairFst q) (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k)) := by
  simp only [lowQuery, PurePowerReductionBits.packet, pairFst_pair, pairSnd_pair]

theorem native_entry_eq (S : Source) (a : Access S) (q : List Bool)
    (r t : Fin (S.rank (original q)))
    (HQ : pairFst q = IntegralBlockMomentBits.context (original q) r.val t.val)
    (HM : Nat.fromBitsLE (pairSnd q) + 1 = S.modulus (original q))
    (i j : Fin (FixedWidthPolynomial.count (S.layout.arity (original q)) (S.layout.width (original q)))) :
    letI := S.ring (original q)
    PurePowerReductionBits.entry (layout S) (fun z => S.layout.bound (pairFst z))
      (constant a) (a.low ∘ lowQuery) (PurePowerReductionBits.packet q j.val i.val) =
      residueBits ((Algebra.leftMulMatrix (S.basis (original q))
        (PurePowerReductionMatrix.matrix (S.layout.coordinate (original q))
          (fun l => S.layout.degree (original q) l.val) (S.low (original q))
          (S.leading (original q) : S.carrier (original q)) (S.layout.bound (original q)) i j) r t : ℤ) :
        ZMod (S.modulus (original q))) := by
  let := S.ring (original q)
  let f := coefficientHom (S.basis (original q)) r t
  have HR : Nat.fromBitsLE (basisRowCode q) = r.val := by
    have H := congrArg (fun z => Nat.fromBitsLE (pairFst (pairSnd z))) HQ
    simpa only [basisRowCode, IntegralBlockMomentBits.context, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits] using H
  have HT : Nat.fromBitsLE (basisColCode q) = t.val := by
    have H := congrArg (fun z => Nat.fromBitsLE (pairSnd (pairSnd z))) HQ
    simpa only [basisColCode, IntegralBlockMomentBits.context, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits] using H
  have HC : constant a q = residueBits
      (f (S.leading (original q) : S.carrier (original q)) : ZMod (Nat.fromBitsLE (pairSnd q) + 1)) := by
    have H : constant a q = residueBits
        (f (S.leading (original q) : S.carrier (original q)) : ZMod (S.modulus (original q))) := by
      rw [constant, HR, HT]
      change (if r.val = t.val then a.leading (original q) else []) =
        residueBits ((coefficientHom (S.basis (original q)) r t (S.leading (original q))) : ZMod (S.modulus (original q)))
      rw [coefficientHom_int]
      by_cases he : r = t
      · rw [ite_eq_left (congrArg Fin.val he), ite_eq_left he, a.leading_eq]
      · have hne : r.val ≠ t.val := fun h => he (Fin.ext h)
        rw [ite_eq_right hne, ite_eq_right he]
        simp only [Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits]
    exact H.trans (residue_cast_congr HM.symm _)
  have HL : ∀ (l : Fin (S.layout.arity (original q))) (k : ℕ),
      (a.low ∘ lowQuery) (PurePowerReductionBits.packet q l.val k) =
        residueBits (f ((S.low (original q) l).coeff
          (RationalSubstitution.Indexed.exponentVector (S.layout.arity (original q))
            (FixedWidthPolynomial.entry (S.layout.width (original q)) k))) : ZMod (Nat.fromBitsLE (pairSnd q) + 1)) := by
    intro l k
    have HP : lowQuery (PurePowerReductionBits.packet q l.val k) =
        pair (IntegralBlockMomentBits.context (original q) r.val t.val)
          (pair (BinaryNatCode.encode l.val) (BinaryNatCode.encode k)) :=
      (lowQuery_packet q l.val k).trans (congrArg (fun z => pair z (pair (BinaryNatCode.encode l.val) (BinaryNatCode.encode k))) HQ)
    rw [Function.comp_apply, HP, a.low_eq]
    exact residue_cast_congr HM.symm _
  have H := PurePowerReductionBits.entry_packet_coefficient (layout S)
    (fun z => S.layout.bound (pairFst z)) (constant a) (a.low ∘ lowQuery) q f (S.low (original q))
    (S.leading (original q) : S.carrier (original q)) (S.layout.coordinate (original q)) HC HL j i
  exact H.trans (residue_cast_congr HM _)

attribute [local irreducible] PurePowerReductionMatrix.matrix

theorem entry_correct (S : Source) (a : Access S) (c : List Bool)
    (i j : Fin ((reductionSource S).dimension c)) (r t : Fin (S.rank c)) :
    entryProgram S a (IntegralReductionActionBits.packet c i.val j.val r.val t.val) =
      residueBits ((((reductionSource S).toSource.entryMatrix c i j r t) : ℤ) : ZMod (S.modulus c)) := by
  rw [entryProgram, Function.comp_apply, writer_packet]
  generalize hz : pair (IntegralBlockMomentBits.context c r.val t.val)
    (BinaryNatCode.encode (S.modulus c - 1)) = q
  have ho : original q = c := by
    rw [original, ← hz]
    simp only [IntegralBlockMomentBits.context, pairFst_pair]
  have HQ : pairFst q = IntegralBlockMomentBits.context c r.val t.val := by rw [← hz, pairFst_pair]
  have HM : Nat.fromBitsLE (pairSnd q) + 1 = S.modulus c := by
    rw [← hz, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    have := S.modulus_ne_zero c
    omega
  subst c
  exact native_entry_eq S a q r t HQ HM i j

end LeanCanny.Algebra.IntegralPurePowerReductionBits
