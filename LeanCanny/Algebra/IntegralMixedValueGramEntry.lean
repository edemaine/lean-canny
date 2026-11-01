/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.NegativeGramEntryRequest
public import LeanCanny.Algebra.IntegralMixedValueDoubleSystem
public import LeanCanny.Algebra.IntegralMixedValueDeterminantMetadata

/-! # Native negative-Gram folds for the actual relative value source

The rectangular matrix here is the literal double-nilpotent mapped
Macaulay system. The row enumeration changes no entries. The native term
and sum controllers carry two virtual digits at the same physical birth;
their certificates charge all requested rectangular entries separately.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueGramEntry
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedCutSource
open IntegralMixedVirtualSweepSource IntegralMixedVirtualNativeBits
open scoped Classical BigOperators
attribute [local irreducible] IntegralMixedValueDoubleNilpotent.basis IntegralMixedValueDoubleNilpotent.matrix

def rowEquiv (n W : ℕ) : MacaulayFullBox.Row n W ≃ Fin ((n + 1) * count n W) :=
  ((Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin (count n W)))).trans finSumFinEquiv).trans
    (finCongr (by ring))

noncomputable def rectangular (F : Family) (I : Indices F) (q : List Bool) :=
  fun a c => MacaulayFullBox.matrix (IntegralMixedValueDoubleSystem.mappedSystem F q (I.coordinate q))
    (RelativeProjectiveValueGram.degrees
      (fun _ => IntegralMixedCoordinateSquarefree.coordinateDegree (F.spatial q) (F.rule q))
        (F.spatial q).degree)
    (IntegralMixedGridValue.width (F.spatial q) (F.rule q)) ((rowEquiv _ _).symm a) c

theorem gram_reindex {A : Type*} [CommRing A] {n W : ℕ}
    (T : Matrix (MacaulayFullBox.Row n W) (MacaulayFullBox.Column n W) A) :
    ProjectiveGramEliminant.gram (fun a c => T ((rowEquiv n W).symm a) c) =
      ProjectiveGramEliminant.gram T := by
  funext i j
  simp only [ProjectiveGramEliminant.gram, Matrix.mul_apply, Matrix.transpose_apply]
  exact Fintype.sum_equiv (rowEquiv n W).symm _ _ (fun _ => rfl)

noncomputable def parameters (F : Family) (I : Indices F) : NegativeGramEntryRequest.Parameters where
  rows q := (F.ambient q - (F.rule q).critical.offset.val + 1 + 2) *
    count (F.ambient q - (F.rule q).critical.offset.val + 1 + 1)
      (IntegralMixedGridValue.width (F.spatial q) (F.rule q))
  rank q := count (F.birth q + 2) (F.width q)
  modulus := I.modulus

theorem controls (F : Family) (I : Indices F) (h : Metadata F I) :
    NegativeGramEntryRequest.Controls (parameters F I) where
  rows := ((BinaryFn.ofUnary (free_unary F I h)).add (BinaryFn.const 2)).mul
    (IntegralMixedValueDeterminantMetadata.columns_binary F I h)
  rank := ((BinaryFn.const 2).powUnary h.width).powUnary (h.birth.add (UnaryFn.const 2))
  modulus := h.modulus

noncomputable abbrev termProgram (F : Family) (I : Indices F) :=
  NegativeGramEntryRequest.termProgram (parameters F I)
noncomputable abbrev sumProgram (F : Family) (I : Indices F) :=
  NegativeGramEntryRequest.sumProgram (parameters F I)

theorem term_certificates (F : Family) (I : Indices F) (h : Metadata F I) :
    (termProgram F I).controller.Certificates
      (encQ := Turing.MultiTapeTM.encBits) (encS := RecursiveFold.encState) :=
  NegativeGramEntryRequest.term_certificates _ (controls F I h)

theorem sum_certificates (F : Family) (I : Indices F) (h : Metadata F I) :
    (sumProgram F I).controller.Certificates
      (encQ := Turing.MultiTapeTM.encBits) (encS := RecursiveFold.encState) :=
  NegativeGramEntryRequest.sum_certificates _ (controls F I h)

theorem source_entry (F : Family) (I : Indices F)
    (index : ∀ q, Fin (IntegralMixedValueTrailing.ChoiceBound (F.spatial q) (F.rule q)))
    (q : List Bool) (i j : Fin ((IntegralMixedValueDeterminantSource.source F I index).dimension q))
    (r t : Fin (count (F.birth q + 2) (F.width q))) :
    (IntegralMixedValueDeterminantSource.source F I index).entryMatrix q i j r t =
      Algebra.leftMulMatrix (IntegralMixedValueDoubleNilpotent.basis (F.state q))
        (-ProjectiveGramEliminant.gram (rectangular F I q) i j) r t := by
  let read (a : IntegralMixedValueDoubleNilpotent.Second (F.state q)) : ℤ :=
    Algebra.leftMulMatrix (IntegralMixedValueDoubleNilpotent.basis (F.state q)) a r t
  have HS : (IntegralMixedValueDeterminantSource.source F I index).entryMatrix q i j r t =
      read (-(IntegralMixedValueDoubleNilpotent.matrix
        (F.state q) (F.birth_bound q) (F.rule q) (I.coordinate q)) i j) := rfl
  rw [HS]
  have HM := (IntegralMixedValueDoubleSystem.matrix_eq F q (I.coordinate q)).trans
    (gram_reindex (MacaulayFullBox.matrix (IntegralMixedValueDoubleSystem.mappedSystem F q (I.coordinate q))
      (RelativeProjectiveValueGram.degrees
        (fun _ => IntegralMixedCoordinateSquarefree.coordinateDegree (F.spatial q) (F.rule q))
          (F.spatial q).degree)
        (IntegralMixedGridValue.width (F.spatial q) (F.rule q)))).symm
  exact congrArg (fun M => read (-M i j)) HM

/-- The lower answers are exactly this entry's finite product requests. -/
theorem entry_value (F : Family) (I : Indices F)
    (index : ∀ q, Fin (IntegralMixedValueTrailing.ChoiceBound (F.spatial q) (F.rule q)))
    (reply : List Bool → List Bool) (q : List Bool)
    (i j : Fin ((IntegralMixedValueDeterminantSource.source F I index).dimension q))
    (r t : Fin (count (F.birth q + 2) (F.width q))) :
    let p := pair (IntegralBlockMomentBits.context q r.val t.val)
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))
    (∀ k : Fin ((parameters F I).rows q * (parameters F I).rank q),
      reply (pair p (BinaryNatCode.encode k.val)) = residueBits
        ((-(Algebra.leftMulMatrix (IntegralMixedValueDoubleNilpotent.basis (F.state q))
            (rectangular F I q k.divNat i) r k.modNat *
          Algebra.leftMulMatrix (IntegralMixedValueDoubleNilpotent.basis (F.state q))
            (rectangular F I q k.divNat j) k.modNat t) : ℤ) : ZMod (I.modulus q))) →
    (sumProgram F I).value reply p =
      residueBits (((IntegralMixedValueDeterminantSource.source F I index).entryMatrix q i j r t : ℤ) :
        ZMod (I.modulus q)) := by
  dsimp only
  intro ha
  rw [source_entry]
  let p := pair (IntegralBlockMomentBits.context q r.val t.val)
    (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))
  have HO : NegativeGramEntryRequest.original p = q := by
    simp only [p, NegativeGramEntryRequest.original, IntegralBerkowitzBlockBits.original,
      IntegralBlockMomentBits.context, pairFst_pair]
  have HC : NegativeGramEntryRequest.count (parameters F I) p =
      (parameters F I).rows q * (parameters F I).rank q := by
    rw [NegativeGramEntryRequest.count, HO]
  have HP : 0 < (parameters F I).modulus (NegativeGramEntryRequest.original p) := by
    rw [HO]
    exact Nat.pos_of_ne_zero (I.modulus_ne_zero q)
  have E := NegativeGramEntryRequest.actual_value (IntegralMixedValueDoubleNilpotent.basis (F.state q))
    (rectangular F I q) (parameters F I) reply p i j r t HC HP
  rw [HO] at E
  exact E ha

end LeanCanny.Algebra.IntegralMixedValueGramEntry
