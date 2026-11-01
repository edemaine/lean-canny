/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueMacaulayEntry

/-! # Actual negative Gram entries from mapped system coefficient replies

The native Macaulay selector, two-reply product and modular sum compose to
the literal negative double-nilpotent Gram source entry. The only semantic
reply hypothesis is for mapped system coefficients at this source. Neither
Macaulay-entry nor Gram-entry correctness is supplied by the caller.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueGramFromRows
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedCutSource IntegralMixedVirtualSweepSource
open IntegralMixedValueGramEntry
open scoped Classical
attribute [local irreducible] IntegralMixedValueDoubleNilpotent.basis

def rectangularPacket (p : List Bool) : List Bool :=
  pair (NegativeGramEntryRequest.original p)
    (pair (pairFst (pairSnd p)) (pair (pairSnd (pairSnd p))
      (pair (IntegralBerkowitzBlockBits.basisRowCode p) (IntegralBerkowitzBlockBits.basisColCode p))))

theorem rectangularPacket_FP : rectangularPacket ∈ FP :=
  mem_FP_pair IntegralBerkowitzBlockBits.original_FP
    (mem_FP_pair (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
      (mem_FP_pair (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
        (mem_FP_pair IntegralBerkowitzBlockBits.basisRowCode_FP IntegralBerkowitzBlockBits.basisColCode_FP)))

theorem rectangularPacket_packet (c : List Bool) (a b r t : ℕ) :
    rectangularPacket (pair (IntegralBlockMomentBits.context c r t)
      (pair (BinaryNatCode.encode a) (BinaryNatCode.encode b))) = MacaulayFullBoxBits.entryPacket c a b r t := by
  simp only [rectangularPacket, NegativeGramEntryRequest.original, IntegralBerkowitzBlockBits.original,
    IntegralBlockMomentBits.context, IntegralBerkowitzBlockBits.basisRowCode,
    IntegralBerkowitzBlockBits.basisColCode, pairFst_pair, pairSnd_pair, MacaulayFullBoxBits.entryPacket]

noncomputable def rowReply (F : Family) (I : Indices F) (coefficient : List Bool → List Bool) (p : List Bool) : List Bool :=
  (IntegralMixedValueMacaulayEntry.program F I).value coefficient (rectangularPacket p)

noncomputable def termReply (F : Family) (I : Indices F) (coefficient : List Bool → List Bool) : List Bool → List Bool :=
  (termProgram F I).value (rowReply F I coefficient)

noncomputable def value (F : Family) (I : Indices F) (coefficient : List Bool → List Bool) : List Bool → List Bool :=
  (sumProgram F I).value (termReply F I coefficient)

theorem rowNumber_symm (n W : ℕ) (a : Fin ((n + 1) * count n W)) :
    MacaulayFullBoxBits.rowNumber n W ((rowEquiv n W).symm a) = a.val := by
  rw [MacaulayFullBoxBits.rowNumber_eq]
  change (rowEquiv n W ((rowEquiv n W).symm a)).val = a.val
  rw [Equiv.apply_symm_apply]

theorem row_value (F : Family) (I : Indices F) (coefficient : List Bool → List Bool) (q : List Bool)
    (ha : ∀ (j : Fin ((IntegralMixedValueMacaulayEntry.layout F).arity q)) k
      (r t : Fin (count (F.birth q + 2) (F.width q))), coefficient
      (pair q (pair (BinaryNatCode.encode j.val) (pair (BinaryNatCode.encode k)
        (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val))))) =
      residueBits ((Algebra.leftMulMatrix (IntegralMixedValueDoubleNilpotent.basis (F.state q))
        ((IntegralMixedValueDoubleSystem.mappedSystem F q (I.coordinate q) j).coeff
          (RationalSubstitution.Indexed.exponentVector ((IntegralMixedValueMacaulayEntry.layout F).arity q)
            (entry ((IntegralMixedValueMacaulayEntry.layout F).width q) k))) r t : ℤ) : ZMod (I.modulus q)))
    (a : Fin ((parameters F I).rows q))
    (b : Fin (count (F.ambient q - (F.rule q).critical.offset.val + 1 + 1)
      (IntegralMixedGridValue.width (F.spatial q) (F.rule q))))
    (r t : Fin (count (F.birth q + 2) (F.width q))) :
    rowReply F I coefficient (pair (IntegralBlockMomentBits.context q r.val t.val)
      (pair (BinaryNatCode.encode a.val) (BinaryNatCode.encode b.val))) =
      residueBits ((Algebra.leftMulMatrix (IntegralMixedValueDoubleNilpotent.basis (F.state q))
        (rectangular F I q a b) r t : ℤ) : ZMod (I.modulus q)) := by
  rw [rowReply, rectangularPacket_packet]
  have H := IntegralMixedValueMacaulayEntry.entry_value F I coefficient q r t (fun j k => ha j k r t)
    ((rowEquiv _ _).symm a) b
  have HN := rowNumber_symm ((IntegralMixedValueMacaulayEntry.layout F).arity q)
    ((IntegralMixedValueMacaulayEntry.layout F).width q) a
  have HP := congrArg (fun number : ℕ => (IntegralMixedValueMacaulayEntry.program F I).value coefficient
    (MacaulayFullBoxBits.entryPacket q number b.val r.val t.val)) HN
  exact HP.symm.trans H

theorem entry_value (F : Family) (I : Indices F)
    (index : ∀ q, Fin (IntegralMixedValueTrailing.ChoiceBound (F.spatial q) (F.rule q)))
    (coefficient : List Bool → List Bool) (q : List Bool)
    (ha : ∀ (j : Fin ((IntegralMixedValueMacaulayEntry.layout F).arity q)) k
      (r t : Fin (count (F.birth q + 2) (F.width q))), coefficient
      (pair q (pair (BinaryNatCode.encode j.val) (pair (BinaryNatCode.encode k)
        (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val))))) =
      residueBits ((Algebra.leftMulMatrix (IntegralMixedValueDoubleNilpotent.basis (F.state q))
        ((IntegralMixedValueDoubleSystem.mappedSystem F q (I.coordinate q) j).coeff
          (RationalSubstitution.Indexed.exponentVector ((IntegralMixedValueMacaulayEntry.layout F).arity q)
            (entry ((IntegralMixedValueMacaulayEntry.layout F).width q) k))) r t : ℤ) : ZMod (I.modulus q)))
    (i j : Fin ((IntegralMixedValueDeterminantSource.source F I index).dimension q))
    (r t : Fin (count (F.birth q + 2) (F.width q))) :
    value F I coefficient (pair (IntegralBlockMomentBits.context q r.val t.val)
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      residueBits (((IntegralMixedValueDeterminantSource.source F I index).entryMatrix q i j r t : ℤ) :
        ZMod (I.modulus q)) := by
  apply IntegralMixedValueGramEntry.entry_value
  intro k
  let : NeZero ((parameters F I).modulus q) := ⟨I.modulus_ne_zero q⟩
  have HL := row_value F I coefficient q ha k.divNat i r k.modNat
  have HR := row_value F I coefficient q ha k.divNat j k.modNat t
  let x : ℤ := Algebra.leftMulMatrix (IntegralMixedValueDoubleNilpotent.basis (F.state q))
    (rectangular F I q k.divNat i) r k.modNat
  let y : ℤ := Algebra.leftMulMatrix (IntegralMixedValueDoubleNilpotent.basis (F.state q))
    (rectangular F I q k.divNat j) k.modNat t
  have HM : (parameters F I).modulus q = I.modulus q := rfl
  have HL' := HL.trans (congrArg (fun m : ℕ => residueBits (x : ZMod m)) HM.symm)
  have HR' := HR.trans (congrArg (fun m : ℕ => residueBits (y : ZMod m)) HM.symm)
  have H := NegativeGramEntryRequest.term_integer_packet (parameters F I) (rowReply F I coefficient) q
    r.val t.val i.val j.val k.val
    x y HL' HR'
  exact H.trans (congrArg (fun m : ℕ => residueBits ((-(x * y) : ℤ) : ZMod m)) HM)

end LeanCanny.Algebra.IntegralMixedValueGramFromRows
