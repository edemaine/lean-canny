/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralScalarSpaceDegreeNative
/-! # Companion entries with charged exact-degree and leading computations

Exact degree, original coefficient, and leading-scalar readers may use
polynomial space. All query construction and modular postprocessing is
native FP on their returned words. This is a local evaluator, with no
recursive controller request depending on the exact degree.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralScalarSpaceDegreeBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralScalarGeneratorBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def value (F : Family) (degree entry leading : List Bool → List Bool) (q : List Bool) : List Bool :=
  finish F (pair (pair (pair q (degree q)) (entry (coefficientQuery F (pair q (degree q))))) (leading q))

theorem evaluator (F : Family) (a : Native F) (degree entry leading : List Bool → List Bool)
    (ED : SpaceFunction degree) (EC : SpaceFunction entry) (EL : SpaceFunction leading) :
    SpaceFunction (value F degree entry leading) := by
  have EQ := ED.withInput
  have EE := EQ.chain (EC.precompose (coefficientQuery F) (coefficientQuery_FP F a))
  exact ((EQ.pairOutputs EE).pairOutputs EL).postcompose (finish F) (finish_FP F a)

attribute [local irreducible] viewValue

theorem finish_packet (F : Family) (q : List Bool) (D : ℕ) (coefficient leading : List Bool) :
    finish F (pair (pair (pair q (BinaryNatCode.encode D)) coefficient) leading) =
      viewValue (F.modulus q) (F.scalarDegree q) D (F.row q).val (F.col q).val (F.oldRow q).val (F.oldCol q).val
        (Nat.fromBitsLE leading : ZMod (F.modulus q)) coefficient := by
  unfold finish
  rw [show original (pair (pair (pair q (BinaryNatCode.encode D)) coefficient) leading) = q from by simp [original],
    show degreeWord (pair (pair (pair q (BinaryNatCode.encode D)) coefficient) leading) = BinaryNatCode.encode D from by simp [degreeWord],
    show coefficientWord (pair (pair (pair q (BinaryNatCode.encode D)) coefficient) leading) = coefficient from by simp [coefficientWord],
    show leadingWord (pair (pair (pair q (BinaryNatCode.encode D)) coefficient) leading) = leading from by simp [leadingWord],
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rfl

theorem coefficientQuery_packet (F : Family) (q : List Bool) :
    coefficientQuery F (pair q (BinaryNatCode.encode (F.selectedDegree q))) = IntegralScalarGeneratorBits.coefficientQuery F q := by
  unfold coefficientQuery
  rw [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rfl

theorem value_eq (F : Family) (degree entry leading : List Bool → List Bool)
    (hd : ∀ q, degree q = BinaryNatCode.encode (F.selectedDegree q))
    (hc : ∀ q k (r t : Fin (F.width q)),
      entry (pair q (pair (BinaryNatCode.encode k) (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) =
        residueBits (F.coefficient q k r t))
    (hl : ∀ q, leading q = residueBits (F.leading q)) (q : List Bool) :
    value F degree entry leading q = F.toFamily.value q := by
  unfold value
  rw [hd q, hl q, finish_packet, coefficientQuery_packet]
  let : NeZero (F.modulus q) := ⟨F.modulus_ne_zero q⟩
  have HL : (Nat.fromBitsLE (residueBits (F.leading q)) : ZMod (F.modulus q)) = F.leading q := by
    simp only [residueBits, BinaryNatCode.encode, Nat.fromBitsLE_bits, ZMod.natCast_zmod_val]
  rw [HL]
  have HV := IntegralScalarGeneratorBits.program_view F id entry q
  simp only [id_eq] at HV
  rw [← HV]
  apply IntegralScalarGeneratorBits.program_value F id entry
  intro c _
  exact hc c _ _ _

theorem actual_evaluator (F : Family) (a : Native F) (degree entry leading : List Bool → List Bool)
    (ED : SpaceFunction degree) (EC : SpaceFunction entry) (EL : SpaceFunction leading)
    (hd : ∀ q, degree q = BinaryNatCode.encode (F.selectedDegree q))
    (hc : ∀ q k (r t : Fin (F.width q)),
      entry (pair q (pair (BinaryNatCode.encode k) (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) =
        residueBits (F.coefficient q k r t))
    (hl : ∀ q, leading q = residueBits (F.leading q)) : SpaceFunction F.toFamily.value :=
  (evaluator F a degree entry leading ED EC EL).congr (funext (value_eq F degree entry leading hd hc hl))
end LeanCanny.Algebra.IntegralScalarSpaceDegreeBits
