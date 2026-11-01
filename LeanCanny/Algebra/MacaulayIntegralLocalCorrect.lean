/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayIntegralEntryRequest

/-! # One current coefficient reply suffices for an actual Macaulay entry

The reference coefficient function is built mathematically from the given
polynomials. It receives no computation or space certificate. A controller
observes it only at its single guarded query, so equality of that current
reply supplies the actual matrix-entry proof.
-/

@[expose] public section
namespace LeanCanny.Algebra.MacaulayIntegralLocalCorrect
open LeanCanny.Encoding LeanCanny.Computation MatrixPower MacaulayFullBoxBits
open scoped Classical

noncomputable def coefficient {A : Type*} [CommRing A] (L : Layout) (q : List Bool)
    (p : Fin (L.arity q) → MvPolynomial (Fin (L.arity q)) A) (enc : A → List Bool) (z : List Bool) : List Bool :=
  if H : Nat.fromBitsLE (idx z) < L.arity q then
    enc ((p ⟨Nat.fromBitsLE (idx z), H⟩).coeff
      (RationalSubstitution.Indexed.exponentVector (L.arity q)
        (FixedWidthPolynomial.entry (L.width q) (Nat.fromBitsLE (shift z))))) else []

theorem coefficient_packet {A : Type*} [CommRing A] (L : Layout) (q : List Bool)
    (p : Fin (L.arity q) → MvPolynomial (Fin (L.arity q)) A) (enc : A → List Bool)
    (i : Fin (L.arity q)) (k r t : ℕ) :
    coefficient L q p enc (entryPacket q i.val k r t) =
      enc ((p i).coeff (RationalSubstitution.Indexed.exponentVector (L.arity q) (FixedWidthPolynomial.entry (L.width q) k))) := by
  simp only [coefficient, idx_entryPacket, shift_entryPacket, BinaryNatCode.encode, Nat.fromBitsLE_bits, i.isLt, dite_eq_left]

theorem observe (P : SingleCall.Program) (reply reference : List Bool → List Bool) (q : List Bool)
    (h : P.request q = true → reply (P.query q) = reference (P.query q)) : P.value reply q = P.value reference q := by
  unfold SingleCall.Program.value
  by_cases HR : P.request q = true
  · rw [ite_eq_left HR, ite_eq_left HR, h HR]
  · rw [ite_eq_right HR, ite_eq_right HR]

theorem actual_value {A : Type*} [CommRing A] {M : ℕ} (basis : Module.Basis (Fin M) ℤ A)
    (L : Layout) (reply : List Bool → List Bool) (q : List Bool)
    (p : Fin (L.arity q) → MvPolynomial (Fin (L.arity q)) A)
    (hlevel : L.level q = Macaulay.level (fun i : Fin (L.arity q) => L.degree q i.val))
    (m : List Bool → ℕ) (hm : 0 < m q) (r t : Fin M)
    (a : MacaulayFullBox.Row (L.arity q) (L.width q)) (b : MacaulayFullBox.Column (L.arity q) (L.width q))
    (h : MacaulayIntegralEntryRequest.request L (entryPacket q (rowNumber _ _ a) b.val r.val t.val) →
      reply (MacaulayIntegralEntryRequest.query L (entryPacket q (rowNumber _ _ a) b.val r.val t.val)) =
        coefficient L q p (fun z => residueBits ((Algebra.leftMulMatrix basis z r t : ℤ) : ZMod (m q)))
          (MacaulayIntegralEntryRequest.query L (entryPacket q (rowNumber _ _ a) b.val r.val t.val))) :
    (MacaulayIntegralEntryRequest.program L m).value reply (entryPacket q (rowNumber _ _ a) b.val r.val t.val) =
      residueBits ((Algebra.leftMulMatrix basis (MacaulayFullBox.matrix p (fun i => L.degree q i.val) (L.width q) a b) r t : ℤ) : ZMod (m q)) := by
  let ref := coefficient L q p (fun z => residueBits ((Algebra.leftMulMatrix basis z r t : ℤ) : ZMod (m q)))
  have HE : (MacaulayIntegralEntryRequest.program L m).value reply (entryPacket q (rowNumber _ _ a) b.val r.val t.val) =
      (MacaulayIntegralEntryRequest.program L m).value ref (entryPacket q (rowNumber _ _ a) b.val r.val t.val) :=
    observe _ reply ref _ (fun H => h (of_decide_eq_true H))
  exact HE.trans (MacaulayIntegralEntryRequest.actual_value basis L m ref q p hlevel hm r t
    (fun i k => coefficient_packet L q p _ i k r.val t.val) a b)

end LeanCanny.Algebra.MacaulayIntegralLocalCorrect
