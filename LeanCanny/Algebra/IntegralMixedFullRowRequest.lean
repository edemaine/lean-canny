/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedFullRowIdentity
public import LeanCanny.Algebra.ModularAddFP
public import LeanCanny.Algebra.ModularNatMulFP
public import LeanCanny.Computation.TwoCallController

/-! # Two current lower replies restore an actual full original row

The lower task supplies the actual frozen-low or gradient-low coefficient
at the guarded repacked target. The scalar task supplies `a*Q^D` for the
equation and `a*Q^D*D` for a derivative. All combination arithmetic and
monomial tests are native FP. No source coefficient or scalar evaluator
is assumed by the local certificates.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullRowRequest
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedCutSource
open IntegralMixedVirtualSweepSource IntegralMixedVirtualNativeBits IntegralMixedFullRowMultiplier
open scoped Classical
attribute [local irreducible] BinaryNat.mulMod ArithmeticBits.addMod

noncomputable def post (F : Family) (I : Indices F) (W : List Bool → ℕ) (z : List Bool) : List Bool :=
  ArithmeticBits.addMod (pair (BinaryNatCode.encode (I.modulus (pairFst z)))
    (pair (if lowFits F I W (pairFst z) then pairFst (pairSnd z) else [])
      (BinaryNat.mulMod (pair (BinaryNatCode.encode (I.modulus (pairFst z)))
        (pair (pairSnd (pairSnd z)) (BinaryNatCode.encode (multiplier F I W (pairFst z))))))))

theorem post_FP (F : Family) (I : Indices F) (W : List Bool → ℕ) (h : Metadata F I) (hW : UnaryFn W) : post F I W ∈ FP := by
  have HM : BinaryFn (fun z => I.modulus (pairFst z)) := h.modulus.comp pairFst_mem_FP
  have HK : BinaryFn (fun z => multiplier F I W (pairFst z)) := (multiplier_binary F I W h hW).comp pairFst_mem_FP
  have HL : (fun z => if lowFits F I W (pairFst z) then pairFst (pairSnd z) else []) ∈ FP :=
    ((lowFits_FP F I W h hW).comp pairFst_mem_FP).ite_mem_FP
      (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) (constFn_mem_FP [])
  have HS : (fun z => BinaryNat.mulMod (pair (BinaryNatCode.encode (I.modulus (pairFst z)))
      (pair (pairSnd (pairSnd z)) (BinaryNatCode.encode (multiplier F I W (pairFst z)))))) ∈ FP :=
    mem_FP_comp (mem_FP_pair HM.bits_mem_FP (mem_FP_pair (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
      HK.bits_mem_FP)) BinaryNat.mulMod_mem_FP
  exact mem_FP_comp (mem_FP_pair HM.bits_mem_FP (mem_FP_pair HL HS)) ArithmeticBits.addMod_mem_FP

noncomputable def program (F : Family) (I : Indices F) (W : List Bool → ℕ)
    (lowTask scalarTask : List Bool → List Bool) : RecursiveFold.Program :=
  TwoCall.program lowTask scalarTask (post F I W)

theorem certificates (F : Family) (I : Indices F) (W : List Bool → ℕ) (h : Metadata F I) (hW : UnaryFn W)
    (lowTask scalarTask : List Bool → List Bool) (hl : lowTask ∈ FP) (hs : scalarTask ∈ FP) :
    (program F I W lowTask scalarTask).controller.Certificates
      (encQ := Turing.MultiTapeTM.encBits) (encS := RecursiveFold.encState) :=
  TwoCall.certificates _ _ _ hl hs (post_FP F I W h hW)

theorem post_packet (F : Family) (I : Indices F) (W : List Bool → ℕ) (q : List Bool)
    (x s : ZMod (I.modulus q)) :
    post F I W (pair q (pair (residueBits x) (residueBits s))) =
      residueBits ((if lowFits F I W q then x else 0) + s * (multiplier F I W q : ZMod (I.modulus q))) := by
  let : NeZero (I.modulus q) := ⟨I.modulus_ne_zero q⟩
  simp only [post, pairFst_pair, pairSnd_pair]
  rw [ArithmeticBits.mulMod_nat_residueBits]
  by_cases HF : lowFits F I W q
  · simp only [HF, ite_true]
    exact ArithmeticBits.addMod_residueBits _ _ _
  · simp only [HF, ite_false]
    simpa only [residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits] using
      ArithmeticBits.addMod_residueBits (I.modulus q) 0 (s * (multiplier F I W q : ZMod (I.modulus q)))

theorem value_at (F : Family) (I : Indices F) (W : List Bool → ℕ)
    (lowTask scalarTask reply : List Bool → List Bool) (q : List Bool)
    (hl : reply (lowTask q) = residueBits ((Algebra.leftMulMatrix
      (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
      ((low F I q).coeff (nativeExponent (Equiv.refl (Fin (free F q))) (canonicalWidth F q) (lowTarget F I W q)))
        (I.row q) (I.col q) : ℤ) : ZMod (I.modulus q)))
    (hs : reply (scalarTask q) = residueBits (scalar F I q : ZMod (I.modulus q))) :
    (program F I W lowTask scalarTask).value reply q = residueBits ((Algebra.leftMulMatrix
      (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
      ((IntegralMixedVirtualOriginalRows.row F q (I.coordinate q)).coeff (exponent F I W q))
        (I.row q) (I.col q) : ℤ) : ZMod (I.modulus q)) := by
  rw [program, TwoCall.value_eq, hl, hs, post_packet]
  let x : ℤ := Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
    ((low F I q).coeff (nativeExponent (Equiv.refl (Fin (free F q))) (canonicalWidth F q) (lowTarget F I W q)))
      (I.row q) (I.col q)
  have HM : (if lowFits F I W q then (x : ZMod (I.modulus q)) else 0) =
      ((if lowFits F I W q then x else 0 : ℤ) : ZMod (I.modulus q)) := by
    split_ifs <;> simp only [Int.cast_zero]
  rw [HM, ← Int.cast_natCast, ← Int.cast_mul, ← Int.cast_add,
    IntegralMixedFullRowIdentity.low_entry, ← IntegralMixedFullRowIdentity.row_entry]

theorem requests_iff (F : Family) (I : Indices F) (W : List Bool → ℕ)
    (lowTask scalarTask reply : List Bool → List Bool) (q child : List Bool) :
    (program F I W lowTask scalarTask).controller.Requests reply (fun _ => 2) q child ↔
      child = lowTask q ∨ child = scalarTask q := TwoCall.requests_iff _ _ _ _ _ _

noncomputable def lowValue (F : Family) (I : Indices F) (W : List Bool → ℕ) (q : List Bool) : List Bool :=
  residueBits ((Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
    ((low F I q).coeff (nativeExponent (Equiv.refl (Fin (free F q))) (canonicalWidth F q) (lowTarget F I W q)))
      (I.row q) (I.col q) : ℤ) : ZMod (I.modulus q))

def stateBound (F : Family) (I : Indices F) (q : List Bool) : ℕ :=
  2 * q.length + 2 * (Turing.MultiTapeTM.encNat 2).length + (I.modulus q).size + 2

theorem stateBound_unary (F : Family) (I : Indices F) (h : Metadata F I) : UnaryFn (stateBound F I) := by
  have HM : UnaryFn (fun q => (I.modulus q).size) :=
    (UnaryFn.length h.modulus.bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)
  exact ((((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add
    (UnaryFn.const (2 * (Turing.MultiTapeTM.encNat 2).length))).add HM).add (UnaryFn.const 2)

theorem state_length (F : Family) (I : Indices F) (W : List Bool → ℕ)
    (lowTask scalarTask reply : List Bool → List Bool) (q : List Bool)
    (hl : reply (lowTask q) = lowValue F I W q)
    (hs : reply (scalarTask q) = residueBits (scalar F I q : ZMod (I.modulus q))) (t : ℕ) :
    (RecursiveFold.encState (((program F I W lowTask scalarTask).controller.reference reply)^[t]
      ((program F I W lowTask scalarTask).initial q))).length ≤ stateBound F I q := by
  let : NeZero (I.modulus q) := ⟨I.modulus_ne_zero q⟩
  have HL : (reply (lowTask q)).length ≤ (I.modulus q).size := by
    rw [hl]
    exact residueBits_length_le (I.modulus q) _
  have HE := value_at F I W lowTask scalarTask reply q hl hs
  have HP := ((TwoCall.value_eq lowTask scalarTask (post F I W) reply q).symm).trans HE
  have HV : (post F I W (pair q (pair (reply (lowTask q)) (reply (scalarTask q))))).length ≤ (I.modulus q).size := by
    rw [HP]
    exact residueBits_length_le (I.modulus q) _
  have H := TwoCall.state_length lowTask scalarTask (post F I W) reply q t
  have HM := max_le HL HV
  exact H.trans (by dsimp only [stateBound]; omega)

end LeanCanny.Algebra.IntegralMixedFullRowRequest
