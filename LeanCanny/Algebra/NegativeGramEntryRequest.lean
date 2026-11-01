/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralBerkowitzBlockSource
public import LeanCanny.Algebra.ModularFoldRecursiveController
public import LeanCanny.Algebra.ModularNegFP
public import LeanCanny.Algebra.ModularPowFP
public import LeanCanny.Algebra.ProjectiveGramEliminant
public import LeanCanny.Computation.TwoCallController

/-! # Resumable integer entries of a negative Gram matrix

One term requests two actual rectangular-matrix entries and multiplies
their replies modulo the caller modulus. A binary-count fold sums these
negative products over the rectangular row and the intermediate integral
basis coordinate. No matrix-entry evaluator is part of the certificates.
-/

@[expose] public section
namespace LeanCanny.Algebra.NegativeGramEntryRequest
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
open scoped BigOperators
attribute [local irreducible] ArithmeticBits.negate BinaryNat.mulMod

structure Parameters where
  rows : List Bool → ℕ
  rank : List Bool → ℕ
  modulus : List Bool → ℕ

structure Controls (F : Parameters) where
  rows : BinaryFn F.rows
  rank : BinaryFn F.rank
  modulus : BinaryFn F.modulus

def original := IntegralBerkowitzBlockBits.original
def matrixRow (p : List Bool) : ℕ := Nat.fromBitsLE (pairFst (pairSnd p))
def matrixCol (p : List Bool) : ℕ := Nat.fromBitsLE (pairSnd (pairSnd p))
def basisRow (p : List Bool) : ℕ := Nat.fromBitsLE (IntegralBerkowitzBlockBits.basisRowCode p)
def basisCol (p : List Bool) : ℕ := Nat.fromBitsLE (IntegralBerkowitzBlockBits.basisColCode p)
def termIndex (p : List Bool) : ℕ := Nat.fromBitsLE (pairSnd p)
def sourceRow (F : Parameters) (p : List Bool) : ℕ := termIndex p / F.rank (original (pairFst p))
def middle (F : Parameters) (p : List Bool) : ℕ := termIndex p % F.rank (original (pairFst p))

def left (F : Parameters) (p : List Bool) : List Bool :=
  pair (IntegralBlockMomentBits.context (original (pairFst p)) (basisRow (pairFst p)) (middle F p))
    (pair (BinaryNatCode.encode (sourceRow F p)) (BinaryNatCode.encode (matrixRow (pairFst p))))

def right (F : Parameters) (p : List Bool) : List Bool :=
  pair (IntegralBlockMomentBits.context (original (pairFst p)) (middle F p) (basisCol (pairFst p)))
    (pair (BinaryNatCode.encode (sourceRow F p)) (BinaryNatCode.encode (matrixCol (pairFst p))))

theorem matrixRow_binary : BinaryFn matrixRow :=
  BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
theorem matrixCol_binary : BinaryFn matrixCol :=
  BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
theorem basisRow_binary : BinaryFn basisRow := BinaryFn.fromBits IntegralBerkowitzBlockBits.basisRowCode_FP
theorem basisCol_binary : BinaryFn basisCol := BinaryFn.fromBits IntegralBerkowitzBlockBits.basisColCode_FP
theorem termIndex_binary : BinaryFn termIndex := BinaryFn.fromBits pairSnd_mem_FP
theorem sourceRow_binary (F : Parameters) (a : Controls F) : BinaryFn (sourceRow F) :=
  termIndex_binary.div ((a.rank.comp IntegralBerkowitzBlockBits.original_FP).comp pairFst_mem_FP)
theorem middle_binary (F : Parameters) (a : Controls F) : BinaryFn (middle F) :=
  termIndex_binary.mod ((a.rank.comp IntegralBerkowitzBlockBits.original_FP).comp pairFst_mem_FP)

theorem left_FP (F : Parameters) (a : Controls F) : left F ∈ FP := by
  have HQ : (fun p => original (pairFst p)) ∈ FP :=
    mem_FP_comp pairFst_mem_FP IntegralBerkowitzBlockBits.original_FP
  have HR : BinaryFn (fun p => basisRow (pairFst p)) := basisRow_binary.comp pairFst_mem_FP
  have HI : BinaryFn (fun p => matrixRow (pairFst p)) := matrixRow_binary.comp pairFst_mem_FP
  exact mem_FP_pair
    (mem_FP_pair HQ (mem_FP_pair HR.bits_mem_FP
      (middle_binary F a).bits_mem_FP))
    (mem_FP_pair (sourceRow_binary F a).bits_mem_FP HI.bits_mem_FP)

theorem right_FP (F : Parameters) (a : Controls F) : right F ∈ FP := by
  have HQ : (fun p => original (pairFst p)) ∈ FP :=
    mem_FP_comp pairFst_mem_FP IntegralBerkowitzBlockBits.original_FP
  have HT : BinaryFn (fun p => basisCol (pairFst p)) := basisCol_binary.comp pairFst_mem_FP
  have HJ : BinaryFn (fun p => matrixCol (pairFst p)) := matrixCol_binary.comp pairFst_mem_FP
  exact mem_FP_pair
    (mem_FP_pair HQ (mem_FP_pair (middle_binary F a).bits_mem_FP
      HT.bits_mem_FP))
    (mem_FP_pair (sourceRow_binary F a).bits_mem_FP HJ.bits_mem_FP)

def post (F : Parameters) (z : List Bool) : List Bool :=
  let modulus := BinaryNatCode.encode (F.modulus (original (pairFst (pairFst z))))
  ArithmeticBits.negate (pair modulus
    (BinaryNat.mulMod (pair modulus (pairSnd z))))

theorem post_FP (F : Parameters) (a : Controls F) : post F ∈ FP := by
  have HMO : BinaryFn (fun p => F.modulus (original p)) := a.modulus.comp IntegralBerkowitzBlockBits.original_FP
  have HMB : BinaryFn (fun z => F.modulus (original (pairFst (pairFst z)))) :=
    HMO.comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  have HM := HMB.bits_mem_FP
  have HP : (fun z => BinaryNat.mulMod
      (pair (BinaryNatCode.encode (F.modulus (original (pairFst (pairFst z))))) (pairSnd z))) ∈ FP :=
    mem_FP_comp (mem_FP_pair HM pairSnd_mem_FP) BinaryNat.mulMod_mem_FP
  exact mem_FP_comp (mem_FP_pair HM HP) ArithmeticBits.negate_mem_FP

def termProgram (F : Parameters) : RecursiveFold.Program := TwoCall.program (left F) (right F) (post F)

theorem term_certificates (F : Parameters) (a : Controls F) :
    (termProgram F).controller.Certificates (encQ := encBits) (encS := RecursiveFold.encState) :=
  TwoCall.certificates _ _ _ (left_FP F a) (right_FP F a) (post_FP F a)

def count (F : Parameters) (p : List Bool) : ℕ := F.rows (original p) * F.rank (original p)
def modulus (F : Parameters) (p : List Bool) : List Bool := BinaryNatCode.encode (F.modulus (original p))
def sumProgram (F : Parameters) : RecursiveFold.Program :=
  ModularFold.RecursiveStage.sumProgram (count F) (modulus F) id

theorem count_binary (F : Parameters) (a : Controls F) : BinaryFn (count F) :=
  (a.rows.mul a.rank).comp IntegralBerkowitzBlockBits.original_FP
theorem modulus_FP (F : Parameters) (a : Controls F) : modulus F ∈ FP :=
  (show BinaryFn (fun p => F.modulus (original p)) from
    a.modulus.comp IntegralBerkowitzBlockBits.original_FP).bits_mem_FP
theorem sum_certificates (F : Parameters) (a : Controls F) :
    (sumProgram F).controller.Certificates (encQ := encBits) (encS := RecursiveFold.encState) :=
  ModularFold.RecursiveStage.sum_certificates _ _ _ (count_binary F a) (modulus_FP F a) id_mem_FP

theorem post_packet (F : Parameters) (p : List Bool) [NeZero (F.modulus (original (pairFst p)))]
    (x y : ZMod (F.modulus (original (pairFst p)))) :
    post F (pair p (pair (residueBits x) (residueBits y))) = residueBits (-(x * y)) := by
  simp only [post, pairFst_pair, pairSnd_pair]
  rw [ArithmeticBits.mulMod_residueBits, ArithmeticBits.negate_residueBits]

theorem term_value (F : Parameters) (reply : List Bool → List Bool) (p : List Bool)
    [NeZero (F.modulus (original (pairFst p)))]
    (x y : ZMod (F.modulus (original (pairFst p))))
    (hx : reply (left F p) = residueBits x) (hy : reply (right F p) = residueBits y) :
    (termProgram F).value reply p = residueBits (-(x * y)) := by
  rw [termProgram, TwoCall.value_eq, hx, hy, post_packet]

theorem term_requests (F : Parameters) (reply : List Bool → List Bool) (p child : List Bool) :
    (termProgram F).controller.Requests reply (fun _ => 2) p child ↔
      child = left F p ∨ child = right F p := TwoCall.requests_iff _ _ _ _ _ _

theorem left_original (F : Parameters) (p : List Bool) :
    original (left F p) = original (pairFst p) := by
  simp only [left, original, IntegralBerkowitzBlockBits.original, IntegralBlockMomentBits.context, pairFst_pair]

theorem right_original (F : Parameters) (p : List Bool) :
    original (right F p) = original (pairFst p) := by
  simp only [right, original, IntegralBerkowitzBlockBits.original, IntegralBlockMomentBits.context, pairFst_pair]

theorem left_packet (F : Parameters) (c : List Bool) (r t i j k : ℕ) :
    left F (pair (pair (IntegralBlockMomentBits.context c r t)
      (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j))) (BinaryNatCode.encode k)) =
      pair (IntegralBlockMomentBits.context c r (k % F.rank c))
        (pair (BinaryNatCode.encode (k / F.rank c)) (BinaryNatCode.encode i)) := by
  simp only [left, sourceRow, middle, termIndex, original, IntegralBerkowitzBlockBits.original,
    basisRow, IntegralBerkowitzBlockBits.basisRowCode, matrixRow, IntegralBlockMomentBits.context,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem right_packet (F : Parameters) (c : List Bool) (r t i j k : ℕ) :
    right F (pair (pair (IntegralBlockMomentBits.context c r t)
      (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j))) (BinaryNatCode.encode k)) =
      pair (IntegralBlockMomentBits.context c (k % F.rank c) t)
        (pair (BinaryNatCode.encode (k / F.rank c)) (BinaryNatCode.encode j)) := by
  simp only [right, sourceRow, middle, termIndex, original, IntegralBerkowitzBlockBits.original,
    basisCol, IntegralBerkowitzBlockBits.basisColCode, matrixCol, IntegralBlockMomentBits.context,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem term_packet (F : Parameters) (reply : List Bool → List Bool) (c : List Bool)
    [NeZero (F.modulus c)] (r t i j k : ℕ) (x y : ZMod (F.modulus c))
    (hx : reply (pair (IntegralBlockMomentBits.context c r (k % F.rank c))
      (pair (BinaryNatCode.encode (k / F.rank c)) (BinaryNatCode.encode i))) = residueBits x)
    (hy : reply (pair (IntegralBlockMomentBits.context c (k % F.rank c) t)
      (pair (BinaryNatCode.encode (k / F.rank c)) (BinaryNatCode.encode j))) = residueBits y) :
    (termProgram F).value reply (pair (pair (IntegralBlockMomentBits.context c r t)
      (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j))) (BinaryNatCode.encode k)) =
        residueBits (-(x * y)) := by
  rw [termProgram, TwoCall.value_eq, left_packet, right_packet, hx, hy]
  simp only [post, original, IntegralBerkowitzBlockBits.original, IntegralBlockMomentBits.context,
    pairFst_pair, pairSnd_pair]
  rw [ArithmeticBits.mulMod_residueBits, ArithmeticBits.negate_residueBits]

theorem term_integer_packet (F : Parameters) (reply : List Bool → List Bool) (c : List Bool)
    [NeZero (F.modulus c)] (r t i j k : ℕ) (x y : ℤ)
    (hx : reply (pair (IntegralBlockMomentBits.context c r (k % F.rank c))
      (pair (BinaryNatCode.encode (k / F.rank c)) (BinaryNatCode.encode i))) =
        residueBits (x : ZMod (F.modulus c)))
    (hy : reply (pair (IntegralBlockMomentBits.context c (k % F.rank c) t)
      (pair (BinaryNatCode.encode (k / F.rank c)) (BinaryNatCode.encode j))) =
        residueBits (y : ZMod (F.modulus c))) :
    (termProgram F).value reply (pair (pair (IntegralBlockMomentBits.context c r t)
      (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j))) (BinaryNatCode.encode k)) =
        residueBits ((-(x * y) : ℤ) : ZMod (F.modulus c)) := by
  rw [term_packet F reply c r t i j k (x : ZMod (F.modulus c)) (y : ZMod (F.modulus c)) hx hy,
    Int.cast_neg, Int.cast_mul]

theorem partial_value (F : Parameters) (reply : List Bool → List Bool) (p : List Bool)
    (a : ℕ → ZMod (F.modulus (original p))) (hpos : 0 < F.modulus (original p))
    (ha : ∀ k < count F p, reply (pair p (BinaryNatCode.encode k)) = residueBits (a k))
    (k : ℕ) (hk : k ≤ count F p) :
    (sumProgram F).partialValue reply p k = residueBits (∑ i ∈ Finset.range k, a i) :=
  ModularFold.RecursiveStage.sum_partialValueWithModulus (count F) (modulus F) id reply
    (fun q => F.modulus (original q)) (funext (fun _ => Nat.fromBitsLE_bits _)) p a hpos ha k hk

theorem sum_requests (F : Parameters) (reply : List Bool → List Bool) (p child : List Bool) :
    (sumProgram F).controller.Requests reply (count F) p child ↔
      ∃ k < count F p, child = pair p (BinaryNatCode.encode k) :=
  (sumProgram F).requests_iff reply p child

def stateBound (F : Parameters) (p : List Bool) : ℕ :=
  2 * p.length + 2 * (count F p).size + (F.modulus (original p)).size + 2

theorem stateBound_unary (F : Parameters) (a : Controls F) : UnaryFn (stateBound F) := by
  have HC : UnaryFn (fun p => (count F p).size) :=
    (UnaryFn.length (count_binary F a).bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)
  have HM : UnaryFn (fun p => (F.modulus (original p)).size) :=
    (UnaryFn.length (show BinaryFn (fun p => F.modulus (original p)) from
      a.modulus.comp IntegralBerkowitzBlockBits.original_FP).bits_mem_FP).of_eq
      (fun _ => BinaryNatCode.length_encode _)
  exact ((((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add ((UnaryFn.const 2).mul HC)).add HM).add
    (UnaryFn.const 2)

theorem state_length (F : Parameters) (reply : List Bool → List Bool) (p : List Bool)
    (a : ℕ → ZMod (F.modulus (original p))) (hpos : 0 < F.modulus (original p))
    (ha : ∀ k < count F p, reply (pair p (BinaryNatCode.encode k)) = residueBits (a k)) (t : ℕ) :
    (RecursiveFold.encState (((sumProgram F).controller.reference reply)^[t]
      ((sumProgram F).initial p))).length ≤ stateBound F p := by
  have HB : (RecursiveFold.encState (((sumProgram F).controller.reference reply)^[t]
      ((sumProgram F).initial p))).length ≤
      2 * p.length + 2 * (Turing.MultiTapeTM.encNat (count F p)).length + (modulus F p).length + 2 := by
    apply (sumProgram F).orbit_length
    intro k hk
    rw [partial_value F reply p a hpos ha k hk]
    let : NeZero (F.modulus (original p)) := ⟨hpos.ne'⟩
    rw [modulus, BinaryNatCode.length_encode]
    exact residueBits_length_le (F.modulus (original p)) _
  change _ ≤ 2 * p.length + 2 * (count F p).bits.length + (modulus F p).length + 2 at HB
  simpa only [stateBound, modulus, BinaryNatCode.length_encode, ← Nat.size_eq_bits_len] using HB

/-- Exact flattening of the rectangular row and the intermediate basis index. -/
theorem matrix_entry {A : Type*} [CommRing A] {L C M : ℕ}
    (b : Module.Basis (Fin M) ℤ A) (T : Matrix (Fin L) (Fin C) A)
    (i j : Fin C) (r t : Fin M) :
    Algebra.leftMulMatrix b (-ProjectiveGramEliminant.gram T i j) r t =
      ∑ k : Fin (L * M), -(Algebra.leftMulMatrix b (T k.divNat i) r k.modNat *
        Algebra.leftMulMatrix b (T k.divNat j) k.modNat t) := by
  rw [map_neg, Matrix.neg_apply, ProjectiveGramEliminant.gram, Matrix.mul_apply,
    map_sum, Matrix.sum_apply]
  simp_rw [Matrix.transpose_apply, map_mul, Matrix.mul_apply]
  rw [← Finset.sum_neg_distrib]
  simp_rw [← Finset.sum_neg_distrib]
  calc
    _ = ∑ k : Fin L × Fin M, -(Algebra.leftMulMatrix b (T k.1 i) r k.2 *
        Algebra.leftMulMatrix b (T k.1 j) k.2 t) := (Fintype.sum_prod_type _).symm
    _ = _ := by
      apply Fintype.sum_equiv finProdFinEquiv
      intro k
      have H := finProdFinEquiv.symm_apply_apply k
      have H₁ := congrArg Prod.fst H
      have H₂ := congrArg Prod.snd H
      change (finProdFinEquiv k).divNat = k.1 at H₁
      change (finProdFinEquiv k).modNat = k.2 at H₂
      rw [H₁, H₂]

/-- Only the replies to this fold's bounded term requests are used. -/
theorem actual_value {A : Type*} [CommRing A] {L C M : ℕ}
    (b : Module.Basis (Fin M) ℤ A) (T : Matrix (Fin L) (Fin C) A)
    (F : Parameters) (reply : List Bool → List Bool) (p : List Bool)
    (i j : Fin C) (r t : Fin M) (hc : count F p = L * M)
    (hpos : 0 < F.modulus (original p))
    (ha : ∀ k : Fin (L * M), reply (pair p (BinaryNatCode.encode k.val)) =
      residueBits ((-(Algebra.leftMulMatrix b (T k.divNat i) r k.modNat *
        Algebra.leftMulMatrix b (T k.divNat j) k.modNat t) : ℤ) : ZMod (F.modulus (original p)))) :
    (sumProgram F).value reply p =
      residueBits ((Algebra.leftMulMatrix b (-ProjectiveGramEliminant.gram T i j) r t : ℤ) :
        ZMod (F.modulus (original p))) := by
  let a (k : ℕ) : ZMod (F.modulus (original p)) :=
    if hk : k < L * M then
      ((-(Algebra.leftMulMatrix b (T (Fin.divNat ⟨k, hk⟩) i) r (Fin.modNat ⟨k, hk⟩) *
        Algebra.leftMulMatrix b (T (Fin.divNat ⟨k, hk⟩) j) (Fin.modNat ⟨k, hk⟩) t) : ℤ) :
          ZMod (F.modulus (original p))) else 0
  have HA (k : ℕ) (hk : k < count F p) :
      reply (pair p (BinaryNatCode.encode k)) = residueBits (a k) := by
    have HK : k < L * M := hc ▸ hk
    simpa only [a, dite_eq_left HK] using ha ⟨k, HK⟩
  have H := partial_value F reply p a hpos HA (count F p) le_rfl
  change (sumProgram F).value reply p = _ at H
  rw [H, matrix_entry, Int.cast_sum, hc, ← Fin.sum_univ_eq_sum_range]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simp only [a, dite_eq_left k.isLt]

end LeanCanny.Algebra.NegativeGramEntryRequest
