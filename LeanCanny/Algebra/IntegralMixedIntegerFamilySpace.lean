/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedIntegerProducerSpaceLeaf
public import LeanCanny.Algebra.IntegralMixedNormalizedCompanionSource
/-! # Original integer companions over any retained mixed prefix

The integer polynomial is an original source leaf indexed by the saved key.
Exact degree and coefficient residues are charged Space readers. Arbitrary old
coefficient algebras contribute their scalar identity matrices, not a supplied
prefix evaluator. The inherited row/column convention is modulo the rank.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedIntegerFamilyBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
open scoped Classical

noncomputable def family (P : Parameters) (F : Family) (p : List Bool → Polynomial ℤ) :
    PaddedIntegralGeneratorFinBits.Family where
  arity q := F.birth (IntegralMixedVirtualTaskBits.saved P q)
  width q := F.width (IntegralMixedVirtualTaskBits.saved P q)
  carrier q := (F.state (IntegralMixedVirtualTaskBits.saved P q)).sampler.scalarPrefix.carrier
  ring q := (F.state (IntegralMixedVirtualTaskBits.saved P q)).sampler.scalarPrefix.ring
  nontrivial q := (F.state (IntegralMixedVirtualTaskBits.saved P q)).sampler.scalarPrefix.nontrivial
  basis q := (F.state (IntegralMixedVirtualTaskBits.saved P q)).sampler.scalarPrefix.basis
  polynomial q := (p (IntegralMixedVirtualTaskBits.saved P q)).map (Int.castRingHom _)
  degree q := (p (IntegralMixedVirtualTaskBits.saved P q)).natDegree
  modulus := modulus P
  modulus_ne_zero := modulus_ne_zero P
  row q := ⟨get P .row q%IntegralMixedNormalizedCompanionBits.newRank P F q,
    Nat.mod_lt _ (IntegralMixedNormalizedCompanionBits.newRank_pos P F q)⟩
  col q := ⟨get P .col q%IntegralMixedNormalizedCompanionBits.newRank P F q,
    Nat.mod_lt _ (IntegralMixedNormalizedCompanionBits.newRank_pos P F q)⟩

noncomputable def taskPolynomial (P : Parameters) (p : List Bool → Polynomial ℤ) (q : List Bool) :=
  p (IntegralMixedVirtualTaskBits.saved P q)
noncomputable def degreeWord (P : Parameters) (p : List Bool → Polynomial ℤ) (q : List Bool) :=
  BinaryNatCode.encode (taskPolynomial P p q).natDegree

structure Original (P : Parameters) (p : List Bool → Polynomial ℤ) : Prop where
  degree : SpaceFunction (degreeWord P p)
  coefficient : SpaceFunction (PrimitivePairBits.coefficient (taskPolynomial P p))

def oldRank (P : Parameters) (F : Family) (q : List Bool) :=
  count (F.birth (IntegralMixedVirtualTaskBits.saved P q)) (F.width (IntegralMixedVirtualTaskBits.saved P q))

theorem oldRank_binary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : BinaryFn (oldRank P F) :=
  BinaryFn.of_bits (mem_FP_of_eq (countCode_mem_FP (h.birth.comp (IntegralMixedVirtualTaskBits.saved_FP P a))
    (h.width.comp (IntegralMixedVirtualTaskBits.saved_FP P a))) (fun q => countCode_code _ _ q))

theorem newRank_binary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    BinaryFn (IntegralMixedNormalizedCompanionBits.newRank P F) :=
  BinaryFn.of_bits (mem_FP_of_eq (countCode_mem_FP
    ((h.birth.comp (IntegralMixedVirtualTaskBits.saved_FP P a)).add (UnaryFn.const 1))
    (h.width.comp (IntegralMixedVirtualTaskBits.saved_FP P a))) (fun q => countCode_code _ _ q))

theorem controls (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (p : List Bool → Polynomial ℤ) :
    IntegralIntegerCompanionBits.Controls (family P F p) where
  width := h.width.comp (IntegralMixedVirtualTaskBits.saved_FP P a)
  modulus := modulus_binary P a
  row := (get_binary P a .row).mod (newRank_binary P a F h)
  col := (get_binary P a .col).mod (newRank_binary P a F h)

noncomputable def companionValue (P : Parameters) (F : Family) (p : List Bool → Polynomial ℤ) : List Bool → List Bool :=
  (family P F p).value
noncomputable def leadingValue (P : Parameters) (p : List Bool → Polynomial ℤ) (q : List Bool) :=
  residueBits ((taskPolynomial P p q).leadingCoeff : ZMod (modulus P q))
noncomputable def rawScalar (P : Parameters) (p : List Bool → Polynomial ℤ) (q : List Bool) :=
  residueBits ((taskPolynomial P p q).coeff (get P .coefficient q) : ZMod (modulus P q))
noncomputable def coefficientValue (P : Parameters) (F : Family) (p : List Bool → Polynomial ℤ) (q : List Bool) :=
  if get P .row q%oldRank P F q=get P .col q%oldRank P F q then rawScalar P p q else []

theorem companion_evaluator (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (p : List Bool → Polynomial ℤ) (hp : Original P p) : SpaceFunction (companionValue P F p) :=
  IntegralIntegerCompanionBits.evaluator (family P F p) (taskPolynomial P p)
    (fun _ => rfl) (fun _ => rfl) (controls P a F h p) (degreeWord P p) hp.degree (fun _ => rfl) hp.coefficient

theorem leading_evaluator (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (p : List Bool → Polynomial ℤ) (hp : Original P p) : SpaceFunction (leadingValue P p) := by
  have E := IntegralIntegerCompanionBits.leading_evaluator (family P F p) (taskPolynomial P p)
    (controls P a F h p) (degreeWord P p) hp.degree hp.coefficient
  refine E.congr (funext fun q => ?_)
  exact IntegralIntegerCompanionBits.leadingReader_eq (family P F p) (taskPolynomial P p)
    (fun _ => rfl) (degreeWord P p) (fun _ => rfl) q

theorem raw_evaluator (P : Parameters) (a : Access P) (p : List Bool → Polynomial ℤ) (hp : Original P p) :
    SpaceFunction (rawScalar P p) := by
  refine (hp.coefficient.precompose (IntegralMixedIntegerProducerSpaceBits.coefficientPacket P)
    (IntegralMixedIntegerProducerSpaceBits.coefficientPacket_FP P a)).congr (funext fun q => ?_)
  exact IntegerPolynomialRootQueriesBits.coefficient_packet (taskPolynomial P p) q (get P .coefficient q)
    (modulus P q) (Nat.pos_of_ne_zero (modulus_ne_zero P q))

theorem coefficient_evaluator (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (p : List Bool → Polynomial ℤ) (hp : Original P p) : SpaceFunction (coefficientValue P F p) := by
  have H := ((get_binary P a .row).mod (oldRank_binary P a F h)).eq
    ((get_binary P a .col).mod (oldRank_binary P a F h))
  exact (SpaceFunction.branch _ H.flag_mem_FP (raw_evaluator P a p hp)
    (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr
    (funext fun q => by simp only [coefficientValue,decide_eq_true_eq])

end LeanCanny.Algebra.IntegralMixedIntegerFamilyBits
