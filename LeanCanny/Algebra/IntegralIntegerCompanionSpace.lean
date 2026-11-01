/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralIntegerCompanionQueries
/-! # Charged local space leaves for integer companion births

Exact degree and original integer coefficients may require polynomial
space. The original integer leading coefficient is read at that exact
degree, without a modular inverse or an FP leading premise.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralIntegerCompanionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
set_option backward.isDefEq.respectTransparency false
universe u

theorem evaluator (F : PaddedIntegralGeneratorFinBits.Family.{u}) (p : List Bool → Polynomial ℤ)
    (hp : ∀ q, letI := F.ring q; F.polynomial q = (p q).map (Int.castRingHom (F.carrier q)))
    (hd : ∀ q, F.degree q = (p q).natDegree) (a : Controls F)
    (degree : List Bool → List Bool) (ED : SpaceFunction degree)
    (hdegree : ∀ q, degree q = BinaryNatCode.encode (F.degree q))
    (EC : SpaceFunction (PrimitivePairBits.coefficient p)) : SpaceFunction F.value := by
  have E := IntegralScalarSpaceDegreeBits.actual_evaluator (scalarFamily F p hp hd) (native F p hp hd a)
    degree (entry F p) (leadingReader F p degree) ED (entry_evaluator F p a EC) (leading_evaluator F p a degree ED EC)
    hdegree (entry_packet F p hp) (leadingReader_eq F p hd degree hdegree)
  exact E.congr (PaddedIntegralGeneratorFinBits.value_eq F)

noncomputable def leaf (F : PaddedIntegralGeneratorFinBits.Family.{u}) : SingleCall.Program where
  request _ := false
  query := id
  immediate := F.value
  finish := pairSnd

theorem leaf_value (F : PaddedIntegralGeneratorFinBits.Family.{u}) (answer : List Bool → List Bool) (q : List Bool) :
    (leaf F).value answer q = F.value q := rfl

theorem leaf_certificates (F : PaddedIntegralGeneratorFinBits.Family.{u}) (p : List Bool → Polynomial ℤ)
    (hp : ∀ q, letI := F.ring q; F.polynomial q = (p q).map (Int.castRingHom (F.carrier q)))
    (hd : ∀ q, F.degree q = (p q).natDegree) (a : Controls F)
    (degree : List Bool → List Bool) (ED : SpaceFunction degree)
    (hdegree : ∀ q, degree q = BinaryNatCode.encode (F.degree q))
    (EC : SpaceFunction (PrimitivePairBits.coefficient p)) :
    (leaf F).controller.Certificates (encQ := encBits) (encS := SingleCall.encState) :=
  (leaf F).certificates_of_space (constFn_mem_FP [false]) id_mem_FP (evaluator F p hp hd a degree ED hdegree EC).computable
    ((SpaceFunction.ofFP _ pairSnd_mem_FP).computable)
end LeanCanny.Algebra.IntegralIntegerCompanionBits
