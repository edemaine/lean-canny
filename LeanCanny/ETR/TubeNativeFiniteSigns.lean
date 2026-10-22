/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeInactiveFiniteSigns

/-! # Native finite-root testing of complete regular tube samples

The actual regular equations and inactive strict inequalities share one native
variable list. Their streamed readers combine without materializing either
polynomial family. Original univariate residues and degree/mass upper bounds
suffice for polynomial-space feasibility.
-/

@[expose] public section
namespace LeanCanny.ETR.TubeNativeFiniteSigns
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open TubeLevelPacket TubeEncoding
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeRegularSource.polynomial

variable (packet mask : List Bool → List Bool)

noncomputable abbrev arity : List Bool → ℕ := TubeRegularFiniteSigns.arity (pairFst ∘ packet)

noncomputable def source : FiniteLeafSignBits.Source (arity packet) :=
  (TubeRegularFiniteSigns.source (pairFst ∘ packet) mask).append
    (TubeInactiveFiniteSigns.nativeSource packet mask)

noncomputable def access (hp : packet ∈ FP) (hm : mask ∈ FP) : (source packet mask).Access :=
  (TubeRegularFiniteSigns.access (pairFst ∘ packet) mask (mem_FP_comp hp pairFst_mem_FP) hm).append
    (TubeInactiveFiniteSigns.nativeAccess packet mask hp hm)

/-- Regular equations and inactive strict inequalities in the same coordinates. -/
noncomputable def satisfies (c : List Bool) (z : Fin (arity packet c) → ℝ) : Prop :=
  (∀ j, (TubeRegularSource.polynomial (pairFst (packet c))
    (activeSet (TubeIndexed.arity (pairFst (packet c))) (mask c)) j).eval₂ (Int.castRingHom ℝ)
      (fun i => z (TubeHomogenization.outputEquiv (pairFst (packet c)) i)) = 0) ∧
  ∀ i, i ∉ activeSet (TubeIndexed.arity (pairFst (packet c))) (mask c) →
    0 < Geometry.PolynomialPerturbation.parameterMap (CompactSource.polynomial (pairFst (packet c)))
      (epsilon (packet c) : ℝ) (Geometry.TubePolynomial.splitPoint
        (fun i => z (TubeHomogenization.outputEquiv (pairFst (packet c)) (some (.inl (.inl i)))))) i

theorem allSigns_iff (c : List Bool) (z : Fin (arity packet c) → ℝ) :
    (∀ j : Fin ((source packet mask).count c),
      SignType.sign (((source packet mask).polynomial c j.val).eval₂ (Int.castRingHom ℝ) z) =
        (source packet mask).pattern c j.val) ↔ satisfies packet mask c z := by
  have H := FiniteLeafSignBits.Source.append_all_iff
    (TubeRegularFiniteSigns.source (pairFst ∘ packet) mask)
    (TubeInactiveFiniteSigns.nativeSource packet mask) c
    (fun p s => SignType.sign (p.eval₂ (Int.castRingHom ℝ) z) = s)
  refine H.trans ?_
  have hr : (∀ j : Fin ((TubeRegularFiniteSigns.source (pairFst ∘ packet) mask).count c),
      SignType.sign (((TubeRegularFiniteSigns.source (pairFst ∘ packet) mask).polynomial c j.val).eval₂
        (Int.castRingHom ℝ) z) = (TubeRegularFiniteSigns.source (pairFst ∘ packet) mask).pattern c j.val) ↔
      ∀ j, (TubeRegularSource.polynomial (pairFst (packet c))
        (activeSet (TubeIndexed.arity (pairFst (packet c))) (mask c)) j).eval₂ (Int.castRingHom ℝ)
          (fun i => z (TubeHomogenization.outputEquiv (pairFst (packet c)) i)) = 0 := by
    refine Iff.trans ?_ (TubeRegularFiniteSigns.all_rows_iff (pairFst ∘ packet) mask c (Int.castRingHom ℝ) z)
    apply forall_congr'
    intro j
    exact sign_eq_zero_iff
  have hi := TubeInactiveFiniteSigns.native_allSigns_iff packet mask c z
  have hi' := and_congr hr hi
  simpa only [satisfies, inactiveSigns, TubeInactiveFiniteSigns.native_samplePoint] using hi'

noncomputable def language (B : SeparableBits.Family) : Language :=
  FiniteLeafSignBits.finiteSignLanguage B (arity packet) (source packet mask)

theorem language_iff (B : SeparableBits.Family) (c : List Bool) :
    c ∈ language packet mask B ↔ ∃ z : Fin (arity packet c) → ℝ,
      (∀ i, (B.polynomial (pair c (BinaryNatCode.encode i.val))).eval₂ (Int.castRingHom ℝ) (z i) = 0) ∧
        satisfies packet mask c z := by
  apply exists_congr
  intro z
  exact and_congr_right (fun _ => allSigns_iff packet mask c z)

theorem language_mem_PSPACE_from_residues (B : SeparableBits.Family) (D b : List Bool → ℕ)
    (hne : ∀ c i, i < arity packet c → B.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0)
    (hdegree : ∀ c i, i < arity packet c → (B.polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ D c)
    (hmass : ∀ c i, i < arity packet c → coefficientMass (B.polynomial (pair c (BinaryNatCode.encode i))) ≤ 2 ^ b c)
    (hp : packet ∈ FP) (hm : mask ∈ FP) (hD : BinaryFn D) (hb : BinaryFn b)
    (E : SpaceFunction (PrimitivePairBits.coefficient B.polynomial)) : language packet mask B ∈ PSPACE :=
  FiniteLeafSignBits.finiteSignLanguage_mem_PSPACE_from_residues B (arity packet) D b hne hdegree hmass
    (source packet mask) (access packet mask hp hm)
    (TubeRegularFiniteSigns.arity_unary _ (mem_FP_comp hp pairFst_mem_FP)) hD hb E

end LeanCanny.ETR.TubeNativeFiniteSigns
