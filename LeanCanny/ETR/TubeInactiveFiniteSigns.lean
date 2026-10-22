/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FiniteLeafSignMask
public import LeanCanny.Algebra.FiniteLeafSignEmbedding
public import LeanCanny.ETR.TubeFiniteLeafSigns
public import LeanCanny.ETR.TubeRegularFiniteSigns
public import LeanCanny.ETR.TubeLevelCoordinates

/-! # Native streamed inactive tube inequalities

Active rows are replaced by the constant one; every inactive row requests a
positive sign of the actual integer tube constraint. The mask is read at a
bounded binary row index, including on malformed inputs.
-/

@[expose] public section
namespace LeanCanny.ETR.TubeInactiveFiniteSigns
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open TubeLevelPacket TubeEncoding
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
attribute [local irreducible] RationalSubstitutionBits.compiledTerm

variable (packet mask : List Bool → List Bool)

noncomputable def skip (c : List Bool) (j : ℕ) : Prop :=
  (mask c)[min j (constraintCount (TubeIndexed.arity (pairFst (packet c))) - 1)]?.getD false = true

theorem skip_pred (hp : packet ∈ FP) (hm : mask ∈ FP) :
    FPPred (FiniteLeafSignBits.rowPredicate (skip packet mask)) := by
  have hc := (TubeZero.constraintCount_unary (TubeSampleCoefficient.n_unary packet hp)).sub (UnaryFn.const 1)
  have hi := UnaryFn.fromBitsLE_min pairSnd_mem_FP (hc.comp pairFst_mem_FP)
  have H := FPPred.getBit (mem_FP_comp pairFst_mem_FP hm) hi
  exact H.of_iff (fun _ => Iff.rfl)

noncomputable def source : FiniteLeafSignBits.Source (TubeSampleCoefficient.A packet) :=
  (TubeFiniteLeafSigns.source packet (fun _ _ => .pos)).ignore (skip packet mask)

noncomputable def access (hp : packet ∈ FP) (hm : mask ∈ FP) : (source packet mask).Access :=
  (TubeFiniteLeafSigns.access packet (fun _ _ => .pos) hp
    (fun _ => InfinitesimalSign.encode .pos) (constFn_mem_FP _) (fun _ _ => rfl)).ignore
      (skip packet mask) (skip_pred packet mask hp hm)

theorem skip_constraint (c : List Bool) (i : PerturbedSource.Index (pairFst (packet c))) :
    skip packet mask c (constraintEquiv (TubeIndexed.arity (pairFst (packet c))) i).val ↔
      i ∈ activeSet (TubeIndexed.arity (pairFst (packet c))) (mask c) := by
  have hi : (constraintEquiv (TubeIndexed.arity (pairFst (packet c))) i).val ≤
      constraintCount (TubeIndexed.arity (pairFst (packet c))) - 1 :=
    Nat.le_pred_of_lt (constraintEquiv (TubeIndexed.arity (pairFst (packet c))) i).isLt
  unfold skip
  rw [min_eq_left hi]
  simp only [TubeEncoding.activeSet, Finset.mem_filter, Finset.mem_univ, true_and]

theorem rowSign_iff (c : List Bool) (i : PerturbedSource.Index (pairFst (packet c)))
    (z : Fin (TubeSampleCoefficient.A packet c) → ℝ) :
    SignType.sign (((source packet mask).polynomial c
      (constraintEquiv (TubeIndexed.arity (pairFst (packet c))) i).val).eval₂ (Int.castRingHom ℝ) z) =
        (source packet mask).pattern c (constraintEquiv (TubeIndexed.arity (pairFst (packet c))) i).val ↔
    (i ∉ activeSet (TubeIndexed.arity (pairFst (packet c))) (mask c) →
      0 < Geometry.PolynomialPerturbation.parameterMap (CompactSource.polynomial (pairFst (packet c)))
        (epsilon (packet c) : ℝ) (Geometry.TubePolynomial.splitPoint (samplePoint (packet c) z)) i) := by
  have hs := skip_constraint packet mask c i
  have hpat : (source packet mask).pattern c (constraintEquiv (TubeIndexed.arity (pairFst (packet c))) i).val = .pos := by
    change (if skip packet mask c (constraintEquiv (TubeIndexed.arity (pairFst (packet c))) i).val then SignType.pos else SignType.pos) = SignType.pos
    split_ifs <;> rfl
  rw [hpat]
  change SignType.sign ((((TubeFiniteLeafSigns.source packet (fun _ _ => .pos)).ignore (skip packet mask)).polynomial c
    (constraintEquiv (TubeIndexed.arity (pairFst (packet c))) i).val).eval₂ (Int.castRingHom ℝ) z) = .pos ↔ _
  rw [FiniteLeafSignBits.Source.ignore_polynomial]
  by_cases hi : i ∈ activeSet (TubeIndexed.arity (pairFst (packet c))) (mask c)
  · rw [ite_eq_left (hs.mpr hi)]
    simp only [MvPolynomial.eval₂_one, sign_one, hi, not_true_eq_false, false_implies]
    constructor
    · intro _; trivial
    · intro _; rfl
  · rw [ite_eq_right (fun h => hi (hs.mp h)), TubeFiniteLeafSigns.sign_eq, TubeFiniteLeafSigns.row_of_constraint]
    simp only [hi, not_false_eq_true, true_implies]
    exact sign_eq_one_iff

theorem allSigns_iff (c : List Bool) (z : Fin (TubeSampleCoefficient.A packet c) → ℝ) :
    (∀ j : Fin ((source packet mask).count c),
      SignType.sign (((source packet mask).polynomial c j.val).eval₂ (Int.castRingHom ℝ) z) =
        (source packet mask).pattern c j.val) ↔ inactiveSigns (packet c) (mask c) z := by
  constructor
  · intro h i hi
    exact (rowSign_iff packet mask c i z).mp (h (constraintEquiv _ i)) hi
  · intro h j
    let i : PerturbedSource.Index (pairFst (packet c)) := (constraintEquiv _).symm ⟨j.val, j.isLt⟩
    have H := (rowSign_iff packet mask c i z).mpr (h i)
    have he : constraintEquiv (TubeIndexed.arity (pairFst (packet c))) i = ⟨j.val, j.isLt⟩ :=
      (constraintEquiv (TubeIndexed.arity (pairFst (packet c)))).apply_symm_apply _
    have he' := congrArg Fin.val he
    dsimp only at he'
    rw [he'] at H
    exact H

/-- The regular variable list contains the rotated spatial variables. -/
theorem arity_le (c : List Bool) :
    TubeSampleCoefficient.A packet c ≤ TubeRegularFiniteSigns.arity (pairFst ∘ packet) c := by
  change TubeProjectionEncoding.pointCount (TubeIndexed.arity (pairFst (packet c))) + 1 + 1 ≤
    TubeProjectionEncoding.pointCount (TubeIndexed.arity (pairFst (packet c))) +
      TubeProjectionEncoding.pointCount (TubeIndexed.arity (pairFst (packet c))) + 3 + 1
  omega

noncomputable def nativeSource : FiniteLeafSignBits.Source (TubeRegularFiniteSigns.arity (pairFst ∘ packet)) :=
  (source packet mask).embed (TubeRegularFiniteSigns.arity (pairFst ∘ packet))

noncomputable def nativeAccess (hp : packet ∈ FP) (hm : mask ∈ FP) : (nativeSource packet mask).Access :=
  (access packet mask hp hm).embed (TubeRegularFiniteSigns.arity (pairFst ∘ packet))
    (TubeSampleCoefficient.A_unary packet hp)

/-- The rotated spatial assignment recovers the native point coordinates. -/
theorem native_samplePoint (c : List Bool)
    (z : Fin (TubeRegularFiniteSigns.arity (pairFst ∘ packet) c) → ℝ) :
    samplePoint (packet c)
      (z ∘ FiniteLeafSignBits.rotationEmbedding (TubeSampleCoefficient.A packet c)
        (TubeRegularFiniteSigns.arity (pairFst ∘ packet) c) (arity_le packet c)) =
      fun i => z (TubeHomogenization.outputEquiv (pairFst (packet c)) (some (.inl (.inl i)))) := by
  funext i
  change z (FiniteLeafSignBits.rotationEmbedding _ _ (arity_le packet c)
    (TubeMacaulay.coordinateEquiv (TubeIndexed.arity (pairFst (packet c))) (some i)).succ) = _
  apply congrArg z
  apply Fin.ext
  rw [FiniteLeafSignBits.rotationEmbedding_val]
  simp only [Fin.val_succ, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, Nat.add_sub_cancel]
  rfl

/-- Inactive inequalities on the spatial part of a native regular assignment. -/
theorem native_allSigns_iff (c : List Bool)
    (z : Fin (TubeRegularFiniteSigns.arity (pairFst ∘ packet) c) → ℝ) :
    (∀ j : Fin ((nativeSource packet mask).count c),
      SignType.sign (((nativeSource packet mask).polynomial c j.val).eval₂ (Int.castRingHom ℝ) z) =
        (nativeSource packet mask).pattern c j.val) ↔
      inactiveSigns (packet c) (mask c)
        (z ∘ FiniteLeafSignBits.rotationEmbedding (TubeSampleCoefficient.A packet c)
          (TubeRegularFiniteSigns.arity (pairFst ∘ packet) c) (arity_le packet c)) := by
  rw [← allSigns_iff packet mask c]
  change (∀ j : Fin ((source packet mask).count c),
    SignType.sign ((((source packet mask).embed (TubeRegularFiniteSigns.arity (pairFst ∘ packet))).polynomial c j.val).eval₂
      (Int.castRingHom ℝ) z) = (source packet mask).pattern c j.val) ↔ _
  apply forall_congr'
  intro j
  rw [FiniteLeafSignBits.Source.embed_eval (source packet mask) _ c j.val (arity_le packet c)]

end LeanCanny.ETR.TubeInactiveFiniteSigns
