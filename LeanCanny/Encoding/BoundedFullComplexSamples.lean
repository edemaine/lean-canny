/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullCriticalSamples
public import LeanCanny.Encoding.BoundedCriticalSeparator
public import LeanCanny.Geometry.RegularAlgebraicRootCount

/-! # Bounded complex samples of the actual full critical source

The selected direction excludes every normalized complex Jacobian kernel.
The complete complex sample set is consequently finite with the same binary
label allowance as the real sample set. A bounded integer projection separates
all complex samples, and therefore also their real subset.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullComplexSamples
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Geometry LeanCanny.Algebra LeanCanny.Computation
open BoundedFullWriter MvPolynomial
open scoped Classical BigOperators Matrix

abbrev Samples (P : Readers) (c : List Bool) :=
  RegularAlgebraicRootCount.Roots (K := ℂ) (BoundedFullCriticalSamples.equations P c)

theorem jacobian_nonzero (P : Readers) (c : List Bool) (x : Samples P c) :
    (JacobianKernelCharts.jacobian (BoundedFullCriticalSamples.equations P c)).eval₂ (Int.castRingHom ℂ) x.val ≠ 0 := by
  have hc : ∀ chart : Fin (P.dim c + 4), ¬ ∃ z v : Fin (P.dim c + 4) → ℂ,
      v chart = 1 ∧ (∀ j, (BoundedFullCriticalSamples.equations P c j).eval₂ (Int.castRingHom ℂ) z = 0) ∧
        JacobianKernelCharts.matrix (Int.castRingHom ℂ) (BoundedFullCriticalSamples.equations P c) z *ᵥ v = 0 := by
    intro chart hb
    exact BoundedFullDirectionChoice.record_good P c chart
      ((CriticalKernel.finite_bad_iff_kernel (Int.castRingHom ℂ) (BoundedFullCriticalSamples.polynomial P c)
        (BoundedFullCriticalSamples.direction P c) (fun j => BoundedFullCriticalSamples.direction P c j.val)
        (fun _ => rfl) chart).mpr hb)
  exact ((JacobianKernelCharts.regular_iff_charts (Int.castRingHom ℂ) (BoundedFullCriticalSamples.equations P c)).mpr hc)
    x.val x.property

theorem finite_samples (P : Readers) (c : List Bool) :
    Finite (Samples P c) ∧ Nat.card (Samples P c) ≤ 2 ^ BoundedFullCriticalSamples.labelWidth P c :=
  RegularAlgebraicRootCount.finite_card_le_uniform (BoundedFullCriticalSamples.equations P c) (degree P c)
    (BoundedFullCriticalSamples.equations_degree P c)
    (by have := BoundedRegularSource.powerDegree_gt_one (size P c); change 0 < BoundedZeroSource.powerDegree (size P c); omega)
    (jacobian_nonzero P c)

noncomputable def value (P : Readers) (record : List Bool → List Bool) (c : List Bool)
    (x : Fin (P.dim c + 4) → ℂ) : ℂ :=
  ∑ i, x i * (BoundedCriticalSeparator.weight P record c i.val : ℂ)

def Good (P : Readers) (c r : List Bool) : Prop :=
  Function.Injective (fun x : Samples P c => value P (fun _ => r) c x.val)

noncomputable def ofReal (P : Readers) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P c) : Samples P c :=
  ⟨fun i => (x.val i : ℂ), fun j => by
    have hm : Complex.ofRealHom.comp (Int.castRingHom ℝ) = Int.castRingHom ℂ := RingHom.ext_int _ _
    change (BoundedFullCriticalSamples.equations P c j).eval₂ (Int.castRingHom ℂ) (Complex.ofRealHom ∘ x.val) = 0
    rw [← hm, ← eval₂_comp_left, x.property j, map_zero]⟩

theorem ofReal_injective (P : Readers) (c : List Bool) : Function.Injective (ofReal P c) := by
  intro x y h
  apply Subtype.ext
  funext i
  exact Complex.ofReal_injective (congrFun (congrArg Subtype.val h) i)

theorem value_ofReal (P : Readers) (record : List Bool → List Bool) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P c) :
    value P record c (ofReal P c x).val = (BoundedCriticalSeparator.value P record c x.val : ℂ) := by
  simp only [value, ofReal, BoundedCriticalSeparator.value, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast]

theorem good_real (P : Readers) (c r : List Bool) (h : Good P c r) : BoundedCriticalSeparator.Good P c r := by
  intro x y he
  apply ofReal_injective P c
  apply h
  change value P (fun _ => r) c (ofReal P c x).val = value P (fun _ => r) c (ofReal P c y).val
  rw [value_ofReal, value_ofReal]
  exact congrArg Complex.ofReal he

theorem exists_record (P : Readers) (c : List Bool) :
    ∃ r : List Bool, r.length = (P.dim c + 4) * BoundedCriticalSeparator.width P c ∧ Good P c r := by
  let : Finite (Samples P c) := (finite_samples P c).1
  let := Fintype.ofFinite (Samples P c)
  obtain ⟨v, hv, hinj⟩ := AffineGridAvoidance.exists_bounded_separating_direction
    (fun _ : Unit => fun x : Samples P c => x.val) (fun _ _ => (0 : ℂ)) (fun _ => Subtype.val_injective)
  have hcard : Fintype.card (Samples P c) ≤ 2 ^ BoundedFullCriticalSamples.labelWidth P c := by
    simpa only [Nat.card_eq_fintype_card] using (finite_samples P c).2
  have hfit (i : Fin (P.dim c + 4)) : v i < 2 ^ BoundedCriticalSeparator.width P c := by
    have hi : v i ≤ Fintype.card (Samples P c) ^ 2 := by simpa only [Fintype.card_unit, one_mul] using hv i
    calc
      v i ≤ (2 ^ BoundedFullCriticalSamples.labelWidth P c) ^ 2 := hi.trans (Nat.pow_le_pow_left hcard 2)
      _ = 2 ^ (2 * BoundedFullCriticalSamples.labelWidth P c) := by rw [← pow_mul, Nat.mul_comm]
      _ < 2 ^ BoundedCriticalSeparator.width P c := by
        unfold BoundedCriticalSeparator.width
        exact Nat.pow_lt_pow_right (by decide) (by omega)
  let e : ℕ → ℕ := fun i => if hi : i < P.dim c + 4 then v ⟨i, hi⟩ else 0
  let r := FixedWidthNatVector.encode (P.dim c + 4) (BoundedCriticalSeparator.width P c) e
  have hw (i : Fin (P.dim c + 4)) : BoundedCriticalSeparator.weight P (fun _ => r) c i.val = v i := by
    change Nat.fromBitsLE ((r.drop (i.val * BoundedCriticalSeparator.width P c)).take (BoundedCriticalSeparator.width P c)) = v i
    rw [FixedWidthNatVector.decode_block _ _ e i.val i.isLt]
    · simp only [e, i.isLt, dite_true, Fin.eta]
    · simpa only [e, i.isLt, dite_true, Fin.eta] using hfit i
  refine ⟨r, FixedWidthNatVector.length_encode _ _ _, ?_⟩
  simpa only [Good, value, hw, zero_add] using hinj ()

end LeanCanny.Encoding.BoundedFullComplexSamples
