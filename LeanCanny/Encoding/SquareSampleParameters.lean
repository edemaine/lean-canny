/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleCoordinates
public import LeanCanny.Geometry.RegularAffineSubsetCount

/-! # Exact regular-root parameters for positive square systems

Checking the square equations and Jacobian selects precisely the regular
system roots among all primitive parameters. The accepted parameters have
a polynomial label-width bound derived from the native parameter degree.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleParameters
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open SquareSampleInput (Inputs)
open SquareSampleCoordinates (parameter coordinate)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] parameter coordinate

noncomputable def decode (F : Inputs) (u : List Bool) (theta : ℝ) :
    Fin (SquareSampleSource.count F u) → ℝ :=
  fun i => (coordinate F (pair u (BinaryNatCode.encode i.val))).eval theta

abbrev Candidates (F : Inputs) (u : List Bool) :=
  RegularAffineRootCount.RegularRoots (F.system u)
def RegularParameters (F : Inputs) (u : List Bool) :=
  {theta : ℝ // (parameter F u).eval₂ (Int.castRingHom ℝ) theta = 0 ∧
    (∀ i, (F.system u i).eval₂ (Int.castRingHom ℝ) (decode F u theta) = 0) ∧
    (fderiv ℝ (fun z => fun i => (F.system u i).eval₂ (Int.castRingHom ℝ) z)
      (decode F u theta)).IsInvertible}

noncomputable def candidate (F : Inputs) (u : List Bool) (theta : RegularParameters F u) : Candidates F u :=
  ⟨⟨decode F u theta.val, theta.property.2.1⟩, theta.property.2.2⟩

theorem candidate_injective (F : Inputs) (u : List Bool) : Function.Injective (candidate F u) := by
  intro theta theta' he
  apply Subtype.ext
  apply SquareSampleCoordinates.parameter_roots_ext F u theta.val theta'.val theta.property.1 theta'.property.1
  intro i
  exact congrFun (congrArg (fun z : Candidates F u => z.val.val) he) i

theorem candidate_surjective (F : Inputs) (u : List Bool) : Function.Surjective (candidate F u) := by
  intro z
  obtain ⟨theta, ht, hx⟩ := SquareSampleCoordinates.regular_root_complete F u z.val.val z.val.property z.property
  have he : decode F u theta = z.val.val := funext fun i => (hx i).2
  have hz : ∀ i, (F.system u i).eval₂ (Int.castRingHom ℝ) (decode F u theta) = 0 := by
    rw [he]
    exact z.val.property
  have hr : (fderiv ℝ (fun y => fun i => (F.system u i).eval₂ (Int.castRingHom ℝ) y)
      (decode F u theta)).IsInvertible := by rw [he]; exact z.property
  refine ⟨⟨theta, ht, hz, hr⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact he

noncomputable def regularEquiv (F : Inputs) (u : List Bool) : RegularParameters F u ≃ Candidates F u :=
  Equiv.ofBijective (candidate F u) ⟨candidate_injective F u, candidate_surjective F u⟩

noncomputable def labelWidth (F : Inputs) (u : List Bool) : ℕ :=
  (SquareSampleCoordinates.parameterDegree F u + 1).size

theorem labelWidth_unary {F : Inputs} (h : F.Access) : UnaryFn (labelWidth F) :=
  (UnaryFn.length ((SquareSampleCoordinates.parameterDegree_binary h).add (BinaryFn.const 1)).bits_mem_FP).of_eq
    (fun u => BinaryNatCode.length_encode (SquareSampleCoordinates.parameterDegree F u + 1))

theorem finite_regular_parameters (F : Inputs) (u : List Bool) :
    Finite (RegularParameters F u) ∧ Nat.card (RegularParameters F u) ≤ 2 ^ labelWidth F u := by
  have H := RootBranchCount.finite_card_le
    (fun t : RegularParameters F u => fun _i : Fin 1 => t.val)
    (fun t t' he => Subtype.ext (congrFun he 0))
    (fun _i : Fin 1 => (parameter F u).map (Int.castRingHom ℝ))
    (fun _ => (Polynomial.map_ne_zero_iff Int.cast_injective).mpr
      (SquareSampleCoordinates.parameter_ne_zero F u))
    (fun t _ => by rw [Polynomial.eval_map]; exact t.property.1)
  refine ⟨H.1, H.2.trans ?_⟩
  calc
    (∏ _i : Fin 1, ((parameter F u).map (Int.castRingHom ℝ)).natDegree) =
        ((parameter F u).map (Int.castRingHom ℝ)).natDegree := by simp
    _ ≤ (parameter F u).natDegree := Polynomial.natDegree_map_le
    _ ≤ SquareSampleCoordinates.parameterDegree F u := (SquareSampleCoordinates.parameter_bounds F u).1
    _ ≤ 2 ^ labelWidth F u := by
      exact (Nat.le_succ _).trans ((Nat.lt_size_self _).le)

end LeanCanny.Encoding.SquareSampleParameters
