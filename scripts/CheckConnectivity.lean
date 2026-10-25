import LeanCanny.Connectivity
import Mathlib.Analysis.Real.Sqrt

/-! Boundary cases for the implicit graph algorithm and the total input codec.
The axiom audit covers the connectivity declarations and their dependencies.
-/

open LeanCanny LeanCanny.Connectivity LeanCanny.Computation
open Cslib.Reachability

-- Width zero has one word. Reachability still accepts its zero-length path.
#guard savitch (fun _ _ => false) 0 0 [] []
-- Distinct isolated words must remain disconnected.
#guard !(savitch (fun _ _ => false) 1 1 [false] [true])
-- A directed edge works only in its stated direction.
#guard savitch (fun u v => u == [false] && v == [true]) 1 1 [false] [true]
#guard !(savitch (fun u v => u == [false] && v == [true]) 1 1 [true] [false])

-- Endpoint search finds a late candidate and keeps its width when none exists.
#guard ImplicitGraph.findWord (fun p : Unit × List Bool => p.2 == [true, true])
  (fun _ => 2) () == [true, true]
#guard (ImplicitGraph.findWord (fun _ : Unit × List Bool => false) (fun _ => 2) ()).length == 2
#guard ImplicitGraph.findWord (fun _ : Unit × List Bool => true) (fun _ => 0) () == []

example (edge : List Bool → List Bool → Bool) (w : ℕ) :
    ImplicitGraph.Connected edge (fun _ => false) w := by
  intro u hu v hv h
  cases h

example (edge : List Bool → List Bool → Bool) (valid : List Bool → Bool) :
    ImplicitGraph.Connected edge valid 0 := by
  intro u hu v hv _ _
  have hU : u = [] := List.length_eq_zero_iff.mp hu
  have hV : v = [] := List.length_eq_zero_iff.mp hv
  subst u
  subst v
  exact .refl

-- A real algebraic endpoint has a finite formula description.
private def positiveSqrtTwo : ETR.Formula :=
  .and (.eqZero (.add (.mul (.var 0) (.var 0)) (.const (-2))))
    (.ltZero (.mul (.const (-1)) (.var 0)))

private def query : PointQuery :=
  ⟨⟨1, .not .falsum⟩, positiveSqrtTwo, positiveSqrtTwo⟩

#guard Input.decode (Input.point query).encode = some (.point query)
#guard Input.decode ((Input.point query).encode ++ [false]) = none
#guard Input.decode [] = none

#guard decide (Input.IsPoint (Input.point query).encode)
#guard !decide (Input.IsWhole (Input.point query).encode)
#guard !decide (Input.IsPoint ((Input.point query).encode ++ [false]))
#guard !decide (Input.IsPoint [])

-- Constant payloads and formula tags must not be mistaken for term variables.
#guard ETR.Interleave.renameBits true (ETR.Formula.eqZero (.const (-1))).encode =
  (ETR.Formula.eqZero (.const (-1))).encode
#guard ETR.Interleave.renameBits true (ETR.Formula.eqZero (.var 0)).encode =
  (ETR.Formula.eqZero (.var 1)).encode
#guard ETR.FormulaArity.value (ETR.Formula.eqZero (.const (-1))).encode == 0
#guard ETR.FormulaArity.value (ETR.Formula.and (.eqZero (.var 2)) (.eqZero (.var 0))).encode == 3

-- A zero-dimensional satisfiable description denotes the unique empty tuple.
example : ∃ x : Fin 0 → ℝ, Denotes 0 (.not .falsum) x := by
  refine ⟨fun i => Fin.elim0 i, by decide, ?_⟩
  intro y
  simp only [ETR.Formula.Holds, not_false_eq_true, true_iff]
  exact Subsingleton.elim _ _

-- Syntactically out-of-dimension descriptions are rejected even if tautological.
example : ¬ ∃ x : Fin 0 → ℝ, Denotes 0 (.eqZero (.mul (.const 0) (.var 1))) x := by
  rintro ⟨x, hx, _⟩
  norm_num [ETR.Formula.arity, ETR.Term.arity] at hx

example : EndpointValidation.validEndpointLanguage ∈ PSPACE :=
  EndpointValidation.validEndpoints_mem_PSPACE

-- The endpoint scheme accepts a unique irrational coordinate.
example : ∃ x : Fin 1 → ℝ, Denotes 1 positiveSqrtTwo x := by
  let r := Real.sqrt 2
  have hr : 0 < r := Real.sqrt_pos.mpr (by norm_num)
  have hs : r ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  refine ⟨fun _ => r, by decide, ?_⟩
  intro y
  simp only [positiveSqrtTwo, ETR.Formula.Holds, ETR.Term.eval, ETR.Formula.extend,
    Nat.zero_lt_succ, ↓reduceDIte, Int.cast_neg, Int.cast_ofNat]
  constructor
  · rintro ⟨hy, hpos⟩
    have hy' : y 0 * y 0 - 2 = 0 := by simpa [sub_eq_add_neg] using hy
    have hpos' : 0 < y 0 := by simpa using hpos
    have h0 : y 0 = r := (sq_eq_sq₀ hpos'.le hr.le).mp (by nlinarith [hy'])
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    simpa only [hi] using h0
  · rintro rfl
    constructor
    · nlinarith [hs]
    · simpa using hr

-- The two input tags cannot be confused by either language.
example (d : Description) : (Input.whole d).encode ∉ pointLanguage := by simp
example (q : PointQuery) : (Input.point q).encode ∉ connectedLanguage := by simp

-- Frontier incidence connects a disjoint arc and its included endpoint.
example :
    let piece : Bool → Set ℝ := fun b => if b then {0} else Set.Ioo 0 1
    FrontierCover.Incident piece false true ∧ ¬ ClosedPathCover.Overlap piece false true := by
  dsimp only
  constructor
  · right
    refine ⟨0, by simp, ?_⟩
    simp only [Bool.false_eq_true, ite_false]
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    norm_num
  · rintro ⟨x, hx, hy⟩
    simp only [Bool.false_eq_true, ite_false, ite_true, Set.mem_singleton_iff] at hx hy
    subst x
    exact lt_irrefl _ hx.1

-- A branch can have a finite endpoint even when direct specialization of its
-- equation is identically zero. The derivative of sqrt also diverges there.
open Polynomial Filter in
open scoped Topology in
example : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let q : Polynomial (Polynomial ℝ) := C (X ^ 2) - X
  have hq0 : q.coeff 0 = X ^ 2 := by
    simp only [q, Polynomial.coeff_sub, Polynomial.coeff_C_zero, Polynomial.coeff_X_zero, sub_zero]
  have hq0ne : q.coeff 0 ≠ 0 := by rw [hq0]; exact pow_ne_zero _ X_ne_zero
  have hq : q ≠ 0 := by intro h; exact hq0ne (by rw [h]; simp)
  let p : Polynomial (Polynomial ℝ) := X ^ 3 * q
  have hp : p ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hq
  have htc : p.trailingCoeff = X ^ 2 := by
    have hx : ((X : Polynomial (Polynomial ℝ)) ^ 3).trailingCoeff = 1 := by
      simp only [Polynomial.trailingCoeff, Polynomial.natTrailingDegree_X_pow,
        Polynomial.coeff_X_pow_self]
    rw [show p.trailingCoeff = (X ^ 3 : Polynomial (Polynomial ℝ)).trailingCoeff *
      q.trailingCoeff from Polynomial.trailingCoeff_mul _ _, hx, one_mul,
      Polynomial.trailingCoeff_eq_coeff_zero hq0ne, hq0]
  have hinterval : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Set.Ioo 0 1 :=
    (nhdsGT_basis 0).mem_of_mem (by norm_num)
  have hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ), Real.sqrt t ∈ Set.Icc 0 1 := by
    filter_upwards [hinterval] with t ht
    exact ⟨Real.sqrt_nonneg _, Real.sqrt_le_one.mpr ht.2.le⟩
  have hz : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      Geometry.AlgebraicBranchLimit.value p t (Real.sqrt t) = 0 := by
    filter_upwards [hinterval] with t ht
    have hs := Real.sq_sqrt ht.1.le
    simp only [Geometry.AlgebraicBranchLimit.value, p, q, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_sub, Polynomial.eval₂_C,
      Polynomial.coe_evalRingHom, Polynomial.eval_pow, Polynomial.eval_X, hs, sub_self, mul_zero]
  obtain ⟨x, _, hlim, hx⟩ := Geometry.AlgebraicBranchLimit.exists_limit p hp
    (by norm_num : (0 : ℝ) < 1) Real.continuous_sqrt.continuousOn isCompact_Icc hbound hz
  rw [htc] at hx
  have hxe : x = 0 := by simpa using hx
  rwa [hxe] at hlim
