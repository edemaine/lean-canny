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

-- Global continuation must enumerate both isolated regular roots at every
-- parameter, not just a branch chosen at the initial root.
open LeanCanny.Geometry Set in
example :
    ∃ curve : RootBranches.Index (fun z : ℝ × ℝ => z.2 ^ 2 - 1) 0 1
        (⟨1/2, by norm_num⟩ : Ioo (0 : ℝ) 1) → C(Ioo (0 : ℝ) 1, ℝ),
      (∀ i t, (curve i t) ^ 2 = 1) ∧
      ∀ t : Ioo (0 : ℝ) 1, ∀ x : ℝ, x ^ 2 = 1 ↔ ∃! i, curve i t = x := by
  let f : ℝ × ℝ → ℝ := fun z => z.2 ^ 2 - 1
  have hcont : Continuous f := by fun_prop
  have hproper : IsProperMap (RootProjection.projection f) := by
    apply RootProjection.isProperMap_of_compact_bound f hcont isCompact_Icc
      (K := Icc (-1 : ℝ) 1)
    intro z
    have hz : z.val.2 ^ 2 - 1 = 0 := z.property
    constructor <;> nlinarith [sq_nonneg (z.val.2 + 1), sq_nonneg (z.val.2 - 1)]
  have hf (z : RootProjection.Space f) : ContDiffAt ℝ 1 f z.val := by fun_prop
  have hJac (z : RootProjection.Space f) :
      (fderiv ℝ f z.val ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    have hz : z.val.2 ^ 2 - 1 = 0 := z.property
    have hn : (2 : ℝ) * z.val.2 ≠ 0 := by intro h; nlinarith
    have hzn : z.val.2 ≠ 0 := by intro h; apply hn; rw [h, mul_zero]
    have hd := ((hasFDerivAt_snd (𝕜 := ℝ) (p := z.val)).pow 2).sub_const 1
    rw [hd.fderiv]
    apply ContinuousLinearMap.IsInvertible.of_inverse
      (g := ((2 * z.val.2)⁻¹) • ContinuousLinearMap.id ℝ ℝ)
    · apply ContinuousLinearMap.ext
      intro x
      change (2 • z.val.2 ^ (2 - 1)) * ((2 * z.val.2)⁻¹ * x) = x
      norm_num only [Nat.reduceSub, pow_one, nsmul_eq_mul, Nat.cast_ofNat]
      field_simp [hzn]
    · apply ContinuousLinearMap.ext
      intro x
      change (2 * z.val.2)⁻¹ * ((2 • z.val.2 ^ (2 - 1)) * x) = x
      norm_num only [Nat.reduceSub, pow_one, nsmul_eq_mul, Nat.cast_ofNat]
      field_simp [hzn]
  obtain ⟨curve, hroots, hcomplete⟩ := RootBranches.exists_branches f 0 1
    ⟨1/2, by norm_num⟩ hproper (fun z _ => hf z) (fun z _ => hJac z)
  refine ⟨curve, ?_, ?_⟩
  · intro i t
    exact sub_eq_zero.mp (hroots i t)
  · intro t x
    exact (sub_eq_zero.symm).trans (hcomplete t x)

namespace ParabolaSlab
open Set

private noncomputable def curve (b : Bool) (t : ℝ) : ℝ := if b then Real.sqrt t else -Real.sqrt t
private def H (t x : ℝ) : Prop := x ^ 2 = t
private def left : Unit → Set ℝ := fun _ => {0}
private def right : Bool → Set ℝ := fun b => {if b then 1 else -1}

private theorem hc (b : Bool) : ContinuousOn (curve b) (Icc 0 1) := by
  cases b
  · exact Real.continuous_sqrt.neg.continuousOn
  · exact Real.continuous_sqrt.continuousOn

private theorem hroot (b : Bool) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : H t (curve b t) := by
  have hs := Real.sq_sqrt ht.1
  cases b <;> simpa [H, curve] using hs

private theorem hcomplete (t : ℝ) (_ : t ∈ Ioo (0 : ℝ) 1) (x : ℝ) (hx : H t x) :
    ∃ b, curve b t = x := by
  have ht : 0 ≤ t := by dsimp [H] at hx; nlinarith [sq_nonneg x]
  have hs := Real.sq_sqrt ht
  have heq : x = Real.sqrt t ∨ x = -Real.sqrt t :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (hx.trans hs.symm)
  rcases heq with h | h
  · exact ⟨true, by simpa [curve] using h.symm⟩
  · exact ⟨false, by simpa [curve] using h.symm⟩

private theorem hlsub (u : Unit) (x : ℝ) (hx : x ∈ left u) : H 0 x := by
  simp only [left, mem_singleton_iff] at hx
  simp [H, hx]

private theorem hrsub (b : Bool) (x : ℝ) (hx : x ∈ right b) : H 1 x := by
  cases b <;> simp_all [right, H]

private theorem hlcover (x : ℝ) (hx : H 0 x) : ∃ u, x ∈ left u := by
  exact ⟨(), by simpa [left] using sq_eq_zero_iff.mp hx⟩

private theorem hrcover (x : ℝ) (hx : H 1 x) : ∃ b, x ∈ right b := by
  have heq : x = 1 ∨ x = -1 := sq_eq_one_iff.mp hx
  rcases heq with h | h
  · exact ⟨true, by simp [right, h]⟩
  · exact ⟨false, by simp [right, h]⟩

-- The two disjoint interior branches merge at the singular left endpoint.
-- Connectivity is proved by the assembled frontier graph, including the
-- distinct right endpoints, rather than assuming the arcs already overlap.
example : IsPreconnected (univ : Set (SlabCover.Space H 0 1)) := by
  let piece := SlabCover.piece H curve left right 0 1
  have hL (b : Bool) : FrontierCover.Incident piece (.inl b) (.inr (.inl ())) := by
    apply (SlabCover.incident_arc_left_iff H (by norm_num) curve hc hroot
      left right hlsub hrsub b ()).mpr
    simp [left, curve]
  have hR (b : Bool) : FrontierCover.Incident piece (.inl b) (.inr (.inr b)) := by
    apply (SlabCover.incident_arc_right_iff H (by norm_num) curve hc hroot
      left right hlsub hrsub b b).mpr
    cases b <;> simp [right, curve]
  have hin (i : SlabCover.Index Bool Unit Bool) :
      Relation.ReflTransGen (FrontierCover.Incident piece) i (.inr (.inl ())) := by
    rcases i with b | (u | b)
    · exact .single (hL b)
    · cases u; exact .refl
    · exact (Relation.ReflTransGen.single ((FrontierCover.incident_symm piece).mp (hR b))).tail (hL b)
  have hout (i : SlabCover.Index Bool Unit Bool) :
      Relation.ReflTransGen (FrontierCover.Incident piece) (.inr (.inl ())) i := by
    rcases i with b | (u | b)
    · exact .single ((FrontierCover.incident_symm piece).mp (hL b))
    · cases u; exact .refl
    · exact (Relation.ReflTransGen.single ((FrontierCover.incident_symm piece).mp (hL b))).tail (hR b)
  apply (SlabCover.isPreconnected_iff_reachable H (by norm_num) curve hc hroot hcomplete
    left right hlsub hrsub hlcover hrcover
    (fun _ => FrontierCover.accessible_singleton 0)
    (fun b => FrontierCover.accessible_singleton (if b then 1 else -1))).mpr
  intro i j _ _
  exact (hin i).trans (hout j)

end ParabolaSlab

section CriticalProjectionTests
open LeanCanny.Geometry LeanCanny.Algebra Set MvPolynomial

-- The unknown can be unbounded globally while its level projection is proper.
example : IsProperMap (fun z : {z : ℝ × ℝ // z.1 = z.2} => z.val.1) :=
  ProperProjection.isProperMap_fst_of_level (isClosed_eq continuous_fst continuous_snd)
    isProperMap_id (fun _ hz => hz)

-- The construction must exclude the singular level of x² even though it
-- produces finite regular critical fibers at all other retained levels.
example : ∃ r : Polynomial ℝ, r ≠ 0 ∧ r.eval 0 = 0 := by
  let p : MvPolynomial Unit ℝ := X () ^ 2
  obtain ⟨u, r, hr, _, hregular⟩ := ProjectionCriticalBranches.exists_regular_direction p ()
  refine ⟨r, hr, ?_⟩
  by_contra hn
  let v := ProjectionFiniteSpecialization.normalizedDirection () (fun i => (u i : ℝ))
  have hv : v () = 1 := by simp [v, ProjectionFiniteSpecialization.normalizedDirection]
  have hroot : PolynomialRootFamily.value (ProjectionCriticalBranches.equation p () v)
      (0, fun _ => 0) = 0 := by
    apply (ProjectionCriticalBranches.value_iff p () v hv 0 (fun _ => 0)).mpr
    constructor
    · simp [p]
    · intro i
      have hi : i = () := Subsingleton.elim _ _
      subst i
      simp [hv, p]
  have hdet := hregular 0 (fun _ => 0) hn hroot
  rw [ProjectionCriticalBranches.eval_jacobian] at hdet
  have hz : GenericProjectionJacobian.spatial p () v (fun _ => 0) = 0 := by
    apply Matrix.ext
    intro i j
    have hi : i = () := Subsingleton.elim _ _
    have hj : j = () := Subsingleton.elim _ _
    subst i
    subst j
    simp [GenericProjectionJacobian.spatial, p]
  rw [hz, Matrix.det_zero] at hdet
  exact hdet rfl

end CriticalProjectionTests
