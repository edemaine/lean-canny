import LeanCanny.Connectivity
import LeanCanny.Geometry.SingularParameterBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

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

section RegularFiberTests
open LeanCanny.Geometry Set MvPolynomial

-- A positive-dimensional, noncompact regular fiber must receive local charts.
example : LocallyPathConnectedSpace {z : ℝ × ℝ // z.1 = 0} := by
  apply RegularFiber.locallyPathConnected Prod.fst 0
  · intro z
    exact contDiff_fst.contDiffAt
  · intro z y
    exact ⟨(y, 0), by simp only [fderiv_fst, ContinuousLinearMap.coe_fst']⟩

namespace ComponentSamplingChecks

private noncomputable def p : MvPolynomial Unit ℝ := X () ^ 2

private theorem finite_level : {x : Unit → ℝ | p.eval x = 1}.Finite := by
  apply (Set.toFinite ({fun _ : Unit => (1 : ℝ), fun _ : Unit => (-1 : ℝ)})).subset
  intro x hx
  have hs : x () ^ 2 = 1 := by simpa [p] using hx
  simp only [mem_insert_iff, mem_singleton_iff]
  rcases sq_eq_one_iff.mp hs with h | h
  · left
    funext i
    cases i
    exact h
  · right
    funext i
    cases i
    exact h

private theorem regular_level (x : Unit → ℝ) (hx : p.eval x = 1) :
    Function.Surjective (fderiv ℝ (fun y => p.eval y) x) := by
  have hne : fderiv ℝ (fun y => p.eval y) x ≠ 0 := by
    intro hz
    have hgrad := (PolynomialCalculus.critical_iff (RingHom.id ℝ) p x).mp hz
    have hh := hgrad ()
    have hs : x () ^ 2 = 1 := by simpa [p] using hx
    simp [p] at hh
    nlinarith
  exact surjective_of_nonzero_of_finrank_eq_one (K := ℝ) (by simp)
    (fun h => hne (ContinuousLinearMap.coe_injective h))

-- The global maximum of the projection is +1. A component-wise sampler
-- starting at -1 must still produce a critical point in the negative component.
example : ∃ y : Unit → ℝ, y () = -1 ∧
    PolynomialRootFamily.value (ProjectionCriticalBranches.equation p () (fun _ => 1)) (1, y) = 0 := by
  obtain ⟨y, hjoined, hcrit⟩ := ComponentCriticalSampling.exists_joined_critical p ()
    (fun _ => 1) rfl 1 finite_level.isCompact regular_level (fun _ => -1) (by simp [p])
  obtain ⟨γ, hγ⟩ := hjoined
  have hfinite : (range γ).Finite := finite_level.subset (by
    rintro z ⟨t, rfl⟩
    exact hγ t)
  have hsub : (range γ).Subsingleton :=
    (isPreconnected_range γ.continuous).isDiscrete_iff_subsingleton.mp hfinite.isDiscrete
  have heq : (fun _ : Unit => (-1 : ℝ)) = y := hsub γ.source_mem_range γ.target_mem_range
  exact ⟨y, by rw [← heq], hcrit⟩

end ComponentSamplingChecks

end RegularFiberTests

section ComponentTransportTests
open LeanCanny.Geometry LeanCanny.Connectivity Set Filter

-- The cover has an infinite index type; a path still yields a finite walk.
example : Relation.ReflTransGen
    (ClosedPathCover.Overlap (fun r : ℝ => Ioo (r - 1) (r + 1))) 0 1000 := by
  apply OpenPathCover.reachable_of_joinedIn _ (fun _ => isOpen_Ioo)
    (fun x => ⟨x, by constructor <;> linarith⟩)
    (x := (0 : ℝ)) (y := (1000 : ℝ)) (by norm_num) (by norm_num)
  exact joinedIn_univ.mpr (PathConnectedSpace.joined _ _)

-- Square has a critical value at zero. Component transport on the positive
-- parameter region must neither require regularity there nor merge its two roots.
example (t : ℝ) (ht : 0 < t) :
    ¬ JoinedIn {x : ℝ | x ^ 2 = t} (Real.sqrt t) (-Real.sqrt t) := by
  let S : Set ℝ := Ioi 0
  let : PreconnectedSpace S := Subtype.preconnectedSpace isPreconnected_Ioi
  have hp : IsProperMap (fun x : ℝ => x ^ 2) := by
    apply isProperMap_iff_tendsto_cocompact.mpr
    refine ⟨continuous_id.pow 2, ?_⟩
    simpa only [← Metric.cobounded_eq_cocompact] using
      (tendsto_pow_cobounded_cobounded (α := ℝ) (by norm_num : (2 : ℕ) ≠ 0))
  have hreg (x : ℝ) (hx : x ^ 2 ∈ S) : Function.Surjective (fderiv ℝ (fun y : ℝ => y ^ 2) x) := by
    have hxn : x ≠ 0 := by intro h; simp [h, S] at hx
    rw [(hasFDerivAt_pow (𝕜 := ℝ) 2).fderiv]
    intro y
    refine ⟨y / (2 * x), ?_⟩
    change (2 • x ^ (2 - 1)) * (y / (2 * x)) = y
    norm_num only [Nat.reduceSub, pow_one, nsmul_eq_mul, Nat.cast_ofNat]
    field_simp [hxn]
  let s : S → ℝ := fun b => Real.sqrt b.val
  let d : S → ℝ := fun b => -Real.sqrt b.val
  have hs : Continuous s := Real.continuous_sqrt.comp continuous_subtype_val
  have hd : Continuous d := hs.neg
  have hps (b : S) : s b ^ 2 = b.val := Real.sq_sqrt b.property.le
  have hpd (b : S) : d b ^ 2 = b.val := by simpa only [d, neg_sq] using hps b
  let a : S := ⟨1, by norm_num [S]⟩
  let b : S := ⟨t, ht⟩
  have H := RegularComponentTransport.joined_sections_iff (fun x : ℝ => x ^ 2) S hp
    (fun _ _ => by fun_prop) hreg hs hd hps hpd a b
  intro hjoin
  have h1 : JoinedIn {x : ℝ | x ^ 2 = 1} 1 (-1) := by
    simpa only [s, d, a, Real.sqrt_one, Set.preimage, mem_singleton_iff] using H.mpr hjoin
  obtain ⟨γ, hγ⟩ := h1
  have hf : {x : ℝ | x ^ 2 = 1}.Finite := by
    have heq : {x : ℝ | x ^ 2 = 1} = {1, -1} := by ext x; simp [sq_eq_one_iff]
    rw [heq]
    exact toFinite _
  have hfinite : (range γ).Finite := hf.subset (by rintro x ⟨u, rfl⟩; exact hγ u)
  have hsub : (range γ).Subsingleton :=
    (isPreconnected_range γ.continuous).isDiscrete_iff_subsingleton.mp hfinite.isDiscrete
  have heq : (1 : ℝ) = -1 := hsub γ.source_mem_range γ.target_mem_range
  norm_num at heq

end ComponentTransportTests

namespace SaturatedSlabTests
open LeanCanny.Geometry Set

abbrev Segment := Icc (0 : ℝ) 1
abbrev Strip := ℝ × Segment
local instance : CompactSpace Segment := isCompact_iff_compactSpace.mp isCompact_Icc
local instance : LocallyPathConnectedSpace Segment := (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
local instance : PathConnectedSpace Segment :=
  isPathConnected_iff_pathConnectedSpace.mp ((convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, by norm_num⟩)

def band : Set Strip := Ioo (0 : ℝ) 1 ×ˢ univ

theorem tails (c : Ioo (0 : ℝ) 1) :
    IsConnected (ConnectedSlabLimit.tail (Prod.fst : Strip → ℝ) (a := 0) band c.val) := by
  have he : ConnectedSlabLimit.tail (Prod.fst : Strip → ℝ) (a := 0) band c.val = Ioo 0 c.val ×ˢ univ := by
    ext x
    constructor
    · rintro ⟨_, hx⟩
      exact ⟨hx, mem_univ _⟩
    · rintro ⟨hx, _⟩
      exact ⟨⟨⟨hx.1, hx.2.trans c.property.2⟩, mem_univ _⟩, hx⟩
  rw [he]
  exact (((convex_Ioo (0 : ℝ) c.val).isPathConnected
    ⟨c.val / 2, by constructor <;> linarith [c.property.1]⟩).prod isPathConnected_univ).isConnected

example :
    let L := closure band ∩ (Prod.fst : Strip → ℝ) ⁻¹' {0}
    IsConnected L ∧ (0, ⟨0, by norm_num⟩) ∈ L ∧ (0, ⟨1, by norm_num⟩) ∈ L := by
  have hc := ConnectedSlabLimit.isConnected_endpoint (Prod.fst : Strip → ℝ)
    isProperMap_fst_of_compactSpace (by norm_num : (0 : ℝ) < 1) (fun x (h : x ∈ band) => h.1) tails
  refine ⟨hc, ?_, ?_⟩ <;> change _ ∈ closure band ∧ _
  all_goals
    constructor
    · simp [band, closure_prod_eq, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    · rfl

noncomputable def sections : Unit → C(ℝ, Strip) := fun _ =>
  ⟨fun t => (t, ⟨0, by norm_num⟩), continuous_id.prodMk continuous_const⟩
noncomputable def chart (_ : Strip) : OpenPartialHomeomorph Strip (ℝ × Segment) :=
  (Homeomorph.refl Strip).toOpenPartialHomeomorph

-- The sample section sits at height zero, but its saturated component also
-- contains height one. Paths may change both the level and the fiber coordinate.
example : JoinedIn univ ((0 : ℝ), (⟨1, by norm_num⟩ : Segment))
    (1, (⟨0, by norm_num⟩ : Segment)) := by
  have hp : IsProperMap (Prod.fst : Strip → ℝ) := isProperMap_fst_of_compactSpace
  have hsource (x : Strip) : x ∈ (chart x).source := mem_univ _
  have hfirst (z x : Strip) (_ : x ∈ (chart z).source) :
      (chart z x).1 = Prod.fst x := rfl
  have hproj (j : Unit) (t : ℝ) : Prod.fst (sections j t) = t := rfl
  have hm (t : ℝ) (v : Segment) : (t, v) ∈ FiberSectionCover.piece Prod.fst sections () := by
    change JoinedIn (Prod.fst ⁻¹' {t}) (t, (⟨0, by norm_num⟩ : Segment)) (t, v)
    apply ((joinedIn_univ.mpr (PathConnectedSpace.joined (⟨0, by norm_num⟩ : Segment) v)).map
      (continuous_const.prodMk continuous_id).continuousOn).mono
    rintro z ⟨_, _, rfl⟩
    rfl
  exact (FiberSectionCover.paths Prod.fst sections chart hsource hfirst hp hproj ()
    _ (hm _ _) _ (hm _ _)).mono (subset_univ _)
end SaturatedSlabTests

namespace ClosedSlabTests
open Set

local instance : PathConnectedSpace ((id : ℝ → ℝ) ⁻¹' Ioo 0 1) :=
  isPathConnected_iff_pathConnectedSpace.mp
    (Convex.isPathConnected (convex_Ioo 0 1) ⟨1 / 2, by norm_num⟩)

noncomputable def D : ComponentSlabCover.InteriorData (id : ℝ → ℝ) 0 1 Unit where
  piece := fun _ => univ
  closed := fun _ => isClosed_univ
  cover := fun _ => ⟨(), mem_univ _⟩
  paths := fun _ _ _ _ _ => joinedIn_univ.mpr (PathConnectedSpace.joined _ _)
  arc := fun _ => id
  continuous_arc := fun _ => continuous_id.continuousOn
  arc_mem := fun _ t => ⟨t, mem_univ _, rfl⟩
  level_left := fun _ => rfl
  level_right := fun _ => rfl
  limit_left := fun _ => Set.Subsingleton.isPreconnected (by
    intro x hx y hy
    exact hx.2.trans hy.2.symm)
  limit_right := fun _ => Set.Subsingleton.isPreconnected (by
    intro x hx y hy
    exact hx.2.trans hy.2.symm)

noncomputable def C (c : ℝ) : ClopenPathCover ((id : ℝ → ℝ) ⁻¹' {c}) Bool where
  piece := fun b => if b then univ else ∅
  clopen := fun b => by cases b <;> simp
  cover := fun _ => ⟨true, by simp⟩
  paths := by
    intro b x hx y hy
    have heq : x = y := Subtype.ext (x.property.trans y.property.symm)
    subst y
    exact JoinedIn.refl hx

private theorem valid : ComponentSlabCover.Valid D (C 0) (C 1) () true true := by
  constructor
  · exact ⟨⟨0, rfl⟩, mem_univ _, rfl⟩
  · exact ⟨⟨1, rfl⟩, mem_univ _, rfl⟩

-- The middle closed piece contains both endpoints although its interior
-- piece omits both. The constructed paths pass through the attached slices.
example :
    let P := ComponentSlabCover.piece D (C 0) (C 1)
    JoinedIn (P (.inl ((), true, true))) ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ := by
  let i : ComponentSlabCover.Index Unit Bool Bool := .inl ((), true, true)
  have hzero : (⟨0, by norm_num⟩ : (id : ℝ → ℝ) ⁻¹' Icc 0 1) ∈ ComponentSlabCover.piece D (C 0) (C 1) i := by
    change 0 ∈ ComponentSlabCover.ambientPiece D (C 0) (C 1) i
    rw [show i = .inl ((), true, true) from rfl,
      ComponentSlabCover.ambientPiece_middle_eq D (C 0) (C 1) continuous_id (by norm_num) () true true valid]
    exact Or.inl (Or.inr ⟨⟨0, rfl⟩, mem_univ _, rfl⟩)
  have hone : (⟨1, by norm_num⟩ : (id : ℝ → ℝ) ⁻¹' Icc 0 1) ∈ ComponentSlabCover.piece D (C 0) (C 1) i := by
    change 1 ∈ ComponentSlabCover.ambientPiece D (C 0) (C 1) i
    rw [show i = .inl ((), true, true) from rfl,
      ComponentSlabCover.ambientPiece_middle_eq D (C 0) (C 1) continuous_id (by norm_num) () true true valid]
    exact Or.inr ⟨⟨1, rfl⟩, mem_univ _, rfl⟩
  exact ComponentSlabCover.paths D (C 0) (C 1) continuous_id (by norm_num)
    ⟨1 / 2, by norm_num⟩ i _ hzero _ hone

-- Choosing an empty endpoint component invalidates the entire triple.
example : ComponentSlabCover.piece D (C 0) (C 1) (.inl ((), false, true)) = ∅ := by
  have hn : ¬ComponentSlabCover.Valid D (C 0) (C 1) () false true := by
    rintro ⟨⟨x, hx, _⟩, _⟩
    exact hx
  ext x
  simp only [ComponentSlabCover.piece, ComponentSlabCover.ambientPiece, Sum.elim_inl,
    ite_eq_right hn, preimage_empty, mem_empty_iff_false]
end ClosedSlabTests

namespace HypersurfaceSweepTests
open LeanCanny.Geometry LeanCanny.Algebra MvPolynomial Set

noncomputable def q : MvPolynomial Unit ℚ := X () ^ 2 - 1

-- A zero-dimensional regular hypersurface still has exceptional coordinate
-- values: both isolated points must be excluded from any regular sweep slab.
example : ∃ d : Polynomial ℚ, d ≠ 0 ∧ d.eval 1 = 0 ∧ d.eval (-1) = 0 := by
  obtain ⟨d, hd, hm⟩ := CoordinateCriticalValues.exists_annihilator q ()
  refine ⟨d, hd, ?_, ?_⟩
  · have he := CoordinateCriticalValues.eval_annihilator q () d hm (fun _ : Unit => (1 : ℚ))
      (by norm_num [q]) (by norm_num [q, pderiv_pow]) (by intro i hi; cases i; exact False.elim (hi rfl))
    simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] using he
  · have he := CoordinateCriticalValues.eval_annihilator q () d hm (fun _ : Unit => (-1 : ℚ))
      (by norm_num [q]) (by norm_num [q, pderiv_pow]) (by intro i hi; cases i; exact False.elim (hi rfl))
    simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] using he

noncomputable def circle : MvPolynomial (Fin 2) ℝ := X 0 ^ 2 + X 1 ^ 2

-- A non-base partial supplies the normal direction independently of the
-- swept coordinate, giving rank two on the regular part of a circle sweep.
example (x : Fin 2 → ℝ) (hx : x 1 ≠ 0) :
    Function.Surjective (fderiv ℝ
      (HypersurfaceSweep.combined (fun y => circle.eval y) (fun y => y 0)) x) := by
  apply PolynomialHypersurfaceSweep.surjective_combined_of_partial circle 0 1 x (by decide)
  simpa [circle, pderiv_pow, mul_ne_zero_iff] using hx

-- The source-coordinate identification keeps paths on the fixed level;
-- it is valid even when the sweep region has no interior.
example (q g : ℝ → ℝ) (c t : ℝ) :
    HypersurfaceSweep.Slab q g c ({t} : Set ℝ) ≃ₜ
      (HypersurfaceSweep.combined q g ⁻¹' HypersurfaceSweep.region c {t}) :=
  HypersurfaceSweep.slabHomeomorph q g c {t}

-- Slicing the circle at its first coordinate transfers the regularity test
-- to the actual polynomial in the one remaining coordinate.
example (y : CoordinateSlice.Index (0 : Fin 2) → ℝ)
    (hy : y ⟨1, by decide⟩ ≠ 0) :
    Function.Surjective (fderiv ℝ (fun z : CoordinateSlice.Index (0 : Fin 2) → ℝ =>
      (CoordinateSlice.family 0 circle).eval₂ (Polynomial.eval₂RingHom (RingHom.id ℝ) 0) z) y) := by
  apply CoordinateSlice.surjective_fderiv_family 0 circle (RingHom.id ℝ) 0 y
  have h := PolynomialHypersurfaceSweep.surjective_combined_of_partial circle 0 1
    (CoordinateSlice.restore 0 0 y) (by decide) (by
      simpa [circle, pderiv_pow, CoordinateSlice.restore, mul_ne_zero_iff] using hy)
  simpa only [eval₂_id] using h

example : Nat.card (CoordinateSlice.Index (0 : Fin 2)) = 1 := by
  have h := CoordinateSlice.card_index_add_one (0 : Fin 2)
  have he : Nat.card (Fin 2) = 2 := by norm_num [Nat.card_eq_fintype_card]
  rw [he] at h
  omega
end HypersurfaceSweepTests

namespace UniformSliceTests
open LeanCanny.Geometry LeanCanny.Algebra MvPolynomial Set
open ProjectionFiniteSpecialization

-- A circle sliced by its first coordinate has two spatial roots that merge
-- at the singular endpoint. The spatial equations keep that endpoint root.
private noncomputable def q : MvPolynomial Unit (Polynomial ℝ) :=
  X () ^ 2 + C (Polynomial.X ^ 2 - 1)

private def direction : DirectionIndex () → ℕ := fun _ => 0

example (t y : ℝ) :
    ParameterizedCriticalBranches.system q () direction (t, fun _ => y) = 0 ↔
      y ^ 2 + t ^ 2 = 1 := by
  rw [ParameterizedCriticalBranches.system_iff]
  constructor
  · intro h
    have he := h.1
    norm_num [q] at he
    linarith
  · intro h
    refine ⟨?_, ?_⟩
    · norm_num [q]
      linarith
    · intro i
      cases i
      simp [normalizedDirection]

example : ParameterizedCriticalBranches.system q () direction (1, fun _ => 0) = 0 := by
  apply (ParameterizedCriticalBranches.system_iff q () direction 1 (fun _ => 0)).mpr
  constructor
  · norm_num [q]
  · intro i
    cases i
    simp [normalizedDirection]

-- Simplicity is deliberately absent at the endpoint: the new spatial
-- family has a root there, but its spatial Jacobian vanishes.
example : (ProjectionCriticalFamily.spatialJacobian q ()
    (normalizedDirection () (fun i => (direction i : Polynomial ℝ)))).eval₂
      (Polynomial.evalRingHom 1) (fun _ => 0) = 0 := by
  simp [ProjectionCriticalFamily.spatialJacobian, ProjectionCriticalFamily.spatialEquation,
    q, Matrix.det_unique]

-- A recursively supplied component cover transfers to the actual endpoint
-- fiber without introducing labels or changing membership queries.
noncomputable example {ι I : Type} [Fintype ι] [DecidableEq ι]
    (p : MvPolynomial ι ℝ) (base : ι) (c t : ℝ)
    (C : ClopenPathCover {z : CoordinateSlice.Index base → ℝ |
      (CoordinateCriticalArcs.equation p base c).eval₂ (Polynomial.evalRingHom t) z = 0} I) :
    ClopenPathCover (CoordinateSlabCover.sweep p base c ⁻¹' {t}) I :=
  C.comap (CoordinateSlabCover.sliceHomeomorph p base c t)

end UniformSliceTests

namespace LowDimensionTests
open LeanCanny.Geometry LeanCanny.Algebra ETR Set Turing.MultiTapeTM

-- The zero-dimensional empty space is connected, but has no valid point query.
example : (Description.mk 0 .falsum).Connected := (ZeroDimension.connected_iff _).mpr (by decide)

example : ¬ (PointQuery.mk ⟨0, .falsum⟩ (.not .falsum) (.not .falsum)).Reachable := by
  rw [ZeroDimension.reachable_iff]
  rintro ⟨_, _, _, env, henv⟩
  exact henv

private def puncturedLine : Formula := .not (.eqZero (.var 0))

-- A missing point disconnects an unbounded Boolean realization.
example : ¬ (Description.mk 1 puncturedLine).Connected := by
  rw [OneDimension.connected_iff]
  rintro ⟨hw, hgap⟩
  apply hgap
  apply (OneDimension.gap_satisfiable puncturedLine hw).mpr
  refine ⟨-1, 1, 0, ?_⟩
  norm_num [OneDimension.realSet, puncturedLine, Formula.Holds, Formula.extend, Term.eval]

private def minusOne : Formula := .eqZero (.add (.var 0) (.const 1))
private def plusOne : Formula := .eqZero (.add (.var 0) (.const (-1)))

example : ¬ (PointQuery.mk ⟨1, puncturedLine⟩ minusOne plusOne).Reachable := by
  rw [OneDimension.point_iff]
  rintro ⟨_, _, _, _, _, hsep⟩
  apply hsep
  let env : ℕ → ℝ := fun k => if k = 0 then -1 else if k = 1 then 1 else 0
  refine ⟨env, (OneDimension.separation_holds puncturedLine minusOne plusOne
    (by decide) (by decide) (by decide) env).mpr ?_⟩
  norm_num [env, OneDimension.realSet, puncturedLine, minusOne, plusOne,
    Formula.Holds, Formula.extend, Term.eval]

-- Both low-dimensional algorithms are uniform native machine certificates.
example {α : Type} [Inhabited α] {enc : α ↪ List Bool} {p s t : α → Formula}
    (hp : ComputableTidilyInPolyTime (fun a => (p a).encode) enc encBits)
    (hs : ComputableTidilyInPolyTime (fun a => (s a).encode) enc encBits)
    (ht : ComputableTidilyInPolyTime (fun a => (t a).encode) enc encBits) :
    ComputableTidilyInPolySpace
      (fun a => @decide (PointQuery.mk ⟨1, p a⟩ (s a) (t a)).Reachable (Classical.propDecidable _))
      enc encBool := OneDimension.point_computable hp hs ht

end LowDimensionTests

namespace BoundedEliminantTests
open LeanCanny.Geometry LeanCanny.Algebra MvPolynomial Set

-- The eliminant is constructed from the equations, not supplied as a
-- certificate. Here the original square system is a translated identity.
example : ∃ H : Polynomial ℤ, H ≠ 0 ∧
    H.natDegree ≤ FixedWidthPolynomial.count 2 2 ∧ H.eval₂ (Int.castRingHom ℝ) 2 = 0 := by
  let q : Fin 1 → MvPolynomial (Fin 1) ℤ := fun i => X i - C 2
  let d : Fin 1 → ℕ := fun _ => 1
  let x : Fin 1 → ℝ := fun _ => 2
  have hD (i : Fin 1) : (q i).totalDegree ≤ d i := by
    change (X i - C (2 : ℤ)).totalDegree ≤ 1
    exact (MvPolynomial.totalDegree_sub _ _).trans (by rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]; decide)
  have hroot (i : Fin 1) : (q i).eval₂ (Int.castRingHom ℝ) x = 0 := by simp [q, x]
  have he : (fun y : Fin 1 → ℝ => fun j => (q j).eval₂ (Int.castRingHom ℝ) y) =
      (fun y => y - x) := by funext y j; simp [q, x]
  have hJac : (fderiv ℝ (fun y => fun j => (q j).eval₂ (Int.castRingHom ℝ) y) x).IsInvertible := by
    rw [he, fderiv_sub_const]
    change (fderiv ℝ (id : (Fin 1 → ℝ) → Fin 1 → ℝ) x).IsInvertible
    rw [fderiv_id]
    exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
  refine ⟨AffineCoordinateEliminant.polynomial q d 0 2, AffineCoordinateEliminant.ne_zero q d 0 2,
    AffineCoordinateEliminant.degree_le q d 0 2, ?_⟩
  exact AffineCoordinateEliminant.eval_eq_zero (Int.castRingHom ℝ) q d hD (by intro j; exact Nat.zero_lt_one)
    0 2 (by norm_num [Macaulay.level, AffineCoordinateSystem.degrees, d, Fin.sum_univ_succ]) x hroot hJac

-- A retained parameter may enter both coefficients. The lowest numerator
-- retains the equation u-t and its specialization, even at t=0.
private noncomputable def A : Matrix (Fin 1) (Fin 1) (Polynomial (Polynomial ℤ)) :=
  fun _ _ => Polynomial.X - Polynomial.C Polynomial.X

example : CharacteristicLowestBounds.lowest A = Polynomial.X - Polynomial.C Polynomial.X := by
  have hA : A 0 0 ≠ 0 := by
    intro hz
    have hc := congrArg (fun p : Polynomial (Polynomial ℤ) => p.coeff 1) hz
    simp [A] at hc
  have h0 : (AffineCharacteristic.subtractiveMatrix A).det.coeff 0 ≠ 0 := by
    simpa [AffineCharacteristic.subtractiveMatrix, Matrix.det_unique] using hA
  rw [CharacteristicLowestBounds.lowest, Polynomial.trailingCoeff_eq_coeff_zero h0]
  simp [A, AffineCharacteristic.subtractiveMatrix, Matrix.det_unique]

end BoundedEliminantTests

namespace SingularEliminantTests
open LeanCanny.Geometry LeanCanny.Algebra MvPolynomial Set

-- A double root has zero Jacobian, but the same constructed affine
-- coordinate eliminant still annihilates it over an algebraically closed field.
example {K : Type*} [Field K] [IsAlgClosed K] :
    ∃ H : Polynomial ℤ, H ≠ 0 ∧
      H.natDegree ≤ FixedWidthPolynomial.count 2 2 ∧ H.eval₂ (Int.castRingHom K) 0 = 0 := by
  let q : Fin 1 → MvPolynomial (Fin 1) ℤ := fun i => X i ^ 2
  let d : Fin 1 → ℕ := fun _ => 2
  have hD (i : Fin 1) : (q i).totalDegree ≤ d i := by
    simpa only [q, d, totalDegree_X, Nat.mul_one] using totalDegree_pow (X i : MvPolynomial (Fin 1) ℤ) 2
  have hfinite : {x : Fin 1 → K | ∀ j, (q j).eval₂ (Int.castRingHom K) x = 0}.Finite := by
    apply (finite_singleton (0 : Fin 1 → K)).subset
    intro x hx
    apply mem_singleton_iff.mpr
    funext i
    exact sq_eq_zero_iff.mp (by simpa [q] using hx i)
  refine ⟨AffineCoordinateEliminant.polynomial q d 0 2, AffineCoordinateEliminant.ne_zero q d 0 2,
    AffineCoordinateEliminant.degree_le q d 0 2, ?_⟩
  exact AffineCoordinateEliminant.eval_eq_zero_of_finite (Int.castRingHom K) q d hD
    (by intro j; exact Nat.zero_lt_two) 0 2
    (by norm_num [Macaulay.level, AffineCoordinateSystem.degrees, d, Fin.sum_univ_succ])
    hfinite (fun _ => 0) (by intro j; simp [q])

-- The zero set is an entire line. Finiteness of its first-coordinate image
-- suffices; finiteness of the spatial fiber is deliberately unavailable.
example : ∃ H : Polynomial ℤ, H ≠ 0 ∧
    H.natDegree ≤ CoerciveCoordinateEliminant.columnBound 2 2 ∧
    H.eval₂ (Int.castRingHom ℝ) 0 = 0 := by
  let q : MvPolynomial (Fin 2) ℤ := X 0 ^ 2
  have hD : q.totalDegree ≤ 2 := by
    simpa only [q, totalDegree_X, Nat.mul_one] using
      totalDegree_pow (X 0 : MvPolynomial (Fin 2) ℤ) 2
  have hfinite : {t : ℝ | ∃ x : Fin 2 → ℝ,
      q.eval₂ (Int.castRingHom ℝ) x = 0 ∧ x 0 = t}.Finite := by
    apply (finite_singleton (0 : ℝ)).subset
    rintro t ⟨x, hx, ht⟩
    have hx0 : x 0 = 0 := sq_eq_zero_iff.mp (by simpa [q] using hx)
    exact mem_singleton_iff.mpr (ht.symm.trans hx0)
  obtain ⟨H, hH, hd, _hm, hann⟩ := FiniteCoordinateAnnihilator.exists_bounded q 2 hD 0 hfinite
  exact ⟨H, hH, hd, hann (fun _ => 0) (by simp [q])⟩

end SingularEliminantTests

namespace SingularParameterTests
open LeanCanny.Geometry LeanCanny.Algebra MvPolynomial
set_option backward.isDefEq.respectTransparency false

-- At t=0 both equations vanish identically in the spatial variables. A
-- bounded exceptional factor still exists; the bad spatial fiber is a plane.
example : ∃ r : Polynomial ℤ, r ≠ 0 ∧
    r.natDegree ≤ CoerciveCoordinateEliminant.columnBound 3
      (2 * SingularParameterBounds.systemDegree 2 2) ∧
    coefficientMass r < 2 ^ SingularParameterBounds.factorMassExponent 2 2 0 ∧
    ∀ z : Fin 3 → ℝ, r.eval₂ (Int.castRingHom ℝ) (z 0) ≠ 0 → z 0 ≠ 0 := by
  let q : Fin 2 → MvPolynomial (Fin 3) ℤ := fun i => X 0 * X i.succ
  have hD (i : Fin 2) : (q i).totalDegree ≤ 2 := by
    exact (totalDegree_mul _ _).trans (by simp [totalDegree_X])
  have hb (i : Fin 2) : MvMass.mass (q i) ≤ 2 ^ 0 := by
    exact (MvMass.mul_le _ _).trans (by simp)
  have hj (z : Fin 3 → ℝ) :
      (SingularParameterBounds.jacobian q).eval₂ (Int.castRingHom ℝ) z = z 0 ^ 2 := by
    unfold SingularParameterBounds.jacobian
    rw [Matrix.det_fin_two]
    simp [q, pow_two]
  have hfinite : (SingularParameterBounds.SingularValues q).Finite := by
    apply (Set.finite_singleton (0 : ℝ)).subset
    rintro t ⟨z, _hz, hsing, ht⟩
    rw [hj] at hsing
    exact Set.mem_singleton_iff.mpr (ht.symm.trans (sq_eq_zero_iff.mp hsing))
  obtain ⟨r, hr, hd, hm, hgood⟩ :=
    SingularParameterBounds.exists_bounded_of_finite q 2 0 hD hb hfinite
  refine ⟨r, hr, hd, hm, ?_⟩
  intro z hz ht
  have he : ∀ j, (q j).eval₂ (Int.castRingHom ℝ) z = 0 := by simp [q, ht]
  have h := hgood z he hz
  rw [hj, ht, zero_pow (by decide : 2 ≠ 0)] at h
  exact h rfl

end SingularParameterTests

namespace NativeParameterQueryTests
open LeanCanny.Algebra LeanCanny.Encoding

-- Short target words retain their literal blocks. Parameter extraction must
-- not exchange the parameter and spatial positions.
#guard IntegerParameterCoefficientBits.parameter (fun _ => 2) id [false, true, true, false] == [false, true]
#guard IntegerParameterCoefficientBits.spatial (fun _ => 2) id [false, true, true, false] == [true]

-- Width zero has parameter exponent zero, and the spatial word still uses
-- canonical binary normalization. This case includes dimension-zero readers.
#guard IntegerParameterCoefficientBits.parameter (fun _ => 0) id [true, false] == []
#guard IntegerParameterCoefficientBits.spatial (fun _ => 0) id [true, false] == [true]

end NativeParameterQueryTests

namespace BoundedDirectionTests
open LeanCanny.Algebra LeanCanny.Encoding MvPolynomial
set_option backward.isDefEq.respectTransparency false

-- A very large degree value is retained in binary; only its bit length
-- determines the record block width. Short records are zero-padded.
#guard FermatCriticalDirection.read (fun _ => 1) (fun _ => 2 ^ 80)
  (pair (pair [] [true]) (BinaryNatCode.encode 0)) == [true]
#guard FermatCriticalDirection.read (fun _ => 1) (fun _ => 2 ^ 80)
  (pair (pair [] [true]) (BinaryNatCode.encode 1)) == []

private noncomputable def quarticLow : MvPolynomial (Fin 2) ℚ := C (-1)

private theorem quartic_regular (L : Type) [Field L] [Algebra ℚ L] (x : Fin 2 → L)
    (hx : aeval x (FermatCriticalHomogenization.polynomial quarticLow 1 4) = 0) :
    ∃ j, aeval x (pderiv j (FermatCriticalHomogenization.polynomial quarticLow 1 4)) ≠ 0 := by
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  by_contra h
  push Not at h
  have hz (j : Fin 2) : x j = 0 := by
    have hj := h j
    have he : aeval x (pderiv j (FermatCriticalHomogenization.polynomial quarticLow 1 4)) = 4 * x j ^ 3 := by
      simp [FermatCriticalHomogenization.pderiv_polynomial, quarticLow]
    rw [he] at hj
    exact (pow_eq_zero_iff (by decide : 3 ≠ 0)).mp ((mul_eq_zero.mp hj).resolve_left (by norm_num))
  have hp : aeval x (FermatCriticalHomogenization.polynomial quarticLow 1 4) = -1 := by
    simp [FermatCriticalHomogenization.polynomial, quarticLow, hz]
  rw [hp] at hx
  norm_num at hx

-- The quartic is regular even over complex extensions, but the coordinate
-- direction has a multiple critical root at (1,0). The constructed direction
-- must therefore have a nonzero non-base entry.
example : ∃ v : ℕ, v ≤ FermatBoundedCriticalDirection.allowance 1 4 ∧ v ≠ 0 := by
  obtain ⟨v, hv, hgood⟩ := FermatBoundedCriticalDirection.exists_bounded quarticLow 1 one_ne_zero 4
    (by norm_num [quarticLow, totalDegree_C]) (by decide) quartic_regular
  refine ⟨v 0, hv 0, ?_⟩
  intro hv0
  have hvall (i : Fin 1) : v i = 0 := by simpa only [Subsingleton.elim i 0] using hv0
  let x : Fin 2 → ℚ := Fin.cons 1 (fun _ => 0)
  let φ := eval₂Hom (algebraMap ℚ ℚ) (fun i => (v i : ℚ))
  have hψC : φ.comp C = algebraMap ℚ ℚ := by ext; simp [φ]
  have hx (j : Fin 2) : (FermatCriticalBadSystem.equations quarticLow 1 4 j).eval₂ φ x = 0 := by
    fin_cases j <;> norm_num [FermatCriticalBadSystem.equations, FermatCriticalHomogenization.spatial,
      FermatCriticalHomogenization.polynomial, FermatCriticalHomogenization.pderiv_polynomial,
      quarticLow, φ, x, hvall, Fin.sum_univ_succ, Pi.single_apply]
  have hj : (FermatCriticalBadSystem.jacobian quarticLow 1 4).eval₂ φ x = 0 := by
    rw [FermatCriticalGeneric.eval_jacobian φ hψC, Matrix.det_fin_two]
    norm_num [GenericProjectionJacobian.spatial, FermatCriticalHomogenization.pderiv_polynomial,
      FermatCriticalGeneric.direction, quarticLow, φ, x, hvall, Fin.sum_univ_succ, Pi.single_apply]
  exact hgood ℚ x hx hj

end BoundedDirectionTests

namespace ConstructedRegularLevelTests
open LeanCanny.Algebra LeanCanny.Geometry MvPolynomial

-- The width formula includes the value coordinate and its homogeneous
-- coordinate row. Binary source values can be much larger than these widths.
#guard FermatRegularSource.width 0 2 = 2
#guard FermatRegularSource.width 0 (2 ^ 80) < 90
#guard (CriticalRegularLevel.exponent 1 (2 ^ 80)
  (FermatRegularSource.width 0 (2 ^ 80)) (2 ^ 80)).size < 2000

-- The scaling reader receives the actual modulus. Its modular-power call
-- must convert to the predecessor-modulus protocol, including modulus one.
#guard FixedWidthDyadicScaleBits.factor (fun _ => 80) (fun _ => BinaryNatCode.encode 5) [] == [true]
#guard FixedWidthDyadicScaleBits.factor (fun _ => 80) (fun _ => BinaryNatCode.encode 1) [] == []

-- The origin is a degenerate critical point of X^4. It must still contribute
-- its value to the bounded annihilator; an invertible-gradient-Jacobian
-- argument would miss it.
example :
    let p := FermatCriticalHomogenization.polynomial (0 : MvPolynomial (Fin 1) ℤ) 1 4
    let W := FermatRegularSource.width 0 4
    CriticalValueBounds.polynomial p 4 W ≠ 0 ∧
      (CriticalValueBounds.polynomial p 4 W).eval₂ (Int.castRingHom ℚ) 0 = 0 := by
  dsimp only
  refine ⟨CriticalValueBounds.ne_zero _ _ _, ?_⟩
  have he := CriticalValueBounds.eval_eq_zero_fermat_extension (Int.castRingHom ℚ)
    (0 : MvPolynomial (Fin 1) ℤ) 1 4 (FermatRegularSource.width 0 4)
    (by simp) (by norm_num) (by decide) (Nat.lt_size_self _) (fun _ => 0)
    (fun _ => by simp [FermatCriticalHomogenization.pderiv_polynomial])
  have hvalue : (FermatCriticalHomogenization.polynomial (0 : MvPolynomial (Fin 1) ℤ) 1 4).eval₂
      (Int.castRingHom ℚ) (fun _ => 0) = 0 := by simp [FermatCriticalHomogenization.polynomial]
  rw [hvalue] at he
  exact he

end ConstructedRegularLevelTests

namespace SweepCertificateTests
open LeanCanny.Algebra LeanCanny.Encoding MvPolynomial

-- With no direction coordinates, the one retained block is still the sweep
-- sample. The next block is outside the record's dimension.
#guard FermatSweepCertificate.read (fun _ => 0) (fun _ => 2 ^ 80)
  (pair (pair [] [true]) (BinaryNatCode.encode 0)) == [true]
#guard FermatSweepCertificate.read (fun _ => 0) (fun _ => 2 ^ 80)
  (pair (pair [] [true]) (BinaryNatCode.encode 1)) == []

private noncomputable def complexOnlyRows (_ : Fin 2) : MvPolynomial (Fin 2) ℚ := X 0 ^ 2 + X 1 ^ 2

-- A real-root emptiness test would accept this fiber, but it has a normalized
-- complex root. Projective certificates must test complex roots.
example : ∀ x : Fin 2 → ℝ, (∀ j, (complexOnlyRows j).eval₂ (algebraMap ℚ ℝ) x = 0) → x = 0 := by
  intro x hx
  have he : x 0 ^ 2 + x 1 ^ 2 = 0 := by simpa [complexOnlyRows] using hx 0
  have h0 : x 0 = 0 := by nlinarith [sq_nonneg (x 1), sq_nonneg (x 0)]
  have h1 : x 1 = 0 := by nlinarith [sq_nonneg (x 1), sq_nonneg (x 0)]
  funext i
  fin_cases i <;> assumption

example : ∃ y : Fin 2 → ℂ, y 0 = 1 ∧ ∀ j, (complexOnlyRows j).eval₂ (algebraMap ℚ ℂ) y = 0 := by
  refine ⟨Fin.cons 1 (fun _ => Complex.I), rfl, ?_⟩
  intro j
  simp [complexOnlyRows, Complex.I_sq]

end SweepCertificateTests

namespace ComplexCircuitTests
open LeanCanny.ETR
open LeanCanny.ETR.ComplexCircuit
open scoped Classical

private def imaginaryRoot : List Gate := [.constant 0 (-1), .mul 0 1 1, .add 2 1 1, .zero 3]

-- Every gate constructor is compiled without expanding the shared wires.
#guard compile (encode imaginaryRoot) == SumSquares.listBits (equations imaginaryRoot)
#guard constantGateBits 3 (Term.const (-(2 ^ 80))).toData.toBits == (Gate.constant 3 (-(2 ^ 80))).encode
#guard arithmeticGateBits 2 2 1 1 == (Gate.mul 2 1 1).encode
#guard zeroGateBits 3 == (Gate.zero 3).encode

private theorem imaginaryRoot_sat : Satisfiable imaginaryRoot := by
  let env : ℕ → ℂ := fun i => if i = 0 then -1 else if i = 1 then Complex.I
    else if i = 2 then Complex.I + Complex.I else 0
  refine ⟨env, ?_⟩
  intro g hg
  simp only [imaginaryRoot, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp [Gate.Holds, env, Complex.I_mul_I]

-- The network has a nonreal solution. Adding a zero constraint on that same
-- wire must make it inconsistent; shared wire identity is essential here.
example : feasible (encode imaginaryRoot) = [true] := by
  rw [feasible_encode, decide_eq_true imaginaryRoot_sat]

example : empty (encode (imaginaryRoot ++ [.zero 1])) = [true] := by
  rw [empty_encode]
  have hn : ¬ Satisfiable (imaginaryRoot ++ [.zero 1]) := by
    rintro ⟨env, h⟩
    have hc := h (.constant 0 (-1)) (by simp [imaginaryRoot])
    have hm := h (.mul 0 1 1) (by simp [imaginaryRoot])
    have hz := h (.zero 1) (by simp)
    simp only [Gate.Holds] at hc hm hz
    rw [hz, mul_zero] at hm
    rw [hm] at hc
    norm_num at hc
  rw [decide_eq_true hn]

end ComplexCircuitTests

namespace SharedPowerTests
open LeanCanny.ETR
open LeanCanny.ETR.ComplexCircuit
open scoped Classical

-- Little-endian exponents, the zero exponent, and a long binary exponent.
#guard Nat.fromBitsLE [true, true, false, true] == 11
#guard Power.gates 0 1 [] == [Gate.constant 1 1]
#guard (Power.gates 0 1 (List.replicate 80 true)).length == 161
#guard compile (encode (Power.gates 0 1 [true, false, true])) ==
  SumSquares.listBits (equations (Power.gates 0 1 [true, false, true]))
#guard Dyadic.gates 0 1 [] == [.constant 1 2, .constant 2 1, .mul 3 0 2,
  .constant 4 (-1), .add 5 3 4]

example (env : ℕ → ℂ) (bits : List Bool) :
    ∃ out : ℕ → ℂ, out 0 = env 0 ∧
      (∀ g ∈ Power.gates 0 1 bits, g.Holds out) ∧
      out (Power.output 1 bits) = env 0 ^ Nat.fromBitsLE bits := by
  obtain ⟨out, hp, hg, hv⟩ := Power.exists_completion 0 1 (by decide) bits env
  exact ⟨out, hp 0 (by decide), hg, hv⟩

-- Zero exponent computes p - 1, including when the source value is zero.
example (env : ℕ → ℂ) (h : ∀ g ∈ Dyadic.gates 0 1 [], g.Holds env) :
    env 5 = env 0 - 1 := by
  simpa [Dyadic.output, Dyadic.productWire, Power.output, Nat.fromBitsLE, Nat.fromBits]
    using Dyadic.sound 0 1 [] env h

-- Each occurrence of the repeated input contributes to the product rule.
#guard Differential.operation 1 (.mul 0 0) ==
  [.mul 0 0, .mul 3 0, .mul 0 3, .add 5 6]

example (env : ℕ → ℂ)
    (h : ∀ g ∈ StraightLine.gates 4 (Differential.operation 1 (.mul 0 0)), g.Holds env) :
    env 4 = env 0 * env 0 ∧ env 7 = env 3 * env 0 + env 0 * env 3 :=
  Differential.operation_sound 1 (.mul 0 0) env h

private def squareProgram : List Operation := [.mul 0 0, .add 0 1]

#guard Transform.run Differential.gateBits (encode (StraightLine.gates 1 squareProgram)) ==
  encode (StraightLine.gates 4 (Differential.program 1 squareProgram))
#guard Transform.run Differential.gateBits (encode [.constant 2 (-7), .zero 1]) ==
  encode ([.constant 2 (-7), .zero 1].flatMap Differential.gate)

example (start : ℕ) (ops : List Operation) (hw : StraightLine.WellFormed start ops) :
    StraightLine.WellFormed (4 * start) (Differential.program start ops) :=
  Differential.wellFormed start ops hw

end SharedPowerTests

namespace SourceCircuitTests
open LeanCanny.ETR
open LeanCanny.ETR.ComplexCircuit
open MvPolynomial
open scoped Classical

private def squareMinusTwo : Term := .add (.mul (.var 0) (.var 0)) (.const (-2))

-- The sequential native writer agrees with the independent recursive circuit.
#guard Source.gates 3 squareMinusTwo == [.mul 3 0 0, .constant 4 (-2), .add 5 3 4]
#guard Source.Machine.compile squareMinusTwo.toData.toBits ==
  encode (Source.gates squareMinusTwo.toData.size squareMinusTwo)
#guard Source.Machine.outputIndex squareMinusTwo.toData.toBits == squareMinusTwo.toData.size + 2
#guard Source.Machine.nextIndex squareMinusTwo.toData.toBits == squareMinusTwo.toData.size + 3

-- A variable-only circuit allocates no gates. Invalid syntax uses the total
-- source view's zero term; the connectivity input validator is separate.
#guard Source.Machine.compile (Term.var 37).toData.toBits == encode []
#guard Source.Machine.outputIndex (Term.var 37).toData.toBits == 37
#guard Source.Machine.compile [] == encode (Source.gates 10 (.const 0))

example (t : Term) (x : ℕ → ℂ) :
    ∃ env : ℕ → ℂ, (∀ i < t.toData.size, env i = x i) ∧
      (∀ g ∈ Source.gates t.toData.size t, g.Holds env) ∧
      env (Source.output t.toData.size t) = t.eval x :=
  Source.exists_completion t.toData.size t (Term.arity_le_dataSize t) x

example (x env : ℕ → ℂ)
    (hi : ∀ i < squareMinusTwo.toData.size,
      env (Differential.valueWire i) = x i ∧
        env (Differential.derivativeWire i) = if i = 0 then 1 else 0)
    (hg : ∀ g ∈ StraightLine.gates (Differential.valueWire squareMinusTwo.toData.size)
      (Differential.program squareMinusTwo.toData.size
        (Source.program squareMinusTwo.toData.size squareMinusTwo)), g.Holds env) :
    env (Differential.derivativeWire (Source.output squareMinusTwo.toData.size squareMinusTwo)) = 2 * x 0 := by
  have h := Source.derivative_sound squareMinusTwo.toData.size squareMinusTwo
    (Term.arity_le_dataSize _) 0 x env hi hg
  have hp : pderiv 0 squareMinusTwo.toPolynomial = X 0 + X 0 := by
    simp only [squareMinusTwo, Term.toPolynomial, map_add, pderiv_mul, pderiv_X_self,
      pderiv_C, one_mul, mul_one, add_zero]
  simpa only [hp, eval₂_add, eval₂_X, two_mul] using h.2

-- The source syntax, binary exponent and fresh-wire metadata all contribute
-- to the native evaluator; no supplied polynomial evaluator is assumed.
example : SpaceFunction (fun bits => [decide (∃ env : ℕ → ℂ,
    (2 : ℂ) ^ Nat.fromBitsLE (pairSnd bits) * (TermView.term (pairFst bits)).eval env - 1 = 0)]) :=
  Source.scaledTerm_evaluator pairFst_mem_FP pairSnd_mem_FP

end SourceCircuitTests

namespace BadRootChartTests
open LeanCanny.Algebra
open MvPolynomial
open scoped Classical Matrix

-- The empty square Jacobian has no normalized nonzero kernel chart.
example : ¬ ∃ i : Fin 0, ∃ v : Fin 0 → ℂ, v i = 1 ∧ (0 : Matrix (Fin 0) (Fin 0) ℂ) *ᵥ v = 0 := by
  simp

-- Normalizing over C retains kernel vectors with nonreal entries.
private def imaginaryMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![1, Complex.I; Complex.I, -1]

example : ∃ i : Fin 2, ∃ v : Fin 2 → ℂ, v i = 1 ∧ imaginaryMatrix *ᵥ v = 0 := by
  apply (JacobianKernelCharts.det_zero_iff imaginaryMatrix).mp
  norm_num [imaginaryMatrix, Matrix.det_fin_two, Complex.I_sq]

-- A direction can have a bad root at infinity even with a nonzero constant
-- lower term. The projective test must retain its separate infinity queries.
example : ¬ (∀ y : Fin 3 → ℂ,
    (∀ j, (FermatCriticalBadSpecialization.rows (C 1 : MvPolynomial (Fin 2) ℚ) 1 3
      (fun _ : Fin 1 => 1) j).eval₂ (algebraMap ℚ ℂ) y = 0) → y = 0) := by
  rw [FermatCriticalBadSpecialization.root_free_iff_kernel_infinity_charts
    (algebraMap ℚ ℂ) (C 1 : MvPolynomial (Fin 2) ℚ) 1 3 (by simp) (by decide)]
  intro h
  apply h.2 (0 : Fin 2)
  refine ⟨Fin.cons 1 (fun _ : Fin 1 => -1), rfl, ?_⟩
  intro j
  fin_cases j <;> norm_num [FermatCriticalInfinity.native, eval₂_mul, eval₂_C, eval₂_sum,
    eval₂_pow, eval₂_X, eval₂_sub, Fin.sum_univ_succ]

end BadRootChartTests

namespace InfinityCircuitTests
open LeanCanny.ETR
open LeanCanny.ETR.ComplexCircuit
open scoped Classical BigOperators

-- An exponent with 80 bits still needs only two arithmetic operations per bit
-- in each block; none of its numerical value is expanded into unary.
#guard (Infinity.prefixProgram 3 (List.replicate 80 true) (fun _ => 0) 3).length == 499
#guard compile (encode (Infinity.query 1 [] (fun _ => 0) 0)) ==
  SumSquares.listBits (equations (Infinity.query 1 [] (fun _ => 0) 0))

-- The normalized cubic direction has a genuine infinity root (1,-1).
example : Satisfiable (Infinity.query 2 [false, true] (fun _ => 1) 0) := by
  rw [Infinity.query_satisfiable_fin 1 [false, true] (fun _ => 1) ⟨0, by decide⟩]
  have hb : Nat.fromBitsLE [false, true] = 2 := by decide
  refine ⟨Fin.cons 1 (fun _ : Fin 1 => -1), rfl, ?_, ?_⟩
  · norm_num [hb, Fin.sum_univ_succ]
  · intro j
    fin_cases j
    norm_num [hb]

-- A single normalized input cannot have zero power sum, also for the empty
-- exponent word (N-1=0). Completeness must preserve the original input wire.
example : ¬ Satisfiable (Infinity.query 1 [] (fun _ => 0) 0) := by
  rw [Infinity.query_satisfiable_fin 0 [] (fun _ => 0) ⟨0, by decide⟩]
  rintro ⟨x, hx, hs, _⟩
  have hx0 : x (0 : Fin 1) = 1 := by
    have he : (0 : Fin 1) = ⟨0, by decide⟩ := Subsingleton.elim _ _
    exact (congrArg x he).trans hx
  simp [Nat.fromBitsLE, Nat.fromBits, hx0] at hs

example {dim degree index : List Bool → ℕ} {record : List Bool → List Bool}
    (hd : UnaryFn dim) (hN : BinaryFn degree) (hi : UnaryFn index) (hr : record ∈ FP) :
    SpaceFunction (LeanCanny.Encoding.FermatInfinityQuery.empty dim degree index record) :=
  LeanCanny.Encoding.FermatInfinityQuery.empty_evaluator hd hN hi hr

end InfinityCircuitTests

namespace HessianCircuitTests
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit MvPolynomial
open scoped Classical

private def mixedTerm : Term := .mul (.var 0) (.mul (.var 1) (.var 1))

-- The executable double transformation matches the independent operation list.
#guard Transform.run Differential.gateBits
    (Transform.run Differential.gateBits (encode (Source.gates 2 mixedTerm))) ==
  encode (StraightLine.gates 32 (Differential.secondProgram 2 (Source.program 2 mixedTerm)))

-- Fresh seeds cover the two first-derivative slots even for a variable-only
-- source with no arithmetic operations. The mixed derivative starts at zero.
#guard Hessian.seedOp 2 0 0 0 == .add 0 2
#guard Hessian.seedOp 2 0 0 3 == .constant 1
#guard Hessian.seedOp 2 0 0 12 == .constant 1
#guard Hessian.seedOp 2 0 0 15 == .constant 0
#guard (Hessian.program 2 3 2 0 1 []).length == 32
#guard (HessianFamily.program 2 3 2 2 (Source.program 2 mixedTerm) 4).length == 256

-- Relocation handles all gate constructors, preserves long negative binary
-- constants, and accepts an empty circuit.
private def shiftGates : List Gate :=
  [.constant 1 (-(2 ^ 80 + 3)), .add 2 0 1, .mul 3 2 2, .zero 3]
#guard WireShift.run (pair (List.replicate 7 true) (encode shiftGates)) ==
  encode (shiftGates.map (Gate.shift 7))
#guard WireShift.run (pair (List.replicate 7 true) (encode [])) == encode []

example : StraightLine.WellFormed 3 (HessianFamily.program 2 3 2 2 (Source.program 2 mixedTerm) 4) :=
  HessianFamily.wellFormed 2 3 2 2 _ 4 (by decide) (by decide)
    (Source.wellFormed 2 mixedTerm (by decide))

-- The original source has mixed derivative 2*x_1, rather than a derivative
-- of an auxiliary wire treated as an independent variable.
example : ∃ env : ℕ → ℂ,
    (∀ g ∈ StraightLine.gates 3 (Hessian.program 2 3 2 0 1 (Source.program 2 mixedTerm)), g.Holds env) ∧
      env 66 = 10 := by
  let x : ℕ → ℂ := fun i => if i = 0 then 3 else if i = 1 then 5 else 0
  obtain ⟨env, _, hg, hv⟩ := Hessian.source_exists_completion 2 3 2 0 1 mixedTerm
    (by decide) (by decide) (by decide) x (by norm_num [x])
  have hp : pderiv 1 (pderiv 0 mixedTerm.toPolynomial) = X 1 + X 1 := by
    simp [mixedTerm, Term.toPolynomial, pderiv_X]
  refine ⟨env, hg, ?_⟩
  have h := hv.2.2.2
  change env 66 = _ at h
  norm_num [hp, eval₂_add, eval₂_X, x] at h
  exact h

end HessianCircuitTests

namespace KernelRowCircuitTests
open LeanCanny.ETR.ComplexCircuit

-- One row computes ((entry-2*first)*u, value-2*baseGradient).
#guard StraightLine.gates 4 (KernelRow.program 3 4 2 1 0 1 (-2) (fun _ => 0) (fun _ => 1)) ==
  [.constant 4 (-2), .mul 5 4 0, .add 6 1 5, .mul 7 6 2,
    .add 8 3 7, .mul 9 4 1, .add 10 0 9]

-- The empty column range retains the shared zero accumulator.
#guard KernelRow.sumWire 3 4 0 == 3
#guard (KernelRow.program 3 4 2 0 0 1 (-2) (fun _ => 0) (fun _ => 1)).length == 3

example : StraightLine.WellFormed 4 (KernelRow.program 3 4 2 1 0 1 (-2) (fun _ => 0) (fun _ => 1)) :=
  KernelRow.wellFormed 3 4 2 1 0 1 (-2) _ _ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

end KernelRowCircuitTests

namespace CompleteKernelCircuitTests
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit MvPolynomial
open scoped Classical

private def square : Term := .mul (.var 0) (.var 0)
private def twoSquares : Term := .add square (.mul (.var 1) (.var 1))

-- The complete one-variable query includes the initialized derivative copy,
-- both row outputs, and the normalized nonzero kernel coordinate.
#guard (CriticalKernel.query 1 1 (Source.program 1 square) (Source.output 1 square) (fun _ => 0) 0).length == 43
#guard (CriticalKernel.query 0 0 [] 0 (fun _ => 0) 0).length == 2
#guard (CriticalKernel.query 2 2 (Source.program 2 twoSquares) (Source.output 2 twoSquares) (fun _ => 1) 1).length == 348

-- The zero root of x^2 is singular, so a normalized kernel exists.
example : Satisfiable (CriticalKernel.query 1 1 (Source.program 1 square)
    (Source.output 1 square) (fun _ => 0) 0) := by
  rw [CriticalKernel.source_satisfiable 1 1 square (by decide) (fun _ => 0) 0 (by decide)]
  refine ⟨fun _ => 0, fun _ => 1, rfl, fun j hj => ?_⟩
  have he : j = 0 := by omega
  subst j
  norm_num [CriticalKernel.criticalValue, CriticalKernel.kernelValue, CriticalKernel.selectedPolynomial,
    CriticalKernel.entryPolynomial, CriticalKernel.coefficient, square, Term.toPolynomial, pderiv_mul, pderiv_X_self]

-- In two coordinates, the zero root and kernel (1,1) satisfy the direction-1
-- row: its Hessian combination is (-2,2), whose dot product is zero.
example : Satisfiable (CriticalKernel.query 2 2 (Source.program 2 twoSquares)
    (Source.output 2 twoSquares) (fun _ => 1) 1) := by
  rw [CriticalKernel.source_satisfiable 2 2 twoSquares (by decide) (fun _ => 1) 1 (by decide)]
  refine ⟨fun _ => 0, fun _ => 1, rfl, fun j hj => ?_⟩
  interval_cases j <;>
    norm_num [CriticalKernel.criticalValue, CriticalKernel.kernelValue, CriticalKernel.selectedPolynomial,
      CriticalKernel.entryPolynomial, CriticalKernel.coefficient, twoSquares, square,
      Term.toPolynomial, pderiv_X, Finset.sum_range_succ]

-- A variable-only source allocates no original arithmetic gates, but its
-- derivative is one and rules out every normalized kernel at its zero root.
example : ¬ Satisfiable (CriticalKernel.query 1 1 (Source.program 1 (.var 0))
    (Source.output 1 (.var 0)) (fun _ => 0) 0) := by
  rw [CriticalKernel.source_satisfiable 1 1 (.var 0) (by decide) (fun _ => 0) 0 (by decide)]
  rintro ⟨x, u, hu, hr⟩
  have h := (hr 0 (by decide)).2
  simp [CriticalKernel.kernelValue, CriticalKernel.entryPolynomial, CriticalKernel.coefficient,
    Term.toPolynomial, hu] at h

-- The native source reader and direction literal writer are charged by the
-- evaluator, including when the supplied syntax is malformed.
example : SpaceFunction (CriticalKernel.sourceBad pairFst (fun _ => 1) (fun _ => 0) (fun _ _ => 0)) :=
  CriticalKernel.sourceBad_evaluator pairFst_mem_FP (UnaryFn.const 1) (UnaryFn.const 0)
    (constFn_mem_FP (Term.const 0).toData.toBits)

end CompleteKernelCircuitTests
