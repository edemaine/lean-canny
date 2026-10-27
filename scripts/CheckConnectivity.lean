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

namespace SampledSourceCircuitTests
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit MvPolynomial
open scoped Classical

private def low : Term := .mul (.var 0) (.var 1)

-- Freezing variable zero redirects it to the computed sample. Variable one
-- becomes spatial coordinate zero; the multiplication output stays fresh.
#guard StraightLine.gates 2 (FrozenSource.program 2 2 7 low) == [.constant 2 7, .mul 3 2 0]
#guard Reindex.run FrozenSource.Encoded.index
    (pair (pair (List.replicate 2 true) (List.replicate 2 true)) (encode (Source.gates 2 low))) ==
  encode [.mul 3 2 0]
#guard (FrozenSource.program 1 1 7 (.var 0)).length == 1
#guard FrozenSource.output 1 1 (.var 0) == 1

-- Two 80-bit exponent words still produce only 503 source operations.
#guard (SampledSource.program 2 2 1 2 1 low (List.replicate 80 true) (List.replicate 80 true)).length == 503

-- With sample2, spatial coordinate3, N=3, a=1, and E=2, the actual shared
-- source computes 4*(2*3+2^3+3^3)-1=163.
example : ∃ env : ℕ → ℂ,
    (∀ g ∈ StraightLine.gates 2 (SampledSource.program 2 2 1 2 1 low [false, true] [false, true]), g.Holds env) ∧
      env (SampledSource.output 2 1 low [false, true] [false, true]) = 163 := by
  let ops := SampledSource.program 2 2 1 2 1 low [false, true] [false, true]
  let wire := Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) 2 ops
  let x : ℕ → ℂ := fun _ => 3
  have hw := SampledSource.wellFormed 2 2 1 2 1 low [false, true] [false, true] (by decide) (by decide) (by decide)
  have hr := Differential.symbolicRun_realizes (fun i => (X i : MvPolynomial ℕ ℤ)) 2 ops hw
  refine ⟨fun i => (wire i).eval₂ (Int.castRingHom ℂ) x, Differential.realizes_gates_eval wire 2 ops hr x, ?_⟩
  change (Differential.symbolicRun _ 2 _ _).eval₂ _ x = _
  rw [SampledSource.symbolic_output 2 2 1 2 1 low [false, true] [false, true] (by decide) (by decide) (by decide),
    SampledSource.polynomial_eval]
  norm_num [low, Term.eval, FrozenSource.inputs, x, Nat.fromBitsLE, Nat.fromBits]

example : SpaceFunction (SampledSource.kernelBad pairFst pairSnd pairSnd
    (fun c => c.length + 10) (fun _ => 1) (fun _ => 0) (fun _ => 2) (fun _ => 1) (fun _ _ => 0)) :=
  SampledSource.kernelBad_evaluator pairFst_mem_FP ((UnaryFn.length id_mem_FP).add (UnaryFn.const 10))
    (UnaryFn.const 1) (UnaryFn.const 0) (constFn_mem_FP (Term.const 2).toData.toBits)
    (constFn_mem_FP (Term.const 1).toData.toBits) pairSnd_mem_FP pairSnd_mem_FP (constFn_mem_FP (Term.const 0).toData.toBits)

end SampledSourceCircuitTests

namespace NativeSweepCertificateTests
open LeanCanny.ETR LeanCanny.Encoding MvPolynomial
open FermatSweepCertificate
open scoped Classical

-- The complete checker charges the actual source and record readers, as well
-- as binary degree and regularization exponents, on arbitrary input words.
example : SpaceFunction (FermatValidity.check pairFst pairSnd (fun _ => 1) (fun _ => 3)
    (fun _ => 2) (fun _ => 1)) :=
  FermatValidity.evaluator pairFst_mem_FP pairSnd_mem_FP (UnaryFn.const 1) (BinaryFn.const 3)
    (BinaryFn.const 2) (constFn_mem_FP (Term.const 1).toData.toBits)

-- Retaining the selected record with the input permits subsequent native
-- field reads. The record search itself requires only polynomial space.
example {source : List Bool → List Bool} {dim degree mass : List Bool → ℕ}
    (ht : source ∈ FP) (hd : UnaryFn dim) (hN : BinaryFn degree) (hb : BinaryFn mass) :
    SpaceFunction (fun c => pair c
      (FermatDirectionChoice.record source dim degree (FermatDirectionChoice.regularExponent dim degree mass)
        (fun _ => 1) c)) :=
  (FermatDirectionChoice.regular_evaluator ht hd hN hb
    (constFn_mem_FP (Term.const 1).toData.toBits)).withInput

example (source : List Bool → List Bool) (dim degree mass : List Bool → ℕ)
    (c : List Bool) (low : MvPolynomial (Fin (dim c + 2)) ℤ)
    (ht : (TermView.term (source c)).toPolynomial = rename Fin.val low)
    (hlow : low.totalDegree < degree c) (hN : 1 < degree c)
    (hm : LeanCanny.Algebra.MvMass.mass
      (LeanCanny.Algebra.FermatCriticalHomogenization.polynomial low 1 (degree c)) ≤ 2 ^ mass c) :
    Valid ((LeanCanny.Geometry.IntegerRegularSource.lower low (degree c) (mass c)).map (Int.castRingHom ℚ))
      (LeanCanny.Geometry.IntegerRegularSource.leading (dim c + 1) 1 (degree c) (mass c) : ℚ) (degree c)
      (FermatDirectionChoice.record source dim degree (FermatDirectionChoice.regularExponent dim degree mass)
        (fun _ => 1) c) :=
  FermatDirectionChoice.regular_record_valid source dim degree mass (fun _ => 1) c low ht (by decide) hlow hN hm

-- A truncated record still decodes direction one. Its cubic infinity root
-- (1,-1) must make the complete checker reject, independently of affine roots.
example (c : List Bool) :
    FermatValidity.check (fun _ => (Term.const 0).toData.toBits) (fun _ => [true])
      (fun _ => 1) (fun _ => 3) (fun _ => 0) (fun _ => 1) c ≠ [true] := by
  intro h
  have hc := FermatValidity.charts_correct (fun _ => (Term.const 0).toData.toBits) (fun _ => [true])
    (fun _ => 1) (fun _ => 3) (fun _ => 0) (fun _ => 1) c 0 (by simp [TermView.term_toBits, Term.toPolynomial])
    (by decide) (by decide) 0 (by decide)
  have hall : ∀ k < 2, FermatValidity.charts (fun _ => (Term.const 0).toData.toBits) (fun _ => [true])
      (fun _ => 1) (fun _ => 3) (fun _ => 0) (fun _ => 1) (pair c (List.replicate k true)) = [true] := by
    simpa only [FermatValidity.check, List.cons.injEq, and_true, decide_eq_true_eq] using h
  apply ((hc.mp (hall 0 (by decide))).2)
  rw [infinity_bad_iff_reduced _ (dyadicLeading_ne_zero 1 (by decide) 0) 3 (by decide)]
  have hd : direction 1 3 [true] (0 : Fin 1) = 1 := by decide
  refine ⟨Fin.cons 1 (fun _ : Fin 1 => -1), rfl, ?_, ?_⟩
  · norm_num [Fin.sum_univ_succ]
  · intro j
    fin_cases j
    norm_num [hd]

-- A zero-length bounded scan accepts even when every child rejects.
example (c : List Bool) :
    [decide (∀ k < 0, (fun _ : List Bool => [false]) (pair c (List.replicate k true)) = [true])] = [true] := by
  simp

end NativeSweepCertificateTests

namespace EncodedSweepPreparationTests
open LeanCanny.ETR LeanCanny.Encoding MvPolynomial
open FermatTermPreparation FermatSweepCertificate

-- Degree and mass controls come from the term; they are not supplied by a
-- semantic oracle or as separate complexity hypotheses.
example : SpaceFunction (FermatTermPreparation.record pairFst (fun c => (pairSnd c).length)) :=
  FermatTermPreparation.evaluator pairFst_mem_FP (UnaryFn.length pairSnd_mem_FP)

-- The one spatial variable fits the two-variable original source at dim=0.
-- Validity therefore needs no supplied degree, mass, or regularity promise.
example (c : List Bool) :
    let source := fun _ : List Bool => (Term.var 1).toData.toBits
    Valid ((LeanCanny.Geometry.IntegerRegularSource.lower (low source (fun _ => 0) c)
        (degree source c) (mass source (fun _ => 0) c)).map (Int.castRingHom ℚ))
      (LeanCanny.Geometry.IntegerRegularSource.leading 1 1 (degree source c) (mass source (fun _ => 0) c) : ℚ)
      (degree source c) (FermatTermPreparation.record source (fun _ => 0) c) := by
  dsimp only
  apply FermatTermPreparation.record_valid
  simp only [TermView.term_toBits, Term.arity, le_refl]

-- Normalization also gives total metadata for malformed encoded syntax.
example : degree (fun _ : List Bool => []) [] = 42 := by
  have ht : TermView.term [] = .const 0 := by
    simp only [TermView.term]
    decide
  simp only [degree, halfDegree, size, ht, Term.dataSize_const_zero]

end EncodedSweepPreparationTests

namespace CompactComponentLimitTests
open LeanCanny.Geometry.CompactSublevelComponents Set

private def energy (x : ℝ) : ℝ := (x ^ 2 - 1) ^ 2

-- Both zeros are singular. The limit theorem nevertheless supplies a
-- positive sublevel tolerance that preserves their separation.
example : ∃ e : ℝ, 0 < e ∧ (1 : ℝ) ∉ connectedComponentIn
    (sublevel (Icc (-2 : ℝ) 2) energy e) (-1) := by
  apply separated_at_positive_sublevel (Icc (-2 : ℝ) 2) isCompact_Icc energy
    (by unfold energy; fun_prop) (fun x _ => sq_nonneg (x ^ 2 - 1)) (-1) 1 (by norm_num) (by norm_num [energy])
  intro hy
  have hx : (-1 : ℝ) ∈ Icc (-2 : ℝ) 2 ∩ energy ⁻¹' {0} := by norm_num [energy]
  have h0 := isPreconnected_connectedComponentIn.Icc_subset (mem_connectedComponentIn hx) hy
    (show (0 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num)
  have hz := (connectedComponentIn_subset _ _ h0).2
  norm_num [energy] at hz

-- An explicit tolerance also separates them: a connected subset of the
-- real line containing -1 and 1 would contain zero, whose energy is one.
example : (1 : ℝ) ∉ connectedComponentIn (sublevel (Icc (-2 : ℝ) 2) energy (1 / 2)) (-1) := by
  intro hy
  have hx : (-1 : ℝ) ∈ sublevel (Icc (-2 : ℝ) 2) energy (1 / 2) := by norm_num [sublevel, energy]
  have h0 := isPreconnected_connectedComponentIn.Icc_subset (mem_connectedComponentIn hx) hy
    (show (0 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num)
  have hz := (connectedComponentIn_subset _ _ h0).2
  norm_num [energy] at hz

end CompactComponentLimitTests

namespace CircleSublevelLiftTests
open LeanCanny.Geometry.CircleSublevelLift Set

-- Radius zero must retain its singleton fiber. A positive radius has the
-- entire connected circle, rather than two disconnected signed square roots.
example : IsConnected ((projection (fun _ : Unit => (0 : ℝ)) 0) ⁻¹' {⟨(), by norm_num [Base]⟩}) :=
  fiber_connected _ _ _

example : IsConnected ((projection (fun _ : Unit => (0 : ℝ)) 1) ⁻¹' {⟨(), by norm_num [Base]⟩}) :=
  fiber_connected _ _ _

-- A negative sublevel of zero is empty. The lift accepts the same empty-set
-- connectivity convention as the original problem.
example : IsPreconnected (Total (fun _ : Unit => (0 : ℝ)) (-1)) := by
  rw [preconnected_iff _ continuous_const]
  have he : Base (fun _ : Unit => (0 : ℝ)) (-1) = ∅ := by
    ext x
    norm_num [Base]
  rw [he]
  exact isPreconnected_empty

-- The component criterion applies to a singular squared polynomial energy;
-- it does not assume local path connectivity of the original zero set.
example (e : ℝ) (x y : Base (fun t : ℝ => (t ^ 2 - 1) ^ 2) e) :
    sectionMap _ e y ∈ connectedComponent (sectionMap _ e x) ↔
      y.val ∈ connectedComponentIn (Base (fun t : ℝ => (t ^ 2 - 1) ^ 2) e) x.val :=
  section_component_iff _ (by fun_prop) e x y

end CircleSublevelLiftTests

namespace RegularPurePowerLiftTests
open LeanCanny.Geometry LeanCanny.Encoding

-- At the positive level of a constant energy, the nonzero slack makes the
-- lifted derivative onto, even though the original derivative is zero.
example : Function.Surjective (fderiv ℝ (CircleSublevelLift.energy (fun _ : ℝ => (0 : ℝ))) (0, 1)) :=
  CircleSublevelLift.regular_energy _ (by fun_prop) 1 (by intro x hx; norm_num at hx) (0, 1)
    (by norm_num [CircleSublevelLift.energy])

example : Function.Surjective (fderiv ℝ (PurePowerSublevelLift.energy 3 (fun _ : ℝ => (0 : ℝ))) (0, 1)) :=
  PurePowerSublevelLift.regular_energy 3 (by decide) _ (by fun_prop) 1
    (by intro x hx; norm_num at hx) (0, 1)
    (by norm_num [PurePowerSublevelLift.energy, PurePowerSublevelLift.penalty])

-- Sixth-power slack fibers retain both the radius-zero singleton and the
-- positive connected fiber. A source degree can use this same shape.
example : IsConnected ((PurePowerSublevelLift.projection 3 (by decide) (fun _ : Unit => (0 : ℝ)) 0) ⁻¹'
    {⟨(), by norm_num [CircleSublevelLift.Base]⟩}) :=
  PurePowerSublevelLift.fiber_connected _ _ _ _ _

example : IsConnected ((PurePowerSublevelLift.projection 3 (by decide) (fun _ : Unit => (0 : ℝ)) 1) ⁻¹'
    {⟨(), by norm_num [CircleSublevelLift.Base]⟩}) :=
  PurePowerSublevelLift.fiber_connected _ _ _ _ _

example (source : List Bool → List Bool) (c : List Bool) :
    Odd (FermatTermPreparation.halfDegree source c) := FermatTermPreparation.halfDegree_odd source c

-- The exact general tolerance exponent is computed from binary controls;
-- its denominator need not have polynomially many bits.
example {dim degree mass : List Bool → ℕ} (hd : UnaryFn dim) (hD : BinaryFn degree) (hb : BinaryFn mass) :
    BinaryFn (fun c => GeneralCriticalValueBounds.exponent (dim c) (degree c) (mass c)) :=
  GeneralRegularLevel.exponent_binary hd hD hb

end RegularPurePowerLiftTests

namespace GeneralCriticalValueTests
open LeanCanny.Geometry LeanCanny.Algebra MvPolynomial
open scoped Classical

private noncomputable def flatSquare : MvPolynomial (Fin 2) ℤ := X 0 ^ 2

-- The critical points (0,t) form an infinite line. The new bound uses the
-- finite value image, and does not require a finite critical-point locus.
example : ∃ q : Polynomial ℤ, q ≠ 0 ∧
    q.natDegree ≤ CoerciveCoordinateEliminant.columnBound 3 4 ∧
    coefficientMass q < 2 ^ GeneralCriticalValueBounds.massExponent 2 2 1 ∧
    ∀ t : ℝ, q.eval₂ (Int.castRingHom ℝ) (flatSquare.eval₂ (Int.castRingHom ℝ)
      (Fin.cons 0 (fun _ : Fin 1 => t))) = 0 := by
  have hd : flatSquare.totalDegree ≤ 2 := (totalDegree_pow _ _).trans (by simp)
  have hm : MvMass.mass flatSquare ≤ 2 ^ 1 := (MvMass.pow_le _ _).trans (by norm_num)
  obtain ⟨q, hq, hdeg, hmass, hann⟩ := GeneralCriticalValueBounds.exists_bounded flatSquare 2 1 hd (by decide) hm
  refine ⟨q, hq, hdeg, hmass, ?_⟩
  intro t
  apply hann
  apply (PolynomialCalculus.critical_iff (Int.castRingHom ℝ) flatSquare _).mpr
  intro i
  fin_cases i <;> norm_num [flatSquare, pderiv_pow, pderiv_X]

-- In dimension zero the positive regularity interval still exists: the
-- derivative has no nonzero directions, and positive levels are empty.
example (e : ℝ) (he : 0 < e) (hδ : e ≤ GeneralCriticalValueBounds.level 0 1 0)
    (x : Fin 0 → ℝ) (hx : (0 : MvPolynomial (Fin 0) ℤ).eval₂ (Int.castRingHom ℝ) x = e) :
    Function.Surjective (fderiv ℝ (fun y : Fin 0 → ℝ => (0 : MvPolynomial (Fin 0) ℤ).eval₂ (Int.castRingHom ℝ) y) x) :=
  GeneralCriticalValueBounds.regular_interval 0 1 0 (by simp) (by decide) (by simp) e he hδ x hx

end GeneralCriticalValueTests

namespace EffectiveSingularComponentTests
open LeanCanny.Geometry LeanCanny.Algebra MvPolynomial Set
open scoped Classical

private noncomputable def doubleWell : MvPolynomial (Fin 1) ℤ := (X 0 ^ 2 - 1) ^ 2

private theorem degree_bound : doubleWell.totalDegree ≤ 4 := by
  have hi : (X 0 ^ 2 - 1 : MvPolynomial (Fin 1) ℤ).totalDegree ≤ 2 :=
    (totalDegree_sub _ _).trans (max_le ((totalDegree_pow _ _).trans (by simp)) (by simp))
  exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 hi)

private theorem mass_bound : MvMass.mass doubleWell ≤ 2 ^ 2 := by
  have hi : MvMass.mass (X 0 ^ 2 - 1 : MvPolynomial (Fin 1) ℤ) ≤ 2 := by
    apply (MvMass.sub_le _ _).trans
    have hx := MvMass.pow_le (X (0 : Fin 1) : MvPolynomial (Fin 1) ℤ) 2
    simp only [MvMass.X, one_pow, MvMass.one] at hx ⊢
    omega
  exact (MvMass.pow_le _ _).trans (Nat.pow_le_pow_left hi 2)

private theorem compact_sublevels (e : ℝ) :
    IsCompact {x : Fin 1 → ℝ | doubleWell.eval₂ (Int.castRingHom ℝ) x ≤ e} := by
  have hc : IsClosed {x : Fin 1 → ℝ | doubleWell.eval₂ (Int.castRingHom ℝ) x ≤ e} :=
    isClosed_le (ProjectionCritical.contDiff_eval (Int.castRingHom ℝ) doubleWell).continuous continuous_const
  apply (CoercivePolynomialSampling.isCompact_sublevel (n := 1) 0 (e + 2)).of_isClosed_subset hc
  intro x hx
  change CoercivePolynomialSampling.penalty 0 x ≤ e + 2
  simp only [CoercivePolynomialSampling.penalty, Fin.sum_univ_one]
  simp only [mem_ofPred_eq, doubleWell, eval₂_pow, eval₂_sub, eval₂_X, eval₂_one] at hx
  change x 0 ^ 2 ≤ e + 2
  nlinarith [sq_nonneg (2 * x 0 ^ 2 - 3)]

-- The exact tolerance is computed from dimension, degree and mass. It
-- separates the two singular zeros without a supplied critical-value oracle.
example : (fun _ : Fin 1 => (1 : ℝ)) ∉ connectedComponentIn
    {x : Fin 1 → ℝ | doubleWell.eval₂ (Int.castRingHom ℝ) x ≤ GeneralCriticalValueBounds.level 1 4 2}
      (fun _ : Fin 1 => (-1 : ℝ)) := by
  have hn (x : Fin 1 → ℝ) : 0 ≤ doubleWell.eval₂ (Int.castRingHom ℝ) x := by
    simp only [doubleWell, eval₂_pow]
    exact sq_nonneg _
  have hi := EffectiveSublevelComponents.zero_component_iff doubleWell 4 2 degree_bound (by decide) mass_bound
    hn compact_sublevels (fun _ => -1) (fun _ => 1) (by norm_num [doubleWell]) (by norm_num [doubleWell])
  intro h
  have hz := hi.mpr h
  have hx : (fun _ : Fin 1 => (-1 : ℝ)) ∈ {x : Fin 1 → ℝ | doubleWell.eval₂ (Int.castRingHom ℝ) x = 0} := by
    norm_num [doubleWell]
  have hc : IsPreconnected ((fun z : Fin 1 → ℝ => z 0) '' connectedComponentIn
      {x : Fin 1 → ℝ | doubleWell.eval₂ (Int.castRingHom ℝ) x = 0} (fun _ => -1)) :=
    isPreconnected_connectedComponentIn.image _ (continuous_apply 0).continuousOn
  have hm0 : (0 : ℝ) ∈ (fun z : Fin 1 → ℝ => z 0) '' connectedComponentIn
      {x : Fin 1 → ℝ | doubleWell.eval₂ (Int.castRingHom ℝ) x = 0} (fun _ => -1) :=
    hc.Icc_subset ⟨_, mem_connectedComponentIn hx, rfl⟩ ⟨_, hz, rfl⟩ (by norm_num)
  obtain ⟨z, hzc, hz0⟩ := hm0
  have hroot := connectedComponentIn_subset _ _ hzc
  norm_num [doubleWell, hz0] at hroot

end EffectiveSingularComponentTests

namespace BoundedRegularSourceTests
open LeanCanny.Geometry LeanCanny.Algebra LeanCanny.Encoding MvPolynomial Set
open scoped Classical

private noncomputable def boundaryPolynomial : MvPolynomial (Fin 1) ℤ := X 0 - 1
private noncomputable def boundaryPoint : BoundedZeroSource.Bounded boundaryPolynomial 0 :=
  ⟨fun _ => 1, by norm_num [BoundedZeroSource.Bounded, boundaryPolynomial, BoundedZeroSource.radial,
    BoundedZeroSource.radiusSquared]⟩

-- Adding an unscaled positive penalty and then taking a tiny level can lose
-- the original zero at one. The shifted source must retain it.
example : ¬ ∃ x : ℝ, (x - 1) ^ 2 + x ^ 2 = 1 / 4 := by
  rintro ⟨x, hx⟩
  nlinarith [sq_nonneg (2 * x - 1)]

example : ∃ w : Fin 5 → ℝ, (BoundedRegularSource.polynomial boundaryPolynomial 1 1 0).eval₂
    (Int.castRingHom ℝ) w = 0 ∧ ∃ j, (pderiv j (BoundedRegularSource.polynomial boundaryPolynomial 1 1 0)).eval₂
      (Int.castRingHom ℝ) w ≠ 0 := by
  have hd : boundaryPolynomial.totalDegree ≤ 1 := (totalDegree_sub _ _).trans (by simp)
  have hm : MvMass.mass boundaryPolynomial ≤ 2 ^ 1 := (MvMass.sub_le _ _).trans (by simp)
  let w := BoundedRegularSource.lift boundaryPolynomial 1 1 0 boundaryPoint
  exact ⟨w.val, w.property, BoundedRegularSource.regular boundaryPolynomial 1 1 0 hd hm w.val w.property⟩

-- With no original coordinates, the compact zero source is a circle and
-- preserves the original singleton's preconnectedness.
example (R : ℕ) : IsPreconnected (BoundedZeroSource.Zeros (0 : MvPolynomial (Fin 0) ℤ) R) := by
  rw [BoundedZeroSource.preconnected_iff]
  exact Set.Subsingleton.isPreconnected (fun x _ y _ => Subsingleton.elim x y)

-- Radius and mass controls stay binary throughout both regularizations.
example {dim degree mass radius : List Bool → ℕ} (hd : UnaryFn dim) (hD : BinaryFn degree)
    (hb : BinaryFn mass) (hR : BinaryFn radius) :
    BinaryFn (fun c => BoundedRegularSource.regularizationExponent (dim c) (degree c) (mass c) (radius c)) :=
  BoundedRegularControls.regularizationExponent_binary hd hD hb hR

private noncomputable def twoRoots : MvPolynomial (Fin 1) ℤ := X 0 ^ 2 - 1
private noncomputable def leftRoot : BoundedZeroSource.Bounded twoRoots 0 :=
  ⟨fun _ => -1, by norm_num [BoundedZeroSource.Bounded, twoRoots, BoundedZeroSource.radial, BoundedZeroSource.radiusSquared]⟩
private noncomputable def rightRoot : BoundedZeroSource.Bounded twoRoots 0 :=
  ⟨fun _ => 1, by norm_num [BoundedZeroSource.Bounded, twoRoots, BoundedZeroSource.radial, BoundedZeroSource.radiusSquared]⟩

-- The complete constructed regular hypersurface cannot connect lifts of
-- the distinct bounded roots. All compactness and radius hypotheses are
-- supplied by the constructed sphere energy, not by a semantic promise.
example : BoundedRegularSource.lift twoRoots 2 1 0 rightRoot ∉
    connectedComponent (BoundedRegularSource.lift twoRoots 2 1 0 leftRoot) := by
  have hd : twoRoots.totalDegree ≤ 2 :=
    (totalDegree_sub _ _).trans (max_le ((totalDegree_pow _ _).trans (by simp)) (by simp))
  have hm : MvMass.mass twoRoots ≤ 2 ^ 1 := by
    apply (MvMass.sub_le _ _).trans
    have hx := MvMass.pow_le (X (0 : Fin 1) : MvPolynomial (Fin 1) ℤ) 2
    simp only [MvMass.X, one_pow, MvMass.one] at hx ⊢
    omega
  intro h
  have hc := (BoundedRegularSource.component_iff_lift twoRoots 2 1 0 hd hm leftRoot rightRoot).mpr h
  have hp : IsPreconnected ((fun z : Fin 1 → ℝ => z 0) ''
      connectedComponentIn (BoundedZeroSource.Bounded twoRoots 0) leftRoot.val) :=
    isPreconnected_connectedComponentIn.image _ (continuous_apply 0).continuousOn
  have hz : (0 : ℝ) ∈ (fun z : Fin 1 → ℝ => z 0) ''
      connectedComponentIn (BoundedZeroSource.Bounded twoRoots 0) leftRoot.val :=
    hp.Icc_subset ⟨_, mem_connectedComponentIn leftRoot.property, rfl⟩ ⟨_, hc, rfl⟩ (by norm_num [leftRoot, rightRoot])
  obtain ⟨z, hz, hz0⟩ := hz
  have hzero := (connectedComponentIn_subset _ _ hz).1
  norm_num [twoRoots, hz0] at hzero

end BoundedRegularSourceTests

namespace BoundedSourceWriterTests
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Encoding LeanCanny.Geometry MvPolynomial
open scoped Classical

private def rootsTerm : Term := .add (.mul (.var 0) (.var 0)) (.const (-1))
private def readers : BoundedSourceWriter.Readers :=
  BoundedDirectionChoice.fromSource (fun _ => rootsTerm.toData.toBits) (fun _ => 1) (fun _ => 0)

private theorem native : readers.PolyTime :=
  BoundedDirectionChoice.fromSource_polyTime (constFn_mem_FP rootsTerm.toData.toBits) (UnaryFn.const 1) (BinaryFn.const 0)

private theorem fits (c : List Bool) : (TermView.term (readers.source c)).arity ≤ readers.dim c := by
  simp only [readers, BoundedDirectionChoice.fromSource, TermView.term_toBits, rootsTerm, Term.arity]
  decide

-- The record is selected by a native space machine from the original term,
-- without serializing any of its constructed giant coefficients.
example : SpaceFunction (BoundedDirectionChoice.record readers) := BoundedDirectionChoice.evaluator native
example : SpaceFunction (fun c => encode (StraightLine.gates
    (BoundedSourceWriter.start (BoundedDirectionChoice.selected readers) c)
    (BoundedSourceWriter.program (BoundedDirectionChoice.selected readers) c))) :=
  BoundedDirectionChoice.selected_encode_evaluator native

-- The selected record validates the exact source constructed from this term.
example (c : List Bool) : FermatSweepCertificate.Valid
    ((BoundedSourceWriter.lower readers c).map (Int.castRingHom ℚ))
    (BoundedSourceWriter.leading readers c : ℚ) (BoundedSourceWriter.degree readers c)
    (BoundedDirectionChoice.record readers c) := BoundedDirectionChoice.record_valid readers c (fits c)

-- Radius exponents remain binary even when supplied by an arbitrary reader.
example {source : List Bool → List Bool} {dim radius : List Bool → ℕ}
    (ht : source ∈ FP) (hd : UnaryFn dim) (hR : BinaryFn radius) :
    SpaceFunction (BoundedDirectionChoice.record (BoundedDirectionChoice.fromSource source dim radius)) :=
  BoundedDirectionChoice.fromSource_evaluator ht hd hR

-- A zero-dimensional original source also receives a constructed record;
-- neither the writer nor the validity proof requires a positive dimension.
private def pointReaders : BoundedSourceWriter.Readers :=
  BoundedDirectionChoice.fromSource (fun _ => (Term.const 0).toData.toBits) (fun _ => 0) (fun _ => 0)

example (c : List Bool) : FermatSweepCertificate.Valid
    ((BoundedSourceWriter.lower pointReaders c).map (Int.castRingHom ℚ))
    (BoundedSourceWriter.leading pointReaders c : ℚ) (BoundedSourceWriter.degree pointReaders c)
    (BoundedDirectionChoice.record pointReaders c) := by
  apply BoundedDirectionChoice.record_valid
  simp only [pointReaders, BoundedDirectionChoice.fromSource, TermView.term_toBits, Term.arity, le_refl]

end BoundedSourceWriterTests

namespace SlackPathTests
open LeanCanny.Geometry MvPolynomial Set

private def upper : CircleSublevelLift.Total (fun _ : Unit => (0 : ℝ)) 1 :=
  ⟨((), Complex.I), by norm_num [CircleSublevelLift.Total, Complex.normSq_apply]⟩
private def lower : CircleSublevelLift.Total (fun _ : Unit => (0 : ℝ)) 1 :=
  ⟨((), -Complex.I), by norm_num [CircleSublevelLift.Total, Complex.normSq_apply]⟩

-- Distinct opposite points of a nonzero slack circle are joined in its
-- actual total space; fiber connectedness alone would not prove this.
example : Joined upper lower :=
  (CircleSublevelLift.joined_iff _ continuous_const 1 upper lower).mpr (Joined.refl _)

-- Degenerate circle fibers are included as well.
example : IsPathConnected ((CircleSublevelLift.projection (fun _ : Unit => (0 : ℝ)) 0) ⁻¹'
    {(⟨(), by change (0 : ℝ) ≤ 0; exact le_refl 0⟩ : CircleSublevelLift.Base (fun _ : Unit => (0 : ℝ)) 0)}) :=
  CircleSublevelLift.fiber_pathConnected _ _ _

private def powerUpper : PurePowerSublevelLift.Total 3 (fun _ : Unit => (0 : ℝ)) 1 :=
  ⟨((), Complex.I), by norm_num [PurePowerSublevelLift.Total, PurePowerSublevelLift.penalty]⟩
private def powerLower : PurePowerSublevelLift.Total 3 (fun _ : Unit => (0 : ℝ)) 1 :=
  ⟨((), -Complex.I), by norm_num [PurePowerSublevelLift.Total, PurePowerSublevelLift.penalty]⟩

example : Joined powerUpper powerLower :=
  (PurePowerSublevelLift.joined_iff 3 (by decide) _ continuous_const 1 powerUpper powerLower).mpr (Joined.refl _)

-- An original zero-dimensional singleton lifts to an entire circle, and
-- every pair of points in that exact polynomial zero source is joined.
example (R : ℕ) (u v : BoundedZeroSource.Zeros (0 : MvPolynomial (Fin 0) ℤ) R) : Joined u v := by
  apply (BoundedZeroSource.joined_iff _ R u v).mpr
  have he : BoundedZeroSource.projection _ R u = BoundedZeroSource.projection _ R v :=
    Subtype.ext (Subsingleton.elim _ _)
  rw [he]

end SlackPathTests

namespace MarkedComponentTests
open LeanCanny.Geometry LeanCanny.Algebra MvPolynomial Set

private def left : List Bool := [false, false]
private def middle : List Bool := [false, true]
private def right : List Bool := [true, false]
private def marks (u : List Bool) : Bool := u == left || u == right
private def chain (u v : List Bool) : Bool :=
  (u == left && v == middle) || (u == middle && v == left) ||
    (u == middle && v == right) || (u == right && v == middle)

-- Both marked endpoints are connected through an unmarked valid vertex.
-- The fourth vertex is an irrelevant isolated valid component.
#guard ImplicitGraph.markedConnected chain (fun _ => true) marks 2
#guard !ImplicitGraph.markedConnected chain marks marks 2
#guard !ImplicitGraph.markedConnected chain (fun _ => true) (fun _ => true) 2
#guard ImplicitGraph.markedConnected chain (fun _ => false) (fun _ => false) 2
-- Marked invalid endpoints are rejected, even at width zero.
#guard !ImplicitGraph.markedConnected chain (fun _ => false) (fun _ => true) 0

-- All marked points over the original zero-dimensional singleton belong
-- together, rather than only the selected section points.
example (D b R : ℕ) (u v : BoundedRegularSource.Marked (0 : MvPolynomial (Fin 0) ℤ) D b R) :
    v.val ∈ connectedComponent u.val := by
  apply (BoundedRegularSource.preconnected_iff_marked (0 : MvPolynomial (Fin 0) ℤ) D b R
    (by simp) (by simp)).mp
  exact Set.Subsingleton.isPreconnected (fun x _ y _ => Subsingleton.elim x y)

end MarkedComponentTests

namespace ParameterCircuitTests
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit MvPolynomial

private def testTerm : Term := .add (.mul (.var 0) (.var 1)) (.const (-2))
private noncomputable def parameterValues (i : ℕ) : ℝ := if i = 0 ∨ i = 5 then Real.sqrt 2 else 17

-- The parameter occupies wire five and holds sqrt(2). Spatial wire zero
-- also holds sqrt(2); all unrelated inputs deliberately hold another value.
-- The original x0*x1-2 vanishes after the actual source circuit is frozen.
example : (Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) 6
    (CircuitFreeze.program 2 5 6 (Source.program 2 testTerm))
    (CircuitFreeze.output 2 5 6 (Source.output 2 testTerm))).eval₂ (Int.castRingHom ℝ) parameterValues = 0 := by
  have ha : testTerm.arity ≤ 2 := by decide
  have ho : Source.output 2 testTerm < 2 + (Source.program 2 testTerm).length := by
    simpa only [Source.program_length] using Source.output_lt 2 testTerm ha
  rw [CircuitFreeze.symbolic_output 2 5 6 _ _ (Source.wellFormed 2 testTerm ha) (by decide) (by decide) ho,
    Source.symbolicRun_output 2 testTerm ha, CircuitFreeze.eval_substitution, Term.eval₂_toPolynomial]
  simp [testTerm, Term.eval, parameterValues]

-- The second operation reads the first operation's relocated output twice.
-- The generic shared-program writer must preserve this dependency.
example : Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) 6
    (CircuitFreeze.program 2 5 6 [.mul 0 1, .mul 2 2]) 7 = (X 5 * X 0) ^ 2 := by
  simp [CircuitFreeze.program, CircuitFreeze.index, Operation.reindex, Differential.symbolicRun,
    Differential.polynomial, pow_two]

end ParameterCircuitTests

namespace FullSourceWireTests
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Encoding MvPolynomial

private def testTerm : Term := .add (.var 0) (.const (-1))
private def atParameter (a : ℝ) (i : ℕ) : ℝ := if i = 4 then a else 0
private noncomputable def model : ℕ → MvPolynomial ℕ ℤ :=
  Differential.symbolicRun (fun i => X i) 5 (BoundedFullSource.program 1 4 5 2 testTerm [] [true] [] [true] [true])

-- Small exponents isolate the full-program wiring. Changing the parameter
-- input must change the source value; freezing it to a literal would fail.
example : (model (BoundedFullSource.output 5 2 testTerm [] [true] [] [true] [true])).eval₂
    (Int.castRingHom ℝ) (atParameter 0) = 5 ∧
    (model (BoundedFullSource.output 5 2 testTerm [] [true] [] [true] [true])).eval₂
      (Int.castRingHom ℝ) (atParameter 1) = -1 := by
  have hs := BoundedFullSource.symbolic_output 1 4 5 2 testTerm [] [true] [] [true] [true]
    (by decide) (by decide) (by decide) (by decide)
  simp only [model, hs, BoundedFullSource.polynomial, BoundedTail.polynomial, BoundedLow.polynomial,
    eval₂_sub, eval₂_add, eval₂_mul, eval₂_C, eval₂_one, eval₂_pow, eval₂_sum, eval₂_X,
    CircuitFreeze.eval_substitution, Term.eval₂_toPolynomial]
  norm_num [testTerm, Term.eval, atParameter, Finset.sum_range_succ, Nat.fromBitsLE, Nat.fromBits]

-- The marking wire computes the unscaled old zero energy, independently
-- of both regularization scales and the full-source output wire.
example : (model (BoundedFullSource.energyOutput 5 2 testTerm [])).eval₂ (Int.castRingHom ℝ) (atParameter 0) = 2 ∧
    (model (BoundedFullSource.energyOutput 5 2 testTerm [])).eval₂ (Int.castRingHom ℝ) (atParameter 1) = 0 := by
  have hs := BoundedFullSource.symbolic_energy 1 4 5 2 testTerm [] [true] [] [true] [true]
    (by decide) (by decide) (by decide) (by decide)
  simp only [model, hs, BoundedFullSource.energy, BoundedTail.energy, eval₂_add, eval₂_pow, eval₂_sub,
    eval₂_C, eval₂_sum, eval₂_X, CircuitFreeze.eval_substitution, Term.eval₂_toPolynomial]
  norm_num [testTerm, Term.eval, atParameter, Finset.sum_range_succ, Nat.fromBitsLE, Nat.fromBits]

-- Full source generation remains native polynomial time at original
-- dimension zero and with an arbitrary binary radius reader.
example {source : List Bool → List Bool} {radius : List Bool → ℕ} (ht : source ∈ FP) (hR : BinaryFn radius) :
    let P : BoundedFullWriter.Readers := ⟨source, fun _ => 0, radius⟩
    (fun c => encode (StraightLine.gates (BoundedFullWriter.start P c) (BoundedFullWriter.program P c))) ∈ FP :=
  BoundedFullWriter.encode_mem_FP ⟨ht, UnaryFn.const 0, hR⟩

end FullSourceWireTests

namespace RealCircuitQueryTests
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit MvPolynomial
open scoped Classical

private def noRealRoot : List Operation := [.mul 0 0, .constant 1, .add 1 2]
private def sqrtTwo : List Operation := [.mul 0 0, .constant (-2), .add 1 2]

-- The unrestricted complex query accepts x^2 + 1 = 0.
example : Satisfiable (StraightLine.gates 1 noRealRoot ++ [.zero 3]) := by
  refine ⟨fun i => if i = 0 then Complex.I else if i = 1 then -1 else if i = 2 then 1 else 0, ?_⟩
  intro g hg
  simp only [StraightLine.gates, noRealRoot, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;>
    norm_num [Operation.gate, Gate.Holds, Complex.I_mul_I]

-- The real-input query rejects the same circuit, despite its complex root.
example : ¬ RealQuery.Satisfiable 1 (StraightLine.gates 1 noRealRoot ++ [.zero 3]) := by
  intro h
  obtain ⟨x, hx⟩ := (RealQuery.zero_constraints_iff 1 noRealRoot [3]
    (by norm_num [StraightLine.WellFormed, Operation.InputsBelow, noRealRoot])
    (by simp [noRealRoot])).mp h
  have hz := hx 3 (by simp)
  norm_num [noRealRoot, Differential.symbolicRun, Differential.polynomial] at hz
  nlinarith [sq_nonneg (x 0)]

-- The Boolean constraint chooses the positive irrational root in the same
-- assignment as the source circuit; no rational approximation is substituted.
example : RealQuery.WithConstraints 1 (StraightLine.gates 1 sqrtTwo ++ [.zero 3]) positiveSqrtTwo := by
  apply (RealQuery.zero_constraints_with_iff 1 sqrtTwo [3] positiveSqrtTwo
    (by norm_num [StraightLine.WellFormed, Operation.InputsBelow, sqrtTwo])
    (by simp [sqrtTwo]) (by decide)).mpr
  refine ⟨fun _ => Real.sqrt 2, ?_, ?_⟩
  · intro out hout
    obtain rfl := List.mem_singleton.mp hout
    norm_num [sqrtTwo, Differential.symbolicRun, Differential.polynomial]
  · have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    simp only [positiveSqrtTwo, Formula.Holds, Term.eval, Int.cast_neg, Int.cast_ofNat, Int.cast_one]
    constructor <;> nlinarith

-- Native source/marking costs retain the original writer, unary varying
-- dimension, and binary radius; no geometric decision routine is assumed.
example {P : LeanCanny.Encoding.BoundedFullWriter.Readers} (h : P.PolyTime)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun c => [decide (∃ x, LeanCanny.Encoding.BoundedRealQuery.MarkedPoint P c x)]) :=
  LeanCanny.Encoding.BoundedRealQuery.marked_evaluator h ht

end RealCircuitQueryTests

namespace InterleavedWitnessTests
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit RealQuery
open scoped Classical

private def witnessZero : Formula := .eqZero (.var 1)

-- Logical variable one is an independent witness although the original
-- circuit uses auxiliary wire one to store seven.
example : WithConstraints 2 (Interleaved.gates 1 2 [.constant 1 7])
    (witnessZero.rename Interleaved.even) := by
  apply (Interleaved.correct 1 1 2 [.constant 1 7] witnessZero (by decide) (by decide)
    (by simp [Gate.arity])).mpr
  refine ⟨fun _ => 0, fun i => if i = 1 then 7 else 0, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain rfl := List.mem_singleton.mp hg
    norm_num [Gate.Holds]
  · intro i hi
    have he : i = 0 := by omega
    simp [he]
  · intro i hi
    have he : i = 0 := by omega
    simp [he]
  · simp [witnessZero, Formula.Holds, Term.eval]

-- Reusing the auxiliary wire for the same logical witness would reject it.
example : ¬ WithConstraints 1 [.constant 1 7] witnessZero := by
  rintro ⟨env, hg, _, hp⟩
  have he : env 1 = (7 : ℂ) := hg (.constant 1 7) (by simp)
  change (env 1).re = 0 at hp
  rw [he] at hp
  norm_num at hp

-- Even dimension zero leaves logical witness zero independent of the
-- added odd-wire zero constant.
example : WithConstraints 0 (Interleaved.gates 0 0 [])
    ((Formula.eqZero (.var 0)).rename Interleaved.even) := by
  apply (Interleaved.correct 0 0 0 [] _ (by decide) (by decide) (by simp)).mpr
  exact ⟨fun _ => 0, fun _ => 0, by simp, by simp, by simp, rfl⟩

example {P : LeanCanny.Encoding.BoundedFullWriter.Readers} {p : List Bool → Formula}
    (h : P.PolyTime) (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c)
    (hp : (fun c => (p c).encode) ∈ FP) :
    SpaceFunction (fun c => [decide (∃ x : ℕ → ℝ,
      LeanCanny.Encoding.BoundedRealQuery.MarkedPoint P c (fun i => x i.val) ∧ (p c).Holds x)]) :=
  LeanCanny.Encoding.BoundedWitnessQuery.marked_evaluator h ht hp

end InterleavedWitnessTests

namespace OriginalCoordinateTests
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit RealQuery LeanCanny.Encoding
open scoped Classical

private def firstElevenSecondSeven : Formula :=
  .and (.eqZero (.add (.var 0) (.const (-11))))
    (.eqZero (.add (.var 1) (.const (-7))))

-- The source stores original coordinate zero on wire four. Logical
-- coordinate one is linked to wire zero, whose value is deliberately different.
example : WithConstraints 10
    (Interleaved.portGates 5 5 (BoundedOriginalQuery.port 1) [.constant 4 11, .constant 0 7])
    (firstElevenSecondSeven.rename Interleaved.even) := by
  apply (Interleaved.port_correct 5 5 5 (BoundedOriginalQuery.port 1) _ _ (by decide) (by decide)
    (BoundedOriginalQuery.port_bound 1) (by simp [Gate.arity])).mpr
  refine ⟨fun i => if i = 0 then 11 else if i = 1 then 7 else 0,
    fun i => if i = 4 then 11 else if i = 0 then 7 else 0, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> norm_num [Gate.Holds]
  · intro i _
    dsimp only
    split_ifs <;> norm_num
  · intro i hi
    interval_cases i <;> norm_num [BoundedOriginalQuery.port]
  · norm_num [firstElevenSecondSeven, Formula.Holds, Term.eval]

-- Original-coordinate source queries retain arbitrary formula witnesses
-- and native varying-dimension/binary-radius costs.
example {P : BoundedFullWriter.Readers} {p : List Bool → Formula} (h : P.PolyTime)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (hp : (fun c => (p c).encode) ∈ FP) :
    SpaceFunction (fun c => [decide (∃ x : ℕ → ℝ,
      BoundedOriginalQuery.MarkedPoint P c (fun i => x i.val) ∧ (p c).Holds x)]) :=
  BoundedOriginalQuery.marked_evaluator h ht hp

end OriginalCoordinateTests

namespace IndependentPieceWitnessTests
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit RealQuery Interleaved
open LeanCanny.Connectivity.BoundedEndpointQuery
open scoped Classical

private def leftPiece : Formula :=
  .and (.eqZero (.add (.var 0) (.const (-5)))) (.eqZero (.var 1))
private def rightPiece : Formula :=
  .and (.eqZero (.add (.var 0) (.const (-5)))) (.eqZero (.add (.var 1) (.const (-1))))
private def differentPoint : Formula := .eqZero (.add (.var 0) (.const (-6)))
private def leftAssignment (i : ℕ) : ℝ := if i = 0 then 5 else 0
private def rightAssignment (i : ℕ) : ℝ := if i = 0 then 5 else 1

-- Both pieces contain the same point, with witness values zero and one.
-- Direct conjunction would incorrectly identify those witnesses.
example : witnessPiece leftPiece (fun _ : Fin 1 => 5) ∧ witnessPiece rightPiece (fun _ : Fin 1 => 5) := by
  constructor
  · refine ⟨leftAssignment, ?_, ?_⟩
    · intro i
      have he : i = 0 := Subsingleton.elim _ _
      simp [he, leftAssignment]
    · norm_num [leftPiece, Formula.Holds, Term.eval, leftAssignment]
  · refine ⟨rightAssignment, ?_, ?_⟩
    · intro i
      have he : i = 0 := Subsingleton.elim _ _
      simp [he, rightAssignment]
    · norm_num [rightPiece, Formula.Holds, Term.eval, rightAssignment]

example : ¬ (Formula.and leftPiece rightPiece).Satisfiable := by
  rintro ⟨x, ⟨_, hzero⟩, ⟨_, hone⟩⟩
  change x 1 = 0 at hzero
  norm_num [Formula.Holds, Term.eval] at hone
  linarith

-- Two links share the source's sole spatial wire, even though the source
-- input frame has length one. Formula witnesses remain independent.
example : WithConstraints 2
    (portGates 2 1 (Duplicated.port id) [.constant 0 5])
    ((Duplicated.combine leftPiece rightPiece).rename even) := by
  apply (port_correct_of_real 2 1 1 (Duplicated.port id) _ _
    (by intro i hi; right; simp only [Duplicated.port, id_eq]; omega) (by decide)
    (by intro i hi; simp only [Duplicated.port, id_eq]; omega) (by simp [Gate.arity])).mpr
  apply (Duplicated.satisfiable_iff 1 1 id _ _ _).mpr
  refine ⟨leftAssignment, rightAssignment, ⟨fun _ => 5, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro g hg
    obtain rfl := List.mem_singleton.mp hg
    norm_num [Gate.Holds]
  · intro i _
    norm_num
  · intro i hi
    have he : i = 0 := by omega
    simp [he, leftAssignment]
  · intro i hi
    have he : i = 0 := by omega
    simp [he, leftAssignment, rightAssignment]
  · norm_num [leftPiece, Formula.Holds, Term.eval, leftAssignment]
  · norm_num [rightPiece, Formula.Holds, Term.eval, rightAssignment]

-- Independent witnesses cannot make two different spatial points intersect.
example : ¬ WithConstraints 2
    (portGates 2 1 (Duplicated.port id) [.constant 0 5])
    ((Duplicated.combine leftPiece differentPoint).rename even) := by
  intro h
  have hs := (port_correct_of_real 2 1 1 (Duplicated.port id) _ _
    (by intro i hi; right; simp only [Duplicated.port, id_eq]; omega) (by decide)
    (by intro i hi; simp only [Duplicated.port, id_eq]; omega) (by simp [Gate.arity])).mp h
  obtain ⟨a, b, _, he, hp, hq⟩ := (Duplicated.satisfiable_iff 1 1 id _ _ _).mp hs
  have hab := he 0 (by decide)
  norm_num [leftPiece, differentPoint, Formula.Holds, Term.eval] at hp hq
  linarith [hp.1]

-- At spatial dimension zero, both variables are independent witnesses.
example : WithConstraints 0 (portGates 0 0 (Duplicated.port id) [])
    ((Duplicated.combine (.eqZero (.var 0)) (.eqZero (.add (.var 0) (.const (-1))))).rename even) := by
  apply (port_correct_of_real 0 0 0 (Duplicated.port id) _ _ (by simp) (by decide) (by simp) (by simp)).mpr
  apply (Duplicated.satisfiable_iff 0 0 id _ _ _).mpr
  refine ⟨fun _ => 0, fun _ => 1, ⟨fun _ => 0, by simp, by simp, by simp⟩, by simp, rfl, ?_⟩
  norm_num [Formula.Holds, Term.eval]

end IndependentPieceWitnessTests

namespace FullCriticalDirectionTests
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Encoding
open scoped Classical

-- Short records are zero padded. Their first bit changes exactly the first
-- direction scalar; the width is positive even at original dimension zero.
example (P : BoundedFullWriter.Readers) (c : List Bool) :
    BoundedFullDirectionQueries.direction P (fun _ => [true]) c 0 = 1 := by
  have hw : ([true] : List Bool).length ≤ BoundedFullDirectionQueries.width P c :=
    BoundedFullDirectionQueries.width_pos P c
  unfold BoundedFullDirectionQueries.direction FixedWidthQuery.coordinate
  simp only [Nat.zero_mul, List.drop_zero, List.take_of_length_le hw]
  decide

example (P : BoundedFullWriter.Readers) (c : List Bool) :
    BoundedFullDirectionQueries.direction P (fun _ => [true]) c 1 = 0 := by
  have hw : ([true] : List Bool).length ≤ BoundedFullDirectionQueries.width P c :=
    BoundedFullDirectionQueries.width_pos P c
  unfold BoundedFullDirectionQueries.direction FixedWidthQuery.coordinate
  simp only [Nat.one_mul, List.drop_eq_nil_iff.mpr hw, List.take_nil]
  decide

-- Complex critical roots use unrestricted complex input wires. These tests
-- are distinct from the real source/marking feasibility tests.
example {P : BoundedFullWriter.Readers} {record : List Bool → List Bool}
    (h : P.PolyTime) (hr : record ∈ FP)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun c => [decide (¬ CriticalKernel.FiniteBad (BoundedFullCriticalKernel.polynomial P c)
      (BoundedFullDirectionQueries.direction P record c) (0 : Fin (P.dim c + 4)))]) :=
  BoundedFullDirectionQueries.empty_evaluator h hr (UnaryFn.const 0) ht

end FullCriticalDirectionTests

namespace FullDirectionChoiceTests
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Encoding MvPolynomial
open scoped Classical

-- A nonempty family of four charts remains at original dimension zero.
private def pointReaders : BoundedFullWriter.Readers :=
  ⟨fun _ => (Term.const 0).toData.toBits, fun _ => 0, fun _ => 0⟩

private theorem pointNative : pointReaders.PolyTime :=
  ⟨constFn_mem_FP _, UnaryFn.const 0, BinaryFn.const 0⟩

private theorem pointFits (c : List Bool) :
    (TermView.term (pointReaders.source c)).arity ≤ pointReaders.dim c := by
  simp only [pointReaders, TermView.term_toBits, Term.arity, le_refl]

example : SpaceFunction (BoundedFullDirectionChoice.record pointReaders) :=
  BoundedFullDirectionChoice.evaluator pointNative pointFits

example (c : List Bool) : BoundedFullDirectionChoice.Good pointReaders c
    (BoundedFullDirectionChoice.record pointReaders c) :=
  BoundedFullDirectionChoice.record_good pointReaders c

example (P : BoundedFullWriter.Readers) (c : List Bool) :
    (BoundedFullDirectionChoice.record P c).length =
      (P.dim c + 3) * BoundedFullDirectionQueries.width P c :=
  BoundedFullDirectionChoice.record_length P c

-- Selection is space bounded; query serialization must compose with it
-- without assuming that the selected record is polynomial-time computable.
example : SpaceFunction (fun c => encode (BoundedFullCriticalKernel.query pointReaders
    (BoundedFullDirectionQueries.direction pointReaders (BoundedFullDirectionChoice.record pointReaders) c) 0 c)) :=
  BoundedFullDirectionChoice.selected_encode_evaluator pointNative (UnaryFn.const 0) pointFits

private noncomputable def cubic : MvPolynomial (Fin 2) ℂ := X 0 + X 1 ^ 3

-- At its sole critical point, the Jacobian kernel lies entirely in chart 1.
-- Scanning only chart 0 would miss this singular critical point.
example : CriticalKernel.FiniteBad cubic (fun _ => 0) 1 := by
  refine ⟨fun _ => 0, fun i => if i = 1 then 1 else 0, by norm_num, ?_⟩
  intro j
  fin_cases j <;>
    norm_num [CriticalKernel.finiteCriticalValue, CriticalKernel.finiteKernelValue,
      CriticalKernel.finiteSelected, CriticalKernel.finiteEntry, CriticalKernel.coefficient,
      cubic, Fin.sum_univ_two]

example : ¬ CriticalKernel.FiniteBad cubic (fun _ => 0) 0 := by
  rintro ⟨x, u, hu, h⟩
  have hc := (h 1).1
  have hk := (h 0).2
  norm_num [CriticalKernel.finiteCriticalValue, CriticalKernel.finiteSelected,
    CriticalKernel.coefficient, cubic] at hc
  have hy : x 1 = 0 := hc
  norm_num [CriticalKernel.finiteKernelValue, CriticalKernel.finiteEntry,
    CriticalKernel.coefficient, cubic, Fin.sum_univ_two, hy] at hk
  norm_num [Fin.sum_univ_two, Pi.single_apply] at hk
  exact one_ne_zero (hu.symm.trans hk)

end FullDirectionChoiceTests

namespace FullCriticalSampleTests
open LeanCanny.ETR LeanCanny.Encoding LeanCanny.Geometry MvPolynomial
open scoped Classical

-- The empty square system has one root: the unique empty coordinate tuple.
example : Finite (RegularAffineRootCount.Roots (fun i : Fin 0 => Fin.elim0 i)) ∧
    Nat.card (RegularAffineRootCount.Roots (fun i : Fin 0 => Fin.elim0 i)) ≤ 1 := by
  simpa only [RegularAffineRootCount.labelWidth, Nat.zero_mul, pow_zero] using
    RegularAffineRootCount.finite_card_le_uniform (fun i : Fin 0 => Fin.elim0 i) 1
      (fun i => Fin.elim0 i) (by decide) (fun _ => by
        apply (PolynomialSystemRegularity.isInvertible_iff (Int.castRingHom ℝ) _ _).mpr
        rw [Matrix.det_isEmpty]
        exact one_ne_zero)

-- A singular root cannot satisfy the regularity hypothesis used by the
-- finite-root bound, even when its actual zero set happens to be finite.
example : ¬ (fderiv ℝ (fun x : Fin 1 → ℝ => fun _ : Fin 1 =>
    (X (0 : Fin 1) ^ 2 : MvPolynomial (Fin 1) ℤ).eval₂ (Int.castRingHom ℝ) x) (fun _ => 0)).IsInvertible := by
  rw [PolynomialSystemRegularity.isInvertible_iff]
  intro h
  apply h
  rw [Matrix.det_fin_one]
  norm_num [PolynomialSystemRegularity.matrix]

-- Binary degrees must remain binary when computing the unary label width.
#guard RegularAffineRootCount.labelWidth 0 (2 ^ 100) == 0
#guard RegularAffineRootCount.labelWidth 1 (2 ^ 100) == 202

example {dim degree : List Bool → ℕ} (hn : UnaryFn dim) (hD : BinaryFn degree) :
    UnaryFn (fun c => RegularAffineRootCount.labelWidth (dim c) (degree c)) :=
  RegularRootLabels.width_unary hn hD

example (P : BoundedFullWriter.Readers) (c : List Bool) :
    Finite (BoundedFullCriticalSamples.Samples P c) ∧
      Nat.card (BoundedFullCriticalSamples.Samples P c) ≤ 2 ^ BoundedFullCriticalSamples.labelWidth P c :=
  BoundedFullCriticalSamples.finite_samples P c

example (P : BoundedFullWriter.Readers) (c : List Bool) :
    Function.Surjective (BoundedFullCriticalSamples.componentMap P c) :=
  BoundedFullCriticalSamples.componentMap_surjective P c

end FullCriticalSampleTests

namespace CriticalSampleQueryTests
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Computation MvPolynomial
open RealQuery.Interleaved
open scoped Classical

private def rows : List Operation := CriticalKernel.program 1 1 [] 0 (fun _ => 0)
private noncomputable def models : List (ℕ × MvPolynomial (Fin 1) ℤ) := [(CriticalSamples.output 1 1 [] 0, X 0)]
private def witness : Formula := .eqZero (.add (.var 2) (.const (-7)))

private theorem wf : StraightLine.WellFormed 2 rows :=
  CriticalKernel.wellFormed 1 1 [] 0 (fun _ => 0) (by trivial) (by decide)

private theorem bound : ∀ z ∈ models, z.1 < 2 + rows.length := by
  intro z hz
  obtain rfl := List.mem_singleton.mp hz
  exact CriticalSamples.output_lt 1 1 [] 0 (fun _ => 0) 0 (by decide)

private theorem model : ∀ z ∈ models, Differential.symbolicRun
    (fun i => (X i : MvPolynomial ℕ ℤ)) 2 rows z.1 = rename Fin.val z.2 := by
  intro z hz
  obtain rfl := List.mem_singleton.mp hz
  rw [show Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) 2 rows
      (CriticalSamples.output 1 1 [] 0) = CriticalSamples.criticalPolynomial (X 0) (fun _ => 0) 0 from
    CriticalSamples.symbolic_output (fun i => X i) 1 1 [] 0 (fun _ => 0)
      (by trivial) (by trivial) (fun _ _ => rfl) (by decide) 0 (by decide)]
  simp only [CriticalSamples.criticalPolynomial, CriticalKernel.selectedPolynomial,
    CriticalKernel.coefficient, ite_true, C_0, zero_mul, add_zero, rename_X, Fin.val_zero]

-- The formula's logical variable 2 is independent of the circuit's zero
-- wire 2. Both the sample and this witness are realized simultaneously.
example : InputSatisfiable 1 2 (CriticalSamples.query 1 1 [] 0 (fun _ => 0)) witness := by
  change InputSatisfiable 1 2 (zeroGates 2 rows models) witness
  rw [finite_correct 2 rows models witness (by decide) wf bound model]
  refine ⟨fun i => if i = 2 then 7 else 0, ?_, ?_⟩
  · intro z hz
    obtain rfl := List.mem_singleton.mp hz
    norm_num
  · norm_num [witness, Formula.Holds, Term.eval]

-- A critical sample need not be singular. The kernel query for this source
-- is empty although the critical-sample query above is feasible.
example : ¬ Satisfiable (CriticalKernel.query 1 1 [] 0 (fun _ => 0) 0) := by
  rw [CriticalKernel.query_satisfiable (fun i => X i) 1 1 [] 0 (fun _ => 0) 0
    (by decide) (by trivial) (by trivial) (fun _ _ => rfl) (by decide)]
  rintro ⟨x, u, hn, h⟩
  have hk := (h 0 (by decide)).2
  norm_num [CriticalKernel.kernelValue, CriticalKernel.entryPolynomial, CriticalKernel.coefficient,
    Pi.single_apply] at hk
  exact one_ne_zero (hn.symm.trans hk)

private def readers : LeanCanny.Encoding.BoundedFullWriter.Readers :=
  ⟨fun _ => (Term.const 0).toData.toBits, fun _ => 0, fun _ => 0⟩

private theorem native : readers.PolyTime := ⟨constFn_mem_FP _, UnaryFn.const 0, BinaryFn.const 0⟩
private theorem fits (c : List Bool) : (TermView.term (readers.source c)).arity ≤ readers.dim c := by
  simp only [readers, TermView.term_toBits, Term.arity, le_refl]

example : SpaceFunction (fun c => encode (LeanCanny.Encoding.BoundedCriticalSampleQuery.query readers
    (LeanCanny.Encoding.BoundedFullDirectionChoice.record readers) c)) :=
  LeanCanny.Encoding.BoundedCriticalSampleQuery.selected_encode_evaluator native fits

example : SpaceFunction (fun c => [decide (∃ y : LeanCanny.Encoding.BoundedFullCriticalSamples.Samples readers c,
    LeanCanny.Encoding.BoundedCriticalSampleQuery.Matches readers c witness y)]) :=
  LeanCanny.Encoding.BoundedCriticalSampleQuery.samples_evaluator native (constFn_mem_FP witness.encode) fits

end CriticalSampleQueryTests

namespace CriticalSeparatorTests
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Encoding
open RealQuery.Interleaved
open scoped Classical

-- Independent copies may constrain the same original wire to different
-- values. The outer formula observes both values simultaneously.
example : InputSatisfiable 2 2 (RealQuery.Paired.gates [.constant 0 0] [.constant 0 1])
    (.and (.eqZero (.var 0)) (.eqZero (.add (.var 1) (.const (-1))))) := by
  rw [RealQuery.Paired.satisfiable_iff 1 1]
  let x : ℕ → ℝ := RealQuery.Paired.merge (fun _ => 0) (fun _ => 1)
  refine ⟨x, ⟨?_, ?_⟩, ?_⟩
  · refine ⟨fun _ => 0, ?_, fun _ _ => rfl, ?_⟩
    · intro g hg
      obtain rfl := List.mem_singleton.mp hg
      simp only [Gate.Holds, Int.cast_zero]
    · intro i _
      simp only [Function.comp_apply, x, RealQuery.Paired.merge_even, Complex.ofReal_zero]
  · refine ⟨fun _ => 1, ?_, fun _ _ => rfl, ?_⟩
    · intro g hg
      obtain rfl := List.mem_singleton.mp hg
      simp only [Gate.Holds, Int.cast_one]
    · intro i _
      simp only [Function.comp_apply, x, RealQuery.Paired.merge_odd, Complex.ofReal_one]
  · norm_num [Formula.Holds, Term.eval, x, RealQuery.Paired.merge, even, odd]

-- Zero weights collide on the distinct tuples (0,0) and (1,0).
example : (ProjectionCollision.formula 2 (fun _ => 0) 0).Holds
    (RealQuery.Paired.merge (fun _ : ℕ => (0 : ℝ)) (fun i => if i = 0 then 1 else 0)) := by
  rw [ProjectionCollision.formula_holds]
  norm_num [ProjectionCollision.projection, RealQuery.Paired.merge_even, RealQuery.Paired.merge_odd]

-- Giving their first coordinate positive weight detects the difference.
example : ¬ (ProjectionCollision.formula 2 (fun _ => 2 ^ 100) 0).Holds
    (RealQuery.Paired.merge (fun _ : ℕ => (0 : ℝ)) (fun i => if i = 0 then 1 else 0)) := by
  rw [ProjectionCollision.formula_holds]
  norm_num [ProjectionCollision.projection, Finset.sum_range_succ,
    RealQuery.Paired.merge_even, RealQuery.Paired.merge_odd]

example (P : BoundedFullWriter.Readers) (c : List Bool)
    (a b : BoundedFullCriticalSamples.Samples P c)
    (he : BoundedCriticalSeparator.value P (BoundedCriticalSeparator.record P) c a.val =
      BoundedCriticalSeparator.value P (BoundedCriticalSeparator.record P) c b.val) : a = b :=
  BoundedCriticalSeparator.value_injective P c he

-- A separating projection requires no witness when the sample set is empty.
example (P : BoundedFullWriter.Readers) (c : List Bool)
    [IsEmpty (BoundedFullCriticalSamples.Samples P c)] : BoundedCriticalSeparator.Good P c [] := by
  intro a
  exact isEmptyElim a

example {P : BoundedFullWriter.Readers} (h : P.PolyTime)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (BoundedCriticalSeparator.record P) :=
  BoundedCriticalSeparator.evaluator h ht

example (P : BoundedFullWriter.Readers) (f : List Bool → List Bool) (c : List Bool) :
    BoundedFullDirectionChoice.record (P.comp f) c = BoundedFullDirectionChoice.record P (f c) :=
  BoundedFullDirectionChoice.record_comp P f c

example (P : BoundedFullWriter.Readers) (f : List Bool → List Bool) (c : List Bool) :
    BoundedCriticalSeparator.record (P.comp f) c = BoundedCriticalSeparator.record P (f c) :=
  BoundedCriticalSeparator.record_comp P f c

end CriticalSeparatorTests

namespace CriticalProjectionLabelTests
open LeanCanny.ETR LeanCanny.Geometry LeanCanny.Algebra LeanCanny.Encoding MvPolynomial
open scoped Classical

-- The retained parameter has coefficient degree one even for signed weights.
example (e : Fin 2 →₀ ℕ) :
    ((LinearProjectionSystem.rows (fun _ : Fin 1 => (X 0 : MvPolynomial (Fin 1) ℤ) - 1)
      (fun _ => 1) (fun _ => -3) 0).coeff e).natDegree ≤ 1 :=
  LinearProjectionSystem.coefficient_degree _ _ _ _ _

-- A negative projection is retained with its sign; regularity belongs to
-- the original equation and does not require a nonzero projection weight.
example (v : ℤ) :
    (LinearProjectionEliminant.polynomial
      (fun _ : Fin 1 => (X 0 : MvPolynomial (Fin 1) ℤ) - 1) (fun _ => 1) (fun _ => v) 2).eval₂
      (Int.castRingHom ℝ) (v : ℝ) = 0 := by
  have he := LinearProjectionEliminant.eval_eq_zero (Int.castRingHom ℝ)
    (fun _ : Fin 1 => (X 0 : MvPolynomial (Fin 1) ℤ) - 1) (fun _ => 1)
    (fun _ => (totalDegree_sub _ _).trans (by simp)) (fun _ => by decide)
    (fun _ => v) 2 (by norm_num [Macaulay.level, AffineCoordinateSystem.degrees, Fin.sum_univ_succ])
    (fun _ => (1 : ℝ)) (by intro j; simp)
    (by
      rw [PolynomialSystemRegularity.isInvertible_iff, Matrix.det_fin_one]
      norm_num [PolynomialSystemRegularity.matrix])
  simpa using he

-- The empty square system has one root, whose linear projection is zero.
example : (LinearProjectionEliminant.polynomial
    (fun i : Fin 0 => Fin.elim0 i) (fun _ => 1) (fun i => Fin.elim0 i) 1 : Polynomial ℤ).eval₂
      (Int.castRingHom ℝ) 0 = 0 := by
  have he := LinearProjectionEliminant.eval_eq_zero (Int.castRingHom ℝ)
    (fun i : Fin 0 => Fin.elim0 i) (fun _ => 1) (fun i => Fin.elim0 i) (fun _ => by decide)
    (fun i => Fin.elim0 i) 1
    (by norm_num [Macaulay.level, AffineCoordinateSystem.degrees, Fin.sum_univ_succ])
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    (by
      apply (PolynomialSystemRegularity.isInvertible_iff _ _ _).mpr
      rw [Matrix.det_isEmpty]
      exact one_ne_zero)
  simpa using he

-- Width is part of label validity: appending a bit destroys representation
-- even though the underlying natural index might have been unchanged.
example (P : BoundedFullWriter.Readers) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P c) :
    ¬ BoundedCriticalLabels.Valid P c (BoundedCriticalLabels.label P c x ++ [false]) := by
  intro hr
  have h := BoundedCriticalLabels.valid_length P c _ hr
  simp only [List.length_append, BoundedCriticalLabels.label_length, List.length_singleton] at h
  omega

example (P : BoundedFullWriter.Readers) (c : List Bool)
    [IsEmpty (BoundedFullCriticalSamples.Samples P c)] (r : List Bool) :
    BoundedCriticalLabels.decode P c r = none := by
  have hn : ¬ BoundedCriticalLabels.Valid P c r := by
    rintro ⟨x, _⟩
    exact isEmptyElim x
  simp only [BoundedCriticalLabels.decode, dite_eq_right hn]

end CriticalProjectionLabelTests

namespace NativeCriticalCoefficientTests
open LeanCanny.ETR LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Computation
open scoped Classical

-- The binary exponent is enormous, but modular exponentiation processes
-- only its 101 digits. Modulus one must also return the zero residue.
#guard BinaryNat.powMod (LeanCanny.pair (BinaryNatCode.encode 2)
  (LeanCanny.pair (BinaryNatCode.encode (2 ^ 100)) (BinaryNatCode.encode 6))) == BinaryNatCode.encode 2
#guard BinaryNat.powMod (LeanCanny.pair (BinaryNatCode.encode 2)
  (LeanCanny.pair (BinaryNatCode.encode (2 ^ 100)) [])) == []

-- Rotation must move the first old coordinate to the last new coordinate.
private def vector : List Bool := FixedWidthNatVector.encode 3 3 (fun i => if i = 0 then 1 else if i = 1 then 2 else 5)
#guard FixedWidthRotate.word (fun _ => 3) (fun _ => 3) (fun _ => vector) [] ==
  FixedWidthNatVector.encode 3 3 (fun i => if i = 0 then 5 else if i = 1 then 1 else 2)
#guard FixedWidthRotate.word (fun _ => 0) (fun _ => 3) (fun _ => vector) [] == []
#guard FixedWidthRotate.word (fun _ => 3) (fun _ => 0) (fun _ => vector) [] == []

-- In dimension zero every exponent query refers to the constant coefficient,
-- even with an unrelated input word and a zero-width exponent block.
example : SizedCollectedCoefficient.value (fun _ => 0) (fun _ => 0)
    (fun _ => (Term.const 7).toData.toBits) id (fun _ => BinaryNatCode.encode 4) [true, false] = BinaryNatCode.encode 2 := by
  unfold SizedCollectedCoefficient.value
  rw [TermView.term_toBits]
  have he : RationalSubstitution.Indexed.exponentVector 0
      (FixedWidthQuery.coordinate (fun _ => 0) id [true, false]) = 0 := Subsingleton.elim _ _
  rw [he]
  simp only [Term.finitePolynomial, MvPolynomial.coeff_C, ite_true]
  rfl

-- At the native binary degree width no extra exponent-fit certificate is
-- assumed by the caller. The selected direction is included in this reader.
example {P : BoundedFullWriter.Readers} (h : P.PolyTime)
    {row : (c : List Bool) → Fin (P.dim c + 4)} (hi : UnaryFn (fun c => (row c).val))
    {target modulus : List Bool → List Bool} (ht : target ∈ FP) (hm : modulus ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (BoundedCriticalCoefficient.value P (BoundedFullDirectionChoice.record P) row
      (fun c => (BoundedFullWriter.degree P c).size) target modulus) :=
  BoundedCriticalCoefficient.selected_evaluator h hi
    ((UnaryFn.length (BoundedFullWriter.degree_binary h).bits_mem_FP).of_eq
      (fun _ => BinaryNatCode.length_encode _)) ht hm ha (fun _ => Nat.lt_size_self _)

end NativeCriticalCoefficientTests

namespace NativeProjectionCoefficientTests
open LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open SubtractiveCharacteristicBits

-- The identity correction is negative, is confined to the constant retained
-- coefficient, and vanishes off the diagonal and modulo one.
#guard finish (LeanCanny.pair (packet [] (BinaryNatCode.encode 4) 2 2 0 1) []) ==
  BinaryNatCode.encode 4
#guard finish (LeanCanny.pair (packet [] (BinaryNatCode.encode 4) 2 2 1 1) []) == []
#guard finish (LeanCanny.pair (packet [] (BinaryNatCode.encode 4) 2 3 0 1) []) == []
#guard finish (LeanCanny.pair (packet [] [] 2 2 0 1) []) == []
#guard finish (LeanCanny.pair (packet [] (BinaryNatCode.encode 4) 2 2 0 2) []) == []

-- The public reader includes direction selection, separator selection, the
-- determinant and the search for the first nonzero characteristic coefficient.
example {P : BoundedFullWriter.Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (BoundedProjectionCoefficient.value P) :=
  BoundedProjectionCoefficient.evaluator h ha

end NativeProjectionCoefficientTests

namespace ProjectionRationalCutTests
open LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR

-- The cut (3 - 1)/(3 + 1) = 1/2 gives 4 X - 2. Negative constants,
-- the denominator's successor, modulus one, and absent coefficients matter.
private def halfCut : List Bool := LeanCanny.pair []
  (LeanCanny.pair (BinaryNatCode.encode 3) (LeanCanny.pair (BinaryNatCode.encode 1) (BinaryNatCode.encode 3)))
private def modularCut (c : List Bool) (k m : ℕ) : List Bool :=
  LeanCanny.pair (LeanCanny.pair c (BinaryNatCode.encode k)) (BinaryNatCode.encode m)

#guard RationalCutBits.coefficient (modularCut halfCut 0 4) == BinaryNatCode.encode 3
#guard RationalCutBits.coefficient (modularCut halfCut 1 4) == BinaryNatCode.encode 4
#guard RationalCutBits.coefficient (modularCut halfCut 2 4) == []
#guard RationalCutBits.coefficient (modularCut halfCut 0 0) == []
#guard RationalCutBits.coefficient (modularCut halfCut 1 0) == []

-- An empty denominator predecessor gives denominator one, including
-- a negative threshold: (1 - 3)/(0 + 1) = -2, whose query is X + 2.
private def negativeCut : List Bool := LeanCanny.pair []
  (LeanCanny.pair (BinaryNatCode.encode 1) (LeanCanny.pair (BinaryNatCode.encode 3) []))
#guard RationalCutBits.coefficient (modularCut negativeCut 0 4) == BinaryNatCode.encode 2
#guard RationalCutBits.coefficient (modularCut negativeCut 1 4) == BinaryNatCode.encode 1

example {P : BoundedFullWriter.Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceDecider (BoundedProjectionRationalCount.belowLanguage P) :=
  BoundedProjectionRationalCount.belowDecider h ha

-- Equality with the cut must not be counted as lying strictly below it.
example (P : BoundedFullWriter.Readers) (c : List Bool)
    (x : BoundedFullCriticalSamples.Samples P (LeanCanny.pairFst c))
    (he : BoundedCriticalSeparator.value P (BoundedCriticalSeparator.record P) (LeanCanny.pairFst c) x.val =
      RationalCutBits.threshold c) :
    LeanCanny.pair c (BoundedCriticalLabels.label P (LeanCanny.pairFst c) x) ∉
      BoundedProjectionRationalCount.belowLanguage P := by
  rw [BoundedProjectionRationalCount.label_below_iff, he]
  exact lt_irrefl _

end ProjectionRationalCutTests

namespace SampleLabelCertificateTests
open LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR

-- Signed rational payloads retain zero numerators and denominator one.
#guard RationalCutBits.payload (0 : ℚ) == LeanCanny.pair [] (LeanCanny.pair [] [])
#guard RationalCutBits.payload (-1 / 2 : ℚ) ==
  LeanCanny.pair [] (LeanCanny.pair (BinaryNatCode.encode 1) (BinaryNatCode.encode 1))
#guard RationalCutBits.payload (3 / 2 : ℚ) ==
  LeanCanny.pair (BinaryNatCode.encode 3) (LeanCanny.pair [] (BinaryNatCode.encode 1))

example : (WeightedProjection.term 0 (fun _ => 37)).eval (fun _ => (9 : ℝ)) = 0 := by
  simp only [WeightedProjection.eval_term, ProjectionCollision.projection, Finset.range_zero, Finset.sum_empty]

-- At projection 1/2 the cut expression 4 theta + 1 - 3 vanishes.
example : (WeightedProjection.cut 1 (fun _ => 2) 3 1 4).eval (fun _ => (1 / 4 : ℝ)) = 0 := by
  norm_num [WeightedProjection.eval_cut, ProjectionCollision.projection, Finset.sum_range_succ]

-- A root at the upper endpoint is excluded by the half-open convention.
example (P : BoundedFullWriter.Readers) (record lower upper : List Bool → List Bool)
    (c : List Bool) (x : ℕ → ℝ)
    (he : ProjectionCollision.projection (P.dim c + 4) (BoundedCriticalSeparator.weight P record c) x =
      RationalCutBits.threshold (upper c)) :
    ¬ (BoundedSampleInterval.formula P record lower upper c).Holds x := by
  rw [BoundedSampleInterval.formula_holds, he]
  exact fun h => lt_irrefl _ h.2

example (P : BoundedFullWriter.Readers) (record lower upper : List Bool → List Bool)
    (c : List Bool) (x : ℕ → ℝ)
    (he : ProjectionCollision.projection (P.dim c + 4) (BoundedCriticalSeparator.weight P record c) x =
      RationalCutBits.threshold (lower c))
    (hh : RationalCutBits.threshold (lower c) < RationalCutBits.threshold (upper c)) :
    (BoundedSampleInterval.formula P record lower upper c).Holds x := by
  rw [BoundedSampleInterval.formula_holds, he]
  exact ⟨le_rfl, hh⟩

-- The public verifier charges both root counts and the actual selected
-- sample query; no coefficient or label-validation oracle is supplied.
example {P : BoundedFullWriter.Readers} {lower upper word : List Bool → List Bool} {p : List Bool → Formula}
    (h : P.PolyTime) (hl : lower ∈ FP) (hu : upper ∈ FP) (hw : word ∈ FP)
    (hp : (fun c => (p c).encode) ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceDecider {c | BoundedSampleLabelCertificate.Certified P lower upper word p c} :=
  BoundedSampleLabelCertificate.decider h hl hu hw hp ha

-- Even if the projection polynomial has extraneous roots, no certificate
-- can manufacture a sample when the actual critical set is empty.
example (P : BoundedFullWriter.Readers) (lower upper word : List Bool → List Bool) (p : List Bool → Formula)
    (c : List Bool) [IsEmpty (BoundedFullCriticalSamples.Samples P c)] :
    ¬ BoundedSampleLabelCertificate.Certified P lower upper word p c := by
  intro hC
  obtain ⟨x, _, _⟩ := BoundedSampleLabelCertificate.accepted_unique P lower upper word p c hC
  exact isEmptyElim x

end SampleLabelCertificateTests

namespace ProjectionRootSeparationTests
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.ETR
open Polynomial

private noncomputable def repeated : ℤ[X] := (X ^ 2 - 1) ^ 2
private theorem repeated_ne_zero : repeated ≠ 0 := by
  intro hz
  have he := congrArg (Polynomial.eval (0 : ℤ)) hz
  norm_num [repeated] at he

-- Neither the source nor the root-difference polynomial needs to be square-free.
example : (repeated.derivative).eval (1 : ℤ) = 0 := by
  norm_num [repeated, Polynomial.derivative_pow]
example : IntegerRootSeparation.difference repeated ≠ 0 :=
  IntegerRootSeparation.ne_zero repeated repeated_ne_zero
example : (IntegerRootSeparation.difference repeated).eval₂ (Int.castRingHom ℝ) ((-1 : ℝ) - 1) = 0 :=
  IntegerRootSeparation.eval_difference repeated repeated_ne_zero (-1) 1
    (by norm_num [repeated, Polynomial.eval₂_pow, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_one])
    (by norm_num [repeated, Polynomial.eval₂_pow, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_one])
example : IntegerRootSeparation.difference (C (7 : ℤ)) ≠ 0 :=
  IntegerRootSeparation.ne_zero _ (by simp)

-- Negative grid indices use floor, so -3/2 lies in [-2,-1) at precision zero.
example : (DyadicIsolatingInterval.lower (-2) 0 : ℝ) ≤ -3 / 2 ∧
    (-3 / 2 : ℝ) < DyadicIsolatingInterval.upper (-2) 0 := by
  norm_num [DyadicIsolatingInterval.lower, DyadicIsolatingInterval.upper]
example : (Int.natAbs (-2)).size ≤ 0 + 1 + 1 :=
  DyadicIsolatingInterval.index_size (-2) 0 1 (-3 / 2)
    (by norm_num [DyadicIsolatingInterval.lower])
    (by norm_num [DyadicIsolatingInterval.upper]) (by norm_num)

-- An inadequately fine grid can contain two roots: separation is essential.
example : (({0, 1 / 2} : Finset ℝ).filter
    (fun t => t < (DyadicIsolatingInterval.upper 0 0 : ℝ))).card = 2 := by
  norm_num [DyadicIsolatingInterval.upper, Finset.filter_insert, Finset.filter_singleton]

example {P : BoundedFullWriter.Readers} (h : P.PolyTime) :
    BinaryFn (BoundedProjectionRootSeparation.precision P) ∧
      BinaryFn (BoundedProjectionRootSeparation.indexBits P) :=
  ⟨BoundedProjectionRootSeparation.precision_binary h, BoundedProjectionRootSeparation.indexBits_binary h⟩

end ProjectionRootSeparationTests

namespace ProjectionThomTests
open LeanCanny.Algebra LeanCanny.Encoding Polynomial

private noncomputable def repeated : ℝ[X] := (X ^ 2 - 1) ^ 2
private theorem repeated_ne_zero : repeated ≠ 0 := by
  intro hz
  have he := congrArg (Polynomial.eval (0 : ℝ)) hz
  norm_num [repeated] at he

-- The first derivative vanishes at both roots; square-freeness is unnecessary.
example : repeated.derivative.eval (-1 : ℝ) = 0 ∧ repeated.derivative.eval (1 : ℝ) = 0 := by
  norm_num [repeated, Polynomial.derivative_pow]

example : ThomEncoding.signature repeated 4 (-1) ≠ ThomEncoding.signature repeated 4 1 := by
  intro he
  have hr := ThomEncoding.root_eq repeated repeated_ne_zero 4
    (by unfold repeated; compute_degree) (-1) 1 (by norm_num [repeated]) (by norm_num [repeated])
    (fun k hk => congrFun he ⟨k, by omega⟩)
  norm_num at hr

-- Padding the degree bound preserves identification; constants have no roots.
example (a b : ℝ) (ha : (X ^ 2 - 2 : ℝ[X]).eval a = 0)
    (hb : (X ^ 2 - 2 : ℝ[X]).eval b = 0)
    (he : ThomEncoding.signature (X ^ 2 - 2) 37 a = ThomEncoding.signature (X ^ 2 - 2) 37 b) : a = b :=
  ThomEncoding.root_eq _ (by intro hz; have h := congrArg (Polynomial.eval (0 : ℝ)) hz; norm_num at h)
    37 (by compute_degree; norm_num) a b ha hb (fun k hk => congrFun he ⟨k, by omega⟩)
example : Function.Injective (fun x : {x : ℝ // (C (7 : ℝ)).IsRoot x} =>
    ThomEncoding.signature (C 7) 0 x.val) :=
  ThomEncoding.signature_injective _ (by simp) 0 (by simp)

-- Omitting the nonzero hypothesis would make root identification false.
example : ThomEncoding.signature (0 : ℝ[X]) 7 (-1) = ThomEncoding.signature 0 7 1 := by
  funext k
  simp [ThomEncoding.signature, ThomEncoding.sign]

-- Binary derivative orders are unrestricted, including zero and far above degree.
example (p : ℤ[X]) (i : ℕ) : (Polynomial.derivative^[0] p).coeff i = p.coeff i := rfl
example : (Polynomial.derivative^[1000000] (X ^ 2 + C (7 : ℤ))).coeff 0 = 0 := by
  rw [Polynomial.coeff_iterate_derivative, Polynomial.coeff_eq_zero_of_natDegree_lt (by compute_degree; norm_num)]
  exact smul_zero _
example : (Polynomial.derivative^[2] (X ^ 3 + C (7 : ℤ))).coeff 1 = 6 := by
  norm_num [Polynomial.coeff_iterate_derivative, Nat.descFactorial_succ]

-- Modular products reduce large factors and retain the modulus-one boundary.
#guard IteratedDerivativeBits.factor (fun _ => BinaryNatCode.encode 5)
  (fun _ => BinaryNatCode.encode 1000000) (fun _ => BinaryNatCode.encode 7)
  (LeanCanny.pair [] (BinaryNatCode.encode 999999)) == BinaryNatCode.encode 6
#guard IteratedDerivativeBits.factor (fun _ => BinaryNatCode.encode 5)
  (fun _ => BinaryNatCode.encode 1000000) (fun _ => BinaryNatCode.encode 1)
  (LeanCanny.pair [] (BinaryNatCode.encode 0)) == []

example {P : BoundedFullWriter.Readers} (h : P.PolyTime)
    (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (BoundedProjectionThom.value P) := BoundedProjectionThom.evaluator h ha
example (P : BoundedFullWriter.Readers) (c : List Bool) :
    Function.Injective (BoundedProjectionThom.signature P c) := BoundedProjectionThom.signature_injective P c

-- Feature orders are normalized, but an arbitrary raw modulus predecessor is retained.
#guard BoundedProjectionDerivativeSigns.query (fun _ => [true, true, false])
  (LeanCanny.pair (LeanCanny.pair [] (LeanCanny.pair (BinaryNatCode.encode 7) (BinaryNatCode.encode 1)))
    [true, false]) ==
  LeanCanny.pair (LeanCanny.pair [] (LeanCanny.pair (BinaryNatCode.encode 3) (BinaryNatCode.encode 1))) [true, false]

-- Query count is unary; derivative orders remain binary. This is not a claim
-- that the complete derivative signature has a polynomial-length encoding.
example {P : BoundedFullWriter.Readers} {features : List Bool → ℕ} {orders patternBits : List Bool → List Bool}
    {pattern : List Bool → ℕ → SignType} (h : P.PolyTime) (hc : UnaryFn features)
    (ho : orders ∈ FP) (hp : patternBits ∈ FP)
    (hs : ∀ c i, patternBits (LeanCanny.pair c (BinaryNatCode.encode i)) = InfinitesimalSign.encode (pattern c i))
    (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceDecider (BoundedProjectionDerivativeSigns.language P features orders pattern) :=
  BoundedProjectionDerivativeSigns.decider h hc ho hp hs ha

end ProjectionThomTests

namespace SparseProjectionMomentTests
open LeanCanny.Algebra LeanCanny.Encoding

-- An exponentially long feature list need not be enumerated in the spanning
-- theorem. Only its last feature distinguishes these two signatures.
private def delayed (b : Bool) (i : Fin 1000000) : SignType :=
  if i.val = 999999 then if b then .pos else .zero else .zero
private theorem delayed_injective : Function.Injective delayed := by
  intro a b he
  have h := congrFun he ⟨999999, by decide⟩
  cases a <;> cases b <;> simp_all [delayed]

example : Submodule.span ℚ (MonomialEvaluationBasis.vector
    (MvPolynomial.aeval (R := ℚ) (fun i b => (delayed b i : ℚ))) ''
      {d | d.support.card ≤ 1 ∧ ∀ i, d i ≤ 2}) = ⊤ :=
  SparseSignSpanning.signatures_span (MonomialOrder.degLex (σ := Fin 1000000)) delayed delayed_injective 1 (by decide)

-- Zero, negative, and positive signs all remain distinct. Squared features
-- are necessary to span arbitrary functions of a three-valued sign.
example : Submodule.span ℚ (MonomialEvaluationBasis.vector
    (MvPolynomial.aeval (R := ℚ) (fun _ : Fin 1 => fun s : SignType => (s : ℚ))) ''
      {d | d.support.card ≤ 2 ∧ ∀ i, d i ≤ 2}) = ⊤ :=
  SparseSignSpanning.signatures_span (MonomialOrder.degLex (σ := Fin 1)) (fun s _ => s)
    (fun _ _ h => congrFun h 0) 2 (by decide)

example : Submodule.span ℚ (MonomialEvaluationBasis.vector
    (MvPolynomial.aeval (R := ℚ) (fun (i : Fin 0) (_x : Fin 0) => (Fin.elim0 i : ℚ))) ''
      {d | d.support.card ≤ 0 ∧ ∀ i, d i ≤ 2}) = ⊤ := by
  apply SparseSignSpanning.sparse_span_eq_top (α := Fin 0) (K := ℚ)
    (MonomialOrder.degLex (σ := Fin 0)) (fun (i : Fin 0) (_x : Fin 0) => Fin.elim0 i) 0 (by decide)
  · intro x; exact Fin.elim0 x
  · intro i; exact Fin.elim0 i

-- Empty products count distinct roots, regardless of unused order fields.
example (P : BoundedFullWriter.Readers) (orders : List Bool → List Bool) (c e : List Bool) :
    BoundedProjectionMoments.moment P (fun _ => 0) orders (LeanCanny.pair c e) =
      (BoundedProjectionRootCount.count P c : ℤ) := by
  rw [BoundedProjectionMoments.moment_eq_sum]
  simp only [LeanCanny.pairFst_pair, Finset.range_zero, Finset.prod_empty,
    Finset.sum_const, nsmul_eq_mul, mul_one, BoundedProjectionRootCount.count]

example {P : BoundedFullWriter.Readers} {features : List Bool → ℕ} {orders : List Bool → List Bool}
    (h : P.PolyTime) (hc : UnaryFn features) (ho : orders ∈ FP)
    (ha : ∀ c, (LeanCanny.ETR.TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (BoundedProjectionMoments.moment P features orders q)) :=
  BoundedProjectionMoments.evaluator h hc ho ha

end SparseProjectionMomentTests

namespace ProjectionRecordTests
open LeanCanny.Algebra LeanCanny.Encoding

private def squaredNegative : List Bool := FixedWidthNatVector.encode 3 2 (fun i => if i < 2 then 1 else 0)
-- Repeated feature codes give powers; the final zero slot contributes one.
#guard SparseFeatureRecords.value (n := 3) (by decide) 3 2
  (fun i : Fin 3 => if i.val = 0 then (-1 : ℤ) else 7) squaredNegative == 1
#guard SparseFeatureRecords.value (n := 3) (by decide) 3 0
  (fun _ : Fin 3 => (0 : ℤ)) [] == 1
-- Arbitrary oversized slot codes are clamped, so the reader is total.
#guard SparseFeatureRecords.factor (n := 3) (by decide) (fun i : Fin 3 => (i.val : ℤ) + 2) 99 == 4

example (v : Fin 3 → ℤ) :
    SparseFeatureRecords.value (by decide) 6 2 v (squaredNegative ++ squaredNegative) =
      SparseFeatureRecords.value (by decide) 3 2 v squaredNegative *
        SparseFeatureRecords.value (by decide) 3 2 v squaredNegative :=
  SparseFeatureRecords.value_append (by decide) 3 3 2 v _ _ (by decide)

-- Unit polynomial coefficients preserve arbitrary raw moduli and zero padding.
#guard BoundedProjectionRecords.unit (LeanCanny.pair
  (LeanCanny.pair [] (LeanCanny.pair [] [])) (BinaryNatCode.encode 6)) == BinaryNatCode.encode 1
#guard BoundedProjectionRecords.unit (LeanCanny.pair
  (LeanCanny.pair [] (LeanCanny.pair [] (BinaryNatCode.encode 2))) (BinaryNatCode.encode 6)) == []
#guard BoundedProjectionRecords.unit (LeanCanny.pair
  (LeanCanny.pair [] (LeanCanny.pair [] [false, false])) (BinaryNatCode.encode 6)) == BinaryNatCode.encode 1
#guard BoundedProjectionRecords.unit (LeanCanny.pair
  (LeanCanny.pair [] (LeanCanny.pair [] [])) [false, false]) == []

example (P : BoundedFullWriter.Readers) (c : List Bool) :
    (BoundedProjectionRecordSpan.gram P c).rank = BoundedProjectionRootCount.count P c :=
  BoundedProjectionRecordSpan.rank_gram P c

-- The matrix entry reader takes only the actual source and its native controls.
example {P : BoundedFullWriter.Readers} (h : P.PolyTime)
    (ha : ∀ c, (LeanCanny.ETR.TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (BoundedProjectionRecordSpan.entry P q)) :=
  BoundedProjectionRecordSpan.entry_evaluator h ha

example (P : BoundedFullWriter.Readers) (c : List Bool) (i j : BoundedProjectionRecordSpan.Index P c) :
    (BoundedProjectionRecordSpan.entry P (LeanCanny.pair c
      (LeanCanny.pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) : ℚ) =
        BoundedProjectionRecordSpan.gram P c i j := BoundedProjectionRecordSpan.entry_packet P c i j

end ProjectionRecordTests

namespace ProjectionRankTests
open LeanCanny.Algebra LeanCanny.Encoding

-- Signed output conversion includes negative integers, padded moduli, and modulus one.
#guard SignedIntegerResidue.value (pair (BinaryNatCode.encode 6) (SignStatisticBits.integerCode (-5))) ==
  BinaryNatCode.encode 2
#guard SignedIntegerResidue.value (pair [false, true, true, false, false] (SignStatisticBits.integerCode 19)) ==
  BinaryNatCode.encode 5
#guard SignedIntegerResidue.value (pair [] (SignStatisticBits.integerCode (-5))) == []
#guard SignedIntegerResidue.value (pair [false, false] (SignStatisticBits.integerCode 5)) == []

-- The rank formula covers empty, zero, singular, and indefinite symmetric matrices.
example (A : Matrix (Fin 0) (Fin 0) ℚ) : A.charpoly.natTrailingDegree = 0 := by
  have h := SymmetricRankTrailing.rank_add_trailing A (by ext i; exact Fin.elim0 i)
  simp only [Fintype.card_fin] at h
  omega

example : (0 : Matrix (Fin 3) (Fin 3) ℚ).charpoly.natTrailingDegree = 3 := by
  have h := SymmetricRankTrailing.rank_add_trailing (0 : Matrix (Fin 3) (Fin 3) ℚ) (by rfl)
  simpa only [Matrix.rank_zero, zero_add, Fintype.card_fin] using h

def indefinite : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 1, 0]
example : indefinite.charpoly.natTrailingDegree = 0 := by
  have hs : indefinite.IsSymm := by decide
  have hr : indefinite.rank = 2 := Matrix.rank_of_det_ne_zero (by norm_num [indefinite, Matrix.det_fin_two])
  have h := SymmetricRankTrailing.rank_add_trailing indefinite hs
  rw [hr, Fintype.card_fin] at h
  omega

def singular : Matrix (Fin 2) (Fin 2) ℚ := !![1, 1; 1, 1]
example : singular.charpoly.natTrailingDegree = Module.finrank ℚ (LinearMap.ker singular.mulVecLin) :=
  SymmetricRankTrailing.trailing_eq_nullity singular (by decide)

example {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (B k : ℕ)
    (h : ∀ i j, (A i j).natAbs ≤ 2 ^ B) :
    (A.charpoly.coeff k).natAbs.size ≤ CharacteristicIntegerBounds.budget n B :=
  CharacteristicIntegerBounds.coefficient_bits A B h k

example (P : BoundedFullWriter.Readers) (c : List Bool) :
    BoundedProjectionPrefixRank.prefixRank P c 0 = 0 := BoundedProjectionPrefixRank.prefixRank_zero P c

example (P : BoundedFullWriter.Readers) (c : List Bool) :
    BoundedProjectionPrefixRank.prefixRank P c (2 ^ BoundedProjectionRecords.length P c) =
      BoundedProjectionRootCount.count P c := BoundedProjectionPrefixRank.prefixRank_full P c _ le_rfl

example (P : BoundedFullWriter.Readers) (c : List Bool) (k : ℕ) :
    BoundedProjectionPrefixRank.prefixRank P c (k + 1) ≤
      BoundedProjectionPrefixRank.prefixRank P c k + 1 := BoundedProjectionRankChoice.prefixRank_step P c k

example {P : BoundedFullWriter.Readers} (h : P.PolyTime)
    (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun q => BinaryNatCode.encode (BoundedProjectionPrefixRank.rank P q)) :=
  BoundedProjectionPrefixRank.evaluator h ha

example {P : BoundedFullWriter.Readers} (h : P.PolyTime)
    (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceDecider (BoundedProjectionPrefixRank.gainLanguage P) := BoundedProjectionPrefixRank.gainDecider h ha

-- Selection's validity requires a rank below the actual root count.
example (P : BoundedFullWriter.Readers) (c : List Bool) (r : ℕ)
    (hr : r < BoundedProjectionRootCount.count P c) :
    BoundedProjectionRankBasis.chosen P c r < 2 ^ BoundedProjectionRecords.length P c :=
  (BoundedProjectionRankBasis.chosen_spec P c r hr).1

example (P : BoundedFullWriter.Readers) (c : List Bool) :
    LinearIndependent ℚ (BoundedProjectionRankBasis.selected P c) := BoundedProjectionRankBasis.independent P c

example (P : BoundedFullWriter.Readers) (c : List Bool) :
    Submodule.span ℚ (Set.range (BoundedProjectionRankBasis.selected P c)) = ⊤ :=
  BoundedProjectionRankBasis.span_selected P c

example (P : BoundedFullWriter.Readers) (c : List Bool) {x y : BoundedProjectionRecordSpan.Root P c}
    (h : ∀ r, BoundedProjectionRankBasis.selected P c r x = BoundedProjectionRankBasis.selected P c r y) : x = y :=
  BoundedProjectionRankBasis.selected_separates P c h

example {P : BoundedFullWriter.Readers} (h : P.PolyTime)
    (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (BoundedProjectionBasisGram.entry P q)) :=
  BoundedProjectionBasisGram.entry_evaluator h ha

example (P : BoundedFullWriter.Readers) (c : List Bool)
    (i j : Fin (BoundedProjectionRootCount.count P c)) :
    (BoundedProjectionBasisGram.entry P (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) : ℚ) =
        BoundedProjectionBasisGram.gram P c i j := BoundedProjectionBasisGram.entry_packet P c i j

example (P : BoundedFullWriter.Readers) (c : List Bool) :
    (BoundedProjectionBasisGram.gram P c).rank = BoundedProjectionRootCount.count P c :=
  BoundedProjectionBasisGram.rank_gram P c

end ProjectionRankTests

namespace ProjectionHashTests
open LeanCanny.Algebra LeanCanny.Encoding Polynomial

-- A small characteristic can merge distinct signs; the separator chooses a larger prime.
#guard ((-1 : ℤ) : ZMod 2) = (1 : ZMod 2)
#guard ((-1 : ℤ) : ZMod 3) ≠ (1 : ZMod 3)

-- Zero features still allow separation of a singleton family.
example : ∃ t : ZMod 2, Function.Injective (fun _x : Unit => ∑ i : Fin 0, (0 : ZMod 2) * t ^ i.val) := by
  exact FiniteFeatureSeparator.exists_parameter (fun _x : Unit => fun _i : Fin 0 => (0 : ZMod 2))
    (fun _ _ _ => Subsingleton.elim _ _) (by decide)

-- Repeated values remain repeated roots of the Gram pencil.
example : (FunctionBasisPencil.pencil (1 : Matrix (Fin 2) (Fin 2) ℚ) (fun _ => 3)).det.roots.toFinset.card = 1 := by
  rw [FunctionBasisPencil.rootSet _ _ (by simp)]
  rw [Finset.image_const (by exact ⟨0, Finset.mem_univ 0⟩), Finset.card_singleton]

-- A singular matrix cannot satisfy the nonzero-determinant hypothesis.
example : (FunctionBasisPencil.pencil (0 : Matrix (Fin 1) (Fin 1) ℚ) (fun _ => 3)).det = 0 := by
  simp [FunctionBasisPencil.pencil, FunctionBasisPencil.gram, FunctionBasisPencil.weighted]

example (P : BoundedFullWriter.Readers) (c : List Bool) :
    ∃ p t : ℕ, p.Prime ∧ p < 2 ^ BoundedProjectionRootHash.bitWidth P c ∧ t < p ∧
      Function.Injective (BoundedProjectionRootHash.label P c p (t : ZMod p)) :=
  BoundedProjectionRootHash.exists_short_labels P c

example {P : BoundedFullWriter.Readers} (h : P.PolyTime) :
    UnaryFn (BoundedProjectionRootHash.bitWidth P) := BoundedProjectionRootHash.bitWidth_unary h

example (P : BoundedFullWriter.Readers) (c : List Bool) {p : ℕ} (hp : 0 < p)
    (hs : p < 2 ^ BoundedProjectionRootHash.bitWidth P c) (t : ℕ) (x : BoundedProjectionRecordSpan.Root P c) :
    (BoundedProjectionRootHash.integerValue P c p t x).natAbs.size ≤ BoundedProjectionRootHash.valueBits P c :=
  BoundedProjectionRootHash.integerValue_bits P c hp hs t x

example (P : BoundedFullWriter.Readers) (c : List Bool) (v : BoundedProjectionRecordSpan.Root P c → ℚ) :
    (BoundedProjectionBasisPencil.pencil P c v).det.roots.toFinset.card = BoundedProjectionRootCount.count P c ↔
      Function.Injective v := BoundedProjectionBasisPencil.rootCount_eq_count_iff P c v

example (P : BoundedFullWriter.Readers) (c : List Bool) :
    ∃ p t : ℕ, p.Prime ∧ p < 2 ^ BoundedProjectionRootHash.bitWidth P c ∧ t < p ∧
      (BoundedProjectionBasisPencil.pencil P c
        (fun x => (BoundedProjectionRootHash.integerValue P c p t x : ℚ))).det.roots.toFinset.card =
          BoundedProjectionRootCount.count P c := BoundedProjectionBasisPencil.exists_hash_parameters P c

end ProjectionHashTests

namespace WeightedProjectionTests
open LeanCanny.Algebra LeanCanny.Encoding

-- The modulus field is a predecessor, including when its word is padded.
#guard BoundedProjectionWeightedMoments.weight (pair
  (pair (BoundedProjectionWeightedMoments.context [true] 3 [false, true, true, false, false] 3) (pair [] []))
  (BinaryNatCode.encode 4)) == BinaryNatCode.encode 4
#guard BoundedProjectionWeightedMoments.weight (pair
  (pair (BoundedProjectionWeightedMoments.context [] 7 [] 19) (pair [] [])) []) == []
#guard BoundedProjectionPencilEntries.negateCode (SignStatisticBits.integerCode (-5)) == SignStatisticBits.integerCode 5
#guard BoundedProjectionPencilEntries.negateCode (SignStatisticBits.integerCode 0) == SignStatisticBits.integerCode 0

-- Zero summands and modulus one are valid on arbitrary source contexts.
example (P : BoundedFullWriter.Readers) (c m indices : List Bool) (t : ℕ) :
    BoundedProjectionWeightedMoments.entry P (pair (BoundedProjectionWeightedMoments.context c 0 m t) indices) = 0 := by
  simp only [BoundedProjectionWeightedMoments.entry, BoundedProjectionWeightedMoments.count,
    BoundedProjectionWeightedMoments.context, pairFst_pair, pairSnd_pair, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, Finset.range_zero, Finset.sum_empty]

example (P : BoundedFullWriter.Readers) (c indices : List Bool) (n t : ℕ) :
    BoundedProjectionWeightedMoments.entry P (pair (BoundedProjectionWeightedMoments.context c n [] t) indices) = 0 := by
  simp only [BoundedProjectionWeightedMoments.entry, BoundedProjectionWeightedMoments.term,
    BoundedProjectionWeightedMoments.base, BoundedProjectionWeightedMoments.context,
    BoundedProjectionWeightedMoments.modulus, pairFst_pair, pairSnd_pair,
    show Nat.fromBitsLE ([] : List Bool) = 0 from rfl, Nat.zero_add, Nat.mod_one, Nat.cast_zero, mul_zero,
    Finset.sum_const_zero]

-- A padded out-of-range degree does not alias the constant or linear coefficient.
example (P : BoundedFullWriter.Readers) (q : List Bool) :
    BoundedProjectionPencilEntries.coefficient P (pair q [false, true, false, false]) = 0 := by
  simp [BoundedProjectionPencilEntries.coefficient,
    show Nat.fromBitsLE [false, true, false, false] = 2 from rfl]

example {P : BoundedFullWriter.Readers} (h : P.PolyTime)
    (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (BoundedProjectionBasisMoments.moment P q)) :=
  BoundedProjectionBasisMoments.evaluator h ha

example (P : BoundedFullWriter.Readers) (c : List Bool) (i j k : Fin (BoundedProjectionRootCount.count P c)) :
    (BoundedProjectionBasisMoments.moment P (pair c (pair (BinaryNatCode.encode i.val)
      (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode k.val)))) : ℚ) =
      ∑ x : BoundedProjectionRecordSpan.Root P c, BoundedProjectionRankBasis.selected P c i x *
        BoundedProjectionRankBasis.selected P c j x * BoundedProjectionRankBasis.selected P c k x :=
  BoundedProjectionBasisMoments.moment_packet P c i j k

example {P : BoundedFullWriter.Readers} (h : P.PolyTime)
    (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (BoundedProjectionWeightedMoments.entry P q)) :=
  BoundedProjectionWeightedMoments.evaluator h ha

example (P : BoundedFullWriter.Readers) (q : List Bool) :
    (BoundedProjectionWeightedMoments.entry P q).natAbs.size ≤ BoundedProjectionWeightedMoments.entryBits P q :=
  BoundedProjectionWeightedMoments.entry_bits P q

example (P : BoundedFullWriter.Readers) (b : List Bool) (k : ℕ) :
    ((BoundedProjectionPencilEntries.matrix P b).det.coeff k).natAbs.size ≤ BoundedProjectionPencilBounds.budget P b :=
  BoundedProjectionPencilBounds.determinant_bits P b k

example {P : BoundedFullWriter.Readers} (h : P.PolyTime)
    (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (BoundedProjectionPencilCoefficient.value P) := BoundedProjectionPencilCoefficient.evaluator h ha

example (P : BoundedFullWriter.Readers) (b m : List Bool) (k : ℕ) :
    BoundedProjectionPencilCoefficient.value P (pair (pair b (BinaryNatCode.encode k)) m) =
      MatrixPower.residueBits ((((BoundedProjectionPencilEntries.matrix P b).det.coeff k : ℤ)) :
        ZMod (Nat.fromBitsLE m + 1)) := BoundedProjectionPencilCoefficient.value_packet P b k m

example {P : BoundedFullWriter.Readers} (h : P.PolyTime)
    (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceDecider (BoundedProjectionPencilRootCount.language P) := BoundedProjectionPencilRootCount.decider h ha

example (P : BoundedFullWriter.Readers) (c m : List Bool) (t : ℕ) :
    BoundedProjectionWeightedMoments.context c (BoundedProjectionRootCount.count P c) m t ∈
        BoundedProjectionPencilRootCount.language P ↔
      Function.Injective (BoundedProjectionRootHash.integerValue P c (Nat.fromBitsLE m + 1) t) :=
  BoundedProjectionPencilRootCount.language_packet P c m t

-- The selected count and parameters are computed internally by native machines.
example {P : BoundedFullWriter.Readers} (h : P.PolyTime)
    (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (BoundedProjectionHashChoice.value P) := BoundedProjectionHashChoice.evaluator h ha

example (P : BoundedFullWriter.Readers) (c : List Bool) :
    Function.Injective (BoundedProjectionHashChoice.hash P c) := BoundedProjectionHashChoice.hash_injective P c

example (P : BoundedFullWriter.Readers) (c : List Bool) (x : BoundedProjectionRecordSpan.Root P c) :
    (BoundedProjectionHashChoice.hash P c x).natAbs.size ≤ BoundedProjectionHashChoice.hashBits P c :=
  BoundedProjectionHashChoice.hash_bits P c x

example {P : BoundedFullWriter.Readers} (h : P.PolyTime) : UnaryFn (BoundedProjectionHashChoice.hashBits P) :=
  BoundedProjectionHashChoice.hashBits_unary h

end WeightedProjectionTests

namespace ProjectionEnumerationTests
open LeanCanny.Algebra LeanCanny.Encoding

-- Equality at a rational cut uses the positive denominator, including fractions.
def halfCut : List Bool := pair [] (pair (BinaryNatCode.encode 1) (pair [] (BinaryNatCode.encode 1)))
example : SignType.sign (((RationalCutBits.polynomial halfCut).map (algebraMap ℤ ℝ)).eval (1 / 2)) = 0 := by
  apply (BoundedProjectionPencilCuts.cut_sign_zero_iff halfCut (1 / 2)).mpr
  norm_num [halfCut, RationalCutBits.threshold, RationalCutBits.numerator, RationalCutBits.divisor,
    RationalCutBits.positive, RationalCutBits.negative, RationalCutBits.denominatorMinusOne,
    BinaryNatCode.encode, show Nat.fromBitsLE ([] : List Bool) = 0 from rfl,
    show Nat.fromBitsLE [true] = 1 from rfl]

example (c : List Bool) : RationalCutBits.threshold (BoundedProjectionHashCuts.integerQuery c (-5)) = (-5 : ℝ) := by
  simpa using BoundedProjectionHashCuts.integer_threshold c (-5)

-- Every accepted integer value denotes exactly one original projection root.
example (P : BoundedFullWriter.Readers) (q : List Bool) (hq : q ∈ BoundedProjectionHashCuts.language P) :
    ∃! x : BoundedProjectionRecordSpan.Root P (pairFst q),
      (BoundedProjectionHashChoice.hash P (pairFst q) x : ℝ) = RationalCutBits.threshold q :=
  BoundedProjectionHashCuts.unique_root P q hq

example {P : BoundedFullWriter.Readers} (h : P.PolyTime)
    (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceDecider (BoundedProjectionHashCuts.language P) := BoundedProjectionHashCuts.decider h ha

example {P : BoundedFullWriter.Readers} (h : P.PolyTime)
    (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun u => SignStatisticBits.integerCode (BoundedProjectionHashEnumeration.value P u)) :=
  BoundedProjectionHashEnumeration.evaluator h ha

-- Ordinal correctness requires the actual root count; the reader is total otherwise.
example (P : BoundedFullWriter.Readers) (c : List Bool) (r : ℕ) (hr : r < BoundedProjectionRootCount.count P c) :
    BoundedProjectionHashEnumeration.value P (pair c (BinaryNatCode.encode r)) ∈ BoundedProjectionHashRoots.values P c ∧
      BoundedProjectionHashRoots.rank P c (BoundedProjectionHashEnumeration.value P (pair c (BinaryNatCode.encode r))) = r :=
  BoundedProjectionHashEnumeration.value_spec P c r hr

example (P : BoundedFullWriter.Readers) (c : List Bool) :
    Function.Bijective (BoundedProjectionHashEnumeration.root P c) :=
  ⟨BoundedProjectionHashEnumeration.root_injective P c, BoundedProjectionHashEnumeration.root_surjective P c⟩

def weights (i : Fin 2) : ℚ := if i = 0 then -2 else 5
def feature (i : Fin 2) : ℚ := if i = 0 then -1 else 0
private theorem weights_injective : Function.Injective weights := by
  decide

-- Negative and zero features use the same nonzero denominator.
example : (FunctionBasisProbe.matrix (1 : Matrix (Fin 2) (Fin 2) ℚ) weights feature (weights 0)).det.coeff 1 = 7 := by
  rw [FunctionBasisProbe.coefficient_one]
  norm_num [FunctionBasisPencil.gram, weights, feature, Finset.univ_fin2]

example : (FunctionBasisProbe.matrix (1 : Matrix (Fin 2) (Fin 2) ℚ) weights (fun _ => 1) (weights 0)).det.coeff 1 = -7 := by
  rw [FunctionBasisProbe.coefficient_one]
  norm_num [FunctionBasisPencil.gram, weights, Finset.univ_fin2]

example : (FunctionBasisProbe.matrix (1 : Matrix (Fin 2) (Fin 2) ℚ) weights feature (weights 1)).det.coeff 1 = 0 := by
  rw [FunctionBasisProbe.coefficient_one]
  norm_num [FunctionBasisPencil.gram, weights, feature, Finset.univ_fin2]

example : SignType.sign ((FunctionBasisProbe.matrix (1 : Matrix (Fin 2) (Fin 2) ℚ) weights feature (weights 0)).det.coeff 1) *
    SignType.sign ((FunctionBasisProbe.matrix (1 : Matrix (Fin 2) (Fin 2) ℚ) weights (fun _ => 1) (weights 0)).det.coeff 1) = -1 := by
  have H := FunctionBasisProbe.sign_ratio (1 : Matrix (Fin 2) (Fin 2) ℚ) weights feature 0 (by simp) weights_injective
  simpa [feature] using H

-- Without separation, the denominator can vanish even for a nonsingular basis.
example : (FunctionBasisProbe.matrix (1 : Matrix (Fin 2) (Fin 2) ℚ) (fun _ => 4) (fun _ => 1) 4).det.coeff 1 = 0 := by
  have H := FunctionBasisProbe.coefficient_one (1 : Matrix (Fin 2) (Fin 2) ℚ) (fun _ => 4) (fun _ => 1) 0
  simpa [FunctionBasisPencil.gram, Finset.univ_fin2] using H

example {P : BoundedFullWriter.Readers} (h : P.PolyTime)
    (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (BoundedProjectionFeatureMoments.moment P q)) :=
  BoundedProjectionFeatureMoments.evaluator h ha

example (P : BoundedFullWriter.Readers) (c : List Bool) (i j : Fin (BoundedProjectionRootCount.count P c))
    (d : BoundedProjectionMoments.Feature P c) :
    (BoundedProjectionFeatureMoments.moment P (pair c (pair (BinaryNatCode.encode i.val)
      (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode d.val)))) : ℚ) =
      ∑ x : BoundedProjectionRecordSpan.Root P c, BoundedProjectionRankBasis.selected P c i x *
        BoundedProjectionRankBasis.selected P c j x * (BoundedProjectionMoments.signature P c x d : ℚ) :=
  BoundedProjectionFeatureMoments.moment_packet P c i j d

example (P : BoundedFullWriter.Readers) (c : List Bool) (r : Fin (BoundedProjectionRootCount.count P c))
    (d : BoundedProjectionMoments.Feature P c) :
    SignType.sign ((BoundedProjectionSignatureProbe.matrix P c (fun x => (BoundedProjectionMoments.signature P c x d : ℚ))
      (BoundedProjectionHashEnumeration.value P (pair c (BinaryNatCode.encode r.val)))).det.coeff 1) *
      SignType.sign ((BoundedProjectionSignatureProbe.matrix P c (fun _ => 1)
        (BoundedProjectionHashEnumeration.value P (pair c (BinaryNatCode.encode r.val)))).det.coeff 1) =
      BoundedProjectionMoments.signature P c (BoundedProjectionHashEnumeration.root P c r) d :=
  BoundedProjectionSignatureProbe.signature_at_ordinal P c r d

end ProjectionEnumerationTests

namespace ProjectionSignatureReadTests
open LeanCanny.Algebra LeanCanny.Encoding
open scoped Classical

-- Signed operands may have redundant high zero bits or nonzero parts on both sides.
#guard SignedIntegerArithmetic.canonical (pair [true, false, false] [true, true, false]) ==
  SignStatisticBits.integerCode (-2)
#guard SignedIntegerArithmetic.canonical (pair [true, false] [true]) == SignStatisticBits.integerCode 0
#guard SignedIntegerArithmetic.subtract (pair (SignStatisticBits.integerCode (-3)) (SignStatisticBits.integerCode 5)) ==
  SignStatisticBits.integerCode (-8)
#guard SignedIntegerArithmetic.subtract (pair (SignStatisticBits.integerCode 5) (SignStatisticBits.integerCode (-3))) ==
  SignStatisticBits.integerCode 8
#guard SignedIntegerArithmetic.subtract (pair (SignStatisticBits.integerCode (-3)) (SignStatisticBits.integerCode (-3))) ==
  SignStatisticBits.integerCode 0

-- All nine pairs, including zero denominators, have total sign-tag semantics.
example (a b : SignType) :
    BoundedProjectionSignatureRead.multiplyTags (pair (InfinitesimalSign.encode a) (InfinitesimalSign.encode b)) =
      InfinitesimalSign.encode (a * b) := BoundedProjectionSignatureRead.multiplyTags_packet a b
#guard BoundedProjectionSignatureRead.multiplyTags (pair [true] [false, true]) == [true]
#guard BoundedProjectionSignatureRead.multiplyTags (pair [true] [true]) == [false, true]
#guard BoundedProjectionSignatureRead.multiplyTags (pair [] [true]) == []

-- Entry degrees use decoded values, so padded zero and one remain valid.
example (P : BoundedFullWriter.Readers) (unit : Bool) (e : List Bool) :
    BoundedProjectionProbeEntries.coefficient P unit (pair e [false, false]) = BoundedProjectionProbeEntries.constant P e := by
  simp only [BoundedProjectionProbeEntries.coefficient, pairFst_pair, pairSnd_pair,
    show Nat.fromBitsLE [false, false] = 0 from rfl, ↓reduceIte]

example (P : BoundedFullWriter.Readers) (unit : Bool) (e : List Bool) :
    BoundedProjectionProbeEntries.coefficient P unit (pair e [true, false]) = BoundedProjectionProbeEntries.linear P unit e := by
  simp only [BoundedProjectionProbeEntries.coefficient, pairFst_pair, pairSnd_pair,
    show Nat.fromBitsLE [true, false] = 1 from rfl, one_ne_zero, ↓reduceIte]

example (P : BoundedFullWriter.Readers) (unit : Bool) (e : List Bool) :
    BoundedProjectionProbeEntries.coefficient P unit (pair e [false, true, false]) = 0 := by
  simp only [BoundedProjectionProbeEntries.coefficient, pairSnd_pair,
    show Nat.fromBitsLE [false, true, false] = 2 from rfl,
    show ¬(2 : ℕ) = 0 from by decide, show ¬(2 : ℕ) = 1 from by decide, ↓reduceIte]

noncomputable def emptyFamily : IntegerPolynomialMatrixBits.Family where
  dimension _ := 0
  matrix _ := 0

-- Empty determinant is one; all its positive coefficients are zero, at raw padded moduli too.
example (c m : List Bool) :
    IntegerPolynomialMatrixBits.value emptyFamily (pair (pair c (BinaryNatCode.encode 0)) m) =
      MatrixPower.residueBits (1 : ZMod (Nat.fromBitsLE m + 1)) := by
  rw [IntegerPolynomialMatrixBits.value_packet]
  change MatrixPower.residueBits (((0 : Matrix (Fin 0) (Fin 0) (Polynomial ℤ)).det.coeff 0 : ℤ) : ZMod (Nat.fromBitsLE m + 1)) = _
  rw [Matrix.det_isEmpty, Polynomial.coeff_one_zero, Int.cast_one]

example (c : List Bool) :
    IntegerPolynomialMatrixBits.value emptyFamily (pair (pair c (BinaryNatCode.encode 1)) [false, false]) =
      MatrixPower.residueBits (0 : ZMod (Nat.fromBitsLE [false, false] + 1)) := by
  rw [IntegerPolynomialMatrixBits.value_packet]
  change MatrixPower.residueBits (((0 : Matrix (Fin 0) (Fin 0) (Polynomial ℤ)).det.coeff 1 : ℤ) : ZMod (Nat.fromBitsLE [false, false] + 1)) = _
  rw [Matrix.det_isEmpty, Polynomial.coeff_one, ite_eq_right one_ne_zero, Int.cast_zero]

example {P : BoundedFullWriter.Readers} (h : P.PolyTime)
    (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) (unit : Bool) :
    SpaceFunction (BoundedProjectionProbeCoefficient.value P unit) :=
  BoundedProjectionProbeCoefficient.evaluator h ha unit

example {P : BoundedFullWriter.Readers} (h : P.PolyTime)
    (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) (unit : Bool) :
    SpaceFunction (fun z => InfinitesimalSign.encode
      (SignType.sign (BoundedProjectionProbeCoefficient.firstCoefficient P unit z))) :=
  BoundedProjectionProbeCoefficient.sign_evaluator h ha unit

-- Both the ordinal label and the separating parameters are computed internally.
example {P : BoundedFullWriter.Readers} (h : P.PolyTime)
    (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (BoundedProjectionSignatureRead.value P) := BoundedProjectionSignatureRead.evaluator h ha

example (P : BoundedFullWriter.Readers) (c : List Bool) (r : Fin (BoundedProjectionRootCount.count P c))
    (d : BoundedProjectionMoments.Feature P c) :
    BoundedProjectionSignatureRead.value P (pair (pair c (BinaryNatCode.encode r.val)) (BinaryNatCode.encode d.val)) =
      InfinitesimalSign.encode (BoundedProjectionMoments.signature P c (BoundedProjectionHashEnumeration.root P c r) d) :=
  BoundedProjectionSignatureRead.signature_packet P c r d

-- This contract includes every natural order, not only the finite feature range.
example (P : BoundedFullWriter.Readers) (c : List Bool) (r : Fin (BoundedProjectionRootCount.count P c)) (k : ℕ) :
    BoundedProjectionSignatureRead.value P (pair (pair c (BinaryNatCode.encode r.val)) (BinaryNatCode.encode k)) =
      InfinitesimalSign.encode (SignType.sign
        (((BoundedProjectionThom.polynomial P c k).map (Int.castRingHom ℝ)).eval
          (BoundedProjectionHashEnumeration.root P c r).val)) :=
  BoundedProjectionSignatureRead.derivative_packet P c r k

example (P : BoundedFullWriter.Readers) (c : List Bool) :
    Function.Injective (BoundedProjectionSignatureRead.signature P c) :=
  BoundedProjectionSignatureRead.signature_injective P c

example (P : BoundedFullWriter.Readers) (c : List Bool) :
    Set.range (BoundedProjectionSignatureRead.signature P c) = Set.range (BoundedProjectionMoments.signature P c) :=
  BoundedProjectionSignatureRead.signature_range P c

end ProjectionSignatureReadTests

namespace ProjectionRootOrderTests
open LeanCanny.Algebra LeanCanny.Encoding

def leftSigns (k : ℕ) : SignType := if k = 1 then .neg else if k = 2 then .pos else .zero
def rightSigns (k : ℕ) : SignType := if k = 1 then .pos else if k = 2 then .pos else .zero
#guard ThomEncoding.orderScan leftSigns rightSigns 3
#guard !ThomEncoding.orderScan rightSigns leftSigns 3
#guard !ThomEncoding.orderScan leftSigns leftSigns 3
#guard !ThomEncoding.orderScan leftSigns rightSigns 0

-- A negative common next derivative reverses the local sign order.
#guard ThomEncoding.direction .pos .neg .neg
#guard !ThomEncoding.direction .pos .neg .pos
#guard !ThomEncoding.direction .neg .pos .zero
#guard ThomOrderBits.orient (pair (pair [false, true] [true]) [true])
#guard !ThomOrderBits.orient (pair (pair [false, true] [true]) [])

def delayedLeft (k : ℕ) : SignType := if k = 100 then .neg else .pos
def delayedRight (k : ℕ) : SignType := if k = 0 then .neg else .pos
-- The later difference replaces the earlier comparison; truncating early is wrong.
#guard !ThomEncoding.orderScan delayedLeft delayedRight 100
#guard ThomEncoding.orderScan delayedLeft delayedRight 102

noncomputable def repeatedPolynomial : Polynomial ℝ := (Polynomial.X ^ 2 - 1) ^ 2
private theorem repeatedPolynomial_ne_zero : repeatedPolynomial ≠ 0 := by
  intro h
  have H := congrArg (fun p : Polynomial ℝ => p.eval 0) h
  norm_num [repeatedPolynomial] at H

-- Repeated roots require later derivatives but obey the same comparison theorem.
example : ThomEncoding.orderScan (ThomEncoding.sign repeatedPolynomial (-1)) (ThomEncoding.sign repeatedPolynomial 1)
    (repeatedPolynomial.natDegree + 1) = true := by
  rw [ThomEncoding.orderScan_roots repeatedPolynomial repeatedPolynomial_ne_zero _ le_rfl _ _
    (by norm_num [Polynomial.IsRoot, repeatedPolynomial]) (by norm_num [Polynomial.IsRoot, repeatedPolynomial])]
  norm_num

example (p : Polynomial ℝ) (hp : p ≠ 0) (D : ℕ) (hD : p.natDegree ≤ D)
    (a b : ℝ) (ha : p.IsRoot a) (hb : p.IsRoot b) :
    ThomEncoding.orderScan (ThomEncoding.sign p a) (ThomEncoding.sign p b) (D + 1) = decide (a < b) :=
  ThomEncoding.orderScan_roots p hp D hD a b ha hb

-- The native scan remains one bit on arbitrary or malformed child replies.
example (f : List Bool → List Bool) (q : List Bool) (n : ℕ) :
    (BoundedFold.fold (ThomOrderBits.update f) (fun _ => [false]) q n).length = 1 :=
  ThomOrderBits.fold_length f q n

example {P : BoundedFullWriter.Readers} (h : P.PolyTime)
    (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (BoundedProjectionRootOrder.value P) := BoundedProjectionRootOrder.evaluator h ha

example (P : BoundedFullWriter.Readers) (c : List Bool) (a b : Fin (BoundedProjectionRootCount.count P c)) :
    BoundedProjectionRootOrder.value P (pair c (pair (BinaryNatCode.encode a.val) (BinaryNatCode.encode b.val))) =
      [decide ((BoundedProjectionHashEnumeration.root P c a).val < (BoundedProjectionHashEnumeration.root P c b).val)] :=
  BoundedProjectionRootOrder.value_packet P c a b

example {P : BoundedFullWriter.Readers} (h : P.PolyTime)
    (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun u => BinaryNatCode.encode (BoundedProjectionRootRank.value P u)) :=
  BoundedProjectionRootRank.evaluator h ha

example (P : BoundedFullWriter.Readers) (c : List Bool) (a : Fin (BoundedProjectionRootCount.count P c)) :
    BoundedProjectionRootRank.value P (pair c (BinaryNatCode.encode a.val)) = BoundedProjectionRootOrder.rank P c a :=
  BoundedProjectionRootRank.value_packet P c a

example {P : BoundedFullWriter.Readers} (h : P.PolyTime)
    (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun u => BinaryNatCode.encode (BoundedProjectionOrderedRoot.index P u)) :=
  BoundedProjectionOrderedRoot.evaluator h ha

example (P : BoundedFullWriter.Readers) (c : List Bool) :
    StrictMono (fun r => (BoundedProjectionOrderedRoot.root P c r).val) :=
  BoundedProjectionOrderedRoot.root_strictMono P c

example {P : BoundedFullWriter.Readers} (h : P.PolyTime)
    (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (BoundedProjectionOrderedRoot.sign P) := BoundedProjectionOrderedRoot.sign_evaluator h ha

example (P : BoundedFullWriter.Readers) (c : List Bool) (r : Fin (BoundedProjectionRootCount.count P c)) (k : ℕ) :
    BoundedProjectionOrderedRoot.sign P (pair (pair c (BinaryNatCode.encode r.val)) (BinaryNatCode.encode k)) =
      InfinitesimalSign.encode (SignType.sign
        (((BoundedProjectionThom.polynomial P c k).map (Int.castRingHom ℝ)).eval (BoundedProjectionOrderedRoot.root P c r).val)) :=
  BoundedProjectionOrderedRoot.sign_packet P c r k

end ProjectionRootOrderTests

namespace ProjectionTestSignTests
open LeanCanny.Algebra LeanCanny.Encoding
open BoundedProjectionTestMoments

private theorem empty_first (c : List Bool) :
    IntegerPolynomialMatrixBits.firstCoefficient ProjectionSignatureReadTests.emptyFamily c = 0 := by
  change (0 : Matrix (Fin 0) (Fin 0) (Polynomial ℤ)).det.coeff 1 = 0
  rw [Matrix.det_isEmpty]
  simp only [Polynomial.coeff_one, one_ne_zero, ite_false]

-- The empty determinant is one, but its first coefficient and extracted sign are zero.
example : SpaceFunction (fun _ : List Bool => ([] : List Bool)) := by
  have hc : IntegerPolynomialMatrixBits.EntryCorrect ProjectionSignatureReadTests.emptyFamily (fun _ => []) := by
    intro c i
    exact Fin.elim0 i
  have E := IntegerPolynomialMatrixBits.firstSign_evaluator ProjectionSignatureReadTests.emptyFamily
    (SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP [])) hc (BinaryFn.const 0) (fun _ => 0) (BinaryFn.const 0)
    (by intro c; simp only [empty_first, Int.natAbs_zero, Nat.size_zero, le_refl])
  exact E.congr (funext fun c => by simp only [empty_first, sign_zero, InfinitesimalSign.encode])

noncomputable def zeroTest : Test where
  polynomial _ := 0
  degree _ := 0
  mass _ := 0
  polynomial_degree _ := by simp
  polynomial_mass _ := by simp

noncomputable def zeroAccess : zeroTest.Access where
  degree_binary := BinaryFn.const 0
  mass_binary := BinaryFn.const 0
  coefficient _ := []
  coefficient_eq c k m _ := by
    simp [zeroTest, IntegerTarskiSeedBits.integerResidue, MatrixPower.residueBits, BinaryNatCode.encode]
  evaluator := SpaceFunction.ofFP _ (constFn_mem_FP [])

example {P : BoundedFullWriter.Readers} (h : P.PolyTime)
    (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (BoundedProjectionTestSign.value P zeroTest) := BoundedProjectionTestSign.evaluator h zeroAccess ha

-- The identically zero test is allowed, even at repeated or extraneous roots.
example (P : BoundedFullWriter.Readers) (c : List Bool) (r : Fin (BoundedProjectionRootCount.count P c)) :
    BoundedProjectionTestSign.value P zeroTest (pair c (BinaryNatCode.encode r.val)) = [] := by
  rw [BoundedProjectionTestSign.value_packet]
  simp only [sign, zeroTest, Polynomial.map_zero, Polynomial.eval_zero, sign_zero, InfinitesimalSign.encode]

noncomputable def negativeTest : Test where
  polynomial _ := Polynomial.C (-3)
  degree _ := 0
  mass _ := 2
  polynomial_degree _ := by simp
  polynomial_mass _ := by rw [coefficientMass_C]; norm_num

example (P : BoundedFullWriter.Readers) (c : List Bool) (r : Fin (BoundedProjectionRootCount.count P c)) :
    BoundedProjectionTestSign.value P negativeTest (pair c (BinaryNatCode.encode r.val)) = [true] := by
  rw [BoundedProjectionTestSign.value_packet]
  norm_num [sign, negativeTest, InfinitesimalSign.encode]

-- Only ordinary modular polynomial coefficients are leaves of the generic query.
example {P : BoundedFullWriter.Readers} (h : P.PolyTime) (T : Test) (A : T.Access)
    (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (BoundedProjectionTestSign.value P T) := BoundedProjectionTestSign.evaluator h A ha

example {P : BoundedFullWriter.Readers} (h : P.PolyTime) (T : Test) (A : T.Access)
    (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) (s : SignType) :
    SpaceDecider (BoundedProjectionTestSign.language P T s) := BoundedProjectionTestSign.decider h A ha s

-- Invalid root ordinals are rejected, rather than querying the total fallback label.
example (P : BoundedFullWriter.Readers) (T : Test) (s : SignType) (u : List Bool)
    (hu : BoundedProjectionRootCount.count P (pairFst u) ≤ Nat.fromBitsLE (pairSnd u)) :
    u ∉ BoundedProjectionTestSign.language P T s := BoundedProjectionTestSign.language_invalid P T s u hu

example (P : BoundedFullWriter.Readers) (T : Test) (c : List Bool) (r : Fin (BoundedProjectionRootCount.count P c)) :
    BoundedProjectionTestSign.value P T (pair c (BinaryNatCode.encode r.val)) =
      InfinitesimalSign.encode (sign T c (BoundedProjectionOrderedRoot.root P c r).val) :=
  BoundedProjectionTestSign.value_packet P T c r

example {P : BoundedFullWriter.Readers} (h : P.PolyTime)
    (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceDecider (BoundedProjectionTestSign.language P BoundedProjectionTestSign.rationalCut .neg) :=
  BoundedProjectionTestSign.decider h BoundedProjectionTestSign.rationalCutAccess ha .neg

example (P : BoundedFullWriter.Readers) (c : List Bool) (r : Fin (BoundedProjectionRootCount.count P c)) :
    pair c (BinaryNatCode.encode r.val) ∈ BoundedProjectionTestSign.language P BoundedProjectionTestSign.rationalCut .neg ↔
      (BoundedProjectionOrderedRoot.root P c r).val < RationalCutBits.threshold c :=
  BoundedProjectionTestSign.rationalCut_below P c r

example (P : BoundedFullWriter.Readers) (T : Test) (q : List Bool) :
    (moment P T q).natAbs ≤ 2 ^ BoundedCriticalProjection.labelWidth P (pairFst q) :=
  moment_bound P T q

end ProjectionTestSignTests

namespace AlgebraicSliceTests
open LeanCanny.Algebra LeanCanny.Encoding Polynomial
open scoped Classical

example (p q : (ℤ[X])[X]) (m n j D : ℕ)
    (hp : ∀ i, (p.coeff i).natDegree ≤ D) (hq : ∀ i, (q.coeff i).natDegree ≤ D) :
    (PrincipalSubresultant.signedPsc p q m n j).natDegree ≤ (m + n + 1) * D :=
  PrincipalSubresultant.signedPsc_parameter_degree p q m n j D hp hq

-- The native degree scanner needs coefficient-zero tests, not integer coefficients.
example : SpaceFunction (fun _ : List Bool => BinaryNatCode.encode 0) := by
  have E := PolynomialDegreeBits.offsetEvaluator (SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP []))
    (fun _ => BinaryNatCode.encode 0) (constFn_mem_FP _) (fun _ => (0 : ℝ[X]))
    (by intro c; simp only [Polynomial.natDegree_zero, BinaryNatCode.encode, Nat.fromBitsLE_bits, le_refl])
    (by intro c i; simp)
  exact E.congr (funext fun c => by simp only [ite_true])

example : PolynomialDegreeBits.scan (fun i => (Polynomial.C (1 : ℝ)).coeff i) 3 = 1 := by
  rw [PolynomialDegreeBits.scan_eq_degree _ _ (by simp)]
  simp

-- Symbolic leading coefficients can vanish at an algebraic parameter.
example (t : ℝ) (ht : t ^ 2 = 2) :
    (((Polynomial.C ((Polynomial.X ^ 2 - 2 : ℤ[X]))) * Polynomial.X + 1 : (ℤ[X])[X]).map
      (ParameterTarski.evalHom t)) = (1 : ℝ[X]) := by
  simp [ParameterTarski.evalHom]
  rw [← Polynomial.C_pow, ht]
  simp

example : (((Polynomial.C (Polynomial.X : ℤ[X])) * Polynomial.X : (ℤ[X])[X]).map
    (ParameterTarski.evalHom 0)) = (0 : ℝ[X]) := by
  simp [ParameterTarski.evalHom]

-- Existing certified bivariate readers are accepted directly.
example (F : DyadicPolynomialBits.Family) (hF : DyadicPolynomialBits.ControlsPolyTime F)
    (A : CertifiedPolynomial.BivariateReader F.polynomial) : BoundedAlgebraicSlice.Family.Access (BoundedAlgebraicSlice.Family.ofDyadic F) :=
  BoundedAlgebraicSlice.Family.accessOfDyadic F hF A

example {P : BoundedFullWriter.Readers} (h : P.PolyTime) (F : BoundedAlgebraicSlice.Family) (A : F.Access)
    (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (BoundedAlgebraicSlice.coefficientSign P F) := BoundedAlgebraicSlice.coefficientSign_evaluator h A ha

example (P : BoundedFullWriter.Readers) (F : BoundedAlgebraicSlice.Family) (u : List Bool) (k : ℕ) :
    BoundedAlgebraicSlice.coefficientSign P F (pair u (BinaryNatCode.encode k)) = [] ↔
      (BoundedAlgebraicSlice.specialized P F u).coeff k = 0 := BoundedAlgebraicSlice.coefficient_zero P F u k

example {P : BoundedFullWriter.Readers} (h : P.PolyTime) (F : BoundedAlgebraicSlice.Family) (A : F.Access)
    (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun u => BinaryNatCode.encode (BoundedAlgebraicSlice.offset P F u)) :=
  BoundedAlgebraicSlice.offset_evaluator h A ha

example {P : BoundedFullWriter.Readers} (h : P.PolyTime) (F : BoundedAlgebraicSlice.Family) (A : F.Access)
    (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun u => BinaryNatCode.encode (BoundedAlgebraicSlice.degree P F u)) :=
  BoundedAlgebraicSlice.degree_evaluator h A ha

example (P : BoundedFullWriter.Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool)
    (r : Fin (BoundedProjectionRootCount.count P c)) :
    BoundedAlgebraicSlice.degree P F (pair c (BinaryNatCode.encode r.val)) =
      (F.slice c (BoundedProjectionOrderedRoot.root P c r).val).natDegree :=
  BoundedAlgebraicSlice.degree_packet P F c r

example {P : BoundedFullWriter.Readers} (h : P.PolyTime) (F : BoundedAlgebraicSlice.Family) (A : F.Access)
    (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (BoundedAlgebraicSlice.leading P F) := BoundedAlgebraicSlice.leading_evaluator h A ha

example {P : BoundedFullWriter.Readers} (h : P.PolyTime) (F : BoundedAlgebraicSlice.Family) (A : F.Access)
    (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceDecider (BoundedAlgebraicSlice.nonzeroLanguage P F) := BoundedAlgebraicSlice.nonzero_decider h A ha

example (P : BoundedFullWriter.Readers) (F : BoundedAlgebraicSlice.Family) (u : List Bool)
    (hu : u ∉ BoundedAlgebraicSlice.valid P) : u ∉ BoundedAlgebraicSlice.nonzeroLanguage P F := by
  simp only [BoundedAlgebraicSlice.nonzeroLanguage, Set.mem_ofPred_eq,
    BoundedAlgebraicSlice.specialized, hu, ite_false, ne_self_iff_false, not_false_eq_true]

-- Reindexing may recompute hash parameters, but preserves the real-order root.
example (P : BoundedFullWriter.Readers) (f : List Bool → List Bool) (c : List Bool)
    (r : Fin (BoundedProjectionRootCount.count (P.comp f) c)) (s : Fin (BoundedProjectionRootCount.count P (f c)))
    (hrs : r.val = s.val) :
    (BoundedProjectionOrderedRoot.root (P.comp f) c r).val = (BoundedProjectionOrderedRoot.root P (f c) s).val :=
  BoundedProjectionOrderedRoot.root_value_comp P f c r s hrs

end AlgebraicSliceTests

namespace AlgebraicPrincipalTests
open LeanCanny.Algebra LeanCanny.Encoding Polynomial
open scoped Classical

-- The parameter-polynomial determinant reader needs no symbolic degree equality.
example (F : PolynomialPrincipalMinorBits.Family) (A : PolynomialPrincipalMinorBits.Access F) :
    SpaceFunction (PolynomialPrincipalMinorBits.modular F).value := PolynomialPrincipalMinorBits.evaluator A

example (F : PolynomialPrincipalCoefficientBits.Family) (A : PolynomialPrincipalCoefficientBits.Access F)
    (z : List Bool) :
    PolynomialPrincipalCoefficientBits.residueValue A z = MatrixPower.residueBits
      (((PolynomialPrincipalCoefficientBits.polynomial F (PolynomialPrincipalMinorBits.origin z)).coeff
        (PolynomialPrincipalCoefficientBits.parameter z) : ℤ) : ZMod (PolynomialPrincipalMinorBits.modulus z)) :=
  PolynomialPrincipalCoefficientBits.residueValue_eq A z

-- Specialization commutes with principal coefficients at retained formal bounds.
example (p q : (ℤ[X])[X]) (m n j : ℕ) (t : ℝ) :
    PrincipalSubresultant.signedPsc (p.map (ParameterTarski.evalHom t)) (q.map (ParameterTarski.evalHom t)) m n j =
      (ParameterTarski.evalHom t) (PrincipalSubresultant.signedPsc p q m n j) :=
  PrincipalSubresultant.signedPsc_map_map _ _ _ _ _ _

-- Empty minors and the retained coefficient above the principal range are included.
example (p q : (ℤ[X])[X]) : PrincipalSubresultant.signedPsc p q 0 0 0 = 1 := by simp

example (p q : (ℤ[X])[X]) : PrincipalSubresultant.signedPsc p q 0 2 2 = q.coeff 2 := by simp

example {P : BoundedFullWriter.Readers} (h : P.PolyTime) (F G : BoundedAlgebraicSlice.Family)
    (A : F.Access) (B : G.Access) (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (BoundedAlgebraicSlice.Principal.value P F G) := BoundedAlgebraicSlice.Principal.evaluator h A B ha

example (P : BoundedFullWriter.Readers) (F G : BoundedAlgebraicSlice.Family) (u : List Bool)
    (hu : u ∈ BoundedAlgebraicSlice.valid P) (j : ℕ) :
    BoundedAlgebraicSlice.Principal.value P F G (pair u (BinaryNatCode.encode j)) = InfinitesimalSign.encode
      (SignType.sign (PrincipalSubresultant.signedPsc
        (BoundedAlgebraicSlice.specialized P F u) (BoundedAlgebraicSlice.specialized P G u)
        (BoundedAlgebraicSlice.degree P F u) (BoundedAlgebraicSlice.degree P G u) j)) :=
  BoundedAlgebraicSlice.Principal.value_packet P F G u hu j

example (P : BoundedFullWriter.Readers) (F G : BoundedAlgebraicSlice.Family) (q : List Bool)
    (hq : pairFst q ∉ BoundedAlgebraicSlice.valid P) : BoundedAlgebraicSlice.Principal.value P F G q = [] :=
  BoundedAlgebraicSlice.Principal.value_invalid P F G q hq

end AlgebraicPrincipalTests
