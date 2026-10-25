import LeanCanny.Connectivity
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
