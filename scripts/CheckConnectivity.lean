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
