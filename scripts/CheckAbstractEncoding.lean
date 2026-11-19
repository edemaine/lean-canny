module

public import LeanCanny.Abstract
public import LeanCanny.CountingHierarchy.DerivedSentenceEncoding
public meta import LeanCanny.Abstract
public meta import LeanCanny.Encoding.FlatSyntax
public meta import LeanCanny.Encoding.DerivedSyntax
public meta import LeanCanny.Encoding.FlatSyntaxInverse
public meta import LeanCanny.CountingHierarchy.DerivedSentenceEncoding
public meta import LeanCanny.ETR.Syntax
public meta import LeanCanny.ETR.Encoding

/-! Check the public encoding against the native inverse compiler and exercise
empty quantifier blocks and quantifier order. Run after building the abstract:
`lake env lean scripts/CheckAbstractEncoding.lean`.
-/

public section
/-! The unified abstract uses this same encoding for the PSPACE and CH results.
Exercise the inverse compiler on signed leaves, every Boolean constructor,
malformed words, and trailing input. -/
namespace UnifiedEncodingCheck
open LeanCanny LeanCanny.Encoding LeanCanny.ETR
open Turing.MultiTapeTM

private def mixed : Formula :=
  .or (.and (.eqZero (.add (.mul (.var 2) (.var 0)) (.const (-7))))
    (.ltZero (.const 3))) (.not .falsum)

private def abstractMixed : Abstract.Formula 3 :=
  .or (.and (.eqZero (.add (.mul (.var 2) (.var 0)) (.const (-7))))
    (.ltZero (.const 3))) (.not .false)

-- The independently specified public encoding agrees with the native compiler's input.
example : Abstract.encFormula 3 abstractMixed = DerivedSyntax.formulaEncoding mixed := rfl

#guard FlatSyntaxInverse.parse (FlatSyntax.encoding (FlatSyntax.formulaTokens mixed)) = mixed.encode
#guard CountingHierarchy.DerivedSentenceEncoding.compile (Abstract.encFormula 3 abstractMixed) = mixed.encode
#guard CountingHierarchy.DerivedSentenceEncoding.compile [] = Formula.falsum.encode
#guard CountingHierarchy.DerivedSentenceEncoding.compile
  (Abstract.encFormula 0 (.not .false) ++ [false]) = Formula.falsum.encode

-- Deeply nested formulas and dimension changes use the same uniform compiler.
private def negations (depth : ℕ) : Abstract.Formula 3 :=
  Nat.rec (.eqZero (.var 2)) (fun _ p => .not p) depth

#guard Formula.decode (CountingHierarchy.DerivedSentenceEncoding.compile
  (Abstract.encFormula 3 (negations 32))) = some (Nat.rec (.eqZero (.var 2)) (fun _ p => .not p) 32)

example : Abstract.encFormula 3 (.eqZero (.var 2)) =
    Abstract.encFormula 10000 (.eqZero (.var 2)) := by
  simp [DerivedSyntax.finite_variable_encoding]

example : LeanCanny.Abstract.ETR ∈ Cslib.Complexity.PSPACE encBits :=
  LeanCanny.Abstract.etr_in_PSPACE
example : LeanCanny.Abstract.ETR ∈ Cslib.Complexity.CountingLevel 26 encBits :=
  LeanCanny.Abstract.etr_in_CountingLevel
example : LeanCanny.Abstract.ExistsForallTheory ∈ Cslib.Complexity.CountingLevel 60 encBits :=
  LeanCanny.Abstract.existsForallTheory_in_CountingLevel
example : LeanCanny.Abstract.ExistsForallReal ⊆ Cslib.Complexity.CountingLevel 60 encBits :=
  LeanCanny.Abstract.existsForallReal_subset_CountingLevel

-- The public two-block semantics includes empty blocks and keeps the
-- existential choice outside the universal block.
example : (LeanCanny.Abstract.Formula.existsForallSolutionSet (r := 0) (s := 0)
    (.not .false)).Nonempty := by
  exact ⟨fun i => Fin.elim0 i, fun _ => id⟩

example : ¬(LeanCanny.Abstract.Formula.existsForallSolutionSet (r := 1) (s := 1)
    (.eqZero (.add (.var 0) (.mul (.const (-1)) (.var 1))))).Nonempty := by
  rintro ⟨x, hx⟩
  have h := hx (fun _ => x 0 + 1)
  simp only [LeanCanny.Abstract.Formula.solutionSet, Set.mem_ofPred_eq,
    LeanCanny.Abstract.Term.eval, Int.cast_neg, Int.cast_one] at h
  have h0 : (0 : Fin 2) = Fin.castAdd 1 (0 : Fin 1) := rfl
  have h1 : (1 : Fin 2) = Fin.natAdd 1 (0 : Fin 1) := rfl
  rw [h0, h1, Fin.addCases_left, Fin.addCases_right] at h
  linarith

end UnifiedEncodingCheck
