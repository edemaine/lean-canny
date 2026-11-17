module

public import LeanCanny.Abstract
public import LeanCanny.CountingHierarchy.FlatSentenceEncoding
public meta import LeanCanny.Encoding.FlatSyntax
public meta import LeanCanny.Encoding.FlatSyntaxInverse
public meta import LeanCanny.CountingHierarchy.FlatSentenceEncoding
public meta import LeanCanny.ETR.Syntax
public meta import LeanCanny.ETR.Encoding

/-! Check the public encoding against the native inverse compiler and exercise
empty quantifier blocks and quantifier order. Run after building the abstract:
`lake env lean scripts/CheckAbstractEncoding.lean`.
-/

public section
/-! The unified abstract uses this same encoding for the PSPACE and CH results.
Exercise the inverse compiler on signed leaves, every Boolean constructor,
noncanonical tokens, and trailing input. -/
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
example : Abstract.encoding abstractMixed.tokens =
    FlatSyntax.encoding (FlatSyntax.formulaTokens mixed) := rfl

#guard FlatSyntaxInverse.parse (FlatSyntax.encoding (FlatSyntax.formulaTokens mixed)) = mixed.encode
#guard CountingHierarchy.FlatSentenceEncoding.compile (FlatSyntax.encoding (FlatSyntax.formulaTokens mixed)) = mixed.encode
#guard Formula.decode (CountingHierarchy.FlatSentenceEncoding.compile []) = none
#guard CountingHierarchy.FlatSentenceEncoding.compile
  (FlatSyntax.encoding (FlatSyntax.formulaTokens (.not .falsum)) ++ [false]) = Formula.falsum.encode

-- A term-only token stream is rejected as a formula.
example : FlatSyntax.encoding (FlatSyntax.termTokens (.const 0)) ∉
    CountingHierarchy.FlatSentenceEncoding.etrLanguage := by
  rintro ⟨p, hp, _⟩
  change FlatSyntax.encoding (FlatSyntax.termTokens (.const 0)) =
    FlatSyntax.encoding (FlatSyntax.formulaTokens p) at hp
  have he := FlatSyntax.encoding.injective hp
  cases p <;> simp [FlatSyntax.formulaTokens, FlatSyntax.termTokens, FlatSyntax.op] at he

example : LeanCanny.Abstract.ETR ∈ Cslib.Complexity.PSPACE encBits :=
  LeanCanny.Abstract.etr_in_PSPACE
example : LeanCanny.Abstract.ETR ∈ Cslib.Complexity.CountingLevel 26 encBits :=
  LeanCanny.Abstract.etr_in_CountingLevel
example : LeanCanny.Abstract.ExistsForallReal ∈ Cslib.Complexity.CountingLevel 60 encBits :=
  LeanCanny.Abstract.existsForallReal_in_CountingLevel

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
