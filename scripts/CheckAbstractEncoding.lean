module

public import LeanCanny.Abstract
public import LeanCanny.CountingHierarchy.FlatSentenceEncoding
public meta import LeanCanny.Encoding.FlatSyntax
public meta import LeanCanny.Encoding.FlatSyntaxInverse
public meta import LeanCanny.CountingHierarchy.FlatSentenceEncoding
public meta import LeanCanny.ETR.Syntax
public meta import LeanCanny.ETR.Encoding

/-! Check that derivation uses constructor metadata rather than the names,
arities or tag count of the arithmetic syntax. Run after building the abstract:
`lake env lean scripts/CheckAbstractEncoding.lean`.
-/

public section
namespace GeneratedEncodingCheck

inductive Expr where
  | number : ℤ → Expr
  | symbol : ℕ → Expr
  | empty : Expr
  | join : Expr → Expr → Expr
  | wrap : Expr → Expr

derive_syntax_encoding Expr (integers := binary) (indices := unary)

-- Three structural constructors give tags 0–2 and shift indices by three.
example (z : ℤ) : (Expr.number z).tokens = [.inl z] := rfl
example (i : ℕ) : (Expr.symbol i).tokens = [.inr (i + 3)] := rfl
example : Expr.empty.tokens = [.inr 0] := rfl
example (a b : Expr) : (Expr.join a b).tokens = .inr 1 :: (a.tokens ++ b.tokens) := rfl
example (a : Expr) : (Expr.wrap a).tokens = .inr 2 :: a.tokens := rfl

-- The generated serializer uses only the selected library encoders.
example : encoding = Turing.MultiTapeTM.encList
    (Turing.MultiTapeTM.encSum Turing.MultiTapeTM.encIntBin Turing.MultiTapeTM.encUnary) := rfl

namespace Ambiguous
inductive Expr where
  | first : ℤ → Expr
  | second : ℤ → Expr

/-- error: Multiple integer leaf constructors in GeneratedEncodingCheck.Ambiguous.Expr -/
#guard_msgs in
derive_syntax_encoding Expr (integers := binary) (indices := unary)
end Ambiguous

namespace Unsupported
inductive Expr where
  | boolean : Bool → Expr

/-- error: Unsupported field type Bool in GeneratedEncodingCheck.Unsupported.Expr.boolean; expected a supplied syntax type or a single integer/index leaf -/
#guard_msgs in
derive_syntax_encoding Expr (integers := binary) (indices := unary)
end Unsupported

end GeneratedEncodingCheck

/-! The unified abstract uses this same encoding for the PSPACE and CH results.
Exercise the inverse compiler on signed leaves, every Boolean constructor,
noncanonical tokens, and trailing input. -/
namespace UnifiedEncodingCheck
open LeanCanny LeanCanny.Encoding LeanCanny.ETR
open Turing.MultiTapeTM

private def mixed : Formula :=
  .or (.and (.eqZero (.add (.mul (.var 2) (.var 0)) (.const (-7))))
    (.ltZero (.const 3))) (.not .falsum)

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
example : LeanCanny.Abstract.ExistsForall ∈ Cslib.Complexity.CountingLevel 60 encBits :=
  LeanCanny.Abstract.existsForall_in_CountingLevel

-- The public two-block semantics includes empty blocks and keeps the
-- existential choice outside the universal block.
example : LeanCanny.Abstract.SentenceHolds (r := 0) (s := 0)
    (LeanCanny.Abstract.Formula.not .falsum) := by
  exact ⟨fun i => Fin.elim0 i, fun _ => id⟩

example : ¬LeanCanny.Abstract.SentenceHolds (r := 1) (s := 1)
    (.eqZero (.add (.var 0) (.mul (.const (-1)) (.var 1)))) := by
  rintro ⟨x, hx⟩
  have h := hx (fun _ => x 0 + 1)
  simp only [LeanCanny.Abstract.Formula.solutionSet, Set.mem_ofPred_eq,
    LeanCanny.Abstract.Term.eval, Int.cast_neg, Int.cast_one] at h
  have h0 : (0 : Fin 2) = Fin.castAdd 1 (0 : Fin 1) := rfl
  have h1 : (1 : Fin 2) = Fin.natAdd 1 (0 : Fin 1) := rfl
  rw [h0, h1, Fin.addCases_left, Fin.addCases_right] at h
  linarith

end UnifiedEncodingCheck
