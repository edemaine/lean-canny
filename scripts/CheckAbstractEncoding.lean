module

public import LeanCanny.Abstract

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
