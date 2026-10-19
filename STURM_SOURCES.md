# Sturm–Tarski source attribution

The files in `LeanCanny/Algebra/Sturm/` adapt proofs by Kim Morrison from
[TauCeti](https://github.com/TauCetiProject/TauCeti) at revision
`034e577c895d28c058d92af4036f7ce0b03081cf`, inspected on 2026-10-19.
The original copyright and Apache 2.0 notices are retained in each file; the
[Apache 2.0 license](LICENSE) applies to this code.

| Local file | Upstream source |
| --- | --- |
| [`SignVariations.lean`](LeanCanny/Algebra/Sturm/SignVariations.lean) | [`Data/List/SignVariations.lean`](https://github.com/TauCetiProject/TauCeti/blob/034e577c895d28c058d92af4036f7ce0b03081cf/TauCeti/Data/List/SignVariations.lean) |
| [`Jumps.lean`](LeanCanny/Algebra/Sturm/Jumps.lean) | [`Data/Finset/Jumps.lean`](https://github.com/TauCetiProject/TauCeti/blob/034e577c895d28c058d92af4036f7ce0b03081cf/TauCeti/Data/Finset/Jumps.lean) |
| [`RealSigns.lean`](LeanCanny/Algebra/Sturm/RealSigns.lean) | [`Algebra/Polynomial/RealClosed/Sign.lean`](https://github.com/TauCetiProject/TauCeti/blob/034e577c895d28c058d92af4036f7ce0b03081cf/TauCeti/Algebra/Polynomial/RealClosed/Sign.lean) |
| [`Signs.lean`](LeanCanny/Algebra/Sturm/Signs.lean) | [`Algebra/Polynomial/Sturm/Signs.lean`](https://github.com/TauCetiProject/TauCeti/blob/034e577c895d28c058d92af4036f7ce0b03081cf/TauCeti/Algebra/Polynomial/Sturm/Signs.lean) |
| [`Local.lean`](LeanCanny/Algebra/Sturm/Local.lean) | [`Algebra/Polynomial/Sturm/Local.lean`](https://github.com/TauCetiProject/TauCeti/blob/034e577c895d28c058d92af4036f7ce0b03081cf/TauCeti/Algebra/Polynomial/Sturm/Local.lean) |
| [`Sequence.lean`](LeanCanny/Algebra/Sturm/Sequence.lean) | [`Algebra/Polynomial/Sturm/Sequence.lean`](https://github.com/TauCetiProject/TauCeti/blob/034e577c895d28c058d92af4036f7ce0b03081cf/TauCeti/Algebra/Polynomial/Sturm/Sequence.lean) |
| [`SignedRemainders.lean`](LeanCanny/Algebra/Sturm/SignedRemainders.lean) | [`Algebra/Polynomial/Sturm/SignedRemainders.lean`](https://github.com/TauCetiProject/TauCeti/blob/034e577c895d28c058d92af4036f7ce0b03081cf/TauCeti/Algebra/Polynomial/Sturm/SignedRemainders.lean) |
| [`Sum.lean`](LeanCanny/Algebra/Sturm/Sum.lean) | [`Algebra/Polynomial/Sturm/Sum.lean`](https://github.com/TauCetiProject/TauCeti/blob/034e577c895d28c058d92af4036f7ce0b03081cf/TauCeti/Algebra/Polynomial/Sturm/Sum.lean) |
| [`Tarski.lean`](LeanCanny/Algebra/Sturm/Tarski.lean) | [`Algebra/Polynomial/Sturm/Tarski.lean`](https://github.com/TauCetiProject/TauCeti/blob/034e577c895d28c058d92af4036f7ce0b03081cf/TauCeti/Algebra/Polynomial/Sturm/Tarski.lean) |
| [`EvalInfinity.lean`](LeanCanny/Algebra/Sturm/EvalInfinity.lean) | [`Algebra/Polynomial/Eval/Infinity.lean`](https://github.com/TauCetiProject/TauCeti/blob/034e577c895d28c058d92af4036f7ce0b03081cf/TauCeti/Algebra/Polynomial/Eval/Infinity.lean) |
| [`Infinity.lean`](LeanCanny/Algebra/Sturm/Infinity.lean) | [`Algebra/Polynomial/Sturm/Infinity.lean`](https://github.com/TauCetiProject/TauCeti/blob/034e577c895d28c058d92af4036f7ce0b03081cf/TauCeti/Algebra/Polynomial/Sturm/Infinity.lean) |

The adaptation uses the project's existing Lean and Mathlib pins rather than adding
a TauCeti dependency. All declarations live in `LeanCanny.Algebra.Sturm` so they
are included in the project axiom audit. Changes include:

- Keep the list-variation recurrence and scaling law, the finite jump-sum lemma,
  and only the second-entry lookup from the upstream sequence extensions.
- Keep the constant-sign and simple-root-crossing lemmas. Prove constant signs
  over ℝ using Mathlib's intermediate value theorem, avoiding the abstract
  real-closed-field development and the one-sided endpoint API.
- Specialize the analytic chain and Tarski theorems to ℝ. The signed remainder
  identities and the removal of common factors still work over ordered fields.
- Prove the whole-line theorem directly from the finite-interval theorem by
  choosing endpoints beyond every chain root. Retain the leading-coefficient
  and degree-parity formulas at infinity; omit the half-line formulas.
- Rename helper declarations into the project namespace and adapt imports and
  proofs to the pinned Mathlib.

[`SturmQuery.lean`](LeanCanny/Algebra/SturmQuery.lean) is the project bridge:
coefficient maps preserve signed remainder sequences and their sign variations,
rational-input queries agree with the sum of signs at distinct real roots, and
these formulas substitute into the scaled sign-pattern count.

These are kernel-checked mathematical correctness results. The reference uses
Mathlib's noncomputable polynomial operations. It does not yet give an encoded
polynomial-space implementation of signed remainders or Tarski-query evaluation.
