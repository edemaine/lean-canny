# Complexitylib2 space-composition experiment

The checked prototype favors adopting Complexitylib2 for space proofs. This
subproject pins Lean **4.36.0-rc1**, Complexitylib2 **cb1b7ce8**, CSLib **b5f3b77d**,
and Mathlib **625d8914** independently of the main development.

```sh
cd experiments/complexitylib2
lake update
lake exe cache get
lake build --wfail
lake env lean Check.lean
```

The build passes without warnings (3651 jobs); `Check.lean` checks four concrete
results and audits all 38 prototype declarations, including their dependencies,
for axioms beyond `propext`, `Classical.choice`, and `Quot.sound`.

## What was checked

`SpacePrototype.scan` streams a sum modulo `m+1`, for a binary count `N`,
retaining `(m, index, accumulator)`. Its correctness theorem identifies the
result with the finite sum. Its child need only be space computable:

* `scan_inSpace` uses `ComputableTidilyInSpace.budget_iterate` and a linear-space
  child. Pairing, arithmetic, and child composition keep the same budget.
* `scan_inPolySpace` accepts an arbitrary polynomial-space child. A polynomial
  bound on the encoded state suffices for the polynomial-space iteration rule.
* `slowChild` explicitly iterates the library's repeated-subtraction division
  step `m` times. Its space proof constructs this loop with `budget_iterate`;
  the enclosing scan then composes that certificate directly.
* `slowChild_rounds` proves that all `2^w` child rounds on `(2^w, 0)` increment
  the quotient. `slowChild_input_length` proves that this input occupies only
  `2*w+3` bits. This tests a prescribed exponential-time implementation. The
  remainder function itself has faster algorithms; no function lower bound
  or separation from FP is asserted.

`BoundedFoldPrototype.evaluator` is a generic replacement for the current
`BoundedFold.evaluator` interface. Context and accumulator have arbitrary fixed
binary encodings. The child receives `(context, binary index, accumulator)`.
The hypotheses are a polynomial-time binary count, a polynomial-space seed and
child, and polynomially bounded accumulator prefixes. The proof certifies the
typed update, bounds the full packet, invokes the iteration rule, and projects
the result. It requires no first-halting time, execution clock, request/resume
program, or saved-child configuration.

## Comparison and decision

The generic evaluator proof is 30 lines, versus 41 lines in the current
`BoundedFoldSpace.evaluator` proof, plus its separate controller and clock
infrastructure. The modular update's space proof is 9 lines and the linear-space
scan's is 8. Line counts alone understate the change: the new child interface
does not require constructing the explicit transition/halting certificate that
`SpaceFunction` currently carries.

The existing `BoundedFold.evaluator` already hides scheduling from its callers;
ordinary clients should not be credited with removing all that code again.
Correctness proofs, encoding lengths, and accumulator invariants are still
needed. Typed encodings avoid manually constructing and parsing binary packets,
but the prototype does not yet certify conversions for our existing raw codecs.

Adopt the new space foundation, retaining existing certified routines through
compatibility interfaces during migration. This is a change in the certificate
type, rather than a drop-in implementation with the old `SpaceFunction` return
type. First check the Lean/Mathlib upgrade and the FP-to-CSLib bridge; preserve
the existing algebraic correctness theorems and prove the required connections
between complexity interfaces. The prototype alone does not migrate the main
project or prove Canny's PSPACE theorem.

The library rules used here are in
[`InSpace`](https://github.com/SamuelSchlesinger/complexitylib2/blob/cb1b7ce8ca0757db30ec29c8365b88d86b78c80a/Complexity/Computability/Machines/Turing/MultiTape/Complexity/InSpace.lean),
[`InSpaceLib`](https://github.com/SamuelSchlesinger/complexitylib2/blob/cb1b7ce8ca0757db30ec29c8365b88d86b78c80a/Complexity/Computability/Machines/Turing/MultiTape/Complexity/InSpaceLib.lean),
and
[`PolySpace`](https://github.com/SamuelSchlesinger/complexitylib2/blob/cb1b7ce8ca0757db30ec29c8365b88d86b78c80a/Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolySpace.lean).
