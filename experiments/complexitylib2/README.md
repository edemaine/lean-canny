# Complexitylib2 space-composition experiment

The checked prototype motivated adopting Complexitylib2 for space proofs. This
subproject pins Lean **4.36.0-rc1**, Complexitylib2 **cb1b7ce8**, CSLib **b5f3b77d**,
and Mathlib **625d8914** independently of the main development.
The canonical repository is now
[Complexitylib](https://github.com/cslib-community/complexitylib). This historical
snapshot keeps the pre-rename `complexitylib2` Lake package and directory names.

```sh
cd experiments/complexitylib2
lake update
lake exe cache get
lake build --wfail
lake env lean Check.lean
```

The build passes without warnings (3651 jobs); `Check.lean` checks five concrete
results and audits all 44 prototype declarations, including their dependencies,
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

`BoundedFoldPrototype.evaluator` is a generic replacement for the original
`BoundedFold.evaluator` interface. Context and accumulator have arbitrary fixed
binary encodings. The child receives `(context, binary index, accumulator)`.
The hypotheses are a polynomial-time binary count, a polynomial-space seed and
child, and polynomially bounded accumulator prefixes. The proof certifies the
typed update, bounds the full packet, invokes the iteration rule, and projects
the result. It requires no first-halting time, execution clock, request/resume
program, or saved-child configuration. `BoundedFoldPrototype.slowScan_inPolySpace`
instantiates that generic evaluator with the concrete slow child and proves the
same scan certificate; its hypotheses are thus exercised by an actual example.

## Comparison and decision

The generic evaluator proof is about 30 lines, versus about 40 lines in the original
`BoundedFoldSpace.evaluator` proof, plus its separate controller and clock
infrastructure. The modular update's space proof is 9 lines and the linear-space
scan's is 8. Line counts alone understate the change: the new child interface
does not require constructing the explicit transition/halting certificate that
the original `SpaceFunction` carried.

The original `BoundedFold.evaluator` already hid scheduling from its callers;
ordinary clients should not be credited with removing all that code again.
Correctness proofs, encoding lengths, and accumulator invariants are still
needed. Typed encodings avoid manually constructing and parsing binary packets,
and the main development now certifies conversions for our existing raw codecs.

The main project now uses the same Lean/Mathlib pins and the native space
foundation throughout. The typed and raw-code folds, universal scan, sum and
balanced-product bits, matrix powering, and Berkowitz use compositional space
proofs. SpaceFunction and SpaceDecider are proof-only native certificates; their
old execution records, the suspended scheduler, and temporary legacy-space
adapters are removed. The FP primitives now also use native certificates; the
legacy Complexitylib dependency and its TidyFP bridge have been removed.
The main ETR closure theorem targets Complexitylib2 PSPACE directly.
Canny's ETR membership theorem is now proved in
[`CoercivePSPACE`](../../LeanCanny/ETR/CoercivePSPACE.lean).

## Upgrade compatibility check

A temporary project required both library pins, explicitly overriding CSLib and
Mathlib to the revisions above, and attempted
`lake build --wfail LeanCanny.Computation.SpaceFunction Complexitylib.Interop.Cslib.MultiTape`.
The unmodified old dependency fails on Lean 4.36.0-rc1:

* `Cobham/Internal/Simulate.lean:490` applies `CobhamFP` as a function instead of
  using set membership; Lean no longer elaborates this as the intended proposition.
* `Interop/Cslib/MultiTape/Defs.lean` constructs machines with a `tr` structure
  field. The new CSLib model uses a relation with a determinism proof and offers
  `MultiTapeTM.ofTr` for this construction. Its generic finite-state derivation
  also fails to elaborate.
* Several old proofs trigger the new unused-tactic linter.

These failures concern the historical V1 dependency. The completed main project
no longer depends on that library or its compatibility patch.

The library rules used here are in
[`InSpace`](https://github.com/cslib-community/complexitylib/blob/cb1b7ce8ca0757db30ec29c8365b88d86b78c80a/Complexity/Computability/Machines/Turing/MultiTape/Complexity/InSpace.lean),
[`InSpaceLib`](https://github.com/cslib-community/complexitylib/blob/cb1b7ce8ca0757db30ec29c8365b88d86b78c80a/Complexity/Computability/Machines/Turing/MultiTape/Complexity/InSpaceLib.lean),
and
[`PolySpace`](https://github.com/cslib-community/complexitylib/blob/cb1b7ce8ca0757db30ec29c8365b88d86b78c80a/Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolySpace.lean).
