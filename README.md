# lean-canny

Foundations for formalizing John Canny's 1988 report,
[*Some Algebraic and Geometric Computations in PSPACE*](https://www2.eecs.berkeley.edu/Pubs/TechRpts/1988/6041.html).
The report is saved as [`canny-tr.pdf`](canny-tr.pdf).

**Canny's PSPACE upper bound is not proved here yet.** The current development defines
an encoded existential theory of the reals (ETR), its reduction class ∃ℝ, and several
algebraic ingredients. It uses Lean 4 and pinned Mathlib/Complexitylib dependencies.

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake update
lake exe cache get
lake build
```

`lean-toolchain` and `lake-manifest.json` record the versions used. The public entry
point is [`LeanCanny.lean`](LeanCanny.lean).

For stricter verification:

```sh
lake build --wfail
lake env lean scripts/CheckAxioms.lean
lake env lean scripts/CheckGrammar.lean
```

The audit checks all declarations in the `LeanCanny` namespace and their transitive
dependencies, allowing only Lean's standard `propext`, `Classical.choice`, and
`Quot.sound` axioms.

## Proved so far

| Module | Result |
| --- | --- |
| [`ETR.Syntax`](LeanCanny/ETR/Syntax.lean) | Integer polynomial expressions; Boolean combinations of equality and strict inequality; real semantics; equivalence between an infinite assignment and a finite existential block. |
| [`ETR.Encoding`](LeanCanny/ETR/Encoding.lean) | A canonical binary codec with both round-trip laws; the ETR language rejects malformed strings. Integer constants use binary magnitudes; variable indices use unary. |
| [`ETR.EncodingBounds`](LeanCanny/ETR/EncodingBounds.lean) | Formula arity is at most encoded input length; binary integer payloads have linear bit overhead. |
| [`Encoding.Brackets`](LeanCanny/Encoding/Brackets.lean), [`BracketsFP`](LeanCanny/Encoding/BracketsFP.lean) | A numerical bracket criterion recognizes exactly the image of `Data.toBits`; its one-bit recognizer belongs to Complexitylib's machine-level `FP`. |
| [`Encoding.BracketAccess`](LeanCanny/Encoding/BracketAccess.lean) | Polynomial-time splitting of the first serialized node, child access, enclosing-bracket operations, and cons; exact behavior is proved against the dependency codec. |
| [`ETR.EncodingFP`](LeanCanny/ETR/EncodingFP.lean) | Polynomial-time unary-field writing and recognition, fresh-variable writing, and tagged-node construction; agreement with the typed term/formula encodings. |
| [`ETR.NumericPayloadFP`](LeanCanny/ETR/NumericPayloadFP.lean) | Polynomial-time recognition of exactly the canonical natural and signed-integer payload codes. A finite-state bit-node decoder keeps magnitudes as binary digit lists, with a linear output bound. |
| [`Encoding.TreeFold`](LeanCanny/Encoding/TreeFold.lean), [`TreeFoldFP`](LeanCanny/Encoding/TreeFoldFP.lean) | A bottom-up stack pass agrees with a generic fold on `Data` trees. Fixed finite frames with positive fixed-width injective codes give a uniform machine-level `FP` implementation, with every intermediate stack bounded. |
| [`Encoding.FiniteTreeLanguage`](LeanCanny/Encoding/FiniteTreeLanguage.lean) | Every finite-frame tree classifier yields a polynomial-time predicate on complete canonical tree encodings. |
| [`Encoding.DynamicTreeFold`](LeanCanny/Encoding/DynamicTreeFold.lean) | Input-dependent tree folds can use variable-length frames in a self-delimiting stack. Polynomial-time frame operations and polynomial intermediate stack bounds give `FP`; a polynomial additive frame-growth allowance supplies the stack bound automatically. |
| [`ETR.SyntaxClassifier`](LeanCanny/ETR/SyntaxClassifier.lean), [`SyntaxClassifierCorrect`](LeanCanny/ETR/SyntaxClassifierCorrect.lean) | A finite summary of children recognizes unary fields, bit nodes, canonical binary magnitudes, integers, terms, and formulas; every flag is proved equivalent to the corresponding typed codec image. |
| [`ETR.Grammar`](LeanCanny/ETR/Grammar.lean) | Executable, machine-certified polynomial-time recognizers for exactly the canonical term and formula encodings. Both syntax languages belong to `P`; the formula checker agrees with successful parsing by the original decoder. |
| [`ETR.Complexity`](LeanCanny/ETR/Complexity.lean) | ∃ℝ is the downward closure of ETR under Complexitylib polynomial-time many-one reductions; ETR is complete by definition; reduction closure and `P ⊆ ∃ℝ`. |
| [`ETR.PSPACEClosure`](LeanCanny/ETR/PSPACEClosure.lean) | `∃ℝ ⊆ PSPACE` is equivalent to `ETR ∈ PSPACE`, using proved PSPACE closure under polynomial-time many-one reductions. The same equivalence holds for any ∃ℝ-complete language. The ETR membership hypothesis remains open. |
| [`ETR.Normalization`](LeanCanny/ETR/Normalization.lean) | Single inequalities and disequalities become equations using fresh witnesses; pairs of equations combine through sums of squares or products. |
| [`ETR.NegationNormalForm`](LeanCanny/ETR/NegationNormalForm.lean), [`NNFEncoding`](LeanCanny/ETR/NNFEncoding.lean), [`NNFFP`](LeanCanny/ETR/NNFFP.lean), [`NNFComplexity`](LeanCanny/ETR/NNFComplexity.lean) | A total polynomial-time normalizer pushes negations to atoms, preserves real semantics and arity, and has linear output length. Both polarities and every intermediate stack are bounded, even on raw malformed trees. NNF satisfiability is ∃ℝ-complete under reductions on all binary strings. |
| [`ETR.EquationSystem`](LeanCanny/ETR/EquationSystem.lean) | Arbitrary Boolean formulas compile into equation systems. Every satisfying assignment extends to a solution, preserving the original variables; every solution satisfies the formula. |
| [`ETR.EquationNormalization`](LeanCanny/ETR/EquationNormalization.lean) | A single final sum of squares collapses the system to one equisatisfiable integer polynomial equation. |
| [`ETR.EquationSize`](LeanCanny/ETR/EquationSize.lean) | For an input of `n` bits, the resulting equation has at most `500*(n+1)^3` encoded bits and arity at most `2*n`. This includes all unary fresh-variable indices and binary integer payloads. |
| [`ETR.SingleEquation`](LeanCanny/ETR/SingleEquation.lean) | A total executable map on binary strings preserves exactly the yes-instances from ETR to the single-equation language. Malformed inputs map to `1 = 0`; the output-length bound holds on all inputs. |
| [`ETR.EquationDegree`](LeanCanny/ETR/EquationDegree.lean) | The corresponding Mathlib integer multivariate polynomial has total degree at most `4*n` and has a real zero exactly when the original formula is satisfiable. |
| [`ETR.SingleEquationComplexity`](LeanCanny/ETR/SingleEquationComplexity.lean) | A polynomial-time many-one reduction from the single-equation language to ETR; hence the single-equation language belongs to ∃ℝ. Correctness covers malformed inputs too. |
| [`ETR.SumSquaresFP`](LeanCanny/ETR/SumSquaresFP.lean) | A polynomial-time bitstring writer collapses an encoded equation list into a sum of squares. Its complete paired state grows by at most 18 bits per iteration; the output vanishes exactly when every input term does. |
| [`ETR.EquationList`](LeanCanny/ETR/EquationList.lean), [`EquationListComplexity`](LeanCanny/ETR/EquationListComplexity.lean) | An exact `FP` recognizer for encoded term lists and a polynomial-time many-one reduction from satisfiable equation systems to one equation. Malformed strings map to `1 = 0`; the equation-system language belongs to ∃ℝ. |
| [`ETR.EquationEncoding`](LeanCanny/ETR/EquationEncoding.lean), [`EquationSystemEncoding`](LeanCanny/ETR/EquationSystemEncoding.lean) | Polynomial-time writers for fresh-witness equations, Boolean selectors, conjunction, and disjunction; exact agreement with the typed operations and literal length formulas. |
| [`ETR.EquationMaskFP`](LeanCanny/ETR/EquationMaskFP.lean) | A polynomial-time pass multiplies every equation by a branch selector, preserving order. The complete loop state adds at most `factor.length + 10` bits per step on all strings. |
| [`ETR.EquationCompilerMachine`](LeanCanny/ETR/EquationCompilerMachine.lean), [`EquationCompilerBounds`](LeanCanny/ETR/EquationCompilerBounds.lean), [`EquationCompilerStateEncoding`](LeanCanny/ETR/EquationCompilerStateEncoding.lean) | A sequential stack compiler agrees exactly with `SignedFormula.equations`, terminates within twice the formula's bit length, and keeps its entire encoded state below `10000*(n+1)^3` bits throughout the run, starting fresh indices at `n`. |
| [`ETR.EquationCompilerAtomEncoding`](LeanCanny/ETR/EquationCompilerAtomEncoding.lean), [`EquationCompilerStepEncoding`](LeanCanny/ETR/EquationCompilerStepEncoding.lean), [`EquationCompilerFP`](LeanCanny/ETR/EquationCompilerFP.lean) | The encoded step implements the typed stack machine and belongs to `FP`. The bounded loop gives polynomial-time reductions from ETR to equation systems and single equations, proving both target languages ∃ℝ-complete. Correctness covers all binary strings. |
| [`Algebra.Separation`](LeanCanny/Algebra/Separation.lean) | For `m` points in a characteristic-zero field, an integer `0 ≤ c ≤ m²` makes `(a,b) ↦ a+c*b` injective. Lagrange interpolation recovers both coordinates with degree below `m`. |
| [`Algebra.GaloisDescent`](LeanCanny/Algebra/GaloisDescent.lean) | For finite point sets stable under a finite Galois group, the nodal polynomial and coordinate interpolants descend to the input field. The nodal polynomial is monic and separable, with exactly the projected points as roots. |
| [`Algebra.PrimitiveCoordinates`](LeanCanny/Algebra/PrimitiveCoordinates.lean) | The algebraic existence part of Lemma 2.1: two square-free polynomials of degrees `d₁,d₂` over a characteristic-zero field have a monic separable degree-`d₁*d₂` representation, with coordinate polynomials over that same field. A common finite Galois splitting field is supplied; `c ≤ (d₁*d₂)^2`. |
| [`Algebra.GCDRecovery`](LeanCanny/Algebra/GCDRecovery.lean) | At `θ = a+c*b`, the GCD of `p₁(θ-c*x)` and `p₂(x)` is linear. Its coefficients recover `b = -g₀/g₁` and `a = θ+c*g₀/g₁`, with `g₁ ≠ 0`. The hypotheses include separability, splitting, and a separating direction. |
| [`Algebra.PrimitiveResultant`](LeanCanny/Algebra/PrimitiveResultant.lean), [`ResultantFactorization`](LeanCanny/Algebra/ResultantFactorization.lean) | The parameter polynomial is defined by a fixed-degree Sylvester determinant. Specialization, its exact roots, its leading-coefficient factor, and degree `d₁*d₂` are proved. Scalar normalization gives a monic polynomial; the sign from swapping the inputs is tracked explicitly. |
| [`Algebra.ResultantCoordinates`](LeanCanny/Algebra/ResultantCoordinates.lean) | The bounded primitive-coordinate representation uses the specified normalized resultant. A separating direction makes it separable, and coordinate polynomials over the input field recover every pair of roots. |
| [`Algebra.ShiftCoefficients`](LeanCanny/Algebra/ShiftCoefficients.lean) | Direct access to the coefficient of `x^i θ^j` in `p(θ-c*x)`: `choose(i+j,i)*p[i+j]*(-c)^i`. For degree `d` and integer input coefficient bound `H`, its magnitude is at most `2^d*H*(c+1)^d` and its bit length at most `d + H.size + (c+1).size*d + 1`. |
| [`Algebra.CoefficientBounds`](LeanCanny/Algebra/CoefficientBounds.lean) | A polynomial determinant with column coefficient-mass bounds `Bⱼ` has each coefficient bounded by `N! * ∏ Bⱼ`. Power-of-two column budgets give explicit binary length bounds. Column degree bounds also bound the determinant's degree, including empty matrices. |
| [`Algebra.ResultantBounds`](LeanCanny/Algebra/ResultantBounds.lean) | The unnormalized integer resultant has explicit coefficient magnitude and binary length bounds. Its degree is at most `d₁*d₂` over any commutative ring, without separability or nonzero hypotheses. The two input orders have equal coefficient magnitudes. |
| [`Algebra.MatrixPowerEntry`](LeanCanny/Algebra/MatrixPowerEntry.lean), [`MatrixPowerMachine`](LeanCanny/Algebra/MatrixPowerMachine.lean), [`MatrixPowerWork`](LeanCanny/Algebra/MatrixPowerWork.lean) | A continuation machine computes one entry of `A^e` over any semiring by balanced recursion, streaming the summation through a counter and accumulator. Correctness and the exact abstract transition count are proved; no intermediate matrix power is stored. |
| [`Algebra.MatrixPowerBounds`](LeanCanny/Algebra/MatrixPowerBounds.lean), [`MatrixPowerEncoding`](LeanCanny/Algebra/MatrixPowerEncoding.lean) | Every reachable state has at most `e.size` frames. A binary state representation is injective when its scalar representation is. For residues modulo nonzero `m`, complete states have at most `64*(N.size + e.size + m.size + 1)^2` bits for an `N`-dimensional matrix supplied as an entry function. |
| [`Encoding.BinaryNatFP`](LeanCanny/Encoding/BinaryNatFP.lean) | Machine-certified polynomial-time normalization, successor, truncated predecessor, floor half, and ceiling half directly on binary words. The arithmetic specifications cover arbitrary little-endian inputs and produce canonical outputs; no magnitude is expanded to unary. Canonical binary words have an `FP` recognizer. |
| [`Encoding.BinaryAddFP`](LeanCanny/Encoding/BinaryAddFP.lean) | Binary natural-number addition belongs to Complexitylib's machine-level `FP`. A Horner fold doubles the partial sum and adds the two digits by binary increment; every intermediate word is linearly bounded in the input length. Correctness covers arbitrary little-endian words and canonical output has at most `a.length+b.length+1` bits. |
| [`Encoding.BinaryMulFP`](LeanCanny/Encoding/BinaryMulFP.lean) | Binary natural-number multiplication and multiply-accumulate belong to `FP`. Every partial product in the shift-and-add fold is canonical and has at most the sum of the operand bit lengths. Correctness includes zero, empty words, and redundant high zeroes. |
| [`Encoding.BinarySubFP`](LeanCanny/Encoding/BinarySubFP.lean) | Comparison and truncated subtraction on binary natural words have machine-level polynomial-time certificates. Fixed-width complement addition detects the subtraction carry; the low bits recover the difference. All specifications include noncanonical inputs. |
| [`Encoding.BinaryModFP`](LeanCanny/Encoding/BinaryModFP.lean) | Uniform `FP` modular reduction and modular multiply-accumulate, with the modulus supplied in binary. Long division uses one comparison and at most one subtraction per digit. Every partial remainder is canonical and no longer than the processed dividend; modulus zero follows `a % 0 = a`. |
| [`Encoding.BinaryPowModFP`](LeanCanny/Encoding/BinaryPowModFP.lean), [`Algebra.ModularPowFP`](LeanCanny/Algebra/ModularPowFP.lean) | Binary repeated squaring has an FP certificate. Input `pair base (pair exponent b)` specifies positive modulus `fromBitsLE b+1`. Every fold result fits in the modulus word; no unreduced power is stored. Binary products, negative natural bases, and powers agree with `ZMod` residue arithmetic. |
| [`Encoding.BinaryDivFP`](LeanCanny/Encoding/BinaryDivFP.lean) | Uniform FP binary quotient and paired quotient/remainder, with exact semantics on all words. Reusing the remainder routine determines each quotient digit. Every partial quotient is canonical and no longer than the processed dividend; division by zero gives zero. The final paired output has at most `3*a.length+2` bits. |
| [`Encoding.DyadicQuotientBitFP`](LeanCanny/Encoding/DyadicQuotientBitFP.lean) | An FP routine reads bit `k` of `floor(2^p*a/m)` for `a<m`, with `a,m-1,p,k` supplied in binary. Modular exponentiation modulo `2m`, multiplication, reduction, and division return the canonical zero/one word. It handles modulus one and out-of-range bit indices without constructing the full power or quotient. |
| [`Encoding.BinaryBitFP`](LeanCanny/Encoding/BinaryBitFP.lean), [`Computation.WordBitSpace`](LeanCanny/Computation/WordBitSpace.lean) | FP lookup reads a word at a binary index, capping unary conversion at the word length. It covers arbitrary words and out-of-range indices. Retaining the query while a space-bounded word evaluator runs gives a uniform bit evaluator. |
| [`Algebra.BinarySumCarry`](LeanCanny/Algebra/BinarySumCarry.lean), [`Computation.SumBitController`](LeanCanny/Computation/SumBitController.lean), [`SumBitCorrect`](LeanCanny/Computation/SumBitCorrect.lean), [`SumBitSpace`](LeanCanny/Computation/SumBitSpace.lean) | A selected bit of a sum has a `SpaceFunction` certificate given FP binary summand-count/index writers and certified space-bounded access to individual summand bits. The carry is at most `N`, the partial column accumulator at most `2N`. An exact run invariant covers all columns and the empty family; the suspended implementation accounts for parent and child workspace and clocks. No full summand or sum is stored. |
| [`Algebra.BinaryProduct`](LeanCanny/Algebra/BinaryProduct.lean), [`Computation.ProductBitSpace`](LeanCanny/Computation/ProductBitSpace.lean) | A selected product bit has a `SpaceFunction` certificate from space-bounded bit access to both implicit operands and an FP binary index writer. Bit `k` uses `k+1` shifted terms, each queried through one left selector and one right bit, and the streamed sum machine handles carries. Parent and child workspace and clocks are included. Balanced products of a variable number of factors remain separate. |
| [`Algebra.BalancedProduct`](LeanCanny/Algebra/BalancedProduct.lean), [`BalancedProductMachine`](LeanCanny/Algebra/BalancedProductMachine.lean), [`BalancedProductBounds`](LeanCanny/Algebra/BalancedProductBounds.lean), [`BalancedProductWork`](LeanCanny/Algebra/BalancedProductWork.lean), [`BalancedProductEncoding`](LeanCanny/Algebra/BalancedProductEncoding.lean), [`BalancedProductQueryFP`](LeanCanny/Algebra/BalancedProductQueryFP.lean), [`BalancedProductPadding`](LeanCanny/Algebra/BalancedProductPadding.lean) | A uniform typed continuation controller evaluates one bit of a complete balanced product tree. Its invariants prove the answer, stack depth at most `H`, abstract clock `2^(H*(2*K.size+5)+1)`, and binary state size at most `128*(H+K.size+1)^2`. Initial and child query writers are FP. Padding relates trees to finite products and omitted-factor cofactors. |
| [`Algebra.BalancedProductController`](LeanCanny/Algebra/BalancedProductController.lean), [`BalancedProductControllerCorrect`](LeanCanny/Algebra/BalancedProductControllerCorrect.lean), [`BalancedProductSubroutine`](LeanCanny/Algebra/BalancedProductSubroutine.lean), [`BalancedProductSpace`](LeanCanny/Algebra/BalancedProductSpace.lean), [`FiniteProductSpace`](LeanCanny/Algebra/FiniteProductSpace.lean) | The binary controller is FP and simulates every typed transition. `treeEvaluator`, `evaluator`, and `cofactorEvaluator` provide uniform `SpaceFunction` certificates from FP count/index writers and space-bounded factor-bit access. They account for saved continuations, suspended leaf workspace, and the expanded clock. Counts stay binary; empty products and omitted factors are included. |
| [`Algebra.BinarySubtract`](LeanCanny/Algebra/BinarySubtract.lean), [`Computation.SubtractBitSpace`](LeanCanny/Computation/SubtractBitSpace.lean), [`ArithmeticBitSpace`](LeanCanny/Computation/ArithmeticBitSpace.lean), [`SpaceFunctionSelect`](LeanCanny/Computation/SpaceFunctionSelect.lean) | Ordered subtraction reduces a selected bit to a three-term complemented sum. Certified source-bit routines and an FP index writer give its `SpaceFunction` evaluator. Uniform product/subtraction queries compose as bit oracles. A space-bounded computed predicate can select a child computation while accounting for the predicate, saved response, and selected child. |
| [`Algebra.MatrixPowerQueryFP`](LeanCanny/Algebra/MatrixPowerQueryFP.lean) | Total `FP` writers for the initial query and both child queries agree with the typed machine. Initial height comes from the exponent word's bit length. |
| [`Algebra.MatrixPowerDecoding`](LeanCanny/Algebra/MatrixPowerDecoding.lean) | Exact decoders for queries, frames, stacks, residues, and complete states. Successful state decoding characterizes equality with the canonical encoding. A checked total transition agrees with the typed step and inherits its result and quadratic modular-state bound. |
| [`Algebra.MatrixPowerArithmeticFP`](LeanCanny/Algebra/MatrixPowerArithmeticFP.lean) | The uniform modular multiply-accumulate routine agrees exactly with `ZMod` residue encodings for every nonzero modulus. Encoded zero and one are certified too, including modulus one. The modulus is an input field of one FP routine. |
| [`Algebra.MatrixPowerController`](LeanCanny/Algebra/MatrixPowerController.lean), [`MatrixPowerControllerCorrect`](LeanCanny/Algebra/MatrixPowerControllerCorrect.lean) | A total context-carrying bitstring transition belongs to `FP` when its explicit callbacks do. It simulates every typed transition on encoded states. The modular specialization supplies scalar callbacks and retains the original context for entry access. Packet initialization is certified too. Every modular packet has at most `2*c.length+2+64*(N.size+e.size+m.size+1)^2` bits throughout the run. |
| [`Computation.HaltingIteration`](LeanCanny/Computation/HaltingIteration.lean) | An FP initializer, transition, halting test, and answer yield a PSPACE decision procedure when states have polynomial length and the first halting time is at most exponential in a polynomial. The wrapper supplies the exact completion/answer protocol required by Complexitylib's `SpaceIter`; the clock need not be computed. |
| [`Computation.SpaceDecider`](LeanCanny/Computation/SpaceDecider.lean) | A reusable decision procedure packages its FP primitives, first halting time, polynomial workspace, exponential clock, and language correctness. Suspended iteration and modular determinant evaluation now expose these certificates for further composition. |
| [`Computation.WindowedMachineFP`](LeanCanny/Computation/WindowedMachineFP.lean), [`WindowedMachineCorrect`](LeanCanny/Computation/WindowedMachineCorrect.lean), [`PSPACERepresentation`](LeanCanny/Computation/PSPACERepresentation.lean), [`PSPACEClosure`](LeanCanny/Computation/PSPACEClosure.lean) | Every Complexitylib PSPACE language has a `SpaceDecider` certificate. Cobham configuration encodings give FP operations; space windows bound encoded states and configuration counting bounds the first halt. FP preprocessing composes the resource polynomials, proving PSPACE preimage and many-one reduction closure for arbitrary PSPACE languages. |
| [`Computation.SpaceFunction`](LeanCanny/Computation/SpaceFunction.lean) | A certified output routine packages FP initialization, transition, halting test, and output projection with full state/clock bounds and output correctness. FP output postprocessing preserves the certificate; an FP final predicate gives a PSPACE decider. This is an evaluator interface built on Complexitylib, rather than a new complexity class. |
| [`Computation.SpaceFunctionComposition`](LeanCanny/Computation/SpaceFunctionComposition.lean) | FP input preparation composes the state and clock polynomials with its output-length bound. An explicit paired-state wrapper retains the original input, adds `2*input.length+2` stored bits, and preserves the child's first halting time. |
| [`Computation.SpaceFunctionBranch`](LeanCanny/Computation/SpaceFunctionBranch.lean) | An FP predicate chooses between certified output routines. One retained tag selects the transition, halt, and output operations throughout the run. The branch certificate accounts for that tag and both resource polynomials; immediate FP outputs have zero-transition certificates. |
| [`Computation.BoundedFold`](LeanCanny/Computation/BoundedFold.lean), [`BoundedFoldSpace`](LeanCanny/Computation/BoundedFoldSpace.lean), [`SpaceFunctionChain`](LeanCanny/Computation/SpaceFunctionChain.lean) | A binary bound permits exponentially many certified space-bounded accumulator updates, given a polynomial bound on fold prefixes. The controller retains the context and counter, and accounts for every child run. Certified output lengths are polynomial; a two-update fold therefore proves sequential composition of `SpaceFunction` routines. |
| [`Algebra.MatrixPowerHalting`](LeanCanny/Algebra/MatrixPowerHalting.lean), [`MatrixPowerPSPACE`](LeanCanny/Algebra/MatrixPowerPSPACE.lean) | The controller first finishes at exactly `work N e.size e + 1` steps. A `SpaceFunction` certificate returns the complete selected modular power entry, given canonical FP field writers and uniform FP entry access on every input. Zero testing belongs to Complexitylib's PSPACE. Dimensions and exponents may be exponentially large; only their binary descriptions enter the bound. |
| [`Algebra.CharacteristicAdjugate`](LeanCanny/Algebra/CharacteristicAdjugate.lean), [`BorderedDeterminant`](LeanCanny/Algebra/BorderedDeterminant.lean) | Every coefficient of `adj(XI-A)` is a sum of characteristic coefficients times powers of `A`. Block elimination proves the bordered determinant formula by cancellation of a regular determinant; a monic characteristic polynomial supplies that cancellation over arbitrary commutative rings. |
| [`Algebra.BerkowitzRecurrence`](LeanCanny/Algebra/BerkowitzRecurrence.lean), [`BerkowitzCoefficients`](LeanCanny/Algebra/BerkowitzCoefficients.lean) | The division-free bordered characteristic-coefficient recurrence uses scalar moments `r A^k c`. A recursive reference on `Fin n` matrices agrees with every Mathlib characteristic coefficient, and its signed constant coefficient equals the determinant, including the empty matrix. This reference has linear recursion depth and no space certificate. |
| [`Algebra.BerkowitzTransform`](LeanCanny/Algebra/BerkowitzTransform.lean), [`BerkowitzProduct`](LeanCanny/Algebra/BerkowitzProduct.lean) | Padded coefficient vectors turn each bordered recurrence into a square matrix action. The ordered product's first column gives all characteristic coefficients; its signed top-left entry is the determinant. Factor entries depend on input entries and scalar power moments, without using characteristic coefficients. |
| [`Algebra.MatrixProductEntry`](LeanCanny/Algebra/MatrixProductEntry.lean), [`BerkowitzBalanced`](LeanCanny/Algebra/BerkowitzBalanced.lean) | Balanced interval recursion computes an entry of any ordered matrix product over a semiring, preserving factor order. Applied to the coefficient transformations, height `n.size` suffices to recover every characteristic coefficient and the determinant. A factor accessor avoids constructing the full list. These identities establish correctness and recursion height; later modules supply the encoded evaluator and its space bound. |
| [`Algebra.LayeredMatrix`](LeanCanny/Algebra/LayeredMatrix.lean), [`LayeredMatrixMachine`](LeanCanny/Algebra/LayeredMatrixMachine.lean) | An ordered product interval is one entry of a layered matrix power. Flattening the layer-coordinate pairs gives `Fin` indices. The existing streamed power machine and context-carrying controller evaluate the product under their entry-access contract, with the inherited exact clock and modular state bound. |
| [`Algebra.BerkowitzPower`](LeanCanny/Algebra/BerkowitzPower.lean) | The `n`th power of an `(n+1)^2`-dimensional layered matrix contains every characteristic coefficient. The power machine computes them, and its encoded controller tests determinant zero under the explicit callback contract. Stored residue states have at most `64*(3*n.size+m.size+2)^2` bits; controller packets add `2*c.length+2`. The suspended implementation below accounts for factor-access workspace. |
| [`Algebra.PolynomialCoefficientMatrix`](LeanCanny/Algebra/PolynomialCoefficientMatrix.lean), [`BerkowitzCoefficientPower`](LeanCanny/Algebra/BerkowitzCoefficientPower.lean) | A lower triangular coefficient matrix preserves polynomial addition and multiplication through degree `d`. Flattening these blocks turns polynomial matrix-power coefficients into scalar power entries. Applied to Berkowitz, each degree-`d` determinant coefficient is a signed power entry in dimension `(n+1)^2*(d+1)`. The encoded evaluator below supplies its entry-access and space certificates. |
| [`Algebra.PolynomialPowerAccessFP`](LeanCanny/Algebra/PolynomialPowerAccessFP.lean), [`PolynomialPowerSpace`](LeanCanny/Algebra/PolynomialPowerSpace.lean) | FP binary division, remainder, subtraction, and guards select one coefficient of an original matrix entry or zero. Modular powering returns a selected polynomial matrix-power coefficient with a `SpaceFunction` certificate, given FP control fields and space-bounded input-coefficient access. Its zero-test language is in PSPACE. No polynomial coefficient vector is stored. |
| [`PolynomialProductPower`](LeanCanny/Algebra/PolynomialProductPower.lean), [`PolynomialProductSpace`](LeanCanny/Algebra/PolynomialProductSpace.lean), [`ModularSumSpace`](LeanCanny/Algebra/ModularSumSpace.lean) | A polynomial product is one entry of a shift-matrix power. FP binary factor-count/modulus/degree fields and suspended factor-coefficient access give a complete selected-coefficient evaluator and PSPACE zero test, including empty products. A modular-sum evaluator reduces after each suspended summand call and keeps its accumulator within the modulus word, including modulus one and empty sums. |
| [`Algebra.PolynomialMomentSpace`](LeanCanny/Algebra/PolynomialMomentSpace.lean) | Source/sink augmentation commutes with taking entry coefficients. FP query writers carry a requested degree into space-bounded vector/matrix coefficient routines. The polynomial power evaluator returns the selected coefficient of `r A^k c`, accounting for all child queries and states. |
| [`Algebra.BerkowitzPolynomialMoment`](LeanCanny/Algebra/BerkowitzPolynomialMoment.lean), [`BerkowitzPolynomialFactor`](LeanCanny/Algebra/BerkowitzPolynomialFactor.lean), [`BerkowitzPolynomialFactorSpace`](LeanCanny/Algebra/BerkowitzPolynomialFactorSpace.lean), [`BerkowitzPolynomialSpace`](LeanCanny/Algebra/BerkowitzPolynomialSpace.lean) | A certified routine returns a selected coefficient of a polynomial determinant modulo a positive modulus. FP dimension/modulus/degree fields and space-bounded original entry-coefficient access suffice. Offset queries compute trailing-block moments, four-case selection yields factor coefficients, and polynomial powering plus an FP parity test supplies the determinant coefficient with its sign. Its zero-test language is in PSPACE. |
| [`Computation.SubroutineIteration`](LeanCanny/Computation/SubroutineIteration.lean), [`SubroutineBounds`](LeanCanny/Computation/SubroutineBounds.lean), [`SubroutineFunction`](LeanCanny/Computation/SubroutineFunction.lean), [`SubroutinePSPACE`](LeanCanny/Computation/SubroutinePSPACE.lean) | An FP transition suspends a parent while a child evaluator runs, retaining both encoded states. A variable clock simulates the abstract parent iteration and classifies every intermediate state. Parent and child bounds `S,U` give at most `2*S+U+3` stored bits. Polynomial state bounds and exponential parent/child clocks yield a multi-bit output certificate; FP final predicates give PSPACE decision procedures. |
| [`Algebra.MatrixPowerSubroutine`](LeanCanny/Algebra/MatrixPowerSubroutine.lean) | Exponent-one queries launch a child entry evaluator; its output resumes the saved power stack. Request writing, resumption, and the complete suspended step have FP certificates from the control operations and child primitives. Correct, terminating child calls simulate the original power controller and preserve the final matrix-power result at the expanded clock. |
| [`Algebra.MatrixPowerSpaceEntries`](LeanCanny/Algebra/MatrixPowerSpaceEntries.lean) | Modular matrix powering returns a certified space-bounded output when field writers are FP and matrix entries have a `SpaceFunction` certificate. The complete entry computation need not be FP. The proof accounts for saved parent states, query lengths, child states, and the expanded physical clock; zero testing is in PSPACE under the same contracts. |
| [`Algebra.BerkowitzFactorAccess`](LeanCanny/Algebra/BerkowitzFactorAccess.lean) | Factor `s` is accessed directly through the trailing block `A[s+i,s+j]`, with a proved identity default beyond the last factor. Its entries split into one, a negated diagonal entry, a negated scalar moment, or zero. The moment case is exactly the negative of an augmented matrix-power entry. No preceding factors or coefficient vectors are needed. |
| [`Algebra.MatrixMomentPower`](LeanCanny/Algebra/MatrixMomentPower.lean), [`MatrixMomentFP`](LeanCanny/Algebra/MatrixMomentFP.lean) | Adding a source and sink makes `r A^k c` one entry of the `(k+2)`nd power of an `(n+2)`-dimensional matrix. Uniform FP binary field, row, column, and original-entry access gives certified augmented-entry access, child initialization, and a complete power controller. Result extraction, first halting time, and every packet's size are proved. The child computes one moment without storing its summands. |
| [`Algebra.MatrixMomentSpaceEntries`](LeanCanny/Algebra/MatrixMomentSpaceEntries.lean), [`BerkowitzMomentSpace`](LeanCanny/Algebra/BerkowitzMomentSpace.lean), [`BerkowitzFactorSpace`](LeanCanny/Algebra/BerkowitzFactorSpace.lean) | Scalar moments accept certified space-bounded row, column, and matrix routines. Offset query writers specialize this evaluator to each trailing principal block. FP guards choose one, a negative diagonal entry, a negative moment, or zero, giving the complete factor evaluator with space-bounded original entries. |
| [`Algebra.ModularNegFP`](LeanCanny/Algebra/ModularNegFP.lean) | Uniform FP negation of binary residues agrees with `ZMod`, including modulus one. Reducing, subtracting from the modulus, and reducing again handles arbitrary binary input words. The moment child has a certified negated-output projection for the factor evaluator. |
| [`Algebra.BerkowitzQueryFP`](LeanCanny/Algebra/BerkowitzQueryFP.lean), [`BerkowitzMomentAccessFP`](LeanCanny/Algebra/BerkowitzMomentAccessFP.lean) | FP division/remainder decodes flattened layer and coefficient indices. FP writers supply the trailing dimension, offset, moment exponent, and four-case selector, with exact numeric specifications. Offset query writers access the original input matrix and give certified callbacks for exactly the trailing block and border vectors in the moment formula. |
| [`Algebra.BerkowitzFactorChild`](LeanCanny/Algebra/BerkowitzFactorChild.lean), [`BerkowitzFactorChildCorrect`](LeanCanny/Algebra/BerkowitzFactorChildCorrect.lean), [`BerkowitzFactorChildBounds`](LeanCanny/Algebra/BerkowitzFactorChildBounds.lean) | The complete factor child combines immediate values with the scalar-moment controller. Its initialization, transition, halting test, and output are FP. Correct layered entries, exact first halting time, packet-size bounds, and an exponential clock bound are proved from original-matrix access. |
| [`Algebra.BerkowitzSuspended`](LeanCanny/Algebra/BerkowitzSuspended.lean), [`BerkowitzSuspendedBounds`](LeanCanny/Algebra/BerkowitzSuspendedBounds.lean), [`BerkowitzPSPACE`](LeanCanny/Algebra/BerkowitzPSPACE.lean) | Modular determinant zero testing belongs to Complexitylib's PSPACE under canonical FP dimension, nonzero modulus, and original-entry access on every input. The physical controller runs the factor child, saves the parent, and includes both packets in the polynomial workspace bound. Dimension may be exponential in input length. |
| [`Algebra.BerkowitzSpaceEntries`](LeanCanny/Algebra/BerkowitzSpaceEntries.lean), [`IntegerDeterminantSpaceEntries`](LeanCanny/Algebra/IntegerDeterminantSpaceEntries.lean) | Modular and integer determinant zero testing accept `SpaceFunction` original-entry residue routines. FP dimension/modulus or dimension/bit-budget fields suffice. The nested power, factor, moment, original-entry, and modulus-scan certificates account for every suspended state and child clock. |
| [`Algebra.IntegerModular`](LeanCanny/Algebra/IntegerModular.lean) | An integer with at most `B` magnitude bits is zero exactly when its residues modulo `1,...,2*B+4` all vanish. An LCM growth estimate keeps the scan linear in the bit budget. The criterion applies to determinants; column entry bounds give determinant bit budgets, including empty matrices. |
| [`Algebra.IntegerReconstruction`](LeanCanny/Algebra/IntegerReconstruction.lean), [`ChineseRemainderSum`](LeanCanny/Algebra/ChineseRemainderSum.lean), [`ChineseRemainderSign`](LeanCanny/Algebra/ChineseRemainderSign.lean), [`SmallModulusCRT`](LeanCanny/Algebra/SmallModulusCRT.lean) | A bounded integer's sign is determined by a sum of small CRT fractions. Local inverse-weighted numerators are reduced modulo their own moduli. Downward truncation at denominator `D > 2*card*product` preserves the sign test after zero is excluded. Maximal prime powers up to `N=2*B+6` have product `lcmUpto N`, individual moduli at most `N`, and sufficient dyadic precision exponent `(N+2)*N.size+2`. The certified streamed evaluator below implements these specifications given local preparation. |
| [`Algebra.ChineseRemainderSignBit`](LeanCanny/Algebra/ChineseRemainderSignBit.lean), [`DyadicSumSpace`](LeanCanny/Algebra/DyadicSumSpace.lean), [`ChineseRemainderSignSpace`](LeanCanny/Algebra/ChineseRemainderSignSpace.lean) | One selected bit of the truncated CRT sum determines the integer sign, including zero through vanishing local numerators. A certified local preparation routine, FP count/precision writers, and the magnitude/precision bounds give a complete sign `SpaceFunction` and PSPACE negative-language theorem. Local preparation is implemented below. |
| [`Algebra.IndexedModulusCRT`](LeanCanny/Algebra/IndexedModulusCRT.lean) | Indexing `0,...,N` uses maximal prime powers at prime indices and modulus one elsewhere. The count is exactly `N+1`, the product remains `lcmUpto N`, and the same precision exponent suffices. For positive `N`, each modulus is at most `N`. No compressed prime enumeration or prime-counting routine is required. |
| [`Algebra.PrimalitySpace`](LeanCanny/Algebra/PrimalitySpace.lean), [`PrimePowerSpace`](LeanCanny/Algebra/PrimePowerSpace.lean), [`IndexedModulusSpace`](LeanCanny/Algebra/IndexedModulusSpace.lean) | The indexed CRT modulus has a `SpaceFunction` evaluator on arbitrary binary words `pair N i`. Trial division agrees with `Nat.Prime`, including zero and one. A capped multiplication fold returns exactly `i^(log i N)`, retaining magnitudes at most `N+1`, including zero/one bases and bound zero. Sequential composition and FP selection supply the prime-power-or-one result. |
| [`Algebra.CofactorProductSpace`](LeanCanny/Algebra/CofactorProductSpace.lean), [`CofactorResidueSpace`](LeanCanny/Algebra/CofactorResidueSpace.lean), [`ModularInverseSpace`](LeanCanny/Algebra/ModularInverseSpace.lean), [`CRTWeightSpace`](LeanCanny/Algebra/CRTWeightSpace.lean), [`CRTPreparationSpace`](LeanCanny/Algebra/CRTPreparationSpace.lean) | Certified local CRT preparation computes the selected modulus, streams its complementary product modulo that modulus, searches for the unique inverse, and combines it with a space-bounded integer-residue query. The output agrees exactly with the CRT numerator/modulus specification, including modulus one; every parent and child state is counted. |
| [`Algebra.IntegerSignSpace`](LeanCanny/Algebra/IntegerSignSpace.lean), [`CannyResultantSign`](LeanCanny/Algebra/CannyResultantSign.lean), [`Computation.SpaceDeciderOutput`](LeanCanny/Computation/SpaceDeciderOutput.lean) | A uniform `SpaceFunction` residue routine and FP binary magnitude-bit budget suffice for integer negativity in PSPACE, even with an exponential bit budget. Canny's selected integer resultant coefficient instantiates the theorem using its proved source-derived budget. Its negative and positive languages are in PSPACE, and a certified three-way evaluator returns canonical tags `0` for zero, `1` for negative, and `2` for positive. |
| [`ChineseRemainderDigits`](LeanCanny/Algebra/ChineseRemainderDigits.lean), [`ChineseRemainderRankSpace`](LeanCanny/Algebra/ChineseRemainderRankSpace.lean), [`IntegerRankSpace`](LeanCanny/Algebra/IntegerRankSpace.lean), [`CannyCoefficientRank`](LeanCanny/Algebra/CannyCoefficientRank.lean) | An exact integer truncation-error formula proves rounded CRT reconstruction and identifies the correction rank with the high part of the truncated sum. Any selected rank bit has a certified space-bounded evaluator from residue access and FP budget/index writers, including Canny's actual resultant and coordinate coefficients. The rank's width is bounded by the FP count word length. |
| [`IndexedProductSpace`](LeanCanny/Algebra/IndexedProductSpace.lean), [`IndexedSumSpace`](LeanCanny/Algebra/IndexedSumSpace.lean) | Certified indexed-modulus access supplies bits of the combined product and every cofactor. Local numerator preparation, streamed multiplication, and streamed summation supply bits of the inverse-weighted CRT integer sum. The bound writer is FP; residue access is space bounded. No product, cofactor, or sum is stored in full. |
| [`IntegerSignumSpace`](LeanCanny/Algebra/IntegerSignumSpace.lean), [`InfinitesimalSign`](LeanCanny/Algebra/InfinitesimalSign.lean), [`InfinitesimalSignSpace`](LeanCanny/Algebra/InfinitesimalSignSpace.lean), [`InfinitesimalResidueSpace`](LeanCanny/Algebra/InfinitesimalResidueSpace.lean) | A polynomial's sign on a sufficiently small positive interval equals its lowest nonzero coefficient's sign; zero polynomials and common intervals for finite families are included. A binary bounded scan retains a sign tag of at most two bits. Uniform coefficient residues and FP degree/coefficient-budget writers give its complete `SpaceFunction` certificate. This handles Canny's small-parameter sign rule; general sign determination at algebraic roots remains open. |
| [`RationalSubstitution`](LeanCanny/Algebra/RationalSubstitution.lean), [`RationalSubstitutionMap`](LeanCanny/Algebra/RationalSubstitutionMap.lean) | An explicit univariate numerator equals the substituted multivariate polynomial times `∏ dᵢ^(2*degreeOfᵢ p)`. The denominator is positive wherever all `dᵢ` are nonzero, so signs agree. The numerator degree is at most `∑ᵢ 2*degreeOfᵢ p*max(deg nᵢ,deg dᵢ)`. Coefficient reduction commutes with the construction when denominator exponents retain the original degree allowances, including reductions that kill leading coefficients. |
| [`CoefficientMass`](LeanCanny/Algebra/CoefficientMass.lean), [`RationalSubstitutionBounds`](LeanCanny/Algebra/RationalSubstitutionBounds.lean), [`RationalSubstitutionBudget`](LeanCanny/Algebra/RationalSubstitutionBudget.lean) | Coefficient mass is subadditive and submultiplicative. For `A` variables, source variable degrees at most `D`, coordinate degrees at most `E`, source coefficient magnitudes at most `2^b₀`, and coordinate coefficient magnitudes at most `2^b`, the cleared numerator has degree at most `2*A*D*E` and coefficient magnitude-bit length at most `b₀+A*(D+1).size+2*A*D*(b+(E+1).size)+1`. Both bounds have FP binary writers. Encoded modular evaluation of the substitution remains open. |
| [`ChineseRemainderDigitSpace`](LeanCanny/Algebra/ChineseRemainderDigitSpace.lean), [`IntegerDigitSpace`](LeanCanny/Algebra/IntegerDigitSpace.lean), [`CannyCoefficientDigits`](LeanCanny/Algebra/CannyCoefficientDigits.lean) | `IntegerDigitBits.evaluator` computes arbitrary integer-magnitude bits from uniform space-bounded residue access and an FP binary magnitude budget. Product, inverse-weighted sum, correction rank, sign, subtraction, and selection are all supplied internally with composed workspace/clock certificates. The actual resultant and all-branch coordinate coefficients have specialized evaluators under their existing source contracts. |
| [`Computation.BoundedScan`](LeanCanny/Computation/BoundedScan.lean), [`BoundedScanPSPACE`](LeanCanny/Computation/BoundedScanPSPACE.lean) | An FP binary bound permits exponentially many sequential calls to a certified space decider. The input, counter, and accumulated answer are retained while each child runs. Correctness, first halting time, combined workspace, and expanded physical clock yield a reusable PSPACE certificate for the universal scan. |
| [`Algebra.IntegerDeterminantPSPACE`](LeanCanny/Algebra/IntegerDeterminantPSPACE.lean) | Integer determinant zero testing belongs to PSPACE under FP dimension and binary bit-budget access and uniform FP original-entry residue access. The scan instantiates the modular determinant decider, including its factor children. Integer entries and the determinant bit budget may be exponentially long/large respectively; their complete integer values are never stored. |
| [`Algebra.SylvesterAccessFP`](LeanCanny/Algebra/SylvesterAccessFP.lean), [`SylvesterAccessCorrect`](LeanCanny/Algebra/SylvesterAccessCorrect.lean) | FP binary guards and query writers access the two shifted coefficient blocks of Mathlib's Sylvester matrix. Entry correctness holds for arbitrary scalar encodings with empty-word zero. If coefficients have magnitude at most `2^b`, the resultant has at most `N.size*N+N*b+1` magnitude bits, where `N=m+n`; its budget writer is FP. |
| [`Algebra.ResultantPSPACE`](LeanCanny/Algebra/ResultantPSPACE.lean) | Zero testing for a specified-degree integer resultant belongs to PSPACE under FP binary degree/budget fields and uniform FP coefficient-residue access. The integer determinant decider runs on streamed Sylvester entries with a computed bit budget. A corollary covers the ordinary resultant when the supplied degrees equal the actual polynomial degrees. |
| [`Algebra.Subresultant`](LeanCanny/Algebra/Subresultant.lean), [`SubresultantMinor`](LeanCanny/Algebra/SubresultantMinor.lean), [`SubresultantBounds`](LeanCanny/Algebra/SubresultantBounds.lean) | Interior subresultants (`k<m,n`) are explicit Sylvester minors with Mathlib's column order. Order zero equals its resultant; coefficient-ring maps commute; degree is at most `k`; order one is explicitly linear. Injective binary row/column formulas embed each minor in the full Sylvester matrix. Column budgets bound every integer/parameter coefficient. |
| [`SubresultantAccessFP`](LeanCanny/Algebra/SubresultantAccessFP.lean), [`SubresultantEntrySpace`](LeanCanny/Algebra/SubresultantEntrySpace.lean), [`SubresultantPolynomialSpace`](LeanCanny/Algebra/SubresultantPolynomialSpace.lean) | Binary index transformations are FP. Given FP metadata and uniform space-bounded input coefficient routines, a certified evaluator computes a selected modular coefficient of any interior symbolic subresultant; its zero language is in PSPACE. Invalid orders/indices return zero, including empty-minor cases. |
| [`SubresultantRoot`](LeanCanny/Algebra/SubresultantRoot.lean), [`SubresultantGCD`](LeanCanny/Algebra/SubresultantGCD.lean) | For degree bounds `m,n>1`, the first subresultant is `D*(X-b)` at every common root `b`. Removing the common factor `X-b` identifies `D` with the quotient resultant. A nonzero linear GCD makes the quotients coprime and proves `D≠0` at the actual input degrees. |
| [`SubresultantRecovery`](LeanCanny/Algebra/SubresultantRecovery.lean), [`SubresultantRecoveryBounds`](LeanCanny/Algebra/SubresultantRecoveryBounds.lean) | Symbolic parameter polynomials `N,D` recover both coordinates at separating root pairs: `D(θ)≠0`, `b=-N(θ)/D(θ)`, `a=θ+c*N(θ)/D(θ)`, for nonzero direction and input degrees greater than one. Both polynomials have degree at most `(d₂-1)*d₁`, with explicit integer coefficient bit bounds. |
| [`CoordinateRecovery`](LeanCanny/Algebra/CoordinateRecovery.lean), [`CoordinateRecoveryBounds`](LeanCanny/Algebra/CoordinateRecoveryBounds.lean) | Direct linear-input branches extend the recovery formulas to every input degree and direction under the separating-root-pair hypotheses. A zero direction forces the second input to be linear. Numerator and denominator have degree at most `max 1 ((d₂-1)*d₁)` and explicit integer coefficient bit bounds. The full coordinate computation's space bound remains open. |
| [`Algebra.SylvesterSpaceAccess`](LeanCanny/Algebra/SylvesterSpaceAccess.lean), [`ResultantSpaceEntries`](LeanCanny/Algebra/ResultantSpaceEntries.lean) | Integer resultant zero testing accepts certified space-bounded coefficient-residue routines under FP degree/budget fields. Sylvester access selects a coefficient child or zero, and the strengthened integer determinant decider consumes the resulting entry routine. A corollary covers ordinary resultants at the actual degrees. |
| [`Algebra.SylvesterPolynomialSpace`](LeanCanny/Algebra/SylvesterPolynomialSpace.lean), [`ResultantPolynomialSpace`](LeanCanny/Algebra/ResultantPolynomialSpace.lean) | A selected coefficient of a specified-degree resultant over a polynomial residue ring has a `SpaceFunction` evaluator. The Sylvester accessor carries the coefficient degree into either input routine, and the polynomial determinant evaluator consumes these space-bounded calls. FP input-degree/modulus/output-degree fields suffice. Modular coefficient zero testing belongs to PSPACE. |
| [`Algebra.CannyResultantResidue`](LeanCanny/Algebra/CannyResultantResidue.lean) | The actual integer `cannyResultant` has a certified modular coefficient evaluator. Shifted-coefficient evaluation supplies `p₁(θ-c*x)`; an FP guard supplies `p₂(x)`. FP source-degree/direction/output-degree fields and uniform FP original-coefficient residue access suffice. Reduction commutes with the resultant at the fixed integer source degrees, including modular degree drops. Its modular coefficient zero test is in PSPACE. |
| [`CannySubresultantResidue`](LeanCanny/Algebra/CannySubresultantResidue.lean), [`CannySubresultantInteger`](LeanCanny/Algebra/CannySubresultantInteger.lean), [`CannySubresultantSign`](LeanCanny/Algebra/CannySubresultantSign.lean) | The concrete symbolic numerator and denominator have certified modular coefficient evaluation, integer zero testing, and three-way integer coefficient signs. The reduced-column bound fits the existing FP resultant budget writer. Under FP source metadata, coefficient selection, original-coefficient residue access, and source bit budgets, the zero and both strict-sign languages are in PSPACE. Sign evaluation at algebraic parameter values remains separate. |
| [`CannyCoordinateResidue`](LeanCanny/Algebra/CannyCoordinateResidue.lean), [`CannyCoordinateInteger`](LeanCanny/Algebra/CannyCoordinateInteger.lean), [`CannyCoordinateSign`](LeanCanny/Algebra/CannyCoordinateSign.lean) | FP degree tests include the direct linear branches in certified modular coefficient evaluation for the combined coordinate numerator and denominator. An expanded FP binary bit budget certifies integer zero testing and full three-way coefficient signs across every branch. Under the source metadata, selection, residue, and bit-budget contracts, the integer zero and both strict-sign languages are in PSPACE. Algebraic-parameter signs remain separate. |
| [`Algebra.CannyResultantInteger`](LeanCanny/Algebra/CannyResultantInteger.lean) | Zero testing for a selected integer coefficient of `cannyResultant` belongs to PSPACE. FP source coefficient-bit budgets determine the resultant coefficient budget through binary arithmetic and word lengths. The certified modulus scan tests the concrete Canny residue decider over `1,...,2*B+4`, accounting for all nested evaluator states. |
| [`Algebra.BinomialPower`](LeanCanny/Algebra/BinomialPower.lean), [`BinomialResidue`](LeanCanny/Algebra/BinomialResidue.lean) | The nth power of the lower bidiagonal matrix with diagonal and subdiagonal one contains `choose n k` at row `k`, column zero, in dimension `k+1`. An explicit FP entry accessor and binary field writers instantiate modular powering to return the complete binomial residue with a `SpaceFunction` certificate. It handles all words, modulus one, and `k>n`; its zero-test language is in PSPACE. |
| [`Algebra.ShiftCoefficientFP`](LeanCanny/Algebra/ShiftCoefficientFP.lean), [`ShiftCoefficientResidue`](LeanCanny/Algebra/ShiftCoefficientResidue.lean) | A certified space-bounded evaluator returns the coefficient of `x^i θ^j` in `p(θ-c*x)` modulo a positive binary modulus. It retains the query while the binomial child runs, then performs FP coefficient lookup, negative-direction powering, and modular multiplication. The contract requires FP original-coefficient residue access and a canonical FP direction writer. Result correctness and modular zero testing in PSPACE hold on every binary input. |

The full equation compiler is now certified in polynomial time. It pushes negations
to atoms, concatenates conjunctions, and masks disjunction branches using fresh Boolean
selectors. It introduces sums of squares once at the end, avoiding exponential tree
copying. Both equation-system satisfiability and single-equation satisfiability are
∃ℝ-complete under Complexitylib's polynomial-time many-one reductions.

The certified entry points are `EquationCompiler.compileTerms` and
`EquationCompiler.toSingleEquation`. Their fresh-variable counter begins at the
normalized formula's encoded length, reserving all original indices. Every complete
intermediate state has a cubic bit-length bound. The earlier `500*(n+1)^3` output-size
theorem describes `Formula.singleEquation`, whose counter begins at the formula's arity.

The grammar checker agrees with the original decoder and validates canonical integer
payloads. It accepts well-formed unsatisfiable formulas; real satisfiability remains
the decision problem. Negation normalization copies arithmetic payloads unchanged.

The parameter polynomial in Lemma 2.1 is now the specified normalized Sylvester
resultant, with its roots, degree, and separability proved. Coordinate polynomials over
the original input field still come from Galois descent and interpolation. Linear-GCD
coefficient recovery is also verified. The shifted input family's coefficients have
direct formulas and integer bit-length bounds. The unnormalized integer resultant
has at most `d₁*d₂+1` supported coefficients. Writing `N = d₁+d₂` and
`b = (d₁+1).size + d₁ + H₁.size + (c+1).size*d₁`, each coefficient's magnitude
has binary length at most `N.size*N + d₂*b + d₁*H₂.size + 1` when the input
coefficient magnitudes are bounded by `H₁,H₂`. Integer sign recovery is certified
below from residue access and a binary bit budget. Symbolic subresultant coefficients
have explicit bit bounds and certified modular evaluation. Direct linear branches
also handle degree-one recovery and zero directions. Magnitude bits now have certified
space-bounded evaluators under the same residue/budget contracts. The report's remaining
polylogarithmic-space computations remain open.

The streamed matrix-power primitive now has a verified continuation machine and
binary state-size bounds. Its abstract run takes at most
`2^((N.size+2)*e.size+1)` transitions. Entry access and scalar arithmetic count as
single abstract operations here. Exact decoding and certified initial/child-query
writers and modular scalar arithmetic are now provided. The context-carrying
controller has a complete `FP` transition certificate given certified dimension,
modulus, and matrix-entry callbacks. It simulates the typed run on encoded states;
the initial packet writer is `FP` given certified exponent and index writers.
`MatrixPower.ModularAccess.zeroLanguage_mem_PSPACE` connects this controller to `SpaceIter`:
zero testing of a selected modular power entry is in `PSPACE` under the explicit
FP access contract. The contract specifies a nonzero modulus and valid indices
on every binary input; a concrete input format must supply validation and defaults.
`MatrixPowerSubroutine` now supplies a second interface: a child evaluator runs
through FP steps while the outer state is saved. Its whole entry computation need
not be FP. `SubroutineIteration.mem_PSPACE` accounts for both states and the expanded
clock, under explicit polynomial workspace and exponential time bounds on the
reachable parent run and its child calls. The determinant-factor evaluator now
instantiates those contracts. The division-free bordered recurrence behind
Berkowitz's algorithm is now proved, together with a recursive determinant reference.
Padded coefficient transformations give an ordered matrix product whose first
column contains the characteristic coefficients. `Berkowitz.balancedDeterminant`
recovers the determinant using product-entry recursion of height `n.size`.
The layered construction reduces that ordered product to the existing streamed
power machine, so no separate outer-product controller is needed. Its matrix has
dimension `(n+1)^2`, and stored residue states have at most
`64*(3*n.size+m.size+2)^2` bits. The abstract clock is at most
`2^((2*n.size+3)*n.size+1)`, counting entry access as one operation.
Direct trailing-block access now agrees with the recursive factor specification.
The nontrivial moment `r A^k c` is one power entry after adding a source and sink.
Its uniform child controller has FP initialization, transition, halting test,
result extraction, and modular negation, given certified binary fields and
row/column/matrix access.
For inner dimension `d`, exponent `k`, modulus `m`, and context `c`, every child
packet has at most `2*c.length+2+64*((d+2).size+(k+2).size+m.size+1)^2` bits.
Binary division/remainder, query decoding, and case selection now have FP
certificates. The offset writers supply exactly the trailing block and border
vectors from the original matrix, giving certified moment-child callbacks.
The complete factor child now combines the immediate and moment cases. Its
initializer, transition, halting test, and output projection are FP under the
original matrix access contract. It returns the correct layered entry and halts
for the first time at its stated clock. For original dimension `n`, modulus `m`,
and query packet `p`, its packets through termination have at most
`2*p.length+2+64*(2*(n+2).size+m.size+1)^2` bits, and its clock is at most
`2^(((n+2).size+2)*(n+2).size+1)`.
`Berkowitz.ModularAccess.zeroLanguage_mem_PSPACE` now combines this child with
the outer controller and proves modular determinant zero testing in PSPACE.
Its access contract specifies canonical dimension/modulus fields and original
matrix entries on every input, with a nonzero modulus; concrete formats must
supply validation and defaults. It assumes no FP evaluator for whole factor
entries.

`Berkowitz.IntegerAccess.zeroLanguage_mem_PSPACE` extends the result to integer
determinant zero testing. Its canonical FP budget field bounds the determinant's
magnitude bit length; the entry routine supplies residues modulo every positive
binary modulus. The integer entries need not fit in polynomial space. The
certified scan tests only the moduli `1,...,2*B+4`, where `B` is that bit budget.
An FP budget word gives polynomial-length modulus counters and exponentially many
calls. The combined bound includes the saved scan parent, modular controller,
and factor child. These contracts cover all input strings; concrete formats
still must supply validation/defaults and prove the access and budget properties.
The sign and magnitude-bit evaluators consume these residue/budget contracts.
Canny's remaining algebraic and geometric arguments remain open.

`Resultant.Access.zeroLanguage_mem_PSPACE` instantiates the integer determinant
theorem with streamed Sylvester access. Both degree parameters and a common
coefficient magnitude-bit budget are FP fields; coefficient residues must have
uniform FP access on all modular contexts and indices. The determinant budget
is computed from these fields. The main theorem retains the specified degree
parameters even when specialization lowers a polynomial's degree; the ordinary
resultant follows when those parameters equal the actual degrees. This is zero
testing of integer resultants. The symbolic modular coefficient evaluator below
extends this pipeline. Concrete residue algorithms for the report's remaining
constructed polynomial families still require proofs.

`BinomialResidue.evaluator` now supplies one ingredient of the shifted-coefficient
formula: a certified space-bounded routine returning `choose n k mod m`. Input
`pair n (pair k b)` uses arbitrary little-endian words and specifies positive
modulus `fromBitsLE b + 1`. Its bidiagonal matrix entries have a concrete FP
implementation. No Pascal row or unreduced binomial coefficient is stored.
The output certificate includes polynomial-length states and an exponential
clock, and exposes the FP primitives needed for a suspended call.
`ShiftCoefficientBits.certified` now composes it with the other factors of
`choose(i+j,i) * p[i+j] * (-c)^i`. The original query is retained in an explicit
paired state. Repeated squaring and modular multiplication are FP, as are the
required direction writer and original-coefficient residue routine. Input
`pair q (pair i j)` uses modular context `q = pair originalContext b`, with
positive modulus `fromBitsLE b+1`; the result agrees with the existing
shifted-polynomial identity on all words. Its modular zero-test language is
in PSPACE. `MatrixPower.ModularAccess.evaluatorWithEntry` now accepts a
`SpaceFunction` entry routine and proves the combined matrix-power certificate.
`Resultant.Access.integer_entryEvaluator` supplies a Sylvester entry routine
from certified coefficient children. `Berkowitz.ModularAccess.deciderWithEntry`
now propagates space-bounded original-entry calls through the augmented moment,
factor, and outer power evaluators. The integer modulus scan retains the same
contract. `Resultant.Access.zeroLanguage_mem_PSPACE_of_evaluators` therefore
proves integer resultant zero testing from space-bounded coefficient routines,
with only degree and bit-budget fields required to be FP.
`ResultantPolynomial.ModularAccess.evaluator` now returns selected symbolic
resultant coefficients over a positive modulus from space-bounded bivariate
input coefficient routines. `CannyResultantBits.Access.evaluator` specializes it
to the actual `cannyResultant` using the shifted-coefficient child and FP
original-coefficient residue access. `CannyResultantBits.IntegerAccess.decider`
adds a budget computed from source coefficient-bit bounds and the modulus scan,
giving PSPACE zero testing of the actual integer coefficient.
`IntegerSignBits.evaluator` now constructs local CRT numerators and computes the
required truncated-sum bit from certified residue access and an FP bit budget.
`CannyResultantBits.IntegerAccess.signumEvaluator` combines this negativity test
with the zero decider, returning the full three-way sign of that coefficient.
Its negative and positive languages belong to PSPACE under the same source-access
and bit-budget contracts. `IntegerDigitBits.evaluator` now supplies magnitude bits
under the same contracts, with actual resultant and coordinate specializations.

Binary addition, multiplication, comparison, subtraction, division, and modular reduction
now have uniform `FP` certificates, with exact semantics and bounds on intermediate
states. Their modular multiply-accumulate composition supplies the scalar arithmetic
callback required by the modular power machine.

## Next obligations

1. Relate the chosen encoding to standard ETR presentations and prove an NP lower inclusion.
2. Instantiate the modular power PSPACE theorem with concrete validated input
   formats and uniform entry evaluators;
   instantiate the suspended-entry interface when the whole entry computation
   requires more than polynomial time.
3. Prove the full coordinate computation's space bound, including algebraic parameter values;
   formalize the remaining parallel/streamed algebra used by the report.
4. Formalize critical points, perturbations, sign tests, and the correctness of Canny's
   ETR decision procedure; prove `ETR ∈ PSPACE`.
5. Apply the proved PSPACE reduction closure once ETR membership is established;
   the conditional equivalence `∃ℝ ⊆ PSPACE ↔ ETR ∈ PSPACE` is already proved.
6. Extend to roadmap connectivity and the geometric consequences in the report.

See [`RESEARCH.md`](RESEARCH.md) for prior work, the machine-model comparison, and
where Savitch's theorem enters.

## Report integrity

Source: [Berkeley PDF](https://www2.eecs.berkeley.edu/Pubs/TechRpts/1988/Archive/CSD-88-439.pdf).
The downloaded file has 936,246 bytes and SHA-256
`7606d41dea23ac1160562a759c196267906d8aec0f754cd4998fdd14fcd185f8`.
The report retains its original rights; the source-code license does not apply to it.
