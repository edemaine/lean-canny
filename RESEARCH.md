# Prior work and choice of complexity infrastructure

Investigation date: 2026-10-19. Negative findings below describe the repositories and
searches checked; they are not claims that no such formalization exists anywhere.

## Existing real-algebraic formalizations

* [TauCeti](https://github.com/TauCetiProject/TauCeti) includes real-algebraic
  quantifier elimination, CAD existence, Tarski–Seidenberg, and Sturm–Tarski/sign
  determination. See
  [quantifier elimination](https://github.com/TauCetiProject/TauCeti/blob/main/TauCeti/Geometry/RealAlgebraic/Semialgebraic/QuantifierElimination.lean)
  and [recursive sign determination](https://github.com/TauCetiProject/TauCeti/blob/main/TauCeti/Geometry/RealAlgebraic/SignDetermination/Recursive.lean).
  The inspected sign-determination construction uses noncomputable choices. Its
  correctness results do not supply Canny's workspace bound.
* [Hex](https://github.com/leanprover/hex) develops exact real-algebraic computation,
  including root isolation, algebraic numbers, resultants, and real-closed-field
  tactics. Such arithmetic can be useful without establishing a PSPACE bound for ETR.
* Isabelle AFP has [Ben-Or–Kozen–Reif](https://www.isa-afp.org/entries/BenOr_Kozen_Reif.html)
  and [hybrid real quantifier elimination](https://www.isa-afp.org/entries/Quantifier_Elimination_Hybrid.html).
  These are relevant algorithmic correctness precedents in a different prover.
* Coq has Cohen and Mahboubi's real-closed-field quantifier elimination and
  [MathComp CAD](https://github.com/math-comp/cad). These are additional prior work,
  rather than Lean complexity-class interfaces.

No existing encoded ∃ℝ complexity-class definition or formal proof of `ETR ∈ PSPACE`
was found in the inspected Mathlib, Complexitylib, CSLib, TauCeti, or adjacent projects.
The ∃ℝ definition in this project uses the standard reduction-class formulation;
equivalence with other finite presentations requires explicit efficient translations.

Mathlib already proves the ordinary
[primitive element theorem](https://github.com/leanprover-community/mathlib4/blob/728a93eeff833da3173895bb0575752fdc24edb0/Mathlib/FieldTheory/PrimitiveElement.lean),
including a linear-GCD argument for two separable elements. Its Galois fixed-field and
Lagrange interpolation theorems also supply the algebraic tools used here. The current
project strengthens the representation interface to all pairs of roots of two input
polynomials, with one bounded integer selector, a monic separable degree-`d₁*d₂`
polynomial, and coordinate polynomials over the input field. The GCD coefficient-ratio
recovery specification is proved. The parameter polynomial now uses Mathlib's
[Sylvester resultant](https://github.com/leanprover-community/mathlib4/blob/728a93eeff833da3173895bb0575752fdc24edb0/Mathlib/RingTheory/Polynomial/Resultant/Basic.lean),
with verified specialization, roots, scalar normalization, and degree. Taylor and Hasse
derivatives supply a direct shifted-coefficient formula and integer bit-length bounds.
The project now bounds coefficients of polynomial determinants by column coefficient
masses, and specializes this estimate to the integer resultant. Its degree is at most
`d₁*d₂` without nonzero or separability hypotheses, and its coefficient bit lengths
are bounded explicitly in the input degrees, coefficient lengths, and direction length.
Interior subresultants now have explicit determinant definitions, coefficient bit bounds,
and certified modular evaluation. The nonzero linear-GCD bridge now proves symbolic
coordinate recovery for input degrees greater than one and nonzero directions.
Direct linear branches extend recovery to every degree and direction under the
separating-pair hypotheses. Integer magnitude-bit recovery is certified from
residue access and an FP budget; the report's remaining space bounds are open.
Integer negativity is certified
from residue access and a binary bit budget, with a full three-way sign evaluator
for Canny's concrete resultant coefficient.
The modules below give certified modular determinant/resultant coefficient
evaluation and integer zero testing, including Canny's concrete resultant family.

The project also proves the division-free bordered characteristic-polynomial
recurrence behind Berkowitz's algorithm. Coefficients of `adj(XI-A)` are expressed
through powers of `A`; cancellation of the monic characteristic polynomial proves
the bordered identity even over rings with zero divisors. A recursive reference
on `Fin n` matrices returns exactly Mathlib's characteristic coefficients and
determinant, including dimension zero. Its linear recursion depth does not supply
the report's polylogarithmic workspace. The coefficient recurrence now acts by
square transformations on padded vectors; their ordered product contains the
characteristic coefficients in its first column. A generic balanced interval
recursion preserves factor order, and `Berkowitz.balancedDeterminant` uses height
`n.size` to recover the determinant. The factor accessor avoids building the full
list. The layered matrix
construction now converts this ordered product to a single power, with dimension
`(n+1)^2` and exponent `n`. It therefore reuses the existing continuation machine
and bitstring controller under their explicit entry-access contract. Stored residue
states have at most `64*(3*n.size+m.size+2)^2` bits; retaining context `c` adds
`2*c.length+2`. The abstract clock is at most `2^((2*n.size+3)*n.size+1)`, counting
entry access as one operation. A generic suspension wrapper and PSPACE composition
theorem now account for a saved parent alongside a running child. The power
controller intercepts exponent-one entry queries, runs the child through FP steps,
and resumes the original stack with its output. Correct and terminating calls
simulate the full abstract power run. Direct factor access is now proved through
the trailing principal block, with no lookup of preceding factors. The factor
cases are one, a negative diagonal entry, a negative scalar moment, or zero.
Adding a source and sink reduces `r A^k c` to a power entry in dimension `n+2`.
Given FP binary fields, row, column, and original-entry access, a uniform controller
computes this moment. Its first halting time, result, and packet bounds are proved;
FP modular negation supplies the negative output, including modulus one.
Uniform FP binary quotient/remainder now decodes the flattened query indices.
Its quotient fold keeps every partial word bounded by the processed dividend's
length, including noncanonical inputs and division by zero. FP field writers
supply the trailing dimension, offset, moment exponent, and four-case selector.
Offset query writers give exactly the original matrix entries for the trailing
block and border vectors, with a certified moment-child callback contract.
The complete factor child now combines the immediate and moment cases, with
correct results, exact first halting time, and concrete workspace/clock bounds.
`Berkowitz.ModularAccess.zeroLanguage_mem_PSPACE` instantiates the suspended
controller and proves modular determinant zero testing in Complexitylib's PSPACE.
It assumes FP canonical dimension/modulus fields and FP original-matrix entries
on every input, with a nonzero modulus. Dimension can be exponential in the input
length. The proof includes the retained parent and child packets and the expanded
physical clock; it assumes no FP computation of whole factor entries.
Integer determinant zero testing now also belongs to PSPACE under FP dimension
and binary determinant-bit-budget access and uniform FP original-entry residue
access. Mathlib's LCM growth bound implies that an integer of at most `B`
magnitude bits is zero exactly when its residues modulo `1,...,2*B+4` vanish.
The project proves this criterion and the determinant specialization. A generic
bounded universal scan retains a binary counter and one answer bit while each
space-certified child runs. Modular determinant evaluation now exposes a reusable
`SpaceDecider` with its FP primitives and full resource/correctness certificates.
The scan composes that decider, accounting for the scan parent, modular controller,
and factor child. Dimension, entry bit lengths, and the determinant bit budget can
be exponential in the input length; complete integer entries are not stored.
The access contract covers all contexts and positive binary moduli. Concrete
formats still must validate/default inputs and supply the uniform residue routine
and bit budget. The generic sign and magnitude-bit evaluators consume these
contracts; the report's ETR upper bound remains open.

The integer determinant theorem now also has a resultant instantiation. Binary
guards and offset writers implement exactly Mathlib's two Sylvester column
blocks through coefficient queries. They preserve the specified degree parameters,
including after a specialization lowers an actual degree. A common coefficient
bound `2^b` gives the computed resultant bit budget `N.size*N+N*b+1`, with `N=m+n`.
`Resultant.Access.zeroLanguage_mem_PSPACE` proves resultant zero testing under
FP degree and coefficient-budget fields and uniform FP coefficient-residue access
on all contexts and indices. A corollary uses the ordinary resultant when the
degree fields equal the actual polynomial degrees. Later modules provide symbolic
modular coefficient evaluation and generic integer sign recovery. Residue algorithms
for all polynomial constructions used in the report remain open.

The project now supplies an explicit binomial-residue routine for the shifted
coefficient formula. The lower bidiagonal matrix with diagonal and subdiagonal
one has `choose n k` at row `k`, column zero of its nth power in dimension `k+1`.
This identity holds over any semiring. Concrete FP binary writers and entry
access instantiate the modular power controller, including arbitrary positive
composite moduli and modulus one. `BinomialResidue.evaluator` returns the complete
residue through a `SpaceFunction` certificate with first halting time, polynomial
state bounds, and an exponential clock. All binary input words are covered;
`k>n` returns zero. Modular power evaluation now exposes the same output interface,
and FP final predicates derive PSPACE decision procedures from it.
The shifted-coefficient residue evaluator now combines the binomial child with
the original coefficient and the power of the negative direction. Binary modular
exponentiation has an FP certificate by repeated squaring, with every fold result
bounded by the modulus word. FP input preparation and an explicit input-retention
wrapper preserve the complete resource certificates. `ShiftCoefficientBits.certified`
returns exactly the coefficient of `x^i θ^j` in `p(θ-c*x)` modulo the supplied
positive modulus, assuming FP original-coefficient residue access and a canonical
FP direction writer. Its modular zero-test language is in PSPACE. All binary
queries, zero coefficients/direction, and modulus one are covered.
Modular powering now also accepts a `SpaceFunction` entry routine under FP field
writers. `MatrixPower.ModularAccess.evaluatorWithEntry` supplies the saved-parent,
query-length, child-workspace, and expanded-clock proofs for the complete output;
zero testing is in PSPACE under the same contracts. An FP-controlled branch
certificate lets Sylvester access select either coefficient routine or zero.
`Resultant.Access.integer_entryEvaluator` exposes a certified routine for the
exact integer-entry function used by the existing resultant encoding. This now
feeds the complete determinant pipeline: augmented scalar moments accept
space-bounded vector/matrix routines, offset queries specialize them to trailing
blocks, and the factor evaluator selects an immediate value or the moment child.
`Berkowitz.ModularAccess.deciderWithEntry` consumes the resulting factor routine
in the outer power; `Berkowitz.IntegerAccess.deciderWithEntry` adds the modulus
scan. `Resultant.Access.zeroLanguage_mem_PSPACE_of_evaluators` consequently
proves integer resultant zero testing under FP degree/budget fields and
`SpaceFunction` coefficient-residue certificates. The ordinary-resultant
corollary requires the supplied degrees to equal the actual degrees. Symbolic
coefficient evaluation for Canny's resultant is supplied by the specialization below,
as are its integer signs and magnitude bits.

The symbolic coefficient reduction now has a scalar matrix representation.
`PolynomialCoefficientMatrix.scalarHom` maps a polynomial to its lower
triangular coefficient matrix of width `d+1`, preserving addition and
multiplication. Entrywise application and block flattening preserve powers.
`Berkowitz.det_coeff_eq_coefficientPower` consequently expresses degree `d`
of a determinant over `R[X]` as a signed power entry over `R`, in dimension
`(n+1)^2*(d+1)`. `PolynomialPower.ModularAccess.evaluator` now implements the
generic polynomial matrix-power coefficient operation. FP binary controls
and a `SpaceFunction` routine for original entry coefficients suffice. The
flattened accessor decodes each coordinate by division/remainder and returns
one input coefficient or zero, with its own space certificate. This covers
all binary contexts and gives modular coefficient zero testing in PSPACE.
`PolynomialMoment.ModularAccess.evaluator` specializes it to coefficients of
`r A^k c`: taking an entry coefficient commutes with source/sink augmentation,
so FP guards and degree-carrying query writers select a vector or matrix
coefficient routine. These routines may each use polynomial space.
The determinant instantiation now supplies the layered factor coefficients.
`BerkowitzPolynomial.ModularAccess.momentEvaluator` carries coefficient degrees
through offset queries to the original trailing block and its border vectors.
The four factor cases have a certified evaluator and agree with coefficients
of the layered matrix on all valid indices. Polynomial powering and an FP
parity test then give `BerkowitzPolynomial.ModularAccess.evaluator`, returning
the selected determinant coefficient with the Berkowitz sign. Its contract
requires FP dimension/modulus/degree fields and a `SpaceFunction` routine for
original entry coefficients; modular coefficient zero testing is in PSPACE.
`ResultantPolynomial.ModularAccess.evaluator` now instantiates this determinant
routine for symbolic resultants. Its Sylvester accessor carries the requested
degree into each input coefficient routine, reusing the existing scalar guards
and indexing proof. FP input-degree/modulus/output-degree fields and certified
space-bounded bivariate coefficient routines suffice; modular resultant
coefficient zero testing is in PSPACE.

`CannyResultantBits.Access.evaluator` now supplies the concrete Canny
instantiation. The shifted-coefficient child accesses `p₁(θ-c*x)` and an FP
degree-zero guard accesses `p₂(x)`. The result is proved equal to a coefficient
of the existing integer `cannyResultant`, reduced modulo any positive modulus.
The fixed integer source degrees are preserved through modular reduction.
The contract requires FP source degrees, direction, and selected output degree,
plus uniform FP residue access to both original integer coefficient functions.
Its modular coefficient zero test is in PSPACE.

`CannyResultantBits.IntegerAccess.decider` extends this to zero testing of the
integer coefficient. For source degrees `m,n`, direction `c`, and coefficient
bounds `2^b₁,2^b₂`, its computed budget is
`B = (m+n).size*(m+n) + n*S + m*(b₂+1) + 1`, where
`S = (m+1).size + m + (b₁+1) + (c+1).size*m`.
The previous coefficient-size theorem proves this budget; binary arithmetic
and encoded word lengths give FP budget writers. The bounded modulus scan
then composes the concrete residue decider and tests moduli `1,...,2*B+4`, with
all child states included. FP source-bit-budget fields and the residue-access
contracts suffice, even when `B` is exponential. The sign evaluator below uses
the same budget and residue-access contracts; the magnitude-bit evaluator below
also consumes these contracts.

The reconstruction specification now has a proved CRT route. A coprime modulus
system uses locally reduced inverse-weighted numerators `aᵢ`; the fractional part
of `Σ aᵢ/mᵢ` equals the combined residue divided by the product `M`. For a nonzero
integer with `2*|z| < M`, comparison with `1/2` determines its sign. Replacing
each fraction by `floor(D*aᵢ/mᵢ)/D` has total downward error at most `card/D`;
`D > 2*card*M` preserves the comparison. The maximal prime powers up to
`N=2*B+6` instantiate this specification for a magnitude-bit budget `B`, with
every individual modulus at most `N` and sufficient precision
`D=2^((N+2)*N.size+2)`. The proof uses large products and sums only as mathematical
specifications. The local preparation and streamed arithmetic below now certify
integer sign recovery from residue access and a binary bit budget.

Individual bits of the dyadic quotients now have a uniform FP accessor.
`DyadicQuotientBits.value` takes binary `a,m-1,p,k`, assuming `a<m`, and returns
bit `k` of `floor(2^p*a/m)`. For `k≤p`, the bit is
`((2^(p-k)*a) mod (2*m))/m`; modular exponentiation keeps each word short.
Indices above `p` return zero. The proof covers arbitrary input words and
modulus one, and the implementation's FP theorem holds on every raw string.
`SumBits.evaluator` now certifies accumulation of these bit streams. The carry
is at most the summand count `N`, and every partial column accumulator is at
most `2N`. A single binary counter locates the column and summand, with one
division-by-two step between columns. The exact abstract run returns bit `K`
after `K*(N+1)+N` steps, including `N=0`. The physical suspended evaluator
accounts for child runs and returns a `SpaceFunction` certificate from FP
count/index writers and certified space-bounded summand-bit access.

The sign-specific instantiation is now proved. `DyadicSumBits.evaluator` retains
each query while a certified routine prepares its local numerator/modulus pair,
then reads the dyadic quotient bit with FP postprocessing. The strict magnitude
bound rules out equality at the half threshold, so only one selected sum bit is
needed. If the integer is zero, every local numerator and the whole truncated
sum vanish. `ChineseRemainder.signEvaluator` and `negativeLanguage_mem_PSPACE`
therefore include zero without a separate oracle, under the explicit local
preparation, FP count/precision, and magnitude/precision contracts. The preparation
routine is now constructed from residue access below.

`indexedSystem N` uses all indices `0,...,N`, assigning modulus one to nonprime
indices. Its count is exactly `N+1`, while its product is still `lcmUpto N` and
the previous precision bound still suffices. This avoids requiring an FP prime
count or a compressed prime enumeration in the eventual implementation.

Indexed moduli now have an actual certified evaluator. `PrimalityBits.evaluator`
scans trial divisors with FP modular reduction and retains one Boolean flag;
its answer agrees with `Nat.Prime`, including zero and one. A separate bounded
multiplication routine returns `i^(log i N)`, with each stored magnitude at most
`N+1`, for all binary `N,i`. `ModulusBits.evaluator` composes the routines and
uses FP selection to return the prime power or one. `BoundedFold.evaluator`
accounts for sequential space-bounded updates, and `SpaceFunction.chain` proves
sequential composition using polynomial output bounds.

`CofactorBits.evaluator` streams the complementary product, skips the selected
index, and reduces after each multiplication. Its output agrees with the actual
CRT cofactor modulo the selected modulus. `ModularInverseBits.evaluator` scans
candidates below a positive modulus; coprimality proves that the result equals
`ZMod`'s inverse value, including modulus one. `WeightBits.evaluator` composes
these routines, and `PreparationBits.evaluator` calls the original integer-residue
routine and performs FP modular multiplication to return exactly the local CRT
numerator and modulus-minus-one code.

`IntegerSignBits.evaluator` closes the sign-recovery pipeline. FP writers compute
`N=2*B+6`, count `N+1`, and precision exponent `(N+2)*N.size+2` from the binary
magnitude-bit budget. Indexed-system product, magnitude, and precision theorems
discharge the sign wrapper's remaining hypotheses. A uniform space-bounded
integer-residue routine and FP bit-budget writer therefore give a certified
integer negativity evaluator and PSPACE negative-language theorem. Neither the
integer nor the large CRT modulus or truncated sums are stored.

`CannyResultantBits.IntegerAccess.signumEvaluator` specializes this construction
to the actual integer coefficient and combines it with the existing zero decider.
Its tags are `0` for zero, `1` for negative, and `2` for positive. Both the negative
and positive languages are in PSPACE under the existing FP source degree,
direction, selected-degree, coefficient-residue, and source-bit-budget contracts.
The full coordinate computation's space bound and the
critical-point/ETR argument remain open.

The subresultant determinant specification is now explicit. For interior order
`k<m,n`, coefficient `r≤k` is the minor with `m-k` shifted `g` columns and `n-k`
shifted `f` columns, selecting coefficient row `r` followed by rows `k+1,k+2,...`.
This follows the ascending-coefficient determinantal construction in
[Definition 1 of the Inria report](https://who.rocq.inria.fr/Alban.Quadrat/PubsTemporaire/RR-9044.pdf),
with Mathlib's block order; its zeroth member is proved equal to Mathlib's
resultant. Mapping coefficients commutes with the construction, its degree is
at most `k`, and the first member is an explicit linear polynomial. Injective
index formulas identify these matrices with submatrices of the full Sylvester
matrix. Integer and parameter-coefficient budgets follow with the reduced
column counts.

`SubresultantPolynomial.ModularAccess.evaluator` now computes a selected modular
parameter coefficient of any selected subresultant coefficient. Binary row/column
selection and validity checks are FP; space-bounded source coefficient routines
supply the entries to the existing polynomial determinant evaluator. The outer
validity branch returns zero even when the invalid minor is empty, whose determinant
would otherwise be one. The corresponding zero language is in PSPACE.

`Subresultant.first_eq_mul_X_sub_C` proves that for degree bounds `m,n>1`, the first
subresultant equals `D*(X-b)` at any common root `b`: the root equations express
the constant row as a linear combination of the positive-degree rows. Hence the
determinant ratio recovers `b` whenever `D≠0`.

`Subresultant.minor_first_one_det_linear_factor` identifies `D` with the resultant
of the quotients after removing `X-b`: the high-coefficient minor is the quotient
Sylvester matrix multiplied by an upper triangular matrix with diagonal entries
one. A Bezout identity for a nonzero linear GCD makes these quotients coprime,
so their resultant is nonzero. Thus `first_spec_of_linear_gcd` proves that the
first subresultant is linear with a nonzero linear coefficient at the actual
input degrees, when both exceed one.

`subresultant_recovery_spec` specializes symbolic parameter polynomials `N,D` to
`p₁(θ-c*x),p₂(x)` and applies the existing separating-pair GCD theorem. For input
degrees greater than one and nonzero direction it proves `D(θ)≠0`,
`b=-N(θ)/D(θ)`, and `a=θ+c*N(θ)/D(θ)`. Both parameter degrees are bounded by
`(d₂-1)*d₁`; their integer coefficients satisfy the reduced-column bit budget.
`CannySubresultantBits.Access.evaluator` now specializes the modular evaluator to
these concrete integer numerator/denominator coefficients, reusing the shifted-input
and constant-input routines. Selection zero is explicitly identified with `N`, and
selection one with `D`. Fixed source degrees preserve the specification through
modular degree drops. The reduced-column coefficient budget is bounded by the full
resultant budget, so the existing FP budget and modulus-scan writers also certify
integer zero testing. Streamed integer sign recovery supplies negativity and the
full three-way sign; zero and both strict-sign languages are in PSPACE under the
same FP metadata, selection, source-residue, and source-bit-budget contracts.
`coordinate_recovery_spec` now removes the interior-degree and nonzero-direction
restrictions from the algebraic recovery statement. If `p₂` is linear, its constant
coefficients recover `b`; otherwise a linear `p₁` uses the shifted input's coefficients;
the remaining case uses the first subresultant. For a separating pair with zero
direction, all roots of `p₂` coincide; separability and splitting therefore force
`p₂` to be linear. Both coordinate polynomials have parameter degree at most
`max 1 ((d₂-1)*d₁)` and a uniform integer coefficient bit budget across the branches.
`CannyCoordinateBits.evaluator` includes these direct branches in the certified
modular coefficient evaluator. FP degree comparisons select the constant right
coefficient, shifted left coefficient, or first-subresultant routine. The explicit
selection identities connect its integer specification to the combined coordinate
numerator and denominator. Its modular coefficient zero language is in PSPACE
under the same FP source-metadata, selection, and original-residue contracts.
`CannyCoordinateBits.integerDecider` and `signumEvaluator` now cover the direct linear
branches as well. Their FP budget writer adds the shifted-input and right-input
allowances to the full resultant budget; the uniform coefficient theorem bounds
every branch by this sum. The zero and both strict-sign languages belong to PSPACE
under the existing FP source metadata, selection, residues, and source-bit budgets.
Signs at algebraic parameter values and the complete
coordinate computation's space bound remain open.

`ChineseRemainderDigits` supplies the exact reconstruction arithmetic behind
integer digit access. Writing `I` for the inverse-weighted integer sum, `M` for
the modulus product, and `T` for the truncated quotient sum at scale `D`, it proves
`D*I=M*T+E`, where `E` is the sum of each local division remainder times its
cofactor and `E≤card*M`. Thus `D>card*M` gives
`I=(M*T+D-1)/D`. It also proves the exact correction rank `T/D=I/M`, including
zero residues, and hence the combined residue is `I-(T/D)*M`. Centered reconstruction
recovers a signed integer under `2*natAbs<M`, with an explicit identity for each
magnitude digit.

`ChineseRemainder.rankBitEvaluator` reads rank bit `k` by reading truncated-sum
bit `precision+k`. `IntegerRankBits.evaluator` combines this with the existing
indexed modulus, inverse-weight, and local preparation certificates. Its rank
is bounded by the modulus count and its binary width by the FP count word length.
The indexed precision and magnitude theorems also specialize the exact centered
reconstruction formula to a binary magnitude budget. `CannyCoefficientRank`
instantiates the rank-bit evaluator for the actual resultant and all-branch
coordinate coefficients. Digit reconstruction uses the large product,
inverse-weighted sum, and rank-product subtraction; none is claimed to fit as a
complete binary word in polynomial space.

`ProductBits.evaluator` now supplies the two-operand multiplication primitive.
For selected index `k`, truncating the left factor to its first `k+1` bits preserves
the product modulo `2^(k+1)`. Each shifted summand's bit is the conjunction of
one left-selector bit, an index guard, and a shifted right bit. Sequentially
composed operand routines supply these bits to `SumBits.evaluator`, whose carry,
workspace, and physical-clock proofs give the product certificate. Both operands
may be implicit and exponentially long. The balanced-product and complete CRT
digit evaluators below use this primitive.

`SubtractBits.evaluator` now certifies ordered natural-number subtraction. At
selected bit `k`, the complemented low `k+1` bits of the second operand plus
one turn subtraction into a three-term sum modulo `2^(k+1)`. The complement
routine uses a source bit and a width guard, and the existing sum machine handles
the carry. `ArithmeticBits` supplies uniform `pair context binaryIndex` product
and subtraction interfaces so their outputs can feed further arithmetic.
`SpaceFunction.select` first runs a space-bounded predicate, retains its response,
then runs one selected child, with all workspace and clocks counted.

`ChineseRemainder.magnitudeBitEvaluatorOfOperands` now composes the product,
ordered subtraction, and computed selection certificates into the final CRT
magnitude-digit computation. The centered residue is `I-Q*M`; negativity selects
`M-(I-Q*M)` when needed. `IntegerDigitBits.evaluatorOfProducts` supplies rank and
sign directly from the original uniform residue routine and FP bit budget.
`IntegerDigitBits.evaluator` also supplies both large operand sources internally,
using the indexed product and weighted-sum implementations below. It computes any
selected magnitude bit from residue access and the FP budget alone;
`magnitudeBitLanguage_mem_PSPACE` places the corresponding query language in
Complexitylib's PSPACE.

`BalancedProduct` now defines the complete product tree, with height-`h` node
`i` covering the factor interval starting at `2^h*i`. Its typed continuation
controller computes one product bit by recursively requesting the two child bits
for each term of a streamed column sum. Frames retain the parent query, scan
counter, carry, and at most one returned selector bit. A carry/continuation
invariant proves the answer. The live-query invariant keeps heights decreasing,
node addresses inside the root tree, and bit indices below the root index `K`;
the stack contains at most `H` frames. A strictly decreasing work allowance proves
termination, the first halting time, and abstract clock bound
`2^(H*(2*K.size+5)+1)`. Every reachable binary state has at most
`128*(H+K.size+1)^2` bits; pairing keeps the continuation tail undoubled.
Initial and child query writers are FP, including binary division for scan
coordinates. Padding with ones identifies complete trees with finite products
and omitted-factor cofactors, including empty families. The binary controller is
FP and simulates every typed transition. `BalancedProduct.treeEvaluator` supplies
a complete `SpaceFunction` certificate from FP count/index writers and a
space-bounded factor-bit evaluator. Suspended calls retain the parent stack;
both child workspace and the expanded physical clock are counted.
`BalancedProduct.evaluator` and `cofactorEvaluator` mask padding and omitted
leaves with FP bits of one, requiring factor-bit correctness only at retained
indices. The count stays binary throughout.

`IndexedProductBits.productEvaluator` and `cofactorEvaluator` instantiate this
algorithm with the certified indexed-modulus evaluator. `BinaryNat.bitAt` reads
word bits at binary indices using unary conversion capped at the word length;
`WordBits.evaluator` retains the query while the word routine runs.
`IndexedSumBits.evaluator` combines local reduced-numerator words, cofactor bits,
the two-operand product evaluator, and the streamed sum evaluator to compute bits
of the inverse-weighted CRT integer sum. Exact semantics identify these operands
with the indexed CRT system used by rank and sign recovery. The complete digit
certificate includes every parent and child workspace and expanded clock.
`CannyCoefficientDigits` specializes it to the actual resultant and all-branch
coordinate coefficients under their existing uniform source/residue/budget contracts.
Signs at algebraic parameter values and the remaining critical-point/ETR argument
are still open.

The explicit sign transformations in Lemma 2.4 now have two further components.
`RationalSubstitution.cleared` expands the substitution `xᵢ=nᵢ(θ)/dᵢ(θ)` after
multiplication by `∏ dᵢ(θ)^(2*degreeOfᵢ p)`. Its exact evaluation identity proves
sign preservation wherever the coordinate denominators are nonzero. The even
powers make this denominator positive, including negative coordinate denominators.
The numerator degree is at most
`∑ᵢ 2*degreeOfᵢ p*max(deg nᵢ,deg dᵢ)`. These algebraic statements include zero
and constant polynomials and empty coordinate families.
`RationalSubstitutionMap.clearedWith` retains explicit degree allowances, proving
that coefficient-ring maps commute with the construction even when modular
reduction kills coefficients and lowers actual degrees.

`CoefficientMass` proves subadditivity, submultiplicativity, and finite
sum/product/power bounds for the sum of absolute integer coefficients.
`RationalSubstitutionBounds` bounds the cleared numerator's coefficient mass by
the source coefficient mass times `∏ Mᵢ^(2*degreeOfᵢ p)` when `Mᵢ` bounds both
coordinate masses. For `A` variables and source variable degrees bounded by `D`,
there are at most `(D+1)^A` supported monomials. Source coefficient magnitudes
at most `2^b₀`, coordinate degrees at most `E`, and coordinate coefficient
magnitudes at most `2^b` therefore give the explicit coefficient bit budget
`b₀+A*(D+1).size+2*A*D*(b+(E+1).size)+1`. The uniform degree allowance is
`2*A*D*E`. `RationalSubstitutionBudget` supplies FP binary writers and semantic
budget theorems for these quantities from arbitrary binary metadata words;
neither a whole source coefficient mass nor the expanded polynomial is computed.
The streamed indexed-source evaluator below supplies modular evaluation with
explicit source access contracts.

`PolynomialProduct` now reduces an indexed polynomial product to one entry of
a shift-matrix power. A one-coordinate layer carries each factor, and exact
power semantics identify the first-to-last entry with the full product, including
the empty family. `PolynomialProduct.ModularAccess.evaluator` uses the existing
polynomial coefficient-matrix and suspended matrix-power certificates. Its FP
control fields supply the factor count, positive modulus, and selected degree;
factor-coefficient access can use polynomial space. The selected-coefficient
zero language is in PSPACE. `ModularSum.evaluator` adds canonical summand residues
through suspended calls, reducing after every addition. The accumulator fits in
the modulus word, including modulus one; the empty sum is zero. These primitives
supply the product and outer-sum computations needed by rational substitution.

`IndexedRationalSubstitution` represents the source as `M` indexed monomials in
`A` variables, allowing repeated exponent vectors, zero coefficients, and
cancellation. A fixed width `W` bounds every exponent; clearing produces
`∑ᵣ aᵣ ∏ᵢ nᵢ^eᵣᵢ dᵢ^(W-eᵣᵢ)`. Coefficient-ring maps commute with this expression.
For even `W`, exact evaluation preserves the source expression's sign wherever
the coordinate denominators are nonzero.

`RationalSubstitution.evaluator` (in `RationalSubstitutionSpace`) computes any selected modular coefficient
by streaming coordinate-factor products, source scalar multiplication, and the
outer term sum through suspended routines. Term/variable counts and width stay
binary; exponent access is FP, and source/coordinate coefficient access may use
polynomial space. Invalid term indices are masked before source access.
`RationalSubstitution.IntegerBits.Access.evaluator` supplies uniform residues of
the actual cleared integer polynomial at packets
`pair (pair context selectedDegree) (m-1)`. It normalizes the modulus field for
source calls and preserves the original width under modular degree drops.

`IndexedRationalSubstitutionBounds` proves degree at most `A*W*E` and coefficient
magnitude-bit length at most `M.size+s+A*W*b+1`, where source coefficients have
magnitude at most `2^s` and coordinate coefficient masses at most `2^b`.
Coordinate degree and coefficient bounds give `b=b₁+(E+1).size`.
`IndexedRationalSubstitutionBudget` writes these bounds in FP, using normalized
word length for `M.size`. `RationalSubstitutionSign` combines the actual residue
evaluator and these budgets with integer sign recovery and the infinitesimal
scan. The output is the cleared numerator's sign throughout some sufficiently
small positive interval. For even width it is also the rational substitution's
sign wherever all coordinate denominators are nonzero. The ETR source bridge
below supplies the encoded source instantiation; the BKR algebraic-root sign
routine and the critical-point decision argument are still required.

`ETR.IndexedExpansion` constructs indexed source monomials directly from the
arithmetic expression tree: addition concatenates the two index intervals, and
multiplication uses quotient/remainder to flatten their Cartesian product.
The sum is exactly `Term.toPolynomial`, with no collection of equal monomials.
`IndexedExpansionBounds` proves finite-variable evaluation agrees with the term,
each exponent is at most `Term.degreeBound`, and unused variables have exponent
zero. The count is at most `2^leafCount`. For literal term bit length `N`,
`IndexedExpansionSize` gives count bit length at most `N+1` and indexed coefficient
magnitude at most `2^N`, including negative constants with the original codec.

`ETR.IndexedRationalSubstitution` applies the even-width construction directly
to these syntax-derived monomials. Its evaluation and sign theorems refer to
`Term.eval` of the actual rational coordinate functions. Its degree is at most
`A*(2*degreeBound)*E`, and coefficient magnitude-bit length is at most
`2*N+A*(2*degreeBound)*b+2` when coordinate coefficient masses are at most `2^b`.
The compiled single-equation semantics proves ETR satisfiability equivalent to
the corresponding finite-variable indexed equation.

`MonomialCountData` extends the count algebra to all raw trees, with linear
binary output length even on malformed syntax. `ETR.MonomialCount.read` (in
`MonomialCountFP`) is a uniform FP implementation over the original bracket encoding. Each frame keeps
raw children and their binary counts; its length is at most ten times the raw
frame size. The tree-fold proof bounds every intermediate stack on all binary
inputs. On an encoded term, the reader returns its exact canonical count.
The exponent and coefficient readers below supply individual indexed access for
the full streamed substitution certificate.

`MonomialReaderMachine` visits a selected source monomial without expanding its
siblings: addition chooses one child, and multiplication divides the index by
the right child's count and visits both children. A monoid-valued leaf fold
describes coefficient multiplication and exponent addition. Exact execution takes
at most the original term's encoded size. Pending subtree sizes never increase,
and every child index is at most the initial index.

`MonomialReaderEncoding` supplies FP binary transitions using the actual count
reader and binary arithmetic. `MonomialReaderCorrect` proves exact simulation;
`MonomialReaderBounds` bounds the context, complete task stack, and accumulator
by `2*context.length+4+(4*index.size+20)*termSize+accumulator.length` throughout.
`MonomialReaderFP.reader_mem_FP` combines these results with FP input fields and
a polynomial accumulator bound, accounting for all intermediate states and the
polynomial traversal clock.

`TermView` validates arbitrary term strings in FP, replacing malformed syntax by
the zero expression. `MonomialExponentAtom` compares the selected binary variable
index with each visited unary variable payload and adds zero or one. Its
accumulator is at most the number of steps. Consequently
`MonomialReader.sourceExponent` is a complete uniform FP exponent reader on
`pair context (pair monomialIndex variableIndex)`, with exact canonical output
for the syntax-derived source family. No variable index is expanded to unary.

`IntegerResidueFP` reads the original integer payloads and computes residues in
FP, incrementing the stored magnitude before negation for `-(n+1)`. It handles
modulus one. `MonomialCoefficientAtom` multiplies the accumulator by a constant
residue or by one for a variable. Every partial accumulator fits in the positive
modulus word. `MonomialReader.sourceCoefficient` therefore has a uniform FP
certificate on `pair (pair context monomialIndex) (m-1)`, with exact integer-cast
semantics for every positive modulus. No complete indexed coefficient is stored.

`EncodedRationalSource` supplies a complete source adapter from an FP term field
and FP arity allowance. The default allowance is the validated term's literal
length `N`; the clearing width is `2*N`. Counts, exponent access, coefficient
residues, and source magnitude-bit budgets all have concrete FP implementations.
`RationalSubstitutionBits.Coordinates.evaluator` (in `EncodedRationalSubstitution`) needs only the coordinate
coefficient routines and their residue contracts. Its sign evaluator additionally
uses FP coordinate degree/coefficient bounds and supplies the source budget
internally. The semantic sign theorem refers to `Term.eval` on the actual rational
coordinate values throughout a sufficiently small positive interval, wherever
all coordinate denominators are nonzero.

`CompiledRationalSource` extracts the source term from the existing verified FP
compiler for arbitrary encoded ETR formulas. Every input produces a well-formed
term, whose real zero set is nonempty exactly when the original input belongs to
ETR. In particular, malformed formula inputs keep the compiler's unsatisfiable
default, even though the lower-level term reader uses zero for malformed term
fields. The source side is thus instantiated for general ETR inputs; constructing
the decision procedure's coordinates, determining signs at algebraic parameter
roots, and the critical-point correctness argument remain open.

`InfinitesimalSign` proves that a real polynomial's sign on some interval
`0<β<δ` equals its trailing coefficient's sign, with a common interval for any
finite family. Injective coefficient maps preserve trailing degree and
coefficient, giving the same theorem for integer polynomials evaluated in the
reals. `InfinitesimalSign.evaluator` scans coefficients in increasing degree and
keeps the first nonzero sign; its accumulator has at most two bits, even when
the degree bound is exponential. Every coefficient call is a suspended child.
`IntegerSignumBits.evaluator` computes three-way integer signs from residue access
by testing negativity of the integer and its negation, with FP modular negation
of residue words. `InfinitesimalSign.evaluatorOfResidues` therefore needs only a
uniform coefficient-residue evaluator and FP binary degree/coefficient-budget
writers, with their semantic bounds. Its output agrees with the sign for all
sufficiently small positive parameters. This implements the small-parameter rule
at the end of Lemma 2.4; it does not yet implement the BKR algebraic-root
sign-determination theorem invoked in Lemma 2.3.

`ScaledSignQueries` starts the algebraic-root counting stage. At each sign value
`t∈{-1,0,1}`, the integer quadratics `2-2*t²`, `t²-t`, and `t²+t` are twice the
indicators of zero, negative, and positive respectively. Expanding a product of
these indicators proves that an integer combination of ternary product Tarski
queries equals `2^k` times the number of distinct real roots realizing the
requested sign pattern. For a nonzero root polynomial, strict positivity is
equivalent to an actual realizing real root. Repeated roots are counted once;
zero query values and an empty query family are included. The zero root polynomial
uses Mathlib's empty root multiset and is excluded from the realization theorem.

`SignQueryProductSpace.queryProductEvaluator` computes a selected modular
coefficient of `∏ Qᵢ^eᵢ`, `eᵢ∈{0,1,2}`, through the existing suspended product
machine. Two factor slots per polynomial suffice, with unit padding. Binary
count/exponent/modulus/degree fields are FP, and source coefficient routines may
use polynomial space. Empty products and modulus one are covered. Coefficient
maps commute with the query polynomial at fixed exponents, including modular
degree drops.

`SignQueryBounds` proves query degree at most `2*k*D` and integer coefficient
magnitude-bit length at most `2*k*(b+(D+1).size)+1` for input degree allowance `D`
and coefficient magnitude allowance `2^b`. A Tarski query lies between minus and
plus the root degree. The scaled count has at most `k+rootDegree.size+1` magnitude
bits. `SignQueryBudget` gives FP binary writers and semantic budget theorems from
count and degree words, without unary expansion of their values.

The ternary moment formulation also appears in TauCeti's
[polynomial sign-sum identities](https://github.com/TauCetiProject/TauCeti/blob/main/TauCeti/Geometry/RealAlgebraic/SignDetermination/Polynomial.lean)
and [adapted matrices](https://github.com/TauCetiProject/TauCeti/blob/main/TauCeti/Geometry/RealAlgebraic/SignDetermination/Adapted.lean).
The integer formulation here supplies explicit bit budgets and a certified
streamed coefficient routine for each product query. The full expansion has
`3^k` queries. It establishes the counting identity, without establishing Canny's
polylogarithmic dependence on the number of input polynomials. Evaluating Tarski
queries from input coefficients, implementing suitable query selection and its
workspace bound, and composing the general algebraic-root sign decider remain open.

## TM2 versus Complexitylib's machines

The project now fills one class-level composition gap in Complexitylib's pinned
API. `nonempty_spaceDecider_of_mem_PSPACE` encodes any PSPACE machine using
Cobham's fixed-block representation in a polynomial space window. FP transition,
halting, and verdict operations, exact run simulation, and the existing
configuration-count theorem supply a complete `SpaceDecider` certificate.
`SpaceDecider.precompose` composes its space/clock polynomials with the output
length polynomial of an FP preprocessing function. Consequently PSPACE is
proved closed under FP preimages and polynomial-time many-one reductions.
`existsReal_subset_PSPACE_iff` discharges the class-theoretic consequence:
`∃ℝ ⊆ PSPACE ↔ ETR ∈ PSPACE`. This leaves the ETR algorithm proof open.

The distinction affects implementation and resource-accounting effort, even though
the intended polynomial-space classes agree mathematically.

* `lean-trominoes` uses Mathlib's `FinTM2`: a finite collection of stacks and structured
  statements for push, pop, peek, branching, and control transfer. Its PSPACE package
  requires finite alphabets on **all** stacks and bounds the total occupied stack
  cells on every reachable configuration. Finite labels and finite internal state
  prevent storage hidden in the control. Its input cells count toward space.
* [Complexitylib's base model](https://github.com/SamuelSchlesinger/complexitylib/blob/add0aca8ee0d71e68969f2cb45cf91554a50f787/Complexitylib/Models/TuringMachine.lean)
  is a custom multitape TM, structurally closer to Mathlib's TM0 than to TM2. It uses
  local read/write/head transitions, a fixed four-symbol alphabet, read-only input,
  and named work/output tapes. It is not an instance of Mathlib's TM0. Its decision
  space predicate also bounds output and excursions of the input head.

TM2 gives a more convenient programming language, but not free arithmetic on arbitrary
integers. Such values still need finite encodings and proofs about the space used to
manipulate them. Conversely, using Complexitylib need not mean writing every algorithm
as individual tape transitions:

* [`SpaceIter.mem_PSPACE_of_iterate`](https://github.com/SamuelSchlesinger/complexitylib/blob/add0aca8ee0d71e68969f2cb45cf91554a50f787/Complexitylib/Classes/Space/Iterate.lean)
  supplies a machine from a polynomial-time bitstring step function, polynomially
  bounded states, and a bounded terminating run (at most `2^poly` steps). There are
  also FP composition/iteration tools and polynomial-space folds.
* `lean-trominoes` has evaluator workspace certificates and a prepared-evaluator
  bridge to its TM2 PSPACE predicate. These can avoid rebuilding stack accounting
  for each arithmetic subroutine. The bridge already composes polynomial-time input
  preparation with space-certified evaluation, retaining the original input-length
  parameter. This is a concrete advantage. Its benefit depends on implementing the
  algorithm in that evaluator language.

Complexitylib also defines a higher-level
[rose-tree machine language](https://github.com/SamuelSchlesinger/complexitylib/blob/add0aca8ee0d71e68969f2cb45cf91554a50f787/Complexitylib/Models/RoseTreeMachine/Prog.lean).
Its documentation explicitly states that no simulation theorem connecting its cost
model to the multitape TM has been proved. An RTM cost certificate alone would therefore
leave a bridge obligation before establishing membership in Complexitylib's `FP` or `PSPACE`.

An ordinary tape can be represented by two stacks, and finite alphabets admit
constant-size binary codes. This explains why a space-preserving simulation is
plausible, up to input-size overhead. **No proved bridge between these two library
PSPACE predicates has been established in this project.** Existing Mathlib
computability simulations cannot simply be assumed to preserve the required space.

The useful benchmark is a concrete symbolic-arithmetic routine with encoded inputs,
encoded intermediate states, and a workspace proof through the intended iteration
interface. For Canny, streamed access to large symbolic objects matters more than
the surface machine language alone. The current arithmetic and power-controller
implementation targets Complexitylib's FP/SpaceIter interface. A separate reusable
module would be justified by its interfaces or proved interoperability, not merely
by having fewer files; the TM2 evaluator remains a possible comparison target.

The project now supplies a concrete benchmark for that comparison: a continuation
machine for one entry of a matrix power, with balanced recursion and a streamed
summation. Its result, exact abstract transition count, and logarithmic frame count
are proved. Its binary representation is injective, and states over `ZMod m` have
a quadratic bound in the binary lengths of the dimension, exponent, and modulus.
Exact decoding and a total encoded transition now preserve the typed run and its
state-size bound. Binary normalization, successor, predecessor, and exponent halves
have actual Complexitylib FP certificates, as do the initial and child-query writers.
Binary addition, multiplication, comparison, subtraction, and modular reduction are
certified too, with exact semantics on all words and bounds on intermediate states.
A uniform modular multiply-accumulate callback takes the modulus as a binary input
and agrees with the machine's `ZMod` residue encoding, including modulus one.
The full context-carrying controller now has an FP certificate from explicit FP
callbacks, including matrix-entry access. Its correctness theorem simulates every
typed transition on encoded states; the modular specialization supplies the scalar
callbacks. Packet initialization is FP from certified binary field writers, and
the size bound includes the retained original context. The project now proves
`MatrixPower.ModularAccess.zeroLanguage_mem_PSPACE`: testing whether a selected modular
matrix-power entry is zero belongs to Complexitylib's PSPACE under canonical FP
field/entry access on every context. The proof supplies the exact first halting
time, FP completion and answer tests, and a general halting-loop wrapper for
SpaceIter. Dimension and exponent can be exponential in the context length.
A concrete input format still must validate or default malformed inputs to meet
the access contract, including valid indices and a nonzero modulus.
The direct callback contract still requires FP entry access. The new suspended
entry interface requires FP certificates only for the child initializer,
transition, halting test, and output projection. It saves the parent while the
child runs. A prefix classification accounts for every intermediate physical
state; parent/child bounds `S,U` give `2*S+U+3` bits. Polynomial state bounds and
exponential parent-step and child-run clocks yield Complexitylib PSPACE through
`SubroutineIteration.mem_PSPACE`. Its hypotheses concern only reachable parent
states and requested calls. The direct factor formulas and the uniform scalar-moment
child now form the complete determinant-factor evaluator, including certified
binary case selection and trailing-block query writers. Its result correctness,
exact first halting time, quadratic workspace bound in the dimension/modulus
binary lengths, and exponential clock bound are proved. Its saved query packet
is included in that workspace bound. The suspended outer determinant controller
now meets the combined polynomial-workspace and exponential-time contracts,
giving the modular determinant PSPACE theorem above.

Local comparison sources, at `lean-trominoes` commit
`6fe52dd234bb616fd4fb3c1e7b0a203de1482bc5`:

* `../lean-trominoes/LeanTrominoes/Complexity/Complexity.lean`
* `../lean-trominoes/LeanTrominoes/Computation/Partrec/PartrecPreparedEvaluatorSpace.lean`
* `../lean-trominoes/LeanTrominoes/Computation/Partrec/PartrecGenericSavitchReachSpace.lean`

The current `lean-wang` main branch inspected earlier did not itself define PSPACE;
the relevant Mathlib-only package was found in `lean-trominoes`.

## Savitch's theorem and Canny

Savitch is useful for reachability in an implicitly represented exponential graph,
as occurs in the report's roadmap/motion-planning consequences. Each vertex and the
recursion stack need polynomial-size representations. The adjacency algorithm also
needs a proved workspace bound; treating adjacency as a free Boolean oracle would
leave an essential gap.

The report's §3.1 ETR procedure instead gives a deterministic enumeration and algebraic
sign-testing argument. Savitch is not a substitute for its algebraic space analysis,
and need not be a dependency of that particular proof.

Savitch support is available in **both** candidate libraries:

* [Complexitylib](https://github.com/SamuelSchlesinger/complexitylib/blob/add0aca8ee0d71e68969f2cb45cf91554a50f787/Complexitylib/Classes/Containments/NPSPACESubsetPSPACE.lean)
  proves `NPSPACE ⊆ PSPACE` and equality of the two polynomial-space classes. Its
  public statement explicitly does not provide the general quantitative theorem
  `NSPACE(S) ⊆ DSPACE(S²)`.
* `lean-trominoes` has a generic Savitch evaluator, reachability correctness, encoded
  search-state bounds, and workspace certificates. Its generic leaf interface accepts
  an evaluator-space certificate for adjacency, not only a polynomial-time test.

Neither result automatically transports algorithms or class membership across the
two machine models.
