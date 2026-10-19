import LeanCanny

open LeanCanny.ETR
open Complexity

/-! Executable boundary checks: syntax recognition accepts well-formed unsatisfiable
instances, and rejects redundant high-zero digits and trailing serialized nodes. -/

def sample : Formula :=
  .or (.ltZero (.add (.mul (.var 3) (.var 3)) (.const (-2))))
    (.not (.eqZero (.const 0)))

#guard Grammar.recognizeFormula (Formula.eqZero (.const 1)).encode
#guard Grammar.recognizeFormula sample.encode

def redundantZeroInteger : Data := .l [Codec.unary 0, .l [Codec.bit false]]
def malformedConstant : Data := .l [Codec.unary 0, redundantZeroInteger]
def malformedEquation : Data := .l [Codec.unary 1, malformedConstant]

#guard !Grammar.recognizeFormula malformedEquation.toBits
#guard !Grammar.recognizeFormula (sample.encode ++ [false, true])

def equationTerms : List Term := [.var 0, .add (.var 0) (.const (-1))]

#guard EquationList.recognize (SumSquares.listBits [])
#guard EquationList.recognize (SumSquares.listBits equationTerms)
#guard Grammar.recognizeFormula (EquationList.toSingleEquation (SumSquares.listBits equationTerms))
#guard !EquationList.recognize (Data.l [Data.empty]).toBits
#guard EquationList.toSingleEquation (Data.l [Data.empty]).toBits ==
  (Formula.eqZero (.const 1)).encode

/-! NNF normalization copies arithmetic payloads, removes double negations,
implements De Morgan's law, and rejects incomplete constructors. -/

def payloadSensitive : Formula := .eqZero (.add (.var 3) (.const (-257)))
def demorganInput : Formula := .not (.and payloadSensitive (.not (.ltZero (.const (-2)))))
def demorganOutput : Formula := .or (.not payloadSensitive) (.ltZero (.const (-2)))

#guard NNF.normalize payloadSensitive.encode == payloadSensitive.encode
#guard NNF.transformBits false payloadSensitive.encode == (Formula.not payloadSensitive).encode
#guard NNF.normalize (Formula.not (.not payloadSensitive)).encode == payloadSensitive.encode
#guard NNF.normalize demorganInput.encode == demorganOutput.encode
#guard NNF.normalize (NNF.normalize demorganInput.encode) == NNF.normalize demorganInput.encode
#guard NNF.toETR demorganInput.encode == Formula.falsum.encode
#guard NNF.toETR demorganOutput.encode == demorganOutput.encode

def tagWithoutOperand : Data := .l [Codec.unary 1]
def missingConjunct : Data := .l [Codec.unary 4, Formula.falsum.toData]

#guard NNF.transformBits true tagWithoutOperand.toBits == Formula.falsum.encode
#guard NNF.transformBits false tagWithoutOperand.toBits == (Formula.not .falsum).encode
#guard NNF.transformBits true missingConjunct.toBits == Formula.falsum.encode
#guard NNF.normalize malformedEquation.toBits == Formula.falsum.encode
#guard NNF.normalize (sample.encode ++ [false, true]) == Formula.falsum.encode
#guard NNF.normalize [] == Formula.falsum.encode

/-! The complete compiler uses one counter through nested joins and atom witnesses.
Compare its bytes with the independently defined recursive equation compiler. -/

def compilerSample : Formula :=
  .and (.not (.ltZero (.var 2)))
    (.or (.not .falsum) (.and (.ltZero (.const (-1))) (.not (.eqZero (.var 0)))))

#guard EquationMask.mask (pair (Term.var 7).toData.toBits (SumSquares.listBits equationTerms)) ==
  SumSquares.listBits (equationTerms.map (Term.mul (.var 7)))
#guard EquationMask.mask (pair (Term.var 7).toData.toBits (SumSquares.listBits [])) ==
  SumSquares.listBits []
#guard EquationCompiler.compileTerms compilerSample.encode ==
  SumSquares.listBits
    ((compilerSample.toSigned true).equations (compilerSample.nnf true).encode.length).terms
#guard Grammar.recognizeFormula (EquationCompiler.toSingleEquation compilerSample.encode)
#guard EquationCompiler.compileTerms malformedEquation.toBits == SumSquares.listBits [.const 1]
#guard EquationCompiler.compileTerms (sample.encode ++ [false, true]) == SumSquares.listBits [.const 1]
#guard EquationCompiler.compileTerms [] == SumSquares.listBits [.const 1]

#eval "Grammar, equation-list, NNF, and full compiler boundary checks passed."
