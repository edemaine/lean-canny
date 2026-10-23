/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.PolyTimePairing
public import Lean

/-! # Generated projections and certificates for raw query packets

`query_layout packet := ((context, index), modulus)` declares the packet writer,
its named field projections, FP certificates for reading and writing, and
projection equations. Certificates are registered with native `polytime`.
`certs "_mem_FP"` selects a legacy certificate suffix; projection equations
are named `field_packetName`.
Generated projections use the existing total pair parsers on every input word.
-/

public section
namespace LeanCanny.Encoding.QueryLayout
open Lean

declare_syntax_cat queryShape
syntax ident : queryShape
syntax "(" queryShape "," queryShape ")" : queryShape
syntax (name := queryLayout) "query_layout " ident (" certs " str)? " := " queryShape : command

private meta partial def fields (shape : TSyntax `queryShape) (value certificate : TSyntax `term) :
    MacroM (Array (Ident × TSyntax `term × TSyntax `term)) := do
  match shape with
  | `(queryShape| $field:ident) => return #[(field, value, certificate)]
  | `(queryShape| ($left, $right)) =>
    return (← fields left (← `(LeanCanny.pairFst $value))
      (← `(LeanCanny.mem_FP_comp $certificate LeanCanny.pairFst_mem_FP))) ++
      (← fields right (← `(LeanCanny.pairSnd $value))
        (← `(LeanCanny.mem_FP_comp $certificate LeanCanny.pairSnd_mem_FP)))
  | _ => Macro.throwErrorAt shape "expected a field or a pair of query layouts"

private meta def binderName (field : Ident) (suffix : String) : MacroM Ident :=
  return mkIdent (← Macro.addMacroScope (field.getId.appendAfter suffix))

private meta partial def writer (shape : TSyntax `queryShape) : MacroM (TSyntax `term) := do
  match shape with
  | `(queryShape| $field:ident) => return ⟨(← binderName field "Word").raw⟩
  | `(queryShape| ($left, $right)) => `(LeanCanny.pair $(← writer left) $(← writer right))
  | _ => Macro.throwErrorAt shape "expected a field or a pair of query layouts"

private meta partial def writerCertificate (shape : TSyntax `queryShape) : MacroM (TSyntax `term) := do
  match shape with
  | `(queryShape| $field:ident) => return ⟨(← binderName field "Cert").raw⟩
  | `(queryShape| ($left, $right)) =>
    `(LeanCanny.mem_FP_pair $(← writerCertificate left) $(← writerCertificate right))
  | _ => Macro.throwErrorAt shape "expected a field or a pair of query layouts"

macro_rules
  | `(query_layout $packet:ident $[certs $suffix:str]? := $shape:queryShape) => do
    let suffix := suffix.map (·.getString) |>.getD "_FP"
    let q := mkIdent (← Macro.addMacroScope `q)
    let fs ← fields shape (← `($q)) (← `(LeanCanny.id_mem_FP))
    let names := fs.map (·.1.getId)
    if names.toList.eraseDups.length != names.size then
      Macro.throwErrorAt shape "query field names must be distinct"
    let args ← fs.mapM (fun f => binderName f.1 "Word")
    let argTerms : Array (TSyntax `term) := args.map (fun a => ⟨a.raw⟩)
    let application ← `($packet $argTerms*)
    let body ← writer shape
    let functions ← fs.mapM (fun f => binderName f.1 "Fn")
    let mut certificates : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
    let mut values : Array (TSyntax `term) := #[]
    for ((field, _, _), fn) in fs.zip functions do
      let h ← binderName field "Cert"
      certificates := certificates.push (← `(bracketedBinder| ($h : $fn ∈ LeanCanny.FP)))
      values := values.push (← `($fn $q))
    let computation ← writerCertificate shape
    let computed ← `($packet $values*)
    let packetFP := mkIdent (packet.getId.appendAfter suffix)
    let mut commands : Array (TSyntax `command) := #[]
    commands := commands.push (← `(command|
      def $packet ($[$args:ident]* : List Bool) : List Bool := $body))
    commands := commands.push (← `(command|
      @[program_certificate]
      theorem $packetFP {$[$functions:ident]* : List Bool → List Bool} $certificates* :
          Turing.MultiTapeTM.ComputableTidilyInPolyTime (fun $q => $computed)
            Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits := $computation))
    for (field, projection, certificate) in fs do
      let fp := mkIdent (field.getId.appendAfter suffix)
      let law := mkIdent (field.getId.appendAfter ("_" ++ packet.getId.toString))
      let word ← binderName field "Word"
      commands := commands.push (← `(command|
        def $field ($q : List Bool) : List Bool := $projection))
      commands := commands.push (← `(command|
        @[program_certificate]
        theorem $fp : Turing.MultiTapeTM.ComputableTidilyInPolyTime $field
          Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits := $certificate))
      let fieldTerm : TSyntax `term := ⟨field.raw⟩
      let packetTerm : TSyntax `term := ⟨packet.raw⟩
      let fieldRule ← `(Lean.Parser.Tactic.simpLemma| $fieldTerm:term)
      let packetRule ← `(Lean.Parser.Tactic.simpLemma| $packetTerm:term)
      commands := commands.push (← `(command|
        @[simp] theorem $law ($[$args:ident]* : List Bool) :
            $field $application = $word := by
          simp only [$fieldRule, $packetRule, LeanCanny.pairFst_pair, LeanCanny.pairSnd_pair]))
    return mkNullNode (commands.map (·.raw))

end LeanCanny.Encoding.QueryLayout
