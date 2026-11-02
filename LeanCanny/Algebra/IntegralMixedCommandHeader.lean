/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullHistoryFamily
public import LeanCanny.Algebra.IntegralMixedRawKindData
public import LeanCanny.Encoding.WordListFP
/-! # A bounded syntactic header for mixed commands

The seven numeric fields contain no algebraic coefficients. Integer commands
record degree zero here; their actual polynomial degree remains a charged
integer-source query. A cut records exactly its written truncation degree.
The trailing raw tag is independent of the producer context; the first six
field positions remain fixed.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCommandHeaderBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralMixedHistory
open IntegralMixedFullHistoryScript
open scoped Classical

structure Header where
  context : ℕ
  coordinate : ℕ
  offset : ℕ
  objective : ℕ
  degree : ℕ
  choice : ℕ
  rawTag : ℕ
  deriving DecidableEq

def encode (h : Header) : List Bool := WordList.encode
  [BinaryNatCode.encode h.context, BinaryNatCode.encode h.coordinate, BinaryNatCode.encode h.offset,
    BinaryNatCode.encode h.objective, BinaryNatCode.encode h.degree, BinaryNatCode.encode h.choice,
    BinaryNatCode.encode h.rawTag]
def decode (w : List Bool) : Header :=
  ⟨Nat.fromBitsLE (WordList.get w 0), Nat.fromBitsLE (WordList.get w 1), Nat.fromBitsLE (WordList.get w 2),
    Nat.fromBitsLE (WordList.get w 3), Nat.fromBitsLE (WordList.get w 4), Nat.fromBitsLE (WordList.get w 5),
    Nat.fromBitsLE (WordList.get w 6)⟩

theorem decode_encode (h : Header) : decode (encode h) = h := by
  cases h
  simp [decode, encode, WordList.get_encode, BinaryNatCode.encode, Nat.fromBitsLE_bits]

def zero : Header := ⟨0, 0, 0, 0, 0, 0, 0⟩
theorem decode_nil : decode [] = zero := rfl

def kindContext {n : ℕ} {P : SpatialSource n} {r : IntegralMixedCriticalSweep.Rule n} :
    IntegralMixedRelativeCuts.Kind P r → ℕ
  | .coordinate .. => 2 | .squarefree .. => 3 | .value .. => 4
def kindRawTag {n : ℕ} {P : SpatialSource n} {r : IntegralMixedCriticalSweep.Rule n} :
    IntegralMixedRelativeCuts.Kind P r → ℕ
  | .coordinate .. => 2 | .squarefree .. => 3 | .value .. => 4
def kindCoordinate {n : ℕ} {P : SpatialSource n} {r : IntegralMixedCriticalSweep.Rule n} :
    IntegralMixedRelativeCuts.Kind P r → ℕ
  | .coordinate j _ => j.val | .squarefree j _ => j.val | .value j _ => j.val
def kindChoice {n : ℕ} {P : SpatialSource n} {r : IntegralMixedCriticalSweep.Rule n} :
    IntegralMixedRelativeCuts.Kind P r → ℕ
  | .coordinate _ c => c.val | .squarefree _ c => c.val | .value _ c => c.val

def selection {n : ℕ} {P : SpatialSource n} (s : IntegralMixedFullHistoryFamilyBits.Selection P) : Header :=
  ⟨kindContext s.kind, kindCoordinate s.kind, s.rule.critical.offset.val, s.rule.critical.objective,
    s.degree, kindChoice s.kind, kindRawTag s.kind⟩
def command {n B : ℕ} {P : SpatialSource n} : Command P B → Header
  | .integer .. => zero
  | .critical r => ⟨1, r.coordinate % (n - r.offset.val + 1), r.offset.val, r.objective, 0, 0, 1⟩
  | .cut r k d _ _ => ⟨kindContext k, kindCoordinate k, r.critical.offset.val, r.critical.objective, d, kindChoice k, kindRawTag k⟩

theorem command_context {n B : ℕ} {P : SpatialSource n} (c : Command P B) : (command c).context = c.context := by
  cases c with
  | integer => rfl
  | critical => rfl
  | cut r k => cases k <;> rfl

theorem command_coordinate {n B : ℕ} {P : SpatialSource n} (c : Command P B) :
    (command c).coordinate = c.coordinate := by
  cases c with
  | integer => rfl
  | critical => rfl
  | cut r k => cases k <;> rfl

theorem command_cut {n B : ℕ} {P : SpatialSource n} (r : IntegralMixedCriticalSweep.Rule n)
    (k : IntegralMixedRelativeCuts.Kind P r) (d : ℕ)
    (ha : d ≤ IntegralMixedExceptionalBounds.auxiliaryCap (n + 1) P.degree) (hd : d ≤ 2 ^ B) :
    command (.cut r k d ha hd) = selection ⟨r, k, d, ha⟩ := rfl

theorem command_default {n B : ℕ} {P : SpatialSource n} : command (defaultCommand (P := P) (B := B)) = zero := rfl

def words {n B : ℕ} {P : SpatialSource n} (cs : List (Command P B)) : List Bool :=
  WordList.encode (cs.reverse.map (fun c => encode (command c)))
def lookup (table : List Bool) (i : ℕ) : Header := decode (WordList.get table i)

theorem lookup_words {n B : ℕ} {P : SpatialSource n} (cs : List (Command P B)) (i : ℕ) :
    lookup (words cs) i = command ((chronological cs i).getD defaultCommand) := by
  unfold lookup words chronological
  rw [WordList.get_encode, List.getElem?_map]
  cases hi : cs.reverse[i]? with
  | none => exact decode_nil.trans command_default.symm
  | some c => exact decode_encode (command c)

theorem encode_length (h : Header) (W : ℕ)
    (hc : h.context.size ≤ W) (hj : h.coordinate.size ≤ W) (ho : h.offset.size ≤ W)
    (hv : h.objective.size ≤ W) (hd : h.degree.size ≤ W) (hi : h.choice.size ≤ W)
    (ht : h.rawTag.size ≤ W) :
    (encode h).length ≤ (2 * W + 2) * 7 := by
  apply WordList.length_le _ W
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simpa only [BinaryNatCode.length_encode] using (by assumption : _ ≤ W)

end LeanCanny.Algebra.IntegralMixedCommandHeaderBits
