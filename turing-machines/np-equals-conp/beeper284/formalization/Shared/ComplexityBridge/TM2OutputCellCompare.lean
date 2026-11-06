import Shared.Codes.FiniteProgramWordCompare
import Shared.ComplexityBridge.TM2BinaryOutputPadding

/-! A concrete finite table distinguishes the fixed-width binary codes of
two Boolean TM2 output cells. The rest of the output extractor remains a
separate controller and tape-writing obligation. -/
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2OutputCellCompare
open Turing
open Shared.ComplexityBridge.TM2BinaryPostCosts
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt consumed)
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramWordCompare

def cell (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool) (marked b : Bool) : Alphabet tm := by
  letI := tm.kDecidableEq
  exact (marked,Function.update (fun _ => none) tm.k₁ (some (out.symm b)))

def emptyMarker (tm : FinTM2) : Alphabet tm := (true,fun _ => none)

def word (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) (marked b : Bool) : List Bool :=
  (enc (cell tm out marked b)).toList

@[simp] theorem word_length (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (out : tm.Γ tm.k₁ ≃ Bool) (marked b : Bool) :
    (word tm enc out marked b).length = width := by simp [word]

theorem cell_injective (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool) (marked : Bool) :
    Function.Injective (cell tm out marked) := by
  intro a b h
  have hh := congrArg (fun x : Alphabet tm => x.2 tm.k₁) h
  have hab : out.symm a = out.symm b := by
    apply Option.some.inj
    simpa [cell] using hh
  exact out.symm.injective hab

theorem cell_ne_blank (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool) (marked b : Bool) :
    cell tm out marked b ≠ default := by
  intro h
  have hh := congrArg (fun x : Alphabet tm => x.2 tm.k₁) h
  simp [cell] at hh

theorem emptyMarker_ne_cell (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool) (marked b : Bool) :
    emptyMarker tm ≠ cell tm out marked b := by
  intro h
  have hh := congrArg (fun x : Alphabet tm => x.2 tm.k₁) h
  simp [emptyMarker,cell] at hh

theorem emptyMarker_ne_blank (tm : FinTM2) : emptyMarker tm ≠ default := by
  intro h
  have hh := congrArg (fun x : Alphabet tm => x.1) h
  change true = false at hh
  contradiction

theorem encoded_injective (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) : Function.Injective (fun a => (enc a).toList) := by
  intro a b h
  have hv := List.Vector.toList_injective h
  have hh := congrArg dec hv
  simpa [hdec] using hh

/-- Each canonical output symbol has a nonblank binary cell, and the empty
marker has a distinct cell. -/
theorem encoded_cell_ne_blank (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (out : tm.Γ tm.k₁ ≃ Bool) (marked b : Bool) :
    word tm enc out marked b ≠ (enc default).toList := by
  intro h
  have he := encoded_injective tm enc dec hdec h
  exact cell_ne_blank tm out marked b he

theorem encoded_empty_ne_cell (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (out : tm.Γ tm.k₁ ≃ Bool) (marked b : Bool) :
    (enc (emptyMarker tm)).toList ≠ word tm enc out marked b := by
  intro h
  have he := encoded_injective tm enc dec hdec h
  exact emptyMarker_ne_cell tm out marked b he

/-- The output stack is serialized in reverse stack order, with one marked
first cell or one empty marker cell. -/
def outputCells (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool) (bits : List Bool) : List (Alphabet tm) :=
  match bits.reverse with
  | [] => [emptyMarker tm]
  | b::bs => cell tm out true b :: bs.map (cell tm out false)

theorem outputCells_eq_trInit (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool) (bits : List Bool) :
    outputCells tm out bits = Turing.TM2to1.trInit tm.k₁ (bits.map out.symm) := by
  letI := tm.kDecidableEq
  cases h : bits.reverse with
  | nil =>
    simp [outputCells,h,Turing.TM2to1.trInit,← List.map_reverse,emptyMarker]
    rfl
  | cons b bs => simp [outputCells,h,Turing.TM2to1.trInit,← List.map_reverse,cell,emptyMarker]

/-- Exact output bits are the concatenated code words of these cells. -/
theorem outputBits_eq_cells (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (out : tm.Γ tm.k₁ ≃ Bool) (bits : List Bool) :
    Shared.ComplexityBridge.TM2BinaryOutputShape.outputBits tm enc (bits.map out.symm) =
      (outputCells tm out bits).flatMap (fun a => (enc a).toList) := by
  rw [outputCells_eq_trInit]
  rfl

/-- A codec with a left inverse cannot merge the two encoded Boolean cells. -/
theorem word_injective (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (out : tm.Γ tm.k₁ ≃ Bool) (marked : Bool) :
    Function.Injective (word tm enc out marked) := by
  intro a b h
  have hv : enc (cell tm out marked a) = enc (cell tm out marked b) :=
    List.Vector.toList_injective h
  have hc := congrArg dec hv
  rw [hdec,hdec] at hc
  exact cell_injective tm out marked hc

/-- Starting at a fixed-width output cell, the generated table compares its
bit with a chosen bit, moves to the next cell, and preserves the tape. -/
theorem compare_output_cell (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (out : tm.Γ tm.k₁ ≃ Bool)
    (marked expected actual : Bool) (L suffix : List Bool) :
    run (program (word tm enc out marked expected))
      (0,tapeAt L (word tm enc out marked actual ++ suffix)) width =
      some (.inr (state width (actual == expected),
        tapeAt (consumed L (word tm enc out marked actual)) suffix)) := by
  have hinj := word_injective tm enc dec hdec out marked
  have hne : word tm enc out marked false ≠ word tm enc out marked true := by
    intro h
    have hh := hinj h
    contradiction
  have heq : (word tm enc out marked actual == word tm enc out marked expected) = (actual == expected) := by
    cases actual <;> cases expected <;> simp [hne,Ne.symm hne]
  have h := compare_word (word tm enc out marked expected) (word tm enc out marked actual) suffix L
    (by simp)
  simpa [word_length,heq] using h

/-- The same comparison works on any blank-equivalent physical tape. -/
theorem compare_output_cell_related (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (out : tm.Γ tm.k₁ ≃ Bool)
    (marked expected actual : Bool) (L suffix : List Bool) (t : Tape)
    (ht : Shared.Codes.FiniteProgramTapeEquiv.TapeRel t
      (tapeAt L (word tm enc out marked actual ++ suffix))) :
    ∃ t', run (program (word tm enc out marked expected)) (0,t) width =
      some (.inr (state width (actual == expected),t')) ∧
      Shared.Codes.FiniteProgramTapeEquiv.TapeRel t'
        (tapeAt (consumed L (word tm enc out marked actual)) suffix) := by
  have hinj := word_injective tm enc dec hdec out marked
  have hne : word tm enc out marked false ≠ word tm enc out marked true := by
    intro h
    have hh := hinj h
    contradiction
  have heq : (word tm enc out marked actual == word tm enc out marked expected) = (actual == expected) := by
    cases actual <;> cases expected <;> simp [hne,Ne.symm hne]
  have h := compare_word_related (word tm enc out marked expected) (word tm enc out marked actual)
    suffix L (by simp) t ht
  simpa [word_length,heq] using h

/-- The generated comparator has exactly two states per word position,
including the two final continuation states. -/
theorem comparator_rows (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (out : tm.Γ tm.k₁ ≃ Bool) (marked b : Bool) :
    (program (word tm enc out marked b)).length = 2*(width+1) := by simp

end Shared.ComplexityBridge.TM2OutputCellCompare
