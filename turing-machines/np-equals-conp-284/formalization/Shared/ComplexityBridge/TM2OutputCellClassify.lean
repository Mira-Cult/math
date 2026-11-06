import Shared.Codes.FiniteProgramTwoWordClassify
import Shared.ComplexityBridge.TM2OutputCellCompare

/-! A one-pass finite-table classifier for canonical Boolean output cells and
their end marker. Nonmatching malformed words share the end-marker state; this
is not a general malformed-input validator. Connecting classified cells to a
writer and loop remains open. -/
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2OutputCellClassify
open Turing
open Shared.ComplexityBridge.TM2BinaryPostCosts
open Shared.ComplexityBridge.TM2OutputCellCompare
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt consumed)
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTwoWordClassify

/-- At the first position `none` denotes the marked empty-stack cell; at
later positions it denotes the blank end cell. -/
def symbol (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool) (marked : Bool) : Option Bool → Alphabet tm
  | some b => cell tm out marked b
  | none => if marked then emptyMarker tm else default

theorem symbol_injective (tm : FinTM2) (out : tm.Γ tm.k₁ ≃ Bool) (marked : Bool) :
    Function.Injective (symbol tm out marked) := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b =>
      cases marked with
      | false => exact False.elim (cell_ne_blank tm out false b (by simpa [symbol] using h.symm))
      | true => exact False.elim (emptyMarker_ne_cell tm out true b (by simpa [symbol] using h))
  | some a =>
    cases b with
    | none =>
      cases marked with
      | false => exact False.elim (cell_ne_blank tm out false a (by simpa [symbol] using h))
      | true => exact False.elim (emptyMarker_ne_cell tm out true a (by simpa [symbol] using h.symm))
    | some b =>
      have he : cell tm out marked a = cell tm out marked b := by simpa [symbol] using h
      exact congrArg some (cell_injective tm out marked he)

def code (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) (marked : Bool) (value : Option Bool) : List Bool :=
  (enc (symbol tm out marked value)).toList

@[simp] theorem code_length (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) (marked : Bool) (value : Option Bool) :
    (code tm enc out marked value).length = width := by simp [code]

theorem code_injective (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (out : tm.Γ tm.k₁ ≃ Bool) (marked : Bool) :
    Function.Injective (code tm enc out marked) := by
  intro a b h
  apply symbol_injective tm out marked
  exact encoded_injective tm enc dec hdec h

/-- One finite table classifies a canonical cell, reaching distinct states
for `some false`, `some true`, and `none` after exactly `width` steps. -/
theorem classify_cell (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (out : tm.Γ tm.k₁ ≃ Bool) (marked : Bool)
    (value : Option Bool) (L suffix : List Bool) :
    let zero := code tm enc out marked (some false)
    let one := code tm enc out marked (some true)
    let actual := code tm enc out marked value
    run (program zero one) (0,tapeAt L (actual++suffix)) width =
      some (.inr (state width (mask (value == some false) (value == some true)),
        tapeAt (consumed L actual) suffix)) := by
  let zero := code tm enc out marked (some false)
  let one := code tm enc out marked (some true)
  let actual := code tm enc out marked value
  have hinj := code_injective tm enc dec hdec out marked
  have hc (v : Option Bool) : (actual == code tm enc out marked v) = (value == v) := by
    by_cases he : value = v
    · subst v; simp [actual]
    · have hn : actual ≠ code tm enc out marked v := fun h => he (hinj h)
      simp [he,hn]
  have h := classify_word zero one actual suffix L (by simp [zero,one]) (by simp [actual,zero])
  simpa [zero,one,actual,code_length,hc] using h

/-- The same classification holds for blank-equivalent physical tapes. -/
theorem classify_cell_related (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (out : tm.Γ tm.k₁ ≃ Bool) (marked : Bool)
    (value : Option Bool) (L suffix : List Bool) (t : Tape)
    (ht : Shared.Codes.FiniteProgramTapeEquiv.TapeRel t
      (tapeAt L (code tm enc out marked value ++ suffix))) :
    let zero := code tm enc out marked (some false)
    let one := code tm enc out marked (some true)
    let actual := code tm enc out marked value
    ∃ t', run (program zero one) (0,t) width =
      some (.inr (state width (mask (value == some false) (value == some true)),t')) ∧
      Shared.Codes.FiniteProgramTapeEquiv.TapeRel t' (tapeAt (consumed L actual) suffix) := by
  let zero := code tm enc out marked (some false)
  let one := code tm enc out marked (some true)
  let actual := code tm enc out marked value
  have hinj := code_injective tm enc dec hdec out marked
  have hc (v : Option Bool) : (actual == code tm enc out marked v) = (value == v) := by
    by_cases he : value = v
    · subst v; simp [actual]
    · have hn : actual ≠ code tm enc out marked v := fun h => he (hinj h)
      simp [he,hn]
  have h := classify_word_related zero one actual suffix L (by simp [zero,one]) (by simp [actual,zero]) t ht
  simpa [zero,one,actual,code_length,hc] using h

theorem classifier_rows (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (out : tm.Γ tm.k₁ ≃ Bool) (marked : Bool) :
    (program (code tm enc out marked (some false)) (code tm enc out marked (some true))).length =
      4*(width+1) := by simp

theorem classification_states_distinct (width : Nat) :
    state width (mask true false) ≠ state width (mask false true) ∧
    state width (mask true false) ≠ state width (mask false false) ∧
    state width (mask false true) ≠ state width (mask false false) := by
  simp [state,mask]

end Shared.ComplexityBridge.TM2OutputCellClassify
