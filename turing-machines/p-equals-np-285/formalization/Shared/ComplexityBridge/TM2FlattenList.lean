import Shared.ComplexityBridge.TM2FlattenBlocks
import Shared.ComplexityBridge.TM2UnaryTransfer
import Shared.ComplexityBridge.TM2ListAppend

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-! Flatten a canonically encoded list of lists. This machine removes exactly
one outer block delimiter per element and retains the inner serialization. -/
namespace Shared.ComplexityBridge.TM2FlattenList
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
abbrev U := Shared.ComplexityBridge.TM2FlattenBlocks.machine
abbrev Key := Shared.ComplexityBridge.TM2FlattenBlocks.Stack
abbrev Label := Shared.ComplexityBridge.TM2FlattenBlocks.Label
abbrev State := Shared.ComplexityBridge.TM2FlattenBlocks.State

def program : Label → Stmt (fun _ : Key => Bool) Label State
  | .done => .load (fun _ => (none,false)) .halt
  | l => Shared.ComplexityBridge.TM2FlattenBlocks.program l

def machine : Turing.FinTM2 := { U with m := program }

def terminal (q : U.Cfg) : Prop := q.l = some .done
noncomputable instance : DecidablePred terminal := fun _ => Classical.propDecidable _
theorem stable (q : U.Cfg) (h : terminal q) : U.step q = some q := by
  cases q with
  | mk l v st => change l = some .done at h; subst l; rfl

theorem simulate (q : U.Cfg) (h : ¬terminal q) : machine.step q = U.step q := by
  cases q with
  | mk l v st => cases l with
    | none => rfl
    | some l => cases l with
      | done => exact False.elim (h rfl)
      | header | data | restore | reject => rfl

theorem halt_step (bits : List Bool) :
    machine.step (Shared.ComplexityBridge.TM2FlattenBlocks.cfg .done none false [] [] bits) =
      some (Turing.haltList machine bits) := by
  change some (Cfg.mk _ _ _) = _
  congr 1; congr 1; funext k; cases k <;>
    simp [machine,U,Shared.ComplexityBridge.TM2FlattenBlocks.machine,Shared.ComplexityBridge.TM2FlattenBlocks.stackVals,Turing.haltList]

theorem run_bits (blocks : List (List Bool)) :
    ∃ t ≤ 2*(Shared.ComplexityBridge.TM2FlattenBlocks.framed blocks).length+3,
      runSteps machine.step t (Turing.initList machine (Shared.ComplexityBridge.TM2FlattenBlocks.framed blocks)) =
      some (Turing.haltList machine blocks.flatten) := by
  let fin := Shared.ComplexityBridge.TM2FlattenBlocks.cfg .done none false [] [] blocks.flatten
  have hrun := Shared.ComplexityBridge.TM2FlattenBlocks.valid_run blocks
  obtain ⟨d,hd,hr⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    U.step machine.step id terminal stable (fun q h => by simpa using simulate q h)
    _ _ fin (by rfl) hrun
  have hlen := Shared.ComplexityBridge.TM2FlattenBlocks.encoded_length_bound blocks
  refine ⟨d+1,by omega,?_⟩
  change runSteps machine.step d (Turing.initList machine (Shared.ComplexityBridge.TM2FlattenBlocks.framed blocks)) = some fin at hr
  rw [runSteps_add,hr]
  exact halt_step blocks.flatten

theorem outer_encoding {α : Type} [BitstringEncoding α] (xs : List (List α)) :
    Shared.ComplexityBridge.TM2FlattenBlocks.framed (xs.map BitstringEncoding.bitEncode) =
      BitstringEncoding.bitEncode xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change BitstringEncoding.delimit (BitstringEncoding.bitEncode x) ++
      Shared.ComplexityBridge.TM2FlattenBlocks.framed (xs.map BitstringEncoding.bitEncode) =
      BitstringEncoding.delimit (BitstringEncoding.bitEncode x) ++ BitstringEncoding.bitEncode xs
    rw [ih]

theorem flatten_encoding {α : Type} [BitstringEncoding α] (xs : List (List α)) :
    (xs.map BitstringEncoding.bitEncode).flatten = BitstringEncoding.bitEncode xs.flatten := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.flatten_cons,ih,Shared.ComplexityBridge.TM2ListAppend.list_encoding_append]

/-- Generic list flattening, including empty elements, has linear cost in the
actual Google-encoded input and returns the standard clean output. -/
noncomputable def timeMachine {α : Type} [BitstringEncoding α] :
    Turing.TM2ComputableInPolyTime (BitstringEncoding.bitEncode : List (List α) → List Bool)
      (BitstringEncoding.bitEncode : List α → List Bool) List.flatten where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 2*Polynomial.X+Polynomial.C 3
  outputsFun xs := by
    classical
    let bs := xs.map BitstringEncoding.bitEncode
    let t := Nat.find (run_bits bs)
    have ht := (Nat.find_spec (run_bits bs)).1
    have hr := (Nat.find_spec (run_bits bs)).2
    refine ⟨⟨t,?_⟩,?_⟩
    · change (fun o => o.bind machine.step)^[t]
        (some (Turing.initList machine ((BitstringEncoding.bitEncode xs).map id))) =
        some (Turing.haltList machine ((BitstringEncoding.bitEncode xs.flatten).map id))
      change runSteps machine.step t _ = _ at hr
      rw [runSteps_iterate] at hr
      change (fun o => o.bind machine.step)^[t]
        (some (Turing.initList machine (Shared.ComplexityBridge.TM2FlattenBlocks.framed (xs.map BitstringEncoding.bitEncode)))) =
        some (Turing.haltList machine ((xs.map BitstringEncoding.bitEncode).flatten)) at hr
      rw [outer_encoding,flatten_encoding] at hr
      simpa only [List.map_id] using hr
    · change t ≤ 2*(Shared.ComplexityBridge.TM2FlattenBlocks.framed (xs.map BitstringEncoding.bitEncode)).length+3 at ht
      rw [outer_encoding] at ht
      simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X] using ht

theorem flatten_isPolyTime {α : Type} [BitstringEncoding α] :
    ComplexityTheory.IsPolyTime (List.flatten : List (List α) → List α) := ⟨timeMachine⟩

namespace Fixtures
example : ∃ t ≤ 3, runSteps machine.step t (Turing.initList machine []) =
    some (Turing.haltList machine []) := by simpa [Shared.ComplexityBridge.TM2FlattenBlocks.framed] using run_bits []
example : ∃ t ≤ 11, runSteps machine.step t (Turing.initList machine [false,true,true,false]) =
    some (Turing.haltList machine [true]) := by
  simpa [Shared.ComplexityBridge.TM2FlattenBlocks.framed,BitstringEncoding.delimit] using run_bits [[],[true]]
end Fixtures
end Shared.ComplexityBridge.TM2FlattenList
