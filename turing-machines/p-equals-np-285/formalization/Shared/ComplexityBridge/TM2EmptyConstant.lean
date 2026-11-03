import Shared.ComplexityBridge.TM2Constant
import Shared.ComplexityBridge.CNFEncodingComputability

set_option backward.isDefEq.respectTransparency false

/-! A finite linear-time eraser supplies any fixed value whose canonical
encoding is empty, including the binary numeral zero. -/
namespace Shared.ComplexityBridge.TM2EmptyConstant
open Turing.TM2 Shared.Codes.TM2Program Shared.ComplexityBridge.TM2Symbols

def machine : Turing.FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ := fun _ => Bool
  Λ := Unit
  main := ()
  σ := Option Bool
  initialState := none
  m := fun _ => .pop () (fun _ h => h)
    (.branch Option.isSome (.goto (fun _ => ())) (.load (fun _ => none) .halt))

def cfg (v : Option Bool) (input : List Bool) : machine.Cfg := ⟨some (),v,fun _ => input⟩

theorem step_cons (v : Option Bool) (b : Bool) (input : List Bool) :
    machine.step (cfg v (b::input)) = some (cfg (some b) input) := by
  change some (Cfg.mk _ _ _) = _
  congr 1

theorem step_nil (v : Option Bool) : machine.step (cfg v []) = some (Turing.haltList machine []) := by
  change some (Cfg.mk _ _ _) = _
  congr 1

theorem erase (input : List Bool) (v : Option Bool) :
    runSteps machine.step (input.length+1) (cfg v input) = some (Turing.haltList machine []) := by
  induction input generalizing v with
  | nil => exact step_nil v
  | cons b input ih =>
    rw [List.length_cons,show input.length+1+1 = (input.length+1)+1 by omega,runSteps_front,step_cons]
    exact ih (some b)

theorem initial_eq (input : List Bool) : Turing.initList machine input = cfg none input := by
  change Cfg.mk _ _ _ = Cfg.mk _ _ _
  congr 1

noncomputable def timeMachine {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (value : β) (hvalue : BitstringEncoding.bitEncode value = []) :
    Turing.TM2ComputableInPolyTime (BitstringEncoding.bitEncode : α → List Bool)
      (BitstringEncoding.bitEncode : β → List Bool) (fun _ => value) where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X+Polynomial.C 1
  outputsFun x := by
    let bits := BitstringEncoding.bitEncode x
    refine ⟨⟨bits.length+1,?_⟩,?_⟩
    · have hr := erase bits none
      rw [← initial_eq] at hr
      rw [runSteps_iterate] at hr
      change (fun o => o.bind machine.step)^[bits.length+1]
        (some (Turing.initList machine (bits.map id))) =
        some (Turing.haltList machine ((BitstringEncoding.bitEncode value).map id))
      simpa [hvalue] using hr
    · simp [bits]

theorem isPolyTime {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (value : β) (hvalue : BitstringEncoding.bitEncode value = []) :
    ComplexityTheory.IsPolyTime (fun _ : α => value) := ⟨timeMachine value hvalue⟩

theorem zero_isPolyTime {α : Type} [BitstringEncoding α] :
    ComplexityTheory.IsPolyTime (fun _ : α => (0 : Nat)) := by
  apply isPolyTime
  change Computability.encodeNat 0 = []
  rw [Shared.ComplexityBridge.CNFEncodingComputability.encodeNat_bits]
  rfl
end Shared.ComplexityBridge.TM2EmptyConstant
