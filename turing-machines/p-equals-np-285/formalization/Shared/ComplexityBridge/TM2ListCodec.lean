import Shared.ComplexityBridge.TM2ComposeEncoded
import Shared.ComplexityBridge.TM2UndelimitBlocksTotal

set_option linter.unusedSimpArgs false
namespace Shared.ComplexityBridge.TM2ListCodec
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
inductive Stack where | input | scratch | output
  deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.input,.scratch,.output] (by intro s; cases s <;> simp)
def stackVals (input scratch output : List Bool) : Stack → List Bool
  | .input => input | .scratch => scratch | .output => output

namespace Decode
inductive Label where | header | data | ending | restore | reject
  deriving DecidableEq
instance : Fintype Label := Fintype.ofList [.header,.data,.ending,.restore,.reject] (by intro l; cases l <;> simp)

def program : Label → Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .header => .pop .input (fun _ h => h)
      (.branch Option.isSome
        (.branch (fun v => v == some true) (.goto (fun _ => .data)) (.goto (fun _ => .reject)))
        (.goto (fun _ => .restore)))
  | .data => .pop .input (fun _ h => h)
      (.branch Option.isSome (.push .scratch (fun v => v.getD false) (.goto (fun _ => .ending)))
        (.goto (fun _ => .reject)))
  | .ending => .pop .input (fun _ h => h)
      (.branch (fun v => v == some false) (.goto (fun _ => .header)) (.goto (fun _ => .reject)))
  | .restore => .pop .scratch (fun _ h => h)
      (.branch Option.isSome (.push .output (fun v => v.getD false) (.goto (fun _ => .restore)))
        (.load (fun _ => none) .halt))
  | .reject => .goto (fun _ => .reject)

def machine : Turing.FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := fun _ => Bool
  Λ := Label
  main := .header
  σ := Option Bool
  initialState := none
  m := program

def cfg (l : Label) (v : Option Bool) (input scratch output : List Bool) : machine.Cfg :=
  ⟨some l,v,stackVals input scratch output⟩

theorem header_true (v : Option Bool) (input scratch output : List Bool) :
    machine.step (cfg .header v (true::input) scratch output) = some (cfg .data (some true) input scratch output) := by
  change some (Cfg.mk (some Label.data) (some true) (Function.update (stackVals (true::input) scratch output) .input input)) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem header_nil (v : Option Bool) (scratch output : List Bool) :
    machine.step (cfg .header v [] scratch output) = some (cfg .restore none [] scratch output) := by
  change some (Cfg.mk (some Label.restore) none (Function.update (stackVals [] scratch output) .input [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem data_cons (v : Option Bool) (b : Bool) (input scratch output : List Bool) :
    machine.step (cfg .data v (b::input) scratch output) = some (cfg .ending (some b) input (b::scratch) output) := by
  change some (Cfg.mk (some Label.ending) (some b)
    (Function.update (Function.update (stackVals (b::input) scratch output) .input input) .scratch (b::scratch))) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem ending_false (v : Option Bool) (input scratch output : List Bool) :
    machine.step (cfg .ending v (false::input) scratch output) = some (cfg .header (some false) input scratch output) := by
  change some (Cfg.mk (some Label.header) (some false) (Function.update (stackVals (false::input) scratch output) .input input)) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_cons (v : Option Bool) (b : Bool) (input scratch output : List Bool) :
    machine.step (cfg .restore v input (b::scratch) output) = some (cfg .restore (some b) input scratch (b::output)) := by
  change some (Cfg.mk (some Label.restore) (some b)
    (Function.update (Function.update (stackVals input (b::scratch) output) .scratch scratch) .output (b::output))) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_nil (v : Option Bool) (output : List Bool) :
    machine.step (cfg .restore v [] [] output) = some (Turing.haltList machine output) := by
  change some (Cfg.mk (none : Option Label) (none : Option Bool) (Function.update (stackVals [] [] output) .scratch [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update,Turing.haltList,machine] <;> rfl

theorem bitEncode_cons (b : Bool) (bits : List Bool) :
    BitstringEncoding.bitEncode (b::bits) = true::b::false::BitstringEncoding.bitEncode bits := rfl

theorem scan_run (bits tail scratch output : List Bool) (v : Option Bool) :
    ∃ v', runSteps machine.step (3*bits.length)
      (cfg .header v (BitstringEncoding.bitEncode bits ++ tail) scratch output) =
      some (cfg .header v' tail (bits.reverse++scratch) output) := by
  induction bits generalizing scratch v with
  | nil => exact ⟨v,by rfl⟩
  | cons b bits ih =>
    obtain ⟨v',h⟩ := ih (b::scratch) (some false)
    refine ⟨v',?_⟩
    rw [bitEncode_cons]
    simp only [List.length_cons,List.cons_append]
    have hn : 3*(bits.length+1) = ((3*bits.length+1)+1)+1 := by omega
    rw [hn,runSteps_front,header_true]
    change runSteps machine.step ((3*bits.length+1)+1)
      (cfg .data (some true) (b::false::(BitstringEncoding.bitEncode bits ++ tail)) scratch output) = _
    rw [runSteps_front,data_cons]
    change runSteps machine.step (3*bits.length+1)
      (cfg .ending (some b) (false::(BitstringEncoding.bitEncode bits ++ tail)) (b::scratch) output) = _
    rw [runSteps_front,ending_false]
    simpa [List.reverse_cons,List.append_assoc] using h

theorem restore_run (scratch output : List Bool) (v : Option Bool) :
    runSteps machine.step (scratch.length+1) (cfg .restore v [] scratch output) =
      some (Turing.haltList machine (scratch.reverse++output)) := by
  induction scratch generalizing output v with
  | nil => exact restore_nil v output
  | cons b scratch ih =>
    rw [List.length_cons,show scratch.length+1+1 = (scratch.length+1)+1 by omega,runSteps_front,restore_cons]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::output) (some b)

theorem initial_eq (input : List Bool) : Turing.initList machine input = cfg .header none input [] [] := by
  change Cfg.mk (some Label.header) none _ = Cfg.mk (some Label.header) none (stackVals input [] [])
  congr 1; funext k; cases k <;> simp [machine,stackVals] <;> rfl

theorem run (bits : List Bool) :
    runSteps machine.step (4*bits.length+2) (Turing.initList machine (BitstringEncoding.bitEncode bits)) =
      some (Turing.haltList machine bits) := by
  obtain ⟨v,hscan⟩ := scan_run bits [] [] [] none
  simp only [List.append_nil] at hscan
  have hrestore := restore_run bits.reverse [] none
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at hrestore
  have hn : 4*bits.length+2 = 3*bits.length+((bits.length+1)+1) := by omega
  rw [hn,initial_eq,runSteps_add,hscan]
  change runSteps machine.step ((bits.length+1)+1) (cfg .header v [] bits.reverse []) = _
  rw [runSteps_front,header_nil]
  exact hrestore

noncomputable def timePolynomial : Polynomial Nat := Polynomial.C 2 * Polynomial.X + Polynomial.C 2

theorem time_bound (bits : List Bool) : 4*bits.length+2 ≤ timePolynomial.eval (BitstringEncoding.bitEncode bits).length := by
  simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
    Shared.ComplexityBridge.bitstring_list_encoded_length]
  omega

set_option backward.isDefEq.respectTransparency false in
/-- Canonical list encoding to raw bits, with every boundary step charged. -/
noncomputable def timeMachine : Turing.TM2ComputableInPolyTime
    (BitstringEncoding.bitEncode : List Bool → List Bool) (id : List Bool → List Bool) id where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial
  outputsFun bits := by
    refine ⟨⟨4*bits.length+2,?_⟩,time_bound bits⟩
    have hr := run bits
    rw [runSteps_iterate] at hr
    change (fun o => o.bind machine.step)^[4*bits.length+2]
      (some (Turing.initList machine ((BitstringEncoding.bitEncode bits).map id))) =
      some (Turing.haltList machine (bits.map id))
    rw [List.map_id,List.map_id]
    exact hr
end Decode

namespace Encode
inductive Label where | scan | restore
  deriving DecidableEq
instance : Fintype Label := Fintype.ofList [.scan,.restore] (by intro l; cases l <;> simp)

def program : Label → Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .scan => .pop .input (fun _ h => h)
      (.branch Option.isSome
        (.push .scratch (fun _ => true)
          (.push .scratch (fun v => v.getD false) (.push .scratch (fun _ => false) (.goto (fun _ => .scan)))))
        (.goto (fun _ => .restore)))
  | .restore => .pop .scratch (fun _ h => h)
      (.branch Option.isSome (.push .output (fun v => v.getD false) (.goto (fun _ => .restore)))
        (.load (fun _ => none) .halt))

def machine : Turing.FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := fun _ => Bool
  Λ := Label
  main := .scan
  σ := Option Bool
  initialState := none
  m := program

def cfg (l : Label) (v : Option Bool) (input scratch output : List Bool) : machine.Cfg :=
  ⟨some l,v,stackVals input scratch output⟩

theorem scan_cons (v : Option Bool) (b : Bool) (input scratch output : List Bool) :
    machine.step (cfg .scan v (b::input) scratch output) =
      some (cfg .scan (some b) input (false::b::true::scratch) output) := by
  change some (Cfg.mk (some Label.scan) (some b) _) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update] <;> rfl

theorem scan_nil (v : Option Bool) (scratch output : List Bool) :
    machine.step (cfg .scan v [] scratch output) = some (cfg .restore none [] scratch output) := by
  change some (Cfg.mk (some Label.restore) none (Function.update (stackVals [] scratch output) .input [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_cons (v : Option Bool) (b : Bool) (input scratch output : List Bool) :
    machine.step (cfg .restore v input (b::scratch) output) = some (cfg .restore (some b) input scratch (b::output)) := by
  change some (Cfg.mk (some Label.restore) (some b)
    (Function.update (Function.update (stackVals input (b::scratch) output) .scratch scratch) .output (b::output))) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_nil (v : Option Bool) (output : List Bool) :
    machine.step (cfg .restore v [] [] output) = some (Turing.haltList machine output) := by
  change some (Cfg.mk (none : Option Label) (none : Option Bool) (Function.update (stackVals [] [] output) .scratch [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update,Turing.haltList,machine] <;> rfl

theorem scan_run (bits scratch output : List Bool) (v : Option Bool) :
    ∃ v', runSteps machine.step bits.length (cfg .scan v bits scratch output) =
      some (cfg .scan v' [] ((BitstringEncoding.bitEncode bits).reverse++scratch) output) := by
  induction bits generalizing scratch v with
  | nil => exact ⟨v,by rfl⟩
  | cons b bits ih =>
    obtain ⟨v',h⟩ := ih (false::b::true::scratch) (some b)
    refine ⟨v',?_⟩
    rw [List.length_cons,runSteps_front,scan_cons]
    simpa [Decode.bitEncode_cons,List.reverse_cons,List.append_assoc] using h

theorem restore_run (scratch output : List Bool) (v : Option Bool) :
    runSteps machine.step (scratch.length+1) (cfg .restore v [] scratch output) =
      some (Turing.haltList machine (scratch.reverse++output)) := by
  induction scratch generalizing output v with
  | nil => exact restore_nil v output
  | cons b scratch ih =>
    rw [List.length_cons,show scratch.length+1+1 = (scratch.length+1)+1 by omega,runSteps_front,restore_cons]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::output) (some b)

theorem initial_eq (input : List Bool) : Turing.initList machine input = cfg .scan none input [] [] := by
  change Cfg.mk (some Label.scan) none _ = Cfg.mk (some Label.scan) none (stackVals input [] [])
  congr 1; funext k; cases k <;> simp [machine,stackVals] <;> rfl

theorem run (bits : List Bool) :
    runSteps machine.step (4*bits.length+2) (Turing.initList machine bits) =
      some (Turing.haltList machine (BitstringEncoding.bitEncode bits)) := by
  obtain ⟨v,hscan⟩ := scan_run bits [] [] none
  simp only [List.append_nil] at hscan
  have hrestore := restore_run (BitstringEncoding.bitEncode bits).reverse [] none
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse,
    Shared.ComplexityBridge.bitstring_list_encoded_length] at hrestore
  have hn : 4*bits.length+2 = bits.length+((3*bits.length+1)+1) := by omega
  rw [hn,initial_eq,runSteps_add,hscan]
  change runSteps machine.step ((3*bits.length+1)+1)
    (cfg .scan v [] (BitstringEncoding.bitEncode bits).reverse []) = _
  rw [runSteps_front,scan_nil]
  exact hrestore

noncomputable def timePolynomial : Polynomial Nat := Polynomial.C 4 * Polynomial.X + Polynomial.C 2

set_option backward.isDefEq.respectTransparency false in
/-- Raw bits to canonical list encoding, with every boundary step charged. -/
noncomputable def timeMachine : Turing.TM2ComputableInPolyTime
    (id : List Bool → List Bool) (BitstringEncoding.bitEncode : List Bool → List Bool) id where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial
  outputsFun bits := by
    refine ⟨⟨4*bits.length+2,?_⟩,?_⟩
    · have hr := run bits
      rw [runSteps_iterate] at hr
      change (fun o => o.bind machine.step)^[4*bits.length+2]
        (some (Turing.initList machine (bits.map id))) =
        some (Turing.haltList machine ((BitstringEncoding.bitEncode bits).map id))
      rw [List.map_id,List.map_id]
      exact hr
    · simp [timePolynomial]
end Encode

end Shared.ComplexityBridge.TM2ListCodec
