import Shared.ComplexityBridge.TM2WitnessRawComplete

set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2TripleRepack
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
inductive Stack where | input | scratch | output deriving DecidableEq
inductive Label where | header | data | tail | restore deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.input,.scratch,.output] (by intro s; cases s <;> simp)
instance : Fintype Label := Fintype.ofList [.header,.data,.tail,.restore] (by intro l; cases l <;> simp)

def program : Label → Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .header => .pop .input (fun _ h => h)
      (.branch Option.isSome
        (.push .scratch (fun v => v.getD false)
          (.branch (fun v => v == some true) (.goto (fun _ => .data)) (.goto (fun _ => .tail))))
        (.goto (fun _ => .restore)))
  | .data => .pop .input (fun _ h => h)
      (.branch Option.isSome (.push .scratch (fun v => v.getD false) (.goto (fun _ => .header)))
        (.goto (fun _ => .restore)))
  | .tail => .pop .input (fun _ h => h)
      (.branch Option.isSome
        (.push .scratch (fun _ => true) (.push .scratch (fun v => v.getD false)
          (.push .scratch (fun _ => false) (.goto (fun _ => .tail)))))
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
  main := .header
  σ := Option Bool
  initialState := none
  m := program

def stackVals (input scratch output : List Bool) : Stack → List Bool
  | .input => input | .scratch => scratch | .output => output
def cfg (l : Label) (v : Option Bool) (input scratch output : List Bool) : machine.Cfg :=
  ⟨some l,v,stackVals input scratch output⟩

theorem header_true (v : Option Bool) (input scratch output : List Bool) :
    machine.step (cfg .header v (true::input) scratch output) = some (cfg .data (some true) input (true::scratch) output) := by
  change some (Cfg.mk _ _ (Function.update (Function.update (stackVals (true::input) scratch output) .input input) .scratch (true::scratch))) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem header_false (v : Option Bool) (input scratch output : List Bool) :
    machine.step (cfg .header v (false::input) scratch output) = some (cfg .tail (some false) input (false::scratch) output) := by
  change some (Cfg.mk _ _ (Function.update (Function.update (stackVals (false::input) scratch output) .input input) .scratch (false::scratch))) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem data_cons (v : Option Bool) (b : Bool) (input scratch output : List Bool) :
    machine.step (cfg .data v (b::input) scratch output) = some (cfg .header (some b) input (b::scratch) output) := by
  change some (Cfg.mk _ _ (Function.update (Function.update (stackVals (b::input) scratch output) .input input) .scratch (b::scratch))) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem tail_cons (v : Option Bool) (b : Bool) (input scratch output : List Bool) :
    machine.step (cfg .tail v (b::input) scratch output) = some (cfg .tail (some b) input (false::b::true::scratch) output) := by
  change some (Cfg.mk _ _ (Function.update (Function.update (Function.update (Function.update
    (stackVals (b::input) scratch output) .input input) .scratch (true::scratch)) .scratch (b::true::scratch)) .scratch (false::b::true::scratch))) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem tail_nil (v : Option Bool) (scratch output : List Bool) :
    machine.step (cfg .tail v [] scratch output) = some (cfg .restore none [] scratch output) := by
  change some (Cfg.mk _ _ (Function.update (stackVals [] scratch output) .input [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_cons (v : Option Bool) (b : Bool) (scratch output : List Bool) :
    machine.step (cfg .restore v [] (b::scratch) output) = some (cfg .restore (some b) [] scratch (b::output)) := by
  change some (Cfg.mk _ _ (Function.update (Function.update (stackVals [] (b::scratch) output) .scratch scratch) .output (b::output))) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_nil (v : Option Bool) (output : List Bool) :
    machine.step (cfg .restore v [] [] output) = some (Turing.haltList machine output) := by
  change some (Cfg.mk _ _ (Function.update (stackVals [] [] output) .scratch [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update,Turing.haltList,machine] <;> rfl

def markers (payload : List Bool) : List Bool := payload.flatMap (fun b => [true,b])

theorem prefix_loop (payload tail scratch output : List Bool) (v : Option Bool) :
    ∃ v', runSteps machine.step (2*payload.length) (cfg .header v (BitstringEncoding.delimit payload ++ tail) scratch output) =
      some (cfg .header v' (false::tail) ((markers payload).reverse++scratch) output) := by
  induction payload generalizing scratch v with
  | nil => exact ⟨v,by simp [runSteps,BitstringEncoding.delimit,markers]⟩
  | cons b payload ih =>
    obtain ⟨v',h⟩ := ih (b::true::scratch) (some b)
    refine ⟨v',?_⟩
    simp only [List.length_cons,BitstringEncoding.delimit,List.cons_append]
    have hn : 2*(payload.length+1) = (2*payload.length+1)+1 := by omega
    rw [hn,runSteps_front,header_true]
    change runSteps machine.step (2*payload.length+1) (cfg .data (some true) (b::(BitstringEncoding.delimit payload ++ tail)) (true::scratch) output) = _
    rw [runSteps_front,data_cons]
    simpa [markers,List.reverse_append,List.append_assoc] using h

theorem delimit_markers (payload : List Bool) : BitstringEncoding.delimit payload = markers payload ++ [false] := by
  induction payload with
  | nil => rfl
  | cons b payload ih => simp [BitstringEncoding.delimit,markers,ih]

theorem tail_loop (tail scratch output : List Bool) (v : Option Bool) :
    ∃ v', runSteps machine.step tail.length (cfg .tail v tail scratch output) =
      some (cfg .tail v' [] ((BitstringEncoding.bitEncode tail).reverse++scratch) output) := by
  induction tail generalizing scratch v with
  | nil => exact ⟨v,by simp [runSteps,BitstringEncoding.bitEncode,BitstringEncoding.toEncoding,BitstringEncoding.instList]⟩
  | cons b tail ih =>
    obtain ⟨v',h⟩ := ih (false::b::true::scratch) (some b)
    refine ⟨v',?_⟩
    rw [List.length_cons,runSteps_front,tail_cons]
    change runSteps machine.step tail.length _ = some (cfg .tail v' [] (([true,b,false] ++ BitstringEncoding.bitEncode tail).reverse ++ scratch) output)
    simpa [List.reverse_append,List.append_assoc] using h

theorem restore_loop (scratch output : List Bool) (v : Option Bool) :
    runSteps machine.step (scratch.length+1) (cfg .restore v [] scratch output) =
      some (Turing.haltList machine (scratch.reverse++output)) := by
  induction scratch generalizing output v with
  | nil =>
    change machine.step (cfg .restore v [] [] output) = _
    simpa using restore_nil v output
  | cons b scratch ih =>
    rw [List.length_cons,show scratch.length+1+1 = (scratch.length+1)+1 by omega,runSteps_front,restore_cons]
    simpa [List.reverse_cons,List.append_assoc] using ih (b::output) (some b)

theorem initial_eq (input : List Bool) : Turing.initList machine input = cfg .header none input [] [] := by
  change Cfg.mk _ _ _ = Cfg.mk _ _ _
  congr 1; funext k; cases k <;> simp [machine,stackVals,Turing.initList] <;> rfl

/-- Re-encode the suffix as a Boolean list, preserving the self-delimiting
first component. The equality counts every scan and restore block. -/
theorem repack_run (payload tail : List Bool) :
    let input := BitstringEncoding.delimit payload ++ tail
    let output := BitstringEncoding.delimit payload ++ BitstringEncoding.bitEncode tail
    runSteps machine.step (input.length+output.length+2) (Turing.initList machine input) =
      some (Turing.haltList machine output) := by
  let pre := BitstringEncoding.delimit payload
  let out := pre ++ BitstringEncoding.bitEncode tail
  obtain ⟨v,hp⟩ := prefix_loop payload tail [] [] none
  simp only [List.append_nil] at hp
  have hp' : runSteps machine.step (2*payload.length+1) (cfg .header none (pre++tail) [] []) =
      some (cfg .tail (some false) tail pre.reverse []) := by
    rw [runSteps_add,hp]
    change machine.step (cfg .header v (false::tail) (markers payload).reverse []) = _
    rw [header_false]
    change some (cfg .tail (some false) tail (false::(markers payload).reverse) []) =
      some (cfg .tail (some false) tail (BitstringEncoding.delimit payload).reverse [])
    rw [delimit_markers]
    simp [List.reverse_append]
  obtain ⟨w,ht⟩ := tail_loop tail pre.reverse [] (some false)
  have ht' : runSteps machine.step (tail.length+1) (cfg .tail (some false) tail pre.reverse []) =
      some (cfg .restore none [] out.reverse []) := by
    rw [runSteps_add,ht]
    change machine.step (cfg .tail w [] ((BitstringEncoding.bitEncode tail).reverse++pre.reverse) []) = _
    rw [tail_nil]
    simp [out,List.reverse_append]
  have hr := restore_loop out.reverse [] none
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at hr
  have hlen : (pre++tail).length = (2*payload.length+1)+tail.length := by
    simp [pre,BitstringEncoding.length_delimit]
  have hn : (pre++tail).length+out.length+2 = (2*payload.length+1)+((tail.length+1)+(out.length+1)) := by omega
  change runSteps machine.step ((pre++tail).length+out.length+2) (Turing.initList machine (pre++tail)) = _
  rw [initial_eq,hn,runSteps_add,hp']
  change runSteps machine.step ((tail.length+1)+(out.length+1)) (cfg .tail (some false) tail pre.reverse []) = _
  rw [runSteps_add,ht']
  exact hr

abbrev Triple := Shared.ComplexityBridge.TM2WitnessComplete.Triple
noncomputable def timePolynomial : Polynomial Nat := Polynomial.C 4*Polynomial.X+Polynomial.C 2

theorem triple_run (p : Triple) :
    ∃ t ≤ timePolynomial.eval (BitstringEncoding.bitEncode p).length,
      runSteps machine.step t (Turing.initList machine (BitstringEncoding.bitEncode p)) =
        some (Turing.haltList machine (Shared.ComplexityBridge.TM2WitnessComplete.tripleInput p)) := by
  let payload := BitstringEncoding.bitEncode p.1
  let tail := BitstringEncoding.bitEncode p.2
  let input := BitstringEncoding.bitEncode p
  let output := Shared.ComplexityBridge.TM2WitnessComplete.tripleInput p
  have hi : input = BitstringEncoding.delimit payload ++ tail := by rfl
  have ho : output = BitstringEncoding.delimit payload ++ BitstringEncoding.bitEncode tail := by rfl
  have h := repack_run payload tail
  change runSteps machine.step ((BitstringEncoding.delimit payload ++ tail).length +
    (BitstringEncoding.delimit payload ++ BitstringEncoding.bitEncode tail).length + 2)
      (Turing.initList machine (BitstringEncoding.delimit payload ++ tail)) =
    some (Turing.haltList machine (BitstringEncoding.delimit payload ++ BitstringEncoding.bitEncode tail)) at h
  rw [← hi,← ho] at h
  have htail : (BitstringEncoding.bitEncode tail).length = 3*tail.length :=
    Shared.ComplexityBridge.bitstring_list_encoded_length tail
  have hlen : output.length ≤ 3*input.length := by
    rw [hi,ho,List.length_append,List.length_append,htail]
    omega
  refine ⟨input.length+output.length+2,?_,h⟩
  change input.length+output.length+2 ≤ timePolynomial.eval input.length
  simp [timePolynomial]
  omega

/-- Convert the public canonical triple encoding to the explicitly nested
serialization used by the finite lookup, without changing its abstract input. -/
noncomputable def timeMachine : Turing.TM2ComputableInPolyTime
    (BitstringEncoding.bitEncode : Triple → List Bool)
    Shared.ComplexityBridge.TM2WitnessComplete.tripleInput (id : Triple → Triple) where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial
  outputsFun p := by
    let t := Classical.choose (triple_run p)
    have ht := (Classical.choose_spec (triple_run p)).1
    have hr := (Classical.choose_spec (triple_run p)).2
    refine ⟨⟨t,?_⟩,?_⟩
    · rw [runSteps_iterate] at hr
      change (fun o => o.bind machine.step)^[t]
        (some (Turing.initList machine ((BitstringEncoding.bitEncode p).map id))) =
        some (Turing.haltList machine ((Shared.ComplexityBridge.TM2WitnessComplete.tripleInput p).map id))
      rw [List.map_id,List.map_id]
      simpa [t] using hr
    · exact ht

/-- The total raw-frame lookup is polynomial-time under the public library's
canonical triple and Boolean encodings, including malformed raw frames. -/
theorem lookupTriple_isPolyTime : ComplexityTheory.IsPolyTime Shared.ComplexityBridge.TM2WitnessComplete.lookupTriple := by
  obtain ⟨m⟩ := Shared.ComplexityBridge.TM2ComposeEncoded.compose
    (BitstringEncoding.bitEncode : Triple → List Bool)
    Shared.ComplexityBridge.TM2WitnessComplete.tripleInput
    (BitstringEncoding.bitEncode : Bool → List Bool)
    (id : Triple → Triple) Shared.ComplexityBridge.TM2WitnessComplete.lookupTriple
    timeMachine Shared.ComplexityBridge.TM2WitnessComplete.tripleTimeMachine
  exact ⟨m⟩

namespace Fixtures
example : Shared.ComplexityBridge.TM2WitnessLookup.lookupRaw [true] [true] [false] = false := by decide
example : Shared.ComplexityBridge.TM2WitnessLookup.lookupRaw [false,true] [true,false] [] = true := by decide
example : Shared.ComplexityBridge.TM2WitnessLookup.lookupRaw [false,true] [false,true] [] = false := by decide
end Fixtures

end Shared.ComplexityBridge.TM2TripleRepack
