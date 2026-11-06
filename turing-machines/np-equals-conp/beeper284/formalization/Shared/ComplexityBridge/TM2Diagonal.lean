import Shared.ComplexityBridge.TM2ListCodec
import Shared.ComplexityBridge.TM2PairMap

set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2Diagonal
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
open Shared.ComplexityBridge.TM2ListCodec (Stack stackVals)
inductive Label where | scan1 | restore1 | scan2 | restore2 deriving DecidableEq
instance : Fintype Label := Fintype.ofList [.scan1,.restore1,.scan2,.restore2] (by intro l; cases l <;> simp)

def program : Label → Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .scan1 => .pop .input (fun _ h => h)
      (.branch Option.isSome (.push .scratch (fun v => v.getD false) (.goto (fun _ => .scan1))) (.goto (fun _ => .restore1)))
  | .restore1 => .pop .scratch (fun _ h => h)
      (.branch Option.isSome
        (.push .input (fun v => v.getD false)
          (.push .output (fun _ => false) (.push .output (fun v => v.getD false)
            (.push .output (fun _ => true) (.goto (fun _ => .restore1))))))
        (.goto (fun _ => .scan2)))
  | .scan2 => .pop .input (fun _ h => h)
      (.branch Option.isSome (.push .scratch (fun v => v.getD false) (.goto (fun _ => .scan2)))
        (.push .output (fun _ => false) (.goto (fun _ => .restore2))))
  | .restore2 => .pop .scratch (fun _ h => h)
      (.branch Option.isSome
        (.push .output (fun _ => false) (.push .output (fun _ => true)
          (.push .output (fun v => v.getD false) (.push .output (fun _ => true)
            (.push .output (fun _ => true) (.push .output (fun _ => true) (.goto (fun _ => .restore2))))))))
        (.load (fun _ => none) .halt))

def machine : Turing.FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := fun _ => Bool
  Λ := Label
  main := .scan1
  σ := Option Bool
  initialState := none
  m := program

def cfg (l : Label) (v : Option Bool) (input scratch output : List Bool) : machine.Cfg :=
  ⟨some l,v,stackVals input scratch output⟩

theorem scan1_cons (v : Option Bool) (b : Bool) (xs scratch out : List Bool) :
    machine.step (cfg .scan1 v (b::xs) scratch out) = some (cfg .scan1 (some b) xs (b::scratch) out) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> simp [stackVals,Function.update]
theorem scan1_nil (v : Option Bool) (scratch out : List Bool) :
    machine.step (cfg .scan1 v [] scratch out) = some (cfg .restore1 none [] scratch out) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> simp [stackVals,Function.update]
theorem restore1_cons (v : Option Bool) (b : Bool) (input scratch out : List Bool) :
    machine.step (cfg .restore1 v input (b::scratch) out) =
      some (cfg .restore1 (some b) (b::input) scratch (true::b::false::out)) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> simp [stackVals,Function.update]
theorem restore1_nil (v : Option Bool) (input out : List Bool) :
    machine.step (cfg .restore1 v input [] out) = some (cfg .scan2 none input [] out) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> simp [stackVals,Function.update]
theorem scan2_cons (v : Option Bool) (b : Bool) (xs scratch out : List Bool) :
    machine.step (cfg .scan2 v (b::xs) scratch out) = some (cfg .scan2 (some b) xs (b::scratch) out) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> simp [stackVals,Function.update]
theorem scan2_nil (v : Option Bool) (scratch out : List Bool) :
    machine.step (cfg .scan2 v [] scratch out) = some (cfg .restore2 none [] scratch (false::out)) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> simp [stackVals,Function.update]
theorem restore2_cons (v : Option Bool) (b : Bool) (scratch out : List Bool) :
    machine.step (cfg .restore2 v [] (b::scratch) out) =
      some (cfg .restore2 (some b) [] scratch (true::true::true::b::true::false::out)) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> simp [stackVals,Function.update]
theorem restore2_nil (v : Option Bool) (out : List Bool) :
    machine.step (cfg .restore2 v [] [] out) = some (Turing.haltList machine out) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> simp [stackVals,Function.update,Turing.haltList,machine] <;> rfl

def encoded (xs : List Bool) : List Bool := xs.flatMap (fun b => [true,b,false])
def prefixBits (xs : List Bool) : List Bool := xs.flatMap (fun b => [true,true,true,b,true,false])
theorem encoded_eq (xs : List Bool) : encoded xs = BitstringEncoding.bitEncode xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    change true::b::false::encoded xs = _
    rw [Shared.ComplexityBridge.TM2ListCodec.Decode.bitEncode_cons,ih]
theorem prefix_eq (xs : List Bool) : BitstringEncoding.delimit (encoded xs) = prefixBits xs ++ [false] := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    change true::true::true::b::true::false::BitstringEncoding.delimit (encoded xs) =
      true::true::true::b::true::false::(prefixBits xs ++ [false])
    rw [ih]

theorem scan1_loop (xs scratch out : List Bool) (v : Option Bool) :
    ∃ v', runSteps machine.step xs.length (cfg .scan1 v xs scratch out) =
      some (cfg .scan1 v' [] (xs.reverse++scratch) out) := by
  induction xs generalizing v scratch with
  | nil => exact ⟨v,by simp [runSteps]⟩
  | cons b xs ih =>
    obtain ⟨z,h⟩ := ih (b::scratch) (some b)
    refine ⟨z,?_⟩
    rw [List.length_cons,runSteps_front,scan1_cons]
    simpa [List.reverse_cons,List.append_assoc] using h

theorem restore1_loop (scratch input out : List Bool) (v : Option Bool) :
    ∃ v', runSteps machine.step scratch.length (cfg .restore1 v input scratch out) =
      some (cfg .restore1 v' (scratch.reverse++input) [] (encoded scratch.reverse++out)) := by
  induction scratch generalizing input out v with
  | nil => exact ⟨v,by simp [runSteps,encoded]⟩
  | cons b scratch ih =>
    obtain ⟨z,h⟩ := ih (b::input) (true::b::false::out) (some b)
    refine ⟨z,?_⟩
    rw [List.length_cons,runSteps_front,restore1_cons]
    simpa [encoded,List.reverse_cons,List.flatMap_append,List.append_assoc] using h

theorem scan2_loop (xs scratch out : List Bool) (v : Option Bool) :
    ∃ v', runSteps machine.step xs.length (cfg .scan2 v xs scratch out) =
      some (cfg .scan2 v' [] (xs.reverse++scratch) out) := by
  induction xs generalizing scratch v with
  | nil => exact ⟨v,by simp [runSteps]⟩
  | cons b xs ih =>
    obtain ⟨z,h⟩ := ih (b::scratch) (some b)
    refine ⟨z,?_⟩
    rw [List.length_cons,runSteps_front,scan2_cons]
    simpa [List.reverse_cons,List.append_assoc] using h

theorem restore2_loop (scratch out : List Bool) (v : Option Bool) :
    runSteps machine.step (scratch.length+1) (cfg .restore2 v [] scratch out) =
      some (Turing.haltList machine (prefixBits scratch.reverse++out)) := by
  induction scratch generalizing out v with
  | nil =>
    change machine.step (cfg .restore2 v [] [] out) = _
    simpa [prefixBits] using restore2_nil v out
  | cons b scratch ih =>
    rw [List.length_cons,show scratch.length+1+1 = (scratch.length+1)+1 by omega,runSteps_front,restore2_cons]
    simpa [prefixBits,List.reverse_cons,List.flatMap_append,List.append_assoc] using ih (true::true::true::b::true::false::out) (some b)

theorem initial_eq (input : List Bool) : Turing.initList machine input = cfg .scan1 none input [] [] := by
  change Cfg.mk _ _ _ = Cfg.mk _ _ _
  congr 1; funext k; cases k <;> simp [machine,stackVals,Turing.initList] <;> rfl

/-- From raw bits, produce the actual canonical encoding of `(x,x)` and halt
with every non-output stack empty. Both copies and all boundary tests cost steps. -/
theorem run (xs : List Bool) :
    runSteps machine.step (4*xs.length+4) (Turing.initList machine xs) =
      some (Turing.haltList machine (BitstringEncoding.bitEncode (xs,xs))) := by
  obtain ⟨a,ha⟩ := scan1_loop xs [] [] none
  simp only [List.append_nil] at ha
  obtain ⟨b,hb⟩ := restore1_loop xs.reverse [] [] none
  simp only [List.reverse_reverse,List.length_reverse,List.append_nil] at hb
  obtain ⟨c,hc⟩ := scan2_loop xs [] (encoded xs) none
  simp only [List.append_nil] at hc
  have hd := restore2_loop xs.reverse (false::encoded xs) none
  simp only [List.reverse_reverse,List.length_reverse] at hd
  have hout : prefixBits xs ++ false::encoded xs = BitstringEncoding.bitEncode (xs,xs) := by
    change prefixBits xs ++ false::encoded xs = BitstringEncoding.delimit (BitstringEncoding.bitEncode xs) ++ BitstringEncoding.bitEncode xs
    rw [← encoded_eq,prefix_eq]
    simp
  rw [hout] at hd
  have hcost : 4*xs.length+4 = xs.length+(1+(xs.length+(1+(xs.length+(1+(xs.length+1)))))) := by omega
  rw [initial_eq,hcost,runSteps_add,ha]
  change runSteps machine.step (1+(xs.length+(1+(xs.length+(1+(xs.length+1)))))) _ = _
  rw [runSteps_add]
  change (machine.step (cfg .scan1 a [] xs.reverse [])).bind _ = _
  rw [scan1_nil]
  change runSteps machine.step (xs.length+(1+(xs.length+(1+(xs.length+1))))) _ = _
  rw [runSteps_add,hb]
  change runSteps machine.step (1+(xs.length+(1+(xs.length+1)))) _ = _
  rw [runSteps_add]
  change (machine.step (cfg .restore1 b xs [] (encoded xs))).bind _ = _
  rw [restore1_nil]
  change runSteps machine.step (xs.length+(1+(xs.length+1))) _ = _
  rw [runSteps_add,hc]
  change runSteps machine.step (1+(xs.length+1)) _ = _
  rw [runSteps_add]
  change (machine.step (cfg .scan2 c [] xs.reverse (encoded xs))).bind _ = _
  rw [scan2_nil]
  exact hd

/-- Executable duplication under raw-bit input and canonical pair output. -/
noncomputable def rawTimeMachine : Turing.TM2ComputableInPolyTime
    (id : List Bool → List Bool) (BitstringEncoding.bitEncode : (List Bool × List Bool) → List Bool)
    (fun x : List Bool => (x,x)) where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 4*Polynomial.X+Polynomial.C 4
  outputsFun xs := by
    refine ⟨⟨4*xs.length+4,?_⟩,?_⟩
    · have hr := run xs
      rw [runSteps_iterate] at hr
      change (fun o => o.bind machine.step)^[4*xs.length+4] (some (Turing.initList machine (xs.map id))) =
        some (Turing.haltList machine ((BitstringEncoding.bitEncode (xs,xs)).map id))
      simpa using hr
    · simp

/-- The canonical-input diagonal has a real finite machine and a charged
encoding adapter; no noncomputable choice is executed by that machine. -/
theorem diagonal_isPolyTime : ComplexityTheory.IsPolyTime (fun x : List Bool => (x,x)) := by
  exact Shared.ComplexityBridge.TM2ComposeEncoded.compose
    (BitstringEncoding.bitEncode : List Bool → List Bool) (id : List Bool → List Bool)
    (BitstringEncoding.bitEncode : (List Bool × List Bool) → List Bool) id (fun x => (x,x))
    Shared.ComplexityBridge.TM2ListCodec.Decode.timeMachine rawTimeMachine

/-- Re-encode pair bytes as a canonical Boolean list with the cost of the
finite list encoder included. -/
noncomputable def pairBytesTimeMachine : Turing.TM2ComputableInPolyTime
    (BitstringEncoding.bitEncode : (List Bool × List Bool) → List Bool)
    (BitstringEncoding.bitEncode : List Bool → List Bool)
    (BitstringEncoding.bitEncode : (List Bool × List Bool) → List Bool) where
  toTM2ComputableAux := Shared.ComplexityBridge.TM2ListCodec.Encode.timeMachine.toTM2ComputableAux
  time := Shared.ComplexityBridge.TM2ListCodec.Encode.timeMachine.time
  outputsFun p := Shared.ComplexityBridge.TM2ListCodec.Encode.timeMachine.outputsFun (BitstringEncoding.bitEncode p)

/-- Construct and serialize both a polynomial-time result and its unchanged
input. The pair map and byte encoding are each separately charged. -/
theorem packed_with_input_isPolyTime (F : List Bool → List Bool) (hF : ComplexityTheory.IsPolyTime F) :
    ComplexityTheory.IsPolyTime (fun x : List Bool => BitstringEncoding.bitEncode (F x,x)) := by
  obtain ⟨diag⟩ := diagonal_isPolyTime
  obtain ⟨mapped⟩ := Shared.ComplexityBridge.TM2PairMap.pairMap_isPolyTime F hF
  obtain ⟨both⟩ := Shared.ComplexityBridge.TM2ComposeEncoded.compose
    (BitstringEncoding.bitEncode : List Bool → List Bool)
    (BitstringEncoding.bitEncode : (List Bool × List Bool) → List Bool)
    (BitstringEncoding.bitEncode : (List Bool × List Bool) → List Bool)
    (fun x : List Bool => (x,x)) (Shared.ComplexityBridge.TM2PairMap.pairMap F) diag mapped
  exact Shared.ComplexityBridge.TM2ComposeEncoded.compose
    (BitstringEncoding.bitEncode : List Bool → List Bool)
    (BitstringEncoding.bitEncode : (List Bool × List Bool) → List Bool)
    (BitstringEncoding.bitEncode : List Bool → List Bool)
    (fun x : List Bool => (F x,x)) (BitstringEncoding.bitEncode : (List Bool × List Bool) → List Bool)
    both pairBytesTimeMachine


namespace Fixtures
example : (runSteps machine.step 4 (Turing.initList machine [])).map
    (fun q => (q.l.isNone,q.stk .output)) = some (true,BitstringEncoding.bitEncode (([],[]) : List Bool × List Bool)) := by
  change (Option.map (fun q => (q.l.isNone,q.stk .output))
    (runSteps machine.step 4 (Turing.initList machine [])) : Option (Bool × List Bool)) = _
  decide
example : (runSteps machine.step 12 (Turing.initList machine [true,false])).map
    (fun q => (q.l.isNone,q.stk .output)) = some (true,BitstringEncoding.bitEncode ([true,false],[true,false])) := by
  change (Option.map (fun q => (q.l.isNone,q.stk .output))
    (runSteps machine.step 12 (Turing.initList machine [true,false])) : Option (Bool × List Bool)) = _
  decide
end Fixtures

end Shared.ComplexityBridge.TM2Diagonal
