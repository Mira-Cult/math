import Shared.ComplexityBridge.TM2PairLength

namespace Shared.ComplexityBridge.TM2PairLengths
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
open Shared.ComplexityBridge.TM2PairLength (xBlock wBlock xBits wBits pair_encoding)

inductive Stack where | input | scratch | xCount | wCount
  deriving DecidableEq
inductive Count where | none | x | w
  deriving DecidableEq
abbrev Label := Shared.ComplexityBridge.TM2PairLength.Label
instance : Fintype Stack := Fintype.ofList [.input,.scratch,.xCount,.wCount] (by intro s; cases s <;> simp)

def scan (next : Label) (count : Count) : Stmt (fun _ : Stack => Bool) Label (Option Bool) :=
  .pop .input (fun _ h => h)
    (.branch Option.isSome
      (.push .scratch (fun v => v.getD false)
        (match count with
         | .none => .goto (fun _ => next)
         | .x => .push .xCount (fun _ => true) (.goto (fun _ => next))
         | .w => .push .wCount (fun _ => true) (.goto (fun _ => next))))
      (.goto (fun _ => .restore)))

def program : Label → Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .start => .goto (fun _ => .x0)
  | .x0 => .pop .input (fun _ h => h)
      (.branch Option.isSome
        (.push .scratch (fun v => v.getD false)
          (.branch (fun v => v == some false) (.goto (fun _ => .w0)) (.goto (fun _ => .x1))))
        (.goto (fun _ => .restore)))
  | .x1 => scan .x2 .none
  | .x2 => scan .x3 .none
  | .x3 => scan .x4 .none
  | .x4 => scan .x5 .none
  | .x5 => scan .x0 .x
  | .w0 => scan .w1 .none
  | .w1 => scan .w2 .none
  | .w2 => scan .w0 .w
  | .restore => .pop .scratch (fun _ h => h)
      (.branch Option.isSome
        (.push .input (fun v => v.getD false) (.goto (fun _ => .restore)))
        (.goto (fun _ => .done)))
  | .done => .goto (fun _ => .done)

def machine : Turing.FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .xCount
  Γ := fun _ => Bool
  Λ := Label
  main := .start
  σ := Option Bool
  initialState := none
  m := program

def stackVals (input scratch : List Bool) (nx nw : Nat) : Stack → List Bool
  | .input => input
  | .scratch => scratch
  | .xCount => List.replicate nx true
  | .wCount => List.replicate nw true

def cfg (l : Label) (v : Option Bool) (input scratch : List Bool) (nx nw : Nat) : machine.Cfg :=
  ⟨some l,v,stackVals input scratch nx nw⟩

theorem start_step (input scratch : List Bool) (nx nw : Nat) (v : Option Bool) :
    machine.step (cfg .start v input scratch nx nw) = some (cfg .x0 v input scratch nx nw) := rfl

theorem header_step (v : Option Bool) (b : Bool) (input scratch : List Bool) (nx nw : Nat) :
    machine.step (cfg .x0 v (b::input) scratch nx nw) =
      some (cfg (if b then .x1 else .w0) (some b) input (b::scratch) nx nw) := by
  cases b <;>
    change some (Cfg.mk (some _) _ (Function.update (Function.update (stackVals (_::_) scratch nx nw) .input input)
      .scratch (_::scratch))) = some (Cfg.mk (some _) _ (stackVals input (_::scratch) nx nw)) <;>
    congr 1 <;> congr 1 <;> funext k <;> cases k <;> simp [stackVals,Function.update] <;> rfl

theorem scan_stepAux (next : Label) (count : Count) (v : Option Bool) (b : Bool)
    (input scratch : List Bool) (nx nw : Nat) :
    stepAux (scan next count) v (stackVals (b::input) scratch nx nw) =
      cfg next (some b) input (b::scratch) (nx + if count = .x then 1 else 0) (nw + if count = .w then 1 else 0) := by
  cases count <;>
    change Cfg.mk (some next) (some b) _ = Cfg.mk (some next) (some b) (stackVals input (b::scratch) _ _) <;>
    congr 1 <;> funext k <;> cases k <;> simp [stackVals,Function.update,List.replicate_succ]

theorem scan_nil (l next : Label) (count : Count) (v : Option Bool) (scratch : List Bool) (nx nw : Nat)
    (h : program l = scan next count) :
    machine.step (cfg l v [] scratch nx nw) = some (cfg .restore none [] scratch nx nw) := by
  change some (stepAux (program l) v (stackVals [] scratch nx nw)) = _
  rw [h]
  change some (Cfg.mk (some Shared.ComplexityBridge.TM2PairLength.Label.restore) none (Function.update (stackVals [] scratch nx nw) .input [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_cons (v : Option Bool) (b : Bool) (input scratch : List Bool) (nx nw : Nat) :
    machine.step (cfg .restore v input (b::scratch) nx nw) = some (cfg .restore (some b) (b::input) scratch nx nw) := by
  change some (Cfg.mk (some Shared.ComplexityBridge.TM2PairLength.Label.restore) (some b)
    (Function.update (Function.update (stackVals input (b::scratch) nx nw) .scratch scratch) .input (b::input))) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_nil (v : Option Bool) (input : List Bool) (nx nw : Nat) :
    machine.step (cfg .restore v input [] nx nw) = some (cfg .done none input [] nx nw) := by
  change some (Cfg.mk (some Shared.ComplexityBridge.TM2PairLength.Label.done) none (Function.update (stackVals input [] nx nw) .scratch [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem scan_cons (l next : Label) (count : Count) (v : Option Bool) (b : Bool)
    (input scratch : List Bool) (nx nw : Nat) (h : program l = scan next count) :
    machine.step (cfg l v (b::input) scratch nx nw) =
      some (cfg next (some b) input (b::scratch) (nx + if count = .x then 1 else 0) (nw + if count = .w then 1 else 0)) := by
  change some (stepAux (program l) v (stackVals (b::input) scratch nx nw)) = _
  rw [h,scan_stepAux]
  rfl

theorem x1_cons (v : Option Bool) (b : Bool) (input scratch : List Bool) (nx nw : Nat) :
    machine.step (cfg .x1 v (b::input) scratch nx nw) =
      some (cfg .x2 (some b) input (b::scratch) (nx+0) (nw+0)) := by
  exact scan_cons .x1 .x2 .none v b input scratch nx nw rfl

theorem x2_cons (v : Option Bool) (b : Bool) (input scratch : List Bool) (nx nw : Nat) :
    machine.step (cfg .x2 v (b::input) scratch nx nw) =
      some (cfg .x3 (some b) input (b::scratch) (nx+0) (nw+0)) := by
  exact scan_cons .x2 .x3 .none v b input scratch nx nw rfl

theorem x3_cons (v : Option Bool) (b : Bool) (input scratch : List Bool) (nx nw : Nat) :
    machine.step (cfg .x3 v (b::input) scratch nx nw) =
      some (cfg .x4 (some b) input (b::scratch) (nx+0) (nw+0)) := by
  exact scan_cons .x3 .x4 .none v b input scratch nx nw rfl

theorem x4_cons (v : Option Bool) (b : Bool) (input scratch : List Bool) (nx nw : Nat) :
    machine.step (cfg .x4 v (b::input) scratch nx nw) =
      some (cfg .x5 (some b) input (b::scratch) (nx+0) (nw+0)) := by
  exact scan_cons .x4 .x5 .none v b input scratch nx nw rfl

theorem x5_cons (v : Option Bool) (b : Bool) (input scratch : List Bool) (nx nw : Nat) :
    machine.step (cfg .x5 v (b::input) scratch nx nw) =
      some (cfg .x0 (some b) input (b::scratch) (nx+1) (nw+0)) := by
  exact scan_cons .x5 .x0 .x v b input scratch nx nw rfl

theorem w0_cons (v : Option Bool) (b : Bool) (input scratch : List Bool) (nx nw : Nat) :
    machine.step (cfg .w0 v (b::input) scratch nx nw) =
      some (cfg .w1 (some b) input (b::scratch) (nx+0) (nw+0)) := by
  exact scan_cons .w0 .w1 .none v b input scratch nx nw rfl

theorem w1_cons (v : Option Bool) (b : Bool) (input scratch : List Bool) (nx nw : Nat) :
    machine.step (cfg .w1 v (b::input) scratch nx nw) =
      some (cfg .w2 (some b) input (b::scratch) (nx+0) (nw+0)) := by
  exact scan_cons .w1 .w2 .none v b input scratch nx nw rfl

theorem w2_cons (v : Option Bool) (b : Bool) (input scratch : List Bool) (nx nw : Nat) :
    machine.step (cfg .w2 v (b::input) scratch nx nw) =
      some (cfg .w0 (some b) input (b::scratch) (nx+0) (nw+1)) := by
  exact scan_cons .w2 .w0 .w v b input scratch nx nw rfl

/-- One encoded first-component block increments only the first counter. -/
theorem xBlock_run (b : Bool) (input scratch : List Bool) (nx nw : Nat) (v : Option Bool) :
    runSteps machine.step 6 (cfg .x0 v (xBlock b ++ input) scratch nx nw) =
      some (cfg .x0 (some false) input ((xBlock b).reverse ++ scratch) (nx+1) nw) := by
  simp only [Shared.ComplexityBridge.TM2PairLength.xBlock, List.cons_append, List.nil_append,
    List.reverse_cons, List.reverse_nil, runSteps_front, Option.bind_some, header_step, if_pos,
    x1_cons,x2_cons,x3_cons,x4_cons,x5_cons,Nat.add_zero]
  rfl

/-- One encoded witness block increments only the witness counter. -/
theorem wBlock_run (b : Bool) (input scratch : List Bool) (nx nw : Nat) (v : Option Bool) :
    runSteps machine.step 3 (cfg .w0 v (wBlock b ++ input) scratch nx nw) =
      some (cfg .w0 (some false) input ((wBlock b).reverse ++ scratch) nx (nw+1)) := by
  simp only [Shared.ComplexityBridge.TM2PairLength.wBlock, List.cons_append, List.nil_append,
    List.reverse_cons, List.reverse_nil, runSteps_front, Option.bind_some, w0_cons,w1_cons,w2_cons,Nat.add_zero]
  rfl

theorem x_run (x : List Bool) (tail scratch : List Bool) (nx nw : Nat) (v : Option Bool) :
    ∃ v', runSteps machine.step (6*x.length) (cfg .x0 v (xBits x ++ tail) scratch nx nw) =
      some (cfg .x0 v' tail ((xBits x).reverse ++ scratch) (nx+x.length) nw) := by
  induction x generalizing scratch nx v with
  | nil => exact ⟨v, by simp [Shared.ComplexityBridge.TM2PairLength.xBits,runSteps]⟩
  | cons b x ih =>
    obtain ⟨v', h⟩ := ih ((xBlock b).reverse ++ scratch) (nx+1) (some false)
    refine ⟨v', ?_⟩
    simp only [List.length_cons, Shared.ComplexityBridge.TM2PairLength.xBits, List.flatMap_cons, List.append_assoc]
    have hn : 6*(x.length+1) = 6+6*x.length := by omega
    rw [hn,runSteps_add,xBlock_run]
    simpa [Shared.ComplexityBridge.TM2PairLength.xBits,List.reverse_append,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem w_run (w : List Bool) (tail scratch : List Bool) (nx nw : Nat) (v : Option Bool) :
    ∃ v', runSteps machine.step (3*w.length) (cfg .w0 v (wBits w ++ tail) scratch nx nw) =
      some (cfg .w0 v' tail ((wBits w).reverse ++ scratch) nx (nw+w.length)) := by
  induction w generalizing scratch nw v with
  | nil => exact ⟨v, by simp [Shared.ComplexityBridge.TM2PairLength.wBits,runSteps]⟩
  | cons b w ih =>
    obtain ⟨v', h⟩ := ih ((wBlock b).reverse ++ scratch) (nw+1) (some false)
    refine ⟨v', ?_⟩
    simp only [List.length_cons, Shared.ComplexityBridge.TM2PairLength.wBits, List.flatMap_cons, List.append_assoc]
    have hn : 3*(w.length+1) = 3+3*w.length := by omega
    rw [hn,runSteps_add,wBlock_run]
    simpa [Shared.ComplexityBridge.TM2PairLength.wBits,List.reverse_append,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem restore_run (scratch input : List Bool) (nx nw : Nat) (v : Option Bool) :
    ∃ v', runSteps machine.step scratch.length (cfg .restore v input scratch nx nw) =
      some (cfg .restore v' (scratch.reverse ++ input) [] nx nw) := by
  induction scratch generalizing input v with
  | nil => exact ⟨v,by simp [runSteps]⟩
  | cons b scratch ih =>
    obtain ⟨v',h⟩ := ih (b::input) (some b)
    refine ⟨v',?_⟩
    rw [List.length_cons,runSteps_front,restore_cons]
    simpa [List.reverse_cons,List.append_assoc] using h

theorem initial_eq (input : List Bool) :
    Turing.initList machine input = cfg .start none input [] 0 0 := by
  change Cfg.mk (some Shared.ComplexityBridge.TM2PairLength.Label.start) none _ =
    Cfg.mk (some Shared.ComplexityBridge.TM2PairLength.Label.start) none (stackVals input [] 0 0)
  congr 1
  funext s
  cases s <;> simp [machine,stackVals] <;> rfl

/-- From the library's actual pair input, restore the input unchanged and
produce separate unary counters of the raw input and witness lengths. -/
theorem load_pair_lengths (x w : List Bool) :
    runSteps machine.step (2*(BitstringEncoding.bitEncode (x,w)).length+3)
      (Turing.initList machine (BitstringEncoding.bitEncode (x,w))) =
    some (cfg .done none (BitstringEncoding.bitEncode (x,w)) [] x.length w.length) := by
  let bits := BitstringEncoding.bitEncode (x,w)
  have hbits : bits = xBits x ++ false::wBits w := by simpa [bits] using pair_encoding x w
  obtain ⟨v,hx⟩ := x_run x (false::wBits w) [] 0 0 none
  simp only [List.append_nil,Nat.zero_add] at hx
  have hx' : runSteps machine.step (6*x.length+1) (cfg .x0 none bits [] 0 0) =
      some (cfg .w0 (some false) (wBits w) (false::(xBits x).reverse) x.length 0) := by
    rw [hbits,runSteps_add,hx]
    change machine.step (cfg .x0 v (false::wBits w) (xBits x).reverse x.length 0) = _
    exact header_step v false (wBits w) (xBits x).reverse x.length 0
  obtain ⟨z,hw⟩ := w_run w [] (false::(xBits x).reverse) x.length 0 (some false)
  simp only [List.append_nil,Nat.zero_add] at hw
  have hw' : runSteps machine.step (3*w.length+1)
      (cfg .w0 (some false) (wBits w) (false::(xBits x).reverse) x.length 0) =
      some (cfg .restore none [] ((wBits w).reverse ++ false::(xBits x).reverse) x.length w.length) := by
    rw [runSteps_add,hw]
    change machine.step (cfg .w0 z [] ((wBits w).reverse ++ false::(xBits x).reverse) x.length w.length) = _
    exact scan_nil .w0 .w1 .none z _ _ _ rfl
  have hreverse : (wBits w).reverse ++ false::(xBits x).reverse = bits.reverse := by
    rw [hbits]
    simp [List.reverse_append,List.append_assoc]
  rw [hreverse] at hw'
  obtain ⟨r,hr⟩ := restore_run bits.reverse [] x.length w.length none
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at hr
  have hr' : runSteps machine.step (bits.length+1) (cfg .restore none [] bits.reverse x.length w.length) =
      some (cfg .done none bits [] x.length w.length) := by
    rw [runSteps_add,hr]
    change machine.step (cfg .restore r bits [] x.length w.length) = _
    exact restore_nil r bits _ _
  have hlength : bits.length = 6*x.length+1+3*w.length :=
    Shared.ComplexityBridge.bitstring_pair_encoded_length x w
  have hcost : 2*bits.length+3 = ((6*x.length+1)+((3*w.length+1)+(bits.length+1)))+1 := by omega
  rw [initial_eq,hcost,runSteps_front,start_step]
  change runSteps machine.step ((6*x.length+1)+((3*w.length+1)+(bits.length+1))) (cfg .x0 none bits [] 0 0) = _
  rw [runSteps_add,hx']
  change runSteps machine.step ((3*w.length+1)+(bits.length+1))
    (cfg .w0 (some false) (wBits w) (false::(xBits x).reverse) x.length 0) = _
  rw [runSteps_add,hw']
  change runSteps machine.step (bits.length+1) (cfg .restore none [] bits.reverse x.length w.length) = _
  rw [hr']

example : (runSteps machine.step 5 (Turing.initList machine (BitstringEncoding.bitEncode (([] : List Bool),([] : List Bool))))).map
    (fun c => (c.stk .xCount,c.stk .wCount)) = some ([],[]) := by
  change (Option.map (fun c => (c.stk .xCount,c.stk .wCount)) (runSteps machine.step 5
    (Turing.initList machine (BitstringEncoding.bitEncode (([] : List Bool),([] : List Bool))))) :
      Option (List Bool × List Bool)) = some ([],[])
  decide

example : (runSteps machine.step 35 (Turing.initList machine (BitstringEncoding.bitEncode ([true,false],[false])))).map
    (fun c => (c.stk .xCount,c.stk .wCount,c.stk .input)) =
      some (List.replicate 2 true,List.replicate 1 true,BitstringEncoding.bitEncode ([true,false],[false])) := by
  change (Option.map (fun c => (c.stk .xCount,c.stk .wCount,c.stk .input)) (runSteps machine.step 35
    (Turing.initList machine (BitstringEncoding.bitEncode ([true,false],[false])))) :
      Option (List Bool × List Bool × List Bool)) = _
  decide

end Shared.ComplexityBridge.TM2PairLengths
