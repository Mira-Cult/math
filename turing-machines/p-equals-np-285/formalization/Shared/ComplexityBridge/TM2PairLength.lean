import Shared.ComplexityBridge.TM2UnaryProductPhase
import Shared.ComplexityBridge.Encodings

namespace Shared.ComplexityBridge.TM2PairLength
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program

inductive Stack where
  | input | scratch | ticks
  deriving DecidableEq
inductive Label where
  | start | x0 | x1 | x2 | x3 | x4 | x5 | w0 | w1 | w2 | restore | done
  deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.input,.scratch,.ticks] (by intro s; cases s <;> simp)
instance : Fintype Label := Fintype.ofList
  [.start,.x0,.x1,.x2,.x3,.x4,.x5,.w0,.w1,.w2,.restore,.done] (by intro l; cases l <;> simp)

/-- Consume and save one bit; optionally add one unary count tick. A short
malformed input falls through to restore, so every table row is total. -/
def scan (next : Label) (count : Bool) : Stmt (fun _ : Stack => Bool) Label (Option Bool) :=
  .pop .input (fun _ h => h)
    (.branch Option.isSome
      (.push .scratch (fun v => v.getD false)
        (if count then .push .ticks (fun _ => true) (.goto (fun _ => next))
         else .goto (fun _ => next)))
      (.goto (fun _ => .restore)))

def program : Label → Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .start => .push .ticks (fun _ => true) (.push .ticks (fun _ => true) (.goto (fun _ => .x0)))
  | .x0 => .pop .input (fun _ h => h)
      (.branch Option.isSome
        (.push .scratch (fun v => v.getD false)
          (.branch (fun v => v == some false) (.goto (fun _ => .w0)) (.goto (fun _ => .x1))))
        (.goto (fun _ => .restore)))
  | .x1 => scan .x2 false
  | .x2 => scan .x3 false
  | .x3 => scan .x4 false
  | .x4 => scan .x5 false
  | .x5 => scan .x0 true
  | .w0 => scan .w1 false
  | .w1 => scan .w2 false
  | .w2 => scan .w0 true
  | .restore => .pop .scratch (fun _ h => h)
      (.branch Option.isSome
        (.push .input (fun v => v.getD false) (.goto (fun _ => .restore)))
        (.goto (fun _ => .done)))
  | .done => .goto (fun _ => .done)

def machine : Turing.FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .ticks
  Γ := fun _ => Bool
  Λ := Label
  main := .start
  σ := Option Bool
  initialState := none
  m := program

def stackVals (input scratch : List Bool) (n : Nat) : Stack → List Bool
  | .input => input
  | .scratch => scratch
  | .ticks => List.replicate n true

def cfg (l : Label) (v : Option Bool) (input scratch : List Bool) (n : Nat) : machine.Cfg :=
  ⟨some l,v,stackVals input scratch n⟩

theorem start_step (input scratch : List Bool) (n : Nat) (v : Option Bool) :
    machine.step (cfg .start v input scratch n) = some (cfg .x0 v input scratch (n+2)) := by
  change some (Cfg.mk (some Label.x0) v
    (Function.update (Function.update (stackVals input scratch n) .ticks (true::List.replicate n true))
      .ticks (true::true::List.replicate n true))) = some (Cfg.mk (some Label.x0) v (stackVals input scratch (n+2)))
  congr 1; congr 1; funext k; cases k <;> simp [stackVals, Function.update, List.replicate_succ]

theorem header_step (v : Option Bool) (b : Bool) (input scratch : List Bool) (n : Nat) :
    machine.step (cfg .x0 v (b::input) scratch n) =
      some (cfg (if b then .x1 else .w0) (some b) input (b::scratch) n) := by
  cases b <;>
    change some (Cfg.mk (some _) _ (Function.update (Function.update (stackVals (_::_) scratch n) .input input)
      .scratch (_::scratch))) = some (Cfg.mk (some _) _ (stackVals input (_::scratch) n)) <;>
    congr 1 <;> congr 1 <;> funext k <;> cases k <;> simp [stackVals,Function.update] <;> rfl

theorem scan_stepAux (next : Label) (count : Bool) (v : Option Bool) (b : Bool)
    (input scratch : List Bool) (n : Nat) :
    stepAux (scan next count) v (stackVals (b::input) scratch n) =
      cfg next (some b) input (b::scratch) (n + if count then 1 else 0) := by
  cases count <;>
    change Cfg.mk (some next) (some b) _ = Cfg.mk (some next) (some b) (stackVals input (b::scratch) _) <;>
    congr 1 <;> funext k <;> cases k <;> simp [stackVals,Function.update,List.replicate_succ]

theorem scan_nil (l : Label) (next : Label) (count : Bool) (v : Option Bool) (scratch : List Bool) (n : Nat)
    (h : program l = scan next count) :
    machine.step (cfg l v [] scratch n) = some (cfg .restore none [] scratch n) := by
  change some (stepAux (program l) v (stackVals [] scratch n)) = _
  rw [h]
  change some (Cfg.mk (some Label.restore) none (Function.update (stackVals [] scratch n) .input [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_cons (v : Option Bool) (b : Bool) (input scratch : List Bool) (n : Nat) :
    machine.step (cfg .restore v input (b::scratch) n) = some (cfg .restore (some b) (b::input) scratch n) := by
  change some (Cfg.mk (some Label.restore) (some b)
    (Function.update (Function.update (stackVals input (b::scratch) n) .scratch scratch) .input (b::input))) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restore_nil (v : Option Bool) (input : List Bool) (n : Nat) :
    machine.step (cfg .restore v input [] n) = some (cfg .done none input [] n) := by
  change some (Cfg.mk (some Label.done) none (Function.update (stackVals input [] n) .scratch [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem scan_cons (l next : Label) (count : Bool) (v : Option Bool) (b : Bool)
    (input scratch : List Bool) (n : Nat) (h : program l = scan next count) :
    machine.step (cfg l v (b::input) scratch n) =
      some (cfg next (some b) input (b::scratch) (n + if count then 1 else 0)) := by
  change some (stepAux (program l) v (stackVals (b::input) scratch n)) = _
  rw [h, scan_stepAux]
  rfl

theorem x1_cons (v : Option Bool) (b : Bool) (input scratch : List Bool) (n : Nat) :
    machine.step (cfg .x1 v (b::input) scratch n) =
      some (cfg .x2 (some b) input (b::scratch) (n+0)) := by
  exact scan_cons .x1 .x2 false v b input scratch n rfl

theorem x2_cons (v : Option Bool) (b : Bool) (input scratch : List Bool) (n : Nat) :
    machine.step (cfg .x2 v (b::input) scratch n) =
      some (cfg .x3 (some b) input (b::scratch) (n+0)) := by
  exact scan_cons .x2 .x3 false v b input scratch n rfl

theorem x3_cons (v : Option Bool) (b : Bool) (input scratch : List Bool) (n : Nat) :
    machine.step (cfg .x3 v (b::input) scratch n) =
      some (cfg .x4 (some b) input (b::scratch) (n+0)) := by
  exact scan_cons .x3 .x4 false v b input scratch n rfl

theorem x4_cons (v : Option Bool) (b : Bool) (input scratch : List Bool) (n : Nat) :
    machine.step (cfg .x4 v (b::input) scratch n) =
      some (cfg .x5 (some b) input (b::scratch) (n+0)) := by
  exact scan_cons .x4 .x5 false v b input scratch n rfl

theorem x5_cons (v : Option Bool) (b : Bool) (input scratch : List Bool) (n : Nat) :
    machine.step (cfg .x5 v (b::input) scratch n) =
      some (cfg .x0 (some b) input (b::scratch) (n+1)) := by
  exact scan_cons .x5 .x0 true v b input scratch n rfl

theorem w0_cons (v : Option Bool) (b : Bool) (input scratch : List Bool) (n : Nat) :
    machine.step (cfg .w0 v (b::input) scratch n) =
      some (cfg .w1 (some b) input (b::scratch) (n+0)) := by
  exact scan_cons .w0 .w1 false v b input scratch n rfl

theorem w1_cons (v : Option Bool) (b : Bool) (input scratch : List Bool) (n : Nat) :
    machine.step (cfg .w1 v (b::input) scratch n) =
      some (cfg .w2 (some b) input (b::scratch) (n+0)) := by
  exact scan_cons .w1 .w2 false v b input scratch n rfl

theorem w2_cons (v : Option Bool) (b : Bool) (input scratch : List Bool) (n : Nat) :
    machine.step (cfg .w2 v (b::input) scratch n) =
      some (cfg .w0 (some b) input (b::scratch) (n+1)) := by
  exact scan_cons .w2 .w0 true v b input scratch n rfl

def xBlock (b : Bool) : List Bool := [true,true,true,b,true,false]
def wBlock (b : Bool) : List Bool := [true,b,false]
def xBits (x : List Bool) : List Bool := x.flatMap xBlock
def wBits (w : List Bool) : List Bool := w.flatMap wBlock

theorem pair_encoding (x w : List Bool) :
    BitstringEncoding.bitEncode (x,w) = xBits x ++ [false] ++ wBits w := by
  change BitstringEncoding.delimit (BitstringEncoding.bitEncode x) ++ BitstringEncoding.bitEncode w = _
  have hw : BitstringEncoding.bitEncode w = wBits w := by
    induction w with
    | nil => rfl
    | cons b w ih =>
      change [true,b,false] ++ BitstringEncoding.bitEncode w = _
      simp [wBits, wBlock, ih]
  rw [hw]
  have hx : BitstringEncoding.delimit (BitstringEncoding.bitEncode x) = xBits x ++ [false] := by
    induction x with
    | nil => rfl
    | cons b x ih =>
      change BitstringEncoding.delimit ([true,b,false] ++ BitstringEncoding.bitEncode x) = _
      simp only [List.cons_append, List.nil_append, BitstringEncoding.delimit]
      simp [xBits,xBlock, ih]
  rw [hx]

/-- One raw first-component bit occupies six encoded bits. -/
theorem xBlock_run (b : Bool) (input scratch : List Bool) (n : Nat) (v : Option Bool) :
    runSteps machine.step 6 (cfg .x0 v (xBlock b ++ input) scratch n) =
      some (cfg .x0 (some false) input ((xBlock b).reverse ++ scratch) (n+1)) := by
  simp only [xBlock, List.cons_append, List.nil_append, List.reverse_cons, List.reverse_nil,
    runSteps_front, Option.bind_some, header_step, if_pos,
    x1_cons, x2_cons, x3_cons, x4_cons, x5_cons, Nat.add_zero]
  rfl

/-- One raw second-component bit occupies three encoded bits. -/
theorem wBlock_run (b : Bool) (input scratch : List Bool) (n : Nat) (v : Option Bool) :
    runSteps machine.step 3 (cfg .w0 v (wBlock b ++ input) scratch n) =
      some (cfg .w0 (some false) input ((wBlock b).reverse ++ scratch) (n+1)) := by
  simp only [wBlock, List.cons_append, List.nil_append, List.reverse_cons, List.reverse_nil,
    runSteps_front, Option.bind_some, w0_cons, w1_cons, w2_cons, Nat.add_zero]
  rfl

theorem x_run (x : List Bool) (tail scratch : List Bool) (n : Nat) (v : Option Bool) :
    ∃ v', runSteps machine.step (6*x.length) (cfg .x0 v (xBits x ++ tail) scratch n) =
      some (cfg .x0 v' tail ((xBits x).reverse ++ scratch) (n+x.length)) := by
  induction x generalizing scratch n v with
  | nil => exact ⟨v, by simp [xBits,runSteps]⟩
  | cons b x ih =>
    obtain ⟨v', h⟩ := ih ((xBlock b).reverse ++ scratch) (n+1) (some false)
    refine ⟨v', ?_⟩
    simp only [List.length_cons, xBits, List.flatMap_cons, List.append_assoc]
    have hn : 6*(x.length+1) = 6+6*x.length := by omega
    rw [hn, runSteps_add, xBlock_run]
    simpa [xBits, List.reverse_append, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem w_run (w : List Bool) (tail scratch : List Bool) (n : Nat) (v : Option Bool) :
    ∃ v', runSteps machine.step (3*w.length) (cfg .w0 v (wBits w ++ tail) scratch n) =
      some (cfg .w0 v' tail ((wBits w).reverse ++ scratch) (n+w.length)) := by
  induction w generalizing scratch n v with
  | nil => exact ⟨v, by simp [wBits,runSteps]⟩
  | cons b w ih =>
    obtain ⟨v', h⟩ := ih ((wBlock b).reverse ++ scratch) (n+1) (some false)
    refine ⟨v', ?_⟩
    simp only [List.length_cons, wBits, List.flatMap_cons, List.append_assoc]
    have hn : 3*(w.length+1) = 3+3*w.length := by omega
    rw [hn, runSteps_add, wBlock_run]
    simpa [wBits, List.reverse_append, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem restore_run (scratch input : List Bool) (n : Nat) (v : Option Bool) :
    ∃ v', runSteps machine.step scratch.length (cfg .restore v input scratch n) =
      some (cfg .restore v' (scratch.reverse ++ input) [] n) := by
  induction scratch generalizing input v with
  | nil => exact ⟨v, by simp [runSteps]⟩
  | cons b scratch ih =>
    obtain ⟨v', h⟩ := ih (b::input) (some b)
    refine ⟨v', ?_⟩
    rw [List.length_cons, runSteps_front, restore_cons]
    simpa [List.reverse_cons, List.append_assoc] using h

theorem initial_eq (input : List Bool) :
    Turing.initList machine input = cfg .start none input [] 0 := by
  change Cfg.mk (some Label.start) none _ = Cfg.mk (some Label.start) none (stackVals input [] 0)
  congr 1
  funext s
  cases s <;> simp [machine,stackVals] <;> rfl

/-- From the canonical pair input, count the raw bits plus two, preserve the
entire encoded input in order, and charge every scan and restore block. -/
theorem load_pair_correct (x w : List Bool) :
    runSteps machine.step (2*(BitstringEncoding.bitEncode (x,w)).length+3)
      (Turing.initList machine (BitstringEncoding.bitEncode (x,w))) =
    some (cfg .done none (BitstringEncoding.bitEncode (x,w)) [] (x.length+w.length+2)) := by
  let bits := BitstringEncoding.bitEncode (x,w)
  have hbits : bits = xBits x ++ false::wBits w := by simpa [bits] using pair_encoding x w
  obtain ⟨v, hx⟩ := x_run x (false::wBits w) [] 2 none
  simp only [List.append_nil] at hx
  have hx' : runSteps machine.step (6*x.length+1) (cfg .x0 none bits [] 2) =
      some (cfg .w0 (some false) (wBits w) (false::(xBits x).reverse) (2+x.length)) := by
    rw [hbits, runSteps_add, hx]
    change machine.step (cfg .x0 v (false::wBits w) (xBits x).reverse (2+x.length)) = _
    exact header_step v false (wBits w) (xBits x).reverse (2+x.length)
  obtain ⟨z, hw⟩ := w_run w [] (false::(xBits x).reverse) (2+x.length) (some false)
  simp only [List.append_nil] at hw
  have hw' : runSteps machine.step (3*w.length+1)
      (cfg .w0 (some false) (wBits w) (false::(xBits x).reverse) (2+x.length)) =
      some (cfg .restore none [] ((wBits w).reverse ++ false::(xBits x).reverse) (2+x.length+w.length)) := by
    rw [runSteps_add, hw]
    change machine.step (cfg .w0 z [] ((wBits w).reverse ++ false::(xBits x).reverse) (2+x.length+w.length)) = _
    exact scan_nil .w0 .w1 false z _ _ rfl
  have hreverse : (wBits w).reverse ++ false::(xBits x).reverse = bits.reverse := by
    rw [hbits]
    simp [List.reverse_append, List.append_assoc]
  rw [hreverse] at hw'
  obtain ⟨r, hr⟩ := restore_run bits.reverse [] (2+x.length+w.length) none
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at hr
  have hr' : runSteps machine.step (bits.length+1) (cfg .restore none [] bits.reverse (2+x.length+w.length)) =
      some (cfg .done none bits [] (2+x.length+w.length)) := by
    rw [runSteps_add, hr]
    change machine.step (cfg .restore r bits [] (2+x.length+w.length)) = _
    exact restore_nil r bits _
  have hlength : bits.length = 6*x.length+1+3*w.length := by
    exact Shared.ComplexityBridge.bitstring_pair_encoded_length x w
  have hcost : 2*bits.length+3 = ((6*x.length+1)+((3*w.length+1)+(bits.length+1)))+1 := by omega
  rw [initial_eq, hcost, runSteps_front, start_step]
  change runSteps machine.step ((6*x.length+1)+((3*w.length+1)+(bits.length+1))) (cfg .x0 none bits [] 2) = _
  rw [runSteps_add, hx']
  change runSteps machine.step ((3*w.length+1)+(bits.length+1))
    (cfg .w0 (some false) (wBits w) (false::(xBits x).reverse) (2+x.length)) = _
  rw [runSteps_add, hw']
  change runSteps machine.step (bits.length+1) (cfg .restore none [] bits.reverse (2+x.length+w.length)) = _
  rw [hr']
  congr 1
  simp [bits, Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

example : (runSteps machine.step 5 (Turing.initList machine (BitstringEncoding.bitEncode (([] : List Bool), ([] : List Bool))))).map
    (fun c => c.stk .ticks) = some (List.replicate 2 true) := by
  change (Option.map (fun c => c.stk .ticks) (runSteps machine.step 5
    (Turing.initList machine (BitstringEncoding.bitEncode (([] : List Bool), ([] : List Bool))))) : Option (List Bool)) = _
  decide

example : (runSteps machine.step 23 (Turing.initList machine (BitstringEncoding.bitEncode ([true], [false])))).map
    (fun c => (c.stk .input, c.stk .ticks)) = some (BitstringEncoding.bitEncode ([true], [false]), List.replicate 4 true) := by
  change (Option.map (fun c => (c.stk .input, c.stk .ticks)) (runSteps machine.step 23
    (Turing.initList machine (BitstringEncoding.bitEncode ([true], [false])))) : Option (List Bool × List Bool)) = _
  decide

end Shared.ComplexityBridge.TM2PairLength
