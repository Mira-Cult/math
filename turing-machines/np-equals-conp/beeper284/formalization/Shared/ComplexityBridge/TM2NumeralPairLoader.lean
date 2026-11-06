import Shared.ComplexityBridge.TM2NumeralCompare
import Shared.ComplexityBridge.TM2PairLength

set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2NumeralPairLoader
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
open Shared.ComplexityBridge.TM2PairLength (xBlock wBlock xBits wBits pair_encoding)
inductive Stack where | input | xScratch | yScratch | left | right
  deriving DecidableEq
inductive Label where | x0 | x1 | x2 | x3 | x4 | x5 | y0 | y1 | y2 | restoreX | restoreY | done
  deriving DecidableEq
instance : Fintype Stack := Fintype.ofList [.input,.xScratch,.yScratch,.left,.right] (by intro s; cases s <;> simp)
instance : Fintype Label := Fintype.ofList [.x0,.x1,.x2,.x3,.x4,.x5,.y0,.y1,.y2,.restoreX,.restoreY,.done] (by intro l; cases l <;> simp)

def scan (next : Label) (save : Option Stack) : Stmt (fun _ : Stack => Bool) Label (Option Bool) :=
  .pop .input (fun _ h => h)
    (.branch Option.isSome
      (match save with
       | none => .goto (fun _ => next)
       | some j => .push j (fun v => v.getD false) (.goto (fun _ => next)))
      (.goto (fun _ => .restoreX)))

def program : Label → Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .x0 => .pop .input (fun _ h => h)
      (.branch Option.isSome
        (.branch (fun v => v == some false) (.goto (fun _ => .y0)) (.goto (fun _ => .x1)))
        (.goto (fun _ => .restoreX)))
  | .x1 => scan .x2 none
  | .x2 => scan .x3 none
  | .x3 => scan .x4 (some .xScratch)
  | .x4 => scan .x5 none
  | .x5 => scan .x0 none
  | .y0 => scan .y1 none
  | .y1 => scan .y2 (some .yScratch)
  | .y2 => scan .y0 none
  | .restoreX => .pop .xScratch (fun _ h => h)
      (.branch Option.isSome (.push .left (fun v => v.getD false) (.goto (fun _ => .restoreX)))
        (.goto (fun _ => .restoreY)))
  | .restoreY => .pop .yScratch (fun _ h => h)
      (.branch Option.isSome (.push .right (fun v => v.getD false) (.goto (fun _ => .restoreY)))
        (.goto (fun _ => .done)))
  | .done => .goto (fun _ => .done)

def machine : Turing.FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .left
  Γ := fun _ => Bool
  Λ := Label
  main := .x0
  σ := Option Bool
  initialState := none
  m := program

def stackVals (input xScratch yScratch left right : List Bool) : Stack → List Bool
  | .input => input | .xScratch => xScratch | .yScratch => yScratch | .left => left | .right => right

def cfg (l : Label) (v : Option Bool) (input xScratch yScratch left right : List Bool) : machine.Cfg :=
  ⟨some l,v,stackVals input xScratch yScratch left right⟩

theorem header_step (v : Option Bool) (b : Bool) (input a c x y : List Bool) :
    machine.step (cfg .x0 v (b::input) a c x y) =
      some (cfg (if b then .x1 else .y0) (some b) input a c x y) := by
  cases b <;>
    change some (Cfg.mk _ _ (Function.update (stackVals (_::input) a c x y) .input input)) = _ <;>
    congr 1 <;> congr 1 <;> funext k <;> cases k <;> simp [stackVals,Function.update]

def saveStacks (save : Option Stack) (b : Bool) (S : Stack → List Bool) : Stack → List Bool :=
  match save with | none => S | some j => Function.update S j (b::S j)

theorem scan_aux (next : Label) (save : Option Stack) (v : Option Bool) (b : Bool)
    (input a c x y : List Bool) :
    stepAux (scan next save) v (stackVals (b::input) a c x y) =
      Cfg.mk (some next) (some b) (saveStacks save b (stackVals input a c x y)) := by
  cases save with
  | none =>
    change Cfg.mk (some next) (some b) (Function.update (stackVals (b::input) a c x y) .input input) = _
    congr 1; funext k; cases k <;> simp [stackVals,Function.update,saveStacks]
  | some j =>
    change Cfg.mk (some next) (some b)
      (Function.update (Function.update (stackVals (b::input) a c x y) .input input) j
        (b::(Function.update (stackVals (b::input) a c x y) .input input) j)) = _
    have hinput : Function.update (stackVals (b::input) a c x y) .input input = stackVals input a c x y := by
      funext k; cases k <;> simp [stackVals,Function.update]
    rw [hinput]
    rfl

theorem scan_cons (l next : Label) (save : Option Stack) (v : Option Bool) (b : Bool)
    (input a c x y : List Bool) (h : program l = scan next save) :
    machine.step (cfg l v (b::input) a c x y) =
      some (Cfg.mk (some next) (some b) (saveStacks save b (stackVals input a c x y))) := by
  change some (stepAux (program l) v (stackVals (b::input) a c x y)) = _
  rw [h,scan_aux]

theorem scan_nil (l next : Label) (save : Option Stack) (v : Option Bool) (a c x y : List Bool)
    (h : program l = scan next save) :
    machine.step (cfg l v [] a c x y) = some (cfg .restoreX none [] a c x y) := by
  change some (stepAux (program l) v (stackVals [] a c x y)) = _
  rw [h]
  change some (Cfg.mk (some Label.restoreX) none (Function.update (stackVals [] a c x y) .input [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem x1 (v : Option Bool) (b : Bool) (input a c x y : List Bool) :
    machine.step (cfg .x1 v (b::input) a c x y) = some (cfg .x2 (some b) input a c x y) := scan_cons .x1 .x2 none v b input a c x y rfl

theorem x2 (v : Option Bool) (b : Bool) (input a c x y : List Bool) :
    machine.step (cfg .x2 v (b::input) a c x y) = some (cfg .x3 (some b) input a c x y) := scan_cons .x2 .x3 none v b input a c x y rfl

theorem x3 (v : Option Bool) (b : Bool) (input a c x y : List Bool) :
    machine.step (cfg .x3 v (b::input) a c x y) = some (cfg .x4 (some b) input (b::a) c x y) := by
  have he : Function.update (stackVals input a c x y) .xScratch (b::a) = stackVals input (b::a) c x y := by
    funext k; cases k <;> simp [stackVals,Function.update]
  simpa [cfg,saveStacks,stackVals,he] using scan_cons .x3 .x4 (some .xScratch) v b input a c x y rfl

theorem x4 (v : Option Bool) (b : Bool) (input a c x y : List Bool) :
    machine.step (cfg .x4 v (b::input) a c x y) = some (cfg .x5 (some b) input a c x y) := scan_cons .x4 .x5 none v b input a c x y rfl

theorem x5 (v : Option Bool) (b : Bool) (input a c x y : List Bool) :
    machine.step (cfg .x5 v (b::input) a c x y) = some (cfg .x0 (some b) input a c x y) := scan_cons .x5 .x0 none v b input a c x y rfl

theorem y0 (v : Option Bool) (b : Bool) (input a c x y : List Bool) :
    machine.step (cfg .y0 v (b::input) a c x y) = some (cfg .y1 (some b) input a c x y) := scan_cons .y0 .y1 none v b input a c x y rfl

theorem y1 (v : Option Bool) (b : Bool) (input a c x y : List Bool) :
    machine.step (cfg .y1 v (b::input) a c x y) = some (cfg .y2 (some b) input a (b::c) x y) := by
  have he : Function.update (stackVals input a c x y) .yScratch (b::c) = stackVals input a (b::c) x y := by
    funext k; cases k <;> simp [stackVals,Function.update]
  simpa [cfg,saveStacks,stackVals,he] using scan_cons .y1 .y2 (some .yScratch) v b input a c x y rfl

theorem y2 (v : Option Bool) (b : Bool) (input a c x y : List Bool) :
    machine.step (cfg .y2 v (b::input) a c x y) = some (cfg .y0 (some b) input a c x y) := scan_cons .y2 .y0 none v b input a c x y rfl

theorem restoreX_cons (v : Option Bool) (b : Bool) (input a c x y : List Bool) :
    machine.step (cfg .restoreX v input (b::a) c x y) = some (cfg .restoreX (some b) input a c (b::x) y) := by
  change some (Cfg.mk (some Label.restoreX) (some b)
    (Function.update (Function.update (stackVals input (b::a) c x y) .xScratch a) .left (b::x))) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restoreX_nil (v : Option Bool) (input c x y : List Bool) :
    machine.step (cfg .restoreX v input [] c x y) = some (cfg .restoreY none input [] c x y) := by
  change some (Cfg.mk (some Label.restoreY) none (Function.update (stackVals input [] c x y) .xScratch [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restoreY_cons (v : Option Bool) (b : Bool) (input c x y : List Bool) :
    machine.step (cfg .restoreY v input [] (b::c) x y) = some (cfg .restoreY (some b) input [] c x (b::y)) := by
  change some (Cfg.mk (some Label.restoreY) (some b)
    (Function.update (Function.update (stackVals input [] (b::c) x y) .yScratch c) .right (b::y))) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem restoreY_nil (v : Option Bool) (input x y : List Bool) :
    machine.step (cfg .restoreY v input [] [] x y) = some (cfg .done none input [] [] x y) := by
  change some (Cfg.mk (some Label.done) none (Function.update (stackVals input [] [] x y) .yScratch [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]


theorem xBlock_run (b : Bool) (input a c x y : List Bool) (v : Option Bool) :
    runSteps machine.step 6 (cfg .x0 v (xBlock b ++ input) a c x y) =
      some (cfg .x0 (some false) input (b::a) c x y) := by
  simp only [xBlock,List.cons_append,List.nil_append,runSteps_front,Option.bind_some,
    header_step,if_pos,x1,x2,x3,x4,x5]
  rfl

theorem yBlock_run (b : Bool) (input a c x y : List Bool) (v : Option Bool) :
    runSteps machine.step 3 (cfg .y0 v (wBlock b ++ input) a c x y) =
      some (cfg .y0 (some false) input a (b::c) x y) := by
  simp only [wBlock,List.cons_append,List.nil_append,runSteps_front,Option.bind_some,y0,y1,y2]
  rfl

theorem x_run (xs tail a c x y : List Bool) (v : Option Bool) :
    ∃ v', runSteps machine.step (6*xs.length) (cfg .x0 v (xBits xs ++ tail) a c x y) =
      some (cfg .x0 v' tail (xs.reverse ++ a) c x y) := by
  induction xs generalizing a v with
  | nil => exact ⟨v, by simp [xBits,runSteps]⟩
  | cons b xs ih =>
    obtain ⟨v',h⟩ := ih (b::a) (some false)
    refine ⟨v',?_⟩
    simp only [List.length_cons,xBits,List.flatMap_cons,List.append_assoc]
    have hn : 6*(xs.length+1) = 6+6*xs.length := by omega
    rw [hn,runSteps_add,xBlock_run]
    simpa [xBits,List.reverse_cons,List.append_assoc] using h

theorem y_run (ys tail a c x y : List Bool) (v : Option Bool) :
    ∃ v', runSteps machine.step (3*ys.length) (cfg .y0 v (wBits ys ++ tail) a c x y) =
      some (cfg .y0 v' tail a (ys.reverse ++ c) x y) := by
  induction ys generalizing c v with
  | nil => exact ⟨v, by simp [wBits,runSteps]⟩
  | cons b ys ih =>
    obtain ⟨v',h⟩ := ih (b::c) (some false)
    refine ⟨v',?_⟩
    simp only [List.length_cons,wBits,List.flatMap_cons,List.append_assoc]
    have hn : 3*(ys.length+1) = 3+3*ys.length := by omega
    rw [hn,runSteps_add,yBlock_run]
    simpa [wBits,List.reverse_cons,List.append_assoc] using h

theorem restoreX_run (a input c x y : List Bool) (v : Option Bool) :
    ∃ v', runSteps machine.step a.length (cfg .restoreX v input a c x y) =
      some (cfg .restoreX v' input [] c (a.reverse ++ x) y) := by
  induction a generalizing x v with
  | nil => exact ⟨v, by simp [runSteps]⟩
  | cons b a ih =>
    obtain ⟨v',h⟩ := ih (b::x) (some b)
    refine ⟨v',?_⟩
    rw [List.length_cons,runSteps_front,restoreX_cons]
    simpa [List.reverse_cons,List.append_assoc] using h

theorem restoreY_run (c input x y : List Bool) (v : Option Bool) :
    ∃ v', runSteps machine.step c.length (cfg .restoreY v input [] c x y) =
      some (cfg .restoreY v' input [] [] x (c.reverse ++ y)) := by
  induction c generalizing y v with
  | nil => exact ⟨v, by simp [runSteps]⟩
  | cons b c ih =>
    obtain ⟨v',h⟩ := ih (b::y) (some b)
    refine ⟨v',?_⟩
    rw [List.length_cons,runSteps_front,restoreY_cons]
    simpa [List.reverse_cons,List.append_assoc] using h

theorem initial_eq (input : List Bool) :
    Turing.initList machine input = cfg .x0 none input [] [] [] [] := by
  change Cfg.mk (some Label.x0) none _ = Cfg.mk (some Label.x0) none (stackVals input [] [] [] [])
  congr 1
  funext s
  cases s <;> simp [machine,stackVals] <;> rfl

theorem load_pair (x y : List Bool) :
    runSteps machine.step (7*x.length+4*y.length+4)
      (Turing.initList machine (BitstringEncoding.bitEncode (x,y))) =
      some (cfg .done none [] [] [] x y) := by
  let bits := BitstringEncoding.bitEncode (x,y)
  have hbits : bits = xBits x ++ false::wBits y := by simpa [bits] using pair_encoding x y
  obtain ⟨v,hx⟩ := x_run x (false::wBits y) [] [] [] [] none
  simp only [List.append_nil] at hx
  have hx' : runSteps machine.step (6*x.length+1) (cfg .x0 none bits [] [] [] []) =
      some (cfg .y0 (some false) (wBits y) x.reverse [] [] []) := by
    rw [hbits,runSteps_add,hx]
    change machine.step (cfg .x0 v (false::wBits y) x.reverse [] [] []) = _
    exact header_step v false (wBits y) x.reverse [] [] []
  obtain ⟨w,hy⟩ := y_run y [] x.reverse [] [] [] (some false)
  simp only [List.append_nil] at hy
  have hy' : runSteps machine.step (3*y.length+1) (cfg .y0 (some false) (wBits y) x.reverse [] [] []) =
      some (cfg .restoreX none [] x.reverse y.reverse [] []) := by
    rw [runSteps_add,hy]
    change machine.step (cfg .y0 w [] x.reverse y.reverse [] []) = _
    exact scan_nil .y0 .y1 none w _ _ _ _ rfl
  obtain ⟨u,hrx⟩ := restoreX_run x.reverse [] y.reverse [] [] none
  simp only [List.reverse_reverse,List.length_reverse,List.append_nil] at hrx
  have hrx' : runSteps machine.step (x.length+1) (cfg .restoreX none [] x.reverse y.reverse [] []) =
      some (cfg .restoreY none [] [] y.reverse x []) := by
    rw [runSteps_add,hrx]
    change machine.step (cfg .restoreX u [] [] y.reverse x []) = _
    exact restoreX_nil u [] y.reverse x []
  obtain ⟨z,hry⟩ := restoreY_run y.reverse [] x [] none
  simp only [List.reverse_reverse,List.length_reverse,List.append_nil] at hry
  have hry' : runSteps machine.step (y.length+1) (cfg .restoreY none [] [] y.reverse x []) =
      some (cfg .done none [] [] [] x y) := by
    rw [runSteps_add,hry]
    change machine.step (cfg .restoreY z [] [] [] x y) = _
    exact restoreY_nil z [] x y
  have hcost : 7*x.length+4*y.length+4 = (6*x.length+1)+((3*y.length+1)+((x.length+1)+(y.length+1))) := by omega
  rw [initial_eq,hcost,runSteps_add,hx']
  change runSteps machine.step ((3*y.length+1)+((x.length+1)+(y.length+1))) _ = _
  rw [runSteps_add,hy']
  change runSteps machine.step ((x.length+1)+(y.length+1)) _ = _
  rw [runSteps_add,hrx']
  exact hry'

/-- The exact loader cost is linear in the length of the actual pair encoding. -/
theorem load_pair_cost (x y : List Bool) :
    7*x.length+4*y.length+4 ≤ 2*(BitstringEncoding.bitEncode (x,y)).length+2 := by
  rw [Shared.ComplexityBridge.bitstring_pair_encoded_length]
  omega

namespace Fixtures
example : runSteps machine.step 4
    (Turing.initList machine (BitstringEncoding.bitEncode (([],[]) : List Bool × List Bool))) =
    some (cfg .done none [] [] [] [] []) := by simpa using load_pair [] []
example : runSteps machine.step 15
    (Turing.initList machine (BitstringEncoding.bitEncode ([false],[true]))) =
    some (cfg .done none [] [] [] [false] [true]) := by simpa using load_pair [false] [true]
end Fixtures

end Shared.ComplexityBridge.TM2NumeralPairLoader
