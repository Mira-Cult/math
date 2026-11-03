import Shared.ComplexityBridge.TM2UnaryPolynomial
import Shared.ComplexityBridge.TM2UnaryCutoff

set_option linter.unusedSimpArgs false

namespace Shared.ComplexityBridge.TM2CutoffGate
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
abbrev Terms := Shared.Codes.NumericPolynomial.Terms
abbrev Parse := Shared.ComplexityBridge.TM2PairLengths.machine
abbrev Poly := Shared.ComplexityBridge.TM2UnaryPolynomial.machine
abbrev Compare := Shared.ComplexityBridge.TM2UnaryCutoff.machine
abbrev ParseStack := Shared.ComplexityBridge.TM2PairLengths.Stack
abbrev PolyKey := Shared.ComplexityBridge.TM2UnaryPolynomial.Key
abbrev CompareStack := Shared.ComplexityBridge.TM2UnaryCutoff.Stack
abbrev Key := Bool ⊕ (Unit ⊕ PolyKey)
abbrev Label (ts : Terms) := Shared.ComplexityBridge.TM2PairLength.Label ⊕
  (Shared.ComplexityBridge.TM2UnaryPolynomial.Label ts ⊕ Shared.ComplexityBridge.TM2UnaryCutoff.Label)
abbrev State := Option Bool ⊕ Bool

def parseKey : ParseStack → Key
  | .input => .inl false
  | .scratch => .inl true
  | .xCount => .inr (.inr (.inr .b))
  | .wCount => .inr (.inl ())

def parseStacks (S : ParseStack → List Bool) (other : PolyKey → List Bool) : Key → List Bool
  | .inl false => S .input
  | .inl true => S .scratch
  | .inr (.inl _) => S .wCount
  | .inr (.inr (.inr .b)) => S .xCount
  | .inr (.inr j) => other j

@[simp] theorem parseStacks_apply (S : ParseStack → List Bool) (other : PolyKey → List Bool) (j : ParseStack) :
    parseStacks S other (parseKey j) = S j := by cases j <;> rfl

theorem parse_update (S : ParseStack → List Bool) (other : PolyKey → List Bool) (j : ParseStack) (xs : List Bool) :
    parseStacks (Function.update S j xs) other = Function.update (parseStacks S other) (parseKey j) xs := by
  funext q
  cases j <;> cases q with
  | inl b => cases b <;> simp [parseStacks,parseKey,Function.update]
  | inr q =>
    cases q with
    | inl u => cases u; simp [parseStacks,parseKey,Function.update]
    | inr q => cases q with
      | inl b => cases b <;> simp [parseStacks,parseKey,Function.update]
      | inr a => cases a <;> simp [parseStacks,parseKey,Function.update]

def polyStacks (bits scratch witness : List Bool) (S : PolyKey → List Bool) : Key → List Bool
  | .inl false => bits
  | .inl true => scratch
  | .inr (.inl _) => witness
  | .inr (.inr j) => S j

theorem poly_update (bits scratch witness : List Bool) (S : PolyKey → List Bool) (j : PolyKey) (xs : List Bool) :
    polyStacks bits scratch witness (Function.update S j xs) = Function.update (polyStacks bits scratch witness S) (.inr (.inr j)) xs := by
  funext q
  cases q with
  | inl b => cases b <;> simp [polyStacks,Function.update]
  | inr q => cases q with
    | inl u => cases u; simp [polyStacks,Function.update]
    | inr a =>
      by_cases h : a = j
      · subst a; simp [polyStacks,Function.update]
      · have hh : (Sum.inr (Sum.inr a) : Key) ≠ .inr (.inr j) := by simpa using h
        simp [polyStacks,Function.update_of_ne h,Function.update_of_ne hh]

def compareKey : CompareStack → Key
  | .witness => .inr (.inl ())
  | .cutoff => .inr (.inr (.inl true))

def compareStacks (S : CompareStack → List Bool) (other : Key → List Bool) : Key → List Bool
  | .inr (.inl _) => S .witness
  | .inr (.inr (.inl true)) => S .cutoff
  | q => other q

@[simp] theorem compareStacks_apply (S : CompareStack → List Bool) (other : Key → List Bool) (j : CompareStack) :
    compareStacks S other (compareKey j) = S j := by cases j <;> rfl

theorem compare_update (S : CompareStack → List Bool) (other : Key → List Bool) (j : CompareStack) (xs : List Bool) :
    compareStacks (Function.update S j xs) other = Function.update (compareStacks S other) (compareKey j) xs := by
  funext q
  cases j <;> cases q with
  | inl b => cases b <;> simp [compareStacks,compareKey,Function.update]
  | inr q => cases q with
    | inl u => cases u; simp [compareStacks,compareKey,Function.update]
    | inr q => cases q with
      | inl b => cases b <;> simp [compareStacks,compareKey,Function.update]
      | inr a => cases a <;> simp [compareStacks,compareKey,Function.update]

def parseState : State → Option Bool | .inl v => v | .inr _ => none
def boolState : State → Bool | .inl _ => false | .inr v => v

def parseEmbed (ts : Terms) (other : PolyKey → List Bool) (q : Parse.Cfg) : Cfg (fun _ : Key => Bool) (Label ts) State :=
  ⟨q.l.map Sum.inl,.inl q.var,parseStacks q.stk other⟩
def polyEmbed (ts : Terms) (bits scratch witness : List Bool) (q : (Poly ts).Cfg) : Cfg (fun _ : Key => Bool) (Label ts) State :=
  ⟨q.l.map (fun l => .inr (.inl l)),.inr q.var,polyStacks bits scratch witness q.stk⟩
def compareEmbed (ts : Terms) (other : Key → List Bool) (q : Compare.Cfg) : Cfg (fun _ : Key => Bool) (Label ts) State :=
  ⟨q.l.map (fun l => .inr (.inr l)),.inr q.var,compareStacks q.stk other⟩

def liftParse (ts : Terms) : Stmt (fun _ : ParseStack => Bool) Shared.ComplexityBridge.TM2PairLength.Label (Option Bool) →
    Stmt (fun _ : Key => Bool) (Label ts) State
  | .push j f q => .push (parseKey j) (fun v => f (parseState v)) (liftParse ts q)
  | .peek j f q => .peek (parseKey j) (fun v h => .inl (f (parseState v) h)) (liftParse ts q)
  | .pop j f q => .pop (parseKey j) (fun v h => .inl (f (parseState v) h)) (liftParse ts q)
  | .load f q => .load (fun v => .inl (f (parseState v))) (liftParse ts q)
  | .branch f q r => .branch (fun v => f (parseState v)) (liftParse ts q) (liftParse ts r)
  | .goto f => .goto (fun v => .inl (f (parseState v)))
  | .halt => .halt

def liftPoly (ts : Terms) : Stmt (fun _ : PolyKey => Bool) (Shared.ComplexityBridge.TM2UnaryPolynomial.Label ts) Bool →
    Stmt (fun _ : Key => Bool) (Label ts) State
  | .push j f q => .push (.inr (.inr j)) (fun v => f (boolState v)) (liftPoly ts q)
  | .peek j f q => .peek (.inr (.inr j)) (fun v h => .inr (f (boolState v) h)) (liftPoly ts q)
  | .pop j f q => .pop (.inr (.inr j)) (fun v h => .inr (f (boolState v) h)) (liftPoly ts q)
  | .load f q => .load (fun v => .inr (f (boolState v))) (liftPoly ts q)
  | .branch f q r => .branch (fun v => f (boolState v)) (liftPoly ts q) (liftPoly ts r)
  | .goto f => .goto (fun v => .inr (.inl (f (boolState v))))
  | .halt => .halt

def liftCompare (ts : Terms) : Stmt (fun _ : CompareStack => Bool) Shared.ComplexityBridge.TM2UnaryCutoff.Label Bool →
    Stmt (fun _ : Key => Bool) (Label ts) State
  | .push j f q => .push (compareKey j) (fun v => f (boolState v)) (liftCompare ts q)
  | .peek j f q => .peek (compareKey j) (fun v h => .inr (f (boolState v) h)) (liftCompare ts q)
  | .pop j f q => .pop (compareKey j) (fun v h => .inr (f (boolState v) h)) (liftCompare ts q)
  | .load f q => .load (fun v => .inr (f (boolState v))) (liftCompare ts q)
  | .branch f q r => .branch (fun v => f (boolState v)) (liftCompare ts q) (liftCompare ts r)
  | .goto f => .goto (fun v => .inr (.inr (f (boolState v))))
  | .halt => .halt

set_option backward.isDefEq.respectTransparency false in
theorem liftParse_aux (ts : Terms) (q : Stmt (fun _ : ParseStack => Bool) Shared.ComplexityBridge.TM2PairLength.Label (Option Bool))
    (v : Option Bool) (S : ParseStack → List Bool) (other : PolyKey → List Bool) :
    stepAux (liftParse ts q) (.inl v) (parseStacks S other) =
      parseEmbed ts other (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih (f v) S
  | push j f q ih =>
    simp only [liftParse,stepAux,parseState,parseStacks_apply]
    rw [← parse_update S other j (f v::S j)]
    exact ih v _
  | peek j f q ih =>
    simp only [liftParse,stepAux,parseState,parseStacks_apply]
    exact ih (f v (S j).head?) S
  | pop j f q ih =>
    simp only [liftParse,stepAux,parseState,parseStacks_apply]
    rw [← parse_update S other j (S j).tail]
    exact ih (f v (S j).head?) _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [liftParse,stepAux,parseState,h,ihq,ihr]

set_option backward.isDefEq.respectTransparency false in
theorem liftPoly_aux (ts : Terms) (q : Stmt (fun _ : PolyKey => Bool) (Shared.ComplexityBridge.TM2UnaryPolynomial.Label ts) Bool)
    (v : Bool) (S : PolyKey → List Bool) (bits scratch witness : List Bool) :
    stepAux (liftPoly ts q) (.inr v) (polyStacks bits scratch witness S) =
      polyEmbed ts bits scratch witness (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih (f v) S
  | push j f q ih =>
    simp only [liftPoly,stepAux,boolState,polyStacks]
    rw [← poly_update bits scratch witness S j (f v::S j)]
    exact ih v _
  | peek j f q ih => exact ih (f v (S j).head?) S
  | pop j f q ih =>
    simp only [liftPoly,stepAux,boolState,polyStacks]
    rw [← poly_update bits scratch witness S j (S j).tail]
    exact ih (f v (S j).head?) _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [liftPoly,stepAux,boolState,h,ihq,ihr]

set_option backward.isDefEq.respectTransparency false in
theorem liftCompare_aux (ts : Terms) (q : Stmt (fun _ : CompareStack => Bool) Shared.ComplexityBridge.TM2UnaryCutoff.Label Bool)
    (v : Bool) (S : CompareStack → List Bool) (other : Key → List Bool) :
    stepAux (liftCompare ts q) (.inr v) (compareStacks S other) =
      compareEmbed ts other (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih (f v) S
  | push j f q ih =>
    simp only [liftCompare,stepAux,boolState,compareStacks_apply]
    rw [← compare_update S other j (f v::S j)]
    exact ih v _
  | peek j f q ih =>
    simp only [liftCompare,stepAux,boolState,compareStacks_apply]
    exact ih (f v (S j).head?) S
  | pop j f q ih =>
    simp only [liftCompare,stepAux,boolState,compareStacks_apply]
    rw [← compare_update S other j (S j).tail]
    exact ih (f v (S j).head?) _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [liftCompare,stepAux,boolState,h,ihq,ihr]

def program (ts : Terms) : Label ts → Stmt (fun _ : Key => Bool) (Label ts) State
  | .inl .done => .push (.inr (.inr (.inr .a))) (fun _ => true)
      (.load (fun _ => .inr false) (.goto (fun _ => .inr (.inl (Shared.ComplexityBridge.TM2UnaryPolynomial.startLabel ts)))))
  | .inl l => liftParse ts (Shared.ComplexityBridge.TM2PairLengths.program l)
  | .inr (.inl l) => if l = Shared.ComplexityBridge.TM2UnaryPolynomial.doneLabel ts then
      .goto (fun _ => .inr (.inr .compare))
    else liftPoly ts (Shared.ComplexityBridge.TM2UnaryPolynomial.program ts l)
  | .inr (.inr l) => liftCompare ts (Shared.ComplexityBridge.TM2UnaryCutoff.program l)

def machine (ts : Terms) : Turing.FinTM2 where
  K := Key
  k₀ := .inl false
  k₁ := .inr (.inl ())
  Γ := fun _ => Bool
  Λ := Label ts
  main := .inl .start
  σ := State
  initialState := .inl none
  m := program ts

def parseTerminal (q : Parse.Cfg) : Prop := q.l = some .done
noncomputable instance : DecidablePred parseTerminal := fun _ => Classical.propDecidable _

theorem parse_stable (q : Parse.Cfg) (h : parseTerminal q) : Parse.step q = some q := by
  cases q with
  | mk l v S =>
    change l = some Shared.ComplexityBridge.TM2PairLength.Label.done at h
    subst l
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem parse_step (ts : Terms) (other : PolyKey → List Bool) (q : Parse.Cfg) (h : ¬ parseTerminal q) :
    (machine ts).step (parseEmbed ts other q) = (Parse.step q).map (parseEmbed ts other) := by
  cases q with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l =>
      cases l with
      | done => exact False.elim (h rfl)
      | start | x0 | x1 | x2 | x3 | x4 | x5 | w0 | w1 | w2 | restore =>
        change some (stepAux (liftParse ts (Shared.ComplexityBridge.TM2PairLengths.program _)) (.inl v) (parseStacks S other)) = _
        rw [liftParse_aux]
        rfl

set_option backward.isDefEq.respectTransparency false in
theorem poly_step (ts : Terms) (bits scratch witness : List Bool) (q : (Poly ts).Cfg)
    (h : ¬ Shared.ComplexityBridge.TM2UnaryPolynomial.doneTerminal ts q) :
    (machine ts).step (polyEmbed ts bits scratch witness q) = ((Poly ts).step q).map (polyEmbed ts bits scratch witness) := by
  cases q with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l =>
      have hl : l ≠ Shared.ComplexityBridge.TM2UnaryPolynomial.doneLabel ts := by intro he; apply h; exact congrArg some he
      change some (stepAux (program ts (.inr (.inl l))) (.inr v) (polyStacks bits scratch witness S)) = _
      simp only [program,if_neg hl]
      rw [liftPoly_aux]
      rfl

set_option backward.isDefEq.respectTransparency false in
theorem compare_step (ts : Terms) (other : Key → List Bool) (q : Compare.Cfg) :
    (machine ts).step (compareEmbed ts other q) = (Compare.step q).map (compareEmbed ts other) := by
  cases q with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l =>
      change some (stepAux (liftCompare ts (Shared.ComplexityBridge.TM2UnaryCutoff.program l)) (.inr v) (compareStacks S other)) = _
      rw [liftCompare_aux]
      rfl

set_option backward.isDefEq.respectTransparency false in
theorem compare_run (ts : Terms) (other : Key → List Bool) (q : Compare.Cfg) (n : Nat) :
    runSteps (machine ts).step n (compareEmbed ts other q) = (runSteps Compare.step n q).map (compareEmbed ts other) := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    rw [runSteps_front,runSteps_front,compare_step]
    cases h : Compare.step q with
    | none => rfl
    | some q' => exact ih q'

theorem initial_eq (ts : Terms) (bits : List Bool) :
    Turing.initList (machine ts) bits = parseEmbed ts (fun _ => []) (Turing.initList Parse bits) := by
  rw [Shared.ComplexityBridge.TM2PairLengths.initial_eq]
  change (Cfg.mk (some (Sum.inl Shared.ComplexityBridge.TM2PairLength.Label.start)) (.inl none) _ : (machine ts).Cfg) = _
  congr 1
  funext q
  cases q with
  | inl b => cases b <;> simp [machine,parseEmbed,parseStacks,Shared.ComplexityBridge.TM2PairLengths.cfg,
      Shared.ComplexityBridge.TM2PairLengths.stackVals,Turing.initList,Function.update] <;> rfl
  | inr q => cases q with
    | inl u => cases u; simp [machine,parseEmbed,parseStacks,Shared.ComplexityBridge.TM2PairLengths.cfg,
        Shared.ComplexityBridge.TM2PairLengths.stackVals,Turing.initList,Function.update]
    | inr q => cases q with
      | inl b => cases b <;> simp [machine,parseEmbed,parseStacks,Shared.ComplexityBridge.TM2PairLengths.cfg,
          Shared.ComplexityBridge.TM2PairLengths.stackVals,Turing.initList,Function.update]
      | inr j => cases j <;> simp [machine,parseEmbed,parseStacks,Shared.ComplexityBridge.TM2PairLengths.cfg,
          Shared.ComplexityBridge.TM2PairLengths.stackVals,Turing.initList,Function.update]

set_option backward.isDefEq.respectTransparency false in
theorem parse_dispatch (ts : Terms) (bits : List Bool) (nx nw : Nat) :
    (machine ts).step (parseEmbed ts (fun _ => [])
      (Shared.ComplexityBridge.TM2PairLengths.cfg .done none bits [] nx nw)) =
    some (polyEmbed ts bits [] (List.replicate nw true)
      (Shared.ComplexityBridge.TM2UnaryPolynomial.initialCfg ts nx 0)) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2
  funext q
  cases q with
  | inl b => cases b <;> simp [parseEmbed,parseStacks,polyEmbed,polyStacks,program,
      Shared.ComplexityBridge.TM2PairLengths.cfg,Shared.ComplexityBridge.TM2PairLengths.stackVals,
      Shared.ComplexityBridge.TM2UnaryPolynomial.initialCfg,Shared.ComplexityBridge.TM2UnaryPolynomial.stackVals,
      Shared.ComplexityBridge.TM2UnaryMonomial.powerStacks,Shared.ComplexityBridge.TM2UnaryMultiply.stackVals,Function.update] <;> (intro h; cases h)
  | inr q => cases q with
    | inl u => cases u; simp [parseEmbed,parseStacks,polyEmbed,polyStacks,program,
        Shared.ComplexityBridge.TM2PairLengths.cfg,Shared.ComplexityBridge.TM2PairLengths.stackVals,
        Shared.ComplexityBridge.TM2UnaryPolynomial.initialCfg,Shared.ComplexityBridge.TM2UnaryPolynomial.stackVals,
        Shared.ComplexityBridge.TM2UnaryMonomial.powerStacks,Shared.ComplexityBridge.TM2UnaryMultiply.stackVals,Function.update] <;> (intro h; cases h)
    | inr q => cases q with
      | inl b => cases b <;> simp [parseEmbed,parseStacks,polyEmbed,polyStacks,program,
          Shared.ComplexityBridge.TM2PairLengths.cfg,Shared.ComplexityBridge.TM2PairLengths.stackVals,
          Shared.ComplexityBridge.TM2UnaryPolynomial.initialCfg,Shared.ComplexityBridge.TM2UnaryPolynomial.stackVals,
          Shared.ComplexityBridge.TM2UnaryMonomial.powerStacks,Shared.ComplexityBridge.TM2UnaryMultiply.stackVals,Function.update] <;> (intro h; cases h)
      | inr j => cases j <;> simp [parseEmbed,parseStacks,polyEmbed,polyStacks,program,
          Shared.ComplexityBridge.TM2PairLengths.cfg,Shared.ComplexityBridge.TM2PairLengths.stackVals,
          Shared.ComplexityBridge.TM2UnaryPolynomial.initialCfg,Shared.ComplexityBridge.TM2UnaryPolynomial.stackVals,
          Shared.ComplexityBridge.TM2UnaryMonomial.powerStacks,Shared.ComplexityBridge.TM2UnaryMultiply.stackVals,Function.update] <;> (intro h; cases h)


def afterPoly (ts : Terms) (bits : List Bool) (nx nw : Nat) : Key → List Bool :=
  polyStacks bits [] (List.replicate nw true)
    (Shared.ComplexityBridge.TM2UnaryPolynomial.finalCfg ts nx
      (Shared.Codes.NumericPolynomial.eval ts nx)).stk

set_option backward.isDefEq.respectTransparency false in
theorem poly_dispatch (ts : Terms) (bits : List Bool) (nx nw : Nat) :
    (machine ts).step (polyEmbed ts bits [] (List.replicate nw true)
      (Shared.ComplexityBridge.TM2UnaryPolynomial.finalCfg ts nx
        (Shared.Codes.NumericPolynomial.eval ts nx))) =
    some (compareEmbed ts (afterPoly ts bits nx nw)
      (Shared.ComplexityBridge.TM2UnaryCutoff.cfg .compare false nw
        (Shared.Codes.NumericPolynomial.eval ts nx))) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  simp only [machine, program, if_pos rfl, stepAux,
    Shared.ComplexityBridge.TM2UnaryPolynomial.finalCfg, Shared.ComplexityBridge.TM2UnaryCutoff.cfg,
    polyEmbed, compareEmbed, Option.map_some]
  congr 2
  funext q
  cases q with
  | inl b => cases b <;> simp [afterPoly,compareEmbed,compareStacks,polyEmbed,polyStacks,
      Shared.ComplexityBridge.TM2UnaryCutoff.cfg,Shared.ComplexityBridge.TM2UnaryCutoff.stackVals,
      Shared.ComplexityBridge.TM2UnaryPolynomial.finalCfg,Shared.ComplexityBridge.TM2UnaryPolynomial.stackVals,
      Shared.ComplexityBridge.TM2UnaryMonomial.powerStacks,Shared.ComplexityBridge.TM2UnaryMultiply.stackVals]
  | inr q => cases q with
    | inl u => cases u; simp [afterPoly,compareEmbed,compareStacks,polyEmbed,polyStacks,
        Shared.ComplexityBridge.TM2UnaryCutoff.cfg,Shared.ComplexityBridge.TM2UnaryCutoff.stackVals,
        Shared.ComplexityBridge.TM2UnaryPolynomial.finalCfg,Shared.ComplexityBridge.TM2UnaryPolynomial.stackVals,
        Shared.ComplexityBridge.TM2UnaryMonomial.powerStacks,Shared.ComplexityBridge.TM2UnaryMultiply.stackVals]
    | inr q => cases q with
      | inl b => cases b <;> simp [afterPoly,compareEmbed,compareStacks,polyEmbed,polyStacks,
          Shared.ComplexityBridge.TM2UnaryCutoff.cfg,Shared.ComplexityBridge.TM2UnaryCutoff.stackVals,
          Shared.ComplexityBridge.TM2UnaryPolynomial.finalCfg,Shared.ComplexityBridge.TM2UnaryPolynomial.stackVals,
          Shared.ComplexityBridge.TM2UnaryMonomial.powerStacks,Shared.ComplexityBridge.TM2UnaryMultiply.stackVals]
      | inr j => cases j <;> simp [afterPoly,compareEmbed,compareStacks,polyEmbed,polyStacks,
          Shared.ComplexityBridge.TM2UnaryCutoff.cfg,Shared.ComplexityBridge.TM2UnaryCutoff.stackVals,
          Shared.ComplexityBridge.TM2UnaryPolynomial.finalCfg,Shared.ComplexityBridge.TM2UnaryPolynomial.stackVals,
          Shared.ComplexityBridge.TM2UnaryMonomial.powerStacks,Shared.ComplexityBridge.TM2UnaryMultiply.stackVals]

set_option backward.isDefEq.respectTransparency false in
/-- The actual pair input is parsed, the fixed cutoff is computed, and the
original witness cutoff is decided. Each dispatch is charged one block. -/
theorem gate_correct (ts : Terms) (x w : List Bool) :
    ∃ t ≤ (2*(BitstringEncoding.bitEncode (x,w)).length+4) +
        (Shared.ComplexityBridge.TM2UnaryPolynomial.cost ts x.length+1) + (w.length+1),
      ∃ remaining,
      runSteps (machine ts).step t (Turing.initList (machine ts) (BitstringEncoding.bitEncode (x,w))) =
      some (compareEmbed ts (afterPoly ts (BitstringEncoding.bitEncode (x,w)) x.length w.length)
        (if w.length ≤ Shared.Codes.NumericPolynomial.eval ts x.length then
          Shared.ComplexityBridge.TM2UnaryCutoff.cfg .accept false 0 remaining
        else Shared.ComplexityBridge.TM2UnaryCutoff.cfg .reject false remaining 0)) := by
  let bits := BitstringEncoding.bitEncode (x,w)
  let finish := Shared.ComplexityBridge.TM2PairLengths.cfg .done none bits [] x.length w.length
  obtain ⟨a,ha,harun⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    Parse.step (machine ts).step (parseEmbed ts (fun _ => [])) parseTerminal
    parse_stable (parse_step ts (fun _ => [])) (2*bits.length+3)
    (Turing.initList Parse bits) finish (by rfl)
    (Shared.ComplexityBridge.TM2PairLengths.load_pair_lengths x w)
  obtain ⟨b,hb,hbrun⟩ := Shared.ComplexityBridge.TM2UnaryPolynomial.evaluate ts x.length 0
  let pend := Shared.ComplexityBridge.TM2UnaryPolynomial.finalCfg ts x.length
    (Shared.Codes.NumericPolynomial.eval ts x.length)
  have hb' : runSteps (Poly ts).step b (Shared.ComplexityBridge.TM2UnaryPolynomial.initialCfg ts x.length 0) = some pend := by
    simpa [pend] using hbrun
  obtain ⟨c,hc,hcrun⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    (Poly ts).step (machine ts).step (polyEmbed ts bits [] (List.replicate w.length true))
    (Shared.ComplexityBridge.TM2UnaryPolynomial.doneTerminal ts)
    (Shared.ComplexityBridge.TM2UnaryPolynomial.done_stable ts)
    (poly_step ts bits [] (List.replicate w.length true)) b
    (Shared.ComplexityBridge.TM2UnaryPolynomial.initialCfg ts x.length 0) pend (by rfl) hb'
  obtain ⟨d,hd,remaining,hdrun⟩ := Shared.ComplexityBridge.TM2UnaryCutoff.compare_progress w.length
    (Shared.Codes.NumericPolynomial.eval ts x.length)
  refine ⟨a+1+c+1+d,by dsimp [bits] at *; omega,remaining,?_⟩
  rw [initial_eq,show a+1+c+1+d = a+(1+(c+(1+d))) by omega,runSteps_add,harun]
  change runSteps (machine ts).step (1+(c+(1+d))) (parseEmbed ts (fun _ => []) finish) = _
  rw [show 1+(c+(1+d)) = (c+(1+d))+1 by omega,runSteps_front,parse_dispatch]
  change runSteps (machine ts).step (c+(1+d)) (polyEmbed ts bits [] (List.replicate w.length true)
    (Shared.ComplexityBridge.TM2UnaryPolynomial.initialCfg ts x.length 0)) = _
  rw [runSteps_add,hcrun]
  change runSteps (machine ts).step (1+d) (polyEmbed ts bits [] (List.replicate w.length true) pend) = _
  rw [show 1+d = d+1 by omega,runSteps_front,poly_dispatch]
  change runSteps (machine ts).step d (compareEmbed ts (afterPoly ts bits x.length w.length)
    (Shared.ComplexityBridge.TM2UnaryCutoff.cfg .compare false w.length
      (Shared.Codes.NumericPolynomial.eval ts x.length))) = _
  rw [compare_run,hdrun]
  split <;> rfl

/-- The fixed control's cost is monotone in the raw input length. -/
theorem cost_mono (ts : Terms) {a b : Nat} (h : a ≤ b) :
    Shared.ComplexityBridge.TM2UnaryPolynomial.cost ts a ≤
      Shared.ComplexityBridge.TM2UnaryPolynomial.cost ts b := by
  induction ts with
  | nil => simp [Shared.ComplexityBridge.TM2UnaryPolynomial.cost]
  | cons term ts ih =>
    rcases term with ⟨c,e⟩
    simp only [Shared.ComplexityBridge.TM2UnaryPolynomial.cost]
    gcongr

noncomputable def timePolynomial (ts : Terms) : Polynomial Nat :=
  Polynomial.C 3 * Polynomial.X + Polynomial.C 6 + Shared.ComplexityBridge.TM2UnaryPolynomial.costPolynomial ts

/-- A polynomial in the length of the entire encoded input bounds the gate. -/
theorem gate_polynomial_bound (ts : Terms) (x w : List Bool) :
    ∃ t ≤ (timePolynomial ts).eval (BitstringEncoding.bitEncode (x,w)).length,
      ∃ remaining,
      runSteps (machine ts).step t (Turing.initList (machine ts) (BitstringEncoding.bitEncode (x,w))) =
      some (compareEmbed ts (afterPoly ts (BitstringEncoding.bitEncode (x,w)) x.length w.length)
        (if w.length ≤ Shared.Codes.NumericPolynomial.eval ts x.length then
          Shared.ComplexityBridge.TM2UnaryCutoff.cfg .accept false 0 remaining
        else Shared.ComplexityBridge.TM2UnaryCutoff.cfg .reject false remaining 0)) := by
  obtain ⟨t,ht,r,hr⟩ := gate_correct ts x w
  refine ⟨t,?_,r,hr⟩
  have hlen := Shared.ComplexityBridge.bitstring_pair_encoded_length x w
  have hx : x.length ≤ (BitstringEncoding.bitEncode (x,w)).length := by omega
  have hw : w.length ≤ (BitstringEncoding.bitEncode (x,w)).length := by omega
  have hc := cost_mono ts hx
  simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
    Shared.ComplexityBridge.TM2UnaryPolynomial.costPolynomial_eval]
  omega

set_option backward.isDefEq.respectTransparency false in
/-- The gate uses the verifier's original cutoff, independently of any larger
outer witness-enumeration bound. The continuation is still a separate task. -/
theorem verifier_gate (v : Shared.NPCONP.TM2Verifier.Verifier) (x w : List Bool) :
    ∃ t ≤ (timePolynomial v.1.2).eval (BitstringEncoding.bitEncode (x,w)).length,
      ∃ remaining,
      runSteps (machine v.1.2).step t (Turing.initList (machine v.1.2) (BitstringEncoding.bitEncode (x,w))) =
      some (compareEmbed v.1.2 (afterPoly v.1.2 (BitstringEncoding.bitEncode (x,w)) x.length w.length)
        (if w.length ≤ Shared.NPCONP.TM2Verifier.cutoff v x then
          Shared.ComplexityBridge.TM2UnaryCutoff.cfg .accept false 0 remaining
        else Shared.ComplexityBridge.TM2UnaryCutoff.cfg .reject false remaining 0)) := by
  exact gate_polynomial_bound v.1.2 x w

/-- Executable end-to-end traces for a zero cutoff and empty/nonempty witness. -/
example : (runSteps (machine []).step 8
    (Turing.initList (machine []) (BitstringEncoding.bitEncode (([] : List Bool),([] : List Bool))))).map
    (fun q => match q.l with | some (.inr (.inr .accept)) => true | _ => false) = some true := by
  change (Option.map (fun q => match q.l with | some (.inr (.inr .accept)) => true | _ => false)
    (runSteps (machine []).step 8 (Turing.initList (machine [])
      (BitstringEncoding.bitEncode (([] : List Bool),([] : List Bool))))) : Option Bool) = _
  decide

example : (runSteps (machine []).step 14
    (Turing.initList (machine []) (BitstringEncoding.bitEncode (([] : List Bool),[true])))).map
    (fun q => match q.l with | some (.inr (.inr .reject)) => true | _ => false) = some true := by
  change (Option.map (fun q => match q.l with | some (.inr (.inr .reject)) => true | _ => false)
    (runSteps (machine []).step 14 (Turing.initList (machine [])
      (BitstringEncoding.bitEncode (([] : List Bool),[true])))) : Option Bool) = _
  decide

end Shared.ComplexityBridge.TM2CutoffGate
