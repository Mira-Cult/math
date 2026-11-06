import Shared.ComplexityBridge.TM2LiteralParse
import Shared.ComplexityBridge.TM2WitnessLookup

set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2LiteralEval
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
abbrev Parse := Shared.ComplexityBridge.TM2LiteralParse.machine
abbrev Lookup := Shared.ComplexityBridge.TM2WitnessLookup.machine
abbrev PKey := Shared.ComplexityBridge.TM2Undelimit.Stack
abbrev Key := Shared.ComplexityBridge.TM2WitnessLookup.Key
abbrev PLabel := Shared.ComplexityBridge.TM2LiteralParse.Label
abbrev LLabel := Shared.ComplexityBridge.TM2WitnessLookup.Label
abbrev PState := Shared.ComplexityBridge.TM2LiteralParse.State
abbrev LState := Shared.ComplexityBridge.TM2WitnessLookup.State
inductive Result where | invalid | yes | no deriving DecidableEq
instance : Fintype Result := Fintype.ofList [.invalid,.yes,.no] (by intro x; cases x <;> simp)
abbrev Label := PLabel ⊕ (LLabel ⊕ Result)
abbrev State := Bool × (PState ⊕ LState)
def parseState : State → PState | (_, .inl v) => v | _ => Parse.initialState
def lookupState : State → LState | (_, .inr v) => v | _ => Lookup.initialState
def sign (v : State) : Bool := v.1

def pkey : PKey → Key | .input => .left | .scratch => .scratch | .payload => .query
def pstacks (S : PKey → List Bool) (other : Key → List Bool) : Key → List Bool
  | .left => S .input | .scratch => S .scratch | .query => S .payload | k => other k
@[simp] theorem pstacks_apply (S : PKey → List Bool) (other : Key → List Bool) (j : PKey) : pstacks S other (pkey j) = S j := by cases j <;> rfl
theorem pupdate (S : PKey → List Bool) (other : Key → List Bool) (j : PKey) (xs : List Bool) :
    pstacks (Function.update S j xs) other = Function.update (pstacks S other) (pkey j) xs := by
  funext k; cases j <;> cases k <;> simp [pstacks,pkey,Function.update]

def pemb (other : Key → List Bool) (q : Parse.Cfg) : Cfg (fun _ : Key => Bool) Label State :=
  ⟨q.l.map Sum.inl,(false,.inl q.var),pstacks q.stk other⟩
def lemb (s : Bool) (q : Lookup.Cfg) : Cfg (fun _ : Key => Bool) Label State :=
  ⟨q.l.map (fun l => .inr (.inl l)),(s,.inr q.var),q.stk⟩

def liftParse : Stmt (fun _ : PKey => Bool) PLabel PState → Stmt (fun _ : Key => Bool) Label State
  | .push j f q => .push (pkey j) (fun v => f (parseState v)) (liftParse q)
  | .peek j f q => .peek (pkey j) (fun v h => (false,.inl (f (parseState v) h))) (liftParse q)
  | .pop j f q => .pop (pkey j) (fun v h => (false,.inl (f (parseState v) h))) (liftParse q)
  | .load f q => .load (fun v => (false,.inl (f (parseState v)))) (liftParse q)
  | .branch f q r => .branch (fun v => f (parseState v)) (liftParse q) (liftParse r)
  | .goto f => .goto (fun v => .inl (f (parseState v)))
  | .halt => .halt

def liftLookup : Stmt (fun _ : Key => Bool) LLabel LState → Stmt (fun _ : Key => Bool) Label State
  | .push j f q => .push j (fun v => f (lookupState v)) (liftLookup q)
  | .peek j f q => .peek j (fun v h => (sign v,.inr (f (lookupState v) h))) (liftLookup q)
  | .pop j f q => .pop j (fun v h => (sign v,.inr (f (lookupState v) h))) (liftLookup q)
  | .load f q => .load (fun v => (sign v,.inr (f (lookupState v)))) (liftLookup q)
  | .branch f q r => .branch (fun v => f (lookupState v)) (liftLookup q) (liftLookup r)
  | .goto f => .goto (fun v => .inr (.inl (f (lookupState v))))
  | .halt => .halt

theorem liftParse_aux (q : Parse.Stmt) (v : PState) (S : PKey → List Bool) (other : Key → List Bool) :
    stepAux (liftParse q) (false,.inl v) (pstacks S other) = pemb other (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih _ _
  | push j f q ih => simp only [liftParse,stepAux,parseState,pstacks_apply]; rw [← pupdate S other j (f v::S j)]; exact ih _ _
  | peek j f q ih => simp only [liftParse,stepAux,parseState,pstacks_apply]; exact ih _ _
  | pop j f q ih => simp only [liftParse,stepAux,parseState,pstacks_apply]; rw [← pupdate S other j (S j).tail]; exact ih _ _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [liftParse,stepAux,parseState,h,ihq,ihr]

theorem liftLookup_aux (q : Lookup.Stmt) (s : Bool) (v : LState) (S : Key → List Bool) :
    stepAux (liftLookup q) (s,.inr v) S = lemb s (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih _ _
  | push j f q ih => exact ih _ _
  | peek j f q ih => exact ih _ _
  | pop j f q ih => exact ih _ _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [liftLookup,stepAux,lookupState,h,ihq,ihr]

def parsedSign : PState → Bool | .inr (some b,_) => b | _ => false
def program : Label → Stmt (fun _ : Key => Bool) Label State
  | .inl (.inr .accept) => .load (fun v => (parsedSign (parseState v),.inr Lookup.initialState)) (.goto (fun _ => .inr (.inl Lookup.main)))
  | .inl (.inr .reject) => .goto (fun _ => .inr (.inr .invalid))
  | .inl l => liftParse (Shared.ComplexityBridge.TM2LiteralParse.program l)
  | .inr (.inl (.inl .yes)) => .branch sign (.goto (fun _ => .inr (.inr .yes))) (.goto (fun _ => .inr (.inr .no)))
  | .inr (.inl (.inl .no)) => .branch sign (.goto (fun _ => .inr (.inr .no))) (.goto (fun _ => .inr (.inr .yes)))
  | .inr (.inl l) => liftLookup (Shared.ComplexityBridge.TM2WitnessLookup.program l)
  | .inr (.inr r) => .goto (fun _ => .inr (.inr r))

def machine : Turing.FinTM2 where
  K := Key
  k₀ := .left
  k₁ := .left
  Γ := fun _ => Bool
  Λ := Label
  main := .inl Parse.main
  σ := State
  initialState := (false,.inl Parse.initialState)
  m := program

def pTerminal (q : Parse.Cfg) : Prop := q.l = some (.inr .accept) ∨ q.l = some (.inr .reject)
noncomputable instance : DecidablePred pTerminal := fun _ => Classical.propDecidable _
theorem pStable (q : Parse.Cfg) (h : pTerminal q) : Parse.step q = some q := by
  cases q with
  | mk l v S =>
    change l = some (.inr Shared.ComplexityBridge.TM2LiteralParse.CheckLabel.accept) ∨ l = some (.inr Shared.ComplexityBridge.TM2LiteralParse.CheckLabel.reject) at h
    rcases h with h | h <;> subst l <;> rfl

theorem pStep (other : Key → List Bool) (q : Parse.Cfg) (h : ¬ pTerminal q) :
    machine.step (pemb other q) = (Parse.step q).map (pemb other) := by
  cases q with
  | mk l v S => cases l with
    | none => rfl
    | some l => cases l with
      | inl l =>
        change some (stepAux (liftParse (Shared.ComplexityBridge.TM2LiteralParse.program (.inl l))) (false,.inl v) (pstacks S other)) = _
        rw [liftParse_aux]; rfl
      | inr l => cases l with
        | accept => exact False.elim (h (Or.inl rfl))
        | reject => exact False.elim (h (Or.inr rfl))
        | sign | endSign =>
          change some (stepAux (liftParse (Shared.ComplexityBridge.TM2LiteralParse.program (.inr _))) (false,.inl v) (pstacks S other)) = _
          rw [liftParse_aux]; rfl

def lTerminal (q : Lookup.Cfg) : Prop := q.l = some (.inl .yes) ∨ q.l = some (.inl .no)
noncomputable instance : DecidablePred lTerminal := fun _ => Classical.propDecidable _
theorem lStable (q : Lookup.Cfg) (h : lTerminal q) : Lookup.step q = some q := by
  cases q with
  | mk l v S =>
    change l = some (.inl Shared.ComplexityBridge.TM2WitnessLookup.Phase.yes) ∨ l = some (.inl Shared.ComplexityBridge.TM2WitnessLookup.Phase.no) at h
    rcases h with h | h <;> subst l <;> rfl

theorem lStep (s : Bool) (q : Lookup.Cfg) (h : ¬ lTerminal q) :
    machine.step (lemb s q) = (Lookup.step q).map (lemb s) := by
  cases q with
  | mk l v S => cases l with
    | none => rfl
    | some l => cases l with
      | inl p => cases p with
        | yes => exact False.elim (h (Or.inl rfl))
        | no => exact False.elim (h (Or.inr rfl))
        | start | copy | restore | clearLeft | clearRight =>
          change some (stepAux (liftLookup (Shared.ComplexityBridge.TM2WitnessLookup.program _)) (s,.inr v) S) = _
          rw [liftLookup_aux]; rfl
      | inr l =>
        change some (stepAux (liftLookup (Shared.ComplexityBridge.TM2WitnessLookup.program _)) (s,.inr v) S) = _
        rw [liftLookup_aux]; rfl


def loaded (vars witness literal : List Bool) : machine.Cfg :=
  pemb (Shared.ComplexityBridge.TM2WitnessLookup.stackVals vars witness [] [] [] [])
    (Turing.initList Parse literal)

theorem dispatch_accept (vars witness name : List Bool) (s : Bool) :
    machine.step (pemb (Shared.ComplexityBridge.TM2WitnessLookup.stackVals vars witness [] [] [] [])
      (Shared.ComplexityBridge.TM2LiteralParse.cfg .accept (some s) none [] [] name)) =
    some (lemb s (Shared.ComplexityBridge.TM2WitnessLookup.cfg .start false false none vars witness name [] [] [])) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> rfl

theorem dispatch_reject (other : Key → List Bool) (q : Parse.Cfg)
    (h : q.l = some (.inr .reject)) :
    ∃ r, machine.step (pemb other q) = some r ∧ r.l = some (.inr (.inr .invalid)) := by
  cases q with
  | mk l v S =>
    change l = some (.inr .reject) at h
    subst l
    exact ⟨⟨some (.inr (.inr .invalid)),(false,.inl v),pstacks S other⟩,rfl,rfl⟩

theorem dispatch_answer (s b : Bool) (q : Lookup.Cfg)
    (h : q.l = some (.inl (if b then .yes else .no))) :
    ∃ r, machine.step (lemb s q) = some r ∧
      r.l = some (.inr (.inr (if b == s then .yes else .no))) := by
  cases q with
  | mk l v S =>
    cases s <;> cases b <;> simp only [Bool.false_eq_true,if_false,if_true] at h ⊢ <;> subst l <;>
      exact ⟨⟨_,(_, .inr v),S⟩,rfl,rfl⟩

/-- Total literal semantics. An invalid encoding is distinguished from a
well-formed literal whose value is false. -/
def evaluate (vars : List (List Bool)) (witness literal : List Bool) : Option Bool :=
  (Shared.ComplexityBridge.TM2LiteralParse.literalBits literal).map
    (fun p => Shared.ComplexityBridge.RawCNFLookup.lookup vars witness p.1 == p.2)

theorem name_length (literal name : List Bool) (s : Bool)
    (h : Shared.ComplexityBridge.TM2LiteralParse.literalBits literal = some (name,s)) :
    name.length ≤ literal.length := by
  cases hu : BitstringEncoding.undelimit literal with
  | none => simp [Shared.ComplexityBridge.TM2LiteralParse.literalBits,hu] at h
  | some pair =>
    rcases pair with ⟨payload,rest⟩
    cases rest with
    | nil => simp [Shared.ComplexityBridge.TM2LiteralParse.literalBits,hu] at h
    | cons b rest => cases rest with
      | cons c rest => simp [Shared.ComplexityBridge.TM2LiteralParse.literalBits,hu] at h
      | nil =>
        simp [Shared.ComplexityBridge.TM2LiteralParse.literalBits,hu] at h
        rcases h with ⟨rfl,rfl⟩
        have he := Shared.ComplexityBridge.CNFWitness.undelimit_sound literal payload [b] hu
        have hl := congrArg List.length he
        simp only [List.length_append,BitstringEncoding.length_delimit,List.length_cons,List.length_nil] at hl
        omega

/-- Loaded parser and witness lookup terminate on all literals. The cost
includes parsing, dispatch, lookup and final result dispatch. The occurrence
and witness stacks are consumed; a caller must charge copies or restoration. -/
theorem loaded_progress (vars : List (List Bool)) (witness literal : List Bool) :
    let B := (Shared.ComplexityBridge.TM2WitnessLookup.frames vars).length+literal.length
    ∃ t ≤ 3*literal.length+5+1+(B+1)*Shared.ComplexityBridge.TM2WitnessLookup.iterationBound B+1,
      ∃ q : machine.Cfg, runSteps machine.step t (loaded (Shared.ComplexityBridge.TM2WitnessLookup.frames vars) witness literal) = some q ∧
      q.l = some (.inr (.inr (match evaluate vars witness literal with
        | none => .invalid | some true => .yes | some false => .no))) := by
  let frames := Shared.ComplexityBridge.TM2WitnessLookup.frames vars
  let other := Shared.ComplexityBridge.TM2WitnessLookup.stackVals frames witness [] [] [] []
  let B := frames.length+literal.length
  obtain ⟨n,hn,q,hr,hq⟩ := Shared.ComplexityBridge.TM2LiteralParse.parse_progress literal
  cases hx : Shared.ComplexityBridge.TM2LiteralParse.literalBits literal with
  | none =>
    have hq' : q.l = some (.inr .reject) := by simpa [hx] using hq
    obtain ⟨a,ha,har⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
      Parse.step machine.step (pemb other) pTerminal pStable (pStep other) n (Turing.initList Parse literal) q (Or.inr hq') hr
    obtain ⟨r,hs,hl⟩ := dispatch_reject other q hq'
    refine ⟨a+1,?_,r,?_,?_⟩
    · omega
    · change runSteps machine.step (a+1) (pemb other (Turing.initList Parse literal)) = _
      rw [runSteps_add,har]; exact hs
    · simpa [evaluate,hx] using hl
  | some pair =>
    rcases pair with ⟨name,s⟩
    have hq' : q = Shared.ComplexityBridge.TM2LiteralParse.cfg .accept (some s) none [] [] name := by simpa [hx] using hq
    subst q
    let finish := Shared.ComplexityBridge.TM2LiteralParse.cfg .accept (some s) none [] [] name
    change runSteps Parse.step n (Turing.initList Parse literal) = some finish at hr
    obtain ⟨a,ha,har⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
      Parse.step machine.step (pemb other) pTerminal pStable (pStep other) n (Turing.initList Parse literal) finish (Or.inl rfl) hr
    obtain ⟨m,hm,q,hlookup,hlabel⟩ := Shared.ComplexityBridge.TM2WitnessLookup.lookup_progress vars witness name false false none
    let b := Shared.ComplexityBridge.RawCNFLookup.lookup vars witness name
    change q.l = some (.inl (if b then .yes else .no)) at hlabel
    have hterminal : lTerminal q := by
      unfold lTerminal
      cases hb : b with
      | false => right; simpa [hb] using hlabel
      | true => left; simpa [hb] using hlabel
    obtain ⟨c,hc,hcr⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
      Lookup.step machine.step (lemb s) lTerminal lStable (lStep s) m
      (Shared.ComplexityBridge.TM2WitnessLookup.cfg .start false false none frames witness name [] [] []) q hterminal hlookup
    obtain ⟨r,hd,hlabel'⟩ := dispatch_answer s b q hlabel
    have hname := name_length literal name s hx
    have hB : frames.length+name.length ≤ B := by dsimp [B]; omega
    have hmono := Shared.ComplexityBridge.TM2WitnessLookup.iterationBound_mono hB
    have hbound := Nat.mul_le_mul (show frames.length+name.length+1 ≤ B+1 by omega) hmono
    refine ⟨a+1+c+1,?_,r,?_,?_⟩
    · change a+1+c+1 ≤ 3*literal.length+5+1+(B+1)*Shared.ComplexityBridge.TM2WitnessLookup.iterationBound B+1
      change m ≤ (frames.length+name.length+1)*Shared.ComplexityBridge.TM2WitnessLookup.iterationBound (frames.length+name.length) at hm
      omega
    · change runSteps machine.step (a+1+c+1) (pemb other (Turing.initList Parse literal)) = _
      rw [show a+1+c+1 = a+(1+(c+1)) by omega,runSteps_add,har]
      change runSteps machine.step (1+(c+1)) (pemb other finish) = _
      rw [runSteps_add]
      change (machine.step (pemb other finish)).bind _ = _
      rw [dispatch_accept]
      change runSteps machine.step (c+1) (lemb s (Shared.ComplexityBridge.TM2WitnessLookup.cfg .start false false none frames witness name [] [] [])) = _
      rw [runSteps_add,hcr]; exact hd
    · change r.l = some (.inr (.inr (match evaluate vars witness literal with
        | none => .invalid | some true => .yes | some false => .no)))
      simp only [evaluate,hx,Option.map_some]
      change r.l = some (.inr (.inr (match some (b == s) with | none => .invalid | some true => .yes | some false => .no)))
      cases hbs : (b == s) <;> simpa [hbs] using hlabel'

/-- On well-formed literals, the loaded result agrees with the public CNF
semantics, including noncanonical names and short witnesses. -/
theorem evaluate_correct (vars : List (List Bool)) (witness literal : List Bool) (lit : Shared.ComplexityBridge.CNF.Literal)
    (h : (BitstringEncoding.bitDecode literal : Option Shared.ComplexityBridge.CNF.Literal) = some lit) :
    evaluate vars witness literal = some (Shared.ComplexityBridge.CNF.evalLiteral
      (Shared.ComplexityBridge.CNF.assignment (vars.map Computability.decodeNat) witness) lit) := by
  rw [Shared.ComplexityBridge.TM2LiteralParse.literalBits_decode] at h
  cases hx : Shared.ComplexityBridge.TM2LiteralParse.literalBits literal with
  | none => simp [hx] at h
  | some p =>
    rcases p with ⟨name,s⟩
    simp [hx] at h
    subst lit
    simp [evaluate,hx,Shared.ComplexityBridge.RawCNFLookup.lookup_correct,Shared.ComplexityBridge.CNF.evalLiteral]


/-- One polynomial bounds the loaded call in the sum of all three input
lengths. The lookup's comparison overhead is charged explicitly. -/
noncomputable def timePolynomial : Polynomial Nat :=
  let D := Shared.ComplexityBridge.TM2GenericStackBound.tableBound Shared.ComplexityBridge.TM2WitnessLookup.Compare
  let X := Polynomial.X
  let I := Polynomial.C 8*(X+Polynomial.C 2)+Polynomial.C 2*((X+Polynomial.C 2)*Polynomial.C D)
  Polynomial.C 3*X+Polynomial.C 5+Polynomial.C 1+(X+Polynomial.C 1)*I+Polynomial.C 1

theorem timePolynomial_eval (n : Nat) :
    timePolynomial.eval n = 3*n+5+1+(n+1)*Shared.ComplexityBridge.TM2WitnessLookup.iterationBound n+1 := by
  simp [timePolynomial,Shared.ComplexityBridge.TM2WitnessLookup.iterationBound]

theorem loaded_progress_polynomial (vars : List (List Bool)) (witness literal : List Bool) :
    let size := (Shared.ComplexityBridge.TM2WitnessLookup.frames vars).length+witness.length+literal.length
    ∃ t ≤ timePolynomial.eval size, ∃ q : machine.Cfg,
      runSteps machine.step t (loaded (Shared.ComplexityBridge.TM2WitnessLookup.frames vars) witness literal) = some q ∧
      q.l = some (.inr (.inr (match evaluate vars witness literal with
        | none => .invalid | some true => .yes | some false => .no))) := by
  let frames := Shared.ComplexityBridge.TM2WitnessLookup.frames vars
  let size := frames.length+witness.length+literal.length
  let B := frames.length+literal.length
  obtain ⟨t,ht,q,hr,hq⟩ := loaded_progress vars witness literal
  change t ≤ 3*literal.length+5+1+(B+1)*Shared.ComplexityBridge.TM2WitnessLookup.iterationBound B+1 at ht
  have hB : B ≤ size := by dsimp [B,size]; omega
  have hmono := Shared.ComplexityBridge.TM2WitnessLookup.iterationBound_mono hB
  have hm := Nat.mul_le_mul (show B+1 ≤ size+1 by omega) hmono
  refine ⟨t,?_,q,hr,hq⟩
  rw [timePolynomial_eval]
  change t ≤ 3*size+5+1+(size+1)*Shared.ComplexityBridge.TM2WitnessLookup.iterationBound size+1
  dsimp [size] at *
  omega

/-- Failure is exactly failure of the pinned public literal decoder. -/
theorem evaluate_none_iff (vars : List (List Bool)) (witness literal : List Bool) :
    evaluate vars witness literal = none ↔
      (BitstringEncoding.bitDecode literal : Option Shared.ComplexityBridge.CNF.Literal) = none := by
  rw [Shared.ComplexityBridge.TM2LiteralParse.literalBits_decode]
  cases hx : Shared.ComplexityBridge.TM2LiteralParse.literalBits literal <;> simp [evaluate,hx]

namespace Fixtures
set_option maxRecDepth 4096 in
example : (runSteps machine.step 26 (loaded (Shared.ComplexityBridge.TM2WitnessLookup.frames [[false]])
    [true] [true,false,false,true])).map
    (fun q => match q.l with | some (.inr (.inr .yes)) => true | _ => false) = some true := by
  change (Option.map (fun q => match q.l with | some (.inr (.inr .yes)) => true | _ => false)
    (runSteps machine.step 26 (loaded (Shared.ComplexityBridge.TM2WitnessLookup.frames [[false]])
      [true] [true,false,false,true])) : Option Bool) = _
  decide
set_option maxRecDepth 4096 in
example : (runSteps machine.step 26 (loaded (Shared.ComplexityBridge.TM2WitnessLookup.frames [[false]])
    [true] [true,false,false,false])).map
    (fun q => match q.l with | some (.inr (.inr .no)) => true | _ => false) = some true := by
  change (Option.map (fun q => match q.l with | some (.inr (.inr .no)) => true | _ => false)
    (runSteps machine.step 26 (loaded (Shared.ComplexityBridge.TM2WitnessLookup.frames [[false]])
      [true] [true,false,false,false])) : Option Bool) = _
  decide
example : (runSteps machine.step 5 (loaded (Shared.ComplexityBridge.TM2WitnessLookup.frames [[false]])
    [true] [false])).map
    (fun q => match q.l with | some (.inr (.inr .invalid)) => true | _ => false) = some true := by
  change (Option.map (fun q => match q.l with | some (.inr (.inr .invalid)) => true | _ => false)
    (runSteps machine.step 5 (loaded (Shared.ComplexityBridge.TM2WitnessLookup.frames [[false]])
      [true] [false])) : Option Bool) = _
  decide
end Fixtures

end Shared.ComplexityBridge.TM2LiteralEval
