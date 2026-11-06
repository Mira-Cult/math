import Shared.ComplexityBridge.TM2Undelimit
import Shared.ComplexityBridge.TM2UnaryTransfer

set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2LiteralParse
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
abbrev Source := Shared.ComplexityBridge.TM2Undelimit.machine
abbrev Key := Shared.ComplexityBridge.TM2Undelimit.Stack
abbrev SourceLabel := Shared.ComplexityBridge.TM2Undelimit.Label
inductive CheckLabel where | sign | endSign | accept | reject deriving DecidableEq
instance : Fintype CheckLabel := Fintype.ofList [.sign,.endSign,.accept,.reject] (by intro x; cases x <;> simp)
abbrev Label := SourceLabel ⊕ CheckLabel
abbrev State := Option Bool ⊕ (Option Bool × Option Bool)
def sourceState : State → Option Bool | .inl v => v | _ => none
def checkState : State → Option Bool × Option Bool | .inr v => v | _ => (none,none)
def embed (q : Source.Cfg) : Cfg (fun _ : Key => Bool) Label State :=
  ⟨q.l.map Sum.inl,.inl q.var,q.stk⟩
def lift : Stmt (fun _ : Key => Bool) SourceLabel (Option Bool) → Stmt (fun _ : Key => Bool) Label State
  | .push j f q => .push j (fun v => f (sourceState v)) (lift q)
  | .peek j f q => .peek j (fun v h => .inl (f (sourceState v) h)) (lift q)
  | .pop j f q => .pop j (fun v h => .inl (f (sourceState v) h)) (lift q)
  | .load f q => .load (fun v => .inl (f (sourceState v))) (lift q)
  | .branch f q r => .branch (fun v => f (sourceState v)) (lift q) (lift r)
  | .goto f => .goto (fun v => .inl (f (sourceState v)))
  | .halt => .halt

theorem lift_aux (q : Source.Stmt) (v : Option Bool) (S : Key → List Bool) :
    stepAux (lift q) (.inl v) S = embed (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih _ _
  | peek j f q ih => exact ih _ _
  | pop j f q ih => exact ih _ _
  | push j f q ih => exact ih _ _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [lift,stepAux,sourceState,h,ihq,ihr]

def program : Label → Stmt (fun _ : Key => Bool) Label State
  | .inl .done => .load (fun _ => .inr (none,none)) (.goto (fun _ => .inr .sign))
  | .inl .reject => .load (fun _ => .inr (none,none)) (.goto (fun _ => .inr .reject))
  | .inl l => lift (Shared.ComplexityBridge.TM2Undelimit.program l)
  | .inr .sign => .pop .input (fun _ h => .inr (h,h))
      (.branch (fun v => (checkState v).1.isSome) (.goto (fun _ => .inr .endSign))
        (.goto (fun _ => .inr .reject)))
  | .inr .endSign => .pop .input (fun v h => .inr ((checkState v).1,h))
      (.branch (fun v => (checkState v).2.isSome) (.goto (fun _ => .inr .reject))
        (.goto (fun _ => .inr .accept)))
  | .inr .accept => .goto (fun _ => .inr .accept)
  | .inr .reject => .goto (fun _ => .inr .reject)

def machine : Turing.FinTM2 where
  K := Key
  k₀ := .input
  k₁ := .payload
  Γ := fun _ => Bool
  Λ := Label
  main := .inl .header
  σ := State
  initialState := .inl none
  m := program

def terminal (q : Source.Cfg) : Prop := q.l = some .done ∨ q.l = some .reject
noncomputable instance : DecidablePred terminal := fun _ => Classical.propDecidable _
theorem stable (q : Source.Cfg) (h : terminal q) : Source.step q = some q := by
  cases q with
  | mk l v S =>
    change l = some Shared.ComplexityBridge.TM2Undelimit.Label.done ∨ l = some Shared.ComplexityBridge.TM2Undelimit.Label.reject at h
    rcases h with h | h <;> subst l <;> rfl

theorem source_step (q : Source.Cfg) (h : ¬ terminal q) :
    machine.step (embed q) = (Source.step q).map embed := by
  cases q with
  | mk l v S => cases l with
    | none => rfl
    | some l => cases l with
      | done => exact False.elim (h (Or.inl rfl))
      | reject => exact False.elim (h (Or.inr rfl))
      | header | data | restore =>
        change some (stepAux (lift (Shared.ComplexityBridge.TM2Undelimit.program _)) (.inl v) S) = _
        rw [lift_aux]; rfl

theorem initial_eq (input : List Bool) : Turing.initList machine input = embed (Turing.initList Source input) := rfl

def cfg (l : CheckLabel) (sign flag : Option Bool) (input scratch payload : List Bool) : machine.Cfg :=
  ⟨some (.inr l),.inr (sign,flag),Shared.ComplexityBridge.TM2Undelimit.stackVals input scratch payload⟩

theorem dispatch_done (tail payload : List Bool) :
    machine.step (embed (Shared.ComplexityBridge.TM2Undelimit.cfg .done none tail [] payload)) =
      some (cfg .sign none none tail [] payload) := by rfl

theorem dispatch_reject (scratch : List Bool) :
    machine.step (embed (Shared.ComplexityBridge.TM2Undelimit.cfg .reject none [] scratch [])) =
      some (cfg .reject none none [] scratch []) := by rfl

theorem sign_nil (payload : List Bool) :
    machine.step (cfg .sign none none [] [] payload) = some (cfg .reject none none [] [] payload) := by
  change some (Cfg.mk _ _ (Function.update (Shared.ComplexityBridge.TM2Undelimit.stackVals [] [] payload) .input [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [Shared.ComplexityBridge.TM2Undelimit.stackVals,Function.update]

theorem sign_cons (b : Bool) (tail payload : List Bool) :
    machine.step (cfg .sign none none (b::tail) [] payload) = some (cfg .endSign (some b) (some b) tail [] payload) := by
  change some (Cfg.mk _ _ (Function.update (Shared.ComplexityBridge.TM2Undelimit.stackVals (b::tail) [] payload) .input tail)) = _
  congr 1; congr 1; funext k; cases k <;> simp [Shared.ComplexityBridge.TM2Undelimit.stackVals,Function.update]

theorem end_nil (b : Bool) (payload : List Bool) :
    machine.step (cfg .endSign (some b) (some b) [] [] payload) = some (cfg .accept (some b) none [] [] payload) := by
  change some (Cfg.mk _ _ (Function.update (Shared.ComplexityBridge.TM2Undelimit.stackVals [] [] payload) .input [])) = _
  congr 1; congr 1; funext k; cases k <;> simp [Shared.ComplexityBridge.TM2Undelimit.stackVals,Function.update]

theorem end_cons (a b : Bool) (tail payload : List Bool) :
    machine.step (cfg .endSign (some a) (some a) (b::tail) [] payload) = some (cfg .reject (some a) (some b) tail [] payload) := by
  change some (Cfg.mk _ _ (Function.update (Shared.ComplexityBridge.TM2Undelimit.stackVals (b::tail) [] payload) .input tail)) = _
  congr 1; congr 1; funext k; cases k <;> simp [Shared.ComplexityBridge.TM2Undelimit.stackVals,Function.update]

/-- Decode the pair framing while retaining the original variable bits.
The Boolean component must be exactly one bit. -/
def literalBits (input : List Bool) : Option (List Bool × Bool) :=
  match BitstringEncoding.undelimit input with
  | some (payload,[b]) => some (payload,b)
  | _ => none

theorem literalBits_decode (input : List Bool) :
    (BitstringEncoding.bitDecode input : Option Shared.ComplexityBridge.CNF.Literal) =
      (literalBits input).map (fun p => (Computability.decodeNat p.1,p.2)) := by
  have hp : (BitstringEncoding.bitDecode input : Option (Nat × Bool)) =
    (match BitstringEncoding.undelimit input with
    | none => none
    | some (block,rest) =>
      match (BitstringEncoding.bitDecode block : Option Nat), (BitstringEncoding.bitDecode rest : Option Bool) with
      | some a,some b => some (a,b)
      | _,_ => none) := by
    unfold BitstringEncoding.bitDecode
    unfold BitstringEncoding.instProd BitstringEncoding.toEncoding Computability.Encoding.decode
    simp only [BitstringEncoding.bitDecode, BitstringEncoding.toEncoding, Computability.Encoding.decode, BitstringEncoding.instNat, BitstringEncoding.instBool]
    cases h : BitstringEncoding.undelimit input with
    | none => rfl
    | some p =>
      rcases p with ⟨a,b⟩
      cases b with
      | nil => rfl
      | cons b bs => cases bs <;> rfl
  rw [hp]
  cases h : BitstringEncoding.undelimit input with
  | none => simp [literalBits,h]
  | some p =>
    rcases p with ⟨payload,tail⟩
    cases tail with
    | nil => simp [literalBits,h,BitstringEncoding.bitDecode, BitstringEncoding.instNat, BitstringEncoding.instBool]
    | cons b tail => cases tail with
      | nil => change (match (some (Computability.decodeNat payload) : Option Nat), (some b : Option Bool) with | some a,some b => some (a,b) | _,_ => none) = _; simp [literalBits,h]
      | cons c tail => simp [literalBits,h,BitstringEncoding.bitDecode, BitstringEncoding.instNat, BitstringEncoding.instBool]

def tailResult (payload tail : List Bool) : Option (List Bool × Bool) :=
  match tail with | [b] => some (payload,b) | _ => none

theorem after_done (tail payload : List Bool) :
    ∃ t ≤ 3, ∃ q : machine.Cfg,
      runSteps machine.step t (embed (Shared.ComplexityBridge.TM2Undelimit.cfg .done none tail [] payload)) = some q ∧
      match tailResult payload tail with
      | none => q.l = some (.inr .reject)
      | some (bits,b) => q = cfg .accept (some b) none [] [] bits := by
  cases tail with
  | nil =>
    refine ⟨2,by omega,cfg .reject none none [] [] payload,?_,rfl⟩
    rw [show 2=1+1 by decide,runSteps_front,dispatch_done]
    exact sign_nil payload
  | cons b tail => cases tail with
    | nil =>
      refine ⟨3,by omega,cfg .accept (some b) none [] [] payload,?_,rfl⟩
      rw [show 3=(1+1)+1 by decide,runSteps_front,dispatch_done]
      change runSteps machine.step (1+1) (cfg .sign none none [b] [] payload) = _
      rw [runSteps_front,sign_cons]
      exact end_nil b payload
    | cons c tail =>
      refine ⟨3,by omega,cfg .reject (some b) (some c) tail [] payload,?_,rfl⟩
      rw [show 3=(1+1)+1 by decide,runSteps_front,dispatch_done]
      change runSteps machine.step (1+1) (cfg .sign none none (b::c::tail) [] payload) = _
      rw [runSteps_front,sign_cons]
      exact end_cons b c tail payload

/-- The machine always finishes literal parsing. A successful result keeps the
raw variable bits and sign; malformed input reaches the reject label. -/
theorem parse_progress (input : List Bool) :
    ∃ t ≤ 3*input.length+5, ∃ q : machine.Cfg,
      runSteps machine.step t (Turing.initList machine input) = some q ∧
      match literalBits input with
      | none => q.l = some (.inr .reject)
      | some (bits,b) => q = cfg .accept (some b) none [] [] bits := by
  rcases Shared.ComplexityBridge.TM2Undelimit.parse_progress input with h | h
  · rcases h with ⟨payload,tail,hdecode,n,hn,hr⟩
    obtain ⟨a,ha,har⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
      Source.step machine.step embed terminal stable source_step n (Turing.initList Source input)
      (Shared.ComplexityBridge.TM2Undelimit.cfg .done none tail [] payload) (Or.inl rfl) hr
    obtain ⟨b,hb,q,hbr,hq⟩ := after_done tail payload
    refine ⟨a+b,by omega,q,?_,?_⟩
    · rw [initial_eq,runSteps_add,har]
      exact hbr
    · cases tail with
      | nil => simpa [literalBits,hdecode,tailResult] using hq
      | cons b tail => cases tail with
        | nil => simpa [literalBits,hdecode,tailResult] using hq
        | cons c tail => simpa [literalBits,hdecode,tailResult] using hq
  · rcases h with ⟨hdecode,n,hn,scratch,hr⟩
    obtain ⟨a,ha,har⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
      Source.step machine.step embed terminal stable source_step n (Turing.initList Source input)
      (Shared.ComplexityBridge.TM2Undelimit.cfg .reject none [] scratch []) (Or.inr rfl) hr
    refine ⟨a+1,by omega,cfg .reject none none [] scratch [],?_,?_⟩
    · rw [initial_eq,runSteps_add,har]
      exact dispatch_reject scratch
    · simp [literalBits,hdecode,cfg]

namespace Fixtures
example : literalBits [true,false,false,true] = some ([false],true) := by decide
example : literalBits [true,false,true,true,false,false] = some ([false,true],false) := by decide
example : literalBits [false] = none := by decide
example : literalBits [false,true,false] = none := by decide
example : (runSteps machine.step 6 (Turing.initList machine [false,true])).map
    (fun q => ((match q.l with | some (.inr .accept) => true | _ => false),q.stk .payload)) = some (true,([] : List Bool)) := by
  change (Option.map (fun q => ((match q.l with | some (.inr .accept) => true | _ => false),q.stk .payload))
    (runSteps machine.step 6 (Turing.initList machine [false,true])) : Option (Bool × List Bool)) = _
  decide
example : (runSteps machine.step 5 (Turing.initList machine [false])).map
    (fun q => (match q.l with | some (.inr .reject) => true | _ => false)) = some true := by
  change (Option.map (fun q => (match q.l with | some (.inr .reject) => true | _ => false))
    (runSteps machine.step 5 (Turing.initList machine [false])) : Option Bool) = _
  decide
end Fixtures

end Shared.ComplexityBridge.TM2LiteralParse
