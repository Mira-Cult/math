import Shared.ComplexityBridge.TM2BooleanInput
import Shared.Codes.TM2Program

/-! Primitive recursiveness for a fixed finite numeric TM2 program.

The statement and program are parameters of the proof, not inputs of a
uniform interpreter. `TM2Primcodable` separately proves computability of the
serialized program decoder; a polynomial bit-cost simulation is still open. Fuel counts complete
TM2 statement blocks. -/
set_option maxHeartbeats 300000

namespace Shared.Codes.TM2FixedComputability
open Shared.Codes.TM2Statements Shared.Codes.TM2StatementExecution Shared.Codes.FiniteTables
open Shared.ComplexityBridge.TM2BooleanInput
open Shared.Codes.TM2Program

abbrev Arg := Nat × Stacks

def execRaw : Code → Arg → Option ResultRaw
  | .halt, (v,s) => some (none,v,s)
  | .goto t, (v,s) => (lookup t v).map fun l => (some l,v,s)
  | .push k t q, (v,s) => do
      let stk ← s[k]?
      let x ← lookup t v
      execRaw q (v,s.set k (x::stk))
  | .peek k t q, (v,s) => do
      let stk ← s[k]?
      let x ← lookup₂ t v (symbolIndex stk.head?)
      execRaw q (x,s)
  | .pop k t q, (v,s) => do
      let stk ← s[k]?
      let x ← lookup₂ t v (symbolIndex stk.head?)
      execRaw q (x,s.set k stk.tail)
  | .load t q, (v,s) => do
      let x ← lookup t v
      execRaw q (x,s)
  | .branch t yes no, (v,s) => do
      let x ← lookup t v
      let b ← boolOfNat x
      if b then execRaw yes (v,s) else execRaw no (v,s)

theorem symbolIndex_primrec : Primrec symbolIndex := by
  have h := Primrec.option_casesOn (Primrec.id : Primrec (fun x : Option Nat => x))
    (Primrec.const 0) (Primrec.succ.comp Primrec.snd).to₂
  exact h.of_eq (by intro x; cases x <;> rfl)

theorem boolOfNat_primrec : Primrec boolOfNat := by
  have h := Primrec.ite (Primrec.eq.comp (Primrec.id : Primrec (fun n : Nat => n)) (Primrec.const 0))
    (Primrec.const (some false))
    (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 1)) (Primrec.const (some true))
      (Primrec.const (none : Option Bool)))
  apply h.of_eq
  intro n
  cases n with
  | zero => rfl
  | succ n => cases n <;> rfl

theorem execRaw_eq (q : Code) (v : Nat) (s : Stacks) :
    execRaw q (v,s) = (exec q v s).map resultRaw := by
  induction q generalizing v s with
  | halt => rfl
  | goto t => cases ht : lookup t v <;> simp [execRaw, exec, resultRaw, ht]
  | push k t q ih =>
    cases hs : s[k]? with
    | none => simp [execRaw, exec, hs]
    | some stk => cases ht : lookup t v <;> simp [execRaw, exec, hs, ht, ih]
  | peek k t q ih =>
    cases hs : s[k]? with
    | none => simp [execRaw, exec, hs]
    | some stk => cases ht : lookup₂ t v (symbolIndex stk.head?) <;> simp [execRaw, exec, hs, ht, ih]
  | pop k t q ih =>
    cases hs : s[k]? with
    | none => simp [execRaw, exec, hs]
    | some stk => cases ht : lookup₂ t v (symbolIndex stk.head?) <;> simp [execRaw, exec, hs, ht, ih]
  | load t q ih => cases ht : lookup t v <;> simp [execRaw, exec, ht, ih]
  | branch t a b iha ihb =>
    cases ht : lookup t v with
    | none => simp [execRaw, exec, ht]
    | some x =>
      cases hb : boolOfNat x with
      | none => simp [execRaw, exec, ht, hb]
      | some y => cases y <;> simp [execRaw, exec, ht, hb, iha, ihb]

theorem execRaw_primrec (q : Code) : Primrec (execRaw q) := by
  induction q with
  | halt =>
    exact Primrec.option_some.comp (Primrec.pair (Primrec.const none) (Primrec.pair Primrec.fst Primrec.snd))
  | goto t =>
    have hlookup : Primrec (fun a : Arg => lookup t a.1) := lookup_primrec.comp (Primrec.const t) Primrec.fst
    have hresult : Primrec₂ (fun (a : Arg) (l : Nat) => ((some l, a.1, a.2) : ResultRaw)) :=
      (Primrec.pair (Primrec.option_some.comp Primrec.snd)
        (Primrec.pair (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))).to₂
    exact Primrec.option_map hlookup hresult
  | load t q ih =>
    have ht : Primrec (fun a : Arg => lookup t a.1) := lookup_primrec.comp (Primrec.const t) Primrec.fst
    have hb : Primrec₂ (fun (a : Arg) (x : Nat) => execRaw q (x,a.2)) :=
      (ih.comp (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst))).to₂
    exact Primrec.option_bind ht hb
  | push k t q ih =>
    have hs : Primrec (fun a : Arg => a.2[k]?) := Primrec.list_getElem?.comp Primrec.snd (Primrec.const k)
    have ht : Primrec (fun p : Arg × List Nat => lookup t p.1.1) :=
      lookup_primrec.comp (Primrec.const t) (Primrec.fst.comp Primrec.fst)
    have hm : Primrec (fun p : (Arg × List Nat) × Nat => p.1.1.2.set k (p.2 :: p.1.2)) :=
      Primrec.list_set.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.pair (Primrec.const k) (Primrec.list_cons.comp Primrec.snd (Primrec.snd.comp Primrec.fst)))
    have hb : Primrec₂ (fun (p : Arg × List Nat) (x : Nat) => execRaw q (p.1.1,p.1.2.set k (x::p.2))) :=
      (ih.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) hm)).to₂
    have h := Primrec.option_bind hs (Primrec.option_bind ht hb).to₂
    exact h
  | peek k t q ih =>
    have hs : Primrec (fun a : Arg => a.2[k]?) := Primrec.list_getElem?.comp Primrec.snd (Primrec.const k)
    have hi : Primrec (fun p : Arg × List Nat => symbolIndex p.2.head?) :=
      symbolIndex_primrec.comp (Primrec.list_head?.comp Primrec.snd)
    have ht : Primrec (fun p : Arg × List Nat => lookup₂ t p.1.1 (symbolIndex p.2.head?)) :=
      lookup₂_primrec.comp (Primrec.pair (Primrec.pair (Primrec.const t) (Primrec.fst.comp Primrec.fst)) hi)
    have hb : Primrec₂ (fun (p : Arg × List Nat) (x : Nat) => execRaw q (x,p.1.2)) :=
      (ih.comp (Primrec.pair Primrec.snd (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))).to₂
    exact Primrec.option_bind hs (Primrec.option_bind ht hb).to₂
  | pop k t q ih =>
    have hs : Primrec (fun a : Arg => a.2[k]?) := Primrec.list_getElem?.comp Primrec.snd (Primrec.const k)
    have hi : Primrec (fun p : Arg × List Nat => symbolIndex p.2.head?) :=
      symbolIndex_primrec.comp (Primrec.list_head?.comp Primrec.snd)
    have ht : Primrec (fun p : Arg × List Nat => lookup₂ t p.1.1 (symbolIndex p.2.head?)) :=
      lookup₂_primrec.comp (Primrec.pair (Primrec.pair (Primrec.const t) (Primrec.fst.comp Primrec.fst)) hi)
    have hm : Primrec (fun p : (Arg × List Nat) × Nat => p.1.1.2.set k p.1.2.tail) :=
      Primrec.list_set.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.pair (Primrec.const k) (Primrec.list_tail.comp (Primrec.snd.comp Primrec.fst)))
    have hb : Primrec₂ (fun (p : Arg × List Nat) (x : Nat) => execRaw q (x,p.1.2.set k p.2.tail)) :=
      (ih.comp (Primrec.pair Primrec.snd hm)).to₂
    exact Primrec.option_bind hs (Primrec.option_bind ht hb).to₂
  | branch t a b iha ihb =>
    have ht : Primrec (fun a : Arg => lookup t a.1) := lookup_primrec.comp (Primrec.const t) Primrec.fst
    have hc : Primrec (fun p : Arg × Nat => boolOfNat p.2) := boolOfNat_primrec.comp Primrec.snd
    have hbranch : Primrec₂ (fun (p : Arg × Nat) (v : Bool) => if v then execRaw a p.1 else execRaw b p.1) := by
      have h := Primrec.cond (Primrec.snd : Primrec (fun p : (Arg × Nat) × Bool => p.2))
        (iha.comp (Primrec.fst.comp (Primrec.fst))) (ihb.comp (Primrec.fst.comp (Primrec.fst)))
      apply h.to₂.of_eq
      intro p v
      cases v <;> rfl
    exact Primrec.option_bind ht (Primrec.option_bind hc hbranch).to₂

/-- Dispatch is primitive recursive when the finite program is fixed. -/
def dispatch : List Code → Nat → Arg → Option ResultRaw
  | [], _, _ => none
  | q :: _, 0, a => execRaw q a
  | _ :: qs, n + 1, a => dispatch qs n a

theorem dispatch_primrec (p : List Code) : Primrec (fun x : Nat × Arg => dispatch p x.1 x.2) := by
  induction p with
  | nil => exact Primrec.const none
  | cons q qs ih =>
    have hz : Primrec (fun x : Nat × Arg => execRaw q x.2) := (execRaw_primrec q).comp Primrec.snd
    have hn : Primrec₂ (fun (x : Nat × Arg) (n : Nat) => dispatch qs n x.2) :=
      (ih.comp (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst))).to₂
    have h := Primrec.nat_casesOn (Primrec.fst : Primrec (fun x : Nat × Arg => x.1)) hz hn
    apply h.of_eq
    intro x
    rcases x with ⟨n,a⟩
    cases n <;> rfl

theorem dispatch_eq (p : List Code) (l : Nat) (v : Nat) (s : Stacks) :
    dispatch p l (v,s) = ((p[l]?).bind fun q => (exec q v s).map resultRaw) := by
  induction p generalizing l with
  | nil => simp [dispatch]
  | cons q qs ih =>
    cases l with
    | zero => simp [dispatch, execRaw_eq]
    | succ l => simpa [dispatch] using ih l

abbrev Status := Option (Bool × ResultRaw)

def initial (r : ResultRaw) : Status := some (r.1.isNone, r)

def advance (p : List Code) : Status → Status
  | none => none
  | some (true, r) => some (true, r)
  | some (false, r) =>
    match r.1 with
    | none => some (true, r)
    | some l => (dispatch p l (r.2.1,r.2.2)).map fun (d : ResultRaw) => (d.1.isNone,d)

def runRaw (p : List Code) (fuel : Nat) (r : ResultRaw) : Status :=
  (advance p)^[fuel] (initial r)

theorem initial_primrec : Primrec initial := by
  have h : Primrec (fun r : ResultRaw => !r.1.isSome) := Primrec.not.comp (Primrec.option_isSome.comp Primrec.fst)
  have hh := Primrec.option_some.comp (Primrec.pair h Primrec.id)
  apply hh.of_eq
  intro r
  rcases r with ⟨o,v,s⟩
  cases o <;> rfl

theorem advance_primrec (p : List Code) : Primrec (advance p) := by
  have hd : Primrec (fun r : ResultRaw => dispatch p (r.1.getD 0) (r.2.1,r.2.2)) := by
    have hl : Primrec (fun r : ResultRaw => r.1.getD 0) := Primrec.option_getD.comp Primrec.fst (Primrec.const 0)
    exact (dispatch_primrec p).comp (Primrec.pair hl Primrec.snd)
  have hi : Primrec (fun r : ResultRaw => (r.1.isNone,r)) := by
    have h := Primrec.pair (Primrec.not.comp (Primrec.option_isSome.comp (Primrec.fst : Primrec (fun r : ResultRaw => r.1)))) Primrec.id
    apply h.of_eq
    intro r
    cases r.1 <;> rfl
  have hm : Primrec (fun r : ResultRaw => (dispatch p (r.1.getD 0) (r.2.1,r.2.2)).map (fun (d : ResultRaw) => (d.1.isNone,d))) :=
    Primrec.option_map hd (hi.comp Primrec.snd).to₂
  have hn : Primrec (fun r : ResultRaw => match r.1 with
      | none => some (true,r)
      | some l => (dispatch p l (r.2.1,r.2.2)).map fun (d : ResultRaw) => (d.1.isNone,d)) := by
    have h := Primrec.option_casesOn (Primrec.fst : Primrec (fun r : ResultRaw => r.1))
      (Primrec.option_some.comp (Primrec.pair (Primrec.const true) Primrec.id))
      (hm.comp Primrec.fst).to₂
    apply h.of_eq
    intro r
    rcases r with ⟨o,v,s⟩
    cases o <;> rfl
  have hb : Primrec (fun x : Bool × ResultRaw => if x.1 then some (true,x.2) else
      match x.2.1 with
      | none => some (true,x.2)
      | some l => (dispatch p l (x.2.2.1,x.2.2.2)).map fun (d : ResultRaw) => (d.1.isNone,d)) := by
    have h := Primrec.cond (Primrec.fst : Primrec (fun x : Bool × ResultRaw => x.1))
      (Primrec.option_some.comp (Primrec.pair (Primrec.const true) Primrec.snd)) (hn.comp Primrec.snd)
    apply h.of_eq
    intro x
    cases x.1 <;> rfl
  have h := Primrec.option_casesOn (Primrec.id : Primrec (fun x : Status => x)) (Primrec.const none)
    (hb.comp Primrec.snd).to₂
  apply h.of_eq
  intro x
  cases x with
  | none => rfl
  | some x => rcases x with ⟨b,r⟩; cases b <;> rfl

theorem runRaw_primrec (p : List Code) : Primrec (fun x : Nat × ResultRaw => runRaw p x.1 x.2) := by
  have h := Primrec.nat_iterate (Primrec.fst : Primrec (fun x : Nat × ResultRaw => x.1))
    (initial_primrec.comp Primrec.snd) ((advance_primrec p).comp Primrec.snd).to₂
  exact h

def outcomeRaw : Outcome → Status
  | .invalid => none
  | .timeout r => some (false,resultRaw r)
  | .halted r => some (true,resultRaw r)

theorem runRaw_eq (p : List Code) (fuel : Nat) (c : Result) :
    runRaw p fuel (resultRaw c) = outcomeRaw (run p fuel c) := by
  induction fuel generalizing c with
  | zero =>
    cases hl : c.label <;> simp [runRaw, initial, resultRaw, run, outcomeRaw, hl]
  | succ n ih =>
    rw [runRaw, Function.iterate_succ_apply]
    cases hl : c.label with
    | none =>
      have hfix : advance p (some (true, resultRaw c)) = some (true, resultRaw c) := rfl
      simpa [initial, advance, resultRaw, hl, run, outcomeRaw] using Function.iterate_fixed hfix n
    | some l =>
      cases hq : p[l]? with
      | none =>
        have hfix : advance p none = none := rfl
        simpa [initial, advance, resultRaw, hl, dispatch_eq, hq, run, outcomeRaw] using Function.iterate_fixed hfix n
      | some q =>
        cases he : exec q c.state c.memory with
        | none =>
          have hfix : advance p none = none := rfl
          simpa [initial, advance, resultRaw, hl, dispatch_eq, hq, he, run, outcomeRaw] using Function.iterate_fixed hfix n
        | some d =>
          simpa [initial, advance, resultRaw, hl, dispatch_eq, hq, he, run, runRaw] using ih d

example : runRaw [.halt] 0 (some 0,0,[]) = some (false,(some 0,0,[])) := by decide
example : runRaw [.halt] 1 (some 0,0,[]) = some (true,(none,0,[])) := by decide
example : runRaw [] 1 (some 0,0,[]) = none := by decide
example : runRaw [.goto []] 1 (some 0,0,[]) = none := by decide
example : runRaw [.goto [0]] 3 (some 0,0,[]) = some (false,(some 0,0,[])) := by decide

end Shared.Codes.TM2FixedComputability
