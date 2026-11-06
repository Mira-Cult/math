import Shared.PNP.TM2Candidate
import Shared.Beeping.ComparisonImplementation
import Shared.ComplexityBridge.TM2Cleanup

namespace Shared.ComplexityBridge.TM2Whole
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.ComplexityBridge.TM2Combined
open Shared.ComplexityBridge.TM2Cleanup Shared.ComplexityBridge.TM2FiniteReverse
open Shared.Codes.TM2Program Shared.Codes.TM2StatementExecution
open Shared.Codes.TM2Micro Shared.Codes.TM2FixedComputability
open Shared.ComplexityBridge.TM2BooleanInput Shared.ComplexityBridge.TM2FiniteBoundary
open Shared.ComplexityBridge.TM2BooleanOutput Shared.ComplexityBridge.TM2StackBound

abbrev RunLabel (p : Program) := Bool ⊕ Fin (p.length+1)
abbrev CleanLabel (ks : Nat) := Unit ⊕ Fin (ks+2)
abbrev Label (ks : Nat) (p : Program) := Unit ⊕ (RunLabel p ⊕ CleanLabel ks)
abbrev RunState (states : Nat) := Option Bool × Fin (states+1)
abbrev CleanState (states : Nat) := Bool × Fin (states+1) × Bool
abbrev State (states : Nat) := RunState states ⊕ CleanState states

def runState (states initial : Nat) : State states → RunState states
  | .inl v => v
  | .inr _ => (none,clip states initial)

def cleanState (states initial : Nat) : State states → CleanState states
  | .inl _ => (false,clip states initial,false)
  | .inr v => v

def runLabel {ks : Nat} {p : Program} (l : RunLabel p) : Label ks p := .inr (.inl l)
def cleanLabel {ks : Nat} {p : Program} (l : CleanLabel ks) : Label ks p := .inr (.inr l)

abbrev RunStmt (ks states symbols : Nat) (p : Program) :=
  Stmt (Alphabet ks symbols) (RunLabel p) (RunState states)
abbrev CleanStmt (ks states symbols : Nat) :=
  Stmt (Alphabet ks symbols) (CleanLabel ks) (CleanState states)

def liftRun (ks states symbols initial : Nat) (p : Program) : RunStmt ks states symbols p →
    Stmt (Alphabet ks symbols) (Label ks p) (State states)
  | .push k f q => .push k (fun s => f (runState states initial s)) (liftRun ks states symbols initial p q)
  | .peek k f q => .peek k (fun s x => .inl (f (runState states initial s) x)) (liftRun ks states symbols initial p q)
  | .pop k f q => .pop k (fun s x => .inl (f (runState states initial s) x)) (liftRun ks states symbols initial p q)
  | .load f q => .load (fun s => .inl (f (runState states initial s))) (liftRun ks states symbols initial p q)
  | .branch f a b => .branch (fun s => f (runState states initial s)) (liftRun ks states symbols initial p a) (liftRun ks states symbols initial p b)
  | .goto f => .goto (fun s => runLabel (f (runState states initial s)))
  | .halt => .load (fun s => .inr (false,(runState states initial s).2,false))
      (.goto (fun _ => cleanLabel (.inl ())))

def liftClean (ks states symbols initial : Nat) (p : Program) : CleanStmt ks states symbols →
    Stmt (Alphabet ks symbols) (Label ks p) (State states)
  | .push k f q => .push k (fun s => f (cleanState states initial s)) (liftClean ks states symbols initial p q)
  | .peek k f q => .peek k (fun s x => .inr (f (cleanState states initial s) x)) (liftClean ks states symbols initial p q)
  | .pop k f q => .pop k (fun s x => .inr (f (cleanState states initial s) x)) (liftClean ks states symbols initial p q)
  | .load f q => .load (fun s => .inr (f (cleanState states initial s))) (liftClean ks states symbols initial p q)
  | .branch f a b => .branch (fun s => f (cleanState states initial s)) (liftClean ks states symbols initial p a) (liftClean ks states symbols initial p b)
  | .goto f => .goto (fun s => cleanLabel (f (cleanState states initial s)))
  | .halt => .halt

def runEmbed (ks states symbols : Nat) (p : Program)
    (c : Cfg (Alphabet ks symbols) (RunLabel p) (RunState states)) :
    Cfg (Alphabet ks symbols) (Label ks p) (State states) :=
  match c.l with
  | some l => ⟨some (runLabel l),.inl c.var,c.stk⟩
  | none => ⟨some (cleanLabel (.inl ())),.inr (false,c.var.2,false),c.stk⟩

def cleanEmbed (ks states symbols : Nat) (p : Program)
    (c : Cfg (Alphabet ks symbols) (CleanLabel ks) (CleanState states)) :
    Cfg (Alphabet ks symbols) (Label ks p) (State states) :=
  ⟨c.l.map cleanLabel,.inr c.var,c.stk⟩

/-- A halted candidate block enters cleanup in the very same block. -/
theorem liftRun_stepAux (ks states symbols initial : Nat) (p : Program)
    (q : RunStmt ks states symbols p) (v : RunState states)
    (S : (k : Bool ⊕ Fin (ks+1)) → List (Alphabet ks symbols k)) :
    stepAux (liftRun ks states symbols initial p q) (.inl v) S =
      runEmbed ks states symbols p (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | push k f q ih => exact ih v _
  | peek k f q ih => exact ih _ S
  | pop k f q ih => exact ih _ _
  | load f q ih => exact ih _ S
  | branch f a b iha ihb => by_cases h : f v <;> simp [liftRun,stepAux,runState,h,iha,ihb]

theorem liftClean_stepAux (ks states symbols initial : Nat) (p : Program)
    (q : CleanStmt ks states symbols) (v : CleanState states)
    (S : (k : Bool ⊕ Fin (ks+1)) → List (Alphabet ks symbols k)) :
    stepAux (liftClean ks states symbols initial p q) (.inr v) S =
      cleanEmbed ks states symbols p (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | push k f q ih => exact ih v _
  | peek k f q ih => exact ih _ S
  | pop k f q ih => exact ih _ _
  | load f q ih => exact ih _ S
  | branch f a b iha ihb => by_cases h : f v <;> simp [liftClean,stepAux,cleanState,h,iha,ihb]

def wholeProgram (ks states symbols : Nat) (p : Program)
    (input output main initial z inOne one : Nat) : Label ks p → Stmt (Alphabet ks symbols) (Label ks p) (State states)
  | .inl () => .load (fun _ => .inl (none,clip states initial))
      (.goto (fun _ => runLabel (.inl false)))
  | .inr (.inl l) => liftRun ks states symbols initial p
      (Shared.ComplexityBridge.TM2Combined.program ks states symbols p input main z inOne l)
  | .inr (.inr l) => liftClean ks states symbols initial p
      (outputProgram ks states symbols initial output one l)

def whole (ks states symbols : Nat) (p : Program) (input output main initial z inOne one : Nat) : Turing.FinTM2 where
  K := Bool ⊕ Fin (ks+1)
  k₀ := .inl false
  k₁ := .inl true
  Γ := Alphabet ks symbols
  Λ := Label ks p
  main := .inl ()
  σ := State states
  initialState := .inr (false,clip states initial,false)
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := wholeProgram ks states symbols p input output main initial z inOne one

set_option backward.isDefEq.respectTransparency false in
/-- Every active candidate block is simulated once. Its halt block redirects
to the output-cleaning prelude instead of terminating the whole machine. -/
theorem candidate_step (ks states symbols : Nat) (p : Program) (input output main initial z inOne one : Nat)
    (c : (machine ks states symbols p input output main initial z inOne).Cfg) (hactive : c.l ≠ none) :
    (whole ks states symbols p input output main initial z inOne one).step (runEmbed ks states symbols p c) =
      ((machine ks states symbols p input output main initial z inOne).step c).map (runEmbed ks states symbols p) := by
  cases c with
  | mk l v S =>
    cases l with
    | none => contradiction
    | some l =>
      change some (stepAux (liftRun ks states symbols initial p
        (Shared.ComplexityBridge.TM2Combined.program ks states symbols p input main z inOne l)) (.inl v) S) = _
      rw [liftRun_stepAux]
      rfl

set_option backward.isDefEq.respectTransparency false in
/-- Every successful finite run of the original candidate machine is mirrored,
including a final candidate halt being redirected into cleanup. -/
theorem candidate_run (ks states symbols : Nat) (p : Program) (input output main initial z inOne one : Nat)
    (n : Nat) (c d : (machine ks states symbols p input output main initial z inOne).Cfg)
    (h : runSteps (machine ks states symbols p input output main initial z inOne).step n c = some d) :
    runSteps (whole ks states symbols p input output main initial z inOne one).step n (runEmbed ks states symbols p c) =
      some (runEmbed ks states symbols p d) := by
  induction n generalizing c with
  | zero =>
    change some c = some d at h
    cases h
    rfl
  | succ n ih =>
    rw [runSteps_front] at h
    change ((machine ks states symbols p input output main initial z inOne).step c).bind
      (runSteps (machine ks states symbols p input output main initial z inOne).step n) = some d at h
    cases hs : (machine ks states symbols p input output main initial z inOne).step c with
    | none =>
      rw [hs] at h
      contradiction
    | some c' =>
      have hactive : c.l ≠ none := by
        intro hl
        have hn : (machine ks states symbols p input output main initial z inOne).step c = none := by
          cases c with
          | mk l v S => cases l with
            | none => rfl
            | some l => simp at hl
        rw [hn] at hs
        contradiction
      have hh : runSteps (machine ks states symbols p input output main initial z inOne).step n c' = some d := by
        rw [hs] at h
        exact h
      rw [runSteps_front, candidate_step ks states symbols p input output main initial z inOne one c hactive, hs]
      exact ih c' hh

set_option backward.isDefEq.respectTransparency false in
/-- The cleanup phase is simulated exactly, including its ordinary halt. -/
theorem cleanup_step (ks states symbols : Nat) (p : Program) (input output main initial z inOne one : Nat)
    (c : (outputCleaner ks states symbols initial output one).Cfg) :
    (whole ks states symbols p input output main initial z inOne one).step (cleanEmbed ks states symbols p c) =
      ((outputCleaner ks states symbols initial output one).step c).map (cleanEmbed ks states symbols p) := by
  cases c with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l =>
      change some (stepAux (liftClean ks states symbols initial p (outputProgram ks states symbols initial output one l)) (.inr v) S) = _
      rw [liftClean_stepAux]
      rfl

set_option backward.isDefEq.respectTransparency false in
theorem cleanup_run (ks states symbols : Nat) (p : Program) (input output main initial z inOne one : Nat)
    (n : Nat) (c : (outputCleaner ks states symbols initial output one).Cfg) :
    runSteps (whole ks states symbols p input output main initial z inOne one).step n (cleanEmbed ks states symbols p c) =
      (runSteps (outputCleaner ks states symbols initial output one).step n c).map (cleanEmbed ks states symbols p) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [runSteps_front, runSteps_front, cleanup_step]
    cases h : (outputCleaner ks states symbols initial output one).step c with
    | none => rfl
    | some c' => exact ih c'

/-- The one-block startup leaves the input untouched and selects candidate
mode, while the whole machine's initial state remains the cleanup reset state. -/
theorem startup (ks states symbols : Nat) (p : Program) (input output main initial z inOne one : Nat)
    (bits : List Bool) :
    (whole ks states symbols p input output main initial z inOne one).step
      (Turing.initList (whole ks states symbols p input output main initial z inOne one) bits) =
        some (runEmbed ks states symbols p
          (Turing.initList (machine ks states symbols p input output main initial z inOne) bits)) := by
  change some (Cfg.mk (some (runLabel (.inl false) : Label ks p)) (.inl (none,clip states initial) : State states) _) =
    some (Cfg.mk (some (runLabel (.inl false) : Label ks p)) (.inl (none,clip states initial) : State states) _)
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- At candidate halt the redirect has exactly the cleanup prelude's data and
control state. No stacks are preloaded or discarded. -/
theorem handoff (ks states symbols : Nat) (p : Program) (input output main initial z inOne one : Nat)
    (c : (machine ks states symbols p input output main initial z inOne).Cfg)
    (hl : c.l = none) (hin : c.stk (.inl false) = []) (hscratch : c.stk (.inl true) = []) :
    runEmbed ks states symbols p c = cleanEmbed ks states symbols p
      (fetchCfg ks states symbols initial output one c.var.2 false (fun k => c.stk (.inr k))) := by
  cases c with
  | mk l v S =>
    cases l with
    | some l => contradiction
    | none =>
      change Cfg.mk (some (cleanLabel (.inl ()) : Label ks p)) (.inr (false,v.2,false) : State states) S =
        Cfg.mk (some (cleanLabel (.inl ()) : Label ks p)) (.inr (false,v.2,false) : State states)
          (embedStacks ks symbols [] [] (fun k => S (.inr k)))
      congr 1
      funext k
      cases k with
      | inl b =>
        cases b with
        | false => exact hin
        | true => exact hscratch
      | inr j => rfl

/-- Cleanup ends at the whole machine's actual Boolean halt configuration. -/
theorem final_halt (ks states symbols : Nat) (p : Program) (input output main initial z inOne one : Nat) (b : Bool) :
    cleanEmbed ks states symbols p (Turing.haltList (outputCleaner ks states symbols initial output one) [b]) =
      Turing.haltList (whole ks states symbols p input output main initial z inOne one) [b] := by
  change Cfg.mk none (.inr (false,clip states initial,false) : State states) _ =
    Cfg.mk none (.inr (false,clip states initial,false) : State states) _
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- A successful validated numeric run is implemented by one finite machine
from `initList` to the exact Boolean `haltList`, including startup, input
loading, computation, output decoding, all stack cleanup, and state reset. -/
theorem numeric_run_complete (d : Shared.ComplexityBridge.TM2BooleanInput.InputData)
    (p : Program) (output zcode one : Nat) (bits : List Bool) (fuel : Nat)
    (start r : Result) (b : Bool)
    (hdata : Shared.ComplexityBridge.TM2BooleanInput.validInputData d = true) (hmain : d.main < p.length)
    (hp : programValid p d.stackCount d.states d.symbols = true)
    (hstart : Shared.ComplexityBridge.TM2BooleanInput.buildStart d bits = some start)
    (hrun : run p fuel start = .halted r)
    (he : Shared.ComplexityBridge.TM2BooleanOutput.extractMemory (zcode,one,output,r.label,r.memory) = some b) :
    ∃ t ≤ 1 + (2*bits.length+2+fuel) +
      ((d.stackCount+1)*(bits.length + fuel * Shared.ComplexityBridge.TM2StackBound.programDepth p + 1)+2),
      runSteps (whole d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState
        d.falseSymbol d.trueSymbol one).step t
        (Turing.initList (whole d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState
          d.falseSymbol d.trueSymbol one) bits) =
        some (Turing.haltList (whole d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState
          d.falseSymbol d.trueSymbol one) [b]) := by
  obtain ⟨n,hn,c,hcand,hl,hin,hscratch,t,ht,hclean⟩ :=
    numeric_run_then_cleanup d p output zcode one bits fuel start r b hdata hmain hp hstart hrun he
  let wc := whole d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol one
  let mc := machine d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol
  let cc := outputCleaner d.stackCount d.states d.symbols d.initialState output one
  have hs : runSteps wc.step 1 (Turing.initList wc bits) = some (runEmbed d.stackCount d.states d.symbols p (Turing.initList mc bits)) := by
    change wc.step (Turing.initList wc bits) = _
    exact startup d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol one bits
  have hc := candidate_run d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol one
    (2*bits.length+2+n) (Turing.initList mc bits) c hcand
  rw [handoff d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol one c hl hin hscratch] at hc
  have hq := cleanup_run d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol one t
    (fetchCfg d.stackCount d.states d.symbols d.initialState output one c.var.2 false (fun k => c.stk (.inr k)))
  rw [hclean] at hq
  change runSteps wc.step t (cleanEmbed d.stackCount d.states d.symbols p
      (fetchCfg d.stackCount d.states d.symbols d.initialState output one c.var.2 false (fun k => c.stk (.inr k)))) =
      some (cleanEmbed d.stackCount d.states d.symbols p (Turing.haltList cc [b])) at hq
  rw [final_halt] at hq
  refine ⟨(1+(2*bits.length+2+n))+t,by omega,?_⟩
  rw [runSteps_add,runSteps_add,hs]
  change (runSteps wc.step (2*bits.length+2+n) (runEmbed d.stackCount d.states d.symbols p (Turing.initList mc bits))).bind _ = _
  rw [hc]
  exact hq

/-- Recover the actual numeric halted result from a successful checked
candidate evaluation. -/
theorem checked_numeric_result (c : Shared.Codes.TM2Candidate.Candidate) (p : Program)
    (hdecode : decodeProgram c.1.1 = some p) (x : List Bool) (b : Bool)
    (heval : Shared.Codes.TM2CheckedCandidate.evaluate c x = some b) :
    let d := inputDataOfRaw c.1.2.2
    validInputData d = true ∧ d.main < p.length ∧ programValid p d.stackCount d.states d.symbols = true ∧
    ∃ start r, buildStart d (BitstringEncoding.bitEncode x) = some start ∧
      run p ((x.length+2)^c.1.2.1) start = .halted r ∧
      extractMemory (c.2.1,c.2.2.1,c.2.2.2,r.label,r.memory) = some b := by
  let d := inputDataOfRaw c.1.2.2
  have he : Shared.Codes.TM2CheckedCandidate.evaluate
      ((c.1.1,c.1.2.1,inputRaw d),(c.2.1,c.2.2.1,c.2.2.2)) x = some b := by
    simpa [d] using heval
  obtain ⟨hdata,p',hdecode',hp⟩ := checked_evaluate_validation d c.1.1 c.1.2.1 c.2.1 c.2.2.1 c.2.2.2 x b he
  have hp' : p' = p := Option.some.inj (hdecode'.symm.trans hdecode)
  subst p'
  have hmain := checked_evaluate_main_in_range d p c.1.1 c.1.2.1 c.2.1 c.2.2.1 c.2.2.2 hdata hdecode x b he
  obtain ⟨start,hstart,hvalid⟩ := buildStart_valid d (BitstringEncoding.bitEncode x) p hdata hmain
  have hin : Shared.ComplexityBridge.TM2RawInput.buildDecisionInput (inputRaw d,x) = some (resultRaw start) := by
    change buildRaw (inputRaw d,BitstringEncoding.bitEncode x) = _
    rw [buildRaw_eq, hstart]
    rfl
  have hcandidate : Shared.Codes.TM2CheckedCandidate.candidateValid
      ((c.1.1,c.1.2.1,inputRaw d),(c.2.1,c.2.2.1,c.2.2.2)) = true := by
    simpa [Shared.Codes.TM2CheckedCandidate.candidateValid, hdecode, inputRaw] using hp
  have heval' : Shared.Codes.TM2Candidate.evaluate
      ((c.1.1,c.1.2.1,inputRaw d),(c.2.1,c.2.2.1,c.2.2.2)) x = some b := by
    simpa [Shared.Codes.TM2CheckedCandidate.evaluate, hcandidate] using he
  have hrun := runEncoded_of_decode c.1.1 p ((x.length+2)^c.1.2.1) start hdecode
  unfold Shared.Codes.TM2Candidate.evaluate at heval'
  rw [hin] at heval'
  change (runEncoded ((c.1.1,(x.length+2)^c.1.2.1), resultRaw start)).bind (fun v =>
    if v.1 then extractMemory (c.2.1,c.2.2.1,c.2.2.2,v.2.1,v.2.2.2) else none) = some b at heval'
  rw [hrun] at heval'
  cases hr : run p ((x.length+2)^c.1.2.1) start with
  | invalid => simp [hr, outcomeRaw] at heval'
  | timeout r => simp [hr, outcomeRaw] at heval'
  | halted r =>
    have hout : extractMemory (c.2.1,c.2.2.1,c.2.2.2,r.label,r.memory) = some b := by
      simpa [hr, outcomeRaw, resultRaw] using heval'
    exact ⟨hdata,hmain,hp,start,r,hstart,hr,hout⟩

/-- A fixed candidate has a fixed polynomial bound in the length of the
actual library-encoded input. -/
noncomputable def timePolynomial (stackCount exponent : Nat) (p : Program) : Polynomial Nat :=
  let n := Polynomial.X
  let clock := (n + Polynomial.C 2)^exponent
  Polynomial.C 1 + (Polynomial.C 2*n + Polynomial.C 2 + clock) +
    (Polynomial.C (stackCount+1)*(n+clock*Polynomial.C (programDepth p)+Polynomial.C 1)+Polynomial.C 2)

theorem timePolynomial_eval (stackCount exponent : Nat) (p : Program) (n : Nat) :
    (timePolynomial stackCount exponent p).eval n =
      1 + (2*n+2+(n+2)^exponent) + ((stackCount+1)*(n+(n+2)^exponent*programDepth p+1)+2) := by
  simp [timePolynomial]

/-- Successful checked evaluation is reproduced by one Boolean-input and
Boolean-output TM2 within a fixed polynomial of encoded input length. -/
theorem checked_whole_run (c : Shared.Codes.TM2Candidate.Candidate) (p : Program)
    (hdecode : decodeProgram c.1.1 = some p) (x : List Bool) (b : Bool)
    (heval : Shared.Codes.TM2CheckedCandidate.evaluate c x = some b) :
    let d := inputDataOfRaw c.1.2.2
    let w := whole d.stackCount d.states d.symbols p d.inputStack c.2.2.2 d.main d.initialState
      d.falseSymbol d.trueSymbol c.2.2.1
    ∃ t ≤ (timePolynomial d.stackCount c.1.2.1 p).eval (BitstringEncoding.bitEncode x).length,
      runSteps w.step t (Turing.initList w (BitstringEncoding.bitEncode x)) = some (Turing.haltList w [b]) := by
  let d := inputDataOfRaw c.1.2.2
  obtain ⟨hdata,hmain,hp,start,r,hstart,hrun,hout⟩ := checked_numeric_result c p hdecode x b heval
  obtain ⟨t,ht,hr⟩ := numeric_run_complete d p c.2.2.2 c.2.1 c.2.2.1 (BitstringEncoding.bitEncode x)
    ((x.length+2)^c.1.2.1) start r b hdata hmain hp hstart hrun hout
  let m := (BitstringEncoding.bitEncode x).length
  have hsize : x.length ≤ m := by
    dsimp [m]
    rw [Shared.ComplexityBridge.bitstring_list_encoded_length]
    omega
  have hclock : (x.length+2)^c.1.2.1 ≤ (m+2)^c.1.2.1 := Nat.pow_le_pow_left (by omega) _
  have hprod := Nat.mul_le_mul_right (programDepth p) hclock
  have hinner : m + (x.length+2)^c.1.2.1 * programDepth p + 1 ≤
      m + (m+2)^c.1.2.1 * programDepth p + 1 := by omega
  have houter := Nat.mul_le_mul_left (d.stackCount+1) hinner
  refine ⟨t,?_,hr⟩
  rw [timePolynomial_eval]
  change t ≤ 1 + (2*m+2+(m+2)^c.1.2.1) +
    ((d.stackCount+1)*(m+(m+2)^c.1.2.1*programDepth p+1)+2)
  change t ≤ 1 + (2*m+2+(x.length+2)^c.1.2.1) +
    ((d.stackCount+1)*(m+(x.length+2)^c.1.2.1*programDepth p+1)+2) at ht
  omega

/-- The whole machine has exactly the public library's Boolean input and
output alphabets. -/
def wholeAux (c : Shared.Codes.TM2Candidate.Candidate) (p : Program) : Turing.TM2ComputableAux Bool Bool where
  tm := let d := inputDataOfRaw c.1.2.2
    whole d.stackCount d.states d.symbols p d.inputStack c.2.2.2 d.main d.initialState
      d.falseSymbol d.trueSymbol c.2.2.1
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool

set_option backward.isDefEq.respectTransparency false in
/-- A checked, fixed-clock candidate which returns `f` on every raw input is
polynomial-time in the pinned public library's actual TM2 definition. -/
theorem checked_total_isPolyTime (c : Shared.Codes.TM2Candidate.Candidate) (f : List Bool → Bool)
    (h : ∀ x, Shared.Codes.TM2CheckedCandidate.evaluate c x = some (f x)) :
    ComplexityTheory.IsPolyTime f := by
  let d := inputDataOfRaw c.1.2.2
  have he : Shared.Codes.TM2CheckedCandidate.evaluate
      ((c.1.1,c.1.2.1,inputRaw d),(c.2.1,c.2.2.1,c.2.2.2)) [] = some (f []) := by
    simpa [d] using h []
  obtain ⟨_,p,hdecode,_⟩ := checked_evaluate_validation d c.1.1 c.1.2.1 c.2.1 c.2.2.1 c.2.2.2 [] (f []) he
  let w := wholeAux c p
  refine ⟨{ toTM2ComputableAux := w, time := timePolynomial d.stackCount c.1.2.1 p, outputsFun := ?_ }⟩
  intro x
  let hrun := checked_whole_run c p hdecode x (f x) (h x)
  let n := Classical.choose hrun
  have hn := Classical.choose_spec hrun
  refine ⟨⟨n,?_⟩,hn.1⟩
  have hr := hn.2
  rw [runSteps_iterate] at hr
  change (fun o => o.bind w.tm.step)^[n]
    (some (Turing.initList w.tm ((BitstringEncoding.bitEncode x).map id))) =
      some (Turing.haltList w.tm ([f x].map id))
  rw [List.map_id, List.map_id]
  exact hr

/-- Checked clocked candidates characterize the canonical deterministic
polynomial-time class. No program-running-time decision is assumed. -/
theorem candidate_iff_P (f : ComplexityTheory.DecisionProblem) :
    (∃ c : Shared.Codes.TM2Candidate.Candidate,
      ∀ x, Shared.Codes.TM2CheckedCandidate.evaluate c x = some (f x)) ↔ f ∈ ComplexityTheory.P := by
  constructor
  · rintro ⟨c,hc⟩
    exact checked_total_isPolyTime c f hc
  · intro hf
    obtain ⟨c,_,hc⟩ := Shared.Codes.TM2CheckedCandidate.canonicalP_covers f hf
    exact ⟨c,hc⟩

/-- The abstract P-versus-NP SAT controller is silent exactly when this
all-bitstrings SAT language belongs to the pinned public P class. -/
theorem pnp_controller_iff_sat_in_P :
    (Shared.Beeping.Controller.system Shared.PNP.TM2Candidate.compareSAT 0).EventuallySilent ↔
      Shared.ComplexityBridge.CNF.sat ∈ ComplexityTheory.P :=
  Shared.PNP.TM2Candidate.controller_silent_iff.trans (candidate_iff_P Shared.ComplexityBridge.CNF.sat)

/-- Class equality follows once the independently stated canonical SAT
completeness and P closure/inclusion obligations are supplied. -/
theorem pnp_controller_conditional
    (complete : Shared.ComplexityBridge.CanonicalClasses.CompleteLanguage Shared.ComplexityBridge.CNF.sat)
    (p_subset_np : ComplexityTheory.P ⊆ ComplexityTheory.NP)
    (p_pullback : Shared.ComplexityBridge.CanonicalClasses.PullbackClosed ComplexityTheory.P) :
    (Shared.Beeping.Controller.system Shared.PNP.TM2Candidate.compareSAT 0).EventuallySilent ↔
      ComplexityTheory.P = ComplexityTheory.NP :=
  pnp_controller_iff_sat_in_P.trans
    (Shared.ComplexityBridge.CanonicalClasses.p_eq_np_iff_complete_in_p complete p_subset_np p_pullback).symm

/-- Conditional finite-machine endpoint. The numeric candidate bridge is
proved here; SAT NP-completeness, P inclusion/closure, and the concrete
progress-sensitive comparison certificate remain explicit obligations. -/
theorem pnp_certified_conditional {n : Nat} {M : Shared.Beeping.Machines.Machine n}
    (cert : Shared.Beeping.ComparisonImplementation.Certificate Shared.PNP.TM2Candidate.compareSAT 0 M)
    (complete : Shared.ComplexityBridge.CanonicalClasses.CompleteLanguage Shared.ComplexityBridge.CNF.sat)
    (p_subset_np : ComplexityTheory.P ⊆ ComplexityTheory.NP)
    (p_pullback : Shared.ComplexityBridge.CanonicalClasses.PullbackClosed ComplexityTheory.P) :
    M.system.EventuallySilent ↔ ComplexityTheory.P = ComplexityTheory.NP := by
  have hcert : M.system.EventuallySilent ↔
      (Shared.Beeping.Controller.system Shared.PNP.TM2Candidate.compareSAT 0).EventuallySilent :=
    cert.toSegmentSimulation.toEventRefinement.eventuallySilent_iff.symm
  exact hcert.trans (pnp_controller_iff_sat_in_P.trans
    (Shared.ComplexityBridge.CanonicalClasses.p_eq_np_iff_complete_in_p complete p_subset_np p_pullback).symm)

/-- Fixture with distinct input and output true-symbol codes. The numeric
output is `1`, which represents false under the output coding `(1,0)`. -/
def distinctCodeFixture : Turing.FinTM2 :=
  whole 1 1 2 ([.push 0 [1] .halt] : Program) 0 0 0 0 0 1 0

example : (runSteps distinctCodeFixture.step 9 (Turing.initList distinctCodeFixture [])).map
    (fun c => c.stk (.inl true)) = some [false] := by
  change (Option.map (fun c => c.stk (.inl true))
    (runSteps distinctCodeFixture.step 9 (Turing.initList distinctCodeFixture [])) : Option (List Bool)) = some [false]
  decide

example : (runSteps distinctCodeFixture.step 9 (Turing.initList distinctCodeFixture [])).map
    (fun c => c.l) = some none := by
  change (Option.map (fun c => c.l) (runSteps distinctCodeFixture.step 9
    (Turing.initList distinctCodeFixture [])) : Option (Option (Label 1 ([.push 0 [1] .halt] : Program)))) = some none
  decide

end Shared.ComplexityBridge.TM2Whole
