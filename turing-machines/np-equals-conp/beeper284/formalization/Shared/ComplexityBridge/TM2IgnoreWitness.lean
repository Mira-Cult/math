import Shared.ComplexityBridge.TM2PairStrip

namespace Shared.ComplexityBridge.TM2IgnoreWitness
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.ComplexityBridge.TM2Combined
open Shared.Codes.TM2Program Shared.ComplexityBridge.TM2FiniteReverse
open Shared.ComplexityBridge.TM2Whole Shared.ComplexityBridge.TM2FiniteBoundary
open Shared.ComplexityBridge.TM2PairStrip

abbrev StripLabel := Shared.ComplexityBridge.TM2PairStrip.Label
abbrev WholeLabel (ks : Nat) (p : Program) := Shared.ComplexityBridge.TM2Whole.Label ks p
abbrev Label (ks : Nat) (p : Program) := Unit ⊕ (StripLabel ⊕ WholeLabel ks p)
abbrev WholeState (states : Nat) := Shared.ComplexityBridge.TM2Whole.State states
abbrev State (states : Nat) := Option Bool ⊕ WholeState states

def stripState {states : Nat} : State states → Option Bool
  | .inl v => v
  | .inr _ => none

def wholeState (states initial : Nat) : State states → WholeState states
  | .inl _ => .inr (false,clip states initial,false)
  | .inr v => v

def stripLabel {ks : Nat} {p : Program} (l : StripLabel) : Label ks p := .inr (.inl l)
def wholeLabel {ks : Nat} {p : Program} (l : WholeLabel ks p) : Label ks p := .inr (.inr l)

abbrev StripStmt (ks symbols : Nat) := Stmt (Alphabet ks symbols) StripLabel (Option Bool)
abbrev WholeStmt (ks states symbols : Nat) (p : Program) :=
  Stmt (Alphabet ks symbols) (WholeLabel ks p) (WholeState states)

def liftStrip (ks states symbols : Nat) (p : Program) : StripStmt ks symbols →
    Stmt (Alphabet ks symbols) (Label ks p) (State states)
  | .push k f q => .push k (fun s => f (stripState s)) (liftStrip ks states symbols p q)
  | .peek k f q => .peek k (fun s x => .inl (f (stripState s) x)) (liftStrip ks states symbols p q)
  | .pop k f q => .pop k (fun s x => .inl (f (stripState s) x)) (liftStrip ks states symbols p q)
  | .load f q => .load (fun s => .inl (f (stripState s))) (liftStrip ks states symbols p q)
  | .branch f a b => .branch (fun s => f (stripState s)) (liftStrip ks states symbols p a) (liftStrip ks states symbols p b)
  | .goto f => .goto (fun s => stripLabel (f (stripState s)))
  | .halt => .halt

def liftWhole (ks states symbols initial : Nat) (p : Program) : WholeStmt ks states symbols p →
    Stmt (Alphabet ks symbols) (Label ks p) (State states)
  | .push k f q => .push k (fun s => f (wholeState states initial s)) (liftWhole ks states symbols initial p q)
  | .peek k f q => .peek k (fun s x => .inr (f (wholeState states initial s) x)) (liftWhole ks states symbols initial p q)
  | .pop k f q => .pop k (fun s x => .inr (f (wholeState states initial s) x)) (liftWhole ks states symbols initial p q)
  | .load f q => .load (fun s => .inr (f (wholeState states initial s))) (liftWhole ks states symbols initial p q)
  | .branch f a b => .branch (fun s => f (wholeState states initial s)) (liftWhole ks states symbols initial p a) (liftWhole ks states symbols initial p b)
  | .goto f => .goto (fun s => wholeLabel (f (wholeState states initial s)))
  | .halt => .halt

def stripEmbed (ks states symbols : Nat) (p : Program)
    (c : Cfg (Alphabet ks symbols) StripLabel (Option Bool)) :
    Cfg (Alphabet ks symbols) (Label ks p) (State states) :=
  ⟨c.l.map stripLabel,.inl c.var,c.stk⟩

def wholeEmbed (ks states symbols : Nat) (p : Program)
    (c : Cfg (Alphabet ks symbols) (WholeLabel ks p) (WholeState states)) :
    Cfg (Alphabet ks symbols) (Label ks p) (State states) :=
  ⟨c.l.map wholeLabel,.inr c.var,c.stk⟩

theorem liftStrip_stepAux (ks states symbols : Nat) (p : Program) (q : StripStmt ks symbols) (v : Option Bool)
    (S : (k : Bool ⊕ Fin (ks+1)) → List (Alphabet ks symbols k)) :
    stepAux (liftStrip ks states symbols p q) (.inl v) S = stripEmbed ks states symbols p (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | push k f q ih => exact ih v _
  | peek k f q ih => exact ih _ S
  | pop k f q ih => exact ih _ _
  | load f q ih => exact ih _ S
  | branch f a b iha ihb => by_cases h : f v <;> simp [liftStrip,stepAux,stripState,h,iha,ihb]

theorem liftWhole_stepAux (ks states symbols initial : Nat) (p : Program) (q : WholeStmt ks states symbols p) (v : WholeState states)
    (S : (k : Bool ⊕ Fin (ks+1)) → List (Alphabet ks symbols k)) :
    stepAux (liftWhole ks states symbols initial p q) (.inr v) S = wholeEmbed ks states symbols p (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | push k f q ih => exact ih v _
  | peek k f q ih => exact ih _ S
  | pop k f q ih => exact ih _ _
  | load f q ih => exact ih _ S
  | branch f a b iha ihb => by_cases h : f v <;> simp [liftWhole,stepAux,wholeState,h,iha,ihb]

def program (ks states symbols : Nat) (p : Program) (input output main initial z inOne one : Nat) :
    Label ks p → Stmt (Alphabet ks symbols) (Label ks p) (State states)
  | .inl () => .load (fun _ => .inl none) (.goto (fun _ => stripLabel .header))
  | .inr (.inl .done) => .load (fun _ => .inr (.inr (false,clip states initial,false)))
      (.goto (fun _ => wholeLabel (.inl ())))
  | .inr (.inl l) => liftStrip ks states symbols p (Shared.ComplexityBridge.TM2PairStrip.program ks symbols l)
  | .inr (.inr l) => liftWhole ks states symbols initial p
      (Shared.ComplexityBridge.TM2Whole.wholeProgram ks states symbols p input output main initial z inOne one l)

def machine (ks states symbols : Nat) (p : Program) (input output main initial z inOne one : Nat) : Turing.FinTM2 where
  K := Bool ⊕ Fin (ks+1)
  k₀ := .inl false
  k₁ := .inl true
  Γ := Alphabet ks symbols
  Λ := Label ks p
  main := .inl ()
  σ := State states
  initialState := .inr (.inr (false,clip states initial,false))
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := program ks states symbols p input output main initial z inOne one

set_option backward.isDefEq.respectTransparency false in
/-- All prelude labels except its terminal dispatch mirror the standalone
stripper one block at a time. -/
theorem strip_step (ks states symbols : Nat) (p : Program) (input output main initial z inOne one : Nat)
    (c : (Shared.ComplexityBridge.TM2PairStrip.stripper ks symbols).Cfg) (hnot : c.l ≠ some .done) :
    (machine ks states symbols p input output main initial z inOne one).step (stripEmbed ks states symbols p c) =
      ((Shared.ComplexityBridge.TM2PairStrip.stripper ks symbols).step c).map (stripEmbed ks states symbols p) := by
  cases c with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l =>
      have hp : program ks states symbols p input output main initial z inOne one (stripLabel l) =
          liftStrip ks states symbols p (Shared.ComplexityBridge.TM2PairStrip.program ks symbols l) := by
        cases l <;> simp_all [program,stripLabel]
      change some (stepAux (program ks states symbols p input output main initial z inOne one (stripLabel l)) (.inl v) S) = _
      rw [hp,liftStrip_stepAux]
      rfl

set_option backward.isDefEq.respectTransparency false in
theorem strip_one (ks states symbols : Nat) (p : Program) (input output main initial z inOne one : Nat)
    (c d : (Shared.ComplexityBridge.TM2PairStrip.stripper ks symbols).Cfg)
    (hnot : c.l ≠ some .done) (h : (Shared.ComplexityBridge.TM2PairStrip.stripper ks symbols).step c = some d) :
    (machine ks states symbols p input output main initial z inOne one).step (stripEmbed ks states symbols p c) =
      some (stripEmbed ks states symbols p d) := by
  rw [strip_step ks states symbols p input output main initial z inOne one c hnot,h]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem whole_step (ks states symbols : Nat) (p : Program) (input output main initial z inOne one : Nat)
    (c : (Shared.ComplexityBridge.TM2Whole.whole ks states symbols p input output main initial z inOne one).Cfg) :
    (machine ks states symbols p input output main initial z inOne one).step (wholeEmbed ks states symbols p c) =
      ((Shared.ComplexityBridge.TM2Whole.whole ks states symbols p input output main initial z inOne one).step c).map (wholeEmbed ks states symbols p) := by
  cases c with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l =>
      change some (stepAux (liftWhole ks states symbols initial p
        (Shared.ComplexityBridge.TM2Whole.wholeProgram ks states symbols p input output main initial z inOne one l)) (.inr v) S) = _
      rw [liftWhole_stepAux]
      rfl

set_option backward.isDefEq.respectTransparency false in
theorem whole_run (ks states symbols : Nat) (p : Program) (input output main initial z inOne one : Nat) (n : Nat)
    (c : (Shared.ComplexityBridge.TM2Whole.whole ks states symbols p input output main initial z inOne one).Cfg) :
    runSteps (machine ks states symbols p input output main initial z inOne one).step n (wholeEmbed ks states symbols p c) =
      (runSteps (Shared.ComplexityBridge.TM2Whole.whole ks states symbols p input output main initial z inOne one).step n c).map (wholeEmbed ks states symbols p) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [runSteps_front,runSteps_front,whole_step]
    cases h : (Shared.ComplexityBridge.TM2Whole.whole ks states symbols p input output main initial z inOne one).step c with
    | none => rfl
    | some c' => exact ih c'

set_option backward.isDefEq.respectTransparency false in
theorem header_run (ks states symbols : Nat) (p : Program) (input output main initial z inOne one : Nat)
    (payload tail scratch : List Bool) (v : Option Bool) (S : Fin (ks+1) → List (Fin (symbols+1))) :
    ∃ v', runSteps (machine ks states symbols p input output main initial z inOne one).step (2*payload.length)
      (stripEmbed ks states symbols p (cfg ks symbols .header v (BitstringEncoding.delimit payload ++ tail) scratch S)) =
        some (stripEmbed ks states symbols p (cfg ks symbols .header v' (false::tail) (payload.reverse++scratch) S)) := by
  induction payload generalizing scratch v with
  | nil => exact ⟨v,by simp [runSteps,BitstringEncoding.delimit]⟩
  | cons x xs ih =>
    obtain ⟨v',hv⟩ := ih (x::scratch) (some x)
    refine ⟨v',?_⟩
    simp only [List.length_cons,BitstringEncoding.delimit,List.cons_append]
    have hn : 2*(xs.length+1) = (2*xs.length+1)+1 := by omega
    rw [hn,runSteps_front]
    rw [strip_one ks states symbols p input output main initial z inOne one _ _ (by simp [cfg])
      (header_true ks symbols v (x::(BitstringEncoding.delimit xs ++ tail)) scratch S)]
    change runSteps (machine ks states symbols p input output main initial z inOne one).step (2*xs.length+1)
      (stripEmbed ks states symbols p (cfg ks symbols .data (some true) (x::(BitstringEncoding.delimit xs ++ tail)) scratch S)) = _
    rw [runSteps_front]
    rw [strip_one ks states symbols p input output main initial z inOne one _ _ (by simp [cfg])
      (data_cons ks symbols (some true) x (BitstringEncoding.delimit xs ++ tail) scratch S)]
    simpa [List.reverse_cons,List.append_assoc] using hv

set_option backward.isDefEq.respectTransparency false in
theorem discard_run (ks states symbols : Nat) (p : Program) (input output main initial z inOne one : Nat)
    (tail scratch : List Bool) (v : Option Bool) (S : Fin (ks+1) → List (Fin (symbols+1))) :
    ∃ v', runSteps (machine ks states symbols p input output main initial z inOne one).step tail.length
      (stripEmbed ks states symbols p (cfg ks symbols .discard v tail scratch S)) =
        some (stripEmbed ks states symbols p (cfg ks symbols .discard v' [] scratch S)) := by
  induction tail generalizing v with
  | nil => exact ⟨v,rfl⟩
  | cons x xs ih =>
    obtain ⟨v',hv⟩ := ih (some x)
    refine ⟨v',?_⟩
    rw [List.length_cons,runSteps_front]
    rw [strip_one ks states symbols p input output main initial z inOne one _ _ (by simp [cfg])
      (discard_cons ks symbols v x xs scratch S)]
    exact hv

set_option backward.isDefEq.respectTransparency false in
theorem restore_run (ks states symbols : Nat) (p : Program) (input output main initial z inOne one : Nat)
    (scratch inp : List Bool) (v : Option Bool) (S : Fin (ks+1) → List (Fin (symbols+1))) :
    ∃ v', runSteps (machine ks states symbols p input output main initial z inOne one).step scratch.length
      (stripEmbed ks states symbols p (cfg ks symbols .restore v inp scratch S)) =
        some (stripEmbed ks states symbols p (cfg ks symbols .restore v' (scratch.reverse++inp) [] S)) := by
  induction scratch generalizing inp v with
  | nil => exact ⟨v,by simp [runSteps]⟩
  | cons x xs ih =>
    obtain ⟨v',hv⟩ := ih (x::inp) (some x)
    refine ⟨v',?_⟩
    rw [List.length_cons,runSteps_front]
    rw [strip_one ks states symbols p input output main initial z inOne one _ _ (by simp [cfg])
      (restore_cons ks symbols v x inp xs S)]
    simpa [List.reverse_cons,List.append_assoc] using hv

set_option backward.isDefEq.respectTransparency false in
theorem embedded_strip (ks states symbols : Nat) (p : Program) (input output main initial z inOne one : Nat)
    (payload tail : List Bool) :
    runSteps (machine ks states symbols p input output main initial z inOne one).step (3*payload.length+tail.length+3)
      (stripEmbed ks states symbols p (cfg ks symbols .header none (BitstringEncoding.delimit payload ++ tail) [] (fun _ => []))) =
        some (stripEmbed ks states symbols p (cfg ks symbols .done none payload [] (fun _ => []))) := by
  obtain ⟨v,hheader⟩ := header_run ks states symbols p input output main initial z inOne one payload tail [] none (fun _ => [])
  simp only [List.append_nil] at hheader
  have hh : runSteps (machine ks states symbols p input output main initial z inOne one).step (2*payload.length+1)
      (stripEmbed ks states symbols p (cfg ks symbols .header none (BitstringEncoding.delimit payload ++ tail) [] (fun _ => []))) =
        some (stripEmbed ks states symbols p (cfg ks symbols .discard (some false) tail payload.reverse (fun _ => []))) := by
    rw [runSteps_add,hheader]
    change (machine ks states symbols p input output main initial z inOne one).step
      (stripEmbed ks states symbols p (cfg ks symbols .header v (false::tail) payload.reverse (fun _ => []))) = _
    exact strip_one ks states symbols p input output main initial z inOne one _ _ (by simp [cfg])
      (header_false ks symbols v tail payload.reverse (fun _ => []))
  obtain ⟨v',hdiscard⟩ := discard_run ks states symbols p input output main initial z inOne one tail payload.reverse (some false) (fun _ => [])
  have hd : runSteps (machine ks states symbols p input output main initial z inOne one).step (tail.length+1)
      (stripEmbed ks states symbols p (cfg ks symbols .discard (some false) tail payload.reverse (fun _ => []))) =
        some (stripEmbed ks states symbols p (cfg ks symbols .restore none [] payload.reverse (fun _ => []))) := by
    rw [runSteps_add,hdiscard]
    change (machine ks states symbols p input output main initial z inOne one).step
      (stripEmbed ks states symbols p (cfg ks symbols .discard v' [] payload.reverse (fun _ => []))) = _
    exact strip_one ks states symbols p input output main initial z inOne one _ _ (by simp [cfg])
      (discard_nil ks symbols v' payload.reverse (fun _ => []))
  obtain ⟨v'',hrestore⟩ := restore_run ks states symbols p input output main initial z inOne one payload.reverse [] none (fun _ => [])
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at hrestore
  have hr : runSteps (machine ks states symbols p input output main initial z inOne one).step (payload.length+1)
      (stripEmbed ks states symbols p (cfg ks symbols .restore none [] payload.reverse (fun _ => []))) =
        some (stripEmbed ks states symbols p (cfg ks symbols .done none payload [] (fun _ => []))) := by
    rw [runSteps_add,hrestore]
    change (machine ks states symbols p input output main initial z inOne one).step
      (stripEmbed ks states symbols p (cfg ks symbols .restore v'' payload [] (fun _ => []))) = _
    exact strip_one ks states symbols p input output main initial z inOne one _ _ (by simp [cfg])
      (restore_nil ks symbols v'' payload (fun _ => []))
  have hn : 3*payload.length+tail.length+3 = ((2*payload.length+1)+(tail.length+1))+(payload.length+1) := by omega
  rw [hn,runSteps_add,runSteps_add,hh]
  change (runSteps (machine ks states symbols p input output main initial z inOne one).step (tail.length+1)
    (stripEmbed ks states symbols p (cfg ks symbols .discard (some false) tail payload.reverse (fun _ => [])))).bind _ = _
  rw [hd]
  exact hr

/-- The wrapper needs one startup block to switch from its reset state to the
prelude state, preserving the complete input stack. -/
theorem startup (ks states symbols : Nat) (p : Program) (input output main initial z inOne one : Nat) (bits : List Bool) :
    (machine ks states symbols p input output main initial z inOne one).step
      (Turing.initList (machine ks states symbols p input output main initial z inOne one) bits) =
        some (stripEmbed ks states symbols p (cfg ks symbols .header none bits [] (fun _ => []))) := by
  change some (Cfg.mk (some (stripLabel .header : Label ks p)) (.inl none : State states) _) =
    some (Cfg.mk (some (stripLabel .header : Label ks p)) (.inl none : State states) _)
  congr 1
  congr 1
  funext k
  cases k with
  | inl b =>
    cases b <;> simp [machine,cfg,embedStacks]
    rfl
  | inr j => simp [machine,cfg,embedStacks]

/-- The dispatch costs one block and starts the decision machine at its
actual initial configuration with the restored payload. -/
theorem dispatch (ks states symbols : Nat) (p : Program) (input output main initial z inOne one : Nat) (payload : List Bool) :
    (machine ks states symbols p input output main initial z inOne one).step
      (stripEmbed ks states symbols p (cfg ks symbols .done none payload [] (fun _ => []))) =
        some (wholeEmbed ks states symbols p
          (Turing.initList (Shared.ComplexityBridge.TM2Whole.whole ks states symbols p input output main initial z inOne one) payload)) := by
  change some (Cfg.mk (some (wholeLabel (.inl ()) : Label ks p))
      (.inr (.inr (false,clip states initial,false)) : State states) _) =
    some (Cfg.mk (some (wholeLabel (.inl ()) : Label ks p))
      (.inr (.inr (false,clip states initial,false)) : State states) _)
  congr 1
  congr 1
  funext k
  cases k with
  | inl b => cases b <;> rfl
  | inr j => rfl

theorem halt_embed (ks states symbols : Nat) (p : Program) (input output main initial z inOne one : Nat) (b : Bool) :
    wholeEmbed ks states symbols p
      (Turing.haltList (Shared.ComplexityBridge.TM2Whole.whole ks states symbols p input output main initial z inOne one) [b]) =
        Turing.haltList (machine ks states symbols p input output main initial z inOne one) [b] := by
  change Cfg.mk none (.inr (.inr (false,clip states initial,false)) : State states) _ =
    Cfg.mk none (.inr (.inr (false,clip states initial,false)) : State states) _
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- On a canonical pair, the wrapper runs the prelude and dispatches to the
decision machine's real initial configuration. -/
theorem pair_prelude (ks states symbols : Nat) (p : Program) (input output main initial z inOne one : Nat)
    (x w : List Bool) :
    runSteps (machine ks states symbols p input output main initial z inOne one).step (9*x.length+3*w.length+5)
      (Turing.initList (machine ks states symbols p input output main initial z inOne one) (BitstringEncoding.bitEncode (x,w))) =
      some (wholeEmbed ks states symbols p
        (Turing.initList (Shared.ComplexityBridge.TM2Whole.whole ks states symbols p input output main initial z inOne one)
          (BitstringEncoding.bitEncode x))) := by
  let pair := BitstringEncoding.bitEncode (x,w)
  let left := BitstringEncoding.bitEncode x
  let right := BitstringEncoding.bitEncode w
  have he : pair = BitstringEncoding.delimit left ++ right := rfl
  have hstart : runSteps (machine ks states symbols p input output main initial z inOne one).step 1
      (Turing.initList (machine ks states symbols p input output main initial z inOne one) pair) =
      some (stripEmbed ks states symbols p (cfg ks symbols .header none pair [] (fun _ => []))) := by
    simpa [runSteps] using startup ks states symbols p input output main initial z inOne one pair
  have hstrip := embedded_strip ks states symbols p input output main initial z inOne one left right
  rw [← he] at hstrip
  have hd : runSteps (machine ks states symbols p input output main initial z inOne one).step 1
      (stripEmbed ks states symbols p (cfg ks symbols .done none left [] (fun _ => []))) =
      some (wholeEmbed ks states symbols p
        (Turing.initList (Shared.ComplexityBridge.TM2Whole.whole ks states symbols p input output main initial z inOne one) left)) := by
    simpa [runSteps] using dispatch ks states symbols p input output main initial z inOne one left
  have hl : left.length = 3*x.length := Shared.ComplexityBridge.bitstring_list_encoded_length x
  have hr : right.length = 3*w.length := Shared.ComplexityBridge.bitstring_list_encoded_length w
  have ht : 9*x.length+3*w.length+5 = (1+(3*left.length+right.length+3))+1 := by omega
  rw [ht,runSteps_add,runSteps_add,hstart]
  change (runSteps (machine ks states symbols p input output main initial z inOne one).step (3*left.length+right.length+3)
    (stripEmbed ks states symbols p (cfg ks symbols .header none pair [] (fun _ => [])))).bind _ = _
  rw [hstrip]
  exact hd

/-- The fixed decision-machine time polynomial is monotone over input length. -/
theorem timePolynomial_mono (stackCount exponent : Nat) (p : Program) {a b : Nat} (hab : a ≤ b) :
    (Shared.ComplexityBridge.TM2Whole.timePolynomial stackCount exponent p).eval a ≤
      (Shared.ComplexityBridge.TM2Whole.timePolynomial stackCount exponent p).eval b := by
  rw [Shared.ComplexityBridge.TM2Whole.timePolynomial_eval, Shared.ComplexityBridge.TM2Whole.timePolynomial_eval]
  have hp : (a+2)^exponent ≤ (b+2)^exponent := Nat.pow_le_pow_left (by omega) _
  have hm := Nat.mul_le_mul_right (Shared.ComplexityBridge.TM2StackBound.programDepth p) hp
  have hi : a+(a+2)^exponent*Shared.ComplexityBridge.TM2StackBound.programDepth p+1 ≤
      b+(b+2)^exponent*Shared.ComplexityBridge.TM2StackBound.programDepth p+1 := by omega
  have ho := Nat.mul_le_mul_left (stackCount+1) hi
  omega

noncomputable def pairTimePolynomial (stackCount exponent : Nat) (p : Program) : Polynomial Nat :=
  Polynomial.C 2 * Polynomial.X + Polynomial.C 3 + Shared.ComplexityBridge.TM2Whole.timePolynomial stackCount exponent p

theorem pairTimePolynomial_eval (stackCount exponent : Nat) (p : Program) (n : Nat) :
    (pairTimePolynomial stackCount exponent p).eval n =
      2*n+3+(Shared.ComplexityBridge.TM2Whole.timePolynomial stackCount exponent p).eval n := by
  simp [pairTimePolynomial]

set_option backward.isDefEq.respectTransparency false in
/-- A successful checked decision candidate runs on a pair by discarding the
witness, with an explicit polynomial bound in the full pair-encoded length. -/
theorem projection_run (c : Shared.Codes.TM2Candidate.Candidate) (p : Program)
    (hdecode : decodeProgram c.1.1 = some p) (x w : List Bool) (b : Bool)
    (heval : Shared.Codes.TM2CheckedCandidate.evaluate c x = some b) :
    let d := inputDataOfRaw c.1.2.2
    let tm := machine d.stackCount d.states d.symbols p d.inputStack c.2.2.2 d.main d.initialState
      d.falseSymbol d.trueSymbol c.2.2.1
    ∃ t ≤ (pairTimePolynomial d.stackCount c.1.2.1 p).eval (BitstringEncoding.bitEncode (x,w)).length,
      runSteps tm.step t (Turing.initList tm (BitstringEncoding.bitEncode (x,w))) = some (Turing.haltList tm [b]) := by
  let d := inputDataOfRaw c.1.2.2
  let tm := machine d.stackCount d.states d.symbols p d.inputStack c.2.2.2 d.main d.initialState d.falseSymbol d.trueSymbol c.2.2.1
  let wc := Shared.ComplexityBridge.TM2Whole.whole d.stackCount d.states d.symbols p d.inputStack c.2.2.2 d.main d.initialState
    d.falseSymbol d.trueSymbol c.2.2.1
  obtain ⟨t,ht,hr⟩ := checked_whole_run c p hdecode x b heval
  have hp := pair_prelude d.stackCount d.states d.symbols p d.inputStack c.2.2.2 d.main d.initialState
    d.falseSymbol d.trueSymbol c.2.2.1 x w
  have hw := whole_run d.stackCount d.states d.symbols p d.inputStack c.2.2.2 d.main d.initialState
    d.falseSymbol d.trueSymbol c.2.2.1 t (Turing.initList wc (BitstringEncoding.bitEncode x))
  rw [hr] at hw
  change runSteps tm.step t (wholeEmbed d.stackCount d.states d.symbols p (Turing.initList wc (BitstringEncoding.bitEncode x))) =
    some (wholeEmbed d.stackCount d.states d.symbols p (Turing.haltList wc [b])) at hw
  rw [halt_embed] at hw
  let m := (BitstringEncoding.bitEncode (x,w)).length
  have hlen : (BitstringEncoding.bitEncode x).length ≤ m := by
    dsimp [m]
    rw [Shared.ComplexityBridge.bitstring_list_encoded_length,Shared.ComplexityBridge.bitstring_pair_encoded_length]
    omega
  change t ≤ (Shared.ComplexityBridge.TM2Whole.timePolynomial d.stackCount c.1.2.1 p).eval
    (BitstringEncoding.bitEncode x).length at ht
  have hmono := timePolynomial_mono d.stackCount c.1.2.1 p hlen
  have hcost : 9*x.length+3*w.length+5 ≤ 2*m+3 := by
    dsimp [m]
    rw [Shared.ComplexityBridge.bitstring_pair_encoded_length]
    omega
  refine ⟨(9*x.length+3*w.length+5)+t,?_,?_⟩
  · rw [pairTimePolynomial_eval]
    change (9*x.length+3*w.length+5)+t ≤ 2*m+3+
      (Shared.ComplexityBridge.TM2Whole.timePolynomial d.stackCount c.1.2.1 p).eval m
    omega
  · rw [runSteps_add,hp]
    exact hw

/-- The wrapper exposes exactly Boolean input and output alphabets. -/
def aux (c : Shared.Codes.TM2Candidate.Candidate) (p : Program) : Turing.TM2ComputableAux Bool Bool where
  tm := let d := inputDataOfRaw c.1.2.2
    machine d.stackCount d.states d.symbols p d.inputStack c.2.2.2 d.main d.initialState
      d.falseSymbol d.trueSymbol c.2.2.1
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool

set_option backward.isDefEq.respectTransparency false in
/-- A canonical polynomial-time decision procedure remains polynomial-time
when applied to the first component of the library's pair encoding. -/
theorem first_projection_poly (L : ComplexityTheory.DecisionProblem) (hL : L ∈ ComplexityTheory.P) :
    ComplexityTheory.IsPolyTime (fun a : List Bool × List Bool => L a.1) := by
  obtain ⟨c,hvalid,hcorrect⟩ := Shared.Codes.TM2CheckedCandidate.canonicalP_covers L hL
  cases hdecode : decodeProgram c.1.1 with
  | none => simp [Shared.Codes.TM2CheckedCandidate.candidateValid,hdecode] at hvalid
  | some p =>
    let d := inputDataOfRaw c.1.2.2
    let tm := aux c p
    refine ⟨{ toTM2ComputableAux := tm, time := pairTimePolynomial d.stackCount c.1.2.1 p, outputsFun := ?_ }⟩
    intro a
    let hrun := projection_run c p hdecode a.1 a.2 (L a.1) (hcorrect a.1)
    let n := Classical.choose hrun
    have hn := Classical.choose_spec hrun
    refine ⟨⟨n,?_⟩,hn.1⟩
    have hr := hn.2
    rw [runSteps_iterate] at hr
    change (fun o => o.bind tm.tm.step)^[n]
      (some (Turing.initList tm.tm ((BitstringEncoding.bitEncode a).map id))) =
        some (Turing.haltList tm.tm ([L a.1].map id))
    rw [List.map_id,List.map_id]
    exact hr

/-- Every canonical polynomial-time decision problem is in canonical NP,
using an empty witness and the verified first-component wrapper. -/
theorem P_subset_NP : ComplexityTheory.P ⊆ ComplexityTheory.NP := by
  intro L hL
  refine ⟨0, (fun a : List Bool × List Bool => L a.1), first_projection_poly L hL, ?_⟩
  intro x
  constructor
  · intro hx
    exact ⟨[],by simp,hx⟩
  · rintro ⟨w,hw,hr⟩
    exact hr

/-- Complement closure then gives the canonical inclusion in coNP as well. -/
theorem P_subset_coNP : ComplexityTheory.P ⊆ ComplexityTheory.coNP :=
  Shared.ComplexityBridge.TM2Complement.P_subset_coNP_iff_P_subset_NP.mpr P_subset_NP

/-- The finite-machine P-versus-NP theorem no longer assumes `P ⊆ NP`;
SAT completeness, P pullback closure and the concrete certificate remain. -/
theorem pnp_certified_conditional {n : Nat} {M : Shared.Beeping.Machines.Machine n}
    (cert : Shared.Beeping.ComparisonImplementation.Certificate Shared.PNP.TM2Candidate.compareSAT 0 M)
    (complete : Shared.ComplexityBridge.CanonicalClasses.CompleteLanguage Shared.ComplexityBridge.CNF.sat)
    (p_pullback : Shared.ComplexityBridge.CanonicalClasses.PullbackClosed ComplexityTheory.P) :
    M.system.EventuallySilent ↔ ComplexityTheory.P = ComplexityTheory.NP :=
  Shared.ComplexityBridge.TM2Whole.pnp_certified_conditional cert complete P_subset_NP p_pullback

end Shared.ComplexityBridge.TM2IgnoreWitness
