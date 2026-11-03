import Shared.ComplexityBridge.TM2Combined

namespace Shared.ComplexityBridge.TM2StackBound
open Shared.Codes.TM2Statements Shared.Codes.TM2StatementExecution Shared.Codes.TM2Program
open Shared.Codes.FiniteTables
open Shared.ComplexityBridge.TM2BooleanInput Shared.ComplexityBridge.TM2Loader
open Shared.ComplexityBridge.TM2FiniteReverse Shared.ComplexityBridge.TM2FiniteBoundary
open Shared.ComplexityBridge.TM2BooleanOutput Shared.ComplexityBridge.TM2Combined
open Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Micro Shared.Codes.TM2FixedComputability
open scoped BigOperators

def StackBound (s : Stacks) (bound : Nat) : Prop :=
  ∀ k, (stackFn s k).length ≤ bound

theorem bound_mono {s : Stacks} {a b : Nat} (h : StackBound s a) (hab : a ≤ b) : StackBound s b :=
  fun k => Nat.le_trans (h k) hab

theorem bound_push (s : Stacks) (k : Nat) (stk : List Nat) (x bound : Nat)
    (hs : s[k]? = some stk) (hb : StackBound s bound) :
    StackBound (s.set k (x::stk)) (bound+1) := by
  have hk : k < s.length := (List.getElem?_eq_some_iff.mp hs).1
  intro j
  rw [stackFn_set s k (x::stk) hk]
  by_cases hj : j = k
  · subst j
    rw [Function.update_self]
    have h := hb k
    simp [stackFn, hs] at h
    simp only [List.length_cons]
    omega
  · rw [Function.update_of_ne hj]
    exact Nat.le_trans (hb j) (Nat.le_succ bound)

theorem bound_pop (s : Stacks) (k : Nat) (stk : List Nat) (bound : Nat)
    (hs : s[k]? = some stk) (hb : StackBound s bound) :
    StackBound (s.set k stk.tail) bound := by
  have hk : k < s.length := (List.getElem?_eq_some_iff.mp hs).1
  intro j
  rw [stackFn_set s k stk.tail hk]
  by_cases hj : j = k
  · subst j
    rw [Function.update_self]
    have h := hb k
    simp [stackFn, hs] at h
    rw [List.length_tail]
    omega
  · rw [Function.update_of_ne hj]
    exact hb j

/-- A successful whole block can increase any stack's length by at most the
statement-tree depth. This does not assume table validation. -/
theorem exec_bound (q : Code) (v : Nat) (s : Stacks) (r : Result) (bound : Nat)
    (hb : StackBound s bound) (he : exec q v s = some r) :
    StackBound r.memory (bound + depth q) := by
  induction q generalizing v s bound with
  | halt =>
    simp [exec] at he
    subst r
    exact bound_mono hb (by simp [depth])
  | goto t =>
    cases ht : lookup t v with
    | none => simp [exec, ht] at he
    | some l =>
      simp [exec, ht] at he
      subst r
      exact bound_mono hb (by simp [depth])
  | push k t q ih =>
    cases hs : s[k]? with
    | none => simp [exec, hs] at he
    | some stk =>
      cases ht : lookup t v with
      | none => simp [exec, hs, ht] at he
      | some x =>
        have hr : exec q v (s.set k (x::stk)) = some r := by simpa [exec, hs, ht] using he
        have h := ih v (s.set k (x::stk)) (bound+1) (bound_push s k stk x bound hs hb) hr
        apply bound_mono h
        simp [depth]
        omega
  | peek k t q ih =>
    cases hs : s[k]? with
    | none => simp [exec, hs] at he
    | some stk =>
      cases ht : lookup₂ t v (symbolIndex stk.head?) with
      | none => simp [exec, hs, ht] at he
      | some v' =>
        have hr : exec q v' s = some r := by simpa [exec, hs, ht] using he
        have h := ih v' s bound hb hr
        apply bound_mono h
        simp [depth]
  | pop k t q ih =>
    cases hs : s[k]? with
    | none => simp [exec, hs] at he
    | some stk =>
      cases ht : lookup₂ t v (symbolIndex stk.head?) with
      | none => simp [exec, hs, ht] at he
      | some v' =>
        have hr : exec q v' (s.set k stk.tail) = some r := by simpa [exec, hs, ht] using he
        have h := ih v' (s.set k stk.tail) bound (bound_pop s k stk bound hs hb) hr
        apply bound_mono h
        simp [depth]
  | load t q ih =>
    cases ht : lookup t v with
    | none => simp [exec, ht] at he
    | some v' =>
      have hr : exec q v' s = some r := by simpa [exec, ht] using he
      have h := ih v' s bound hb hr
      apply bound_mono h
      simp [depth]
  | branch t a b iha ihb =>
    cases ht : lookup t v with
    | none => simp [exec, ht] at he
    | some x =>
      cases hx : boolOfNat x with
      | none => simp [exec, ht, hx] at he
      | some bit =>
        cases bit with
        | false =>
          have hr : exec b v s = some r := by simpa [exec, ht, hx] using he
          have h := ihb v s bound hb hr
          apply bound_mono h
          simp only [depth]
          omega
        | true =>
          have hr : exec a v s = some r := by simpa [exec, ht, hx] using he
          have h := iha v s bound hb hr
          apply bound_mono h
          simp only [depth]
          omega

/-- A fixed finite program-wide constant bounds the depth of every block. -/
def programDepth (p : Program) : Nat := (p.map depth).sum

theorem programDepth_bound (p : Program) (l : Nat) (q : Code) (hq : p[l]? = some q) :
    depth q ≤ programDepth p := by
  apply List.single_le_sum (by intros; omega)
  exact List.mem_map_of_mem (List.mem_of_getElem? hq)

def OutcomeBound (bound : Nat) : Outcome → Prop
  | .invalid => True
  | .timeout r => StackBound r.memory bound
  | .halted r => StackBound r.memory bound

theorem outcomeBound_mono {a b : Nat} {r : Outcome} (h : OutcomeBound a r) (hab : a ≤ b) : OutcomeBound b r := by
  cases r with
  | invalid => trivial
  | timeout r => exact bound_mono h hab
  | halted r => exact bound_mono h hab

/-- In any bounded execution, including a timeout, every stack has at most
its initial uniform bound plus fuel times a fixed program constant. Invalid
outcomes carry no result and satisfy the theorem trivially. -/
theorem run_bound (p : Program) (fuel : Nat) (d : Result) (bound : Nat)
    (hb : StackBound d.memory bound) :
    OutcomeBound (bound + fuel * programDepth p) (run p fuel d) := by
  induction fuel generalizing d bound with
  | zero =>
    cases hl : d.label with
    | none => simpa [run, hl, OutcomeBound] using hb
    | some l => simpa [run, hl, OutcomeBound] using hb
  | succ n ih =>
    cases hl : d.label with
    | none =>
      simp only [run, hl, OutcomeBound]
      exact bound_mono hb (by omega)
    | some l =>
      cases hq : p[l]? with
      | none => simp [run, hl, hq, OutcomeBound]
      | some q =>
        cases he : exec q d.state d.memory with
        | none => simp [run, hl, hq, he, OutcomeBound]
        | some r =>
          have hr := exec_bound q d.state d.memory r bound hb he
          have h := ih r (bound + depth q) hr
          have hdepth := programDepth_bound p l q hq
          have hle : (bound + depth q) + n * programDepth p ≤ bound + (n+1) * programDepth p := by
            rw [Nat.add_mul, Nat.one_mul]
            omega
          have h' := outcomeBound_mono h hle
          simpa [run, hl, hq, he] using h'

/-- Initializing an encoded input places at most its length on any stack. -/
theorem buildStart_bound (d : InputData) (bits : List Bool) (start : Result)
    (h : buildStart d bits = some start) : StackBound start.memory bits.length := by
  cases hd : validInputData d with
  | false => simp [buildStart, hd] at h
  | true =>
    have hval := hd
    simp only [validInputData, Bool.and_eq_true, decide_eq_true_eq] at hval
    obtain ⟨⟨⟨⟨⟨_,_⟩,hi⟩,_⟩,_⟩,_⟩ := hval
    have heq : start = ⟨some d.main,d.initialState,
        (List.replicate d.stackCount []).set d.inputStack (bits.map (inputBit d.falseSymbol d.trueSymbol))⟩ := by
      simpa [buildStart, hd] using h.symm
    subst start
    intro k
    have hi' : d.inputStack < (List.replicate d.stackCount ([] : List Nat)).length := by simpa using hi
    rw [stackFn_set _ _ _ hi']
    by_cases hk : k = d.inputStack
    · subst k
      simp
    · rw [Function.update_of_ne hk]
      simp [stackFn_empty]

/-- Any successful or timed-out run from encoded input has a uniform stack
bound linear in encoded input length and the fixed program's block clock. -/
theorem run_from_input_bound (d : InputData) (bits : List Bool) (p : Program) (fuel : Nat)
    (start : Result) (hstart : buildStart d bits = some start) :
    OutcomeBound (bits.length + fuel * programDepth p) (run p fuel start) :=
  run_bound p fuel start bits.length (buildStart_bound d bits start hstart)

/-- Related finite-core stacks have the same length as the numeric stacks. -/
theorem related_stack_length (ks states symbols labels : Nat)
    (c : Turing.TM2.Cfg (fun _ : Fin (ks+1) => Fin (symbols+1)) (Fin (labels+1)) (Fin (states+1)))
    (r : Result) (hr : CfgRel ks states symbols labels c (erase r)) (k : Fin (ks+1)) :
    (c.stk k).length = (stackFn r.memory k.val).length := by
  have h := hr.2.2 k
  change stackFn r.memory k.val = (c.stk k).map Fin.val at h
  simpa using (congrArg List.length h).symm

/-- A numeric outcome's bound transfers to every finite-core stack of a
related configuration. -/
theorem related_stack_bound (ks states symbols labels : Nat)
    (c : Turing.TM2.Cfg (fun _ : Fin (ks+1) => Fin (symbols+1)) (Fin (labels+1)) (Fin (states+1)))
    (r : Result) (hr : CfgRel ks states symbols labels c (erase r)) (bound : Nat)
    (hb : StackBound r.memory bound) : ∀ k, (c.stk k).length ≤ bound := by
  intro k
  rw [related_stack_length ks states symbols labels c r hr k]
  exact hb k.val

set_option backward.isDefEq.respectTransparency false in
/-- The actual combined TM2 run ends with every core stack bounded by
`|bits| + fuel * programDepth p`. The Boolean output and both empty loader
stacks are retained. This is a block-time space bound, not bit-cost analysis. -/
theorem combined_numeric_halt_bounded (d : InputData) (p : Program) (output z o : Nat)
    (bits : List Bool) (fuel : Nat) (start r : Result) (b : Bool)
    (hdata : validInputData d = true) (hmain : d.main < p.length)
    (hp : programValid p d.stackCount d.states d.symbols = true)
    (hstart : buildStart d bits = some start) (hrun : run p fuel start = .halted r)
    (he : extractMemory (z,o,output,r.label,r.memory) = some b) :
    ∃ n ≤ fuel, ∃ final,
      runSteps (machine d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState
        d.falseSymbol d.trueSymbol).step (2*bits.length+2+n)
        (Turing.initList (machine d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState
          d.falseSymbol d.trueSymbol) bits) = some final ∧ final.l = none ∧
      decodeStack (z,o,(final.stk (.inr (clip d.stackCount output))).map Fin.val) = some b ∧
      final.stk (.inl false) = [] ∧ final.stk (.inl true) = [] ∧
      ∀ k : Fin (d.stackCount+1), (final.stk (.inr k)).length ≤ bits.length + fuel * programDepth p := by
  obtain ⟨start',hs,hvalid⟩ := buildStart_valid d bits p hdata hmain
  have eq : start = start' := Option.some.inj (hstart.symm.trans hs)
  subst start'
  have hrvalid : Shared.Codes.TM2StatementValidation.resultValid d.stackCount d.states d.symbols p.length r := by
    have hh := run_safe p d.stackCount d.states d.symbols hp fuel start hvalid
    rw [hrun] at hh
    exact hh.1
  have hbound := run_from_input_bound d bits p fuel start hstart
  rw [hrun] at hbound
  have hcore := finite_run_from_config d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState hp fuel start hvalid
  rw [hrun] at hcore
  obtain ⟨n,hn,q,hsteps,hrel,hl⟩ := hcore
  have hdecoded := extract_from_related r q hrvalid hrel b he
  have hstack := related_stack_bound d.stackCount d.states d.symbols p.length q r hrel
    (bits.length + fuel * programDepth p) hbound
  obtain ⟨start',hs',hload⟩ := combined_load_numeric d p output bits hdata
  have eq : start = start' := Option.some.inj (hstart.symm.trans hs')
  subst start'
  have hsim := core_run d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState
    d.falseSymbol d.trueSymbol (finiteConfig d.stackCount d.states d.symbols p.length start) none [] [] n
  rw [hsteps] at hsim
  refine ⟨n,hn,embedCfg d.stackCount d.states d.symbols p.length none [] [] q,?_,?_,?_,?_,?_,?_⟩
  · rw [runSteps_add, hload]
    exact hsim
  · simp [embedCfg, hl, Option.map]
  · exact hdecoded.2
  · rfl
  · rfl
  · exact hstack

/-- A uniform per-stack bound gives a total bound over the finite core. -/
theorem total_stack_bound (ks symbols : Nat)
    (S : Fin (ks+1) → List (Fin (symbols+1))) (bound : Nat)
    (h : ∀ k, (S k).length ≤ bound) :
    (∑ k, (S k).length) ≤ (ks+1)*bound := by
  calc
    (∑ k, (S k).length) ≤ ∑ _k : Fin (ks+1), bound := by
      apply Finset.sum_le_sum
      intro k hk
      exact h k
    _ = (ks+1)*bound := by simp

set_option backward.isDefEq.respectTransparency false in
/-- Every successful checked decision candidate has a single combined TM2
run whose final core stacks have a linear-in-clock total length bound. -/
theorem checked_any_combined_bounded (c : Shared.Codes.TM2Candidate.Candidate) (x : List Bool) (b : Bool)
    (heval : Shared.Codes.TM2CheckedCandidate.evaluate c x = some b) :
    let d := inputDataOfRaw c.1.2.2
    ∃ p n, decodeProgram c.1.1 = some p ∧ n ≤ (x.length+2)^c.1.2.1 ∧ ∃ final,
      runSteps (machine d.stackCount d.states d.symbols p d.inputStack c.2.2.2 d.main d.initialState
        d.falseSymbol d.trueSymbol).step (6*x.length+2+n)
        (Turing.initList (machine d.stackCount d.states d.symbols p d.inputStack c.2.2.2 d.main d.initialState
          d.falseSymbol d.trueSymbol) (BitstringEncoding.bitEncode x)) = some final ∧ final.l = none ∧
      decodeStack (c.2.1,c.2.2.1,(final.stk (.inr (clip d.stackCount c.2.2.2))).map Fin.val) = some b ∧
      final.stk (.inl false) = [] ∧ final.stk (.inl true) = [] ∧
      (∑ k : Fin (d.stackCount+1), (final.stk (.inr k)).length) ≤
        (d.stackCount+1) * (3*x.length + (x.length+2)^c.1.2.1 * programDepth p) := by
  let d := inputDataOfRaw c.1.2.2
  have he : Shared.Codes.TM2CheckedCandidate.evaluate
      ((c.1.1,c.1.2.1,inputRaw d),(c.2.1,c.2.2.1,c.2.2.2)) x = some b := by
    simpa [d] using heval
  obtain ⟨hdata,p,hdecode,hp⟩ := checked_evaluate_validation d c.1.1 c.1.2.1 c.2.1 c.2.2.1 c.2.2.2 x b he
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
    obtain ⟨n,hn,final,hsteps,hl,hout',hleft,hright,hstack⟩ :=
      combined_numeric_halt_bounded d p c.2.2.2 c.2.1 c.2.2.1 (BitstringEncoding.bitEncode x)
        ((x.length+2)^c.1.2.1) start r b hdata hmain hp hstart hr hout
    have hlen := Shared.ComplexityBridge.bitstring_list_encoded_length x
    rw [hlen] at hsteps hstack
    have htime : 2*(3*x.length)+2+n = 6*x.length+2+n := by omega
    rw [htime] at hsteps
    refine ⟨p,n,hdecode,hn,final,hsteps,hl,hout',hleft,hright,?_⟩
    exact total_stack_bound d.stackCount d.symbols (fun k => final.stk (.inr k)) _ hstack

/-- An explicit polynomial bounding total core-stack symbols for one fixed
candidate's decoded program and exponent. -/
noncomputable def stackPolynomial (stackCount exponent : Nat) (p : Program) : Polynomial Nat :=
  Polynomial.C (stackCount+1) *
    (Polynomial.C 3 * Polynomial.X + (Polynomial.X + Polynomial.C 2)^exponent * Polynomial.C (programDepth p))

theorem stackPolynomial_eval (stackCount exponent : Nat) (p : Program) (n : Nat) :
    (stackPolynomial stackCount exponent p).eval n =
      (stackCount+1) * (3*n + (n+2)^exponent * programDepth p) := by
  simp [stackPolynomial]

/-- The stack-size bound exported for checked candidates is the evaluation of
one fixed polynomial; no coefficient or exponent depends on the input. -/
theorem checked_any_combined_polynomial (c : Shared.Codes.TM2Candidate.Candidate) (x : List Bool) (b : Bool)
    (heval : Shared.Codes.TM2CheckedCandidate.evaluate c x = some b) :
    let d := inputDataOfRaw c.1.2.2
    ∃ p n, decodeProgram c.1.1 = some p ∧ n ≤ (x.length+2)^c.1.2.1 ∧ ∃ final,
      runSteps (machine d.stackCount d.states d.symbols p d.inputStack c.2.2.2 d.main d.initialState
        d.falseSymbol d.trueSymbol).step (6*x.length+2+n)
        (Turing.initList (machine d.stackCount d.states d.symbols p d.inputStack c.2.2.2 d.main d.initialState
          d.falseSymbol d.trueSymbol) (BitstringEncoding.bitEncode x)) = some final ∧ final.l = none ∧
      decodeStack (c.2.1,c.2.2.1,(final.stk (.inr (clip d.stackCount c.2.2.2))).map Fin.val) = some b ∧
      final.stk (.inl false) = [] ∧ final.stk (.inl true) = [] ∧
      (∑ k : Fin (d.stackCount+1), (final.stk (.inr k)).length) ≤
        (stackPolynomial d.stackCount c.1.2.1 p).eval x.length := by
  obtain ⟨p,n,hp,hn,final,hrun,hl,hout,hleft,hright,hstack⟩ := checked_any_combined_bounded c x b heval
  refine ⟨p,n,hp,hn,final,hrun,hl,hout,hleft,hright,?_⟩
  rw [stackPolynomial_eval]
  exact hstack

/-- Fixing the candidate and its decoded program fixes the same stack-space
polynomial simultaneously for all inputs and successful outputs. -/
theorem fixed_program_polynomial (c : Shared.Codes.TM2Candidate.Candidate) (p : Program)
    (hdecode : decodeProgram c.1.1 = some p) :
    ∀ x b, Shared.Codes.TM2CheckedCandidate.evaluate c x = some b →
      let d := inputDataOfRaw c.1.2.2
      ∃ n ≤ (x.length+2)^c.1.2.1, ∃ final,
        runSteps (machine d.stackCount d.states d.symbols p d.inputStack c.2.2.2 d.main d.initialState
          d.falseSymbol d.trueSymbol).step (6*x.length+2+n)
          (Turing.initList (machine d.stackCount d.states d.symbols p d.inputStack c.2.2.2 d.main d.initialState
            d.falseSymbol d.trueSymbol) (BitstringEncoding.bitEncode x)) = some final ∧ final.l = none ∧
        decodeStack (c.2.1,c.2.2.1,(final.stk (.inr (clip d.stackCount c.2.2.2))).map Fin.val) = some b ∧
        final.stk (.inl false) = [] ∧ final.stk (.inl true) = [] ∧
        (∑ k : Fin (d.stackCount+1), (final.stk (.inr k)).length) ≤
          (stackPolynomial d.stackCount c.1.2.1 p).eval x.length := by
  intro x b heval
  obtain ⟨p',n,hp',hn,final,hrun,hl,hout,hleft,hright,hstack⟩ := checked_any_combined_polynomial c x b heval
  have heq : p' = p := Option.some.inj (hp'.symm.trans hdecode)
  subst p'
  exact ⟨n,hn,final,hrun,hl,hout,hleft,hright,hstack⟩

end Shared.ComplexityBridge.TM2StackBound
