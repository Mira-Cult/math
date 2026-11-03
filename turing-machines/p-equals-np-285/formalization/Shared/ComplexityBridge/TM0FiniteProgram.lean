import Shared.Codes.FinitePrograms
import Shared.Codes.TM2ProgramHalt
import Shared.ComplexityBridge.ClockBounds
import Mathlib.Computability.TuringMachine.PostTuringMachine

/-! Binary post-Turing machines as executable finite programs.
A move takes one target transition; a write takes two, since finite-program
transitions must move the head. A halted machine returns the bit under its head.
The input/output wrapper for translated TM2 machines is a separate obligation. -/
namespace Shared.ComplexityBridge.TM0FiniteProgram
open Turing
open Shared.Codes.FinitePrograms
open Shared.Codes.TM2Program (runSteps_add runSteps_front)
open Shared.ComplexityBridge.TM2Symbols

variable {m : Nat}

abbrev Machine (m : Nat) := Fin m → Bool → Option (Fin m × TM0.Stmt Bool)

def mainIndex (q : Fin m) : Nat := 2*q.val
def pendingIndex (q : Fin m) : Nat := 2*q.val+1

def mainRow (M : Machine m) (q : Fin m) (b : Bool) : Row :=
  match M q b with
  | none => (b,true,0,if b then 2 else 1)
  | some (next,.move .left) => (b,false,mainIndex next,0)
  | some (next,.move .right) => (b,true,mainIndex next,0)
  | some (next,.write w) => (w,true,pendingIndex next,0)

def pendingRow (q : Fin m) (b : Bool) : Row := (b,false,mainIndex q,0)

def sourceIndex (i : Fin (2*m)) : Fin m :=
  ⟨i.val / 2, by have h := i.isLt; omega⟩

def rowPair (M : Machine m) (i : Fin (2*m)) : Row × Row :=
  let q := sourceIndex i
  if i.val % 2 = 0 then (mainRow M q false,mainRow M q true)
  else (pendingRow q false,pendingRow q true)

def program (M : Machine m) : Program := List.ofFn (rowPair M)

@[simp] theorem program_length (M : Machine m) : (program M).length = 2*m := by
  simp [program]

theorem sourceIndex_main (q : Fin m) : sourceIndex ⟨mainIndex q, by have := q.isLt; dsimp [mainIndex]; omega⟩ = q := by
  apply Fin.ext
  simp [sourceIndex,mainIndex]

theorem sourceIndex_pending (q : Fin m) : sourceIndex ⟨pendingIndex q, by have := q.isLt; dsimp [pendingIndex]; omega⟩ = q := by
  apply Fin.ext
  dsimp [sourceIndex,pendingIndex]
  omega

theorem program_main (M : Machine m) (q : Fin m) :
    (program M)[mainIndex q]? = some (mainRow M q false,mainRow M q true) := by
  have h : mainIndex q < (program M).length := by rw [program_length]; have := q.isLt; dsimp [mainIndex]; omega
  rw [List.getElem?_eq_getElem h]
  simp only [program,List.getElem_ofFn]
  have hm : mainIndex q % 2 = 0 := by simp [mainIndex]
  simp only [rowPair,hm,if_true,sourceIndex_main]

theorem program_pending (M : Machine m) (q : Fin m) :
    (program M)[pendingIndex q]? = some (pendingRow q false,pendingRow q true) := by
  have h : pendingIndex q < (program M).length := by rw [program_length]; have := q.isLt; dsimp [pendingIndex]; omega
  rw [List.getElem?_eq_getElem h]
  simp only [program,List.getElem_ofFn]
  have hm : pendingIndex q % 2 ≠ 0 := by simp [pendingIndex]
  simp only [rowPair,hm,if_false,sourceIndex_pending]

/-- The list tape and mathlib's blank-quotiented tape represent the same tape. -/
def tape (t : Shared.Codes.FinitePrograms.Tape) : Turing.Tape Bool :=
  ⟨t.2.1,ListBlank.mk t.1,ListBlank.mk t.2.2⟩

theorem tape_move (t : Shared.Codes.FinitePrograms.Tape) (w : Bool) (d : Dir) :
    tape (moveTape (d == .left) w t) = ((tape t).write w).move d := by
  rcases t with ⟨l,b,r⟩
  cases d <;> cases l <;> cases r <;> simp [tape,moveTape,Tape.write,Tape.move,ListBlank.head_mk,ListBlank.tail_mk,ListBlank.cons_mk]

theorem tape_initial (input : List Bool) : tape (initial input).2 = Turing.Tape.mk₁ input := by
  cases input with
  | nil => simp [tape,initial,Tape.mk₁,Tape.mk₂,Tape.mk',ListBlank.head_mk,ListBlank.tail_mk]
  | cons b bs => simp [tape,initial,Tape.mk₁,Tape.mk₂,Tape.mk',ListBlank.head_mk,ListBlank.tail_mk]

/-- The target's pending state returns left without changing the scanned bit. -/
theorem pending_step (M : Machine m) (q : Fin m) (t : Shared.Codes.FinitePrograms.Tape) :
    run (program M) (pendingIndex q,t) 1 =
      some (.inr (mainIndex q,moveTape true t.2.1 t)) := by
  cases hb : t.2.1 <;> simp [run,advance,step,program_pending,pendingRow,hb]

/-- Each live post-Turing step executes in one or two finite-program steps. -/
theorem one_step (M : Machine m) (q q' : Fin m) (t : Shared.Codes.FinitePrograms.Tape)
    (op : TM0.Stmt Bool) (h : M q t.2.1 = some (q',op)) :
    ∃ d t', 1 ≤ d ∧ d ≤ 2 ∧
      run (program M) (mainIndex q,t) d = some (.inr (mainIndex q',t')) ∧
      tape t' = (match op with | .move dir => (tape t).move dir | .write b => (tape t).write b) := by
  cases op with
  | move dir =>
    cases dir with
    | left =>
      refine ⟨1,moveTape true t.2.1 t,by omega,by omega,?_,?_⟩
      · cases hb : t.2.1 <;> simp only [hb] at h <;> simp [run,advance,step,program_main,mainRow,hb,h]
      · have ht := tape_move t t.2.1 Dir.left
        change tape (moveTape true t.2.1 t) = ((tape t).write (tape t).head).move .left at ht
        simpa using ht
    | right =>
      refine ⟨1,moveTape false t.2.1 t,by omega,by omega,?_,?_⟩
      · cases hb : t.2.1 <;> simp only [hb] at h <;> simp [run,advance,step,program_main,mainRow,hb,h]
      · have ht := tape_move t t.2.1 Dir.right
        change tape (moveTape false t.2.1 t) = ((tape t).write (tape t).head).move .right at ht
        simpa using ht
  | write b =>
    let t₁ := moveTape false b t
    let t₂ := moveTape true t₁.2.1 t₁
    refine ⟨2,t₂,by omega,by omega,?_,?_⟩
    · change advance (program M) (run (program M) (mainIndex q,t) 1) = _
      have hfirst : run (program M) (mainIndex q,t) 1 = some (.inr (pendingIndex q',t₁)) := by
        cases hb : t.2.1 <;> simp only [hb] at h <;> simp [run,advance,step,program_main,mainRow,hb,h,t₁]
      rw [hfirst]
      change step (program M) (pendingIndex q',t₁) = _
      have hsecond := pending_step M q' t₁
      exact hsecond
    · have h₁ := tape_move t b Dir.right
      change tape t₁ = ((tape t).write b).move .right at h₁
      have h₂ := tape_move t₁ t₁.2.1 Dir.left
      change tape t₂ = ((tape t₁).write (tape t₁).head).move .left at h₂
      rw [h₂,Tape.write_self,h₁,Tape.move_right_left]

/-- A halted source row returns the bit currently under the head. -/
theorem halted_step (M : Machine m) (q : Fin m) (t : Shared.Codes.FinitePrograms.Tape)
    (h : M q t.2.1 = none) :
    run (program M) (mainIndex q,t) 1 = some (.inl t.2.1) := by
  cases hb : t.2.1 <;> simp only [hb] at h <;> simp [run,advance,step,program_main,mainRow,hb,h]

theorem run_continue (p : Program) (c c' : Config) (d e : Nat)
    (h : run p c d = some (.inr c')) : run p c (d+e) = run p c' e := by
  rw [run_add,h]
  induction e with
  | zero => rfl
  | succ e ih =>
    rw [Function.iterate_succ_apply',ih,run_succ]

section
variable [Inhabited (Fin m)]

/-- Every successful source run has an exact target segment costing between
one and two target transitions per source step. -/
theorem run_simulation (M : Machine m) (n : Nat) (q q' : Fin m)
    (t : Shared.Codes.FinitePrograms.Tape) (T' : Turing.Tape Bool)
    (h : runSteps (TM0.step M) n ⟨q,tape t⟩ = some ⟨q',T'⟩) :
    ∃ d t', n ≤ d ∧ d ≤ 2*n ∧ tape t' = T' ∧
      run (program M) (mainIndex q,t) d = some (.inr (mainIndex q',t')) := by
  induction n generalizing q t with
  | zero =>
    change some (TM0.Cfg.mk q (tape t)) = some (TM0.Cfg.mk q' T') at h
    have he := Option.some.inj h
    cases he
    exact ⟨0,t,by omega,by omega,rfl,rfl⟩
  | succ n ih =>
    rw [runSteps_front] at h
    change (TM0.step M ⟨q,tape t⟩).bind (runSteps (TM0.step M) n) = _ at h
    cases hs : M q t.2.1 with
    | none =>
      have hf : TM0.step M ⟨q,tape t⟩ = none := by simp [TM0.step,tape,hs]
      rw [hf] at h
      contradiction
    | some pair =>
      rcases pair with ⟨next,op⟩
      let T := match op with | .move dir => (tape t).move dir | .write b => (tape t).write b
      have hf : TM0.step M ⟨q,tape t⟩ = some ⟨next,T⟩ := by cases op <;> simp [TM0.step,tape,hs,T]
      rw [hf] at h
      obtain ⟨d,u,hdpos,hdbound,hfirst,hu⟩ := one_step M q next t op hs
      have hrest : runSteps (TM0.step M) n ⟨next,tape u⟩ = some ⟨q',T'⟩ := by
        rw [hu]
        cases op <;> simpa [T] using h
      obtain ⟨e,v,hepos,hebound,hv,hsecond⟩ := ih next u hrest
      refine ⟨d+e,v,by omega,by omega,hv,?_⟩
      rw [run_continue _ _ _ _ _ hfirst]
      exact hsecond

/-- The whole initialized machine computes the final head bit within
`2*n+1` finite-program transitions, including the output-tag transition. -/
theorem bounded_from_source_run (M : Machine m) (input : List Bool) (n : Nat)
    (q' : Fin m) (T' : Turing.Tape Bool)
    (hstart : (default : Fin m).val = 0)
    (hrun : runSteps (TM0.step M) n (TM0.init input) = some ⟨q',T'⟩)
    (hhalt : M q' T'.head = none) :
    bounded (program M) input (2*n+1) = some T'.head := by
  have hs : runSteps (TM0.step M) n ⟨default,tape (initial input).2⟩ = some ⟨q',T'⟩ := by
    simpa [TM0.init,tape_initial] using hrun
  obtain ⟨d,t',hlo,hhi,ht,hr⟩ := run_simulation M n default q' (initial input).2 T' hs
  have hq : mainIndex (default : Fin m) = 0 := by simp [mainIndex,hstart]
  have hi : (mainIndex (default : Fin m),(initial input).2) = initial input := by
    simp [hq,initial]
  rw [hi] at hr
  have hh : M q' t'.2.1 = none := by
    change M q' (tape t').head = none
    rw [ht]
    exact hhalt
  have hbit : t'.2.1 = T'.head := by
    have he := congrArg Turing.Tape.head ht
    exact he
  apply (bounded_iff_result (program M) input (2*n+1) T'.head).2
  refine ⟨d+1,by omega,?_⟩
  rw [run_continue _ _ _ _ _ hr]
  simpa [hbit] using halted_step M q' t' hh

/-- A uniform source polynomial yields a uniform target polynomial for
Boolean head output, measured in raw input bits and target transitions. -/
theorem polynomial_computes (M : Machine m) (f : List Bool → Bool) (p : Polynomial Nat)
    (hstart : (default : Fin m).val = 0)
    (source : ∀ input, ∃ n q T, n ≤ p.eval input.length ∧
      runSteps (TM0.step M) n (TM0.init input) = some ⟨q,T⟩ ∧
      M q T.head = none ∧ T.head = f input) :
    ∀ input, bounded (program M) input ((2*p+1).eval input.length) = some (f input) := by
  intro input
  obtain ⟨n,q,T,hn,hr,hh,hout⟩ := source input
  have hb := bounded_from_source_run M input n q T hstart hr hh
  rw [hout] at hb
  obtain ⟨d,hd,he⟩ := (bounded_iff_result (program M) input (2*n+1) (f input)).1 hb
  apply (bounded_iff_result (program M) input ((2*p+1).eval input.length) (f input)).2
  refine ⟨d,?_,he⟩
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one]
  omega

omit [Inhabited (Fin m)] in
theorem mainRow_valid (M : Machine m) (q : Fin m) (b : Bool) :
    validRow (2*m) (mainRow M q b) = true := by
  cases hm : M q b with
  | none => cases b <;> simp [mainRow,hm,validRow]
  | some pair =>
    rcases pair with ⟨q',op⟩
    have hq := q'.isLt
    cases op with
    | move dir => cases dir <;> simp [mainRow,hm,validRow,mainIndex]
    | write w => simp [mainRow,hm,validRow,pendingIndex]; omega

omit [Inhabited (Fin m)] in
theorem pendingRow_valid (q : Fin m) (b : Bool) :
    validRow (2*m) (pendingRow q b) = true := by
  have hq := q.isLt
  simp [pendingRow,validRow,mainIndex]

/-- The generated table is accepted by the shared candidate decoder. -/
theorem program_valid (M : Machine m) : valid (program M) = true := by
  have hm : 0 < m := by have h := (default : Fin m).isLt; omega
  have hn : program M ≠ [] := by
    apply List.ne_nil_iff_length_pos.mpr
    rw [program_length]
    omega
  simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true]
  constructor
  · cases he : (program M).isEmpty with
    | false => rfl
    | true => exact False.elim (hn (List.isEmpty_iff.mp he))
  · intro pair hp
    change pair ∈ List.ofFn (rowPair M) at hp
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    rw [program_length]
    by_cases h : i.val % 2 = 0
    · simp only [rowPair,h,if_true]
      exact ⟨mainRow_valid M _ _,mainRow_valid M _ _⟩
    · simp only [rowPair,h,if_false]
      exact ⟨pendingRow_valid _ _,pendingRow_valid _ _⟩

theorem program_candidate_coverage (M : Machine m) (k : Nat) :
    ∃ e, decode e = some (k,program M) :=
  candidate_coverage (k,program M) (program_valid M)

/-- A polynomially bounded Boolean-head machine is represented by a valid
fixed-exponent candidate from the shared enumeration. -/
theorem candidate_implements (M : Machine m) (f : List Bool → Bool) (p : Polynomial Nat)
    (hstart : (default : Fin m).val = 0)
    (source : ∀ input, ∃ n q T, n ≤ p.eval input.length ∧
      runSteps (TM0.step M) n (TM0.init input) = some ⟨q,T⟩ ∧
      M q T.head = none ∧ T.head = f input) :
    ∃ candidate : Candidate, valid candidate.2 = true ∧
      (∃ e, decode e = some candidate) ∧ ∀ input, evaluate candidate input = some (f input) := by
  obtain ⟨k,hk⟩ := Shared.ComplexityBridge.ClockBounds.polynomial_fixed_exponent (2*p+1)
  refine ⟨(k,program M),program_valid M,program_candidate_coverage M k,?_⟩
  intro input
  have hb := polynomial_computes M f p hstart source input
  obtain ⟨d,hd,hr⟩ := (bounded_iff_result (program M) input ((2*p+1).eval input.length) (f input)).1 hb
  change bounded (program M) input ((input.length+2)^k) = some (f input)
  exact (bounded_iff_result (program M) input _ (f input)).2 ⟨d,le_trans hd (hk input.length),hr⟩

end

namespace Fixtures

def writeThenHalt : Machine 2 := fun q _ =>
  if q.val = 0 then some (⟨1,by decide⟩,.write true) else none

def leftThenHalt : Machine 2 := fun q _ =>
  if q.val = 0 then some (⟨1,by decide⟩,.move .left) else none

example : bounded (program writeThenHalt) [] 2 = none := by decide
example : bounded (program writeThenHalt) [] 3 = some true := by decide
example : bounded (program leftThenHalt) [true] 1 = none := by decide
example : bounded (program leftThenHalt) [true] 2 = some false := by decide

end Fixtures

end Shared.ComplexityBridge.TM0FiniteProgram
