import Shared.Codes.RawInputCollision
import Shared.Codes.TM2ProgramHalt
import Shared.ComplexityBridge.TM0FiniteProgram

/-! A finite binary post-Turing scanner for canonical Google pair inputs.
It moves right over the pair and stops on the first blank beyond it; all
transitions are moves, so no input cell is rewritten. This is one stage of
an input wrapper, not the complete input-to-stack serialization. -/
namespace Shared.ComplexityBridge.PairInputScanner
open Turing
open Shared.ComplexityBridge.TM2Symbols
open Shared.Codes.TM2Program (runSteps_front runSteps_add)

abbrev State := Fin 5

def pairMark : State := ⟨0,by decide⟩
def pairData : State := ⟨1,by decide⟩
def witnessMark : State := ⟨2,by decide⟩
def witnessData : State := ⟨3,by decide⟩
def witnessEnd : State := ⟨4,by decide⟩

def machine : TM0.Machine Bool State := fun q b =>
  if q = pairMark then some (if b then pairData else witnessMark,.move .right)
  else if q = pairData then some (pairMark,.move .right)
  else if q = witnessMark then if b then some (witnessData,.move .right) else none
  else if q = witnessData then some (witnessEnd,.move .right)
  else some (witnessMark,.move .right)

def tapeAt (L : ListBlank Bool) (xs : List Bool) : Tape Bool := Tape.mk' L (ListBlank.mk xs)

def consumed (L : ListBlank Bool) (xs : List Bool) : ListBlank Bool :=
  ListBlank.append xs.reverse L

theorem consumed_nil (L : ListBlank Bool) : consumed L [] = L := rfl

theorem consumed_cons (L : ListBlank Bool) (b : Bool) (xs : List Bool) :
    consumed L (b::xs) = consumed (L.cons b) xs := by
  simp [consumed,List.reverse_cons,ListBlank.append_assoc]

theorem step_on (q q' : State) (b : Bool) (L : ListBlank Bool) (xs : List Bool)
    (h : machine q b = some (q',.move .right)) :
    TM0.step machine ⟨q,tapeAt L (b::xs)⟩ = some ⟨q',tapeAt (L.cons b) xs⟩ := by
  simp [TM0.step,tapeAt,Tape.move_right_mk',ListBlank.head_mk,ListBlank.tail_mk,h]

theorem pair_true (L : ListBlank Bool) (xs : List Bool) :
    TM0.step machine ⟨pairMark,tapeAt L (true::xs)⟩ = some ⟨pairData,tapeAt (L.cons true) xs⟩ :=
  step_on _ _ _ _ _ (by rfl)

theorem pair_data (L : ListBlank Bool) (b : Bool) (xs : List Bool) :
    TM0.step machine ⟨pairData,tapeAt L (b::xs)⟩ = some ⟨pairMark,tapeAt (L.cons b) xs⟩ := by
  apply step_on
  cases b <;> rfl

theorem pair_end (L : ListBlank Bool) (xs : List Bool) :
    TM0.step machine ⟨pairMark,tapeAt L (false::xs)⟩ = some ⟨witnessMark,tapeAt (L.cons false) xs⟩ :=
  step_on _ _ _ _ _ (by rfl)

theorem witness_true (L : ListBlank Bool) (xs : List Bool) :
    TM0.step machine ⟨witnessMark,tapeAt L (true::xs)⟩ = some ⟨witnessData,tapeAt (L.cons true) xs⟩ :=
  step_on _ _ _ _ _ (by rfl)

theorem witness_data (L : ListBlank Bool) (b : Bool) (xs : List Bool) :
    TM0.step machine ⟨witnessData,tapeAt L (b::xs)⟩ = some ⟨witnessEnd,tapeAt (L.cons b) xs⟩ := by
  apply step_on
  cases b <;> rfl

theorem witness_end (L : ListBlank Bool) (xs : List Bool) :
    TM0.step machine ⟨witnessEnd,tapeAt L (false::xs)⟩ = some ⟨witnessMark,tapeAt (L.cons false) xs⟩ :=
  step_on _ _ _ _ _ (by rfl)

theorem halt_at_blank (L : ListBlank Bool) : TM0.step machine ⟨witnessMark,tapeAt L []⟩ = none := by
  simp [TM0.step,machine,tapeAt,Tape.mk'_head,ListBlank.head_mk,witnessMark,pairMark,pairData]

/-- The first delimited block is scanned exactly, with its payload preserved
on the left side of the head. -/
theorem scan_delimit (xs suffix : List Bool) (L : ListBlank Bool) :
    runSteps (TM0.step machine) (2*xs.length+1)
      ⟨pairMark,tapeAt L (BitstringEncoding.delimit xs ++ suffix)⟩ =
      some ⟨witnessMark,tapeAt (consumed L (BitstringEncoding.delimit xs)) suffix⟩ := by
  induction xs generalizing L with
  | nil => simpa [BitstringEncoding.delimit,consumed,runSteps] using pair_end L suffix
  | cons b xs ih =>
    simp only [BitstringEncoding.delimit,List.cons_append,List.length_cons]
    rw [show 2*(xs.length+1)+1 = (2*xs.length+1)+2 by omega,runSteps_front,pair_true]
    simp only [Option.bind_some]
    rw [show 2*xs.length+1+1 = (2*xs.length+1)+1 by rfl,runSteps_front,pair_data]
    simp only [Option.bind_some]
    simpa only [consumed_cons] using ih ((L.cons true).cons b)

/-- Each Boolean list element is a three-bit self-delimiting block. -/
theorem scan_witness (ws : List Bool) (L : ListBlank Bool) :
    runSteps (TM0.step machine) (3*ws.length)
      ⟨witnessMark,tapeAt L (BitstringEncoding.bitEncode ws)⟩ =
      some ⟨witnessMark,tapeAt (consumed L (BitstringEncoding.bitEncode ws)) []⟩ := by
  induction ws generalizing L with
  | nil => change some _ = some _; rfl
  | cons b ws ih =>
    change runSteps (TM0.step machine) (3*(ws.length+1))
      ⟨witnessMark,tapeAt L (true::b::false::BitstringEncoding.bitEncode ws)⟩ = _
    rw [show 3*(ws.length+1) = ((3*ws.length+1)+1)+1 by omega,runSteps_front,witness_true]
    simp only [Option.bind_some]
    rw [runSteps_front,witness_data]
    simp only [Option.bind_some]
    rw [runSteps_front,witness_end]
    simp only [Option.bind_some]
    change runSteps (TM0.step machine) (3*ws.length)
      ⟨witnessMark,tapeAt (((L.cons true).cons b).cons false) (BitstringEncoding.bitEncode ws)⟩ =
      some ⟨witnessMark,tapeAt (consumed L (true::b::false::BitstringEncoding.bitEncode ws)) []⟩
    simpa only [consumed_cons] using ih (((L.cons true).cons b).cons false)

theorem consumed_append (L : ListBlank Bool) (xs ys : List Bool) :
    consumed (consumed L xs) ys = consumed L (xs ++ ys) := by
  simp [consumed,List.reverse_append,ListBlank.append_assoc]

/-- From the ordinary binary input tape, a canonical pair is scanned in
exactly its full encoded length. The complete input is retained to the left
of the head, and the machine halts on the blank immediately afterward. -/
theorem scan_pair (x w : List Bool) :
    let input := BitstringEncoding.bitEncode (x,w)
    let finish : TM0.Cfg Bool State := ⟨witnessMark,tapeAt (consumed ∅ input) []⟩
    runSteps (TM0.step machine) input.length (TM0.init input) = some finish ∧
      TM0.step machine finish = none := by
  let a := BitstringEncoding.bitEncode x
  let b := BitstringEncoding.bitEncode w
  have hi : BitstringEncoding.bitEncode (x,w) = BitstringEncoding.delimit a ++ b := rfl
  have hlen : (BitstringEncoding.bitEncode (x,w)).length = 2*a.length+1+3*w.length := by
    rw [hi,List.length_append,BitstringEncoding.length_delimit]
    simp [b,Shared.ComplexityBridge.bitstring_list_encoded_length]
  have hstart : (TM0.init (BitstringEncoding.bitEncode (x,w)) : TM0.Cfg Bool State) =
      ⟨pairMark,tapeAt ∅ (BitstringEncoding.delimit a ++ b)⟩ := by
    rw [hi]
    rfl
  constructor
  · rw [hlen,hstart,runSteps_add,scan_delimit]
    simp only [Option.bind_some]
    change runSteps (TM0.step machine) (3*w.length)
      ⟨witnessMark,tapeAt (consumed ∅ (BitstringEncoding.delimit a)) (BitstringEncoding.bitEncode w)⟩ = _
    rw [scan_witness,consumed_append,← hi]
  · exact halt_at_blank _

/-- The exact scanner time uses the full pair encoding, including the first
component's delimiter and both input lengths. -/
theorem scan_pair_time (x w : List Bool) :
    (BitstringEncoding.bitEncode (x,w)).length = 6*x.length+1+3*w.length :=
  Shared.ComplexityBridge.bitstring_pair_encoded_length x w

/-- An extended machine may replace the scanner's final halt row with its
own continuation. All live scanner rows must agree. -/
def ExtendsScanner {Λ : Type} [Inhabited Λ]
    (M : TM0.Machine Bool Λ) (state : State → Λ) : Prop :=
  ∀ q b next op, machine q b = some (next,op) → M (state q) b = some (state next,op)

def liftConfig {Λ : Type} (state : State → Λ) (c : TM0.Cfg Bool State) : TM0.Cfg Bool Λ :=
  ⟨state c.q,c.Tape⟩

theorem extend_step {Λ : Type} [Inhabited Λ]
    (M : TM0.Machine Bool Λ) (state : State → Λ) (hext : ExtendsScanner M state)
    (c d : TM0.Cfg Bool State) (h : TM0.step machine c = some d) :
    TM0.step M (liftConfig state c) = some (liftConfig state d) := by
  rcases c with ⟨q,T⟩
  cases hr : machine q T.head with
  | none => simp [TM0.step,hr] at h
  | some pair =>
    rcases pair with ⟨next,op⟩
    have hm := hext q T.head next op hr
    cases op <;> simp [TM0.step,hr] at h <;> cases h <;> simp [TM0.step,liftConfig,hm]

theorem extend_run {Λ : Type} [Inhabited Λ]
    (M : TM0.Machine Bool Λ) (state : State → Λ) (hext : ExtendsScanner M state)
    (n : Nat) (c d : TM0.Cfg Bool State) (h : runSteps (TM0.step machine) n c = some d) :
    runSteps (TM0.step M) n (liftConfig state c) = some (liftConfig state d) := by
  induction n generalizing c with
  | zero =>
    change some c = some d at h
    cases Option.some.inj h
    rfl
  | succ n ih =>
    rw [runSteps_front] at h
    cases hs : TM0.step machine c with
    | none => rw [hs] at h; contradiction
    | some mid =>
      rw [hs] at h
      rw [runSteps_front,extend_step M state hext c mid hs]
      exact ih mid h

/-- The parser can be embedded into a larger machine: its continuation is
reached after exactly the input length, with the entire input preserved. -/
theorem scan_pair_extended {Λ : Type} [Inhabited Λ]
    (M : TM0.Machine Bool Λ) (state : State → Λ) (hext : ExtendsScanner M state)
    (hstart : state pairMark = default) (x w : List Bool) :
    let input := BitstringEncoding.bitEncode (x,w)
    runSteps (TM0.step M) input.length (TM0.init input) =
      some ⟨state witnessMark,tapeAt (consumed ∅ input) []⟩ := by
  have h := extend_run M state hext (BitstringEncoding.bitEncode (x,w)).length
    (TM0.init (BitstringEncoding.bitEncode (x,w)))
    ⟨witnessMark,tapeAt (consumed ∅ (BitstringEncoding.bitEncode (x,w))) []⟩ (scan_pair x w).1
  change runSteps (TM0.step M) (BitstringEncoding.bitEncode (x,w)).length
    ⟨state pairMark,Tape.mk₁ (BitstringEncoding.bitEncode (x,w))⟩ = _ at h
  rw [hstart] at h
  exact h

/-- An actual continuation transition follows the complete scan. Its
operation is explicit and charged as one additional post-Turing step. -/
theorem scan_pair_continue {Λ : Type} [Inhabited Λ]
    (M : TM0.Machine Bool Λ) (state : State → Λ) (hext : ExtendsScanner M state)
    (hstart : state pairMark = default) (next : Λ) (op : TM0.Stmt Bool)
    (hend : M (state witnessMark) false = some (next,op)) (x w : List Bool) :
    let input := BitstringEncoding.bitEncode (x,w)
    let tape := tapeAt (consumed ∅ input) []
    runSteps (TM0.step M) (input.length+1) (TM0.init input) =
      some ⟨next,match op with | .move dir => tape.move dir | .write b => tape.write b⟩ := by
  change (runSteps (TM0.step M) (BitstringEncoding.bitEncode (x,w)).length
    (TM0.init (BitstringEncoding.bitEncode (x,w)))).bind (TM0.step M) = _
  rw [scan_pair_extended M state hext hstart x w]
  simp only [Option.bind_some,TM0.step]
  have hh : (tapeAt (consumed ∅ (BitstringEncoding.bitEncode (x,w))) []).head = false := by
    simp [tapeAt]
  rw [hh]
  cases op <;> simp [hend]

/-- The same continuation boundary is reached by the shared finite-program
interpreter, with at most two target transitions per scanner move. -/
theorem finite_program_scan {m : Nat} [Inhabited (Fin m)]
    (M : TM0FiniteProgram.Machine m) (state : State → Fin m) (hext : ExtendsScanner M state)
    (hstart : state pairMark = default) (hzero : (default : Fin m).val = 0) (x w : List Bool) :
    let input := BitstringEncoding.bitEncode (x,w)
    ∃ d tape, input.length ≤ d ∧ d ≤ 2*input.length ∧
      TM0FiniteProgram.tape tape = tapeAt (consumed ∅ input) [] ∧
      Shared.Codes.FinitePrograms.run (TM0FiniteProgram.program M)
        (Shared.Codes.FinitePrograms.initial input) d =
          some (.inr (TM0FiniteProgram.mainIndex (state witnessMark),tape)) := by
  let input := BitstringEncoding.bitEncode (x,w)
  have hs := scan_pair_extended M state hext hstart x w
  have hr : runSteps (TM0.step M) input.length
      ⟨default,TM0FiniteProgram.tape (Shared.Codes.FinitePrograms.initial input).2⟩ =
      some ⟨state witnessMark,tapeAt (consumed ∅ input) []⟩ := by
    simpa [input,TM0.init,TM0FiniteProgram.tape_initial] using hs
  obtain ⟨d,t,hlo,hhi,ht,hsim⟩ := TM0FiniteProgram.run_simulation M input.length default
    (state witnessMark) (Shared.Codes.FinitePrograms.initial input).2 (tapeAt (consumed ∅ input) []) hr
  refine ⟨d,t,hlo,hhi,ht,?_⟩
  have hh : (TM0FiniteProgram.mainIndex (default : Fin m),
      (Shared.Codes.FinitePrograms.initial input).2) = Shared.Codes.FinitePrograms.initial input := by
    simp [TM0FiniteProgram.mainIndex,hzero,Shared.Codes.FinitePrograms.initial]
  rw [hh] at hsim
  exact hsim

/-- Instantiating the extension with the actual five-state table gives a
concrete valid finite program, with no assumed interpreter or table oracle. -/
theorem concrete_finite_scan (x w : List Bool) :
    let input := BitstringEncoding.bitEncode (x,w)
    Shared.Codes.FinitePrograms.valid (TM0FiniteProgram.program machine) = true ∧
      ∃ d tape, input.length ≤ d ∧ d ≤ 2*input.length ∧
        TM0FiniteProgram.tape tape = tapeAt (consumed ∅ input) [] ∧
        Shared.Codes.FinitePrograms.run (TM0FiniteProgram.program machine)
          (Shared.Codes.FinitePrograms.initial input) d =
            some (.inr (TM0FiniteProgram.mainIndex witnessMark,tape)) := by
  constructor
  · exact TM0FiniteProgram.program_valid machine
  · exact finite_program_scan machine id (by intro q b next op h; exact h) rfl rfl x w

namespace Fixtures
example : (BitstringEncoding.bitEncode (([] : List Bool),([] : List Bool))).length = 1 := by decide
example : (BitstringEncoding.bitEncode (([false] : List Bool),([false] : List Bool))).length = 10 := by decide
example : TM0.step machine ⟨witnessMark,tapeAt ∅ []⟩ = none := halt_at_blank _
example : Shared.Codes.FinitePrograms.bounded (TM0FiniteProgram.program machine)
    (BitstringEncoding.bitEncode (([] : List Bool),([] : List Bool))) 1 = none := by decide
example : Shared.Codes.FinitePrograms.bounded (TM0FiniteProgram.program machine)
    (BitstringEncoding.bitEncode (([] : List Bool),([] : List Bool))) 2 = some false := by decide
end Fixtures

end Shared.ComplexityBridge.PairInputScanner
