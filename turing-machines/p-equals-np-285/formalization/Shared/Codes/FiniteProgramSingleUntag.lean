import Shared.Codes.FiniteProgramSingleInput
import Shared.Codes.FiniteProgramTwoExit
import Shared.Codes.FiniteProgramWitnessFirst
import Shared.Codes.FiniteProgramMirror
import Shared.ComplexityBridge.FiniteProgramTM2
import Shared.ComplexityBridge.TM2PairFirst
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false

/-! Connect the nonempty single-input scanner to a literal untagger. The raw
pair input is produced in reflected tape orientation for a mirrored finite
continuation. This module does not yet implement the empty-input branch. -/
namespace Shared.Codes.FiniteProgramSingleUntag
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (link shiftConfig shiftStatus run_shift)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel StatusRel run_related)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.Codes.FiniteProgramBitShuttle (tagged)
open Shared.Codes.FiniteProgramUntag (cursor cost padding)

abbrev source := Shared.Codes.FiniteProgramSingleInput.program [true] [true]
abbrev stop := 5+Shared.Codes.FiniteProgramWitnessController.boundary [true] [true]

def erase : Program :=
  [((false,true,1,0),(false,true,1,0)),
   ((false,false,2,0),(true,false,2,0)),
   ((false,true,0,1),(true,true,0,1))]

def convert : Program := Shared.Codes.FiniteProgramSplice.program erase Shared.Codes.FiniteProgramUntag.program

theorem erase_valid : valid erase = true := by decide

theorem convert_valid : valid convert = true :=
  Shared.Codes.FiniteProgramSplice.program_valid erase Shared.Codes.FiniteProgramUntag.program
    erase_valid Shared.Codes.FiniteProgramUntag.program_valid

theorem stop_bound : stop < source.length := by
  have h : Shared.Codes.FiniteProgramWitnessController.boundary [true] [true] <
      (Shared.Codes.FiniteProgramWitnessController.program [true] [true]).length :=
    Shared.Codes.FiniteProgramWitnessFirst.boundary_bound [true] [true]
  simp only [source,Shared.Codes.FiniteProgramSingleInput.program,link,
    Shared.Codes.FiniteProgramSingleInput.pre_length,List.length_append,List.length_map,List.length_nil,
    Nat.add_zero,stop]
  omega

theorem stop_step (t : Tape) : step source (stop,t) = some (.inl false) := by
  let s := Shared.Codes.FiniteProgramWitnessController.program [true] [true]
  let q := Shared.Codes.FiniteProgramWitnessController.boundary [true] [true]
  have hbound : q < s.length := Shared.Codes.FiniteProgramWitnessFirst.boundary_bound [true] [true]
  have h := Shared.Codes.FiniteProgramLink.step_shift Shared.Codes.FiniteProgramSingleInput.pre s [] (q,t) hbound
  rw [Shared.Codes.FiniteProgramWitnessFirst.scanner_boundary] at h
  simpa [source,Shared.Codes.FiniteProgramSingleInput.program,stop,s,q,shiftConfig,shiftStatus] using h

def stage : Program := Shared.Codes.FiniteProgramTwoExit.program source convert stop stop

theorem stage_valid : valid stage = true :=
  Shared.Codes.FiniteProgramTwoExit.program_valid source convert stop stop
    (Shared.Codes.FiniteProgramSingleInput.program_valid [true] [true]) convert_valid stop_bound stop_bound

theorem erase_start (xs : List Bool) :
    run convert (0,tapeAt [] (true::false::tagged xs ++ [false,false,false])) 2 =
      some (.inr (2,tapeAt [] (false::false::tagged xs ++ [false,false,false]))) := by
  simp [run,advance,step,convert,Shared.Codes.FiniteProgramSplice.program,
    Shared.Codes.FiniteProgramSplice.stem,link,erase,tapeAt,moveTape]

theorem convert_run (xs : List Bool) :
    run convert (0,tapeAt [] (true::false::tagged xs ++ [false,false,false])) (2+cost xs) =
      some (.inr (14,tapeAt (cursor false [] xs).2
        ((cursor false [] xs).1::false::false::padding xs.length [false,false]))) := by
  have hshift := run_shift (Shared.Codes.FiniteProgramSplice.stem erase)
    Shared.Codes.FiniteProgramUntag.program [] Shared.Codes.FiniteProgramUntag.program_valid
    (0,tapeAt [] (false::false::tagged xs ++ [false,false,false]))
    (by simp [Shared.Codes.FiniteProgramUntag.program_length]) (cost xs)
  rw [Shared.Codes.FiniteProgramUntag.run_all xs [] [false,false] false] at hshift
  have hh : (Shared.Codes.FiniteProgramSplice.stem erase).length = 2 := by simp [Shared.Codes.FiniteProgramSplice.stem,erase]
  rw [hh] at hshift
  change run convert (2,_) _ = some (.inr (14,_)) at hshift
  rw [run_continue _ _ _ _ _ (erase_start xs)]
  exact hshift


private theorem status_live (s : Status) (q : Nat) (t : Tape)
    (h : StatusRel s (some (.inr (q,t)))) :
    ∃ c, s = some (.inr c) ∧ c.1 = q ∧ TapeRel c.2 t := by
  cases s with
  | none => exact False.elim h
  | some v => cases v with
    | inl b => exact False.elim h
    | inr c => exact ⟨c,rfl,h.1,h.2⟩

def buffer (x : List Bool) : List Bool :=
  Shared.Codes.FiniteProgramWitnessController.loopOutput [true] [true] x.reverse []

def rawTape (xs : List Bool) : Tape :=
  tapeAt (cursor false [] xs).2 ((cursor false [] xs).1::false::false::padding xs.length [false,false])

def scanCost (x : List Bool) : Nat :=
  3*x.length+3+Shared.Codes.FiniteProgramWitnessController.loopCost [true] [true] x.reverse []

def totalCost (x : List Bool) : Nat := scanCost x+2+(2+cost (buffer x))

/-- A real linked table scans, installs the sentinel, processes all nonempty
input triples, erases the sentinel, and removes every physical tag. -/
theorem run_nonempty (x : List Bool) (hne : x ≠ []) :
    ∃ d, run stage (initial (BitstringEncoding.bitEncode x)) (totalCost x) = some (.inr d) ∧
      d.1 = (Shared.Codes.FiniteProgramTwoExit.pre source stop stop).length+14 ∧
      TapeRel d.2 (rawTape (buffer x)) := by
  let xs := buffer x
  let t := tapeAt [] (true::false::tagged xs ++ [false,false,false])
  obtain ⟨d,hr,hstate,htape⟩ := Shared.Codes.FiniteProgramSingleInput.run_nonempty [true] [true] x hne
  have ht : TapeRel d.2 t := by
    change TapeRel d.2 (Shared.Codes.FiniteProgramWitnessPhases.witnessTape [] xs []) at htape
    have he : Shared.Codes.FiniteProgramWitnessPhases.witnessTape [] xs [] = t := by
      change Shared.ComplexityBridge.PairReverseWitness.tapeLeft [true]
        (false::tagged xs ++ [false,false,false]) = t
      rfl
    rw [←he]
    exact htape
  have hdstate : d.1 = stop := hstate
  have hc : (initial (BitstringEncoding.bitEncode x)).1 < source.length := by
    simpa [initial] using Shared.Codes.FiniteProgramLink.valid_nonempty source
      (Shared.Codes.FiniteProgramSingleInput.program_valid [true] [true])
  have hprefix := Shared.Codes.FiniteProgramTwoExit.first_entry source convert stop stop
    (initial (BitstringEncoding.bitEncode x)) d (scanCost x)
    (Shared.Codes.FiniteProgramSingleInput.program_valid [true] [true]) hc stop_step stop_step hr
  change run stage (initial (BitstringEncoding.bitEncode x)) (scanCost x) = some (.inr d) at hprefix
  have hshape : t = tapeAt [] (true::false::(tagged xs ++ [false,false,false])) := by simp [t]
  have hh := Shared.Codes.FiniteProgramTwoExit.handoff_second source convert stop stop stop_bound
    true false [] (tagged xs ++ [false,false,false])
  rw [← hshape] at hh
  have hrel := run_related stage d (stop,t) hdstate ht 2
  change run stage (stop,t) 2 = _ at hh
  rw [hh] at hrel
  obtain ⟨after,hafter,hqafter,htafter⟩ := status_live _ _ _ hrel
  let pre := Shared.Codes.FiniteProgramTwoExit.pre source stop stop
  have hconvert := run_shift pre convert [] convert_valid (0,t)
    (Shared.Codes.FiniteProgramLink.valid_nonempty convert convert_valid) (2+cost xs)
  rw [convert_run] at hconvert
  change run stage (pre.length,t) (2+cost xs) = some (.inr (pre.length+14,rawTape xs)) at hconvert
  have hrel' := run_related stage after (pre.length,t) hqafter htafter (2+cost xs)
  rw [hconvert] at hrel'
  obtain ⟨last,hlast,hlastq,hlastt⟩ := status_live _ _ _ hrel'
  refine ⟨last,?_,hlastq,hlastt⟩
  change run stage (initial (BitstringEncoding.bitEncode x)) (scanCost x+2+(2+cost xs)) = _
  rw [Nat.add_assoc,run_continue _ _ _ _ _ hprefix,run_continue _ _ _ _ _ hafter]
  exact hlast

private theorem padding_all (n : Nat) : (false::false::padding n [false,false]).all (fun b => !b) = true := by
  have aux (n : Nat) (R : List Bool) (h : R.all (fun b => !b) = true) :
      (padding n R).all (fun b => !b) = true := by
    induction n generalizing R with
    | zero => exact h
    | succ n ih => simpa [padding] using ih (false::false::R) (by simpa using h)
  simpa using aux n [false,false] (by decide)

/-- Untagging places the target pair encoding on the left of the head, with
only blank padding on the opposite side: exactly a reflected initial tape. -/
theorem rawTape_reflected (xs : List Bool) :
    TapeRel (rawTape xs) (Shared.Codes.FiniteProgramMirror.tape (initial (xs.reverse ++ [false])).2) := by
  have hc := Shared.Codes.FiniteProgramUntag.cursor_contents false [] xs
  have hi : (initial (xs.reverse ++ [false])).2 =
      ([],(cursor false [] xs).1,(cursor false [] xs).2) := by
    unfold initial
    rw [←hc]
    rfl
  have hb : Turing.ListBlank.mk (false::false::padding xs.length [false,false]) =
      Turing.ListBlank.mk ([] : List Bool) := by
    have ha := padding_all xs.length
    have he : false::false::padding xs.length [false,false] =
        List.replicate (false::false::padding xs.length [false,false]).length false := by
      apply List.eq_replicate_length.mpr
      intro b hm
      have hh := List.all_eq_true.mp ha b hm
      cases b <;> simp_all
    apply Quotient.sound
    exact Or.inr ⟨_,by simpa using he⟩
  rw [hi]
  unfold TapeRel rawTape tapeAt Shared.Codes.FiniteProgramMirror.tape
  simp only [List.head?_cons,Option.getD_some,List.tail_cons]
  change (⟨_,Turing.ListBlank.mk _,Turing.ListBlank.mk _⟩ : Turing.Tape Bool) =
    ⟨_,Turing.ListBlank.mk _,Turing.ListBlank.mk []⟩
  rw [hb]

theorem pairTape_reflected (x : List Bool) :
    TapeRel (rawTape (buffer x))
      (Shared.Codes.FiniteProgramMirror.tape (initial (BitstringEncoding.bitEncode (x,([] : List Bool)))).2) := by
  have hp := Shared.Codes.FiniteProgramSingleInput.pair_output x
  have he : (buffer x).reverse ++ [false] = BitstringEncoding.bitEncode (x,([] : List Bool)) := by
    have h := congrArg List.reverse hp
    simpa [buffer,List.reverse_cons] using h
  rw [←he]
  exact rawTape_reflected (buffer x)


/-- The boundary state is the untagger's designated terminal fixture. -/
theorem untag_stop (t : Tape) :
    step Shared.Codes.FiniteProgramUntag.program (12,t) = some (.inl false) := by
  have hr : Shared.Codes.FiniteProgramUntag.program[12]? =
      some ((false,true,0,1),(true,true,0,1)) := by decide
  cases hb : t.2.1 <;> simp [step,hr,hb]

theorem convert_stop (t : Tape) : step convert (14,t) = some (.inl false) := by
  have h := Shared.Codes.FiniteProgramLink.step_shift (Shared.Codes.FiniteProgramSplice.stem erase)
    Shared.Codes.FiniteProgramUntag.program [] (12,t)
    (by simp [Shared.Codes.FiniteProgramUntag.program_length])
  rw [untag_stop] at h
  simpa [convert,Shared.Codes.FiniteProgramSplice.program,Shared.Codes.FiniteProgramSplice.stem,
    erase,shiftConfig,shiftStatus] using h

def stageStop : Nat := (Shared.Codes.FiniteProgramTwoExit.pre source stop stop).length+14

theorem stageStop_bound : stageStop < stage.length := by
  have hc : 14 < convert.length := by
    simp [convert,Shared.Codes.FiniteProgramSplice.program,link,
      Shared.Codes.FiniteProgramSplice.stem,erase,Shared.Codes.FiniteProgramUntag.program_length]
  simp only [stage,Shared.Codes.FiniteProgramTwoExit.program,link,List.length_append,
    List.length_map,List.length_nil,Nat.add_zero,stageStop]
  omega

theorem stageStop_step (t : Tape) : step stage (stageStop,t) = some (.inl false) := by
  let pre := Shared.Codes.FiniteProgramTwoExit.pre source stop stop
  have hc : 14 < convert.length := by
    simp [convert,Shared.Codes.FiniteProgramSplice.program,link,
      Shared.Codes.FiniteProgramSplice.stem,erase,Shared.Codes.FiniteProgramUntag.program_length]
  have h := Shared.Codes.FiniteProgramLink.step_shift pre convert [] (14,t) hc
  rw [convert_stop] at h
  simpa [stage,Shared.Codes.FiniteProgramTwoExit.program,stageStop,pre,shiftConfig,shiftStatus] using h

/-- The initialized configuration is blank-equivalent to the reflected
canonical pair tape, ready to enter a mirrored evaluator. -/
theorem run_nonempty_reflected (x : List Bool) (hne : x ≠ []) :
    ∃ d, run stage (initial (BitstringEncoding.bitEncode x)) (totalCost x) = some (.inr d) ∧
      d.1 = stageStop ∧ TapeRel d.2
        (Shared.Codes.FiniteProgramMirror.tape (initial (BitstringEncoding.bitEncode (x,([] : List Bool)))).2) := by
  obtain ⟨d,hr,hq,ht⟩ := run_nonempty x hne
  exact ⟨d,hr,hq,Eq.trans ht (pairTape_reflected x)⟩


/-- Continue with the reflected version of an arbitrary valid evaluator. -/
def complete (eval : Program) : Program :=
  Shared.Codes.FiniteProgramTwoExit.program stage (Shared.Codes.FiniteProgramMirror.program eval) stageStop stageStop

theorem complete_valid (eval : Program) (hv : valid eval = true) : valid (complete eval) = true := by
  apply Shared.Codes.FiniteProgramTwoExit.program_valid stage (Shared.Codes.FiniteProgramMirror.program eval)
    stageStop stageStop stage_valid
  · simpa [Shared.Codes.FiniteProgramMirror.valid_mirror] using hv
  · exact stageStop_bound
  · exact stageStop_bound

theorem result_mirror (s : Status) :
    Shared.Codes.FiniteProgramTapeEquiv.result (Shared.Codes.FiniteProgramMirror.status s) =
      Shared.Codes.FiniteProgramTapeEquiv.result s := by
  cases s with
  | none => rfl
  | some v => cases v <;> rfl

/-- Exact fuel preservation after the charged nonempty-input initialization.
This includes `none` for timeouts or invalid execution, rather than replacing
it by a false Boolean result. -/
theorem bounded_nonempty (eval : Program) (hv : valid eval = true) (x : List Bool)
    (hne : x ≠ []) (fuel : Nat) :
    bounded (complete eval) (BitstringEncoding.bitEncode x) (totalCost x+2+fuel) =
      bounded eval (BitstringEncoding.bitEncode (x,([] : List Bool))) fuel := by
  let mirror := Shared.Codes.FiniteProgramMirror.program eval
  let target := BitstringEncoding.bitEncode (x,([] : List Bool))
  let xs := buffer x
  let L := (cursor false [] xs).2
  let head := (cursor false [] xs).1
  let R := false::padding xs.length [false,false]
  let t := tapeAt L (head::false::R)
  have htshape : t = rawTape xs := by rfl
  have hmirror : valid mirror = true := by simpa [mirror,Shared.Codes.FiniteProgramMirror.valid_mirror] using hv
  obtain ⟨d,hr,hq,htape⟩ := run_nonempty x hne
  have ht : TapeRel d.2 t := by simpa [t,htshape,xs] using htape
  have hin : (initial (BitstringEncoding.bitEncode x)).1 < stage.length := by
    simpa [initial] using Shared.Codes.FiniteProgramLink.valid_nonempty stage stage_valid
  have hp := Shared.Codes.FiniteProgramTwoExit.first_entry stage mirror stageStop stageStop
    (initial (BitstringEncoding.bitEncode x)) d (totalCost x) stage_valid hin stageStop_step stageStop_step hr
  change run (complete eval) (initial (BitstringEncoding.bitEncode x)) (totalCost x) = some (.inr d) at hp
  have hh := Shared.Codes.FiniteProgramTwoExit.handoff_second stage mirror stageStop stageStop stageStop_bound
    head false L R
  change run (complete eval) (stageStop,t) 2 = _ at hh
  have hrel := run_related (complete eval) d (stageStop,t) hq ht 2
  rw [hh] at hrel
  obtain ⟨after,hafter,hqafter,htafter⟩ := status_live _ _ _ hrel
  let pre := Shared.Codes.FiniteProgramTwoExit.pre stage stageStop stageStop
  have heq : after = shiftConfig pre.length (0,after.2) := by
    apply Prod.ext
    · simpa [shiftConfig,pre] using hqafter
    · rfl
  have hshift := run_shift pre mirror [] hmirror (0,after.2)
    (Shared.Codes.FiniteProgramLink.valid_nonempty mirror hmirror) fuel
  change run (complete eval) (shiftConfig pre.length (0,after.2)) fuel = _ at hshift
  have hm : TapeRel after.2 (Shared.Codes.FiniteProgramMirror.config (initial target)).2 := by
    apply Eq.trans htafter
    change TapeRel t (Shared.Codes.FiniteProgramMirror.tape (initial target).2)
    rw [htshape]
    exact pairTape_reflected x
  have hres := Shared.Codes.FiniteProgramTapeEquiv.run_result_congr mirror (0,after.2)
    (Shared.Codes.FiniteProgramMirror.config (initial target)) (by rfl) hm fuel
  unfold bounded
  change Shared.Codes.FiniteProgramTapeEquiv.result
    (run (complete eval) (initial (BitstringEncoding.bitEncode x)) (totalCost x+2+fuel)) =
    Shared.Codes.FiniteProgramTapeEquiv.result (run eval (initial target) fuel)
  rw [Nat.add_assoc,run_continue _ _ _ _ _ hp,run_continue _ _ _ _ _ hafter,heq,hshift]
  rw [Shared.Codes.FiniteProgramLink.result_shift,hres]
  change Shared.Codes.FiniteProgramTapeEquiv.result
    (run (Shared.Codes.FiniteProgramMirror.program eval)
      (Shared.Codes.FiniteProgramMirror.config (initial target)) fuel) = _
  rw [Shared.Codes.FiniteProgramMirror.run_mirror,result_mirror]


theorem buffer_length (x : List Bool) : (buffer x).length = 6*x.length := by
  have h := congrArg List.length (Shared.Codes.FiniteProgramSingleInput.pair_output x)
  simp only [List.length_cons,List.length_reverse,Shared.ComplexityBridge.bitstring_pair_encoded_length,
    List.length_nil,Nat.mul_zero,Nat.add_zero] at h
  change (buffer x).length+1 = 6*x.length+1 at h
  omega

noncomputable def costPolynomial : Polynomial Nat :=
  Shared.Codes.FiniteProgramSingleInput.costPolynomial [true] [true] +
    (Polynomial.C 6 * Polynomial.X) * (Polynomial.C 20 * (Polynomial.C 6 * Polynomial.X) + Polynomial.C 21) +
    Polynomial.C 8

theorem totalCost_bound (x : List Bool) : totalCost x ≤ costPolynomial.eval x.length := by
  have hs := Shared.Codes.FiniteProgramSingleInput.cost_bound [true] [true] x
  have hu := Shared.Codes.FiniteProgramUntag.cost_bound (buffer x)
  rw [buffer_length] at hu
  have hp := Shared.Codes.FiniteProgramSingleInput.costPolynomial_eval [true] [true] x.length
  unfold totalCost scanCost
  simp only [costPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  omega

/-- One fixed exponent covers the entire scan, linked handoff, and untagger
on the actual encoded source input. -/
theorem totalCost_fixed_exponent : ∃ k : Nat, ∀ x : List Bool,
    totalCost x+2 ≤ ((BitstringEncoding.bitEncode x).length+2)^k := by
  obtain ⟨k,hk⟩ := Shared.ComplexityBridge.ClockBounds.polynomial_fixed_exponent (costPolynomial+Polynomial.C 2)
  refine ⟨k,fun x => ?_⟩
  have hinput : x.length ≤ (BitstringEncoding.bitEncode x).length := by
    rw [Shared.ComplexityBridge.bitstring_list_encoded_length]; omega
  calc
    _ ≤ (costPolynomial+Polynomial.C 2).eval x.length := by
      simp only [Polynomial.eval_add,Polynomial.eval_C]; have h := totalCost_bound x; omega
    _ ≤ (x.length+2)^k := hk x.length
    _ ≤ ((BitstringEncoding.bitEncode x).length+2)^k := Nat.pow_le_pow_left (by omega) k


/-- Dispatch on the canonical list-encoding's first bit: the empty input is
all blank, while each nonempty encoded input begins with true. -/
def dispatchStub : Program :=
  [((false,true,2,0),(true,true,1,0)),
   ((false,false,3,0),(true,false,3,0)),
   ((false,true,0,1),(true,true,0,1)),
   ((false,true,0,1),(true,true,0,1))]

def dispatch : Program := Shared.Codes.FiniteProgramSplice.program dispatchStub stage

theorem dispatchStub_valid : valid dispatchStub = true := by decide

theorem dispatch_valid : valid dispatch = true :=
  Shared.Codes.FiniteProgramSplice.program_valid dispatchStub stage dispatchStub_valid stage_valid

theorem dispatchStem_length : (Shared.Codes.FiniteProgramSplice.stem dispatchStub).length = 3 := by
  simp [Shared.Codes.FiniteProgramSplice.stem,dispatchStub]

def emptyExit : Nat := 2
def nonemptyExit : Nat := 3+stageStop

theorem emptyExit_bound : emptyExit < dispatch.length := by
  have hs := Shared.Codes.FiniteProgramLink.valid_nonempty stage stage_valid
  simp [emptyExit,dispatch,Shared.Codes.FiniteProgramSplice.program,link,dispatchStem_length]
  omega

theorem nonemptyExit_bound : nonemptyExit < dispatch.length := by
  have hs := stageStop_bound
  simp only [nonemptyExit,dispatch,Shared.Codes.FiniteProgramSplice.program,link,
    dispatchStem_length,List.length_append,List.length_map,List.length_nil,Nat.add_zero]
  omega

theorem exits_ne : emptyExit ≠ nonemptyExit := by simp [emptyExit,nonemptyExit]; omega

theorem emptyExit_step (t : Tape) : step dispatch (emptyExit,t) = some (.inl false) := by
  have hr : dispatch[2]? = some ((false,true,0,1),(true,true,0,1)) := by
    simp [dispatch,Shared.Codes.FiniteProgramSplice.program,link,Shared.Codes.FiniteProgramSplice.stem,dispatchStub]
  cases hb : t.2.1 <;> simp [emptyExit,step,hr,hb]

theorem nonemptyExit_step (t : Tape) : step dispatch (nonemptyExit,t) = some (.inl false) := by
  have h := Shared.Codes.FiniteProgramLink.step_shift (Shared.Codes.FiniteProgramSplice.stem dispatchStub)
    stage [] (stageStop,t) stageStop_bound
  rw [stageStop_step] at h
  simpa [dispatch,Shared.Codes.FiniteProgramSplice.program,dispatchStem_length,
    nonemptyExit,shiftConfig,shiftStatus] using h

theorem dispatch_empty : run dispatch (initial (BitstringEncoding.bitEncode ([] : List Bool))) 1 =
    some (.inr (emptyExit,([false],false,[]))) := by
  change run dispatch (initial []) 1 = _
  simp [run,advance,step,dispatch,Shared.Codes.FiniteProgramSplice.program,
    Shared.Codes.FiniteProgramSplice.stem,link,dispatchStub,emptyExit,initial,moveTape]

theorem dispatch_nonempty_start (b : Bool) (xs : List Bool) :
    let input := BitstringEncoding.bitEncode (b::xs)
    run dispatch (initial input) 2 = some (.inr (3,(initial input).2)) := by
  change run dispatch (initial (true::b::false::BitstringEncoding.bitEncode xs)) 2 =
    some (.inr (3,(initial (true::b::false::BitstringEncoding.bitEncode xs)).2))
  cases b <;> simp [run,advance,step,dispatch,Shared.Codes.FiniteProgramSplice.program,
    Shared.Codes.FiniteProgramSplice.stem,link,dispatchStub,initial,moveTape]

def setupCost (x : List Bool) : Nat := if x.isEmpty then 1 else 2+totalCost x

theorem dispatch_nonempty (x : List Bool) (hne : x ≠ []) :
    ∃ d, run dispatch (initial (BitstringEncoding.bitEncode x)) (setupCost x) = some (.inr d) ∧
      d.1 = nonemptyExit ∧ TapeRel d.2
        (Shared.Codes.FiniteProgramMirror.tape (initial (BitstringEncoding.bitEncode (x,([] : List Bool)))).2) := by
  cases x with
  | nil => contradiction
  | cons b xs =>
    have hne' : b::xs ≠ [] := by simp
    obtain ⟨d,hr,hq,ht⟩ := run_nonempty_reflected (b::xs) hne'
    have hshift := run_shift (Shared.Codes.FiniteProgramSplice.stem dispatchStub) stage [] stage_valid
      (initial (BitstringEncoding.bitEncode (b::xs))) (by simpa [initial] using
        (Shared.Codes.FiniteProgramLink.valid_nonempty stage stage_valid)) (totalCost (b::xs))
    rw [hr] at hshift
    have hstart := dispatch_nonempty_start b xs
    change run dispatch (initial (BitstringEncoding.bitEncode (b::xs))) 2 = _ at hstart
    change run dispatch (3,(initial (BitstringEncoding.bitEncode (b::xs))).2) _ =
      some (.inr (shiftConfig 3 d)) at hshift
    refine ⟨shiftConfig 3 d,?_,?_,ht⟩
    · change run dispatch (initial (BitstringEncoding.bitEncode (b::xs))) (2+totalCost (b::xs)) = _
      rw [run_continue _ _ _ _ _ hstart]
      exact hshift
    · change 3+d.1 = 3+stageStop
      rw [hq]

theorem blankTape_reflected : TapeRel ([false],false,[])
    (Shared.Codes.FiniteProgramMirror.tape
      (initial (BitstringEncoding.bitEncode (([] : List Bool),([] : List Bool)))).2) := by
  change (⟨false,Turing.ListBlank.mk [false],Turing.ListBlank.mk []⟩ : Turing.Tape Bool) =
    ⟨false,Turing.ListBlank.mk [],Turing.ListBlank.mk []⟩
  have h : Turing.ListBlank.mk [false] = Turing.ListBlank.mk ([] : List Bool) := by
    apply Quotient.sound
    exact Or.inr ⟨1,by decide⟩
  rw [h]

theorem dispatch_all (x : List Bool) :
    ∃ d, run dispatch (initial (BitstringEncoding.bitEncode x)) (setupCost x) = some (.inr d) ∧
      (d.1 = emptyExit ∨ d.1 = nonemptyExit) ∧ TapeRel d.2
        (Shared.Codes.FiniteProgramMirror.tape (initial (BitstringEncoding.bitEncode (x,([] : List Bool)))).2) := by
  cases x with
  | nil =>
    refine ⟨(emptyExit,([false],false,[])),?_,Or.inl rfl,?_⟩
    · exact dispatch_empty
    · exact blankTape_reflected
  | cons b xs =>
    obtain ⟨d,hr,hq,ht⟩ := dispatch_nonempty (b::xs) (by simp)
    exact ⟨d,hr,Or.inr hq,ht⟩


/-- A two-exit wrapper dispatches every canonical source input to the same
mirrored evaluator, including the all-blank empty input. -/
def completeAll (eval : Program) : Program :=
  Shared.Codes.FiniteProgramTwoExit.program dispatch (Shared.Codes.FiniteProgramMirror.program eval)
    emptyExit nonemptyExit

theorem completeAll_valid (eval : Program) (hv : valid eval = true) : valid (completeAll eval) = true := by
  apply Shared.Codes.FiniteProgramTwoExit.program_valid dispatch (Shared.Codes.FiniteProgramMirror.program eval)
    emptyExit nonemptyExit dispatch_valid
  · simpa [Shared.Codes.FiniteProgramMirror.valid_mirror] using hv
  · exact emptyExit_bound
  · exact nonemptyExit_bound

theorem reflected_shape (input : List Bool) :
    TapeRel (tapeAt input.tail [input.head?.getD false,false])
      (Shared.Codes.FiniteProgramMirror.tape (initial input).2) := by
  change (⟨input.head?.getD false,Turing.ListBlank.mk input.tail,Turing.ListBlank.mk [false]⟩ : Turing.Tape Bool) =
    ⟨input.head?.getD false,Turing.ListBlank.mk input.tail,Turing.ListBlank.mk []⟩
  have h : Turing.ListBlank.mk [false] = Turing.ListBlank.mk ([] : List Bool) := by
    apply Quotient.sound
    exact Or.inr ⟨1,by decide⟩
  rw [h]

/-- All bitstrings, including the empty list, are converted and handed to
the mirrored evaluator. Exact bounded results include timeouts. -/
theorem bounded_all (eval : Program) (hv : valid eval = true) (x : List Bool) (fuel : Nat) :
    bounded (completeAll eval) (BitstringEncoding.bitEncode x) (setupCost x+2+fuel) =
      bounded eval (BitstringEncoding.bitEncode (x,([] : List Bool))) fuel := by
  let mirror := Shared.Codes.FiniteProgramMirror.program eval
  let target := BitstringEncoding.bitEncode (x,([] : List Bool))
  let L := target.tail
  let head := target.head?.getD false
  let t := tapeAt L [head,false]
  have hmirror : valid mirror = true := by simpa [mirror,Shared.Codes.FiniteProgramMirror.valid_mirror] using hv
  obtain ⟨d,hr,hq,htape⟩ := dispatch_all x
  have ht : TapeRel d.2 t := Eq.trans htape (Eq.symm (reflected_shape target))
  have hin : (initial (BitstringEncoding.bitEncode x)).1 < dispatch.length := by
    simpa [initial] using Shared.Codes.FiniteProgramLink.valid_nonempty dispatch dispatch_valid
  have hp := Shared.Codes.FiniteProgramTwoExit.first_entry dispatch mirror emptyExit nonemptyExit
    (initial (BitstringEncoding.bitEncode x)) d (setupCost x) dispatch_valid hin
    emptyExit_step nonemptyExit_step hr
  change run (completeAll eval) (initial (BitstringEncoding.bitEncode x)) (setupCost x) = some (.inr d) at hp
  let pre := Shared.Codes.FiniteProgramTwoExit.pre dispatch emptyExit nonemptyExit
  have hh : ∃ after, run (completeAll eval) d 2 = some (.inr after) ∧
      after.1 = pre.length ∧ TapeRel after.2 t := by
    rcases hq with he | hn
    · have h := Shared.Codes.FiniteProgramTwoExit.handoff_first dispatch mirror emptyExit nonemptyExit
        emptyExit_bound exits_ne head false L []
      change run (completeAll eval) (emptyExit,t) 2 = _ at h
      have hr' := run_related (completeAll eval) d (emptyExit,t) he ht 2
      rw [h] at hr'
      exact status_live _ _ _ hr'
    · have h := Shared.Codes.FiniteProgramTwoExit.handoff_second dispatch mirror emptyExit nonemptyExit
        nonemptyExit_bound head false L []
      change run (completeAll eval) (nonemptyExit,t) 2 = _ at h
      have hr' := run_related (completeAll eval) d (nonemptyExit,t) hn ht 2
      rw [h] at hr'
      exact status_live _ _ _ hr'
  obtain ⟨after,hafter,hqafter,htafter⟩ := hh
  have heq : after = shiftConfig pre.length (0,after.2) := by
    apply Prod.ext
    · simpa [shiftConfig] using hqafter
    · rfl
  have hshift := run_shift pre mirror [] hmirror (0,after.2)
    (Shared.Codes.FiniteProgramLink.valid_nonempty mirror hmirror) fuel
  change run (completeAll eval) (shiftConfig pre.length (0,after.2)) fuel = _ at hshift
  have hm : TapeRel after.2 (Shared.Codes.FiniteProgramMirror.config (initial target)).2 := by
    apply Eq.trans htafter
    exact reflected_shape target
  have hres := Shared.Codes.FiniteProgramTapeEquiv.run_result_congr mirror (0,after.2)
    (Shared.Codes.FiniteProgramMirror.config (initial target)) (by rfl) hm fuel
  unfold bounded
  change Shared.Codes.FiniteProgramTapeEquiv.result
    (run (completeAll eval) (initial (BitstringEncoding.bitEncode x)) (setupCost x+2+fuel)) =
    Shared.Codes.FiniteProgramTapeEquiv.result (run eval (initial target) fuel)
  rw [Nat.add_assoc,run_continue _ _ _ _ _ hp,run_continue _ _ _ _ _ hafter,heq,hshift]
  rw [Shared.Codes.FiniteProgramLink.result_shift,hres]
  change Shared.Codes.FiniteProgramTapeEquiv.result
    (run (Shared.Codes.FiniteProgramMirror.program eval)
      (Shared.Codes.FiniteProgramMirror.config (initial target)) fuel) = _
  rw [Shared.Codes.FiniteProgramMirror.run_mirror,result_mirror]


/-- A single polynomial pays for both dispatch cases and the final handoff. -/
theorem setupCost_bound (x : List Bool) : setupCost x+2 ≤ costPolynomial.eval x.length+4 := by
  have h := totalCost_bound x
  cases x with
  | nil => change 1+2 ≤ costPolynomial.eval ([] : List Bool).length+4; omega
  | cons b xs =>
    change (2+totalCost (b::xs))+2 ≤ costPolynomial.eval (b::xs).length+4
    omega

noncomputable def combinedClock (q : Polynomial Nat) : Polynomial Nat :=
  costPolynomial + Polynomial.C 4 + q.comp (Polynomial.C 2*Polynomial.X+Polynomial.C 1)

theorem combinedClock_bound (q : Polynomial Nat) (x : List Bool) :
    setupCost x+2+q.eval (BitstringEncoding.bitEncode (x,([] : List Bool))).length ≤
      (combinedClock q).eval (BitstringEncoding.bitEncode x).length := by
  have hx : x.length ≤ (BitstringEncoding.bitEncode x).length := by
    rw [Shared.ComplexityBridge.bitstring_list_encoded_length]; omega
  have hs := setupCost_bound x
  have hm := Shared.ComplexityBridge.TM2Compose.polynomial_eval_mono costPolynomial hx
  have hp : (BitstringEncoding.bitEncode (x,([] : List Bool))).length =
      2*(BitstringEncoding.bitEncode x).length+1 := by
    rw [Shared.ComplexityBridge.bitstring_pair_encoded_length,
      Shared.ComplexityBridge.bitstring_list_encoded_length]
    simp; omega
  simp only [combinedClock,Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X]
  rw [hp]
  omega

/-- The pair evaluator becomes a single-input evaluator with a charged
polynomial wrapper. The fixed evaluator need only be total on the selected
pairs; its arbitrary unbounded execution need not terminate. -/
theorem compile_decision (L : List Bool → Bool) (hL : ComplexityTheory.IsPolyTime L) :
    ∃ (p : Program) (clock : Polynomial Nat), valid p = true ∧ ∀ x,
      bounded p (BitstringEncoding.bitEncode x)
        (clock.eval (BitstringEncoding.bitEncode x).length) = some (L x) := by
  let R : List Bool × List Bool → Bool := fun v => L v.1
  have hR : ComplexityTheory.IsPolyTime R := by
    have h := Shared.ComplexityBridge.TM2Compose.isPolyTime_comp
      (Shared.ComplexityBridge.TM2PairFirst.first (α := List Bool) (β := List Bool)) L
      Shared.ComplexityBridge.TM2PairFirst.first_isPolyTime hL
    simpa [R,Shared.ComplexityBridge.TM2PairFirst.first] using h
  obtain ⟨eval,q,hvalid,heval⟩ :=
    (Shared.ComplexityBridge.FiniteProgramTM2.canonical_pair_iff_finite R).mp hR
  refine ⟨completeAll eval,combinedClock q,completeAll_valid eval hvalid,?_⟩
  intro x
  let fuel := q.eval (BitstringEncoding.bitEncode (x,([] : List Bool))).length
  have hrun := bounded_all eval hvalid x fuel
  have he : bounded eval (BitstringEncoding.bitEncode (x,([] : List Bool))) fuel = some (L x) := by
    simpa [fuel,R] using heval x []
  rw [he] at hrun
  obtain ⟨t,ht,hr⟩ := (bounded_iff_result (completeAll eval) (BitstringEncoding.bitEncode x)
    (setupCost x+2+fuel) (L x)).1 hrun
  apply (bounded_iff_result (completeAll eval) (BitstringEncoding.bitEncode x)
    ((combinedClock q).eval (BitstringEncoding.bitEncode x).length) (L x)).2
  exact ⟨t,le_trans ht (combinedClock_bound q x),hr⟩

/-- Complete canonical P-to-finite-table and finite-table-to-P equivalence
for every raw Boolean-list language, with the public Google encoding. -/
theorem canonical_decision_iff_finite (L : List Bool → Bool) :
    ComplexityTheory.IsPolyTime L ↔
      ∃ (p : Program) (clock : Polynomial Nat), valid p = true ∧ ∀ x,
        bounded p (BitstringEncoding.bitEncode x)
          (clock.eval (BitstringEncoding.bitEncode x).length) = some (L x) := by
  constructor
  · exact compile_decision L
  · rintro ⟨p,clock,hp,h⟩
    exact Shared.ComplexityBridge.FiniteProgramTM2.finite_isPolyTime p clock L hp h


/-- The single-input polynomial clock can be normalized to one fixed
exponent, fixed once per candidate and measured on the encoded input. -/
theorem finite_candidate_iff (L : List Bool → Bool) :
    (∃ c : Candidate, valid c.2 = true ∧ ∀ x,
      evaluate c (BitstringEncoding.bitEncode x) = some (L x)) ↔ ComplexityTheory.IsPolyTime L := by
  constructor
  · rintro ⟨⟨k,p⟩,hv,h⟩
    let q : Polynomial Nat := (Polynomial.X+Polynomial.C 2)^k
    apply Shared.ComplexityBridge.FiniteProgramTM2.finite_isPolyTime p q L hv
    intro x
    have hx := h x
    change bounded p (BitstringEncoding.bitEncode x) (((BitstringEncoding.bitEncode x).length+2)^k) = _ at hx
    simpa [q,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C] using hx
  · intro hL
    obtain ⟨p,q,hv,h⟩ := compile_decision L hL
    obtain ⟨k,hk⟩ := Shared.ComplexityBridge.ClockBounds.polynomial_fixed_exponent q
    refine ⟨(k,p),hv,?_⟩
    intro x
    change bounded p (BitstringEncoding.bitEncode x) (((BitstringEncoding.bitEncode x).length+2)^k) = _
    obtain ⟨t,ht,hr⟩ := (bounded_iff_result p (BitstringEncoding.bitEncode x)
      (q.eval (BitstringEncoding.bitEncode x).length) (L x)).1 (h x)
    exact (bounded_iff_result p (BitstringEncoding.bitEncode x) _ _).2
      ⟨t,le_trans ht (hk _),hr⟩


namespace Fixtures
def constantTrue : Program := [((false,false,0,2),(true,false,0,2))]
example : valid constantTrue = true := by decide
example : bounded (completeAll constantTrue) (BitstringEncoding.bitEncode ([] : List Bool))
    (setupCost []+2+0) = none := by rw [bounded_all constantTrue (by decide) [] 0]; decide
example : bounded (completeAll constantTrue) (BitstringEncoding.bitEncode ([] : List Bool))
    (setupCost []+2+1) = some true := by rw [bounded_all constantTrue (by decide) [] 1]; decide
example : bounded (completeAll constantTrue) (BitstringEncoding.bitEncode [true,false])
    (setupCost [true,false]+2+1) = some true := by rw [bounded_all constantTrue (by decide) [true,false] 1]; decide
end Fixtures

end Shared.Codes.FiniteProgramSingleUntag
