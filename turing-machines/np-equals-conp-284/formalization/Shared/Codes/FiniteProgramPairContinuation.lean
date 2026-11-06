import Shared.Codes.FiniteProgramPairUnified
import Shared.Codes.FiniteProgramTwoExit
import Shared.ComplexityBridge.TM2BinaryFiniteProgram
set_option maxHeartbeats 3000000
set_option linter.constructorNameAsVariable false
set_option linter.style.haveILetI false

/-! The two terminal rows of the unified pair initializer can both be linked
to the same finite evaluator. -/
namespace Shared.Codes.FiniteProgramPairContinuation
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (link shiftPair shiftConfig shiftStatus step_shift)
open Shared.Codes.FiniteProgramPairUnified (nonemptyHead emptyHead nonemptyExit emptyExit)

abbrev source := Shared.Codes.FiniteProgramPairUnified.program

theorem positioned_stop (t : Tape) :
    step Shared.Codes.FiniteProgramMirror.positioned (14,t) = some (.inl false) := by
  have h : Shared.Codes.FiniteProgramMirror.positioned[14]? =
      some ((false,false,2,1),(true,false,2,1)) := by decide
  cases hbit : t.2.1 <;> simp [step,h,hbit]

theorem nonempty_head_stop (mz mo z o : List Bool) (width : Nat) (t : Tape) :
    step (nonemptyHead mz mo z o width)
      ((Shared.Codes.FiniteProgramPairHeadAll.handoffPre mz mo z o width).length+14,t) =
        some (.inl false) := by
  have h := step_shift (Shared.Codes.FiniteProgramPairHeadAll.handoffPre mz mo z o width)
    Shared.Codes.FiniteProgramMirror.positioned [] (14,t)
    (by simp [Shared.Codes.FiniteProgramMirror.positioned_length])
  rw [positioned_stop] at h
  simpa [nonemptyHead,Shared.Codes.FiniteProgramPairHeadAll.program,shiftConfig,shiftStatus] using h

theorem empty_head_stop (mz mo z o : List Bool) (width : Nat) (t : Tape) :
    step (emptyHead mz mo z o width)
      ((Shared.Codes.FiniteProgramEmptyWitnessHead.handoffPre mz mo z o width).length+14,t) =
        some (.inl false) := by
  have h := step_shift (Shared.Codes.FiniteProgramEmptyWitnessHead.handoffPre mz mo z o width)
    Shared.Codes.FiniteProgramMirror.positioned [] (14,t)
    (by simp [Shared.Codes.FiniteProgramMirror.positioned_length])
  rw [positioned_stop] at h
  simpa [emptyHead,Shared.Codes.FiniteProgramEmptyWitnessHead.program,shiftConfig,shiftStatus] using h

theorem nonempty_head_exit_bound (mz mo z o : List Bool) (width : Nat) :
    (Shared.Codes.FiniteProgramPairHeadAll.handoffPre mz mo z o width).length+14 <
      (nonemptyHead mz mo z o width).length := by
  simp [nonemptyHead,Shared.Codes.FiniteProgramPairHeadAll.program,link,
    Shared.Codes.FiniteProgramMirror.positioned_length]

theorem empty_head_exit_bound (mz mo z o : List Bool) (width : Nat) :
    (Shared.Codes.FiniteProgramEmptyWitnessHead.handoffPre mz mo z o width).length+14 <
      (emptyHead mz mo z o width).length := by
  simp [emptyHead,Shared.Codes.FiniteProgramEmptyWitnessHead.program,link,
    Shared.Codes.FiniteProgramMirror.positioned_length]

theorem nonempty_stop (mz mo z o : List Bool) (width : Nat) (t : Tape) :
    step (source mz mo z o width) (nonemptyExit mz mo z o width,t) = some (.inl false) := by
  let n := nonemptyHead mz mo z o width
  let e := emptyHead mz mo z o width
  let q := (Shared.Codes.FiniteProgramPairHeadAll.handoffPre mz mo z o width).length+14
  have h := step_shift (Shared.Codes.FiniteProgramPairDispatch.pre n) n
    (e.map (shiftPair (8+n.length))) (q,t) (nonempty_head_exit_bound mz mo z o width)
  rw [nonempty_head_stop] at h
  simpa [source,Shared.Codes.FiniteProgramPairDispatch.tm2Program,
    Shared.Codes.FiniteProgramPairDispatch.program,Shared.Codes.FiniteProgramPairDispatch.pre_length,
    nonemptyExit,shiftConfig,shiftStatus,n,e,q,Nat.add_assoc] using h

theorem empty_stop (mz mo z o : List Bool) (width : Nat) (t : Tape) :
    step (source mz mo z o width) (emptyExit mz mo z o width,t) = some (.inl false) := by
  let n := nonemptyHead mz mo z o width
  let e := emptyHead mz mo z o width
  let pre := Shared.Codes.FiniteProgramPairDispatch.pre n ++ n.map (shiftPair 8)
  let q := (Shared.Codes.FiniteProgramEmptyWitnessHead.handoffPre mz mo z o width).length+14
  have heq : source mz mo z o width = link pre e [] := by
    simp [source,Shared.Codes.FiniteProgramPairDispatch.tm2Program,
      Shared.Codes.FiniteProgramPairDispatch.program,link,pre,
      Shared.Codes.FiniteProgramPairDispatch.pre_length,n,e,List.append_assoc]
  have h := step_shift pre e [] (q,t) (empty_head_exit_bound mz mo z o width)
  rw [empty_head_stop] at h
  rw [heq]
  simpa [pre,Shared.Codes.FiniteProgramPairDispatch.pre_length,emptyExit,
    shiftConfig,shiftStatus,n,e,q,Nat.add_assoc] using h

theorem nonempty_exit_bound (mz mo z o : List Bool) (width : Nat) :
    nonemptyExit mz mo z o width < (source mz mo z o width).length := by
  have h := nonempty_head_exit_bound mz mo z o width
  simp only [source,Shared.Codes.FiniteProgramPairDispatch.tm2Program,
    Shared.Codes.FiniteProgramPairDispatch.program_length,nonemptyExit]
  dsimp only [nonemptyHead,emptyHead] at h ⊢
  omega

theorem empty_exit_bound (mz mo z o : List Bool) (width : Nat) :
    emptyExit mz mo z o width < (source mz mo z o width).length := by
  have h := empty_head_exit_bound mz mo z o width
  simp only [source,Shared.Codes.FiniteProgramPairDispatch.tm2Program,
    Shared.Codes.FiniteProgramPairDispatch.program_length,emptyExit]
  dsimp only [nonemptyHead,emptyHead] at h ⊢
  omega

theorem exits_distinct (mz mo z o : List Bool) (width : Nat) :
    nonemptyExit mz mo z o width ≠ emptyExit mz mo z o width := by
  have h := nonempty_head_exit_bound mz mo z o width
  unfold nonemptyExit emptyExit
  omega

def program (mz mo z o : List Bool) (width : Nat) (eval : Program) : Program :=
  Shared.Codes.FiniteProgramTwoExit.program (source mz mo z o width) eval
    (nonemptyExit mz mo z o width) (emptyExit mz mo z o width)

theorem program_valid (mz mo z o : List Bool) (width : Nat) (eval : Program) (hv : valid eval = true) :
    valid (program mz mo z o width eval) = true := by
  apply Shared.Codes.FiniteProgramTwoExit.program_valid _ _ _ _
    (Shared.Codes.FiniteProgramPairDispatch.tm2Program_valid mz mo z o width) hv
    (nonempty_exit_bound mz mo z o width) (empty_exit_bound mz mo z o width)


/-- The literal paired-input initializer followed by a valid evaluator has
    exactly the evaluator's bounded result on the canonical translated input.
    The time charged is initialization plus the two-step handoff plus fuel. -/
theorem bounded_tm2 (tm : Turing.FinTM2) {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm → List.Vector Bool width)
    (inp : tm.Γ tm.k₀ ≃ Bool) (eval : Program) (hvalid : valid eval = true)
    (x w : List Bool) (fuel : Nat) :
    let mz := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true false
    let mo := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true true
    let z := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false false
    let o := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false true
    let input := BitstringEncoding.bitEncode (x,w)
    let words := Shared.ComplexityBridge.TM2BinaryPostCosts.inputBits tm enc (input.map inp.symm)
    let setup := Shared.Codes.FiniteProgramPairUnified.runtime mz mo z o x w width
    bounded (program mz mo z o width eval) input (setup+2+fuel) = bounded eval words fuel := by
  dsimp only
  let mz := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true false
  let mo := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true true
  let z := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false false
  let o := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false true
  obtain ⟨d,hr,hstate,htape⟩ := Shared.Codes.FiniteProgramPairUnified.run_tm2_all_at_exit tm enc inp x w
  exact Shared.Codes.FiniteProgramTwoExit.bounded_after_exit
    (source mz mo z o width) eval (nonemptyExit mz mo z o width) (emptyExit mz mo z o width)
    (BitstringEncoding.bitEncode (x,w))
    (Shared.ComplexityBridge.TM2BinaryPostCosts.inputBits tm enc
      ((BitstringEncoding.bitEncode (x,w)).map inp.symm))
    (Shared.Codes.FiniteProgramPairUnified.runtime mz mo z o x w width) fuel d
    (Shared.Codes.FiniteProgramPairDispatch.tm2Program_valid mz mo z o width) hvalid
    (nonempty_exit_bound mz mo z o width) (empty_exit_bound mz mo z o width)
    (exits_distinct mz mo z o width) (nonempty_stop mz mo z o width)
    (empty_stop mz mo z o width) hr hstate htape

/-- The number of rows is explicit; the evaluator remains an arbitrary valid
    finite table and is not assumed to terminate without a fuel bound. -/
theorem program_length (mz mo z o : List Bool) (width : Nat) (eval : Program) :
    (program mz mo z o width eval).length =
      1156+6*mz.length+6*mo.length+54*z.length+54*o.length+16*width+eval.length := by
  simp [program,Shared.Codes.FiniteProgramTwoExit.program_length,source,
    Shared.Codes.FiniteProgramPairDispatch.tm2Program_length]
  omega


/-- Under the audited finite-alphabet and codec hypotheses, attach the actual
    finite TM2 simulator to the paired-input initializer. This exports the
    simulator's encoded final head bit; decoding a Boolean output remains a
    separate obligation. -/
theorem finite_tm2_evaluator (tm : Turing.FinTM2) (alphabet : ∀ k, Fintype (tm.Γ k))
    {width : Nat} (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm → List.Vector Bool width)
    (dec : List.Vector Bool width → Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm)
    (enc0 : enc default = List.Vector.replicate width false)
    (encdec : ∀ a, dec (enc a) = a) (inp : tm.Γ tm.k₀ ≃ Bool) (p : Polynomial Nat) :
    letI := tm.kFin
    letI := alphabet
    letI : Inhabited tm.Λ := ⟨tm.main⟩
    ∃ eval : Program, valid eval = true ∧
      ∀ (x w : List Bool) (n : Nat) (last : tm.Cfg),
        let bits := (BitstringEncoding.bitEncode (x,w)).map inp.symm
        let mz := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true false
        let mo := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true true
        let z := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false false
        let o := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false true
        Shared.ComplexityBridge.TM2Symbols.runSteps tm.step n (Turing.initList tm bits) = some last →
        n ≤ p.eval bits.length → last.l = none →
        ∃ mid, Turing.TM2to1.TrCfg last mid ∧
          bounded (program mz mo z o width eval) (BitstringEncoding.bitEncode (x,w))
            (Shared.Codes.FiniteProgramPairUnified.runtime mz mo z o x w width + 2 +
              ((2*Shared.ComplexityBridge.TM2BinaryPostCosts.timePolynomial tm alphabet enc dec p+1).eval bits.length)) =
                some ((Turing.TM1to1.trTape enc0 mid.Tape).head) := by
  letI := tm.kFin
  letI := alphabet
  letI : Inhabited tm.Λ := ⟨tm.main⟩
  obtain ⟨eval,hvalid,hcomp⟩ := Shared.ComplexityBridge.TM2BinaryFiniteProgram.finite_program
    tm alphabet enc dec enc0 encdec p
  refine ⟨eval,hvalid,?_⟩
  intro x w n last
  dsimp only
  intro hrun htime hhalt
  obtain ⟨mid,hrel,hresult⟩ := hcomp ((BitstringEncoding.bitEncode (x,w)).map inp.symm)
    n last hrun htime hhalt
  refine ⟨mid,hrel,?_⟩
  rw [bounded_tm2 tm enc inp eval hvalid x w]
  exact hresult

namespace Fixtures
example : valid (program [true] [false] [false] [true] 1
    Shared.Codes.FiniteProgramMirror.positioned) = true :=
  program_valid [true] [false] [false] [true] 1 _ Shared.Codes.FiniteProgramMirror.positioned_valid
end Fixtures

end Shared.Codes.FiniteProgramPairContinuation
