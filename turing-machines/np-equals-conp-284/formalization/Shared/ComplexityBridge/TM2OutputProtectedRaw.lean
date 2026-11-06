import Shared.Codes.FiniteProgramTaggedRawOutput
import Shared.ComplexityBridge.TM2OutputProtectedBoolean

/-! An actual finite continuation connects the protected TM2 output compactor
to the checked untagger. On nonempty output it reaches a positioned raw binary
tape modulo blank padding. The distinct empty-output path remains separate. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2OutputProtectedRaw

open Turing
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel StatusRel run_related)
open Shared.Codes.FiniteProgramLink (shiftConfig shiftStatus)
open Shared.Codes.FiniteProgramTaggedLoop (canonical)
open Shared.ComplexityBridge.TM2BinaryPostCosts (Alphabet)
open Shared.ComplexityBridge.TM2OutputProtectedAllScan (cells)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

abbrev raw := Shared.Codes.FiniteProgramTaggedRawOutput.program

def source (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : Program := TM2OutputProtectedCompact.program tm enc out

def exit (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : Nat := TM2OutputProtectedCompact.finalStop tm enc out

def program (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : Program :=
  Shared.Codes.FiniteProgramOneExit.program (source tm enc out) raw (exit tm enc out)

def offset (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : Nat := Shared.Codes.FiniteProgramOneExit.offset (source tm enc out)

def rawExit (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : Nat := offset tm enc out+22

theorem exit_bound (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : exit tm enc out < (source tm enc out).length :=
  TM2OutputProtectedBoolean.finalStop_bound tm enc out

theorem program_valid (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : valid (program tm enc out) = true :=
  Shared.Codes.FiniteProgramOneExit.program_valid _ _ _ (TM2OutputProtectedCompact.program_valid tm enc out)
    Shared.Codes.FiniteProgramTaggedRawOutput.program_valid (exit_bound tm enc out)

theorem rawExit_bound (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : rawExit tm enc out < (program tm enc out).length := by
  simp [rawExit,program,offset,Shared.Codes.FiniteProgramOneExit.program_length,
    Shared.Codes.FiniteProgramTaggedRawOutput.program_length]

theorem rawExit_placeholder (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) (t : Tape) :
    step (program tm enc out) (rawExit tm enc out,t) = some (.inl false) := by
  have h := Shared.Codes.FiniteProgramOneExit.continuation (source tm enc out) raw (exit tm enc out)
    Shared.Codes.FiniteProgramTaggedRawOutput.program_valid (22,t)
    (by simp [Shared.Codes.FiniteProgramTaggedRawOutput.program_length]) 1
  have hr : run raw (22,t) 1 = some (.inl false) := by
    simpa [run,advance] using Shared.Codes.FiniteProgramTaggedRawOutput.terminal_placeholder t
  rw [hr] at h
  simpa [program,rawExit,offset,shiftConfig,shiftStatus,run,advance] using h

def cost (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) (bits bs : List Bool) : Nat :=
  TM2OutputProtectedCompact.cost width (cells tm enc out bs.reverse)+2+
    Shared.Codes.FiniteProgramTaggedRawOutput.cost bits

/-- The actual protected-output program and raw cleanup run in one linked
table, returning a positioned raw tape for every nonempty output word. -/
theorem run_nonempty (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (enc0 : enc default = List.Vector.replicate width false)
    (out : tm.Γ tm.k₁ ≃ Bool) (bits : List Bool) (first : Bool) (bs : List Bool)
    (hrev : bits.reverse = first::bs) (t : Tape)
    (ht : TM0FiniteProgram.tape t = Turing.Tape.mk₁
      (TM2BinaryOutputShape.outputBits tm (TM2OutputProtectedCodec.encode tm enc) (bits.map out.symm))) :
    ∃ t', run (program tm enc out) (0,t) (cost tm enc out bits bs) =
        some (.inr (rawExit tm enc out,t')) ∧ TapeRel t' (initial bits).2 := by
  let p := source tm enc out
  let e := exit tm enc out
  let n := TM2OutputProtectedCompact.cost width (cells tm enc out bs.reverse)
  have hp : valid p = true := TM2OutputProtectedCompact.program_valid tm enc out
  have hp0 : 0 < p.length := Shared.Codes.FiniteProgramLink.valid_nonempty p hp
  have he : e < p.length := exit_bound tm enc out
  have hstop : ∀ u, step p (e,u) = some (.inl false) := TM2OutputProtectedCompact.final_placeholder tm enc out
  obtain ⟨u,hu,hurel⟩ := TM2OutputProtectedCompact.run_nonempty tm enc dec hdec enc0 out bits first bs hrev t ht
  have hpre := Shared.Codes.FiniteProgramOneExit.first_entry p raw e (0,t) (e,u) n hp hp0 hstop hu
  have hhand := Shared.Codes.FiniteProgramOneExit.handoff p raw e he u
  let bounced := Shared.Codes.FiniteProgramThreeExit.bounce u
  have hrel : TapeRel bounced (canonical [] false bits).2 :=
    (Shared.Codes.FiniteProgramThreeExit.bounce_related u).trans hurel
  obtain ⟨v,hraw,hv⟩ := Shared.Codes.FiniteProgramTaggedRawOutput.run_output bits (0,bounced) rfl hrel
  have hshift := Shared.Codes.FiniteProgramOneExit.continuation p raw e
    Shared.Codes.FiniteProgramTaggedRawOutput.program_valid (0,bounced)
    (by simp [Shared.Codes.FiniteProgramTaggedRawOutput.program_length])
    (Shared.Codes.FiniteProgramTaggedRawOutput.cost bits)
  rw [hraw] at hshift
  refine ⟨v,?_,hv⟩
  change run (Shared.Codes.FiniteProgramOneExit.program p raw e) (0,t)
    (n+2+Shared.Codes.FiniteProgramTaggedRawOutput.cost bits) = _
  rw [show n+2+Shared.Codes.FiniteProgramTaggedRawOutput.cost bits =
    n+(2+Shared.Codes.FiniteProgramTaggedRawOutput.cost bits) by omega,
    run_continue _ _ _ _ _ hpre,run_continue _ _ _ _ _ hhand]
  simpa [program,source,exit,rawExit,offset,p,e,n,bounced,shiftConfig,shiftStatus] using hshift

/-- The entire compaction and raw positioning clock is polynomial in the
codec width and the number of output bits. -/
theorem cost_bound (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) (bits : List Bool) (first : Bool) (bs : List Bool)
    (hrev : bits.reverse = first::bs) :
    cost tm enc out bits bs ≤
      TM2OutputProtectedPipeline.writerCost width bs.length+
      (2+((width+4)+((bs.length+1)*((10*width+36)*bs.length+19*width+69)+2*bs.length)))+
      2+(3*bits.length+5+(bits.length*(20*bits.length+21)+6)) := by
  have hc := TM2OutputProtectedCompact.cost_bound width (cells tm enc out bs.reverse)
  have hr := Shared.Codes.FiniteProgramTaggedRawOutput.cost_bound bits
  have hlen : (cells tm enc out bs.reverse).length = bs.length := by simp [cells]
  rw [hlen] at hc
  unfold cost
  omega

end Shared.ComplexityBridge.TM2OutputProtectedRaw
