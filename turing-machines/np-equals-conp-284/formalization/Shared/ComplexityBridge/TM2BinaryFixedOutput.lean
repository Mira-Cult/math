import Shared.ComplexityBridge.TM2BinaryFixedHalt
import Shared.ComplexityBridge.TM0FiniteTerminal
import Shared.ComplexityBridge.TM2BinaryOutputShape

/-! A fixed TM2 simulator reaches its fixed halt state and executes a charged
finite continuation on the full encoded output tape. This does not itself
provide an input wrapper, a total evaluator, or event preservation. -/
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2BinaryFixedOutput
open Turing
open Shared.Codes.FinitePrograms
open Shared.ComplexityBridge.TM2Symbols
open Shared.ComplexityBridge.TM2BinaryPostCosts
open Shared.ComplexityBridge.TM2BinaryFixedHalt
open Shared.ComplexityBridge.TM0FiniteReindex
open Shared.ComplexityBridge.TM0FiniteProgram

variable (tm : FinTM2) (alphabet : ∀ k, Fintype (tm.Γ k))
variable {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
variable (dec : List.Vector Bool width → Alphabet tm)
variable (enc0 : enc default = List.Vector.replicate width false)
variable (encdec : ∀ a, dec (enc a) = a)
include enc0 encdec

/-- The selected table and halt row depend only on the fixed machine and
codec. The run reaches the full serialized output and executes the requested
finite continuation after two additional physical transitions. -/
theorem halted_run_continuation (clock : Polynomial Nat) (continuation : Program)
    (hcont : valid continuation = true) :
    letI := tm.kFin
    letI := alphabet
    letI : Inhabited tm.Λ := ⟨tm.main⟩
    let M := TM1to0.tr (TM1to1.tr enc dec (TM2to1.tr tm.m))
    let S := support0 tm alphabet enc dec
    let hs := support0_correct tm alphabet enc dec
    let p := program (machine M S hs)
    let stop := mainIndex (index M S hs (control tm enc dec))
    ∀ (bits : List (tm.Γ tm.k₀)) (output : List (tm.Γ tm.k₁)) (n fuel : Nat),
      runSteps tm.step n (Turing.initList tm bits) = some (Turing.haltList tm output) →
      n ≤ clock.eval bits.length →
      ∃ d ≤ (2*timePolynomial tm alphabet enc dec clock).eval bits.length, ∃ t,
        tape t = Tape.mk₁ (TM2BinaryOutputShape.outputBits tm enc output) ∧
        run (Shared.Codes.FiniteProgramOneExit.program p continuation stop)
          (initial (inputBits tm enc bits)) (d+2+fuel) =
          Shared.Codes.FiniteProgramLink.shiftStatus
            (Shared.Codes.FiniteProgramOneExit.offset p)
            (run continuation (0,Shared.Codes.FiniteProgramThreeExit.bounce t) fuel) := by
  letI := tm.kFin
  letI := alphabet
  letI : Inhabited tm.Λ := ⟨tm.main⟩
  let M := TM1to0.tr (TM1to1.tr enc dec (TM2to1.tr tm.m))
  let S := support0 tm alphabet enc dec
  let hs := support0_correct tm alphabet enc dec
  dsimp only
  intro bits output n fuel hrun htime
  obtain ⟨k,_,hk,mid,hrel,hr,_⟩ := halt_bounded tm alphabet enc dec enc0 encdec
    clock bits n (Turing.haltList tm output) hrun htime (by rfl)
  let last := TM1to0.trCfg (TM1to1.tr enc dec (TM2to1.tr tm.m))
    (TM1to1.trCfg enc enc0 mid)
  have hcontrol : last.q = control tm enc dec :=
    translated_control tm enc dec enc0 output mid hrel
  have hmem : control tm enc dec ∈ S := control_mem_support tm enc dec alphabet
  have hh : ∀ b, M (control tm enc dec) b = none := control_halts tm enc dec
  obtain ⟨d,hd,t,ht,hlinked⟩ := TM0FiniteTerminal.reindexed_run_continuation M S hs
    (control tm enc dec) hmem hh continuation hcont (inputBits tm enc bits) k fuel last hr hcontrol
  have hshape : last.Tape = Tape.mk₁ (TM2BinaryOutputShape.outputBits tm enc output) := by
    change TM1to1.trTape enc0 mid.Tape = _
    exact TM2BinaryOutputShape.halt_binary_tape tm enc enc0 output mid hrel
  refine ⟨d,?_,t,?_,hlinked⟩
  · simp only [Polynomial.eval_mul,Polynomial.eval_ofNat]
    omega
  · rw [ht,hshape]

end Shared.ComplexityBridge.TM2BinaryFixedOutput
