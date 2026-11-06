import Shared.ComplexityBridge.TM2OutputProtectedVerifier
import Shared.ComplexityBridge.TM2BinaryFixedOutput

/-! A halted finite TM2 machine, its protected output extraction, and an
arbitrary clocked finite verifier form one finite binary program. This is a
successful-run composition for nonempty output; invalid codes, timeouts,
empty output, and the source/physical-machine binding remain separate. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2ProtectedVerifierComposition

open Turing
open Shared.Codes.FinitePrograms
open Shared.ComplexityBridge.TM2Symbols
open Shared.ComplexityBridge.TM2BinaryPostCosts
open Shared.ComplexityBridge.TM2BinaryFixedHalt
open Shared.ComplexityBridge.TM0FiniteReindex
open Shared.ComplexityBridge.TM0FiniteProgram

/-- A single finite program first simulates the fixed TM2 machine, then
compacts and untags its nonempty output, then runs the supplied bounded
verifier. Every transition and both handoffs are included in the clock. -/
theorem halted_nonempty_verifier (tm : FinTM2) (alphabet : ∀ k, Fintype (tm.Γ k))
    {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (dec : List.Vector Bool width → Alphabet tm)
    (enc0 : enc default = List.Vector.replicate width false)
    (encdec : ∀ a, dec (enc a) = a) (out : tm.Γ tm.k₁ ≃ Bool)
    (clock : Polynomial Nat) (verifier : Program) (hv : valid verifier = true) :
    letI := tm.kFin
    letI := alphabet
    letI : Inhabited tm.Λ := ⟨tm.main⟩
    ∃ (program : Program) (bound : Polynomial Nat), valid program = true ∧
      ∀ (input : List (tm.Γ tm.k₀)) (bits : List Bool) (first : Bool) (bs : List Bool)
        (n fuel : Nat) (answer : Bool),
        bits.reverse = first::bs →
        runSteps tm.step n (Turing.initList tm input) = some (Turing.haltList tm (bits.map out.symm)) →
        n ≤ clock.eval input.length → bounded verifier bits fuel = some answer →
        ∃ d ≤ bound.eval input.length,
          run program (initial (inputBits tm (TM2OutputProtectedCodec.encode tm enc) input))
            (d+2+(TM2OutputProtectedRaw.cost tm enc out bits bs+2+fuel)) = some (.inl answer) := by
  letI := tm.kFin
  letI := alphabet
  letI : Inhabited tm.Λ := ⟨tm.main⟩
  let penc := TM2OutputProtectedCodec.encode tm enc
  let pdec := TM2OutputProtectedCodec.decode tm dec
  have hpenc0 : penc default = List.Vector.replicate (width+3) false :=
    TM2OutputProtectedCodec.encode_blank tm enc enc0
  have hpdec : ∀ a, pdec (penc a) = a := TM2OutputProtectedCodec.decode_encode tm enc dec encdec
  let M := TM1to0.tr (TM1to1.tr penc pdec (TM2to1.tr tm.m))
  let S := support0 tm alphabet penc pdec
  let hs := support0_correct tm alphabet penc pdec
  letI : Inhabited (Fin S.card) := ⟨zero M S hs⟩
  let p := program (machine M S hs)
  let stop := mainIndex (index M S hs (control tm penc pdec))
  let continuation := TM2OutputProtectedVerifier.program tm enc out verifier
  have hcont : valid continuation = true := TM2OutputProtectedVerifier.program_valid tm enc out verifier hv
  have hp : valid p = true := TM0FiniteProgram.program_valid (machine M S hs)
  have hstop : stop < p.length := by
    dsimp [stop,p]
    rw [TM0FiniteProgram.program_length]
    have hi := (index M S hs (control tm penc pdec)).isLt
    dsimp [mainIndex]
    omega
  let linked := Shared.Codes.FiniteProgramOneExit.program p continuation stop
  have hlinked : valid linked = true := Shared.Codes.FiniteProgramOneExit.program_valid _ _ _ hp hcont hstop
  refine ⟨linked,2*timePolynomial tm alphabet penc pdec clock,hlinked,?_⟩
  intro input bits first bs n fuel answer hrev hrun hclock hbounded
  have h := TM2BinaryFixedOutput.halted_run_continuation tm alphabet penc pdec hpenc0 hpdec clock continuation hcont
    input (bits.map out.symm) n (TM2OutputProtectedRaw.cost tm enc out bits bs+2+fuel) hrun hclock
  obtain ⟨d,hd,t,ht,hr⟩ := h
  refine ⟨d,hd,?_⟩
  let bounced := Shared.Codes.FiniteProgramThreeExit.bounce t
  have hb := Shared.Codes.FiniteProgramThreeExit.bounce_related t
  have hbTape : tape bounced = tape t := hb
  have ht' : tape bounced = Turing.Tape.mk₁ (TM2BinaryOutputShape.outputBits tm penc (bits.map out.symm)) := by
    rw [hbTape,ht]
  have hc := TM2OutputProtectedVerifier.run_nonempty tm enc dec encdec enc0 out verifier hv bits first bs
    hrev bounced ht' fuel answer hbounded
  rw [hc] at hr
  simpa [linked,penc,pdec,M,S,hs,p,stop,continuation,Shared.Codes.FiniteProgramLink.shiftStatus] using hr

end Shared.ComplexityBridge.TM2ProtectedVerifierComposition
