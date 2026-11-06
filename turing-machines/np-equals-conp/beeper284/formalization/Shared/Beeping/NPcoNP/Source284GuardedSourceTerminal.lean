import Shared.Beeping.NPcoNP.Source284LoadedTerminal

/-! The raw source program reaches the Boolean terminal result of the guarded
joined verifier. Runway bounds are explicit and may depend on the input; no
uniform coefficient, beeper controller, or physical table is claimed. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
namespace Shared.Beeping.NPcoNP.Source284GuardedSourceTerminal

open Turing ComplexityTheory Shared.ComplexityBridge
open Shared.ComplexityBridge.TM2BinaryPostCosts
open Shared.Codes.FinitePrograms
open Shared.Beeping.NPcoNP.Source284JoinedFrames
open Shared.Beeping.NPcoNP.Source284JoinedHaltingVerifier
open Shared.Beeping.NPcoNP.Source284FramedEncoderTable (word)
open Shared.Beeping.NPcoNP.Source284FramedEncoder (serialClock sourceTime sourceDescription)
open Shared.Beeping.NPcoNP.Source284CertificateProbeLayout (firstZeros)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)

/-- The real fixed source continuation returns the guarded Boolean after the
paid loader, finite verifier prefix, and one terminal source step. Both runway
inequalities are necessary hypotheses; they are not uniformized here. -/
theorem guarded_source_terminal (cutoff : Polynomial Nat) (R : List Bool × List Bool → Bool)
    (hR : IsPolyTime R) :
    letI := Source284JoinedHaltingEncoder.machine.kFin
    letI := alphabet
    letI : Inhabited Source284JoinedHaltingEncoder.machine.Λ := ⟨Source284JoinedHaltingEncoder.machine.main⟩
    ∃ (width : Nat) (enc : Alphabet Source284JoinedHaltingEncoder.machine → List.Vector Bool width)
      (program : Program) (bound verifierClock : Polynomial Nat),
      valid program = true ∧ ∀ x w : List Bool,
        let bits := BitstringEncoding.bitEncode (joinedBits x w,([] : List Bool))
        ∃ (first : Bool) (bs : List Bool) (d fuel : Nat),
          bits.reverse = first::bs ∧ d ≤ bound.eval (joinedBits x w).length ∧
          fuel < d+2+(TM2OutputProtectedRaw.cost Source284JoinedHaltingEncoder.machine enc
            (Equiv.refl Bool) bits bs+2+verifierClock.eval bits.length) ∧
          ∀ (k limit certificate inputSuffix : Nat),
            Source284TaggedWitnessCodec.decode limit certificate = some w →
            1+fuel-(2*(inputBits Source284JoinedRawEncodeTM2.machine
              (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc) (joinedBits x w)).length+3)
                ≤ k*(x.length*x.length)+2 →
            (word (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc)).length+
              (1+serialClock (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc) x w fuel)
                ≤ firstZeros k x.length+2*x.length+4 →
            ((Source284Relative.run
              (sourceDescription (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc) program k)
              (Source284Relative.initial (encodeFrame x inputSuffix) certificate)
              (sourceTime (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc) k x w fuel+1)).state == 0) =
                (if w.length ≤ cutoff.eval x.length then R (x,w) else false) := by
  letI := Source284JoinedHaltingEncoder.machine.kFin
  letI := alphabet
  letI : Inhabited Source284JoinedHaltingEncoder.machine.Λ := ⟨Source284JoinedHaltingEncoder.machine.main⟩
  obtain ⟨width,enc,program,bound,vc,hvalid,hpred⟩ :=
    Source284VerifierPredecessor.guarded_source_predecessor cutoff R hR
  refine ⟨width,enc,program,bound,vc,hvalid,?_⟩
  intro x w
  obtain ⟨first,bs,d,fuel,q,reference,hrev,hd,hfuel,_,hq,_,hsource⟩ := hpred x w
  refine ⟨first,bs,d,fuel,hrev,hd,hfuel,?_⟩
  intro k limit certificate inputSuffix hdec hi hw
  obtain ⟨ws,actual,rev,hcert,hstep,_,hwindow⟩ := hsource k limit certificate inputSuffix hdec hi hw
  rw [hcert] at hwindow ⊢
  exact Source284LoadedTerminal.loaded_terminal_step
    (TM2OutputProtectedCodec.encode Source284JoinedHaltingEncoder.machine enc)
    program k x w ws inputSuffix fuel q actual rev _ hvalid hq hstep hwindow

end Shared.Beeping.NPcoNP.Source284GuardedSourceTerminal
