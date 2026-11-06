import Shared.Beeping.NPcoNP.Source284JoinedHaltingEncoder
import Shared.Beeping.NPcoNP.Source284JoinedFiniteVerifier

/-! A single finite binary program for the joined encoder and original-cutoff
verifier, starting from a protected TM2 input encoding. The source loader and
physical 284-state table are not bound here. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
namespace Shared.Beeping.NPcoNP.Source284JoinedHaltingVerifier

open Turing ComplexityTheory Shared.ComplexityBridge
open Shared.ComplexityBridge.TM2Symbols
open Shared.ComplexityBridge.TM2BinaryPostCosts
open Shared.Codes.FinitePrograms
open Shared.Beeping.NPcoNP.Source284JoinedFrames
open Shared.Beeping.NPcoNP.Source284JoinedHaltingEncoder

def alphabet (k : machine.K) : Fintype (machine.Γ k) := by
  change Fintype Bool
  infer_instance

noncomputable def blockClock : Polynomial Nat := 2*Polynomial.X+2

/-- The halt-only program change does not alter the serialized input format.
In particular the existing source serializer can be instantiated with the
protected codec used by this verifier pipeline. -/
theorem protected_input_agrees {width : Nat}
    (enc : Alphabet machine → List.Vector Bool width) (bits : List Bool) :
    inputBits machine (TM2OutputProtectedCodec.encode machine enc) bits =
      inputBits Source284JoinedRawEncodeTM2.machine (TM2OutputProtectedCodec.encode machine enc) bits := by
  rfl

/-- For a fixed polynomial relation and original cutoff, one valid finite
program encodes every exact joined input and returns the guarded answer. Its
input is the protected serialized TM2 input, and all machine handoffs and the
bounded verifier clock are explicitly charged. -/
theorem encoded_joined_verifier (p : Polynomial Nat) (R : List Bool × List Bool → Bool)
    (hR : IsPolyTime R) :
    letI := machine.kFin
    letI := alphabet
    letI : Inhabited machine.Λ := ⟨machine.main⟩
    ∃ (width : Nat) (enc : Alphabet machine → List.Vector Bool width)
      (program : Program) (bound verifierClock : Polynomial Nat),
      valid program = true ∧ ∀ x w : List Bool,
        let bits := BitstringEncoding.bitEncode (joinedBits x w,([] : List Bool))
        ∃ (first : Bool) (bs : List Bool) (d : Nat),
          bits.reverse = first::bs ∧ d ≤ bound.eval (joinedBits x w).length ∧
          run program (initial (inputBits machine (TM2OutputProtectedCodec.encode machine enc) (joinedBits x w)))
            (d+2+(TM2OutputProtectedRaw.cost machine enc (Equiv.refl Bool) bits bs+2+
              verifierClock.eval bits.length)) =
            some (.inl (if w.length ≤ p.eval x.length then R (x,w) else false)) := by
  letI := machine.kFin
  letI := alphabet
  letI : Inhabited machine.Λ := ⟨machine.main⟩
  obtain ⟨width,enc,dec,hblank,hinv⟩ := TM2BinaryPostCosts.codec_exists machine alphabet
  obtain ⟨verifier,vclock,hvalid,hverifier⟩ := Source284JoinedFiniteVerifier.guarded_bounded p R hR
  obtain ⟨program,bound,hprogram,hcombined⟩ :=
    TM2ProtectedVerifierComposition.halted_nonempty_verifier machine alphabet enc dec hblank hinv
      (Equiv.refl Bool) blockClock verifier hvalid
  refine ⟨width,enc,program,bound,vclock,hprogram,?_⟩
  intro x w
  let bits := BitstringEncoding.bitEncode (joinedBits x w,([] : List Bool))
  have hlen : bits.length = 12*x.length+12*w.length+37 :=
    Source284JoinedDecodeTM2.canonical_joined_length x w
  have hnonempty : bits.reverse ≠ [] := by
    intro hn
    have he : bits.length = 0 := by
      have := congrArg List.length hn
      simpa using this
    omega
  obtain ⟨first,bs,hrev⟩ := List.exists_cons_of_ne_nil hnonempty
  obtain ⟨n,hn,hrun⟩ := encode_joined_halts x w
  have hclock : n ≤ blockClock.eval (joinedBits x w).length := by
    simp only [blockClock,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_X]
    omega
  have hbounded := hverifier x w
  have hrun' : runSteps machine.step n (Turing.initList machine (joinedBits x w)) =
      some (Turing.haltList machine (bits.map (Equiv.refl Bool).symm)) := by
    simpa [bits] using hrun
  obtain ⟨d,hd,hr⟩ := hcombined (joinedBits x w) bits first bs n (vclock.eval bits.length)
    (if w.length ≤ p.eval x.length then R (x,w) else false) hrev hrun' hclock hbounded
  exact ⟨first,bs,d,hrev,hd,hr⟩

end Shared.Beeping.NPcoNP.Source284JoinedHaltingVerifier
