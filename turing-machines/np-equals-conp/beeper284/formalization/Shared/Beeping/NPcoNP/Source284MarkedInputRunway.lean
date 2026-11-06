import Shared.Beeping.NPcoNP.Source284MarkedJoinedUniform
import Shared.Beeping.NPcoNP.Source284InputRunwayClear

/-! Clear the joined input-side sentinel after the counter transfer. This
exposes the two independent blank runways required by the serializer. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.Source284MarkedInputRunway

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (stack)
open Shared.Beeping.NPcoNP.Source284SourceRelocation (lift lift_toSource)
open Shared.Beeping.NPcoNP.Source284CheckpointMarkedWorkspace (blankTail)

def description (k r states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284MarkedJoinedInput.description k r (6+states) (Source284InputRunwayClear.table continuation)

def cost (k r : Nat) (input witness : List Bool) : Nat :=
  Source284MarkedJoinedInput.totalCost k r input witness+6

/-- Both actual high suffixes are retained at the serializer entry. -/
theorem decoded_then (k r states : Nat) (continuation : Nat → Bool → Row)
    (input witness : List Bool) (certificate inputSuffix : Nat) (hn : 0 < states) (hv : Closed states continuation)
    (hdec : Source284TaggedWitnessCodec.decode (Source284DynamicGuardSource.bound k input.length)
      certificate = some witness) :
    ∃ witnessSuffix, certificate=4*encodeFrame witness witnessSuffix ∧ ∀ fuel,
      Source284Relative.run (description k r states continuation)
        (Source284Relative.initial (encodeFrame input inputSuffix) certificate) (cost k r input witness+fuel) =
      lift (1371+317*k+317*r+318+1+178+254+6) (Source284Relative.run (encode states continuation 1)
        ⟨8*(blankTail k r input.length inputSuffix/2),
          stack (Source284JoinedFrames.joinedBits input witness)
            (Source284DynamicJoinedInput.witnessTail (Source284MarkedJoinedInput.enlargedLimit k r input.length) witnessSuffix),
          active 0⟩ fuel) := by
  have hc := Source284InputRunwayClear.closed states continuation hn hv
  obtain ⟨witnessSuffix,hcert,hjoined⟩ := Source284MarkedJoinedInput.decoded_joined
    k r (6+states) (Source284InputRunwayClear.table continuation) input witness certificate inputSuffix
    (by omega) hc hdec
  refine ⟨witnessSuffix,hcert,?_⟩
  intro fuel
  let limit := Source284MarkedJoinedInput.enlargedLimit k r input.length
  let t := blankTail k r input.length inputSuffix/2
  let right := stack (Source284JoinedFrames.joinedBits input witness)
    (Source284DynamicJoinedInput.witnessTail limit witnessSuffix)
  have h := hjoined (6+fuel)
  have ht : cost k r input witness+fuel = Source284MarkedJoinedInput.totalCost k r input witness+(6+fuel) := by
    simp [cost]; omega
  change Source284Relative.run (description k r states continuation)
    (Source284Relative.initial (encodeFrame input inputSuffix) certificate) _ =
      lift (1371+317*k+317*r+318+1+178+254) (Source284Relative.run
        (encode (6+states) (Source284InputRunwayClear.table continuation) 1)
        ⟨4*(2*t+1),right,active 0⟩ (6+fuel)) at h
  let c : Config := ⟨4*(2*t+1),right,some 0⟩
  have hvalid : Valid (6+states) c := by intro q hq; simp [c] at hq; subst q; omega
  have hrun := run_toSource (6+states) (Source284InputRunwayClear.table continuation) 1 c hc hvalid (6+fuel)
  change Source284Relative.run (encode (6+states) (Source284InputRunwayClear.table continuation) 1)
    ⟨4*(2*t+1),right,active 0⟩ (6+fuel) = _ at hrun
  rw [hrun,Source284InputRunwayClear.clear_then,← lift_toSource,Source284SourceRelocation.lift_add] at h
  let d : Config := ⟨8*t,right,some 0⟩
  have hd : Valid states d := by intro q hq; simp [d] at hq; subst q; exact hn
  have hfinal := run_toSource states continuation 1 d hv hd fuel
  change Source284Relative.run (encode states continuation 1) ⟨8*t,right,active 0⟩ fuel = _ at hfinal
  rw [← hfinal] at h
  rw [ht]
  exact h

theorem rejected_raw_never_accepts (k r states : Nat) (continuation : Nat → Bool → Row)
    (input certificate : Nat) (hn : 0 < states) (hv : Closed states continuation)
    (hbad : Source284TaggedWitnessCodec.decode
      (Source284DynamicGuardSource.bound k (Source284Parser.length input)) certificate = none) :
    ∀ clock, Source284Relative.accepts (description k r states continuation) input certificate clock = false := by
  unfold description
  exact Source284MarkedJoinedInput.rejected_raw_never_accepts k r (6+states)
    (Source284InputRunwayClear.table continuation) input certificate (by omega)
    (Source284InputRunwayClear.closed states continuation hn hv) hbad

noncomputable def costPolynomial (k r : Nat) : Polynomial Nat :=
  Source284MarkedJoinedUniform.totalPolynomial k r+6

theorem cost_polynomial (k r : Nat) (input witness : List Bool) (certificate : Nat)
    (hdec : Source284TaggedWitnessCodec.decode (Source284DynamicGuardSource.bound k input.length)
      certificate = some witness) : cost k r input witness ≤ (costPolynomial k r).eval input.length := by
  have h := Source284MarkedJoinedUniform.total_polynomial k r input witness certificate hdec
  simp only [costPolynomial,Polynomial.eval_add,Polynomial.eval_ofNat,cost]
  omega

end Shared.Beeping.NPcoNP.Source284MarkedInputRunway
