import Shared.Beeping.NPcoNP.Source284DynamicJoinedInput
import Shared.Beeping.NPcoNP.Source284InputRunwayClear

/-! Clear the paid input-side sentinel after the dynamic witness guard and
joined-prefix construction. This exposes the zero runway expected by the
existing serializer. The source verifier and physical refinement are not yet
proved here. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.Source284DynamicInputRunway

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (stack)
open Shared.Beeping.NPcoNP.Source284SourceRelocation (lift lift_toSource)

def description (k states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284DynamicJoinedInput.description k (6+states) (Source284InputRunwayClear.table continuation)

def cost (k : Nat) (input witness : List Bool) : Nat :=
  Source284GapUnarySource.totalCost k input+
    (Source284DynamicGuardReveal.revealCost (Source284DynamicGuardSource.bound k input.length) witness+
      (Source284DynamicInputFrame.cost input+
        (Source284DynamicJoinedInput.cost (Source284DynamicGuardSource.bound k input.length) input witness+6)))

/-- The exact source computation reaches the same two-sided joined-prefix
layout as the existing serializer, including both retained high suffixes. -/
theorem decoded_then (k states : Nat) (continuation : Nat → Bool → Row)
    (input witness : List Bool) (certificate inputSuffix : Nat) (hn : 0 < states) (hv : Closed states continuation)
    (hdec : Source284TaggedWitnessCodec.decode (Source284DynamicGuardSource.bound k input.length)
      certificate = some witness) :
    ∃ witnessSuffix, certificate=4*encodeFrame witness witnessSuffix ∧ ∀ fuel,
      Source284Relative.run (description k states continuation)
        (Source284Relative.initial (encodeFrame input inputSuffix) certificate) (cost k input witness+fuel) =
      lift (707+317*k+318+1+139+254+6) (Source284Relative.run (encode states continuation 1)
        ⟨8*Source284DynamicInputFrame.tail k input inputSuffix,
          stack (Source284JoinedFrames.joinedBits input witness)
            (Source284DynamicJoinedInput.witnessTail (Source284DynamicGuardSource.bound k input.length) witnessSuffix),
          active 0⟩ fuel) := by
  have hc := Source284InputRunwayClear.closed states continuation hn hv
  obtain ⟨witnessSuffix,hcert,hjoined⟩ := Source284DynamicJoinedInput.decoded_joined
    k (6+states) (Source284InputRunwayClear.table continuation) input witness certificate inputSuffix
    (by omega) hc hdec
  refine ⟨witnessSuffix,hcert,?_⟩
  intro fuel
  let limit := Source284DynamicGuardSource.bound k input.length
  let t := Source284DynamicInputFrame.tail k input inputSuffix
  let right := stack (Source284JoinedFrames.joinedBits input witness)
    (Source284DynamicJoinedInput.witnessTail limit witnessSuffix)
  have h := hjoined (6+fuel)
  have ht : cost k input witness+fuel = Source284GapUnarySource.totalCost k input+
      (Source284DynamicGuardReveal.revealCost limit witness+
        (Source284DynamicInputFrame.cost input+(Source284DynamicJoinedInput.cost limit input witness+(6+fuel)))) := by
    simp [cost,limit]; omega
  change Source284Relative.run (description k states continuation)
    (Source284Relative.initial (encodeFrame input inputSuffix) certificate) _ =
      lift (707+317*k+318+1+139+254) (Source284Relative.run
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

/-- Malformed and overlong certificates remain nonaccepting at every source
clock for this same serializer-ready table. -/
theorem rejected_raw_never_accepts (k states : Nat) (continuation : Nat → Bool → Row)
    (input certificate : Nat) (hn : 0 < states) (hv : Closed states continuation)
    (hbad : Source284TaggedWitnessCodec.decode
      (Source284DynamicGuardSource.bound k (Source284Parser.length input)) certificate = none) :
    ∀ clock, Source284Relative.accepts (description k states continuation) input certificate clock = false := by
  exact Source284DynamicJoinedInput.rejected_raw_never_accepts k (6+states)
    (Source284InputRunwayClear.table continuation) input certificate (by omega)
    (Source284InputRunwayClear.closed states continuation hn hv) hbad

noncomputable def costPolynomial (k : Nat) : Polynomial Nat :=
  Source284DynamicJoinedInput.totalPolynomial k+6

theorem cost_polynomial (k : Nat) (input witness : List Bool) (certificate : Nat)
    (hdec : Source284TaggedWitnessCodec.decode (Source284DynamicGuardSource.bound k input.length)
      certificate = some witness) : cost k input witness ≤ (costPolynomial k).eval input.length := by
  have h := Source284DynamicJoinedInput.total_polynomial k input witness certificate hdec
  simp only [costPolynomial,Polynomial.eval_add,Polynomial.eval_ofNat]
  simp only [cost] at *
  omega

end Shared.Beeping.NPcoNP.Source284DynamicInputRunway
