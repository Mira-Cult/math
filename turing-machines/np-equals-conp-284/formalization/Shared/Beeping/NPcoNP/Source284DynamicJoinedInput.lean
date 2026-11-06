import Shared.Beeping.NPcoNP.Source284DynamicInputFrame
import Shared.Beeping.NPcoNP.Source284JoinedFrames
import Shared.Beeping.NPcoNP.Source284WitnessCompact

/-! Join the restored input and guarded witness into the existing executable
joined-prefix encoding. The canonical serializer, original smaller cutoff,
comparison controller and physical-table refinement remain separate. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.Source284DynamicJoinedInput

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (stack)
open Shared.Beeping.NPcoNP.Source284SourceRelocation (lift lift_toSource)

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284WitnessSeek.table (Source284WitnessCompact.table
    (Source284ScratchNormalize.table (Source284JoinedFrames.table continuation)))

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (254+states) (table continuation) := by
  have hj := Source284JoinedFrames.closed states continuation hn hv
  have hnrm := Source284WitnessReframe.closed (16+states) (Source284JoinedFrames.table continuation)
    (by omega) hj
  have hc := Source284WitnessCompact.closed (68+(16+states))
    (Source284ScratchNormalize.table (Source284JoinedFrames.table continuation)) (by omega) hnrm
  have hs := Source284WitnessSeek.closed (160+(68+(16+states)))
    (Source284WitnessCompact.table (Source284ScratchNormalize.table (Source284JoinedFrames.table continuation)))
    (by omega) hc
  simpa [table,show 10+(160+(68+(16+states)))=254+states by omega] using hs

def cost (limit : Nat) (input witness : List Bool) : Nat :=
  (3+2*((limit+1)+1)+(if witness=[] then 4 else 2))+
    Source284WitnessCompact.extraCost (limit+1) witness.length+
      (6*witness.length+11)+(2*input.length+6)

def witnessTail (limit witnessSuffix : Nat) : Nat :=
  2^(2*((limit+1)+1))*((8*((witnessSuffix/4)/4)+1)/4)

/-- The paid seek and compaction recover the guarded witness, then the
normalizer and finite join table construct the complete joined bit stream. -/
theorem join_then (states : Nat) (continuation : Nat → Bool → Row)
    (limit inputSuffix witnessSuffix fuel : Nat) (input witness : List Bool)
    (hn : 0 < states) (hv : Closed states continuation) :
    let wf := encodeFrame witness (8*((witnessSuffix/4)/4)+1)
    let saved := 4*(4^(limit+1)*(2*wf))+1
    run (table continuation) ⟨2*saved,encodeFrame input inputSuffix,some 0⟩
      (cost limit input witness+fuel) =
    shiftConfig 254 (run continuation
      ⟨inputSuffix,stack (Source284JoinedFrames.joinedBits input witness)
        (witnessTail limit witnessSuffix),some 0⟩ fuel) := by
  let wf := encodeFrame witness (8*((witnessSuffix/4)/4)+1)
  let inputFrame := encodeFrame input inputSuffix
  let seekTime := 3+2*((limit+1)+1)+(if witness=[] then 4 else 2)
  let compactTime := Source284WitnessCompact.extraCost (limit+1) witness.length
  let normalizeTime := 6*witness.length+11
  let joinTime := 2*input.length+6
  have ht : cost limit input witness+fuel = seekTime+(compactTime+(normalizeTime+(joinTime+fuel))) := by
    simp [cost,seekTime,compactTime,normalizeTime,joinTime]; omega
  dsimp only
  rw [ht]
  change run (Source284WitnessSeek.table (Source284WitnessCompact.table
    (Source284ScratchNormalize.table (Source284JoinedFrames.table continuation))))
    ⟨2*(4*(4^(limit+1)*(2*wf))+1),inputFrame,some 0⟩ _ = _
  rw [Source284WitnessSeek.seek_then]
  change shiftConfig 10 (run (Source284WitnessCompact.table
    (Source284ScratchNormalize.table (Source284JoinedFrames.table continuation)))
    ⟨4^((limit+1)+1)*(4*inputFrame+1),wf,some (if witness=[] then 1 else 0)⟩ _) = _
  have hj := Source284JoinedFrames.closed states continuation hn hv
  have hnrm := Source284WitnessReframe.closed (16+states) (Source284JoinedFrames.table continuation) (by omega) hj
  change shiftConfig 10 (run (Source284WitnessScratch.entry
    (Source284WitnessCompact.engine (Source284ScratchNormalize.table (Source284JoinedFrames.table continuation))))
    ⟨4^((limit+1)+1)*(4*inputFrame+1),wf,some (if witness=[] then 1 else 0)⟩ _) = _
  rw [Source284WitnessCompact.compact_after_seek (68+(16+states))
    (Source284ScratchNormalize.table (Source284JoinedFrames.table continuation))
    (limit+1) inputFrame (8*((witnessSuffix/4)/4)+1) witness (normalizeTime+(joinTime+fuel))
    (by omega) hnrm]
  change shiftConfig 10 (shiftConfig 160 (run
    (Source284ScratchNormalize.table (Source284JoinedFrames.table continuation))
    ⟨4*inputFrame+1,2*Source284ScratchFlip.flipped witness (witnessTail limit witnessSuffix),some 0⟩ _)) = _
  rw [Source284WitnessReframe.normalize_then,Source284JoinedFrames.join_then,
    Source284JoinedFrames.joined_stack]
  repeat rw [Source284SourceRelocation.shiftConfig_add]

def description (k states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284DynamicInputFrame.description k (254+states) (table continuation)

/-- For each in-bound decoded witness, a single finite source program starts
from the actual input and certificate, runs the guard, restores both frames,
and reaches the existing joined-prefix interface with exact suffixes. -/
theorem decoded_joined (k states : Nat) (continuation : Nat → Bool → Row)
    (input witness : List Bool) (certificate inputSuffix : Nat) (hn : 0 < states) (hv : Closed states continuation)
    (hdec : Source284TaggedWitnessCodec.decode (Source284DynamicGuardSource.bound k input.length)
      certificate = some witness) :
    ∃ witnessSuffix, certificate=4*encodeFrame witness witnessSuffix ∧ ∀ fuel,
      let limit := Source284DynamicGuardSource.bound k input.length
      let inputTail := Source284DynamicInputFrame.tail k input inputSuffix
      Source284Relative.run (description k states continuation)
        (Source284Relative.initial (encodeFrame input inputSuffix) certificate)
        (Source284GapUnarySource.totalCost k input+
          (Source284DynamicGuardReveal.revealCost limit witness+
            (Source284DynamicInputFrame.cost input+(cost limit input witness+fuel)))) =
      lift (707+317*k+318+1+139+254) (Source284Relative.run (encode states continuation 1)
        ⟨4*(2*inputTail+1),stack (Source284JoinedFrames.joinedBits input witness)
          (witnessTail limit witnessSuffix),active 0⟩ fuel) := by
  have hc := closed states continuation hn hv
  obtain ⟨witnessSuffix,hcert,hframe⟩ := Source284DynamicInputFrame.decoded_input_frame
    k (254+states) (table continuation) input witness certificate inputSuffix (by omega) hc hdec
  refine ⟨witnessSuffix,hcert,?_⟩
  intro fuel
  let limit := Source284DynamicGuardSource.bound k input.length
  let t := Source284DynamicInputFrame.tail k input inputSuffix
  let wf := encodeFrame witness (8*((witnessSuffix/4)/4)+1)
  let saved := 4*(4^(limit+1)*(2*wf))+1
  let inputFrame := encodeFrame input (4*(2*t+1))
  have hr := hframe (cost limit input witness+fuel)
  change Source284Relative.run (description k states continuation) _ _ =
    lift (707+317*k+318+1+139) (Source284Relative.run (encode (254+states) (table continuation) 1)
      ⟨2*saved,inputFrame,active 0⟩ (cost limit input witness+fuel)) at hr
  let c : Config := ⟨2*saved,inputFrame,some 0⟩
  have hvalid : Valid (254+states) c := by intro q hq; simp [c] at hq; subst q; omega
  have heval := run_toSource (254+states) (table continuation) 1 c hc hvalid (cost limit input witness+fuel)
  change Source284Relative.run (encode (254+states) (table continuation) 1)
    ⟨2*saved,inputFrame,active 0⟩ _ = _ at heval
  have hj := join_then states continuation limit (4*(2*t+1)) witnessSuffix fuel input witness hn hv
  change run (table continuation) c _ = _ at hj
  rw [heval,hj,← lift_toSource,Source284SourceRelocation.lift_add] at hr
  let d : Config := ⟨4*(2*t+1),stack (Source284JoinedFrames.joinedBits input witness)
    (witnessTail limit witnessSuffix),some 0⟩
  have hd : Valid states d := by intro q hq; simp [d] at hq; subst q; exact hn
  have hfinal := run_toSource states continuation 1 d hv hd fuel
  change Source284Relative.run (encode states continuation 1)
    ⟨4*(2*t+1),stack (Source284JoinedFrames.joinedBits input witness)
      (witnessTail limit witnessSuffix),active 0⟩ fuel = _ at hfinal
  rw [← hfinal] at hr
  exact hr

/-- The very same source description rejects malformed and overlong
certificates at every clock, including during initialization. -/
theorem rejected_raw_never_accepts (k states : Nat) (continuation : Nat → Bool → Row)
    (input certificate : Nat) (hn : 0 < states) (hv : Closed states continuation)
    (hbad : Source284TaggedWitnessCodec.decode
      (Source284DynamicGuardSource.bound k (Source284Parser.length input)) certificate = none) :
    ∀ clock, Source284Relative.accepts (description k states continuation) input certificate clock = false := by
  have hc := closed states continuation hn hv
  have hi := Source284DynamicInputFrame.closed (254+states) (table continuation) (by omega) hc
  have hr := Source284DynamicGuardReveal.table_closed (139+(254+states))
    (Source284DynamicInputFrame.table (table continuation)) (by omega) hi
  change ∀ clock, Source284Relative.accepts
    (Source284DynamicGuardSource.description k (Source284DynamicGuardReveal.states (139+(254+states)))
      (Source284DynamicGuardReveal.table (Source284DynamicInputFrame.table (table continuation))))
    input certificate clock = false
  exact Source284DynamicGuardSource.rejected_raw_certificate_never_accepts k _ _ input certificate
    (by simp [Source284DynamicGuardReveal.states]) hr hbad

noncomputable def totalPolynomial (k : Nat) : Polynomial Nat :=
  let b := Source284RestoredPolynomialRunway.countPolynomial k+1
  Source284DynamicGuardReveal.revealPolynomial k+18*b*b+84*b+12*Polynomial.X+134

/-- The raw initialization, dynamic guard, input-frame restoration,
witness compaction and joined-prefix handoff share one polynomial clock. -/
theorem total_polynomial (k : Nat) (input witness : List Bool) (certificate : Nat)
    (hdec : Source284TaggedWitnessCodec.decode (Source284DynamicGuardSource.bound k input.length)
      certificate = some witness) :
    Source284GapUnarySource.totalCost k input+
      Source284DynamicGuardReveal.revealCost (Source284DynamicGuardSource.bound k input.length) witness+
      Source284DynamicInputFrame.cost input+cost (Source284DynamicGuardSource.bound k input.length) input witness ≤
        (totalPolynomial k).eval input.length := by
  let limit := Source284DynamicGuardSource.bound k input.length
  let b := Source284PolynomialMarkedCleanup.count k input.length+1
  have hw : witness.length ≤ limit := Source284TaggedWitnessCodec.decode_length limit certificate witness hdec
  have hb : limit ≤ b := by
    dsimp [limit,b,Source284DynamicGuardSource.bound,Source284GapUnarySource.gap]
    exact Nat.div_le_self _ _
  have hwb : witness.length ≤ b := le_trans hw hb
  have hsquare := Nat.mul_self_le_mul_self hwb
  have hmul : (2*((limit+1)+1))*(8*witness.length+11) ≤ (2*(b+2))*(8*b+11) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hseek := Source284WitnessSeek.seek_time_bound limit witness
  have hreveal := Source284DynamicGuardReveal.reveal_polynomial k input witness certificate hdec
  rw [Source284DynamicInputFrame.cost_formula]
  simp only [totalPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,
    Polynomial.eval_one,Polynomial.eval_ofNat,Source284RestoredPolynomialRunway.countPolynomial_eval]
  unfold cost Source284WitnessCompact.extraCost
  rw [Source284ScratchPack.totalCost_formula]
  change Source284GapUnarySource.totalCost k input+
      Source284DynamicGuardReveal.revealCost limit witness+(10*input.length+36)+
      ((3+2*((limit+1)+1)+(if witness=[] then 4 else 2))+
        ((2+(2*witness.length*witness.length+18*witness.length+16))+
          ((2*witness.length+3)+((2*witness.length+5)+(2*((limit+1)+1))*(8*witness.length+11))))+
        (6*witness.length+11)+(2*input.length+6)) ≤ _
  dsimp [b] at hwb hsquare hmul hb
  nlinarith

end Shared.Beeping.NPcoNP.Source284DynamicJoinedInput
