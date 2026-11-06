import Shared.Beeping.NPcoNP.Source284DelimitedPolynomialRunway
import Shared.Beeping.NPcoNP.Source284SingleCertificateJoin
import Shared.Beeping.NPcoNP.Source284GenericJoinedFinishing

/-! A fixed source table prepares polynomial workspace, reads and packs the
entire valid tagged witness, and produces the joined input stream required by
the existing serializer. Invalid certificates and physical refinement remain
separate obligations. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284PolynomialJoinedInput

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (stack)
open Shared.Beeping.NPcoNP.Source284PositivePolynomialRunway (block)
open Shared.Beeping.NPcoNP.Source284PolynomialMarkedCleanup (count)

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284SingleCertificateJoin.table (Source284GenericJoinedFinishing.table continuation)

def description (k states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284DelimitedPolynomialRunway.description k (434+states) (table continuation)

def totalCost (k : Nat) (input witness : List Bool) : Nat :=
  Source284DelimitedPolynomialRunway.totalCost k input+
    Source284SingleCertificateJoin.cost (count k input.length) witness+
    Source284GenericJoinedFinishing.cost input witness

def inputTail (k n suffix : Nat) : Nat :=
  2^(block k n)*Source284DelimitedPolynomialRunway.retained k n suffix

def witnessTail (k n suffix : Nat) : Nat :=
  Source284SingleCertificateJoin.witnessTail (count k n) suffix

theorem witnessTail_half (k n suffix : Nat) :
    witnessTail k n suffix/2 = 2^(count k n+3)*(suffix/4) := by
  have he : Source284SingleCertificateJoin.witnessTail (count k n) suffix =
      2*(2^(count k n+3)*(suffix/4)) := by
    unfold Source284SingleCertificateJoin.witnessTail
    rw [show count k n+3=(count k n+2)+1 by omega,pow_succ]
    ring
  unfold witnessTail
  rw [he,Nat.mul_div_cancel_left _ (by decide : 0 < 2)]

theorem inputTail_zero (k n suffix depth : Nat) (hfit : depth ≤ block k n) :
    2^depth ∣ inputTail k n suffix := by
  unfold inputTail
  exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 hfit) _

theorem witnessTail_zero (k n suffix depth : Nat) (hfit : depth ≤ count k n+3) :
    2^depth ∣ witnessTail k n suffix/2 := by
  rw [witnessTail_half]
  exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 hfit) _

/-- Both tail demands may be arbitrary fixed polynomials; one stage count
is selected once and works for every input length and every high suffix. -/
theorem uniform_tail_bound (inputDemand witnessDemand : Polynomial Nat) :
    ∃ k : Nat, ∀ n inputSuffix witnessSuffix : Nat,
      2^(inputDemand.eval n) ∣ inputTail k n inputSuffix ∧
      2^(witnessDemand.eval n) ∣ witnessTail k n witnessSuffix/2 := by
  obtain ⟨k,hk⟩ := Source284PositivePolynomialRunway.block_dominates (inputDemand+witnessDemand)
  refine ⟨k,?_⟩
  intro n inputSuffix witnessSuffix
  have hb := hk n
  simp only [Polynomial.eval_add] at hb
  have hc : block k n ≤ count k n+3 := by
    simp only [count,Source284PolynomialRunwayCleanup.zeros]; omega
  exact ⟨inputTail_zero k n inputSuffix _ (by omega),
    witnessTail_zero k n witnessSuffix _ (by omega)⟩

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (434+states) (table continuation) := by
  have hf := Source284GenericJoinedFinishing.closed states continuation hn hv
  have hj := Source284SingleCertificateJoin.closed (247+states)
    (Source284GenericJoinedFinishing.table continuation) (by omega) hf
  simpa [table,show 187+(247+states)=434+states by omega] using hj

/-- The exact paid valid-certificate path reaches the same joined-bit
interface used by the guarded serializer, with explicit retained tails. -/
theorem source_then (k states : Nat) (continuation : Nat → Bool → Row)
    (input witness : List Bool) (inputSuffix witnessSuffix fuel : Nat)
    (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description k states continuation)
      (Source284Relative.initial (encodeFrame input inputSuffix) (4*encodeFrame witness witnessSuffix))
      (totalCost k input witness+fuel) =
    toSource (shiftConfig (1133+317*k) (run continuation
      ⟨8*inputTail k input.length inputSuffix,
        stack (Source284JoinedFrames.joinedBits input witness)
          (witnessTail k input.length witnessSuffix/2),some 0⟩ fuel)) := by
  have hc := closed states continuation hn hv
  have hp := Source284DelimitedPolynomialRunway.source_then k (434+states) (table continuation)
    input (4*encodeFrame witness witnessSuffix) inputSuffix
    (Source284SingleCertificateJoin.cost (count k input.length) witness+
      (Source284GenericJoinedFinishing.cost input witness+fuel)) (by omega) hc
  have ht : totalCost k input witness+fuel = Source284DelimitedPolynomialRunway.totalCost k input+
      (Source284SingleCertificateJoin.cost (count k input.length) witness+
        (Source284GenericJoinedFinishing.cost input witness+fuel)) := by simp [totalCost]; omega
  rw [ht]
  change Source284Relative.run (Source284DelimitedPolynomialRunway.description k (434+states)
    (table continuation)) _ _ = _
  rw [hp]
  unfold table
  change toSource (shiftConfig (699+317*k)
    (run (Source284SingleCertificateJoin.table (Source284GenericJoinedFinishing.table continuation))
      ⟨2^(count k input.length+1)*(2*(4*encodeFrame witness witnessSuffix)+1),
        2*flipped (input++[false]) (inputTail k input.length inputSuffix),some 0⟩ _)) = _
  rw [Source284SingleCertificateJoin.join_then (247+states)
    (Source284GenericJoinedFinishing.table continuation) (count k input.length)
    (flipped (input++[false]) (inputTail k input.length inputSuffix)) witnessSuffix witness
    (Source284GenericJoinedFinishing.cost input witness+fuel) (by omega)
    (Source284GenericJoinedFinishing.closed states continuation hn hv),
    Source284GenericJoinedFinishing.finish_then states continuation input witness
      (inputTail k input.length inputSuffix)
      (Source284SingleCertificateJoin.witnessTail (count k input.length) witnessSuffix) fuel hn hv]
  repeat rw [Source284SourceRelocation.shiftConfig_add]
  have hs : 699+317*k+187+247=1133+317*k := by omega
  rw [hs]
  rfl

theorem extraCost_formula (z : Nat) (input witness : List Bool) :
    Source284SingleCertificateJoin.cost z witness+Source284GenericJoinedFinishing.cost input witness =
      z+2*witness.length*witness.length+48*witness.length+12*input.length+131+
        (z+2)*(8*witness.length+11) := by
  simp [Source284SingleCertificateJoin.cost,Source284SingleCertificateSeek.seekCost,
    Source284WitnessCompact.extraCost,Source284ScratchPack.totalCost_formula,
    Source284ClearCompact.cost,Source284GenericJoinedFinishing.cost,Source284FramedJoin.finishingCost,
    Source284JoinedTripleAdapter.cost]
  ring

noncomputable def costPolynomial (k : Nat) (witnessBound : Polynomial Nat) : Polynomial Nat :=
  let z := Source284RestoredPolynomialRunway.countPolynomial k
  Source284DelimitedPolynomialRunway.costPolynomial k+
    (z+2*witnessBound*witnessBound+48*witnessBound+12*Polynomial.X+131+
      (z+2)*(8*witnessBound+11))

/-- A fixed polynomial bound on witness length yields a fixed polynomial
bound for initialization, witness packing, gap removal and joining. -/
theorem totalCost_polynomial (k : Nat) (witnessBound : Polynomial Nat)
    (input witness : List Bool) (hw : witness.length ≤ witnessBound.eval input.length) :
    totalCost k input witness ≤ (costPolynomial k witnessBound).eval input.length := by
  have hrun := Source284DelimitedPolynomialRunway.totalCost_polynomial k input
  have hsquare := Nat.mul_self_le_mul_self hw
  have hmul : (count k input.length+2)*(8*witness.length+11) ≤
      (count k input.length+2)*(8*witnessBound.eval input.length+11) := by
    apply Nat.mul_le_mul_left; omega
  unfold totalCost
  rw [Nat.add_assoc,extraCost_formula]
  simp only [costPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,
    Polynomial.eval_ofNat,Polynomial.eval_one,Source284RestoredPolynomialRunway.countPolynomial_eval]
  nlinarith

/-- Every witness accepted by the existing bounded tagged decoder follows
the actual finite join path, including all valid high-suffix aliases. -/
theorem decoded_then (k states limit certificate : Nat) (continuation : Nat → Bool → Row)
    (input witness : List Bool) (inputSuffix fuel : Nat)
    (hn : 0 < states) (hv : Closed states continuation)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some witness) :
    ∃ witnessSuffix,
      certificate = 4*encodeFrame witness witnessSuffix ∧
      Source284Relative.run (description k states continuation)
        (Source284Relative.initial (encodeFrame input inputSuffix) certificate)
        (totalCost k input witness+fuel) =
      toSource (shiftConfig (1133+317*k) (run continuation
        ⟨8*inputTail k input.length inputSuffix,
          stack (Source284JoinedFrames.joinedBits input witness)
            (witnessTail k input.length witnessSuffix/2),some 0⟩ fuel)) := by
  obtain ⟨suffix,hcert⟩ := Source284CertificateProbeSource.decoded_has_frame limit certificate witness hdec
  refine ⟨suffix,hcert,?_⟩
  rw [hcert]
  exact source_then k states continuation input witness inputSuffix suffix fuel hn hv

end Shared.Beeping.NPcoNP.Source284PolynomialJoinedInput
