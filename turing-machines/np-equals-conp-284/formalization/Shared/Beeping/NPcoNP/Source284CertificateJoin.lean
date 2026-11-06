import Shared.Beeping.NPcoNP.Source284CertificateCompactCoverage
import Shared.Beeping.NPcoNP.Source284ClearCompact

/-! Finish removing the loader's internal boundary sentinels. The fixed
finite source table joins the complete framed input and witness streams at
the head, without consulting the mathematical gap lengths as runtime data. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284CertificateJoin

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284CertificateProbeLayout (firstZeros)
open Shared.Beeping.NPcoNP.Source284CertificatePackSource (stream)
open Shared.Beeping.NPcoNP.Source284CertificateCompact (innerInput)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)

def finishing (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284ClearCompact.table (Source284ClearCompact.table (Source284SentinelClear.table continuation))

theorem finishing_closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (40+states) (finishing continuation) := by
  have h0 := Source284SentinelClear.closed states continuation hn hv
  have h1 := Source284ClearCompact.closed (4+states) (Source284SentinelClear.table continuation) (by omega) h0
  have h2 := Source284ClearCompact.closed (18+(4+states))
    (Source284ClearCompact.table (Source284SentinelClear.table continuation)) (by omega) h1
  change Closed (18+(18+(4+states))) (finishing continuation) at h2
  convert h2 using 1 <;> omega

def finishCost (z n : Nat) (w : List Bool) :=
  Source284ClearCompact.cost (2*n+1) w+Source284ClearCompact.cost z w+4

def witnessTail (z n suffix : Nat) := 2^(z+1)*(2^(2*n+2)*(4*(suffix/4)))

/-- Starting at the first sentinel, cross both zero gaps and clear the final
marker, retaining the complete input and witness streams. -/
theorem finish_then (continuation : Nat → Bool → Row) (z n input suffix : Nat)
    (w : List Bool) (fuel : Nat) :
    run (finishing continuation)
      ⟨4*innerInput z n input+1,2*flipped w (4*(suffix/4)),some 0⟩
      (finishCost z n w+fuel) =
    shiftConfig 40 (run continuation
      ⟨2*input,2*flipped w (witnessTail z n suffix),some 0⟩ fuel) := by
  have hl : 4*innerInput z n input+1 =
      2^((2*n+1)+1)*(2*(2^z*(2*input+1))+1)+1 := by
    unfold innerInput
    have he : (2*n+1)+1=2*n+2 := by omega
    rw [he,pow_add]
    ring
  have ht : finishCost z n w+fuel = Source284ClearCompact.cost (2*n+1) w+
      (Source284ClearCompact.cost z w+(4+fuel)) := by simp [finishCost]; omega
  rw [hl,ht]
  unfold finishing
  rw [Source284ClearCompact.cross_then]
  have hnext : 2*(2^z*(2*input+1))+1 = 2^(z+1)*(2*input+1)+1 := by
    rw [pow_succ]; ring
  rw [hnext,Source284ClearCompact.cross_then]
  have hexp : 2*n+1+1=2*n+2 := by omega
  rw [hexp]
  change shiftConfig 18 (shiftConfig 18 (run (Source284SentinelClear.table continuation)
    ⟨2*input+1,2*flipped w (witnessTail z n suffix),some 0⟩ (4+fuel))) = _
  rw [Source284SentinelClear.clear_then]
  repeat rw [Source284SourceRelocation.shiftConfig_add]

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284CertificateCompact.table (finishing continuation)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (205+states) (table continuation) := by
  have h := Source284CertificateCompact.closed (40+states) (finishing continuation)
    (by omega) (finishing_closed states continuation hn hv)
  change Closed (165+(40+states)) (table continuation) at h
  convert h using 1 <;> omega

def description (k states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284TwoSidedScaledQuadratic.description k (205+states) (table continuation)

def totalCost (k : Nat) (input witness : List Bool) : Nat :=
  Source284CertificateCompact.totalCost k input witness+finishCost (firstZeros k input.length) input.length witness

/-- On a framed valid certificate, the source program reaches two adjacent
self-delimiting data streams and then follows every continuation step. -/
theorem source_join_then (k states : Nat) (continuation : Nat → Bool → Row)
    (input witness : List Bool) (witnessSuffix inputSuffix fuel : Nat)
    (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description k states continuation)
      (Source284Relative.initial (encodeFrame input inputSuffix) (4*encodeFrame witness witnessSuffix))
      (totalCost k input witness+fuel) =
    toSource (shiftConfig (1045+220*k) (run continuation
      ⟨2*stream k input inputSuffix,
        2*flipped witness (witnessTail (firstZeros k input.length) input.length witnessSuffix),some 0⟩ fuel)) := by
  have hp := Source284CertificateCompact.source_compact_then k (40+states) (finishing continuation)
    input witness witnessSuffix inputSuffix (finishCost (firstZeros k input.length) input.length witness+fuel)
    (by omega) (finishing_closed states continuation hn hv)
  have hd : description k states continuation =
      Source284CertificateCompact.description k (40+states) (finishing continuation) := by
    unfold description table Source284CertificateCompact.description
    congr 1 <;> omega
  have ht : totalCost k input witness+fuel = Source284CertificateCompact.totalCost k input witness+
      (finishCost (firstZeros k input.length) input.length witness+fuel) := by simp [totalCost]; omega
  rw [hd,ht,hp,finish_then,Source284SourceRelocation.shiftConfig_add]
  have he : 1005+220*k+40=1045+220*k := by omega
  rw [he]

theorem decoded_join_then (k states limit certificate : Nat) (continuation : Nat → Bool → Row)
    (input witness : List Bool) (inputSuffix fuel : Nat)
    (hn : 0 < states) (hv : Closed states continuation)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some witness) :
    ∃ witnessSuffix,
      certificate=4*encodeFrame witness witnessSuffix ∧
      Source284Relative.run (description k states continuation)
        (Source284Relative.initial (encodeFrame input inputSuffix) certificate)
        (totalCost k input witness+fuel) =
      toSource (shiftConfig (1045+220*k) (run continuation
        ⟨2*stream k input inputSuffix,
          2*flipped witness (witnessTail (firstZeros k input.length) input.length witnessSuffix),some 0⟩ fuel)) := by
  obtain ⟨suffix,hcert⟩ := Source284CertificateProbeSource.decoded_has_frame limit certificate witness hdec
  refine ⟨suffix,hcert,?_⟩
  rw [hcert]
  exact source_join_then k states continuation input witness suffix inputSuffix fuel hn hv

end Shared.Beeping.NPcoNP.Source284CertificateJoin
