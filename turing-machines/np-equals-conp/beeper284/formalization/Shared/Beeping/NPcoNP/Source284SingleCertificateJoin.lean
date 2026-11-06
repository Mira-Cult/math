import Shared.Beeping.NPcoNP.Source284SingleCertificateSeek
import Shared.Beeping.NPcoNP.Source284CertificateCompact
import Shared.Beeping.NPcoNP.Source284ClearCompact

/-! Cross the single paid delimiter, pack the complete tagged witness,
remove the gap, and hand off adjacent protected input and witness streams.
The certificate must be a valid tagged frame; rejection of malformed frames
is a separate obligation. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284SingleCertificateJoin

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)

def finishing (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284ClearCompact.table (Source284SentinelClear.table continuation)

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284SingleCertificateSeek.table (Source284WitnessCompact.table (finishing continuation))

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (187+states) (table continuation) := by
  have hs := Source284SentinelClear.closed states continuation hn hv
  have hc := Source284ClearCompact.closed (4+states) (Source284SentinelClear.table continuation) (by omega) hs
  have hw := Source284WitnessCompact.closed (18+(4+states)) (finishing continuation) (by omega) hc
  have ht := Source284SingleCertificateSeek.closed (160+(18+(4+states)))
    (Source284WitnessCompact.table (finishing continuation)) (by omega) hw
  simpa [table,show 5+(160+(18+(4+states)))=187+states by omega] using ht

def cost (z : Nat) (w : List Bool) : Nat :=
  Source284SingleCertificateSeek.seekCost (z+1)+Source284WitnessCompact.extraCost 0 w.length+
    Source284ClearCompact.cost (z+1) w+4

def witnessTail (z suffix : Nat) : Nat := 2^(z+2)*(4*(suffix/4))

theorem inputSide_shape (z stream : Nat) :
    Source284SingleCertificateSeek.inputSide (z+1) stream =
      4^(0+1)*(4*(2^z*(2*stream+1))+1) := by
  simp [Source284SingleCertificateSeek.inputSide,pow_succ]
  ring

/-- The part after the tag seek is reusable when a checked seek has already
dispatched to this valid-frame entry. -/
theorem after_seek_then (states : Nat) (continuation : Nat → Bool → Row)
    (z stream suffix : Nat) (w : List Bool) (fuel : Nat)
    (hn : 0 < states) (hv : Closed states continuation) :
    run (Source284WitnessCompact.table (finishing continuation))
      ⟨Source284SingleCertificateSeek.inputSide (z+1) stream,encodeFrame w suffix,some 0⟩
      (Source284WitnessCompact.extraCost 0 w.length+Source284ClearCompact.cost (z+1) w+4+fuel) =
    shiftConfig 182 (run continuation
      ⟨2*stream,2*flipped w (witnessTail z suffix),some 0⟩ fuel) := by
  have hs := Source284SentinelClear.closed states continuation hn hv
  have hc := Source284ClearCompact.closed (4+states) (Source284SentinelClear.table continuation) (by omega) hs
  have ht : Source284WitnessCompact.extraCost 0 w.length+Source284ClearCompact.cost (z+1) w+4+fuel =
      Source284WitnessCompact.extraCost 0 w.length+(Source284ClearCompact.cost (z+1) w+(4+fuel)) := by omega
  rw [ht,inputSide_shape,
    Source284CertificateCompact.compact_after_seek_zero (18+(4+states)) (finishing continuation)
      0 (2^z*(2*stream+1)) suffix w _ (by omega) hc]
  have hl : 4*(2^z*(2*stream+1))+1 = 2^((z+1)+1)*(2*stream+1)+1 := by
    rw [show (z+1)+1=z+2 by omega,pow_add]; norm_num; ring
  rw [hl]
  unfold finishing
  rw [Source284ClearCompact.cross_then,Source284SentinelClear.clear_then]
  repeat rw [Source284SourceRelocation.shiftConfig_add]
  have hq : 160+18+4=182 := by omega
  rw [hq]
  simp [witnessTail]

/-- A complete witness frame is packed and placed adjacent to the input.
All loops stop on actual delimiters, not on a runtime-supplied gap length. -/
theorem join_then (states : Nat) (continuation : Nat → Bool → Row)
    (z stream suffix : Nat) (w : List Bool) (fuel : Nat)
    (hn : 0 < states) (hv : Closed states continuation) :
    run (table continuation) ⟨2^(z+1)*(2*(4*encodeFrame w suffix)+1),2*stream,some 0⟩
      (cost z w+fuel) =
    shiftConfig 187 (run continuation
      ⟨2*stream,2*flipped w (witnessTail z suffix),some 0⟩ fuel) := by
  have hs := Source284SentinelClear.closed states continuation hn hv
  have hc := Source284ClearCompact.closed (4+states) (Source284SentinelClear.table continuation) (by omega) hs
  have ht : cost z w+fuel = Source284SingleCertificateSeek.seekCost (z+1)+
      (Source284WitnessCompact.extraCost 0 w.length+(Source284ClearCompact.cost (z+1) w+(4+fuel))) := by
    simp [cost]; omega
  rw [ht]
  unfold table
  rw [Source284SingleCertificateSeek.seek_then,inputSide_shape,
    Source284CertificateCompact.compact_after_seek_zero (18+(4+states)) (finishing continuation)
      0 (2^z*(2*stream+1)) suffix w _ (by omega) hc]
  have hl : 4*(2^z*(2*stream+1))+1 = 2^((z+1)+1)*(2*stream+1)+1 := by
    rw [show (z+1)+1=z+2 by omega,pow_add]; norm_num; ring
  rw [hl]
  unfold finishing
  rw [Source284ClearCompact.cross_then,Source284SentinelClear.clear_then]
  repeat rw [Source284SourceRelocation.shiftConfig_add]
  have hq : 5+160+18+4=187 := by omega
  rw [hq]
  simp [witnessTail]

namespace Fixtures
def loop (_ : Nat) (b : Bool) : Row := ⟨b,false,some 0⟩
example : run (table loop) ⟨2,0,some 0⟩ 83 = ⟨0,0,some 187⟩ := by decide +kernel
example : run (table loop) ⟨50,0,some 0⟩ 139 = ⟨0,6,some 187⟩ := by decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284SingleCertificateJoin
