import Shared.Beeping.NPcoNP.Source284CertificateProbeLayout
import Shared.Beeping.NPcoNP.Source284OffsetDecodedHandoff

/-! Raw-input initialization followed by a paid marker-controlled probe of
the actual tagged certificate. The bit is handed to a finite continuation;
full witness copying and general verifier compilation remain separate. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284CertificateProbeSource

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284TwoSidedScaledQuadraticWindow (leftData rightData)
open Shared.Beeping.NPcoNP.Source284CertificateProbeRun (body mode cost)
open Shared.Beeping.NPcoNP.Source284CertificateProbeLayout (firstZeros secondZeros)

def description (k states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284TwoSidedScaledQuadratic.description k (18+states) (Source284CertificateProbe.table continuation)

def totalCost (k : Nat) (w : List Bool) : Nat :=
  Source284TwoSidedScaledQuadratic.totalCost k w+cost (firstZeros k w.length) (secondZeros w.length)

/-- Actual execution after raw initialization, with both tape halves exactly
restored and the first certificate-frame marker handed to the continuation. -/
theorem source_probe_then (k states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (frame suffix fuel : Nat) (hn : 2 ≤ states) (hv : Closed states continuation) :
    Source284Relative.run (description k states continuation)
      (Source284Relative.initial (Source284Parser.encodeFrame w suffix) (4*frame)) (totalCost k w+fuel) =
    toSource (shiftConfig (858+220*k) (run continuation
      ⟨leftData k w (4*frame),rightData k w suffix,some (mode frame)⟩ fuel)) := by
  have hc := Source284CertificateProbe.closed states continuation hn hv
  have hp := Source284TwoSidedScaledQuadratic.source_then k (18+states)
    (Source284CertificateProbe.table continuation) w (4*frame) suffix
    (cost (firstZeros k w.length) (secondZeros w.length)+fuel) (by omega) hc
  have ht : totalCost k w+fuel = Source284TwoSidedScaledQuadratic.totalCost k w+
      (cost (firstZeros k w.length) (secondZeros w.length)+fuel) := by simp [totalCost]; omega
  rw [ht]
  change Source284Relative.run (Source284TwoSidedScaledQuadratic.description k (18+states)
    (Source284CertificateProbe.table continuation))
    (Source284Relative.initial (Source284Parser.encodeFrame w suffix) (4*frame)) _ = _
  rw [hp]
  change toSource (shiftConfig (840+220*k) (run (Source284CertificateProbe.table continuation)
    ⟨leftData k w (4*frame),rightData k w suffix,some 0⟩ _)) = _
  rw [Source284CertificateProbeLayout.leftData_eq_body]
  unfold rightData
  rw [Source284CertificateProbeRun.probe_then,Source284SourceRelocation.shiftConfig_add]
  have he : 840+220*k+18=858+220*k := by omega
  rw [he]

/-- A certificate decoded within the original cutoff is exactly some tagged
frame for that witness, including arbitrary ignored high suffix bits. -/
theorem decoded_has_frame (limit certificate : Nat) (w : List Bool)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some w) :
    ∃ suffix, certificate=4*Source284Parser.encodeFrame w suffix := by
  have htag : certificate%4 = 0 := by
    by_contra h
    simp [Source284TaggedWitnessCodec.decode,h] at hdec
  obtain ⟨v,suffix,hframe⟩ := Source284Parser.encodeFrame_surjective (certificate/4)
  have hcert : certificate = 4*Source284Parser.encodeFrame v suffix := by rw [hframe]; omega
  have hvalid : Source284TaggedWitnessCodec.decode limit (4*Source284Parser.encodeFrame v suffix) ≠ none := by
    rw [← hcert,hdec]
    simp
  have hvlen : v.length ≤ limit := by
    by_contra h
    apply hvalid
    exact (Source284PreparedCutoff.tagged_decode_none_iff limit v suffix).mpr (by omega)
  have hd := Source284OffsetDecodedHandoff.tagged_decode_frame limit v suffix hvlen
  rw [← hcert,hdec] at hd
  have heq : w=v := Option.some.inj hd
  subst v
  exact ⟨suffix,hcert⟩

/-- The probe reaches the same continuation mode for every high-suffix alias
of a valid bounded witness. This is a nonempty-witness test, not a full
witness decoder or a general verifier. -/
theorem decoded_probe_then (k states limit certificate : Nat) (continuation : Nat → Bool → Row)
    (input witness : List Bool) (inputSuffix fuel : Nat)
    (hn : 2 ≤ states) (hv : Closed states continuation)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some witness) :
    ∃ witnessSuffix,
      certificate=4*Source284Parser.encodeFrame witness witnessSuffix ∧
      Source284Relative.run (description k states continuation)
        (Source284Relative.initial (Source284Parser.encodeFrame input inputSuffix) certificate)
        (totalCost k input+fuel) =
      toSource (shiftConfig (858+220*k) (run continuation
        ⟨leftData k input certificate,rightData k input inputSuffix,
          some (if witness=[] then 0 else 1)⟩ fuel)) := by
  obtain ⟨suffix,hcert⟩ := decoded_has_frame limit certificate witness hdec
  refine ⟨suffix,hcert,?_⟩
  rw [hcert]
  have h := source_probe_then k states continuation input (Source284Parser.encodeFrame witness suffix)
    inputSuffix fuel hn hv
  rw [Source284CertificateProbeLayout.mode_frame] at h
  exact h

theorem probeCost_formula (k n : Nat) : cost (firstZeros k n) (secondZeros n) =
    2*k*(n*n)+16*n+26 := Source284CertificateProbeLayout.cost_formula k n

end Shared.Beeping.NPcoNP.Source284CertificateProbeSource
