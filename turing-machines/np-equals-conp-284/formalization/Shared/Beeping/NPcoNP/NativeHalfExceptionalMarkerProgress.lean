import Shared.Beeping.NPcoNP.NativeHalfMarkerRetain
import Shared.Beeping.NPcoNP.NativeHalfCleanupMarker

/-! Prepared exceptional HALF cleanup followed by marker-preserving return.
The protected base is assumed to have a left-zero tail. This theorem does
not establish that the actual blank-start execution reaches the prepared
configuration, nor that state 28 completes the HALF routine. -/

namespace Shared.Beeping.NPcoNP.NativeHalfExceptionalMarkerProgress

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfCycleTape
open Shared.Beeping.NPcoNP.NativeHalfCleanupComposed
open Shared.Beeping.NPcoNP.NativeHalfCleanupPrefix
open Shared.Beeping.NPcoNP.NativeHalfCleanupMarker
open Shared.Beeping.NPcoNP.NativeHalfMarkerRetain

/-- The exceptional path creates its own rightward marker. A finite left
zero tail of the protected base suffices for the subsequent 23/1/27 scans,
so the literal table reaches state 28 in positive finite silent time. -/
theorem exceptional_to_28 (base : Int → Bool) (b : Int) (values : List Nat)
    (hb : base b = true) (hleft : ∃ z : Int, ∀ q ≤ z, base q = false) :
    ∃ (duration : Nat) (e : Config 284), 0 < duration ∧ e.state = 28 ∧
      silentSegment machine
        (cfg 30 b (prior base b (false :: UnaryBank.encode values))) e duration := by
  obtain ⟨z, hz⟩ := hleft
  let k : Nat := (b - min z b).toNat
  have hk : b - (k : Int) ≤ z := by
    have hn : 0 ≤ b - min z b := by omega
    have he : (k : Int) = b - min z b := Int.toNat_of_nonneg hn
    omega
  have htail : ∀ q ≤ b - (k : Int), postTape base b values q = false := by
    intro q hq
    have hqb : q ≤ b := by omega
    rw [postTape_prefix base b q values hqb]
    exact hz q (le_trans hq hk)
  obtain ⟨p, hp, hm⟩ := postTape_marker_right base b values
  obtain ⟨n, hn, hclean⟩ := exceptional_through_cleanup base b values hb
  have hclean' : silentSegment machine
      (cfg 30 b (prior base b (false :: UnaryBank.encode values)))
      (cfg 23 b (postTape base b values)) n := by
    simpa [postTape] using hclean
  obtain ⟨m, e, hmpos, he, hret⟩ :=
    marker_to_28 k b p (postTape base b values) htail (by omega) hm
  exact ⟨n+m, e, by omega, he, segAdd machine _ _ _ n m hclean' hret⟩

end Shared.Beeping.NPcoNP.NativeHalfExceptionalMarkerProgress
