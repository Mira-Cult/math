import Shared.Beeping.NPcoNP.Bootstrap284ReachableRecurrence
import Shared.Beeping.NPcoNP.NativePostAbsenceUnitScan

/-! Connect the post-absence unit scan to the literal blank-start run.
The result remains a finite prefix, not a graph/table simulation. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284PostAbsenceUnitScan
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativePostAbsenceUnitScan
open Shared.Beeping.NPcoNP.Bootstrap284ReachableRecurrence
open Shared.Beeping.NPcoNP.UnaryBank

set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

/-- The actual post-absence state completes the state-261 round trip in
7,648 silent transitions, retaining the bank and exposing the next selector. -/
theorem blank_start_post_absence_unit_roundtrip :
    ∃ (m n k : Nat) (out : Int → Bool), 0<m ∧ 1891≤n ∧ 0<k ∧
      Holds out (-3820) (markerWindow (List.replicate 11 0 ++ [1,0,3793])) ∧
      Holds out 5 (encode (List.replicate 1897 0) ++ List.replicate 101 false) ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out)
        (2134479+m+29+n+(k+31)+7648) := by
  obtain ⟨m,n,k,t,hm,hn,hk,hbank,hpre,hleft,_h2,_h3,_h4,hmark,hcorr,hstop,_hdelim,hseg⟩ :=
    blank_start_after_marker_absence_with_control
  let out := scanOutput (-3820) 3789 t
  have hround := post_absence_roundtrip (-3820) 3789 t hpre (by simpa using hleft)
    (by simpa using hmark) (by simpa using hcorr) (by simpa using hstop)
  obtain ⟨hnext,hwindow,hframe⟩ := hround
  have hnext' : silentSegment machine (cfg 93 (-3820) t) (cfg 93 (-3820) out) 7648 := by
    simpa [out] using hnext
  have hbank' : Holds out 5 (encode (List.replicate 1897 0) ++ List.replicate 101 false) := by
    apply holds_transport t out _ _ hbank
    intro q hq _
    symm
    apply hframe q
    right
    omega
  have hall := segAdd machine _ _ _ (2134479+m+29+n+(k+31)) 7648 hseg hnext'
  exact ⟨m,n,k,out,hm,hn,hk,by simpa [out] using hwindow,hbank',hall⟩

#print axioms blank_start_post_absence_unit_roundtrip
end Shared.Beeping.NPcoNP.Bootstrap284PostAbsenceUnitScan
