import Shared.Beeping.NPcoNP.Bootstrap284LastPositiveBlankRay
import Shared.Beeping.NPcoNP.NativeShortTerminalBlankRay
import Shared.Beeping.NPcoNP.Bootstrap284LastShortPositive
import Shared.Beeping.NPcoNP.NativeShortCycleTerminal

/-! The blank-start run reaches the marker-at-head boundary silently. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284TerminalMarkerBlankRay
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeShortCycleStage
open Shared.Beeping.NPcoNP.NativeShortCycleTerminal
open Shared.Beeping.NPcoNP.Bootstrap284LastShortPositive
open Shared.Beeping.NPcoNP.Bootstrap284LastPositiveBlankRay
open Shared.Beeping.NPcoNP.NativeShortTerminalBlankRay
open Shared.Beeping.NPcoNP.NativeShortStageBlankRay
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 1024
set_option maxHeartbeats 16000000

theorem blank_start_terminal_marker_with_ray :
    ∃ (n : Nat) (out : Int → Bool), 0<n ∧
      out (-3822)=false ∧ out (-3821)=true ∧ (∀ q, q< -3822 → out q=false) ∧
      out (-3820)=true ∧ (∀ q, -3820<q → q<3 → out q=false) ∧
      out 3=true ∧ out 4=false ∧
      Holds out 5 ((encode (0::((List.replicate 1898 0 ++ List.replicate 8 0) ++ [0])) ++
        [true,false,false]) ++ List.replicate 76 false) ∧
      ZeroRay (-3820) 0 3813 0
        ((List.replicate 1898 0 ++ List.replicate 8 0) ++ [0]) out ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out) n := by
  obtain ⟨n,t,hn,ht,hray,hfirst⟩ := blank_start_last_short_positive_with_ray
  obtain ⟨m,out,hm,hleft0,hleft1,hray,hmark,hcorr,hstop,hdelim,hbank,houtRay,hsecond⟩ :=
    short_positive_terminal_with_ray t (-3820) 3813 0
      ((List.replicate 1898 0 ++ List.replicate 8 0) ++ [0]) (List.replicate 76 false) ht hray
  have hall := segAdd machine _ _ _ n m hfirst hsecond
  refine ⟨n+m,out,by omega,hleft0,hleft1,hray,hmark,?_,?_,?_,?_,houtRay,hall⟩
  · simpa [controlStop,controlD] using hcorr
  · simpa [controlStop,controlD] using hstop
  · simpa [controlStop,controlD] using hdelim
  · change Holds out 5 ((encode (0::((List.replicate 1898 0 ++ List.replicate 8 0) ++ [0])) ++
        [true,false,false]) ++ List.replicate 76 false) at hbank
    exact hbank


#print axioms blank_start_terminal_marker_with_ray
end Shared.Beeping.NPcoNP.Bootstrap284TerminalMarkerBlankRay
