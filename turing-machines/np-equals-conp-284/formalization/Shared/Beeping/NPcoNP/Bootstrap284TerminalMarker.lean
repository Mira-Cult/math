import Shared.Beeping.NPcoNP.Bootstrap284LastShortPositive
import Shared.Beeping.NPcoNP.NativeShortCycleTerminal

/-! The blank-start run reaches the marker-at-head boundary silently. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284TerminalMarker
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeShortCycleStage
open Shared.Beeping.NPcoNP.NativeShortCycleTerminal
open Shared.Beeping.NPcoNP.Bootstrap284LastShortPositive
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

theorem blank_start_terminal_marker :
    ∃ (n : Nat) (out : Int → Bool), 0<n ∧
      out (-3822)=false ∧ out (-3821)=true ∧ (∀ q, q< -3822 → out q=false) ∧
      out (-3820)=true ∧ (∀ q, -3820<q → q<3 → out q=false) ∧
      out 3=true ∧ out 4=false ∧
      Holds out 5 ((encode (0::((List.replicate 1898 0 ++ List.replicate 8 0) ++ [0])) ++
        [true,false,false]) ++ List.replicate 76 false) ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out) n := by
  obtain ⟨n,t,hn,ht,hfirst⟩ := blank_start_last_short_positive
  obtain ⟨m,out,hm,hleft0,hleft1,hray,hmark,hcorr,hstop,hdelim,hbank,hsecond⟩ :=
    short_positive_terminal t (-3820) 3813 0
      ((List.replicate 1898 0 ++ List.replicate 8 0) ++ [0]) (List.replicate 76 false) ht
  have hall := segAdd machine _ _ _ n m hfirst hsecond
  refine ⟨n+m,out,by omega,hleft0,hleft1,hray,hmark,?_,?_,?_,?_,hall⟩
  · simpa [controlStop,controlD] using hcorr
  · simpa [controlStop,controlD] using hstop
  · simpa [controlStop,controlD] using hdelim
  · simpa [controlBank,controlD] using hbank

#print axioms blank_start_terminal_marker
end Shared.Beeping.NPcoNP.Bootstrap284TerminalMarker
