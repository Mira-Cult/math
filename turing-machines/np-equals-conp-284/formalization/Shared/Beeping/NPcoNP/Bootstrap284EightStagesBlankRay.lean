import Shared.Beeping.NPcoNP.Bootstrap284VariablePositiveRedispatchBlankRays
import Shared.Beeping.NPcoNP.NativeShortIterationBlankRay
import Shared.Beeping.NPcoNP.Bootstrap284VariablePositiveRedispatch
import Shared.Beeping.NPcoNP.NativeShortCycleIteration

/-! Instantiate the finite local iteration on the actual blank-start run. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284EightStagesBlankRay
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeShortCycleStage
open Shared.Beeping.NPcoNP.NativeShortCycleIteration
open Shared.Beeping.NPcoNP.NativeShortIterationBlankRay
open Shared.Beeping.NPcoNP.NativeShortStageBlankRay
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeAllZeroUnitAbsent
open Shared.Beeping.NPcoNP.Bootstrap284VariablePositiveRedispatchBlankRays
open Shared.Beeping.NPcoNP.UnaryBank
open Shared.Beeping.NPcoNP.Bootstrap284VariablePositiveRedispatch
set_option autoImplicit false
set_option maxRecDepth 1024
set_option maxHeartbeats 16000000

theorem zero_word_prefix : zeroWord.take 18=markerWindow (List.replicate 8 0 ++ [0]) := by decide
attribute [local irreducible] markerWindow

theorem blank_start_eight_short_stages_with_ray :
    ∃ (n : Nat) (out : Int → Bool), 8≤n ∧
      ShortStage (-3820) 0 3813 0 (List.replicate 1898 0 ++ List.replicate 8 0)
        (List.replicate 78 false) out ∧
      ZeroRay (-3820) 0 3813 0 (List.replicate 1898 0 ++ List.replicate 8 0) out ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out) n := by
  obtain ⟨m,n,k,j,l,p,t,hm,hn,hk,hj,hl,hp,hprefix,_hunit,hleft1,hleft0,_h3,_h4,_h5,hray,hmark,hdelim,hbank,hcorr,hstop,hblank,hseg⟩ :=
    blank_start_variable_positive_redispatch_with_blank_rays
  have hpad : List.replicate 94 false = List.replicate (2*8) false ++ List.replicate 78 false := by
    rw [←List.replicate_add]
  have hstage : ShortStage (-3820) 8 3797 0 (List.replicate 1898 0)
      (List.replicate (2*8) false ++ List.replicate 78 false) t := by
    have hwin : Holds t (-3820) (markerWindow (List.replicate 8 0 ++ [0])) := by
      simpa only [zero_word_prefix] using hprefix
    refine ⟨hwin,?_,hleft0,hleft1,?_,?_,?_,?_,?_⟩
    · intro q hq; exact hray q (by omega)
    · simpa [controlD] using hmark
    · simpa [controlD,controlStop] using hcorr
    · simpa [controlD,controlStop] using hstop
    · simpa [controlD,controlStop] using hdelim
    · rw [←hpad]
      change Holds t 5 ((Shared.Beeping.NPcoNP.UnaryBank.encode (0 :: List.replicate 1898 0) ++ [true,false,false]) ++ List.replicate 94 false)
      simpa only [show List.replicate 1899 0 = 0 :: List.replicate 1898 0 by rfl] using hbank
  have hstageRay : ZeroRay (-3820) 8 3797 0 (List.replicate 1898 0) t := by
    change ∀ q, 5+((encode (0::List.replicate 1898 0)).length : Int)+1≤q → t q=false
    exact hblank
  obtain ⟨q,out,hq,hout,houtRay,hnext⟩ :=
    short_stage_iterate_with_ray 8 t (-3820) 8 3797 0 (List.replicate 1898 0)
      (List.replicate 78 false) (by decide) (by decide) hstage hstageRay
  have hall := segAdd machine _ _ _ _ q hseg hnext
  refine ⟨_,out,by omega,?_,?_,hall⟩
  · change ShortStage (-3820) 0 3813 0 (List.replicate 1898 0 ++ List.replicate 8 0) (List.replicate 78 false) out at hout
    exact hout
  · change ZeroRay (-3820) 0 3813 0 (List.replicate 1898 0 ++ List.replicate 8 0) out at houtRay
    exact houtRay


#print axioms blank_start_eight_short_stages_with_ray
end Shared.Beeping.NPcoNP.Bootstrap284EightStagesBlankRay
