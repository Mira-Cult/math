import Shared.Beeping.NPcoNP.Bootstrap284VariablePositiveRedispatch
import Shared.Beeping.NPcoNP.NativeShortCycleIteration

/-! Instantiate the finite local iteration on the actual blank-start run. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284ShortCycleIteration
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeShortCycleStage
open Shared.Beeping.NPcoNP.NativeShortCycleIteration
open Shared.Beeping.NPcoNP.Bootstrap284VariablePositiveRedispatch
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

/-- The real blank-start run reaches eight further silent stages. The final
layout retains 78 explicit blank bank cells; this is a finite reachability
result and does not assert a global graph simulation. -/
theorem blank_start_eight_short_stages :
    ∃ (n : Nat) (out : Int → Bool), 8≤n ∧
      ShortStage (-3820) 0 3813 0 (List.replicate 1898 0 ++ List.replicate 8 0)
        (List.replicate 78 false) out ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out) n := by
  obtain ⟨m,n,k,j,l,p,t,hm,hn,hk,hj,hl,hp,hwin,hleft0,hleft1,hray,hmark,hdelim,hbank,hcorr,hstop,hseg⟩ :=
    blank_start_variable_positive_redispatch
  have hpad : List.replicate 94 false = List.replicate (2*8) false ++ List.replicate 78 false := by
    rw [←List.replicate_add]
  have hstage : ShortStage (-3820) 8 3797 0 (List.replicate 1898 0)
      (List.replicate (2*8) false ++ List.replicate 78 false) t := by
    refine ⟨hwin,?_,hleft0,hleft1,?_,?_,?_,?_,?_⟩
    · exact hray
    · simpa [controlD] using hmark
    · simpa [controlD,controlStop] using hcorr
    · simpa [controlD,controlStop] using hstop
    · simpa [controlD,controlStop] using hdelim
    · rw [←hpad]
      change Holds t 5 ((Shared.Beeping.NPcoNP.UnaryBank.encode (0 :: List.replicate 1898 0) ++ [true,false,false]) ++ List.replicate 94 false)
      simpa only [show List.replicate 1899 0 = 0 :: List.replicate 1898 0 by rfl] using hbank
  obtain ⟨q,out,hq,hout,hnext⟩ :=
    short_stage_iterate 8 t (-3820) 8 3797 0 (List.replicate 1898 0)
      (List.replicate 78 false) (by decide) (by decide) hstage
  have hall := segAdd machine _ _ _ _ q hseg hnext
  refine ⟨_,out,by omega,?_,hall⟩
  simpa using hout

#print axioms blank_start_eight_short_stages
end Shared.Beeping.NPcoNP.Bootstrap284ShortCycleIteration
