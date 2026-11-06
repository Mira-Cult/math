import Shared.Beeping.NPcoNP.Bootstrap284ShortCycleIteration

/-! One further finite transition at the zero-leading-block boundary. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284LastShortPositive
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeShortCycleStage
open Shared.Beeping.NPcoNP.Bootstrap284ShortCycleIteration
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

theorem blank_start_last_short_positive :
    ∃ (n : Nat) (out : Int → Bool), 0<n ∧
      ShortPositiveStage (-3820) 0 3813 0
        ((List.replicate 1898 0 ++ List.replicate 8 0) ++ [0])
        (List.replicate 76 false) out ∧
      silentSegment machine (machine.system.run 0) (cfg 93 (-3820) out) n := by
  obtain ⟨n,t,hn,ht,hfirst⟩ := blank_start_eight_short_stages
  have hpad : List.replicate 78 false=[false,false] ++ List.replicate 76 false := by
    change List.replicate 78 false = List.replicate 2 false ++ List.replicate 76 false
    rw [←List.replicate_add]
  have ht' : ShortStage (-3820) 0 3813 0
      (List.replicate 1898 0 ++ List.replicate 8 0)
      ([false,false] ++ List.replicate 76 false) t := by
    simpa only [hpad] using ht
  obtain ⟨m,e,hm,_,hpos,hsecond⟩ := short_stage_to_positive t (-3820) 0 3813 0
    (List.replicate 1898 0 ++ List.replicate 8 0) (List.replicate 76 false) (by decide) ht'
  exact ⟨n+m,_,by omega,hpos,segAdd machine _ _ _ n m hfirst hsecond⟩

#print axioms blank_start_last_short_positive
end Shared.Beeping.NPcoNP.Bootstrap284LastShortPositive
