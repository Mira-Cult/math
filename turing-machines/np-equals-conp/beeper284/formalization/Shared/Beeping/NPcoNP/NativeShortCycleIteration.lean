import Shared.Beeping.NPcoNP.NativeShortCycleStage

/-! Finite iteration of the explicitly supplied local stage. -/
namespace Shared.Beeping.NPcoNP.NativeShortCycleIteration
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeShortCycleStage
set_option autoImplicit false
set_option maxHeartbeats 12000000

theorem short_stage_iterate (depth : Nat) (t : Int → Bool) (a : Int) (k s v : Nat)
    (rest : List Nat) (pad : List Bool) (hd : depth≤k) (hk : k≤10)
    (stage : ShortStage a k s v rest (List.replicate (2*depth) false ++ pad) t) :
    ∃ (n : Nat) (out : Int → Bool), depth≤n ∧
      ShortStage a (k-depth) (s+2*depth) v (rest ++ List.replicate depth 0) pad out ∧
      silentSegment machine (cfg 93 a t) (cfg 93 a out) n := by
  induction depth generalizing t k s rest with
  | zero =>
      refine ⟨0,t,by omega,?_,?_⟩
      · simpa using stage
      · simp [silentSegment, W, WordEventSystem.advance, WordEventSystem.wordFrom]
  | succ depth ih =>
      have hpad : List.replicate (2*(depth+1)) false ++ pad =
          [false,false] ++ (List.replicate (2*depth) false ++ pad) := by
        have hh : 2*(depth+1)=2+2*depth := by omega
        simp [hh,List.replicate_add,List.append_assoc]
      have hstage : ShortStage a k s v rest
          ([false,false] ++ (List.replicate (2*depth) false ++ pad)) t := by
        simpa only [hpad] using stage
      obtain ⟨n,mid,hn,hmid,hfirst⟩ :=
        short_stage_step t a k s v rest (List.replicate (2*depth) false ++ pad)
          (by omega) hk hstage
      obtain ⟨m,out,hm,hout,hsecond⟩ :=
        ih mid (k-1) (s+2) (rest ++ [0]) (by omega) (by omega) hmid
      refine ⟨n+m,out,by omega,?_,segAdd machine _ _ _ n m hfirst hsecond⟩
      have hsub : k-1-depth=k-(depth+1) := by omega
      have hadd : s+2+2*depth=s+2*(depth+1) := by omega
      have hrest : (rest ++ [0]) ++ List.replicate depth 0 =
          rest ++ List.replicate (depth+1) 0 := by
        simp [List.replicate_succ, List.append_assoc]
      simpa only [hsub,hadd,hrest] using hout

#print axioms short_stage_iterate
end Shared.Beeping.NPcoNP.NativeShortCycleIteration
