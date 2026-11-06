import Shared.Beeping.NPcoNP.NativeHalfOddResidual
import Shared.Beeping.NPcoNP.NativeHalfOddCleanupComposed
import Shared.Beeping.NPcoNP.NativeHalfLoopLayout

/-! The odd residual's three writes produce exactly the prepared tape used
by its forward and backward cleanup. -/
namespace Shared.Beeping.NPcoNP.NativeHalfOddCleanupLayout

open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfLoopLayout
open Shared.Beeping.NPcoNP.UnarySuffixShift

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- Identity on the entire two-sided tape, including the arbitrary left
prefix and the appended reserve to the right. -/
theorem odd_writes (base : Int → Bool) (g : Int) (s : List Bool) :
    put (put (put (after base g (true :: false :: s)) g true) (g+1) false) (g+2) false =
      after (put base g true) (g+1) (false :: s) := by
  funext p
  by_cases hp : p<g
  · simp [put,after,hp,show p≠g by omega,show p≠g+1 by omega,
      show p≠g+2 by omega,show p<g+1 by omega]
  by_cases h0 : p=g
  · subst p
    simp [put,after,show g≠g+1 by omega,show g≠g+2 by omega]
  by_cases h1 : p=g+1
  · subst p
    simp [put,after,show g+1≠g+2 by omega]
  by_cases h2 : p=g+2
  · subst p
    simp [put,after,bitAt,show g+2≠g+1 by omega] <;> omega
  have hge : g+3≤p := by omega
  have hn : ¬p<g+1 := by omega
  have he1 : p≠g+1 := by omega
  have he2 : p≠g+2 := by omega
  have hidx : (p-g-1).toNat = (p-g-3).toNat+2 := by omega
  have hidx' : (p-(g+1)-1).toNat = (p-g-3).toNat+1 := by omega
  have hbound : p<g+1+((true :: false :: s).length : Int) ↔
      p<(g+1)+1+((false :: s).length : Int) := by simp; omega
  have heq : p=g+1+((true :: false :: s).length : Int) ↔
      p=(g+1)+1+((false :: s).length : Int) := by simp; omega
  simp only [put,he1,he2,h0,if_false,after,hp,hn]
  simp only [if_false,hbound,heq]
  split_ifs with hb hr
  · rw [hidx,hidx']
    simp [bitAt_cons]
  · rfl
  · rfl

end Shared.Beeping.NPcoNP.NativeHalfOddCleanupLayout

#print axioms Shared.Beeping.NPcoNP.NativeHalfOddCleanupLayout.odd_writes
