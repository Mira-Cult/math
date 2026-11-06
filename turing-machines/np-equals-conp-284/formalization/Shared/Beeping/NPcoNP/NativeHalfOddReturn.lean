import Shared.Beeping.NPcoNP.NativeHalfOddToCleanup
import Shared.Beeping.NPcoNP.NativeHalfReturn23

/-! Odd HALF return through the literal state-25/26 leftward scan. A finite
delimiter in the protected prefix is an explicit premise. -/
namespace Shared.Beeping.NPcoNP.NativeHalfOddReturn

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.NPcoNP.NativeHalfCleanupPrefix
open Shared.Beeping.NPcoNP.NativeHalfOddToCleanup
open Shared.Beeping.NPcoNP.NativeHalfRegularIteration
open Shared.Beeping.NPcoNP.NativeHalfLoopIteration
open Shared.Beeping.NPcoNP.NativeHalfLoopArithmetic
open Shared.Beeping.NPcoNP.NativeHalfCycleTape

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

theorem row25_zero : machine.table.row 25 false = ⟨false,.left,26,false⟩ := by decide
theorem row25_one : machine.table.row 25 true = ⟨true,.left,25,false⟩ := by decide
theorem row26_zero : machine.table.row 26 false = ⟨false,.left,95,false⟩ := by decide
theorem row26_one : machine.table.row 26 true = ⟨true,.left,25,false⟩ := by decide

theorem step25_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 25 h t)=(cfg 26 (h-1) t,false) := by
  have hw : (⟨25,h,t⟩ : Config 284).write false=t := by rw [← ht]; exact write_current _
  simp [cfg,Machine.step,ht,row25_zero,Move.apply,hw]

theorem step25_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 25 h t)=(cfg 25 (h-1) t,false) := by
  have hw : (⟨25,h,t⟩ : Config 284).write true=t := by rw [← ht]; exact write_current _
  simp [cfg,Machine.step,ht,row25_one,Move.apply,hw]

theorem step26_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 26 h t)=(cfg 95 (h-1) t,false) := by
  have hw : (⟨26,h,t⟩ : Config 284).write false=t := by rw [← ht]; exact write_current _
  simp [cfg,Machine.step,ht,row26_zero,Move.apply,hw]

theorem step26_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 26 h t)=(cfg 25 (h-1) t,false) := by
  have hw : (⟨26,h,t⟩ : Config 284).write true=t := by rw [← ht]; exact write_current _
  simp [cfg,Machine.step,ht,row26_one,Move.apply,hw]

/-- The odd return scan preserves the complete tape and takes exactly one
step per supplied bit plus two delimiter steps. -/
theorem return_scan25 (s : Shape) (h : Int) (t : Int → Bool)
    (hm : downHolds t h (bits s ++ [false,false])) :
    silentSegment machine (cfg 25 h t)
      (cfg 95 (h-(bits s).length-2) t) ((bits s).length+2) := by
  induction s generalizing h with
  | stop =>
    simp only [bits,List.nil_append,downHolds] at hm
    have ha := oneSeg machine _ _ (step25_zero h t hm.1)
    have hb := oneSeg machine _ _ (step26_zero (h-1) t hm.2.1)
    have hh := segAdd machine _ _ _ 1 1 ha hb
    simpa [bits,Int.sub_sub] using hh
  | one s ih =>
    simp only [bits,List.cons_append,downHolds] at hm
    have ha := oneSeg machine _ _ (step25_one h t hm.1)
    have hb := ih (h-1) hm.2
    have hh := segAdd machine _ _ _ 1 ((bits s).length+2) ha hb
    simpa [bits,List.length_cons,Int.sub_sub,Int.add_assoc,Int.add_comm,
      Int.add_left_comm,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
  | zeroOne s ih =>
    simp only [bits,List.cons_append,downHolds] at hm
    have ha := oneSeg machine _ _ (step25_zero h t hm.1)
    have hb := oneSeg machine _ _ (step26_one (h-1) t hm.2.1)
    have hc := ih (h-1-1) hm.2.2
    have hab := segAdd machine _ _ _ 1 1 ha hb
    have hall := segAdd machine _ _ _ 2 ((bits s).length+2) hab hc
    have he : h-((bits (Shape.zeroOne s)).length : Int)-2 =
        h-1-1-(bits s).length-2 := by simp [bits]; omega
    have hn : (bits (Shape.zeroOne s)).length+2=2+((bits s).length+2) := by simp [bits]; omega
    rw [he,hn]
    exact hall

/-- The one-unit odd residual and cleanup return to state 95 under the
explicit finite left-delimiter condition. -/
theorem residual_one_to95 (base : Int → Bool) (g : Int) (xs : List Nat) (s : Shape)
    (hm : downHolds (put base g true) g (bits s ++ [false,false])) :
    silentSegment machine
      (cfg 30 g (UnarySuffixShift.after base g (UnaryBank.encode (0::xs))))
      (cfg 95 (g-(bits s).length-2) (postTape (put base g true) g xs))
      (2*(UnaryBank.encode xs).length+10+((bits s).length+2)) := by
  have hc := residual_one_through_cleanup base g xs
  have hp := downHolds_postTape (put base g true) g g xs (bits s ++ [false,false]) (by omega) hm
  have hr := return_scan25 s g (postTape (put base g true) g xs) hp
  exact segAdd machine _ _ _ _ _ hc hr

/-- Every prepared odd residual of size at least three completes its
iterations, cleanup, and return to state 95, provided the indicated finite
delimiter is present in the protected prefix at the final boundary. -/
theorem maximal_odd_to95 (base : Int → Bool) (b : Int) (m : Nat)
    (xs : List Nat) (s : Shape) (hb : base b=true) (hm : 3≤m) (hodd : m%2=1)
    (hpat : let k := regularCount m-1
      let g := boundary b k+1
      downHolds (put (bases base b k) g true) g (bits s ++ [false,false])) :
    let k := regularCount m-1
    let g := boundary b k+1
    let bs := bases base b k
    let vs := tailValues xs k
    silentSegment machine
      (cfg 30 (boundary b 0)
        (prior (bases base b 0) (boundary b 0) (suffix (value m) (tailValues xs) 0)))
      (cfg 95 (g-(bits s).length-2) (postTape (put bs g true) g vs))
      (totalDuration (value m) (tailValues xs) k + duration (value m) (tailValues xs) k +
        3 + (2*(UnaryBank.encode vs).length+7) + ((bits s).length+2)) := by
  dsimp only at hpat ⊢
  let k := regularCount m-1
  let g := boundary b k+1
  let bs := bases base b k
  let vs := tailValues xs k
  have hc := maximal_odd_through_cleanup base b m xs hb hm hodd
  dsimp only at hc
  change silentSegment machine _ (cfg 25 g (postTape (put bs g true) g vs)) _ at hc
  have hp : downHolds (postTape (put bs g true) g vs) g (bits s ++ [false,false]) :=
    downHolds_postTape (put bs g true) g g vs (bits s ++ [false,false]) (by omega) hpat
  have hr := return_scan25 s g (postTape (put bs g true) g vs) hp
  exact segAdd machine _ _ _ _ _ hc hr

end Shared.Beeping.NPcoNP.NativeHalfOddReturn

#print axioms Shared.Beeping.NPcoNP.NativeHalfOddReturn.residual_one_to95
#print axioms Shared.Beeping.NPcoNP.NativeHalfOddReturn.maximal_odd_to95
