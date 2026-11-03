import Shared.PNP.Record285.IncrementMeaning

/-! Literal increment preparation from a clean terminal to redispatch. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.IncrementPreparation
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.IncrementSelector (odd_bit odd_tail)
open Shared.PNP.Record285.IncrementShift (atWord even_bit even_tail)
open Shared.PNP.Record285.IncrementReturn (atLeftWord push_run)

def prep1 : Fin 285 := ⟨9,by decide⟩
def prep2 : Fin 285 := ⟨10,by decide⟩
def break0 : Fin 285 := ⟨119,by decide⟩
def dispatch0 : Fin 285 := ⟨110,by decide⟩
def dispatch1 : Fin 285 := ⟨111,by decide⟩
def dispatch2 : Fin 285 := ⟨112,by decide⟩

def terminal : Nat → Fin 285
  | 0 => ⟨76,by decide⟩ | 1 => ⟨78,by decide⟩
  | 2 => ⟨90,by decide⟩ | 3 => ⟨92,by decide⟩
  | 4 => ⟨94,by decide⟩ | 5 => ⟨96,by decide⟩
  | 6 => ⟨98,by decide⟩ | 7 => ⟨100,by decide⟩
  | 8 => ⟨102,by decide⟩ | 9 => ⟨104,by decide⟩
  | 10 => ⟨80,by decide⟩ | 11 => ⟨82,by decide⟩
  | 12 => ⟨84,by decide⟩ | 13 => ⟨86,by decide⟩
  | 14 => ⟨88,by decide⟩ | _ => ⟨76,by decide⟩

structure Rows (M : Machine 285) (term : Fin 285) where
  termZero : M.table.row term false = ⟨true,.right,prep1,false⟩
  prepOneZero : M.table.row prep1 false = ⟨false,.right,prep2,false⟩
  prepTwoZero : M.table.row prep2 false = ⟨true,.right,prep2,false⟩
  prepTwoOne : M.table.row prep2 true = ⟨true,.left,break0,false⟩
  breakZero : M.table.row break0 false = ⟨false,.left,break0,false⟩
  breakOne : M.table.row break0 true = ⟨true,.left,dispatch0,false⟩
  dispatchZero : M.table.row dispatch0 false = ⟨false,.left,dispatch1,false⟩
  dispatchOne : M.table.row dispatch0 true = ⟨true,.left,dispatch0,false⟩
  dispatch1Zero : M.table.row dispatch1 false = ⟨false,.left,dispatch2,false⟩
  dispatch1One : M.table.row dispatch1 true = ⟨true,.left,dispatch0,false⟩

/-- Fill the finite zero gap, stopping at the original anchor one. -/
theorem fill_gap (M : Machine 285) (term : Fin 285) (rows : Rows M term)
    (g : Nat) (head : Int) (left tail : Nat) :
    silent M g (atWord prep2 head left (runPattern false g true tail)) =
      some (atWord prep2 (head+g) (pushBit g true left) (1+2*tail)) := by
  cases g with
  | zero => simp [atWord,runPattern,bitVal,pushBit,silent]
  | succ g =>
    have hs := run_sweep_right M prep2 false true rows.prepTwoZero g true tail left head
    have hh : atWord prep2 head left (runPattern false (g+1) true tail) =
        ⟨prep2,head,left,false,runPattern false g true tail⟩ := by
      simp only [atWord,runPattern,bitVal,Bool.false_eq_true,if_false,Nat.zero_add,even_bit,even_tail]
    rw [hh]
    simpa only [atWord,odd_bit,odd_tail,Int.natCast_succ] using hs

/-- The short return from the anchor crosses the filled gap and enters the
leftward dispatcher at the cell immediately before the marked terminal. -/
theorem gap_return (M : Machine 285) (term : Fin 285) (rows : Rows M term)
    (g : Nat) (head : Int) (left tail : Nat) :
    silent M (g+2) (atLeftWord break0 (head+g+1)
      (runPattern true g false (1+2*left)) (2*tail+1)) =
      some (atLeftWord dispatch0 (head-1) left (1+4*pushBit (g+1) true tail)) := by
  cases g with
  | zero =>
    simp only [runPattern,bitVal,Bool.false_eq_true,if_false,Nat.zero_add,atLeftWord,
      even_bit,even_tail,odd_bit,odd_tail,silent,PhysicalNumeric.step,rows.breakZero,
      rows.breakOne,if_true,pushBit]
    have hh : head + ((0:Nat):Int) + 1 - 1 - 1 = head-1 := by omega
    have hr : 2*(2*(2*tail+1)+0)+1 = 1+4*(2*tail+1) := by omega
    simp only [hh,hr]
  | succ g =>
    have hd : IncrementReturn.Rows M dispatch0 dispatch1 dispatch2 :=
      ⟨rows.dispatchOne,rows.dispatchZero,rows.dispatch1One,rows.dispatch1Zero⟩
    have hfirst : silent M 1 (atLeftWord break0 (head+(g+1)+1)
        (runPattern true (g+1) false (1+2*left)) (2*tail+1)) =
        some (atLeftWord dispatch0 (head+(g+1))
          (runPattern true g false (1+2*left)) (2*(2*tail+1)+1)) := by
      simp only [atLeftWord,runPattern,bitVal,if_true,odd_bit,odd_tail,silent,
        PhysicalNumeric.step,rows.breakOne,Bool.false_eq_true,if_false]
      have hh : head+((g:Int)+1)+1-1 = head+((g:Int)+1) := by omega
      rw [hh]
    have hrest := IncrementReturn.return_block M dispatch0 dispatch1 dispatch2 hd g
      (head+(g+1)) left (2*(2*tail+1)+1)
    simp only [Int.natCast_succ]
    rw [show (g+1)+2 = 1+(g+2) by omega,silent_add,hfirst]
    simp only [Option.bind_some]
    have hp : pushBit g true (2*(2*tail+1)+1) = pushBit ((g+1)+1) true tail := by
      simp only [pushBit,bitVal,if_true]
    have hh : head+((g:Int)+1)-((g:Int)+2) = head-1 := by omega
    simpa only [hp,Int.natCast_add,Int.natCast_one,hh,show 4*pushBit ((g+1)+1) true tail+1 =
      1+4*pushBit ((g+1)+1) true tail by omega] using hrest

/-- Starting at a clean terminal, mark it, fill the zero gap up to the
anchor, and return to the shared dispatcher with the complete tape specified. -/
theorem prepare_to_dispatch (M : Machine 285) (term : Fin 285) (rows : Rows M term)
    (g : Nat) (head : Int) (left tail : Nat) :
    silent M (2*g+5)
      ⟨term,head,left,false,2*runPattern false g true tail⟩ =
      some (atLeftWord dispatch0 (head-1) left (1+4*pushBit (g+1) true tail)) := by
  have hfirst : silent M 2 ⟨term,head,left,false,2*runPattern false g true tail⟩ =
      some (atWord prep2 (head+2) (4*left+2) (runPattern false g true tail)) := by
    simp only [silent,PhysicalNumeric.step,rows.termZero,rows.prepOneZero,
      Bool.false_eq_true,if_false,bitVal,if_true,even_bit,even_tail,atWord]
    have hh : head+1+1 = head+2 := by omega
    have hl : 2*(2*left+1)+0 = 4*left+2 := by omega
    simp only [hh,hl]
  have hfill := fill_gap M term rows g (head+2) (4*left+2) tail
  have hanchor : silent M 1
      (atWord prep2 (head+2+g) (pushBit g true (4*left+2)) (1+2*tail)) =
      some (atLeftWord break0 (head+g+1) (runPattern true g false (1+2*left)) (2*tail+1)) := by
    have hp : pushBit g true (4*left+2) = runPattern true g false (1+2*left) := by
      rw [show 4*left+2 = 2*(1+2*left) by omega,push_run]
    simp only [atWord,odd_bit,odd_tail,silent,PhysicalNumeric.step,rows.prepTwoOne,
      Bool.false_eq_true,if_false,bitVal,if_true,atLeftWord,hp]
    have hh : head+2+(g:Int)-1 = head+(g:Int)+1 := by omega
    rw [hh]
  have hret := gap_return M term rows g head left tail
  rw [show 2*g+5 = 2+(g+(1+(g+2))) by omega,silent_add,hfirst]
  simp only [Option.bind_some]
  rw [silent_add,hfill]
  simp only [Option.bind_some]
  rw [silent_add,hanchor]
  simp only [Option.bind_some]
  exact hret

/-- Check both terminal rows for every emitted ordinary increment index. -/
def terminalCheck (i : Nat) : Bool :=
  decide (NumericTables.target.table.row (terminal i) false = ⟨true,.right,prep1,false⟩) &&
  decide (NumericTables.target.table.row (terminal i) true =
    ⟨false,.right,IncrementSelector.literalState (i+2),false⟩)

theorem terminal_check_all : (List.range 15).all terminalCheck = true := by decide

theorem terminal_rows (i : Nat) (hi : i < 15) :
    Record285.machine.table.row (terminal i) false = ⟨true,.right,prep1,false⟩ ∧
    Record285.machine.table.row (terminal i) true =
      ⟨false,.right,IncrementSelector.literalState (i+2),false⟩ := by
  have h := List.all_eq_true.mp terminal_check_all i (List.mem_range.mpr hi)
  simp only [terminalCheck,Bool.and_eq_true,decide_eq_true_eq] at h
  simpa only [ArtifactEndpoint.literal_rows] using h

theorem literal_rows (i : Nat) (hi : i < 15) : Rows Record285.machine (terminal i) := by
  constructor
  · exact (terminal_rows i hi).1
  all_goals rw [ArtifactEndpoint.literal_rows] <;> decide

theorem literal_prepare (i : Nat) (hi : i < 15) (g : Nat) (head : Int) (left tail : Nat) :
    silent Record285.machine (2*g+5)
      ⟨terminal i,head,left,false,2*runPattern false g true tail⟩ =
      some (atLeftWord dispatch0 (head-1) left (1+4*pushBit (g+1) true tail)) :=
  prepare_to_dispatch Record285.machine (terminal i) (literal_rows i hi) g head left tail

theorem literal_prepare_physical (i : Nat) (hi : i < 15) (g : Nat) (head : Int) (left tail : Nat)
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel ⟨terminal i,head,left,false,2*runPattern false g true tail⟩ physical) :
    Rel (atLeftWord dispatch0 (head-1) left (1+4*pushBit (g+1) true tail))
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run (2*g+5)) ∧
    ∀ t, t < 2*g+5 → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t :=
  silent_physical Record285.machine _ physical hrel _ _ (literal_prepare i hi g head left tail)

end Shared.PNP.Record285.IncrementPreparation
