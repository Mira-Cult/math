import Shared.Beeping.NPcoNP.NativeHalfZeroGeneralScan
import Shared.Beeping.NPcoNP.NativeHalfZeroGeneralReturn

/-! All four prepared native HALF entries select a zero-valued bank block and
return to the carry while preserving arbitrary earlier unary blocks. -/
namespace Shared.Beeping.NPcoNP.NativeHalfZeroPreparedGeneral
open PASoundness Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeGrammarPreterminalDispatch
open Shared.Beeping.NPcoNP.NativeHalfZeroGeneralScan
open Shared.Beeping.NPcoNP.NativeHalfZeroGeneralReturn
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

theorem prepared_zero_to1 (state : Fin 185) (path : Path) (name : String) (values : List Nat)
    (leaf : graphLeaf state=some (path,name)) (entry : operationEntry name=some (entryAt values.length))
    (hlen : values.length≤3) (origin h separator : Int) (t : Int → Bool) (tail : List Bool)
    (hentry : h=origin+((path.length : Nat) : Int)) (space : h+3≤separator)
    (word : Holds t origin path) (marker : t h=true) (lastZero : t (h-1)=false)
    (z1 : t (h+1)=false) (control : ∀ q, h+2≤q → q<separator → t q=true)
    (sep : t separator=false) (bank : Holds t (separator+1) (encode values ++ ([true,false] ++ tail))) :
    let out := clearAt h t
    ∃ steps : Nat, 0<steps ∧ Holds out (separator+1) (encode values ++ ([true,false] ++ tail)) ∧
      (∀ q, q≠h → out q=t q) ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 1 (h-2) out) steps := by
  dsimp only
  let out := clearAt h t
  let pos := separator+1+((encode values).length : Int)
  obtain ⟨a,ha,hbank,_,_,hframe,hscan⟩ :=
    prepared_to_selected_zero state path name values leaf entry hlen origin h separator t tail
      hentry space word marker z1 control sep bank
  change ∀ q, q≠h → out q=t q at hframe
  have hz0 : out h=false := by simp [out,clearAt]
  have hz1 : out (h+1)=false := (hframe _ (by omega)).trans z1
  have hprev : out (h-1)=false := (hframe _ (by omega)).trans lastZero
  have hcontrol : ∀ q, h+2≤q → q<separator → out q=true := by
    intro q hq hq'
    rw [hframe q (by omega)]
    exact control q hq hq'
  have hsep : out separator=false := (hframe _ (by omega)).trans sep
  obtain ⟨b,hb,hreturn⟩ := selected_zero_returns h separator out values tail space hz0 hz1 hprev hcontrol hsep hbank
  exact ⟨a+b,by omega,hbank,hframe,segAdd machine _ _ _ a b hscan hreturn⟩

#print axioms prepared_zero_to1
end Shared.Beeping.NPcoNP.NativeHalfZeroPreparedGeneral
