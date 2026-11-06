import Shared.Beeping.NPcoNP.NativeHalf143Scan
import Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape

/-! The literal HALF entry scanners cross up to three arbitrary unary blocks
without changing them. Selection and return are separate obligations. -/
namespace Shared.Beeping.NPcoNP.NativeHalfZeroBankScan
open PASoundness Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalf143Scan
open Shared.Beeping.NPcoNP.NativeRow13Scan
open Shared.Beeping.NPcoNP.NativeGrammarAdministrativeDispatch
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

def scanRow : Nat → Fin 284
  | 0 => 29
  | 1 => 44
  | 2 => 45
  | _ => 46

theorem scan_prefix (values : List Nat) (h : Int) (t : Int → Bool)
    (hlen : values.length≤3) (bank : Holds t h (encode values)) :
    silentSegment machine (cfg (scanRow values.length) h t)
      (cfg 29 (h+((encode values).length : Int)) t) (encode values).length := by
  induction values generalizing h with
  | nil =>
    simpa [encode,scanRow] using (show silentSegment machine (cfg 29 h t) (cfg 29 h t) 0 from by
      simp [silentSegment,WordEventSystem.advance,WordEventSystem.wordFrom])
  | cons v vs ih =>
    have hl : vs.length≤2 := by simp only [List.length_cons] at hlen; omega
    obtain ⟨hblock,hrest⟩ := holds_split t h (block v) (encode vs) (by simpa [encode] using bank)
    have hones : ∀ i : Nat, i<v+1 → t (h+(i : Int))=true := by
      intro i hi
      have hh := holds_get t h (block v) hblock i (by simp [block]; omega)
      have hi' : i<(List.replicate (v+1) true).length := by simpa using hi
      simpa only [block,List.getElem_append_left hi',List.getElem_replicate] using hh
    have hz : t (h+((v+1 : Nat) : Int))=false := by
      have hh := holds_get t h (block v) hblock (v+1) (by simp [block])
      simpa [block] using hh
    have hfirst : silentSegment machine (cfg (scanRow (v::vs).length) h t)
        (cfg (scanRow vs.length) (h+((v+2 : Nat) : Int)) t) (v+2) := by
      have hc : vs.length=0 ∨ vs.length=1 ∨ vs.length=2 := by omega
      rcases hc with hc | hc | hc
      · have hs := scan44 (v+1) h t hones hz
        simpa [scanRow,hc,Nat.cast_add,Int.add_assoc] using hs
      · have hs := scan45 (v+1) h t hones hz
        simpa [scanRow,hc,Nat.cast_add,Int.add_assoc] using hs
      · have hs := scan46 (v+1) h t hones hz
        simpa [scanRow,hc,Nat.cast_add,Int.add_assoc] using hs
    have hr : Holds t (h+((v+2 : Nat) : Int)) (encode vs) := by
      simpa [block_length] using hrest
    have hnext := ih (h+((v+2 : Nat) : Int)) (by omega) hr
    have hall := segAdd machine _ _ _ (v+2) (encode vs).length hfirst hnext
    simpa [encode,block_length,List.length_append,Nat.cast_add,Int.add_assoc] using hall

#print axioms scan_prefix
end Shared.Beeping.NPcoNP.NativeHalfZeroBankScan
