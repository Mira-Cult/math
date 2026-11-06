import Shared.Beeping.NPcoNP.Native273BankScan

/-! Literal state-280 scan across six encoded producer-array values. -/
namespace Shared.Beeping.NPcoNP.Native280BankScan
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.Native279BankScan
open Shared.Beeping.NPcoNP.Native273BankScan
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Six complete bank blocks are scanned, then the first one of the next
block is cleared. The duration and full tape effect are exact. -/
theorem scan_to262 (h separator : Int) (t : Int → Bool)
    (values : List Nat) (value : Nat) (tail : List Bool) (hlen : values.length=6)
    (hlong : h+11≤separator) (h9 : t (h+9)=false) (h10 : t (h+10)=false)
    (ones : ∀ q, h+11≤q → q<separator → t q=true) (sep : t separator=false)
    (bank : Holds t (separator+1) (encode values ++ (block value ++ tail))) :
    let pos := separator+1+((encode values).length : Int)
    let k := (separator-(h+11)).toNat
    (∀ q, q≠pos → clearAt pos t q=t q) ∧
    silentSegment machine (cfg 280 (h+9) t) (cfg 262 (pos-2) (clearAt pos t))
      (k+(encode values).length+5) := by
  dsimp only
  let pos := separator+1+((encode values).length : Int)
  let k := (separator-(h+11)).toNat
  have hk : (k : Int)=separator-(h+11) := Int.toNat_of_nonneg (by omega)
  have hc : ∀ i : Nat, i<k → t (h+11+(i : Int))=true := by
    intro i hi
    apply ones <;> omega
  have hd : t (h+11+(k : Int))=false := by
    have he : h+11+(k : Int)=separator := by omega
    rw [he]; exact sep
  have ha := oneSeg machine _ _ (Native273BankScan.step_zero PrefixRow.r280 (h+9) t h9)
  have hb := oneSeg machine _ _ (Native279BankScan.step_zero RightRow.r279 (h+10) t h10)
  have ha' : silentSegment machine (cfg 280 (h+9) t) (cfg 279 (h+10) t) 1 := by
    simpa only [show h+9+1=h+10 by omega] using ha
  have hab : silentSegment machine (cfg 280 (h+9) t) (cfg 278 (h+11) t) 2 := by
    have hs := segAdd machine _ _ _ 1 1 ha' hb
    simpa [Int.add_assoc] using hs
  have hc' := Native279BankScan.scan_run RightRow.r278 k (h+11) t hc hd
  have hcontrol : silentSegment machine (cfg 278 (h+11) t) (cfg 277 (separator+1) t) (k+1) := by
    have he : h+11+(k : Int)+1=separator+1 := by omega
    simpa only [he] using hc'
  have chain : Chain 6 277 42 :=
    .cons .r277 (.cons .r276 (.cons .r275 (.cons .r271 (.cons .r270 (.cons .r9 (.refl 42))))))
  obtain ⟨hrest,hlast,hscan⟩ := scan_bank chain values (separator+1) t (block value ++ tail) hlen bank
  have htarget : t pos=true := by
    change Holds t pos (block value ++ tail) at hrest
    simp only [block,List.replicate_succ,List.cons_append,Holds] at hrest
    exact hrest.1
  have hzero : t (pos-1)=false := by
    have hh := hlast (by decide)
    simpa [pos] using hh
  let u := clearAt pos t
  have hz : u (pos-1)=false := by simp [u,clearAt,show pos-1≠pos by omega,hzero]
  have hfirst := oneSeg machine _ _ (step42_one pos t htarget)
  have hsecond := oneSeg machine _ _ (step283_zero (pos-1) u hz)
  have hfinish : silentSegment machine (cfg 42 pos t) (cfg 262 (pos-2) u) 2 := by
    have hs := segAdd machine _ _ _ 1 1 hfirst hsecond
    have he : pos-1-1=pos-2 := by omega
    simpa [u,he] using hs
  have hscan' : silentSegment machine (cfg 277 (separator+1) t) (cfg 42 pos t) (encode values).length := by
    simpa only [pos] using hscan
  have a := segAdd machine _ _ _ 2 (k+1) hab hcontrol
  have b := segAdd machine _ _ _ (2+(k+1)) (encode values).length a hscan'
  have all := segAdd machine _ _ _ (2+(k+1)+(encode values).length) 2 b hfinish
  constructor
  · intro q hq
    simp [clearAt,hq]
  · have he : 2+(k+1)+(encode values).length+2=k+(encode values).length+5 := by omega
    simpa only [he,pos,k,u] using all

#print axioms scan_to262
end Shared.Beeping.NPcoNP.Native280BankScan
