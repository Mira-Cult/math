import Shared.Beeping.NPcoNP.NativeRow8PositivePrepare
import Shared.Beeping.NPcoNP.Native51Redispatch

/-! Connect the positive row-8 result through the complete next selector
and the row-9 one entry. Supplied tape layouts remain explicit. -/
namespace Shared.Beeping.NPcoNP.NativeRow8PositiveRedispatch
open Shared.Beeping Shared.Beeping.Machines PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeRow8PositivePrepare
open Shared.Beeping.NPcoNP.Native51Redispatch
open Shared.Beeping.NPcoNP.NativeFourthNextPath
open Shared.Beeping.NPcoNP.NativeFifthNextPath
open Shared.Beeping.NPcoNP.NativePositiveGraphBank
open Shared.Beeping.NPcoNP.Grammar284ForwardParser
open Shared.Beeping.NPcoNP.Bootstrap284BankDecode
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

/-- Positive row 8 and the next row-9 preparation, selector, dispatch,
and one-entry transition form one finite silent physical segment. -/
theorem positive_then_redispatch_suffix_frame (h b separator : Int) (t : Int → Bool)
    (values : List Nat) (v : Nat) (vs : List Nat) (hlen : values.length=10)
    (hlong : h+12≤separator) (path : Holds t (h-4) fifthPath)
    (left : ∀ q, q<h-4 → t q=false)
    (mark : t (h+7)=true) (z1 : t (h+8)=false) (z2 : t (h+9)=false)
    (ones : ∀ q, h+10≤q → q<separator → t q=true)
    (sep : t separator=false) (right : ∀ q, b≤q → t q=false)
    (bank : Holds t (separator+1)
      (encode values ++ (encode ((v+1)::vs) ++ [false,false]))) :
    ∃ (n : Nat) (mid : Int → Bool),
      let out := fillRange (setAt (h+8) mid) (h+11) (separator-1)
      let final := clearAt (h+8) out
      0<n ∧ Holds final (h-4) sixthPath ∧
      parseForward 52 final (h-4)=some ("3.$coalesced.0.inc",12) ∧
      Holds final (separator+1) (encode values ++ (encode (v::vs) ++ [true,false,false])) ∧
      (∀ q, q<h-4 → final q=false) ∧
      final (h+9)=false ∧ final (h+10)=false ∧
      (∀ q, h+11≤q → q<separator → final q=true) ∧ final separator=false ∧
      (∀ q, separator+1+((encode values).length : Int)+3+((List.replicate v true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)).length : Int)≤q → final q=t q) ∧
      silentSegment machine (cfg 273 (h+8) t) (cfg 275 (h+9) final) n := by
  obtain ⟨n,mid,head,hn,hpath,hparse,hbank,hleft,hhead,h8,h9,h10,hrun,hsep,htail,hseg⟩ :=
    positive_then_prepare_control_suffix_frame h b separator t values v vs hlen hlong path left mark z1 z2 ones sep right bank
  let out := fillRange (setAt (h+8) mid) (h+11) (separator-1)
  let k := (separator-(h+12)).toNat
  have hk : (k : Int)=separator-(h+12) := Int.toNat_of_nonneg (by omega)
  have hhead' : head=(if k=0 then h+7 else separator-3) := hhead
  have hselector : ∃ m : Nat, 0<m ∧
      silentSegment machine (cfg 83 head out) (cfg 93 (h-3) out) m := by
    by_cases hz : k=0
    · have hh : head=h+7 := by simpa [hz] using hhead'
      refine ⟨32,by omega,?_⟩
      rw [hh]
      exact selector_empty h out hpath hleft
    · let r := k-1
      have hkr : k=r+1 := by dsimp [r]; omega
      have hr : (r : Int)=separator-(h+13) := by omega
      have hh : head=h+10+(r : Int) := by rw [if_neg hz] at hhead'; omega
      have hone : ∀ q, h+11≤q → q≤h+10+(r : Int) → out q=true := by
        intro q hq hq'
        exact hrun q hq (by omega)
      have hs := selector_long h r out hpath hleft h8 h9 h10 hone
      refine ⟨r+31,by omega,?_⟩
      simpa only [hh] using hs
  obtain ⟨m,hm,hsel⟩ := hselector
  have hdispatch := dispatch_sixth_path h out hpath
  have hone := oneSeg machine _ _ (step51_one (h+8) out h8)
  let final := clearAt (h+8) out
  have hfinalframe : ∀ q, q≠h+8 → final q=out q := by
    intro q hq
    simp [final,clearAt,hq]
  have hpath' : Holds final (h-4) sixthPath := by
    apply holds_transport out final _ _ hpath
    intro q hq hq'
    symm
    apply hfinalframe
    simp [sixthPath] at hq'
    omega
  have hbank' : Holds final (separator+1)
      (encode values ++ (encode (v::vs) ++ [true,false,false])) := by
    apply holds_transport out final _ _ hbank
    intro q hq _
    symm
    apply hfinalframe
    omega
  have hleft' : ∀ q, q<h-4 → final q=false := by
    intro q hq
    rw [hfinalframe q (by omega)]
    exact hleft q hq
  have a := segAdd machine _ _ _ n m hseg hsel
  have bb := segAdd machine _ _ _ (n+m) 11 a hdispatch
  have cc := segAdd machine _ _ _ (n+m+11) 1 bb hone
  have h9' : final (h+9)=false := by rw [hfinalframe _ (by omega)]; exact h9
  have h10' : final (h+10)=false := by rw [hfinalframe _ (by omega)]; exact h10
  have hrun' : ∀ q, h+11≤q → q<separator → final q=true := by
    intro q hq hq'
    rw [hfinalframe q (by omega)]
    exact hrun q hq hq'
  have hsep' : final separator=false := by rw [hfinalframe _ (by omega)]; exact hsep
  have htail' : ∀ q, separator+1+((encode values).length : Int)+3+((List.replicate v true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)).length : Int)≤q → final q=t q := by
    intro q hq
    rw [hfinalframe q (by omega)]
    exact htail q hq
  refine ⟨n+m+11+1,mid,by omega,hpath',sixth_path_parse final (h-4) hpath',hbank',hleft',
    h9',h10',hrun',hsep',htail',?_⟩
  have hh : h+8+1=h+9 := by omega
  simpa only [hh,final,out] using cc

theorem positive_then_redispatch (h b separator : Int) (t : Int → Bool)
    (values : List Nat) (v : Nat) (vs : List Nat) (hlen : values.length=10)
    (hlong : h+12≤separator) (path : Holds t (h-4) fifthPath)
    (left : ∀ q, q<h-4 → t q=false)
    (mark : t (h+7)=true) (z1 : t (h+8)=false) (z2 : t (h+9)=false)
    (ones : ∀ q, h+10≤q → q<separator → t q=true)
    (sep : t separator=false) (right : ∀ q, b≤q → t q=false)
    (bank : Holds t (separator+1)
      (encode values ++ (encode ((v+1)::vs) ++ [false,false]))) :
    ∃ (n : Nat) (mid : Int → Bool),
      let out := fillRange (setAt (h+8) mid) (h+11) (separator-1)
      let final := clearAt (h+8) out
      0<n ∧ Holds final (h-4) sixthPath ∧
      parseForward 52 final (h-4)=some ("3.$coalesced.0.inc",12) ∧
      Holds final (separator+1) (encode values ++ (encode (v::vs) ++ [true,false,false])) ∧
      (∀ q, q<h-4 → final q=false) ∧
      final (h+9)=false ∧ final (h+10)=false ∧
      (∀ q, h+11≤q → q<separator → final q=true) ∧ final separator=false ∧
      silentSegment machine (cfg 273 (h+8) t) (cfg 275 (h+9) final) n := by
  obtain ⟨n,mid,hn,hpath,hparse,hbank,hleft,h9,h10,hrun,hsep,_,hseg⟩ :=
    positive_then_redispatch_suffix_frame h b separator t values v vs hlen hlong
      path left mark z1 z2 ones sep right bank
  exact ⟨n,mid,hn,hpath,hparse,hbank,hleft,h9,h10,hrun,hsep,hseg⟩

#print axioms positive_then_redispatch_suffix_frame
#print axioms positive_then_redispatch
end Shared.Beeping.NPcoNP.NativeRow8PositiveRedispatch
