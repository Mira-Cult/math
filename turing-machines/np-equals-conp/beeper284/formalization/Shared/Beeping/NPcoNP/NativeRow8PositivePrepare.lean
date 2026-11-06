import Shared.Beeping.NPcoNP.Native273PositiveNext
import Shared.Beeping.NPcoNP.Native51Prepare
import Shared.Beeping.NPcoNP.NativePositiveGraphBank

/-! The positive row-8 physical operation supplies the marker needed for
its next row-9 preparation, including the empty control-gap case.
This is a finite supplied-layout result, not a complete row-9 simulation. -/
namespace Shared.Beeping.NPcoNP.NativeRow8PositivePrepare
open Shared.Beeping Shared.Beeping.Machines PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.Native273PositiveNext
open Shared.Beeping.NPcoNP.Native51Prepare
open Shared.Beeping.NPcoNP.NativeFourthNextPath
open Shared.Beeping.NPcoNP.NativeFifthNextPath
open Shared.Beeping.NPcoNP.NativePositiveGraphBank
open Shared.Beeping.NPcoNP.Grammar284ForwardParser
open Shared.Beeping.NPcoNP.Bootstrap284BankDecode
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- The positive decrement and its following state-51 zero preparation are
one finite silent segment. The returned head depends on the gap length. -/
theorem positive_then_prepare_control_suffix_frame (h b separator : Int) (t : Int → Bool)
    (values : List Nat) (v : Nat) (vs : List Nat) (hlen : values.length=10)
    (hlong : h+12≤separator) (path : Holds t (h-4) fifthPath)
    (left : ∀ q, q<h-4 → t q=false)
    (mark : t (h+7)=true) (z1 : t (h+8)=false) (z2 : t (h+9)=false)
    (ones : ∀ q, h+10≤q → q<separator → t q=true)
    (sep : t separator=false) (right : ∀ q, b≤q → t q=false)
    (bank : Holds t (separator+1)
      (encode values ++ (encode ((v+1)::vs) ++ [false,false]))) :
    ∃ (n : Nat) (mid : Int → Bool) (head : Int),
      let out := fillRange (setAt (h+8) mid) (h+11) (separator-1)
      0<n ∧ Holds out (h-4) sixthPath ∧
      parseForward 52 out (h-4)=some ("3.$coalesced.0.inc",12) ∧
      Holds out (separator+1) (encode values ++ (encode (v::vs) ++ [true,false,false])) ∧
      (∀ q, q<h-4 → out q=false) ∧
      head=(if (separator-(h+12)).toNat=0 then h+7 else separator-3) ∧
      out (h+8)=true ∧ out (h+9)=false ∧ out (h+10)=false ∧
      (∀ q, h+11≤q → q<separator → out q=true) ∧ out separator=false ∧
      (∀ q, separator+1+((encode values).length : Int)+3+((List.replicate v true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)).length : Int)≤q → out q=t q) ∧
      silentSegment machine (cfg 273 (h+8) t) (cfg 83 head out) n := by
  obtain ⟨n,mid,hn,hpath,hparse,hbank,hleft,hgap,hmarker,hsepOut,htail,hseg⟩ :=
    positive_to_sixth_dispatch_suffix_frame h b separator t values v vs hlen (by omega)
      path left mark z1 z2 ones sep right bank
  let k := (separator-(h+12)).toNat
  have hk : (k : Int)=separator-(h+12) := Int.toNat_of_nonneg (by omega)
  have h0 : mid (h+8)=false := hgap _ (by omega) (by omega)
  have h1 : mid (h+8+1)=false := hgap _ (by omega) (by omega)
  have h2 : mid (h+8+2)=false := hgap _ (by omega) (by omega)
  have hz : ∀ i : Nat, i<k → mid (h+8+3+(i : Int))=false := by
    intro i hi
    apply hgap <;> omega
  have hm : mid (h+8+3+(k : Int))=true := by
    have he : h+8+3+(k : Int)=separator-1 := by omega
    simpa only [he] using hmarker
  let m := if k=0 then 7 else k+5
  let head := if k=0 then h+7 else separator-3
  have hmpos : 0<m := by dsimp [m]; split_ifs <;> omega
  have hprepare := Native51Prepare.zero_prepare_to83_exact (h+8) mid k h0 h1 h2 hz hm
  let out := fillRange (setAt (h+8) mid) (h+11) (separator-1)
  have he : h+11+(k : Int)=separator-1 := by omega
  have hhead' : (if k=0 then h+8-1 else separator-1-2)=head := by
    dsimp [head]
    split_ifs <;> omega
  have hprepare' : silentSegment machine (cfg 51 (h+8) mid) (cfg 83 head out) m := by
    simpa only [show h+8+3=h+11 by omega,he,hhead',out,m] using hprepare
  have hf : ∀ q, q≠h+8 → (q<h+11 ∨ separator-1≤q) → out q=mid q := by
    intro q hne hside
    have hn : ¬ (h+11≤q ∧ q<separator-1) := by omega
    simp [out,fillRange,setAt,hn,hne]
  have hpath' : Holds out (h-4) sixthPath := by
    apply holds_transport mid out _ _ hpath
    intro q hq hq'
    symm
    apply hf q (by simp [sixthPath] at hq'; omega)
    left
    simp [sixthPath] at hq'
    omega
  have hparse' : parseForward 52 out (h-4)=some ("3.$coalesced.0.inc",12) :=
    sixth_path_parse out (h-4) hpath'
  have hbank' : Holds out (separator+1)
      (encode values ++ (encode (v::vs) ++ [true,false,false])) := by
    apply holds_transport mid out _ _ hbank
    intro q hq _
    symm
    exact hf q (by omega) (Or.inr (by omega))
  have hleft' : ∀ q, q<h-4 → out q=false := by
    intro q hq
    rw [hf q (by omega) (Or.inl (by omega))]
    exact hleft q hq
  have h8 : out (h+8)=true := by simp [out,fillRange,setAt,show ¬(h+11≤h+8 ∧ h+8<separator-1) by omega]
  have h9 : out (h+9)=false := by
    rw [hf _ (by omega) (Or.inl (by omega))]
    exact hgap _ (by omega) (by omega)
  have h10 : out (h+10)=false := by
    rw [hf _ (by omega) (Or.inl (by omega))]
    exact hgap _ (by omega) (by omega)
  have hrun : ∀ q, h+11≤q → q<separator → out q=true := by
    intro q hq hq'
    by_cases hlt : q<separator-1
    · simp [out,fillRange,hq,hlt]
    · have heq : q=separator-1 := by omega
      subst q
      rw [hf _ (by omega) (Or.inr (by omega))]
      exact hmarker
  have hsep' : out separator=false := by
    rw [hf separator (by omega) (Or.inr (by omega))]
    exact hsepOut
  have htail' : ∀ q, separator+1+((encode values).length : Int)+3+((List.replicate v true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)).length : Int)≤q → out q=t q := by
    intro q hq
    rw [hf q (by omega) (Or.inr (by omega))]
    exact htail q hq
  exact ⟨n+m,mid,head,by omega,hpath',hparse',hbank',hleft',rfl,h8,h9,h10,hrun,hsep',htail',
    segAdd machine _ _ _ n m hseg hprepare'⟩

theorem positive_then_prepare_control (h b separator : Int) (t : Int → Bool)
    (values : List Nat) (v : Nat) (vs : List Nat) (hlen : values.length=10)
    (hlong : h+12≤separator) (path : Holds t (h-4) fifthPath)
    (left : ∀ q, q<h-4 → t q=false)
    (mark : t (h+7)=true) (z1 : t (h+8)=false) (z2 : t (h+9)=false)
    (ones : ∀ q, h+10≤q → q<separator → t q=true)
    (sep : t separator=false) (right : ∀ q, b≤q → t q=false)
    (bank : Holds t (separator+1)
      (encode values ++ (encode ((v+1)::vs) ++ [false,false]))) :
    ∃ (n : Nat) (mid : Int → Bool) (head : Int),
      let out := fillRange (setAt (h+8) mid) (h+11) (separator-1)
      0<n ∧ Holds out (h-4) sixthPath ∧
      parseForward 52 out (h-4)=some ("3.$coalesced.0.inc",12) ∧
      Holds out (separator+1) (encode values ++ (encode (v::vs) ++ [true,false,false])) ∧
      (∀ q, q<h-4 → out q=false) ∧
      head=(if (separator-(h+12)).toNat=0 then h+7 else separator-3) ∧
      out (h+8)=true ∧ out (h+9)=false ∧ out (h+10)=false ∧
      (∀ q, h+11≤q → q<separator → out q=true) ∧ out separator=false ∧
      silentSegment machine (cfg 273 (h+8) t) (cfg 83 head out) n := by
  obtain ⟨n,mid,head,hn,hpath,hparse,hbank,hleft,hhead,h8,h9,h10,hrun,hsep,_,hseg⟩ :=
    positive_then_prepare_control_suffix_frame h b separator t values v vs hlen hlong
      path left mark z1 z2 ones sep right bank
  exact ⟨n,mid,head,hn,hpath,hparse,hbank,hleft,hhead,h8,h9,h10,hrun,hsep,hseg⟩

/-- The original row-8-to-preparation interface. -/
theorem positive_then_prepare (h b separator : Int) (t : Int → Bool)
    (values : List Nat) (v : Nat) (vs : List Nat) (hlen : values.length=10)
    (hlong : h+12≤separator) (path : Holds t (h-4) fifthPath)
    (left : ∀ q, q<h-4 → t q=false)
    (mark : t (h+7)=true) (z1 : t (h+8)=false) (z2 : t (h+9)=false)
    (ones : ∀ q, h+10≤q → q<separator → t q=true)
    (sep : t separator=false) (right : ∀ q, b≤q → t q=false)
    (bank : Holds t (separator+1)
      (encode values ++ (encode ((v+1)::vs) ++ [false,false]))) :
    ∃ (n : Nat) (mid : Int → Bool) (head : Int),
      let out := fillRange (setAt (h+8) mid) (h+11) (separator-1)
      0<n ∧ Holds out (h-4) sixthPath ∧
      parseForward 52 out (h-4)=some ("3.$coalesced.0.inc",12) ∧
      Holds out (separator+1) (encode values ++ (encode (v::vs) ++ [true,false,false])) ∧
      (∀ q, q<h-4 → out q=false) ∧
      head=(if (separator-(h+12)).toNat=0 then h+7 else separator-3) ∧
      silentSegment machine (cfg 273 (h+8) t) (cfg 83 head out) n := by
  obtain ⟨n,mid,head,hn,hpath,hparse,hbank,hleft,hhead,_,_,_,_,_,hseg⟩ :=
    positive_then_prepare_control h b separator t values v vs hlen hlong path left mark z1 z2 ones sep right bank
  exact ⟨n,mid,head,hn,hpath,hparse,hbank,hleft,hhead,hseg⟩

/-- The preparation retains the decoded output of graph row 8 exactly. Graph
row 9 has not yet been executed: the physical endpoint is its selector return. -/
theorem positive_then_prepare_graph (h b separator : Int) (t : Int → Bool)
    (values : List Nat) (v z : Nat) (rest : List Nat) (graphBank : Bank 12)
    (hlen : values.length=10) (hgraph : List.ofFn graphBank=values ++ [v+1,z])
    (hlong : h+12≤separator) (path : Holds t (h-4) fifthPath)
    (left : ∀ q, q<h-4 → t q=false)
    (mark : t (h+7)=true) (z1 : t (h+8)=false) (z2 : t (h+9)=false)
    (ones : ∀ q, h+10≤q → q<separator → t q=true)
    (sep : t separator=false) (right : ∀ q, b≤q → t q=false)
    (bank : Holds t (separator+1)
      (encode values ++ (encode ((v+1)::z::rest) ++ [false,false]))) :
    let result := (target.system.step ⟨8,graphBank⟩).1
    ∃ (n : Nat) (mid : Int → Bool) (head : Int),
      let out := fillRange (setAt (h+8) mid) (h+11) (separator-1)
      0<n ∧ Holds out (h-4) sixthPath ∧
      parseForward 52 out (h-4)=some ("3.$coalesced.0.inc",12) ∧
      decode 12 (readCells out (separator+1)
        (encode (List.ofFn result.bank) ++ (encode rest ++ [true,false,false])).length)=
          some (List.ofFn result.bank,encode rest ++ [true,false,false]) ∧
      result.state=9 ∧ (target.system.step ⟨8,graphBank⟩).2=[] ∧
      head=(if (separator-(h+12)).toNat=0 then h+7 else separator-3) ∧
      silentSegment machine (cfg 273 (h+8) t) (cfg 83 head out) n := by
  obtain ⟨n,mid,head,hn,hpath,hparse,hbank,hleft,hhead,hseg⟩ :=
    positive_then_prepare h b separator t values v (z::rest) hlen hlong
      path left mark z1 z2 ones sep right bank
  let out := fillRange (setAt (h+8) mid) (h+11) (separator-1)
  have hp : Holds out (separator+1) (encode values) :=
    holds_prefix_word out (separator+1) (encode values) _ hbank
  have hu := holds_append_tail out (separator+1) (encode values)
    (encode (v::z::rest) ++ [true,false,false]) hbank
  have hmatch := decoded_matches_row8 out (separator+1) values v z rest graphBank hlen hgraph hp hu
  exact ⟨n,mid,head,hn,hpath,hparse,hmatch.1,hmatch.2.1,hmatch.2.2,hhead,hseg⟩

#print axioms positive_then_prepare_control_suffix_frame
#print axioms positive_then_prepare_control
#print axioms positive_then_prepare_graph
#print axioms positive_then_prepare
end Shared.Beeping.NPcoNP.NativeRow8PositivePrepare
