import Shared.Beeping.NPcoNP.NativeRow8ToRow9Next
import Shared.Beeping.NPcoNP.Native54ReturnTo273

/-! Composed positive row-8/row-9 progress through the next prepared entry. -/
namespace Shared.Beeping.NPcoNP.NativeRow8ToRow9Prepared
open Shared.Beeping Shared.Beeping.Machines PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeFourthNextPath
open Shared.Beeping.NPcoNP.NativeSegmentSupport
open Shared.Beeping.NPcoNP.NativeRow8ToRow9Next
open Shared.Beeping.NPcoNP.Native54ReturnTo273
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.Bootstrap284BankDecode
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 20000000

theorem positive_row8_then_row9_prepared_suffix_frame (h bound separator : Int) (t : Int → Bool)
    (a b : Nat) (prior : List Nat) (v z : Nat) (rest : List Nat) (graphBank : Bank 12)
    (hlen : prior.length=8)
    (hgraph : arrayBank graphBank=(a::b::prior) ++ [v+1,z])
    (hlong : h+12≤separator) (path : Holds t (h-4) fifthPath)
    (left : ∀ q, q<h-4 → t q=false)
    (mark : t (h+7)=true) (z1 : t (h+8)=false) (z2 : t (h+9)=false)
    (ones : ∀ q, h+10≤q → q<separator → t q=true)
    (sep : t separator=false) (right : ∀ q, bound≤q → t q=false)
    (bank : Holds t (separator+1)
      (encode (a::b::prior) ++ (encode ((v+1)::z::rest) ++ [false,false]))) :
    let first := (target.system.step ⟨8,graphBank⟩).1
    let second := (target.system.step ⟨9,first.bank⟩).1
    let tail := encode rest ++ [true,false]
    ∃ (n : Nat) (out : Int → Bool), 0<n ∧ Holds out (h-4) fifthPath ∧
      (∀ q, q<h-4 → out q=false) ∧ out (h+7)=true ∧
      (out (h+8)=false ∧ out (h+9)=false) ∧
      (∀ q, h+10≤q → q<separator → out q=true) ∧ out separator=false ∧
      (∃ endBound, ∀ q, endBound≤q → out q=false) ∧
      (∀ q, separator+1+(((encode (a::b::prior) ++ (encode ((v+1)::z::rest) ++ [false,false])).length : Nat):Int)≤q → out q=t q) ∧
      Holds out (separator+1) (encode (arrayBank second.bank) ++ tail) ∧
      first.state=9 ∧ second.state=8 ∧
      (target.system.step ⟨8,graphBank⟩).2=[] ∧ (target.system.step ⟨9,first.bank⟩).2=[] ∧
      decode 12 (readCells out (separator+1)
        (encode (arrayBank second.bank) ++ tail).length)=some (arrayBank second.bank,tail) ∧
      silentSegment machine (cfg 273 (h+8) t) (cfg 273 (h+8) out) n := by
  dsimp only
  obtain ⟨n,midTape,hn,hvpath,hvleft,hv7,hvgap,hvmark,hvsep,hvblank,hvframe,hvbank,
    hfirst,hsecond,hev1,hev2,hdecode,hseg⟩ :=
    positive_row8_then_row9_next_entry_full h bound separator t a b prior v z rest graphBank
      hlen hgraph hlong path left mark z1 z2 ones sep right bank
  let u := fillRange (setAt (h+7) midTape) (h+10) (separator-1)
  obtain ⟨m,hm,hupath,huleft,hu7,hu8,hu9,hones,husep,huframe,huseg⟩ :=
    prepare_and_enter h separator midTape hlong hvpath hvleft hv7 hvgap hvmark hvsep
  have hubank : Holds u (separator+1)
      (encode (arrayBank (target.system.step ⟨9,(target.system.step ⟨8,graphBank⟩).1.bank⟩).1.bank) ++
        (encode rest ++ [true,false])) := by
    apply holds_transport midTape u _ _ hvbank
    intro q hq _
    exact (huframe q (by omega)).symm
  have hlength : (arrayBank (target.system.step ⟨9,(target.system.step ⟨8,graphBank⟩).1.bank⟩).1.bank).length=12 := by
    simp [arrayBank]
  have hdecode' := decode_encode
    (arrayBank (target.system.step ⟨9,(target.system.step ⟨8,graphBank⟩).1.bank⟩).1.bank)
    (encode rest ++ [true,false])
  rw [hlength] at hdecode'
  have hread := read_of_holds u (separator+1) _ hubank
  rw [←hread] at hdecode'
  have all := segAdd machine _ _ _ n m hseg huseg
  obtain ⟨endBound,hend⟩ := silent_right_blank machine (cfg 273 (h+8) t)
    (cfg 273 (h+8) u) (n+m) ⟨bound,right⟩ all
  have hframe : ∀ q, separator+1+(((encode (a::b::prior) ++ (encode ((v+1)::z::rest) ++ [false,false])).length : Nat):Int)≤q → u q=t q := by
    intro q hq
    change (fillRange (setAt (h+7) midTape) (h+10) (separator-1)) q=t q
    rw [huframe q (by omega)]
    exact hvframe q hq
  exact ⟨n+m,u,by omega,hupath,huleft,hu7,⟨hu8,hu9⟩,hones,husep,
    ⟨endBound,hend⟩,hframe,hubank,hfirst,hsecond,hev1,hev2,hdecode',all⟩

theorem positive_row8_then_row9_prepared (h bound separator : Int) (t : Int → Bool)
    (a b : Nat) (prior : List Nat) (v z : Nat) (rest : List Nat) (graphBank : Bank 12)
    (hlen : prior.length=8)
    (hgraph : arrayBank graphBank=(a::b::prior) ++ [v+1,z])
    (hlong : h+12≤separator) (path : Holds t (h-4) fifthPath)
    (left : ∀ q, q<h-4 → t q=false)
    (mark : t (h+7)=true) (z1 : t (h+8)=false) (z2 : t (h+9)=false)
    (ones : ∀ q, h+10≤q → q<separator → t q=true)
    (sep : t separator=false) (right : ∀ q, bound≤q → t q=false)
    (bank : Holds t (separator+1)
      (encode (a::b::prior) ++ (encode ((v+1)::z::rest) ++ [false,false]))) :
    let first := (target.system.step ⟨8,graphBank⟩).1
    let second := (target.system.step ⟨9,first.bank⟩).1
    let tail := encode rest ++ [true,false]
    ∃ (n : Nat) (out : Int → Bool), 0<n ∧ Holds out (h-4) fifthPath ∧
      (∀ q, q<h-4 → out q=false) ∧ out (h+7)=true ∧
      (out (h+8)=false ∧ out (h+9)=false) ∧
      (∀ q, h+10≤q → q<separator → out q=true) ∧ out separator=false ∧
      (∃ endBound, ∀ q, endBound≤q → out q=false) ∧
      Holds out (separator+1) (encode (arrayBank second.bank) ++ tail) ∧
      first.state=9 ∧ second.state=8 ∧
      (target.system.step ⟨8,graphBank⟩).2=[] ∧ (target.system.step ⟨9,first.bank⟩).2=[] ∧
      decode 12 (readCells out (separator+1)
        (encode (arrayBank second.bank) ++ tail).length)=some (arrayBank second.bank,tail) ∧
      silentSegment machine (cfg 273 (h+8) t) (cfg 273 (h+8) out) n := by
  obtain ⟨n,out,hn,hpath,hleft,h7,h89,hones,hsep,hblank,_,hbank,
    hfirst,hsecond,hev1,hev2,hdecode,hseg⟩ :=
    positive_row8_then_row9_prepared_suffix_frame h bound separator t a b prior v z rest graphBank
      hlen hgraph hlong path left mark z1 z2 ones sep right bank
  exact ⟨n,out,hn,hpath,hleft,h7,h89,hones,hsep,hblank,hbank,
    hfirst,hsecond,hev1,hev2,hdecode,hseg⟩

#print axioms positive_row8_then_row9_prepared_suffix_frame
#print axioms positive_row8_then_row9_prepared
end Shared.Beeping.NPcoNP.NativeRow8ToRow9Prepared
