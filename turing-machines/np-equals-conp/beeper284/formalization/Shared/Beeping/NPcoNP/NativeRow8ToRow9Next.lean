import Shared.Beeping.NPcoNP.NativeRow8ToRow9Increment
import Shared.Beeping.NPcoNP.NativeRow9Continuation
import Shared.Beeping.NPcoNP.NativeSegmentSupport

/-! Conditional two-graph-step physical progress to the next row-8 entry. -/
namespace Shared.Beeping.NPcoNP.NativeRow8ToRow9Next
open Shared.Beeping Shared.Beeping.Machines PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeRow8PositiveRedispatch
open Shared.Beeping.NPcoNP.Native275BankEntry
open Shared.Beeping.NPcoNP.NativeRow9IncrementReturn
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.NativeFourthNextPath
open Shared.Beeping.NPcoNP.NativeFifthNextPath
open Shared.Beeping.NPcoNP.NativeSegmentSupport
open Shared.Beeping.NPcoNP.NativeRow9Continuation
open Shared.Beeping.NPcoNP.Bootstrap284BankDecode
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 20000000

/-- The reverse-oriented shift suffix has the same length as the bank encoding. -/
theorem shift_suffix_length (vs : List Nat) :
    (vs.flatMap (fun z => false :: List.replicate (z+1) true)).length = (encode vs).length := by
  induction vs with
  | nil => rfl
  | cons x xs ih => simp [encode,block,ih]; omega

theorem positive_row8_then_row9_next_entry_full (h bound separator : Int) (t : Int → Bool)
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
      (∀ q, q<h-4 → out q=false) ∧ out (h+7)=false ∧
      (∀ q, h+7<q → q<separator-1 → out q=false) ∧
      out (separator-1)=true ∧ out separator=false ∧
      (∃ endBound, ∀ q, endBound≤q → out q=false) ∧
      (∀ q, separator+1+(((encode (a::b::prior) ++ (encode ((v+1)::z::rest) ++ [false,false])).length : Nat):Int)≤q → out q=t q) ∧
      Holds out (separator+1) (encode (arrayBank second.bank) ++ tail) ∧
      first.state=9 ∧ second.state=8 ∧
      (target.system.step ⟨8,graphBank⟩).2=[] ∧ (target.system.step ⟨9,first.bank⟩).2=[] ∧
      decode 12 (readCells out (separator+1)
        (encode (arrayBank second.bank) ++ tail).length)=some (arrayBank second.bank,tail) ∧
      silentSegment machine (cfg 273 (h+8) t) (cfg 54 (h+7) out) n := by
  dsimp only
  have hten : (a::b::prior).length=10 := by simp [hlen]
  obtain ⟨n,mid,hn,hpath,hparse,hbank,hleft,h9,h10,hrun,hsep,htail,hseg⟩ :=
    positive_then_redispatch_suffix_frame h bound separator t (a::b::prior) v (z::rest) hten hlong
      path left mark z1 z2 ones sep right bank
  let out := fillRange (setAt (h+8) mid) (h+11) (separator-1)
  let final := clearAt (h+8) out
  let pos := separator+1+((a+2 : Nat):Int)
  let bits := encode prior ++ (encode (v::z::rest) ++ [true,false,false])
  have hb : Holds final (separator+1) (block a ++ (block b ++ bits)) := by
    simpa [encode,bits,List.append_assoc] using hbank
  have hs := scan_to262 h separator final a b bits (by omega) h9 h10 hrun hsep hb
  let k := (separator-(h+11)).toNat
  have hs' : silentSegment machine (cfg 275 (h+9) final)
      (cfg 262 (pos-2) (clearAt pos final)) (k+a+7) := by simpa only [pos,k] using hs
  let suffix := prior ++ [v,z] ++ rest ++ [0]
  have hbankall : Holds final (separator+1) (encode (a::b::suffix) ++ [false]) := by
    simpa [suffix,encode_append,encode,block,List.append_assoc] using hbank
  have h8 : final (h+8)=false := by simp [final,clearAt]
  obtain ⟨m,e,hm,he,hword,hmark,hframe,hinc⟩ := increment_then_return_full h separator final a b suffix
    hlong h8 h9 h10 hrun hsep hbankall
  have hinc' : silentSegment machine (cfg 262 (pos-2) (clearAt pos final))
      (cfg 1 (h+7) e.tape) m := by
    simpa only [pos] using hinc
  have hgraphstep := row8_then9_array graphBank a b prior v z hlen hgraph
  obtain ⟨hfirst,hsecond,harr,hev1,hev2⟩ := hgraphstep
  have henc : encode ((a::(b+1)::prior) ++ [v,z]) ++ (encode rest ++ [true,false]) =
      encode (a::(b+1)::suffix) := by
    simp [suffix,encode_append,encode,block,List.append_assoc]
  have hout : Holds e.tape (separator+1)
      (encode (arrayBank (target.system.step ⟨9,(target.system.step ⟨8,graphBank⟩).1.bank⟩).1.bank) ++
        (encode rest ++ [true,false])) := by
    rw [harr,henc]
    exact hword
  have hlength : (arrayBank (target.system.step ⟨9,(target.system.step ⟨8,graphBank⟩).1.bank⟩).1.bank).length=12 := by
    simp [arrayBank]
  have hdecode := decode_encode
    (arrayBank (target.system.step ⟨9,(target.system.step ⟨8,graphBank⟩).1.bank⟩).1.bank)
    (encode rest ++ [true,false])
  rw [hlength] at hdecode
  have pre := segAdd machine _ _ _ n (k+a+7) hseg hs'
  have all := segAdd machine _ _ _ (n+(k+a+7)) m pre hinc'
  have hframe' : ∀ q, q≠h+10 → q<separator+1 → e.tape q=final q := by
    intro q hne hq
    apply hframe q hne
    left
    dsimp [pos]
    omega
  have hepath : Holds e.tape (h-4) sixthPath := by
    apply holds_transport final e.tape _ _ hpath
    intro q hq hq'
    symm
    apply hframe' q <;> simp [sixthPath] at hq' <;> omega
  have heleft : ∀ q, q<h-4 → e.tape q=false := by
    intro q hq
    rw [hframe' q (by omega) (by omega)]
    exact hleft q hq
  have he8 : e.tape (h+8)=false := by rw [hframe' _ (by omega) (by omega)]; exact h8
  have he9 : e.tape (h+9)=false := by rw [hframe' _ (by omega) (by omega)]; exact h9
  have hecontrol : ∀ q, h+10≤q → q<separator → e.tape q=true := by
    intro q hq hq'
    by_cases heq : q=h+10
    · simpa [heq] using hmark
    · rw [hframe' q heq (by omega)]
      exact hrun q (by omega) hq'
  have hesep : e.tape separator=false := by rw [hframe' _ (by omega) (by omega)]; exact hsep
  obtain ⟨endBound,hend⟩ := silent_right_blank machine (cfg 273 (h+8) t)
    (cfg 1 (h+7) e.tape) (n+(k+a+7)+m) ⟨bound,right⟩ all
  obtain ⟨p,u,hp,hupath,huleft,huz7,hugap,humark,huframe,huseg⟩ :=
    carry_to_row8_entry_full h endBound separator e.tape hlong hepath heleft he8 he9 hecontrol hesep hend
  have huword : Holds u (separator+1)
      (encode (arrayBank (target.system.step ⟨9,(target.system.step ⟨8,graphBank⟩).1.bank⟩).1.bank) ++
        (encode rest ++ [true,false])) := by
    apply holds_transport e.tape u _ _ hout
    intro q hq hq'
    exact (huframe q (by omega)).symm
  have hread := read_of_holds u (separator+1) _ huword
  rw [←hread] at hdecode
  have full := segAdd machine _ _ _ (n+(k+a+7)+m) p all huseg
  have husep : u separator=false := by rw [huframe _ (by omega)]; exact hesep
  obtain ⟨outBound,houtblank⟩ := silent_right_blank machine (cfg 273 (h+8) t)
    (cfg 54 (h+7) u) (n+(k+a+7)+m+p) ⟨bound,right⟩ full
  let boundary := separator+1+(((encode (a::b::prior) ++ (encode ((v+1)::z::rest) ++ [false,false])).length : Nat):Int)
  have hboundary : separator+1+((encode (a::b::prior)).length : Int)+3+
      ((List.replicate v true ++ (z::rest).flatMap (fun n => false :: List.replicate (n+1) true)).length : Int) ≤ boundary := by
    dsimp [boundary]
    have hr := shift_suffix_length (z::rest)
    simp only [List.length_append,List.length_replicate,hr]
    simp [encode,block_length]
    omega
  have hstop : pos+1+((b+(encode suffix).length : Nat):Int)<boundary := by
    dsimp [boundary,pos,suffix]
    simp [encode_append,encode,block_length]
    omega
  have hboundarySep : separator+1≤boundary := by dsimp [boundary]; omega
  have hsuffix : ∀ q, boundary≤q → u q=t q := by
    intro q hq
    rw [huframe q (by omega)]
    rw [hframe q (by omega) (Or.inr (by omega))]
    exact htail q (by omega)
  exact ⟨n+(k+a+7)+m+p,u,by omega,hupath,huleft,huz7,hugap,humark,husep,
    ⟨outBound,houtblank⟩,hsuffix,huword,hfirst,hsecond,hev1,hev2,hdecode,full⟩

theorem positive_row8_then_row9_next_entry (h bound separator : Int) (t : Int → Bool)
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
      first.state=9 ∧ second.state=8 ∧
      (target.system.step ⟨8,graphBank⟩).2=[] ∧ (target.system.step ⟨9,first.bank⟩).2=[] ∧
      decode 12 (readCells out (separator+1)
        (encode (arrayBank second.bank) ++ tail).length)=some (arrayBank second.bank,tail) ∧
      silentSegment machine (cfg 273 (h+8) t) (cfg 54 (h+7) out) n := by
  obtain ⟨n,out,hn,hpath,_,_,_,_,_,_,_,_,hfirst,hsecond,hev1,hev2,hdecode,hseg⟩ :=
    positive_row8_then_row9_next_entry_full h bound separator t a b prior v z rest graphBank
      hlen hgraph hlong path left mark z1 z2 ones sep right bank
  exact ⟨n,out,hn,hpath,hfirst,hsecond,hev1,hev2,hdecode,hseg⟩

#print axioms positive_row8_then_row9_next_entry_full
#print axioms positive_row8_then_row9_next_entry
end Shared.Beeping.NPcoNP.NativeRow8ToRow9Next
