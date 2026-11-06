import Shared.Beeping.NPcoNP.NativeGrammarAdministrativeDispatch
import Shared.Beeping.NPcoNP.NativeGrammarSelectorDispatch
import Shared.Beeping.NPcoNP.NativeCarryExactControl

/-! A supplied `_continue.1` grammar leaf clears its final one, returns to
the previous marked one, and reselects a supplied prefix-plus-zeros word. -/
namespace Shared.Beeping.NPcoNP.NativeContinueOneGeneric
open PASoundness Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfMarkerExact
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeIncSelected
open Shared.Beeping.NPcoNP.NativeGrammarAdministrativeDispatch
open Shared.Beeping.NPcoNP.NativeGrammarSelectorDispatch
open Shared.Beeping.NPcoNP.NativeSelectorPrefixReturn
open Shared.Beeping.NPcoNP.NativeCarryExactControl
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.Grammar284ExpansionPaths
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- A supplied continuation leaf with a marked preceding one and zeros to
its right silently returns to the parser with the corresponding carried-prefix
word. The exact grammar restart index is a separate finite obligation. -/
theorem continue_one_to_candidate_exact (e : Expansion)
    (expanded : expand producerGrammar.nodes 53 (.node producerGrammar.root)
      [true,true,false] [] {} = some e)
    (entry : Path × String) (member : entry ∈ e.leaves.toList)
    (name : entry.2="_continue.1") (origin separator : Int) (t : Int → Bool)
    (i zeros : Nat) (ilo : 1 ≤ i) (ihi : i+1<entry.1.length)
    (word : Holds t origin entry.1) (left : ∀ q, q<origin → t q=false)
    (one : t (origin+(i : Int))=true)
    (inside : ∀ q, origin+(i : Int)<q → q<origin+((entry.1.length : Nat) : Int)-1 → t q=false)
    (gap : ∀ q, origin+((entry.1.length : Nat) : Int)-1<q → q<separator-1 → t q=false)
    (room : origin+(i : Int)+(zeros : Int)<separator-1)
    (hspace : origin+((entry.1.length : Nat) : Int)+1≤separator)
    (right : t (separator-1)=true) (sep : t separator=false) :
    ∃ (steps : Nat) (out : Int → Bool), 0<steps ∧
      Holds out origin (entry.1.take i ++ true::List.replicate zeros false) ∧
      (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+(((entry.1.take i ++ true::List.replicate zeros false).length : Nat) : Int)≤q →
        q<separator-1 → out q=false) ∧
      out (separator-1)=true ∧ out separator=false ∧ (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) steps := by
  let path := entry.1
  let last := origin+((path.length : Nat) : Int)-1
  let mark := origin+(i : Int)
  let out := clearAt last t
  have walk := expanded_leaf_follows e expanded entry member
  have count : path.count false≤11 := (prepared_path_bound path (.op entry.2) walk).2
  obtain ⟨first,tail⟩ := prepared_head_tail t origin path entry.2 walk word
  have target : administrativeEntry entry.2=some 97 := by rw [name]; rfl
  have dispatch := expanded_administrative_dispatch e expanded entry member 97 target (origin+1) t tail
  have listed : entry ∈ Grammar284.ExpandSteps.ProducerTrace.traceState557.acc.leaves.toList := by
    have he := expanded
    rw [Grammar284.ExpandSteps.ProducerTrace.producerExpand] at he
    cases he
    exact member
  obtain ⟨_,_,hlast,_⟩ := administrative_path_checked entry listed 97 target
  have htailLen : entry.1.tail.dropLast.length+1=entry.1.tail.length := by
    have he : entry.1.tail.dropLast ++ [true]=entry.1.tail :=
      List.dropLast_append_getLast? true (by simp [hlast])
    have hh := congrArg List.length he
    simpa using hh
  have hpathLen : entry.1.tail.length+1=entry.1.length := by
    obtain ⟨raw,he,_⟩ := walk
    rw [he]
    simp [preparedPrefix]
  have hlastPos : origin+1+((entry.1.tail.dropLast.length : Nat) : Int)=last := by dsimp [last,path]; omega
  have hdispatch : silentSegment machine (cfg 93 (origin+1) t) (cfg 97 (last-1) out)
      (entry.1.tail.dropLast.length+1) := by
    rw [hlastPos] at dispatch
    have he' : (cfg (93 : Fin 284) last t).write false=out := rfl
    rw [he'] at dispatch
    exact dispatch
  have hmark : out mark=true := by
    simpa [out,clearAt,mark,last,path,show origin+(i : Int)≠origin+((entry.1.length : Nat) : Int)-1 by omega] using one
  have hbetween : ∀ q, mark<q → q≤last-1 → out q=false := by
    intro q hq hq'
    simpa [out,clearAt,show q≠last by omega] using inside q (by simpa only [mark] using hq) (by dsimp [last,path] at *; omega)
  let d := (last-1-mark).toNat
  have hd : last-1-(d : Int)=mark := by
    have hd' : (d : Int)=last-1-mark := Int.toNat_of_nonneg (by dsimp [last,mark,path]; omega)
    omega
  have h97 := scan97_corridor d (last-1) mark out hd hmark hbetween
  let pref := path.take i
  have hpref : Holds t origin pref := by
    apply holds_prefix t origin (path.take i) (path.drop i)
    simpa only [List.take_append_drop] using word
  have hprefout : Holds out origin pref := by
    apply holds_transport t out origin pref hpref
    intro q hq hq'
    simp [out,clearAt,show q≠last by simp [pref,List.length_take_of_le (by omega : i ≤ path.length)] at hq'; dsimp [last,mark]; omega]
  have hleftout : ∀ q, q<origin → out q=false := by
    intro q hq
    simpa [out,clearAt,show q≠last by dsimp [last,path]; omega] using left q hq
  have hfirstout : out origin=true := by
    simpa [out,clearAt,show origin≠last by dsimp [last,path]; omega] using first
  have hcount : pref.count false≤11 := by
    have hc := congrArg (List.count false) (List.take_append_drop i path)
    simp only [List.count_append] at hc
    dsimp [pref]
    omega
  obtain ⟨b,hb,hselector⟩ := selector_returns_to_origin out origin pref hcount hprefout hleftout hfirstout
  have hlen : pref.length=i := by simp [pref,List.length_take_of_le (by omega : i ≤ path.length)]
  have hstart : origin+((pref.length : Nat) : Int)-1=mark-1 := by simp only [hlen,mark]
  rw [hstart] at hselector
  have hunchanged : ∀ q, q<mark → out q=t q := by
    intro q hq
    simp [out,clearAt,show q≠last by dsimp [last,mark,path] at *; omega]
  have houtgap : ∀ q, mark<q → q<separator-1 → out q=false := by
    intro q hq hq'
    by_cases he : q=last
    · simp [out,clearAt,he]
    · have hz : t q=false := by
        by_cases hh : q<last
        · exact inside q (by simpa only [mark] using hq) (by simpa only [last,path] using hh)
        · exact gap q (by dsimp [last,path] at *; omega) hq'
      simpa [out,clearAt,he] using hz
  have hnew := control_word_of_frame t out origin mark separator path zeros (by dsimp [mark]; omega)
    (by dsimp [mark,path]; omega) word hunchanged hmark houtgap (by simpa [mark] using room)
  have hright : out (separator-1)=true := by
    simpa [out,clearAt,show separator-1≠last by dsimp [last,mark,path] at *; omega] using right
  have hsep : out separator=false := by
    simpa [out,clearAt,show separator≠last by dsimp [last,mark,path] at *; omega] using sep
  have hbank : ∀ q, separator≤q → out q=t q := by
    intro q hq
    simp [out,clearAt,show q≠last by dsimp [last,mark,path] at *; omega]
  have hchain := segAdd machine _ _ _ (entry.1.tail.dropLast.length+1) (d+1) hdispatch h97
  have hgapfinal : ∀ q, origin+(((entry.1.take i ++ true::List.replicate zeros false).length : Nat) : Int)≤q →
      q<separator-1 → out q=false := by
    intro q hq hq'
    apply houtgap q _ hq'
    simp only [List.length_append,List.length_take_of_le (by omega : i≤entry.1.length),
      List.length_cons,List.length_replicate] at hq
    dsimp [mark]
    omega
  refine ⟨(entry.1.tail.dropLast.length+1)+(d+1)+b,out,by omega,?_,hleftout,hgapfinal,hright,hsep,hbank,?_⟩
  · have he : (mark-origin).toNat=i := by simp [mark]
    simpa only [he,path] using hnew
  · exact segAdd machine _ _ _ _ _ hchain hselector

/-- Original interface, retaining the segment and tape-word conclusions. -/
theorem continue_one_to_candidate (e : Expansion)
    (expanded : expand producerGrammar.nodes 53 (.node producerGrammar.root)
      [true,true,false] [] {} = some e)
    (entry : Path × String) (member : entry ∈ e.leaves.toList)
    (name : entry.2="_continue.1") (origin separator : Int) (t : Int → Bool)
    (i zeros : Nat) (ilo : 1 ≤ i) (ihi : i+1<entry.1.length)
    (word : Holds t origin entry.1) (left : ∀ q, q<origin → t q=false)
    (one : t (origin+(i : Int))=true)
    (inside : ∀ q, origin+(i : Int)<q → q<origin+((entry.1.length : Nat) : Int)-1 → t q=false)
    (gap : ∀ q, origin+((entry.1.length : Nat) : Int)-1<q → q<separator-1 → t q=false)
    (room : origin+(i : Int)+(zeros : Int)<separator-1)
    (hspace : origin+((entry.1.length : Nat) : Int)+1≤separator)
    (right : t (separator-1)=true) (sep : t separator=false) :
    ∃ (steps : Nat) (out : Int → Bool), 0<steps ∧
      Holds out origin (entry.1.take i ++ true::List.replicate zeros false) ∧
      out (separator-1)=true ∧ out separator=false ∧ (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) steps := by
  obtain ⟨steps,out,hs,hw,_,_,hr,hsep,hbank,hseg⟩ := continue_one_to_candidate_exact e expanded entry member name origin separator t i zeros ilo ihi word left one inside gap room hspace right sep
  exact ⟨steps,out,hs,hw,hr,hsep,hbank,hseg⟩

#print axioms continue_one_to_candidate_exact
#print axioms continue_one_to_candidate
end Shared.Beeping.NPcoNP.NativeContinueOneGeneric
