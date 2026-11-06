import Shared.Beeping.NPcoNP.Grammar284HalfZeroSuccessor
import Shared.Beeping.NPcoNP.Grammar284HalfGraphZero
import Shared.Beeping.NPcoNP.Grammar284HalfPreparation
import Shared.Beeping.NPcoNP.Grammar284ReservedWindow
import Shared.Beeping.NPcoNP.NativeHalfZeroPreparedGeneral
import Shared.Beeping.NPcoNP.NativeAllBankSelectedValue
import Shared.Beeping.NPcoNP.Grammar284OrdinaryPhysical

/-! A zero native HALF preserves a supplied reserve and infinite blank tail,
with arbitrary preceding bank values. Reachability remains separate. -/
namespace Shared.Beeping.NPcoNP.Grammar284HalfZeroReserved
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeGrammarPreterminalDispatch
open Shared.Beeping.NPcoNP.NativeAllBankSelectedValue
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.NativeHalfZeroGeneralScan
open Shared.Beeping.NPcoNP.Coalescing284Map
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
open Shared.Beeping.NPcoNP.Grammar284ExpansionPaths
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
open Shared.Beeping.NPcoNP.Grammar284HalfZeroShape
open Shared.Beeping.NPcoNP.Grammar284HalfGraphZero
open Shared.Beeping.NPcoNP.Grammar284HalfPreparation
open Shared.Beeping.NPcoNP.Grammar284HalfZeroSuccessor
open Shared.Beeping.NPcoNP.Grammar284OrdinaryPhysical
open Shared.Beeping.NPcoNP.Grammar284ReservedWindow
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 30000000

theorem prepared_zero_step (row : Fin 185) (path : Path) (name : String) (graph : Bank 12)
    (values rest more : List Nat)
    (leaf : graphLeaf row=some (path,name)) (entry : operationEntry name=some (entryAt values.length))
    (hlen : values.length≤3) (layout : arrayBank graph=values++0::rest)
    (origin h separator : Int) (t : Int → Bool)
    (hentry : h=origin+((path.length : Nat) : Int)) (space : h+4≤separator)
    (room : origin+59≤separator) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false) (marker : t h=true) (z1 : t (h+1)=false)
    (control : ∀ q, h+2≤q → q<separator → t q=true) (sep : t separator=false)
    (bank : Holds t (separator+1) (encode (arrayBank graph++more) ++ [true,false]))
    (tail : ∀ q, separator+2+((encode (arrayBank graph++more)).length : Int)≤q → t q=false) :
    ∃ steps out, 0<steps ∧ (target.system.step ⟨row,graph⟩).2=[] ∧
      ReservedWindow (target.system.step ⟨row,graph⟩).1.state
        (target.system.step ⟨row,graph⟩).1.bank origin separator out ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) steps := by
  have hc : values.length=0 ∨ values.length=1 ∨ values.length=2 ∨ values.length=3 := by omega
  have hq : entryAt values.length=74 ∨ entryAt values.length=75 ∨ entryAt values.length=76 ∨ entryAt values.length=77 := by
    rcases hc with hc | hc | hc | hc <;> simp [hc,entryAt]
  let n : Fin 12 := ⟨values.length,by omega⟩
  have hreg : expectedRegister (entryAt values.length)=some (arrayToSuffix n) := by
    rcases hc with hc | hc | hc | hc <;> simp [hc,entryAt,expectedRegister,arrayToSuffix,n]
  obtain ⟨hshape,hrightmost,hlast,dst,hsucc,htarget⟩ :=
    half_zero_shapes row path name (entryAt values.length) leaf entry hq
  have hvalue := selected_graph_value graph n values rest 0 rfl layout
  have hstep := half_zero_step row path name (entryAt values.length) (arrayToSuffix n) leaf entry hreg graph hvalue.symm
  have hbank : Holds t (separator+1) (encode values ++ ([true,false] ++ (encode (rest++more) ++ [true,false]))) := by
    rw [layout] at bank
    simpa [encode_append,encode,block,List.append_assoc] using bank
  have hreturn : t (h-1)=false →
      ∃ steps : Nat, 0<steps ∧ Holds (clearAt h t) (separator+1) (encode (arrayBank graph++more) ++ [true,false]) ∧
      (∀ q, q≠h → clearAt h t q=t q) ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 1 (h-2) (clearAt h t)) steps := by
    intro lastZero
    have hh := Shared.Beeping.NPcoNP.NativeHalfZeroPreparedGeneral.prepared_zero_to1 row path name values leaf entry hlen
      origin h separator t (encode (rest++more) ++ [true,false]) hentry (by omega) word marker lastZero z1 control sep hbank
    simpa [layout,encode_append,encode,block,List.append_assoc] using hh
  obtain ⟨next,nextName,a,mid,hnext,ha,hw,hl,hgap,hsep,hmark,houtbank,houtframe,hsegment⟩ :=
    prepared_zero_to_first_successor_frame row dst path name leaf hshape hrightmost hlast hsucc
      origin h separator t (encode (arrayBank graph++more) ++ [true,false]) hentry space (by omega)
      word left marker z1 control sep bank hreturn
  obtain ⟨total,last,out,htotal,hgraph,hout,houtleft,houtgap,houtmark,houtsep,hbank',hframe,hfinal⟩ :=
    finish_contraction_frame (cfg 93 (origin+1) t) a mid origin separator dst next nextName target.code[row].no
      htarget hnext ha hsegment hw hl hgap (by omega) hmark hsep _ houtbank
  have htail : ∀ q, separator+2+((encode (arrayBank graph++more)).length : Int)≤q → out q=false := by
    intro q hq
    rw [hframe q (by omega),houtframe q (by omega)]
    exact tail q hq
  rw [hstep]
  refine ⟨total,out,htotal,rfl,?_,hfinal⟩
  exact ⟨last.1,last.2,more,by simpa using hgraph,room,hout,houtleft,houtgap,houtmark,houtsep,hbank',htail⟩

/-- From a supplied reserved parser window, a zero selected HALF matches its
graph step and preserves a reserved infinite-tail window. -/
theorem zero_step (row : Fin 185) (path : Path) (name : String) (graph : Bank 12)
    (values rest : List Nat) (origin separator : Int) (t : Int → Bool)
    (window : ReservedWindow row graph origin separator t)
    (leaf : graphLeaf row=some (path,name)) (entry : operationEntry name=some (entryAt values.length))
    (hlen : values.length≤3) (layout : arrayBank graph=values++0::rest) :
    ∃ steps out, 0<steps ∧ (target.system.step ⟨row,graph⟩).2=[] ∧
      ReservedWindow (target.system.step ⟨row,graph⟩).1.state
        (target.system.step ⟨row,graph⟩).1.bank origin separator out ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) steps := by
  obtain ⟨path',name',more,hleaf,room,word,left,gap,right,sep,bank,tail⟩ := window
  have he : (path',name')=(path,name) := Option.some.inj (hleaf.symm.trans leaf)
  cases Prod.mk.inj he with
  | intro hp hn =>
    subst path'
    subst name'
    have walk : PreparedWalk path (.op name) :=
      expanded_leaf_follows traceState557.acc producerExpand (path,name) (graph_leaf_member row path name leaf)
    have hpathlen : path.length≤55 := (prepared_path_bound path (.op name) walk).1
    let h := origin+((path.length : Nat) : Int)
    have space : h+4≤separator := by dsimp [h]; omega
    have hgap : ∀ p, h≤p → p<separator-1 → t p=false := by
      intro p hp hp'
      exact gap p (by dsimp [h] at hp; omega) hp'
    have hc : values.length=0 ∨ values.length=1 ∨ values.length=2 ∨ values.length=3 := by omega
    have hq : entryAt values.length=74 ∨ entryAt values.length=75 ∨ entryAt values.length=76 ∨ entryAt values.length=77 := by
      rcases hc with hc | hc | hc | hc <;> simp [hc,entryAt]
    obtain ⟨a,mid,ha,hw,hl,hm,hz,hcontrol,hsep,hframe,hsegment⟩ :=
      prepare_from_parser row path name leaf (entryAt values.length) hq entry origin h separator t
        rfl (by omega) word left hgap right sep
    have hbank : Holds mid (separator+1) (encode (arrayBank graph++more) ++ [true,false]) := by
      apply holds_transport t mid (separator+1) _ bank
      intro p hp _
      exact (hframe p (by omega)).symm
    have htail : ∀ p, separator+2+((encode (arrayBank graph++more)).length : Int)≤p → mid p=false := by
      intro p hp
      rw [hframe p (by omega)]
      exact tail p hp
    obtain ⟨b,out,hb,hevent,hwindow,hrest⟩ :=
      prepared_zero_step row path name graph values rest more leaf entry hlen layout origin h separator mid
        rfl space room hw hl hm hz hcontrol hsep hbank htail
    exact ⟨a+b,out,by omega,hevent,hwindow,segAdd machine _ _ _ a b hsegment hrest⟩

#print axioms zero_step
end Shared.Beeping.NPcoNP.Grammar284HalfZeroReserved
