import Shared.Beeping.NPcoNP.Grammar284HalfPositivePrepared
import Shared.Beeping.NPcoNP.Grammar284HalfEvenGraph
import Shared.Beeping.NPcoNP.Grammar284HalfOddGraph
import Shared.Beeping.NPcoNP.Grammar284HalfPreparation
import Shared.Beeping.NPcoNP.Grammar284ReservedWindow
import Shared.Beeping.NPcoNP.NativeAllBankSelectedValue
import Shared.Beeping.NPcoNP.Grammar284BankCorrespondence
import Shared.Beeping.NPcoNP.Grammar284OrdinaryPhysical

/-! Every positive HALF preserves a supplied reserved infinite-tail window.
Reachable initialization is a separate obligation. -/
namespace Shared.Beeping.NPcoNP.Grammar284HalfPositiveWindow
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeGrammarPreterminalDispatch
open Shared.Beeping.NPcoNP.NativeAllBankSelectedValue
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.NativeHalfSelectedGeneralScan
open Shared.Beeping.NPcoNP.Coalescing284Map
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
open Shared.Beeping.NPcoNP.Grammar284ExpansionPaths
open Shared.Beeping.NPcoNP.Grammar284SuccessorShapeBase
open Shared.Beeping.NPcoNP.Grammar284SuccessorShape
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
open Shared.Beeping.NPcoNP.Grammar284HalfOddShape
open Shared.Beeping.NPcoNP.Grammar284HalfOddGraph
open Shared.Beeping.NPcoNP.Grammar284HalfEvenGraph
open Shared.Beeping.NPcoNP.Grammar284HalfZeroShape
open Shared.Beeping.NPcoNP.Grammar284HalfGraphZero
open Shared.Beeping.NPcoNP.Grammar284HalfPreparation
open Shared.Beeping.NPcoNP.Grammar284OrdinaryPhysical
open Shared.Beeping.NPcoNP.Grammar284ReservedWindow
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 30000000

theorem prepared_positive_step (row : Fin 185) (path : Path) (name : String) (graph : Bank 12)
    (values rest more : List Nat) (m skip : Nat) (hskip : skip≤1)
    (leaf : graphLeaf row=some (path,name)) (entry : operationEntry name=some (entryAt values.length))
    (hlen : values.length≤3)
    (parity : (skip=0 ∧ (m+1)%2=1) ∨ (skip=1 ∧ (m+1)%2=0))
    (layout : arrayBank graph=values++(m+1)::rest)
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
  let nextState := if skip=0 then target.code[row].yes else target.code[row].no
  have hcert : successorShape path skip=true ∧ rightmostOK path skip=true ∧ path.getLast?=some false ∧
      ∃ dst, successor traceState557.acc.starts path skip=some dst ∧
        Grammar284.target producerFullRows producerNumbering.map 3 dst=some nextState.val := by
    rcases parity with ⟨hs,ho⟩ | ⟨hs,he⟩
    · subst skip
      simpa [nextState] using half_odd_shapes row path name (entryAt values.length) leaf entry hq
    · subst skip
      simpa [nextState] using Grammar284HalfZeroShape.half_zero_shapes row path name (entryAt values.length) leaf entry hq
  obtain ⟨hshape,hrightmost,hlast,dst,hsucc,htarget⟩ := hcert
  have hvalue := selected_graph_value graph n values rest (m+1) rfl layout
  have hstep : target.system.step ⟨row,graph⟩=(⟨nextState,write graph (arrayToSuffix n) ((m+1)/2)⟩,[]) := by
    rcases parity with ⟨hs,ho⟩ | ⟨hs,he⟩
    · subst skip
      simpa [nextState] using half_odd_step row path name (entryAt values.length) (arrayToSuffix n) leaf entry hreg graph (m+1) hvalue.symm ho
    · subst skip
      simpa [nextState] using Grammar284HalfEvenGraph.half_even_step row path name (entryAt values.length) (arrayToSuffix n) leaf entry hreg graph (m+1) hvalue.symm he
  have hbank : Holds t (separator+1) (encode values ++ (block (m+1) ++ (encode (rest++more) ++ [true,false]))) := by
    rw [layout] at bank
    simpa [encode_append,encode,List.append_assoc] using bank
  have htail : ∀ q, separator+2+((encode values ++ block (m+1) ++ encode (rest++more)).length : Int)≤q → t q=false := by
    intro q hq
    apply tail
    rw [layout]
    simpa [encode_append,encode,List.append_assoc] using hq
  obtain ⟨next,nextName,a,mid,hnext,ha,hw,hl,hgap,hsep,hmark,houtbank,houttail,hsegment⟩ :=
    Grammar284HalfPositivePrepared.prepared_positive_to_first_successor row dst path name values (rest++more) m skip hskip leaf entry hlen parity
      hshape hrightmost hlast hsucc origin h separator t hentry space (by omega) word left marker z1 control sep hbank htail
  obtain ⟨total,last,out,htotal,hgraph,hout,houtleft,houtgap,houtmark,houtsep,hbank',hframe,hfinal⟩ :=
    finish_contraction_frame (cfg 93 (origin+1) t) a mid origin separator dst next nextName nextState
      htarget hnext ha hsegment hw hl hgap (by omega) hmark hsep _ houtbank
  let more' := more ++ List.replicate ((m+2)/2) 0
  have hgbank : arrayBank (write graph (arrayToSuffix n) ((m+1)/2))=values++((m+1)/2)::rest :=
    Shared.Beeping.NPcoNP.Grammar284BankCorrespondence.write_selected_array graph n values rest (m+1) ((m+1)/2) rfl layout
  have hresultbank : Holds out (separator+1)
      (encode (arrayBank (write graph (arrayToSuffix n) ((m+1)/2))++more') ++ [true,false]) := by
    rw [hgbank]
    simpa [more',List.append_assoc] using hbank'
  have hresulttail : ∀ q, separator+2+((encode (arrayBank (write graph (arrayToSuffix n) ((m+1)/2))++more')).length : Int)≤q → out q=false := by
    intro q hq
    rw [hframe q (by omega)]
    apply houttail
    rw [hgbank] at hq
    simpa [more',List.append_assoc] using hq
  rw [hstep]
  refine ⟨total,out,htotal,rfl,?_,hfinal⟩
  exact ⟨last.1,last.2,more',by simpa using hgraph,room,hout,houtleft,houtgap,houtmark,houtsep,hresultbank,hresulttail⟩

/-- From a supplied reserved parser window, a positive native HALF
matches its graph step and preserves a reserved infinite-tail window. -/
theorem positive_step (row : Fin 185) (path : Path) (name : String) (graph : Bank 12)
    (values rest : List Nat) (m skip : Nat) (hskip : skip≤1) (origin separator : Int) (t : Int → Bool)
    (window : ReservedWindow row graph origin separator t)
    (leaf : graphLeaf row=some (path,name)) (entry : operationEntry name=some (entryAt values.length))
    (hlen : values.length≤3)
    (parity : (skip=0 ∧ (m+1)%2=1) ∨ (skip=1 ∧ (m+1)%2=0)) (layout : arrayBank graph=values++(m+1)::rest) :
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
      prepared_positive_step row path name graph values rest more m skip hskip leaf entry hlen parity layout origin h separator mid
        rfl space room hw hl hm hz hcontrol hsep hbank htail
    exact ⟨a+b,out,by omega,hevent,hwindow,segAdd machine _ _ _ a b hsegment hrest⟩

/-- The parity and corresponding graph branch are selected from the value. -/
theorem positive_step_all (row : Fin 185) (path : Path) (name : String) (graph : Bank 12)
    (values rest : List Nat) (m : Nat) (origin separator : Int) (t : Int → Bool)
    (window : ReservedWindow row graph origin separator t)
    (leaf : graphLeaf row=some (path,name)) (entry : operationEntry name=some (entryAt values.length))
    (hlen : values.length≤3) (layout : arrayBank graph=values++(m+1)::rest) :
    ∃ steps out, 0<steps ∧ (target.system.step ⟨row,graph⟩).2=[] ∧
      ReservedWindow (target.system.step ⟨row,graph⟩).1.state
        (target.system.step ⟨row,graph⟩).1.bank origin separator out ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) steps := by
  have hp : (m+1)%2=0 ∨ (m+1)%2=1 := by omega
  rcases hp with he | ho
  · exact positive_step row path name graph values rest m 1 (by decide) origin separator t
      window leaf entry hlen (Or.inr ⟨rfl,he⟩) layout
  · exact positive_step row path name graph values rest m 0 (by decide) origin separator t
      window leaf entry hlen (Or.inl ⟨rfl,ho⟩) layout

#print axioms prepared_positive_step
#print axioms positive_step
#print axioms positive_step_all
end Shared.Beeping.NPcoNP.Grammar284HalfPositiveWindow
