import Shared.Beeping.NPcoNP.Grammar284PositiveTailFrame
import Shared.Beeping.NPcoNP.NativeAllBankDecrementPadding
import Shared.Beeping.NPcoNP.Grammar284DecrementSuccessor
import Shared.Beeping.NPcoNP.Grammar284OrdinaryPhysical
import Shared.Beeping.NPcoNP.Grammar284OrdinaryPreparation

/-! An arbitrary suffix survives a positive decrement through the contracted
physical graph step under the supplied prepared bank layout. -/
namespace Shared.Beeping.NPcoNP.Grammar284PaddedPositive
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeGrammarPreterminalDispatch
open Shared.Beeping.NPcoNP.NativeGrammarSelectorDispatch
open Shared.Beeping.NPcoNP.Grammar284ExpansionPaths
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.NativeAllBankScan
open Shared.Beeping.NPcoNP.NativeAllBankDecrementPadding
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
open Shared.Beeping.NPcoNP.Grammar284GraphOperation
open Shared.Beeping.NPcoNP.Grammar284BankCorrespondence
open Shared.Beeping.NPcoNP.Grammar284PhysicalSuccessor
open Shared.Beeping.NPcoNP.Grammar284OrdinaryPhysical
open Shared.Beeping.NPcoNP.Grammar284OrdinaryContraction
open Shared.Beeping.NPcoNP.Grammar284OrdinaryPreparation
open Shared.Beeping.NPcoNP.Grammar284DecrementSuccessor
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

theorem positive_to_first_successor_padded (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (notRoot : state.val≠184)
    (n : Fin 12) (operation : namedOperation name=some (n,false))
    (graph : Bank 12) (values graphTail more : List Nat) (value : Nat) (pad : List Bool)
    (hlen : values.length=n.val) (layout : arrayBank graph=values++(value+1)::graphTail)
    (origin h separator : Int) (t : Int → Bool)
    (hentry : h=origin+((path.length : Nat) : Int)) (hlong : h+4≤separator)
    (room : origin+55<separator) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false) (marker : t h=true)
    (z1 : t (h+1)=false) (z2 : t (h+2)=false)
    (control : ∀ q, h+3≤q → q<separator → t q=true) (delimiter : t separator=false)
    (bank : Holds t (separator+1)
      ((encode values ++ (encode ((value+1)::(graphTail++more)) ++ [false,false])) ++ pad)) :
    let result := target.system.step ⟨state,graph⟩
    ∃ (dst : Nat) (next : Path) (nextName : String) (steps : Nat) (out : Int → Bool),
      successor traceState557.acc.starts path 0=some dst ∧
      traceState557.acc.leaves[dst]?=some (next,nextName) ∧
      0<steps ∧ result.2=[] ∧ result.1.state=target.code[state].yes ∧
      Holds out origin next ∧ Holds out (separator+1) ((encode (arrayBank result.1.bank++more++[0]) ++ [false]) ++ pad) ∧
      (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((next.length : Nat) : Int)-1<q → q<separator-1 → out q=false) ∧
      out separator=false ∧ out (separator-1)=true ∧
      silentSegment machine (cfg (operationAt n false) h t) (cfg 93 (origin+1) out) steps := by
  obtain ⟨dst,next,nextName,steps,out,hsucc,hnext,hsteps,hevent,hstate,hword,hbank,hleft,hgap,hsep,hmark,_hfar,hsegment⟩ :=
    Shared.Beeping.NPcoNP.Grammar284PositiveTailFrame.positive_to_first_successor_frame
      state path name leaf notRoot n operation graph values graphTail more value pad hlen layout
      origin h separator t hentry hlong room word left marker z1 z2 control delimiter bank
  exact ⟨dst,next,nextName,steps,out,hsucc,hnext,hsteps,hevent,hstate,hword,hbank,hleft,hgap,hsep,hmark,hsegment⟩

theorem positive_from_parser_to_first_successor_frame (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (notRoot : state.val≠184)
    (n : Fin 12) (operation : namedOperation name=some (n,false))
    (graph : Bank 12) (values graphTail more : List Nat) (value : Nat) (pad : List Bool)
    (hlen : values.length=n.val) (layout : arrayBank graph=values++(value+1)::graphTail)
    (origin h separator : Int) (t : Int → Bool)
    (hentry : h=origin+((path.length : Nat) : Int)) (hlong : h+4≤separator)
    (room : origin+55<separator) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false) (marker : t h=true)
    (z1 : t (h+1)=false) (z2 : t (h+2)=false)
    (control : ∀ q, h+3≤q → q<separator → t q=true) (delimiter : t separator=false)
    (bank : Holds t (separator+1)
      ((encode values ++ (encode ((value+1)::(graphTail++more)) ++ [false,false])) ++ pad)) :
    let result := target.system.step ⟨state,graph⟩
    ∃ (dst : Nat) (next : Path) (nextName : String) (steps : Nat) (out : Int → Bool),
      successor traceState557.acc.starts path 0=some dst ∧
      traceState557.acc.leaves[dst]?=some (next,nextName) ∧
      0<steps ∧ result.2=[] ∧ result.1.state=target.code[state].yes ∧
      Holds out origin next ∧ Holds out (separator+1) ((encode (arrayBank result.1.bank++more++[0]) ++ [false]) ++ pad) ∧
      (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((next.length : Nat) : Int)-1<q → q<separator-1 → out q=false) ∧
      out separator=false ∧ out (separator-1)=true ∧
      (∀ q, separator+1+((encode (arrayBank result.1.bank++more++[0])).length : Int)≤q → out q=t q) ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) steps := by
  dsimp only
  have dispatch := decrement_from_parser state path name leaf n operation origin h t hentry word
  obtain ⟨dst,next,nextName,k,out,hsucc,hnext,hk,hevent,hstate,hword,hbank,hleft,hgap,hsep,hmark,hfar,hseg⟩ :=
    Shared.Beeping.NPcoNP.Grammar284PositiveTailFrame.positive_to_first_successor_frame state path name leaf notRoot n operation graph values graphTail more value pad
      hlen layout origin h separator t hentry hlong room word left marker z1 z2 control delimiter bank
  exact ⟨dst,next,nextName,path.tail.length+k,out,hsucc,hnext,by omega,hevent,hstate,hword,hbank,hleft,hgap,hsep,hmark,hfar,
    segAdd machine _ _ _ path.tail.length k dispatch hseg⟩


theorem positive_from_parser_to_first_successor_padded (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (notRoot : state.val≠184)
    (n : Fin 12) (operation : namedOperation name=some (n,false))
    (graph : Bank 12) (values graphTail more : List Nat) (value : Nat) (pad : List Bool)
    (hlen : values.length=n.val) (layout : arrayBank graph=values++(value+1)::graphTail)
    (origin h separator : Int) (t : Int → Bool)
    (hentry : h=origin+((path.length : Nat) : Int)) (hlong : h+4≤separator)
    (room : origin+55<separator) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false) (marker : t h=true)
    (z1 : t (h+1)=false) (z2 : t (h+2)=false)
    (control : ∀ q, h+3≤q → q<separator → t q=true) (delimiter : t separator=false)
    (bank : Holds t (separator+1)
      ((encode values ++ (encode ((value+1)::(graphTail++more)) ++ [false,false])) ++ pad)) :
    let result := target.system.step ⟨state,graph⟩
    ∃ (dst : Nat) (next : Path) (nextName : String) (steps : Nat) (out : Int → Bool),
      successor traceState557.acc.starts path 0=some dst ∧
      traceState557.acc.leaves[dst]?=some (next,nextName) ∧
      0<steps ∧ result.2=[] ∧ result.1.state=target.code[state].yes ∧
      Holds out origin next ∧ Holds out (separator+1) ((encode (arrayBank result.1.bank++more++[0]) ++ [false]) ++ pad) ∧
      (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((next.length : Nat) : Int)-1<q → q<separator-1 → out q=false) ∧
      out separator=false ∧ out (separator-1)=true ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) steps := by
  obtain ⟨dst,next,nextName,steps,out,hsucc,hnext,hsteps,hevent,hstate,hword,hbank,hleft,hgap,hsep,hmark,_hfar,hsegment⟩ :=
    positive_from_parser_to_first_successor_frame state path name leaf notRoot n operation graph values graphTail more value pad
      hlen layout origin h separator t hentry hlong room word left marker z1 z2 control delimiter bank
  exact ⟨dst,next,nextName,steps,out,hsucc,hnext,hsteps,hevent,hstate,hword,hbank,hleft,hgap,hsep,hmark,hsegment⟩

theorem positive_to_contracted_successor_frame (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (notRoot : state.val≠184)
    (n : Fin 12) (operation : namedOperation name=some (n,false))
    (graph : Bank 12) (values graphTail more : List Nat) (value : Nat) (pad : List Bool)
    (hlen : values.length=n.val) (layout : arrayBank graph=values++(value+1)::graphTail)
    (origin h separator : Int) (t : Int → Bool)
    (hentry : h=origin+((path.length : Nat) : Int)) (hlong : h+4≤separator)
    (room : origin+55<separator) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false) (marker : t h=true)
    (z1 : t (h+1)=false) (z2 : t (h+2)=false)
    (control : ∀ q, h+3≤q → q<separator → t q=true) (delimiter : t separator=false)
    (bank : Holds t (separator+1)
      ((encode values ++ (encode ((value+1)::(graphTail++more)) ++ [false,false])) ++ pad)) :
    let result := target.system.step ⟨state,graph⟩
    ∃ (total : Nat) (last : Path × String) (out : Int → Bool), 0<total ∧ result.2=[] ∧
      graphLeaf result.1.state=some last ∧ Holds out origin last.1 ∧
      (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((last.1.length : Nat) : Int)-1<q → q<(separator)-1 → out q=false) ∧
      out ((separator)-1)=true ∧ out (separator)=false ∧
      Holds out ((separator)+1) ((encode (arrayBank (target.system.step ⟨state,graph⟩).1.bank++more++[0]) ++ [false]) ++ pad) ∧
      (∀ q, separator+1+((encode (arrayBank result.1.bank++more++[0])).length : Int)≤q → out q=t q) ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) total := by
  dsimp only
  obtain ⟨dst,next,nextName,steps,mid,hsucc,hleaf,hsteps,hevent,hstate,hword,hbank,hleft,hgap,hsep,hright,hfar,hsegment⟩ :=
    positive_from_parser_to_first_successor_frame state path name leaf notRoot n operation graph values graphTail more value pad hlen layout origin h separator t hentry hlong room word left marker z1 z2 control delimiter bank
  have hc := successor_contracts state path name leaf n false operation 0 dst
    (by exact Or.inl rfl) hsucc
  have targetAt : Grammar284.target producerFullRows producerNumbering.map 3 dst=
      some (target.system.step ⟨state,graph⟩).1.state.val := by
    rw [hstate]
    simpa using hc
  have hbank' : Holds mid ((separator)+1) ((encode (arrayBank (target.system.step ⟨state,graph⟩).1.bank++more++[0]) ++ [false]) ++ pad) := by
    exact hbank
  obtain ⟨total,last,out,htotal,hgraph,hout,houtleft,houtgap,houtmark,houtsep,houtbank,houtframe,hfinal⟩ :=
    finish_contraction_frame (cfg 93 (origin+1) t) steps mid origin (separator) dst next nextName
      (target.system.step ⟨state,graph⟩).1.state targetAt hleaf hsteps hsegment hword hleft hgap room hright hsep _ hbank'
  refine ⟨total,last,out,htotal,hevent,hgraph,hout,houtleft,houtgap,houtmark,houtsep,houtbank,?_,hfinal⟩
  intro q hq
  rw [houtframe q (by omega)]
  exact hfar q hq


theorem positive_to_contracted_successor_padded (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (notRoot : state.val≠184)
    (n : Fin 12) (operation : namedOperation name=some (n,false))
    (graph : Bank 12) (values graphTail more : List Nat) (value : Nat) (pad : List Bool)
    (hlen : values.length=n.val) (layout : arrayBank graph=values++(value+1)::graphTail)
    (origin h separator : Int) (t : Int → Bool)
    (hentry : h=origin+((path.length : Nat) : Int)) (hlong : h+4≤separator)
    (room : origin+55<separator) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false) (marker : t h=true)
    (z1 : t (h+1)=false) (z2 : t (h+2)=false)
    (control : ∀ q, h+3≤q → q<separator → t q=true) (delimiter : t separator=false)
    (bank : Holds t (separator+1)
      ((encode values ++ (encode ((value+1)::(graphTail++more)) ++ [false,false])) ++ pad)) :
    let result := target.system.step ⟨state,graph⟩
    ∃ (total : Nat) (last : Path × String) (out : Int → Bool), 0<total ∧ result.2=[] ∧
      graphLeaf result.1.state=some last ∧ Holds out origin last.1 ∧
      (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((last.1.length : Nat) : Int)-1<q → q<(separator)-1 → out q=false) ∧
      out ((separator)-1)=true ∧ out (separator)=false ∧
      Holds out ((separator)+1) ((encode (arrayBank (target.system.step ⟨state,graph⟩).1.bank++more++[0]) ++ [false]) ++ pad) ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) total := by
  obtain ⟨total,last,out,htotal,hevent,hgraph,hword,hleft,hgap,hmark,hsep,hbank,_hfar,hsegment⟩ :=
    positive_to_contracted_successor_frame state path name leaf notRoot n operation graph values graphTail more value pad
      hlen layout origin h separator t hentry hlong room word left marker z1 z2 control delimiter bank
  exact ⟨total,last,out,htotal,hevent,hgraph,hword,hleft,hgap,hmark,hsep,hbank,hsegment⟩

theorem positive_step_frame (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (notRoot : state.val≠184)
    (n : Fin 12) (operation : namedOperation name=some (n,false))
    (graph : Bank 12) (values graphTail more : List Nat) (value : Nat) (pad : List Bool)
    (hlen : values.length=n.val) (layout : arrayBank graph=values++(value+1)::graphTail)
    (origin h separator : Int) (t : Int → Bool)
    (hentry : h=origin+((path.length : Nat) : Int)) (space : h+4≤separator)
    (room : origin+55<separator) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false)
    (gap : ∀ q, h≤q → q<separator-1 → t q=false)
    (right : t (separator-1)=true) (delimiter : t separator=false)
    (bank : Holds t (separator+1)
      ((encode values ++ (encode ((value+1)::(graphTail++more)) ++ [false,false])) ++ pad)) :
    let result := target.system.step ⟨state,graph⟩
    ∃ (total : Nat) (last : Path × String) (out : Int → Bool), 0<total ∧ result.2=[] ∧
      graphLeaf result.1.state=some last ∧ Holds out origin last.1 ∧
      (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((last.1.length : Nat) : Int)-1<q → q<separator-1 → out q=false) ∧
      out (separator-1)=true ∧ out separator=false ∧
      Holds out (separator+1) ((encode (arrayBank result.1.bank++more++[0]) ++ [false]) ++ pad) ∧
      (∀ q, separator+1+((encode (arrayBank result.1.bank++more++[0])).length : Int)≤q → out q=t q) ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) total := by
  dsimp only
  obtain ⟨a,mid,ha,hword,hleft,hmarker,hz1,hz2,hcontrol,hsep,hframe,hprep⟩ :=
    prepare_from_parser state path name leaf n false operation origin h separator t
      hentry space word left gap right delimiter
  have hbank : Holds mid (separator+1)
      ((encode values ++ (encode ((value+1)::(graphTail++more)) ++ [false,false])) ++ pad) := by
    apply holds_transport t mid (separator+1) _ bank
    intro q hq _
    exact (hframe q (by omega)).symm
  obtain ⟨b,last,out,hb,hevent,hgraph,hout,houtleft,houtgap,hright,houtsep,houtbank,houtfar,hstep⟩ :=
    positive_to_contracted_successor_frame state path name leaf notRoot n operation graph values graphTail more value pad
      hlen layout origin h separator mid hentry space room hword hleft hmarker hz1 hz2 hcontrol hsep hbank
  refine ⟨a+b,last,out,by omega,hevent,hgraph,hout,houtleft,houtgap,hright,houtsep,houtbank,?_,
    segAdd machine _ _ _ a b hprep hstep⟩
  intro q hq
  rw [houtfar q hq,hframe q (by omega)]



theorem positive_step_padded (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (notRoot : state.val≠184)
    (n : Fin 12) (operation : namedOperation name=some (n,false))
    (graph : Bank 12) (values graphTail more : List Nat) (value : Nat) (pad : List Bool)
    (hlen : values.length=n.val) (layout : arrayBank graph=values++(value+1)::graphTail)
    (origin h separator : Int) (t : Int → Bool)
    (hentry : h=origin+((path.length : Nat) : Int)) (space : h+4≤separator)
    (room : origin+55<separator) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false)
    (gap : ∀ q, h≤q → q<separator-1 → t q=false)
    (right : t (separator-1)=true) (delimiter : t separator=false)
    (bank : Holds t (separator+1)
      ((encode values ++ (encode ((value+1)::(graphTail++more)) ++ [false,false])) ++ pad)) :
    let result := target.system.step ⟨state,graph⟩
    ∃ (total : Nat) (last : Path × String) (out : Int → Bool), 0<total ∧ result.2=[] ∧
      graphLeaf result.1.state=some last ∧ Holds out origin last.1 ∧
      (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((last.1.length : Nat) : Int)-1<q → q<separator-1 → out q=false) ∧
      out (separator-1)=true ∧ out separator=false ∧
      Holds out (separator+1) ((encode (arrayBank result.1.bank++more++[0]) ++ [false]) ++ pad) ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) total := by
  obtain ⟨total,last,out,htotal,hevent,hgraph,hword,hleft,hgap,hmark,hsep,hbank,_hfar,hsegment⟩ :=
    positive_step_frame state path name leaf notRoot n operation graph values graphTail more value pad
      hlen layout origin h separator t hentry space room word left gap right delimiter bank
  exact ⟨total,last,out,htotal,hevent,hgraph,hword,hleft,hgap,hmark,hsep,hbank,hsegment⟩

#print axioms positive_step_padded
end Shared.Beeping.NPcoNP.Grammar284PaddedPositive
