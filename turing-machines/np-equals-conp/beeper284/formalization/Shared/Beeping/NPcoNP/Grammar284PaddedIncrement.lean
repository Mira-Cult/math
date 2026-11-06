import Shared.Beeping.NPcoNP.Grammar284IncrementTailFrame
import Shared.Beeping.NPcoNP.NativeAllBankIncrementPadding
import Shared.Beeping.NPcoNP.Grammar284IncrementSuccessor
import Shared.Beeping.NPcoNP.Grammar284OrdinaryPhysical
import Shared.Beeping.NPcoNP.Grammar284OrdinaryPreparation

/-! Preserve an arbitrary suffix through an increment and its first expanded
successor under an explicit prepared operation window. -/
namespace Shared.Beeping.NPcoNP.Grammar284PaddedIncrement
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
open Shared.Beeping.NPcoNP.NativeAllBankIncrementPadding
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
open Shared.Beeping.NPcoNP.Grammar284GraphOperation
open Shared.Beeping.NPcoNP.Grammar284BankCorrespondence
open Shared.Beeping.NPcoNP.Grammar284PhysicalSuccessor
open Shared.Beeping.NPcoNP.Grammar284OrdinaryPhysical
open Shared.Beeping.NPcoNP.Grammar284OrdinaryContraction
open Shared.Beeping.NPcoNP.Grammar284OrdinaryPreparation
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem increment_to_first_successor_padded (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (notRoot : state.val≠184)
    (n : Fin 12) (operation : namedOperation name=some (n,true))
    (graph : Bank 12) (values graphTail more : List Nat) (value : Nat) (pad : List Bool)
    (hlen : values.length=n.val) (layout : arrayBank graph=values++value::graphTail)
    (origin h : Int) (t : Int → Bool) (k : Nat)
    (hentry : h=origin+((path.length : Nat) : Int)) (hk : 0<k)
    (room : origin+55<h+3+(k : Int)) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false) (marker : t h=true)
    (z1 : t (h+1)=false) (z2 : t (h+2)=false)
    (control : ∀ i : Nat, i<k → t (h+3+(i : Int))=true)
    (delimiter : t (h+3+(k : Int))=false)
    (bank : Holds t (h+4+(k : Int))
      ((encode (values++value::(graphTail++more)) ++ [false]) ++ pad)) :
    let result := target.system.step ⟨state,graph⟩
    ∃ (dst : Nat) (next : Path) (nextName : String) (steps : Nat) (out : Int → Bool),
      successor traceState557.acc.starts path 0=some dst ∧
      traceState557.acc.leaves[dst]?=some (next,nextName) ∧
      0<steps ∧ result.2=[] ∧ result.1.state=target.code[state].yes ∧
      Holds out origin next ∧ Holds out (h+4+(k : Int)) (encode (arrayBank result.1.bank++more) ++ pad) ∧
      (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((next.length : Nat) : Int)-1<q → q<h+3+(k : Int)-1 → out q=false) ∧
      out (h+3+(k : Int))=false ∧ out (h+3+(k : Int)-1)=true ∧
      silentSegment machine (cfg (operationAt n true) h t) (cfg 93 (origin+1) out) steps := by
  obtain ⟨dst,next,nextName,steps,out,hsucc,hnext,hsteps,hevent,hstate,hword,hbank,hleft,hgap,hsep,hmark,_hfar,hsegment⟩ :=
    Shared.Beeping.NPcoNP.Grammar284IncrementTailFrame.increment_to_first_successor_frame
      state path name leaf notRoot n operation graph values graphTail more value pad hlen layout
      origin h t k hentry hk room word left marker z1 z2 control delimiter bank
  exact ⟨dst,next,nextName,steps,out,hsucc,hnext,hsteps,hevent,hstate,hword,hbank,hleft,hgap,hsep,hmark,hsegment⟩

theorem increment_from_parser_to_first_successor_frame (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (notRoot : state.val≠184)
    (n : Fin 12) (operation : namedOperation name=some (n,true))
    (graph : Bank 12) (values graphTail more : List Nat) (value : Nat) (pad : List Bool)
    (hlen : values.length=n.val) (layout : arrayBank graph=values++value::graphTail)
    (origin h : Int) (t : Int → Bool) (k : Nat)
    (hentry : h=origin+((path.length : Nat) : Int)) (hk : 0<k)
    (room : origin+55<h+3+(k : Int)) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false) (marker : t h=true)
    (z1 : t (h+1)=false) (z2 : t (h+2)=false)
    (control : ∀ i : Nat, i<k → t (h+3+(i : Int))=true)
    (delimiter : t (h+3+(k : Int))=false)
    (bank : Holds t (h+4+(k : Int))
      ((encode (values++value::(graphTail++more)) ++ [false]) ++ pad)) :
    let result := target.system.step ⟨state,graph⟩
    ∃ (dst : Nat) (next : Path) (nextName : String) (steps : Nat) (out : Int → Bool),
      successor traceState557.acc.starts path 0=some dst ∧
      traceState557.acc.leaves[dst]?=some (next,nextName) ∧
      0<steps ∧ result.2=[] ∧ result.1.state=target.code[state].yes ∧
      Holds out origin next ∧ Holds out (h+4+(k : Int)) (encode (arrayBank result.1.bank++more) ++ pad) ∧
      (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((next.length : Nat) : Int)-1<q → q<h+3+(k : Int)-1 → out q=false) ∧
      out (h+3+(k : Int))=false ∧ out (h+3+(k : Int)-1)=true ∧
      (∀ q, h+4+(k : Int)+((encode (arrayBank result.1.bank++more)).length : Int)≤q → out q=t q) ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) steps := by
  dsimp only
  have member := graph_leaf_member state path name leaf
  have walk : PreparedWalk path (.op name) :=
    expanded_leaf_follows traceState557.acc producerExpand (path,name) member
  obtain ⟨_,tail⟩ := prepared_head_tail t origin path name walk word
  have target := named_operation_entry (path,name) member n true operation
  have hdispatch := expanded_leaf_dispatch_to_entry traceState557.acc producerExpand (path,name) member
    (operationAt n true) target (origin+1) t tail
  have hlenPath : (path.tail.length : Int)+1=(path.length : Int) := by
    obtain ⟨raw,he,_⟩ := walk
    rw [he]
    simp [preparedPrefix]
  have hdispatch' : silentSegment machine (cfg 93 (origin+1) t)
      (cfg (operationAt n true) h t) path.tail.length := by
    have he : origin+1+(path.tail.length : Int)=h := by omega
    simpa only [he] using hdispatch
  obtain ⟨dst,next,nextName,ksteps,out,hsucc,hnext,hksteps,hevent,hstate,hword,hbank,hleft,hgap,hsep,hmark,hfar,hseg⟩ :=
    Shared.Beeping.NPcoNP.Grammar284IncrementTailFrame.increment_to_first_successor_frame state path name leaf notRoot n operation graph values graphTail more value pad
      hlen layout origin h t k hentry hk room word left marker z1 z2 control delimiter bank
  exact ⟨dst,next,nextName,path.tail.length+ksteps,out,hsucc,hnext,by omega,hevent,hstate,hword,hbank,hleft,hgap,hsep,hmark,hfar,
    segAdd machine _ _ _ path.tail.length ksteps hdispatch' hseg⟩



theorem increment_from_parser_to_first_successor_padded (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (notRoot : state.val≠184)
    (n : Fin 12) (operation : namedOperation name=some (n,true))
    (graph : Bank 12) (values graphTail more : List Nat) (value : Nat) (pad : List Bool)
    (hlen : values.length=n.val) (layout : arrayBank graph=values++value::graphTail)
    (origin h : Int) (t : Int → Bool) (k : Nat)
    (hentry : h=origin+((path.length : Nat) : Int)) (hk : 0<k)
    (room : origin+55<h+3+(k : Int)) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false) (marker : t h=true)
    (z1 : t (h+1)=false) (z2 : t (h+2)=false)
    (control : ∀ i : Nat, i<k → t (h+3+(i : Int))=true)
    (delimiter : t (h+3+(k : Int))=false)
    (bank : Holds t (h+4+(k : Int))
      ((encode (values++value::(graphTail++more)) ++ [false]) ++ pad)) :
    let result := target.system.step ⟨state,graph⟩
    ∃ (dst : Nat) (next : Path) (nextName : String) (steps : Nat) (out : Int → Bool),
      successor traceState557.acc.starts path 0=some dst ∧
      traceState557.acc.leaves[dst]?=some (next,nextName) ∧
      0<steps ∧ result.2=[] ∧ result.1.state=target.code[state].yes ∧
      Holds out origin next ∧ Holds out (h+4+(k : Int)) (encode (arrayBank result.1.bank++more) ++ pad) ∧
      (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((next.length : Nat) : Int)-1<q → q<h+3+(k : Int)-1 → out q=false) ∧
      out (h+3+(k : Int))=false ∧ out (h+3+(k : Int)-1)=true ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) steps := by
  obtain ⟨dst,next,nextName,steps,out,hsucc,hnext,hsteps,hevent,hstate,hword,hbank,hleft,hgap,hsep,hmark,_hfar,hsegment⟩ :=
    increment_from_parser_to_first_successor_frame state path name leaf notRoot n operation graph values graphTail more value pad
      hlen layout origin h t k hentry hk room word left marker z1 z2 control delimiter bank
  exact ⟨dst,next,nextName,steps,out,hsucc,hnext,hsteps,hevent,hstate,hword,hbank,hleft,hgap,hsep,hmark,hsegment⟩

theorem increment_to_contracted_successor_frame (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (notRoot : state.val≠184)
    (n : Fin 12) (operation : namedOperation name=some (n,true))
    (graph : Bank 12) (values graphTail more : List Nat) (value : Nat) (pad : List Bool)
    (hlen : values.length=n.val) (layout : arrayBank graph=values++value::graphTail)
    (origin h : Int) (t : Int → Bool) (k : Nat)
    (hentry : h=origin+((path.length : Nat) : Int)) (hk : 0<k)
    (room : origin+55<h+3+(k : Int)) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false) (marker : t h=true)
    (z1 : t (h+1)=false) (z2 : t (h+2)=false)
    (control : ∀ i : Nat, i<k → t (h+3+(i : Int))=true)
    (delimiter : t (h+3+(k : Int))=false)
    (bank : Holds t (h+4+(k : Int))
      ((encode (values++value::(graphTail++more)) ++ [false]) ++ pad)) :
    let result := target.system.step ⟨state,graph⟩
    ∃ (total : Nat) (last : Path × String) (out : Int → Bool), 0<total ∧ result.2=[] ∧
      graphLeaf result.1.state=some last ∧ Holds out origin last.1 ∧
      (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((last.1.length : Nat) : Int)-1<q → q<(h+3+(k : Int))-1 → out q=false) ∧
      out ((h+3+(k : Int))-1)=true ∧ out (h+3+(k : Int))=false ∧
      Holds out ((h+3+(k : Int))+1) (encode (arrayBank (target.system.step ⟨state,graph⟩).1.bank++more) ++ pad) ∧
      (∀ q, h+4+(k : Int)+((encode (arrayBank result.1.bank++more)).length : Int)≤q → out q=t q) ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) total := by
  dsimp only
  obtain ⟨dst,next,nextName,steps,mid,hsucc,hleaf,hsteps,hevent,hstate,hword,hbank,hleft,hgap,hsep,hright,hfar,hsegment⟩ :=
    increment_from_parser_to_first_successor_frame state path name leaf notRoot n operation graph values graphTail more value pad hlen layout origin h t k hentry hk room word left marker z1 z2 control delimiter bank
  have hc := successor_contracts state path name leaf n true operation 0 dst
    (by exact Or.inl rfl) hsucc
  have targetAt : Grammar284.target producerFullRows producerNumbering.map 3 dst=
      some (target.system.step ⟨state,graph⟩).1.state.val := by
    rw [hstate]
    simpa using hc
  have hbank' : Holds mid ((h+3+(k : Int))+1) (encode (arrayBank (target.system.step ⟨state,graph⟩).1.bank++more) ++ pad) := by
    have he : h+3+(k : Int)+1=h+4+(k : Int) := by omega
    simpa only [he] using hbank
  obtain ⟨total,last,out,htotal,hgraph,hout,houtleft,houtgap,houtmark,houtsep,houtbank,houtframe,hfinal⟩ :=
    finish_contraction_frame (cfg 93 (origin+1) t) steps mid origin (h+3+(k : Int)) dst next nextName
      (target.system.step ⟨state,graph⟩).1.state targetAt hleaf hsteps hsegment hword hleft hgap room hright hsep _ hbank'
  refine ⟨total,last,out,htotal,hevent,hgraph,hout,houtleft,houtgap,houtmark,houtsep,houtbank,?_,hfinal⟩
  intro q hq
  rw [houtframe q (by omega)]
  exact hfar q hq


theorem increment_to_contracted_successor_padded (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (notRoot : state.val≠184)
    (n : Fin 12) (operation : namedOperation name=some (n,true))
    (graph : Bank 12) (values graphTail more : List Nat) (value : Nat) (pad : List Bool)
    (hlen : values.length=n.val) (layout : arrayBank graph=values++value::graphTail)
    (origin h : Int) (t : Int → Bool) (k : Nat)
    (hentry : h=origin+((path.length : Nat) : Int)) (hk : 0<k)
    (room : origin+55<h+3+(k : Int)) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false) (marker : t h=true)
    (z1 : t (h+1)=false) (z2 : t (h+2)=false)
    (control : ∀ i : Nat, i<k → t (h+3+(i : Int))=true)
    (delimiter : t (h+3+(k : Int))=false)
    (bank : Holds t (h+4+(k : Int))
      ((encode (values++value::(graphTail++more)) ++ [false]) ++ pad)) :
    let result := target.system.step ⟨state,graph⟩
    ∃ (total : Nat) (last : Path × String) (out : Int → Bool), 0<total ∧ result.2=[] ∧
      graphLeaf result.1.state=some last ∧ Holds out origin last.1 ∧
      (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((last.1.length : Nat) : Int)-1<q → q<(h+3+(k : Int))-1 → out q=false) ∧
      out ((h+3+(k : Int))-1)=true ∧ out (h+3+(k : Int))=false ∧
      Holds out ((h+3+(k : Int))+1) (encode (arrayBank (target.system.step ⟨state,graph⟩).1.bank++more) ++ pad) ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) total := by
  obtain ⟨total,last,out,htotal,hevent,hgraph,hword,hleft,hgap,hmark,hsep,hbank,_hfar,hsegment⟩ :=
    increment_to_contracted_successor_frame state path name leaf notRoot n operation graph values graphTail more value pad
      hlen layout origin h t k hentry hk room word left marker z1 z2 control delimiter bank
  exact ⟨total,last,out,htotal,hevent,hgraph,hword,hleft,hgap,hmark,hsep,hbank,hsegment⟩

theorem increment_step_frame (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (notRoot : state.val≠184)
    (n : Fin 12) (operation : namedOperation name=some (n,true))
    (graph : Bank 12) (values graphTail more : List Nat) (value : Nat) (pad : List Bool)
    (hlen : values.length=n.val) (layout : arrayBank graph=values++value::graphTail)
    (origin h separator : Int) (t : Int → Bool)
    (hentry : h=origin+((path.length : Nat) : Int)) (space : h+4≤separator)
    (room : origin+55<separator) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false)
    (gap : ∀ q, h≤q → q<separator-1 → t q=false)
    (right : t (separator-1)=true) (delimiter : t separator=false)
    (bank : Holds t (separator+1) ((encode (values++value::(graphTail++more)) ++ [false]) ++ pad)) :
    let result := target.system.step ⟨state,graph⟩
    ∃ (total : Nat) (last : Path × String) (out : Int → Bool), 0<total ∧ result.2=[] ∧
      graphLeaf result.1.state=some last ∧ Holds out origin last.1 ∧
      (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((last.1.length : Nat) : Int)-1<q → q<separator-1 → out q=false) ∧
      out (separator-1)=true ∧ out separator=false ∧
      Holds out (separator+1) (encode (arrayBank result.1.bank++more) ++ pad) ∧
      (∀ q, separator+1+((encode (arrayBank result.1.bank++more)).length : Int)≤q → out q=t q) ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) total := by
  dsimp only
  obtain ⟨a,mid,ha,hword,hleft,hmarker,hz1,hz2,hcontrol,hsep,hframe,hprep⟩ :=
    prepare_from_parser state path name leaf n true operation origin h separator t
      hentry space word left gap right delimiter
  let k := (separator-h-3).toNat
  have hk : (k : Int)=separator-h-3 := Int.toNat_of_nonneg (by omega)
  have hpos : 0<k := by omega
  have hsepEq : h+3+(k : Int)=separator := by omega
  have hbank : Holds mid (h+4+(k : Int)) ((encode (values++value::(graphTail++more)) ++ [false]) ++ pad) := by
    have hbank' : Holds mid (separator+1) ((encode (values++value::(graphTail++more)) ++ [false]) ++ pad) := by
      apply holds_transport t mid (separator+1) _ bank
      intro q hq _
      exact (hframe q (by omega)).symm
    have he : h+4+(k : Int)=separator+1 := by omega
    simpa only [he] using hbank'
  have hcontrol' : ∀ i : Nat, i<k → mid (h+3+(i : Int))=true := by
    intro i hi
    exact hcontrol _ (by omega) (by omega)
  obtain ⟨b,last,out,hb,hevent,hgraph,hout,houtleft,houtgap,hright,houtsep,houtbank,houtfar,hstep⟩ :=
    increment_to_contracted_successor_frame state path name leaf notRoot n operation graph values graphTail more value pad
      hlen layout origin h mid k hentry hpos (by simpa only [hsepEq] using room) hword hleft
      hmarker hz1 hz2 hcontrol' (by simpa only [hsepEq] using hsep) hbank
  refine ⟨a+b,last,out,by omega,hevent,hgraph,hout,houtleft,?_,?_,?_,?_,?_,segAdd machine _ _ _ a b hprep hstep⟩
  · simpa only [hsepEq] using houtgap
  · simpa only [hsepEq] using hright
  · simpa only [hsepEq] using houtsep
  · have he : h+3+(k : Int)+1=separator+1 := by omega
    simpa only [he] using houtbank
  · intro q hq
    have hq' : h+4+(k : Int)+((encode (arrayBank (target.system.step ⟨state,graph⟩).1.bank++more)).length : Int)≤q := by omega
    rw [houtfar q hq',hframe q (by omega)]


theorem increment_step_padded (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (notRoot : state.val≠184)
    (n : Fin 12) (operation : namedOperation name=some (n,true))
    (graph : Bank 12) (values graphTail more : List Nat) (value : Nat) (pad : List Bool)
    (hlen : values.length=n.val) (layout : arrayBank graph=values++value::graphTail)
    (origin h separator : Int) (t : Int → Bool)
    (hentry : h=origin+((path.length : Nat) : Int)) (space : h+4≤separator)
    (room : origin+55<separator) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false)
    (gap : ∀ q, h≤q → q<separator-1 → t q=false)
    (right : t (separator-1)=true) (delimiter : t separator=false)
    (bank : Holds t (separator+1) ((encode (values++value::(graphTail++more)) ++ [false]) ++ pad)) :
    let result := target.system.step ⟨state,graph⟩
    ∃ (total : Nat) (last : Path × String) (out : Int → Bool), 0<total ∧ result.2=[] ∧
      graphLeaf result.1.state=some last ∧ Holds out origin last.1 ∧
      (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((last.1.length : Nat) : Int)-1<q → q<separator-1 → out q=false) ∧
      out (separator-1)=true ∧ out separator=false ∧
      Holds out (separator+1) (encode (arrayBank result.1.bank++more) ++ pad) ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) total := by
  obtain ⟨total,last,out,htotal,hevent,hgraph,hword,hleft,hgap,hmark,hsep,hbank,_hfar,hsegment⟩ :=
    increment_step_frame state path name leaf notRoot n operation graph values graphTail more value pad
      hlen layout origin h separator t hentry space room word left gap right delimiter bank
  exact ⟨total,last,out,htotal,hevent,hgraph,hword,hleft,hgap,hmark,hsep,hbank,hsegment⟩

#print axioms increment_to_first_successor_padded
#print axioms increment_from_parser_to_first_successor_padded
#print axioms increment_to_contracted_successor_padded
#print axioms increment_step_padded
end Shared.Beeping.NPcoNP.Grammar284PaddedIncrement
