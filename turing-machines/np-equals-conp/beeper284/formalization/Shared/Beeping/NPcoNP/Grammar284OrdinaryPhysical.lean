import Shared.Beeping.NPcoNP.Grammar284OrdinaryContraction
import Shared.Beeping.NPcoNP.Grammar284IncrementSuccessor
import Shared.Beeping.NPcoNP.Grammar284DecrementSuccessor
import Shared.Beeping.NPcoNP.Grammar284NumberInverse

/-! Composition of an ordinary physical step with its checked administrative
contraction, under explicit control-window and bank-layout hypotheses. -/
namespace Shared.Beeping.NPcoNP.Grammar284OrdinaryPhysical
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeIncSelected
open Shared.Beeping.NPcoNP.NativeAllBankScan
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
open Shared.Beeping.NPcoNP.Grammar284OrdinaryContraction
open Shared.Beeping.NPcoNP.Grammar284ContractedPhysical
open Shared.Beeping.NPcoNP.Grammar284Operational
open Shared.Beeping.NPcoNP.Grammar284IncrementSuccessor
open Shared.Beeping.NPcoNP.Grammar284DecrementSuccessor
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 30000000

/-- A nonempty output gap makes the next operation-entry cell blank. This
shows why the current true-marker entry hypotheses do not alone iterate. -/
theorem gap_blanks_operation_entry (t : Int → Bool) (origin separator : Int) (path : Path)
    (gap : ∀ q, origin+((path.length : Nat) : Int)-1<q → q<separator-1 → t q=false)
    (space : origin+((path.length : Nat) : Int)<separator-1) :
    t (origin+((path.length : Nat) : Int))=false := by
  exact gap _ (by omega) space

/-- Finish a positive physical prefix at its graph-contracted parser boundary,
preserving an arbitrary supplied bank word. -/
theorem finish_contraction_frame (start : Config 284) (steps : Nat) (mid : Int → Bool)
    (origin separator : Int) (dst : Nat) (path : Path) (name : String) (nextState : Fin 185)
    (targetAt : Grammar284.target producerFullRows producerNumbering.map 3 dst=some nextState.val)
    (hleaf : traceState557.acc.leaves[dst]?=some (path,name))
    (hsteps : 0<steps) (segment : silentSegment machine start (cfg 93 (origin+1) mid) steps)
    (word : Holds mid origin path) (left : ∀ q, q<origin → mid q=false)
    (gap : ∀ q, origin+((path.length : Nat) : Int)-1<q → q<separator-1 → mid q=false)
    (room : origin+55<separator) (right : mid (separator-1)=true) (sep : mid separator=false)
    (bankWord : List Bool) (bank : Holds mid (separator+1) bankWord) :
    ∃ (total : Nat) (last : Path × String) (out : Int → Bool), 0<total ∧
      graphLeaf nextState=some last ∧ Holds out origin last.1 ∧
      (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((last.1.length : Nat) : Int)-1<q → q<separator-1 → out q=false) ∧
      out (separator-1)=true ∧ out separator=false ∧ Holds out (separator+1) bankWord ∧
      (∀ q, separator≤q → out q=mid q) ∧
      silentSegment machine start (cfg 93 (origin+1) out) total := by
  obtain ⟨final,count,later,last,out,_,_,hlast,hmap,hword,hleft,hgap,hright,hsep,hframe,hseg⟩ :=
    contraction_runs 3 dst nextState.val targetAt (path,name) hleaf origin separator mid
      word left gap room right sep
  have hinverse := inverse_sound _ _ hmap
  have hgraph : graphLeaf nextState=some last := by
    change (producerNumbering.kept[nextState.val]?).bind
      (fun i => traceState557.acc.leaves[i]?)=some last
    rw [hinverse]
    exact hlast
  have hbank : Holds out (separator+1) bankWord := by
    apply holds_transport mid out (separator+1) bankWord bank
    intro q hq _
    exact (hframe q (by omega)).symm
  exact ⟨steps+later,last,out,by omega,hgraph,hword,hleft,hgap,hright,hsep,hbank,hframe,
    segAdd machine _ _ _ steps later segment hseg⟩

theorem finish_contraction (start : Config 284) (steps : Nat) (mid : Int → Bool)
    (origin separator : Int) (dst : Nat) (path : Path) (name : String) (nextState : Fin 185)
    (targetAt : Grammar284.target producerFullRows producerNumbering.map 3 dst=some nextState.val)
    (hleaf : traceState557.acc.leaves[dst]?=some (path,name))
    (hsteps : 0<steps) (segment : silentSegment machine start (cfg 93 (origin+1) mid) steps)
    (word : Holds mid origin path) (left : ∀ q, q<origin → mid q=false)
    (gap : ∀ q, origin+((path.length : Nat) : Int)-1<q → q<separator-1 → mid q=false)
    (room : origin+55<separator) (right : mid (separator-1)=true) (sep : mid separator=false)
    (bankWord : List Bool) (bank : Holds mid (separator+1) bankWord) :
    ∃ (total : Nat) (last : Path × String) (out : Int → Bool), 0<total ∧
      graphLeaf nextState=some last ∧ Holds out origin last.1 ∧
      (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((last.1.length : Nat) : Int)-1<q → q<separator-1 → out q=false) ∧
      out (separator-1)=true ∧ out separator=false ∧ Holds out (separator+1) bankWord ∧
      silentSegment machine start (cfg 93 (origin+1) out) total := by
  obtain ⟨total,last,out,htotal,hgraph,hword,hleft,hgap,hright,hsep,hbank,_hframe,hseg⟩ :=
    finish_contraction_frame start steps mid origin separator dst path name nextState targetAt hleaf hsteps
      segment word left gap room right sep bankWord bank
  exact ⟨total,last,out,htotal,hgraph,hword,hleft,hgap,hright,hsep,hbank,hseg⟩

/-- A supplied increment parser window executes the graph operation and its
entire administrative contraction with the graph bank and silent event. -/
theorem increment_to_contracted_successor (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (notRoot : state.val≠184)
    (n : Fin 12) (operation : namedOperation name=some (n,true))
    (graph : Bank 12) (values graphTail more : List Nat) (value : Nat)
    (hlen : values.length=n.val) (layout : arrayBank graph=values++value::graphTail)
    (origin h : Int) (t : Int → Bool) (k : Nat)
    (hentry : h=origin+((path.length : Nat) : Int)) (hk : 0<k)
    (room : origin+55<h+3+(k : Int)) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false) (marker : t h=true)
    (z1 : t (h+1)=false) (z2 : t (h+2)=false)
    (control : ∀ i : Nat, i<k → t (h+3+(i : Int))=true)
    (delimiter : t (h+3+(k : Int))=false)
    (bank : Holds t (h+4+(k : Int))
      (encode (values++value::(graphTail++more)) ++ [false])) :
    let result := target.system.step ⟨state,graph⟩
    ∃ (total : Nat) (last : Path × String) (out : Int → Bool), 0<total ∧ result.2=[] ∧
      graphLeaf result.1.state=some last ∧ Holds out origin last.1 ∧
      (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((last.1.length : Nat) : Int)-1<q → q<(h+3+(k : Int))-1 → out q=false) ∧
      out ((h+3+(k : Int))-1)=true ∧ out (h+3+(k : Int))=false ∧
      Holds out ((h+3+(k : Int))+1) (encode (arrayBank (target.system.step ⟨state,graph⟩).1.bank++more)) ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) total := by
  dsimp only
  obtain ⟨dst,next,nextName,steps,mid,hsucc,hleaf,hsteps,hevent,hstate,hword,hbank,hleft,hgap,hsep,hright,hsegment⟩ :=
    increment_from_parser_to_first_successor_exact state path name leaf notRoot n operation graph values graphTail more value hlen layout origin h t k hentry hk room word left marker z1 z2 control delimiter bank
  have hc := successor_contracts state path name leaf n true operation 0 dst
    (by exact Or.inl rfl) hsucc
  have targetAt : Grammar284.target producerFullRows producerNumbering.map 3 dst=
      some (target.system.step ⟨state,graph⟩).1.state.val := by
    rw [hstate]
    simpa using hc
  have hbank' : Holds mid ((h+3+(k : Int))+1) (encode (arrayBank (target.system.step ⟨state,graph⟩).1.bank++more)) := by
    have he : h+3+(k : Int)+1=h+4+(k : Int) := by omega
    simpa only [he] using hbank
  obtain ⟨total,last,out,htotal,hgraph,hout,houtleft,houtgap,houtmark,houtsep,houtbank,hfinal⟩ :=
    finish_contraction (cfg 93 (origin+1) t) steps mid origin (h+3+(k : Int)) dst next nextName
      (target.system.step ⟨state,graph⟩).1.state targetAt hleaf hsteps hsegment hword hleft hgap room hright hsep _ hbank'
  exact ⟨total,last,out,htotal,hevent,hgraph,hout,houtleft,houtgap,houtmark,houtsep,houtbank,hfinal⟩

/-- A supplied positive parser window executes the graph operation and its
entire administrative contraction with the graph bank and silent event. -/
theorem positive_to_contracted_successor (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (notRoot : state.val≠184)
    (n : Fin 12) (operation : namedOperation name=some (n,false))
    (graph : Bank 12) (values graphTail more : List Nat) (value : Nat)
    (hlen : values.length=n.val) (layout : arrayBank graph=values++(value+1)::graphTail)
    (origin h separator : Int) (t : Int → Bool)
    (hentry : h=origin+((path.length : Nat) : Int)) (hlong : h+4≤separator)
    (room : origin+55<separator) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false) (marker : t h=true)
    (z1 : t (h+1)=false) (z2 : t (h+2)=false)
    (control : ∀ q, h+3≤q → q<separator → t q=true) (delimiter : t separator=false)
    (bank : Holds t (separator+1)
      (encode values ++ (encode ((value+1)::(graphTail++more)) ++ [false,false]))) :
    let result := target.system.step ⟨state,graph⟩
    ∃ (total : Nat) (last : Path × String) (out : Int → Bool), 0<total ∧ result.2=[] ∧
      graphLeaf result.1.state=some last ∧ Holds out origin last.1 ∧
      (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((last.1.length : Nat) : Int)-1<q → q<(separator)-1 → out q=false) ∧
      out ((separator)-1)=true ∧ out (separator)=false ∧
      Holds out ((separator)+1) (encode (arrayBank (target.system.step ⟨state,graph⟩).1.bank++more++[0]) ++ [false]) ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) total := by
  dsimp only
  obtain ⟨dst,next,nextName,steps,mid,hsucc,hleaf,hsteps,hevent,hstate,hword,hbank,hleft,hgap,hsep,hright,hsegment⟩ :=
    positive_from_parser_to_first_successor_exact state path name leaf notRoot n operation graph values graphTail more value hlen layout origin h separator t hentry hlong room word left marker z1 z2 control delimiter bank
  have hc := successor_contracts state path name leaf n false operation 0 dst
    (by exact Or.inl rfl) hsucc
  have targetAt : Grammar284.target producerFullRows producerNumbering.map 3 dst=
      some (target.system.step ⟨state,graph⟩).1.state.val := by
    rw [hstate]
    simpa using hc
  have hbank' : Holds mid ((separator)+1) (encode (arrayBank (target.system.step ⟨state,graph⟩).1.bank++more++[0]) ++ [false]) := by
    exact hbank
  obtain ⟨total,last,out,htotal,hgraph,hout,houtleft,houtgap,houtmark,houtsep,houtbank,hfinal⟩ :=
    finish_contraction (cfg 93 (origin+1) t) steps mid origin (separator) dst next nextName
      (target.system.step ⟨state,graph⟩).1.state targetAt hleaf hsteps hsegment hword hleft hgap room hright hsep _ hbank'
  exact ⟨total,last,out,htotal,hevent,hgraph,hout,houtleft,houtgap,houtmark,houtsep,houtbank,hfinal⟩

/-- A supplied zero parser window executes the graph operation and its
entire administrative contraction with the graph bank and silent event. -/
theorem zero_to_contracted_successor_frame (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (notRoot : state.val≠184)
    (n : Fin 12) (operation : namedOperation name=some (n,false))
    (graph : Bank 12) (values graphTail more : List Nat) (pad : List Bool)
    (hlen : values.length=n.val) (layout : arrayBank graph=values++0::graphTail)
    (origin h separator : Int) (t : Int → Bool)
    (hentry : h=origin+((path.length : Nat) : Int)) (hlong : h+4≤separator)
    (room : origin+55<separator) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false) (marker : t h=true)
    (z1 : t (h+1)=false) (z2 : t (h+2)=false)
    (control : ∀ q, h+3≤q → q<separator → t q=true) (delimiter : t separator=false)
    (bank : Holds t (separator+1) (encode (arrayBank graph++more) ++ pad)) :
    let result := target.system.step ⟨state,graph⟩
    ∃ (total : Nat) (last : Path × String) (out : Int → Bool), 0<total ∧ result.2=[] ∧
      graphLeaf result.1.state=some last ∧ Holds out origin last.1 ∧
      (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((last.1.length : Nat) : Int)-1<q → q<(separator)-1 → out q=false) ∧
      out ((separator)-1)=true ∧ out (separator)=false ∧
      Holds out ((separator)+1) (encode (arrayBank (target.system.step ⟨state,graph⟩).1.bank++more) ++ pad) ∧
      (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) total := by
  dsimp only
  obtain ⟨dst,next,nextName,steps,mid,hsucc,hleaf,hsteps,hevent,hstate,hword,hbank,hleft,hgap,hsep,hright,hfar,hsegment⟩ :=
    zero_from_parser_to_first_successor_frame state path name leaf notRoot n operation graph values graphTail more pad hlen layout origin h separator t hentry hlong room word left marker z1 z2 control delimiter bank
  have hc := successor_contracts state path name leaf n false operation 1 dst
    (by exact Or.inr ⟨rfl,rfl⟩) hsucc
  have targetAt : Grammar284.target producerFullRows producerNumbering.map 3 dst=
      some (target.system.step ⟨state,graph⟩).1.state.val := by
    rw [hstate]
    simpa using hc
  have hbank' : Holds mid ((separator)+1) (encode (arrayBank (target.system.step ⟨state,graph⟩).1.bank++more) ++ pad) := by
    exact hbank
  obtain ⟨total,last,out,htotal,hgraph,hout,houtleft,houtgap,houtmark,houtsep,houtbank,houtframe,hfinal⟩ :=
    finish_contraction_frame (cfg 93 (origin+1) t) steps mid origin (separator) dst next nextName
      (target.system.step ⟨state,graph⟩).1.state targetAt hleaf hsteps hsegment hword hleft hgap room hright hsep _ hbank'
  refine ⟨total,last,out,htotal,hevent,hgraph,hout,houtleft,houtgap,houtmark,houtsep,houtbank,?_,hfinal⟩
  intro q hq
  exact (houtframe q hq).trans (hfar q hq)

theorem zero_to_contracted_successor (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (notRoot : state.val≠184)
    (n : Fin 12) (operation : namedOperation name=some (n,false))
    (graph : Bank 12) (values graphTail more : List Nat) (pad : List Bool)
    (hlen : values.length=n.val) (layout : arrayBank graph=values++0::graphTail)
    (origin h separator : Int) (t : Int → Bool)
    (hentry : h=origin+((path.length : Nat) : Int)) (hlong : h+4≤separator)
    (room : origin+55<separator) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false) (marker : t h=true)
    (z1 : t (h+1)=false) (z2 : t (h+2)=false)
    (control : ∀ q, h+3≤q → q<separator → t q=true) (delimiter : t separator=false)
    (bank : Holds t (separator+1) (encode (arrayBank graph++more) ++ pad)) :
    let result := target.system.step ⟨state,graph⟩
    ∃ (total : Nat) (last : Path × String) (out : Int → Bool), 0<total ∧ result.2=[] ∧
      graphLeaf result.1.state=some last ∧ Holds out origin last.1 ∧
      (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((last.1.length : Nat) : Int)-1<q → q<(separator)-1 → out q=false) ∧
      out ((separator)-1)=true ∧ out (separator)=false ∧
      Holds out ((separator)+1) (encode (arrayBank (target.system.step ⟨state,graph⟩).1.bank++more) ++ pad) ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) total := by
  obtain ⟨total,last,out,htotal,hevent,hgraph,hword,hleft,hgap,hmark,hsep,hbank,_hfar,hsegment⟩ :=
    zero_to_contracted_successor_frame state path name leaf notRoot n operation graph values graphTail more pad
      hlen layout origin h separator t hentry hlong room word left marker z1 z2 control delimiter bank
  exact ⟨total,last,out,htotal,hevent,hgraph,hword,hleft,hgap,hmark,hsep,hbank,hsegment⟩

#print axioms finish_contraction
#print axioms gap_blanks_operation_entry
#print axioms increment_to_contracted_successor
#print axioms positive_to_contracted_successor
#print axioms zero_to_contracted_successor
end Shared.Beeping.NPcoNP.Grammar284OrdinaryPhysical
