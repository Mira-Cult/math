import Shared.Beeping.NPcoNP.Grammar284ZeroTailFrame
import Shared.Beeping.NPcoNP.Grammar284PhysicalSuccessor
import Shared.Beeping.NPcoNP.Grammar284BankCorrespondence
import Shared.Beeping.NPcoNP.NativeGrammarSelectorDispatch
import Shared.Beeping.NPcoNP.NativeAllBankDecrementNext

/-! Ordinary decrement bank effects through the first expanded successor.
Administrative jumps, root return and reachable-window recurrence are separate. -/
namespace Shared.Beeping.NPcoNP.Grammar284DecrementSuccessor
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeGrammarPreterminalDispatch
open Shared.Beeping.NPcoNP.NativeGrammarAdministrativeDispatch
open Shared.Beeping.NPcoNP.NativeGrammarSelectorDispatch
open Shared.Beeping.NPcoNP.Grammar284SuccessorShape
open Shared.Beeping.NPcoNP.NativeAllBankScan
open Shared.Beeping.NPcoNP.NativeAllBankDecrement
open Shared.Beeping.NPcoNP.NativeAllBankDecrementNext
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.Grammar284ExpansionPaths
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
open Shared.Beeping.NPcoNP.Grammar284GraphOperation
open Shared.Beeping.NPcoNP.Grammar284BankCorrespondence
open Shared.Beeping.NPcoNP.Grammar284PhysicalSuccessor
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- A positive ordinary decrement implements the graph bank effect and reaches
the first full-grammar successor silently under supplied tape conditions. -/
theorem positive_to_first_successor_exact (state : Fin 185) (path : Path) (name : String)
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
    ∃ (dst : Nat) (next : Path) (nextName : String) (steps : Nat) (out : Int → Bool),
      successor traceState557.acc.starts path 0=some dst ∧
      traceState557.acc.leaves[dst]?=some (next,nextName) ∧
      0<steps ∧ result.2=[] ∧ result.1.state=target.code[state].yes ∧
      Holds out origin next ∧ Holds out (separator+1) (encode (arrayBank result.1.bank++more++[0]) ++ [false]) ∧
      (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((next.length : Nat) : Int)-1<q → q<separator-1 → out q=false) ∧
      out separator=false ∧ out (separator-1)=true ∧
      silentSegment machine (cfg (operationAt n false) h t) (cfg 93 (origin+1) out) steps := by
  dsimp only
  let pos := separator+1+((encode values).length : Int)
  have gstep := graph_decrement_positive_step state path name leaf n operation graph values graphTail value hlen layout
  have gbank : arrayBank (target.system.step ⟨state,graph⟩).1.bank=values++value::graphTail := by
    rw [gstep]
    exact write_selected_array graph n values graphTail (value+1) value hlen layout
  obtain ⟨a,mid,ha,hbank,hzero,hzero1,hmark,hcontrol,hsep,hframe,_hbound,hseg⟩ :=
    positive_to1 n h separator t values value (graphTail++more) hlen hlong marker z1 z2 control delimiter bank
  have hmidword : Holds mid origin path := by
    apply holds_transport t mid origin path word
    intro q hq hq'
    exact (hframe q (by omega) (by omega) (by omega)).symm
  have hmidleft : ∀ q, q<origin → mid q=false := by
    intro q hq
    rw [hframe q (by omega) (by omega) (by omega)]
    exact left q hq
  have hbetween : ∀ q, h-1<q → q<h+2 → mid q=false := by
    intro q hq hq'
    have he : q=h ∨ q=h+1 := by omega
    rcases he with rfl | rfl
    · exact hzero
    · exact hzero1
  obtain ⟨dst,next,nextName,b,out,hsucc,hnext,_hwalk,hb,hnextWord,houtleft,houtgap,houtsep,hright,hbankFrame,hcarry⟩ :=
    carry_to_first_successor_exact state path name leaf notRoot n false operation 0 (Or.inl rfl)
      (by intro _; rfl) mid origin (h-1) (h+2) separator (by simp [hentry]) room hmidword hmidleft
      (by omega) hmark hbetween (by omega)
      (by intro q hq hq'; exact hcontrol q (by omega) hq') hsep
  have houtbank : Holds out (separator+1)
      (encode values ++ (encode (value::(graphTail++more)) ++ [true,false,false])) := by
    apply holds_transport mid out (separator+1) _ hbank
    intro q hq _
    exact (hbankFrame q (by omega)).symm
  refine ⟨dst,next,nextName,a+b,out,hsucc,hnext,by omega,?_,?_,hnextWord,?_,houtleft,houtgap,houtsep,hright,?_⟩
  · simp only [gstep]
  · simp only [gstep]
  · rw [gbank]
    simpa [encode_append,encode,block,List.append_assoc] using houtbank
  · exact segAdd machine _ _ _ a b hseg hcarry

/-- Original decrement interface. -/
theorem positive_to_first_successor (state : Fin 185) (path : Path) (name : String)
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
    ∃ (dst : Nat) (next : Path) (nextName : String) (steps : Nat) (out : Int → Bool),
      successor traceState557.acc.starts path 0=some dst ∧
      traceState557.acc.leaves[dst]?=some (next,nextName) ∧
      0<steps ∧ result.2=[] ∧ result.1.state=target.code[state].yes ∧
      Holds out origin next ∧ Holds out (separator+1) (encode (arrayBank result.1.bank++more++[0]) ++ [false]) ∧
      out (separator-1)=true ∧
      silentSegment machine (cfg (operationAt n false) h t) (cfg 93 (origin+1) out) steps := by
  obtain ⟨dst,next,nextName,steps,out,hsucc,hnext,hs,hevent,hstate,hw,hbank,_,_,_,hr,hseg⟩ := positive_to_first_successor_exact state path name leaf notRoot n operation graph values graphTail more value hlen layout origin h separator t hentry hlong room word left marker z1 z2 control delimiter bank
  exact ⟨dst,next,nextName,steps,out,hsucc,hnext,hs,hevent,hstate,hw,hbank,hr,hseg⟩

/-- A zero ordinary decrement preserves the graph bank and reaches the first
full-grammar no-branch successor silently under supplied tape conditions. -/
theorem zero_to_first_successor_exact (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (notRoot : state.val≠184)
    (n : Fin 12) (operation : namedOperation name=some (n,false))
    (graph : Bank 12) (values graphTail more : List Nat) (pad : List Bool)
    (hlen : values.length=n.val) (layout : arrayBank graph=values++0::graphTail)
    (origin h separator : Int) (t : Int → Bool)
    (hentry : h=origin+((path.length : Nat) : Int)) (hlong : h+4≤separator)
    (room : origin+55<separator) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false) (marker : t h=true) (prev : t (h-1)=false)
    (z1 : t (h+1)=false) (z2 : t (h+2)=false)
    (control : ∀ q, h+3≤q → q<separator → t q=true) (delimiter : t separator=false)
    (bank : Holds t (separator+1) (encode (arrayBank graph++more) ++ pad)) :
    let result := target.system.step ⟨state,graph⟩
    ∃ (dst : Nat) (next : Path) (nextName : String) (steps : Nat) (out : Int → Bool),
      successor traceState557.acc.starts path 1=some dst ∧
      traceState557.acc.leaves[dst]?=some (next,nextName) ∧
      0<steps ∧ result.2=[] ∧ result.1.state=target.code[state].no ∧
      Holds out origin next ∧ Holds out (separator+1) (encode (arrayBank result.1.bank++more) ++ pad) ∧
      (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((next.length : Nat) : Int)-1<q → q<separator-1 → out q=false) ∧
      out separator=false ∧ out (separator-1)=true ∧
      silentSegment machine (cfg (operationAt n false) h t) (cfg 93 (origin+1) out) steps := by
  obtain ⟨dst,next,nextName,steps,out,hsucc,hnext,hsteps,hevent,hstate,hword,hbank,hleft,hgap,hsep,hmark,_hfar,hsegment⟩ :=
    Shared.Beeping.NPcoNP.Grammar284ZeroTailFrame.zero_to_first_successor_frame state path name leaf notRoot n operation
      graph values graphTail more pad hlen layout origin h separator t hentry hlong room word left marker prev z1 z2 control delimiter bank
  exact ⟨dst,next,nextName,steps,out,hsucc,hnext,hsteps,hevent,hstate,hword,hbank,hleft,hgap,hsep,hmark,hsegment⟩

/-- Original decrement interface. -/
theorem zero_to_first_successor (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (notRoot : state.val≠184)
    (n : Fin 12) (operation : namedOperation name=some (n,false))
    (graph : Bank 12) (values graphTail more : List Nat) (pad : List Bool)
    (hlen : values.length=n.val) (layout : arrayBank graph=values++0::graphTail)
    (origin h separator : Int) (t : Int → Bool)
    (hentry : h=origin+((path.length : Nat) : Int)) (hlong : h+4≤separator)
    (room : origin+55<separator) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false) (marker : t h=true) (prev : t (h-1)=false)
    (z1 : t (h+1)=false) (z2 : t (h+2)=false)
    (control : ∀ q, h+3≤q → q<separator → t q=true) (delimiter : t separator=false)
    (bank : Holds t (separator+1) (encode (arrayBank graph++more) ++ pad)) :
    let result := target.system.step ⟨state,graph⟩
    ∃ (dst : Nat) (next : Path) (nextName : String) (steps : Nat) (out : Int → Bool),
      successor traceState557.acc.starts path 1=some dst ∧
      traceState557.acc.leaves[dst]?=some (next,nextName) ∧
      0<steps ∧ result.2=[] ∧ result.1.state=target.code[state].no ∧
      Holds out origin next ∧ Holds out (separator+1) (encode (arrayBank result.1.bank++more) ++ pad) ∧
      out (separator-1)=true ∧
      silentSegment machine (cfg (operationAt n false) h t) (cfg 93 (origin+1) out) steps := by
  obtain ⟨dst,next,nextName,steps,out,hsucc,hnext,hs,hevent,hstate,hw,hbank,_,_,_,hr,hseg⟩ := zero_to_first_successor_exact state path name leaf notRoot n operation graph values graphTail more pad hlen layout origin h separator t hentry hlong room word left marker prev z1 z2 control delimiter bank
  exact ⟨dst,next,nextName,steps,out,hsucc,hnext,hs,hevent,hstate,hw,hbank,hr,hseg⟩

/-- Every checked decrement leaf ends in a zero control bit. -/
theorem decrement_last_control_zero (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (notRoot : state.val≠184)
    (n : Fin 12) (operation : namedOperation name=some (n,false))
    (origin h : Int) (t : Int → Bool) (hentry : h=origin+((path.length : Nat) : Int))
    (word : Holds t origin path) : t (h-1)=false := by
  have checks := ordinary_successor_shapes state path name leaf notRoot n false operation
  have last := (checks.2.2 rfl).2.2
  have he : path.dropLast ++ [false]=path :=
    List.dropLast_append_getLast? false (by simp [last])
  have hw : Holds t origin (path.dropLast ++ [false]) := by rw [he]; exact word
  obtain ⟨_,htail⟩ := holds_split t origin path.dropLast [false] hw
  have hlast : t (origin+(path.dropLast.length : Int))=false := by simpa [Holds] using htail
  have hlength : path.dropLast.length+1=path.length := by
    have hh := congrArg List.length he
    simpa using hh
  have hcoord : origin+(path.dropLast.length : Int)=h-1 := by omega
  simpa only [hcoord] using hlast

/-- Every named decrement path dispatches from its parser boundary to the
correct literal operation entry on the unchanged supplied tape. -/
theorem decrement_from_parser (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (n : Fin 12)
    (operation : namedOperation name=some (n,false)) (origin h : Int) (t : Int → Bool)
    (hentry : h=origin+((path.length : Nat) : Int)) (word : Holds t origin path) :
    silentSegment machine (cfg 93 (origin+1) t) (cfg (operationAt n false) h t) path.tail.length := by
  have member := graph_leaf_member state path name leaf
  have walk : PreparedWalk path (.op name) :=
    expanded_leaf_follows traceState557.acc producerExpand (path,name) member
  obtain ⟨_,tail⟩ := prepared_head_tail t origin path name walk word
  have target := named_operation_entry (path,name) member n false operation
  have dispatch := expanded_leaf_dispatch_to_entry traceState557.acc producerExpand (path,name) member
    (operationAt n false) target (origin+1) t tail
  have hlenPath : (path.tail.length : Int)+1=(path.length : Int) := by
    obtain ⟨raw,he,_⟩ := walk
    rw [he]
    simp [preparedPrefix]
  have he : origin+1+(path.tail.length : Int)=h := by omega
  simpa only [he] using dispatch

/-- From the parser boundary, a positive decrement reaches the first grammar
successor and matches the graph bank and event effect. -/
theorem positive_from_parser_to_first_successor_exact (state : Fin 185) (path : Path) (name : String)
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
    ∃ (dst : Nat) (next : Path) (nextName : String) (steps : Nat) (out : Int → Bool),
      successor traceState557.acc.starts path 0=some dst ∧
      traceState557.acc.leaves[dst]?=some (next,nextName) ∧
      0<steps ∧ result.2=[] ∧ result.1.state=target.code[state].yes ∧
      Holds out origin next ∧ Holds out (separator+1) (encode (arrayBank result.1.bank++more++[0]) ++ [false]) ∧
      (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((next.length : Nat) : Int)-1<q → q<separator-1 → out q=false) ∧
      out separator=false ∧ out (separator-1)=true ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) steps := by
  dsimp only
  have dispatch := decrement_from_parser state path name leaf n operation origin h t hentry word
  obtain ⟨dst,next,nextName,k,out,hsucc,hnext,hk,hevent,hstate,hword,hbank,hleft,hgap,hsep,hmark,hseg⟩ :=
    positive_to_first_successor_exact state path name leaf notRoot n operation graph values graphTail more value
      hlen layout origin h separator t hentry hlong room word left marker z1 z2 control delimiter bank
  exact ⟨dst,next,nextName,path.tail.length+k,out,hsucc,hnext,by omega,hevent,hstate,hword,hbank,hleft,hgap,hsep,hmark,
    segAdd machine _ _ _ path.tail.length k dispatch hseg⟩

/-- Original decrement parser interface. -/
theorem positive_from_parser_to_first_successor (state : Fin 185) (path : Path) (name : String)
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
    ∃ (dst : Nat) (next : Path) (nextName : String) (steps : Nat) (out : Int → Bool),
      successor traceState557.acc.starts path 0=some dst ∧
      traceState557.acc.leaves[dst]?=some (next,nextName) ∧
      0<steps ∧ result.2=[] ∧ result.1.state=target.code[state].yes ∧
      Holds out origin next ∧ Holds out (separator+1) (encode (arrayBank result.1.bank++more++[0]) ++ [false]) ∧
      out (separator-1)=true ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) steps := by
  obtain ⟨dst,next,nextName,steps,out,hsucc,hnext,hs,hevent,hstate,hw,hbank,_,_,_,hr,hseg⟩ := positive_from_parser_to_first_successor_exact state path name leaf notRoot n operation graph values graphTail more value hlen layout origin h separator t hentry hlong room word left marker z1 z2 control delimiter bank
  exact ⟨dst,next,nextName,steps,out,hsucc,hnext,hs,hevent,hstate,hw,hbank,hr,hseg⟩

/-- From the parser boundary, a zero decrement reaches the first grammar
no-branch successor and matches the graph bank and event effect. The previous
control bit is derived from the checked producer path. -/
theorem zero_from_parser_to_first_successor_frame (state : Fin 185) (path : Path) (name : String)
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
    ∃ (dst : Nat) (next : Path) (nextName : String) (steps : Nat) (out : Int → Bool),
      successor traceState557.acc.starts path 1=some dst ∧
      traceState557.acc.leaves[dst]?=some (next,nextName) ∧
      0<steps ∧ result.2=[] ∧ result.1.state=target.code[state].no ∧
      Holds out origin next ∧ Holds out (separator+1) (encode (arrayBank result.1.bank++more) ++ pad) ∧
      (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((next.length : Nat) : Int)-1<q → q<separator-1 → out q=false) ∧
      out separator=false ∧ out (separator-1)=true ∧
      (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) steps := by
  dsimp only
  have dispatch := decrement_from_parser state path name leaf n operation origin h t hentry word
  have prev := decrement_last_control_zero state path name leaf notRoot n operation origin h t hentry word
  obtain ⟨dst,next,nextName,k,out,hsucc,hnext,hk,hevent,hstate,hword,hbank,hleft,hgap,hsep,hmark,hfar,hseg⟩ :=
    Shared.Beeping.NPcoNP.Grammar284ZeroTailFrame.zero_to_first_successor_frame state path name leaf notRoot n operation graph values graphTail more pad
      hlen layout origin h separator t hentry hlong room word left marker prev z1 z2 control delimiter bank
  exact ⟨dst,next,nextName,path.tail.length+k,out,hsucc,hnext,by omega,hevent,hstate,hword,hbank,hleft,hgap,hsep,hmark,hfar,
    segAdd machine _ _ _ path.tail.length k dispatch hseg⟩

theorem zero_from_parser_to_first_successor_exact (state : Fin 185) (path : Path) (name : String)
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
    ∃ (dst : Nat) (next : Path) (nextName : String) (steps : Nat) (out : Int → Bool),
      successor traceState557.acc.starts path 1=some dst ∧
      traceState557.acc.leaves[dst]?=some (next,nextName) ∧
      0<steps ∧ result.2=[] ∧ result.1.state=target.code[state].no ∧
      Holds out origin next ∧ Holds out (separator+1) (encode (arrayBank result.1.bank++more) ++ pad) ∧
      (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((next.length : Nat) : Int)-1<q → q<separator-1 → out q=false) ∧
      out separator=false ∧ out (separator-1)=true ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) steps := by
  obtain ⟨dst,next,nextName,steps,out,hsucc,hnext,hsteps,hevent,hstate,hword,hbank,hleft,hgap,hsep,hmark,_hfar,hsegment⟩ :=
    zero_from_parser_to_first_successor_frame state path name leaf notRoot n operation graph values graphTail more pad
      hlen layout origin h separator t hentry hlong room word left marker z1 z2 control delimiter bank
  exact ⟨dst,next,nextName,steps,out,hsucc,hnext,hsteps,hevent,hstate,hword,hbank,hleft,hgap,hsep,hmark,hsegment⟩

/-- Original decrement parser interface. -/
theorem zero_from_parser_to_first_successor (state : Fin 185) (path : Path) (name : String)
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
    ∃ (dst : Nat) (next : Path) (nextName : String) (steps : Nat) (out : Int → Bool),
      successor traceState557.acc.starts path 1=some dst ∧
      traceState557.acc.leaves[dst]?=some (next,nextName) ∧
      0<steps ∧ result.2=[] ∧ result.1.state=target.code[state].no ∧
      Holds out origin next ∧ Holds out (separator+1) (encode (arrayBank result.1.bank++more) ++ pad) ∧
      out (separator-1)=true ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) steps := by
  obtain ⟨dst,next,nextName,steps,out,hsucc,hnext,hs,hevent,hstate,hw,hbank,_,_,_,hr,hseg⟩ := zero_from_parser_to_first_successor_exact state path name leaf notRoot n operation graph values graphTail more pad hlen layout origin h separator t hentry hlong room word left marker z1 z2 control delimiter bank
  exact ⟨dst,next,nextName,steps,out,hsucc,hnext,hs,hevent,hstate,hw,hbank,hr,hseg⟩

#print axioms positive_to_first_successor_exact
#print axioms positive_to_first_successor
#print axioms zero_to_first_successor_exact
#print axioms zero_to_first_successor
#print axioms decrement_last_control_zero
#print axioms decrement_from_parser
#print axioms positive_from_parser_to_first_successor_exact
#print axioms positive_from_parser_to_first_successor
#print axioms zero_from_parser_to_first_successor_exact
#print axioms zero_from_parser_to_first_successor
end Shared.Beeping.NPcoNP.Grammar284DecrementSuccessor
