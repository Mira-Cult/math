import Shared.Beeping.NPcoNP.Grammar284OrdinaryPreparation
import Shared.Beeping.NPcoNP.Grammar284OrdinaryPhysical

/-! A supplied sufficiently spaced parser window performs a named ordinary graph
step, including literal preparation and all administrative contraction jumps. -/
namespace Shared.Beeping.NPcoNP.Grammar284PreparedOrdinaryStep
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeIncSelected
open Shared.Beeping.NPcoNP.NativeAllBankScan
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
open Shared.Beeping.NPcoNP.Grammar284OrdinaryPreparation
open Shared.Beeping.NPcoNP.Grammar284OrdinaryPhysical
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

theorem positive_step (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (notRoot : state.val≠184)
    (n : Fin 12) (operation : namedOperation name=some (n,false))
    (graph : Bank 12) (values graphTail more : List Nat) (value : Nat)
    (hlen : values.length=n.val) (layout : arrayBank graph=values++(value+1)::graphTail)
    (origin h separator : Int) (t : Int → Bool)
    (hentry : h=origin+((path.length : Nat) : Int)) (space : h+4≤separator)
    (room : origin+55<separator) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false)
    (gap : ∀ q, h≤q → q<separator-1 → t q=false)
    (right : t (separator-1)=true) (delimiter : t separator=false)
    (bank : Holds t (separator+1)
      (encode values ++ (encode ((value+1)::(graphTail++more)) ++ [false,false]))) :
    let result := target.system.step ⟨state,graph⟩
    ∃ (total : Nat) (last : Path × String) (out : Int → Bool), 0<total ∧ result.2=[] ∧
      graphLeaf result.1.state=some last ∧ Holds out origin last.1 ∧
      (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((last.1.length : Nat) : Int)-1<q → q<separator-1 → out q=false) ∧
      out (separator-1)=true ∧ out separator=false ∧
      Holds out (separator+1) (encode (arrayBank result.1.bank++more++[0]) ++ [false]) ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) total := by
  dsimp only
  obtain ⟨a,mid,ha,hword,hleft,hmarker,hz1,hz2,hcontrol,hsep,hframe,hprep⟩ :=
    prepare_from_parser state path name leaf n false operation origin h separator t
      hentry space word left gap right delimiter
  have hbank : Holds mid (separator+1)
      (encode values ++ (encode ((value+1)::(graphTail++more)) ++ [false,false])) := by
    apply holds_transport t mid (separator+1) _ bank
    intro q hq _
    exact (hframe q (by omega)).symm
  obtain ⟨b,last,out,hb,hevent,hgraph,hout,houtleft,houtgap,hright,houtsep,houtbank,hstep⟩ :=
    positive_to_contracted_successor state path name leaf notRoot n operation graph values graphTail more value
      hlen layout origin h separator mid hentry space room hword hleft hmarker hz1 hz2 hcontrol hsep hbank
  exact ⟨a+b,last,out,by omega,hevent,hgraph,hout,houtleft,houtgap,hright,houtsep,houtbank,
    segAdd machine _ _ _ a b hprep hstep⟩

theorem zero_step_frame (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (notRoot : state.val≠184)
    (n : Fin 12) (operation : namedOperation name=some (n,false))
    (graph : Bank 12) (values graphTail more : List Nat) (pad : List Bool)
    (hlen : values.length=n.val) (layout : arrayBank graph=values++0::graphTail)
    (origin h separator : Int) (t : Int → Bool)
    (hentry : h=origin+((path.length : Nat) : Int)) (space : h+4≤separator)
    (room : origin+55<separator) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false)
    (gap : ∀ q, h≤q → q<separator-1 → t q=false)
    (right : t (separator-1)=true) (delimiter : t separator=false)
    (bank : Holds t (separator+1) (encode (arrayBank graph++more) ++ pad)) :
    let result := target.system.step ⟨state,graph⟩
    ∃ (total : Nat) (last : Path × String) (out : Int → Bool), 0<total ∧ result.2=[] ∧
      graphLeaf result.1.state=some last ∧ Holds out origin last.1 ∧
      (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((last.1.length : Nat) : Int)-1<q → q<separator-1 → out q=false) ∧
      out (separator-1)=true ∧ out separator=false ∧
      Holds out (separator+1) (encode (arrayBank result.1.bank++more) ++ pad) ∧
      (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) total := by
  dsimp only
  obtain ⟨a,mid,ha,hword,hleft,hmarker,hz1,hz2,hcontrol,hsep,hframe,hprep⟩ :=
    prepare_from_parser state path name leaf n false operation origin h separator t
      hentry space word left gap right delimiter
  have hbank : Holds mid (separator+1) (encode (arrayBank graph++more) ++ pad) := by
    apply holds_transport t mid (separator+1) _ bank
    intro q hq _
    exact (hframe q (by omega)).symm
  obtain ⟨b,last,out,hb,hevent,hgraph,hout,houtleft,houtgap,hright,houtsep,houtbank,houtfar,hstep⟩ :=
    zero_to_contracted_successor_frame state path name leaf notRoot n operation graph values graphTail more pad
      hlen layout origin h separator mid hentry space room hword hleft hmarker hz1 hz2 hcontrol hsep hbank
  refine ⟨a+b,last,out,by omega,hevent,hgraph,hout,houtleft,houtgap,hright,houtsep,houtbank,?_,
    segAdd machine _ _ _ a b hprep hstep⟩
  intro q hq
  exact (houtfar q hq).trans (hframe q hq)

theorem zero_step (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (notRoot : state.val≠184)
    (n : Fin 12) (operation : namedOperation name=some (n,false))
    (graph : Bank 12) (values graphTail more : List Nat) (pad : List Bool)
    (hlen : values.length=n.val) (layout : arrayBank graph=values++0::graphTail)
    (origin h separator : Int) (t : Int → Bool)
    (hentry : h=origin+((path.length : Nat) : Int)) (space : h+4≤separator)
    (room : origin+55<separator) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false)
    (gap : ∀ q, h≤q → q<separator-1 → t q=false)
    (right : t (separator-1)=true) (delimiter : t separator=false)
    (bank : Holds t (separator+1) (encode (arrayBank graph++more) ++ pad)) :
    let result := target.system.step ⟨state,graph⟩
    ∃ (total : Nat) (last : Path × String) (out : Int → Bool), 0<total ∧ result.2=[] ∧
      graphLeaf result.1.state=some last ∧ Holds out origin last.1 ∧
      (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((last.1.length : Nat) : Int)-1<q → q<separator-1 → out q=false) ∧
      out (separator-1)=true ∧ out separator=false ∧
      Holds out (separator+1) (encode (arrayBank result.1.bank++more) ++ pad) ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) total := by
  obtain ⟨total,last,out,htotal,hevent,hgraph,hword,hleft,hgap,hmark,hsep,hbank,_hfar,hsegment⟩ :=
    zero_step_frame state path name leaf notRoot n operation graph values graphTail more pad hlen layout
      origin h separator t hentry space room word left gap right delimiter bank
  exact ⟨total,last,out,htotal,hevent,hgraph,hword,hleft,hgap,hmark,hsep,hbank,hsegment⟩

theorem increment_step (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (notRoot : state.val≠184)
    (n : Fin 12) (operation : namedOperation name=some (n,true))
    (graph : Bank 12) (values graphTail more : List Nat) (value : Nat)
    (hlen : values.length=n.val) (layout : arrayBank graph=values++value::graphTail)
    (origin h separator : Int) (t : Int → Bool)
    (hentry : h=origin+((path.length : Nat) : Int)) (space : h+4≤separator)
    (room : origin+55<separator) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false)
    (gap : ∀ q, h≤q → q<separator-1 → t q=false)
    (right : t (separator-1)=true) (delimiter : t separator=false)
    (bank : Holds t (separator+1) (encode (values++value::(graphTail++more)) ++ [false])) :
    let result := target.system.step ⟨state,graph⟩
    ∃ (total : Nat) (last : Path × String) (out : Int → Bool), 0<total ∧ result.2=[] ∧
      graphLeaf result.1.state=some last ∧ Holds out origin last.1 ∧
      (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((last.1.length : Nat) : Int)-1<q → q<separator-1 → out q=false) ∧
      out (separator-1)=true ∧ out separator=false ∧
      Holds out (separator+1) (encode (arrayBank result.1.bank++more)) ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) total := by
  dsimp only
  obtain ⟨a,mid,ha,hword,hleft,hmarker,hz1,hz2,hcontrol,hsep,hframe,hprep⟩ :=
    prepare_from_parser state path name leaf n true operation origin h separator t
      hentry space word left gap right delimiter
  let k := (separator-h-3).toNat
  have hk : (k : Int)=separator-h-3 := Int.toNat_of_nonneg (by omega)
  have hpos : 0<k := by omega
  have hsepEq : h+3+(k : Int)=separator := by omega
  have hbank : Holds mid (h+4+(k : Int)) (encode (values++value::(graphTail++more)) ++ [false]) := by
    have hbank' : Holds mid (separator+1) (encode (values++value::(graphTail++more)) ++ [false]) := by
      apply holds_transport t mid (separator+1) _ bank
      intro q hq _
      exact (hframe q (by omega)).symm
    have he : h+4+(k : Int)=separator+1 := by omega
    simpa only [he] using hbank'
  have hcontrol' : ∀ i : Nat, i<k → mid (h+3+(i : Int))=true := by
    intro i hi
    exact hcontrol _ (by omega) (by omega)
  obtain ⟨b,last,out,hb,hevent,hgraph,hout,houtleft,houtgap,hright,houtsep,houtbank,hstep⟩ :=
    increment_to_contracted_successor state path name leaf notRoot n operation graph values graphTail more value
      hlen layout origin h mid k hentry hpos (by simpa only [hsepEq] using room) hword hleft
      hmarker hz1 hz2 hcontrol' (by simpa only [hsepEq] using hsep) hbank
  refine ⟨a+b,last,out,by omega,hevent,hgraph,hout,houtleft,?_,?_,?_,?_,segAdd machine _ _ _ a b hprep hstep⟩
  · simpa only [hsepEq] using houtgap
  · simpa only [hsepEq] using hright
  · simpa only [hsepEq] using houtsep
  · have he : h+3+(k : Int)+1=separator+1 := by omega
    simpa only [he] using houtbank

#print axioms increment_step
#print axioms positive_step
#print axioms zero_step
end Shared.Beeping.NPcoNP.Grammar284PreparedOrdinaryStep
