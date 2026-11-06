import Shared.Beeping.NPcoNP.NativeHalfPrepareReturn
import Shared.Beeping.NPcoNP.Grammar284GraphOperation
import Shared.Beeping.NPcoNP.NativeGrammarSelectorDispatch

/-! A sufficiently spaced graph parser window prepares any native-HALF zero
entry and returns to the same parser, preserving its bank-side tape. -/
namespace Shared.Beeping.NPcoNP.Grammar284HalfPreparation
open PASoundness Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeGrammarPreterminalDispatch
open Shared.Beeping.NPcoNP.NativeGrammarSelectorDispatch
open Shared.Beeping.NPcoNP.NativeAllBankScan
open Shared.Beeping.NPcoNP.NativeHalfPrepareReturn
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.Grammar284ExpansionPaths
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

/-- From a parser word followed by at least three zeros and a marked right
boundary, perform zero-entry preparation and return to the parser with a marker,
one zero and a solid run. The whole suffix from the right boundary is retained. -/
theorem prepare_from_parser (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (q : Fin 284)
    (hq : q=74 ∨ q=75 ∨ q=76 ∨ q=77) (operation : operationEntry name=some q) (origin x separator : Int) (t : Int → Bool)
    (hentry : x=origin+((path.length : Nat) : Int)) (space : x+3≤separator)
    (word : Holds t origin path) (left : ∀ q, q<origin → t q=false)
    (gap : ∀ q, x≤q → q<separator-1 → t q=false)
    (right : t (separator-1)=true) (sep : t separator=false) :
    ∃ (steps : Nat) (out : Int → Bool), 0<steps ∧ Holds out origin path ∧
      (∀ q, q<origin → out q=false) ∧ out x=true ∧ out (x+1)=false ∧
      (∀ q, x+2≤q → q<separator → out q=true) ∧ out separator=false ∧
      (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) steps := by
  have member := graph_leaf_member state path name leaf
  have walk : PreparedWalk path (.op name) :=
    expanded_leaf_follows traceState557.acc producerExpand (path,name) member
  have count : path.count false≤11 := (prepared_path_bound path (.op name) walk).2
  have len : 0<path.length := by
    obtain ⟨raw,he,_⟩ := walk
    rw [he]
    simp [preparedPrefix]
  obtain ⟨first,tail⟩ := prepared_head_tail t origin path name walk word
  have dispatch := expanded_leaf_dispatch_to_entry traceState557.acc producerExpand (path,name) member
    q operation (origin+1) t tail
  have hlenPath : (path.tail.length : Int)+1=(path.length : Int) := by
    obtain ⟨raw,he,_⟩ := walk
    rw [he]
    simp [preparedPrefix]
  have hdispatch : silentSegment machine (cfg 93 (origin+1) t)
      (cfg q x t) path.tail.length := by
    have he : origin+1+(path.tail.length : Int)=x := by omega
    simpa only [he] using dispatch
  let k := (separator-x-3).toNat
  have hk : (k : Int)=separator-x-3 := Int.toNat_of_nonneg (by omega)
  have hm : x+2+(k : Int)=separator-1 := by omega
  have h0 : t x=false := gap x (by omega) (by omega)
  have h1 : t (x+1)=false := gap (x+1) (by omega) (by omega)
  have hz : ∀ i : Nat, i<k → t (x+2+(i : Int))=false := by
    intro i hi
    exact gap _ (by omega) (by omega)
  have hmarker : t (x+2+(k : Int))=true := by simpa only [hm] using right
  obtain ⟨a,ha,hword,hx,hx1,hcontrol,hframe,hprepare⟩ :=
    half_prepare_returns_all q hq origin x t path k hentry len count word left first h0 h1 hz hmarker
  let out := fillRange (setAt x t) (x+2) (x+2+(k : Int))
  change ∀ q, q<x ∨ x+2+(k : Int)≤q → out q=t q at hframe
  have houtleft : ∀ q, q<origin → out q=false := by
    intro q hq
    rw [hframe q (Or.inl (by omega))]
    exact left q hq
  have houtsep : out separator=false := by
    rw [hframe separator (Or.inr (by omega))]
    exact sep
  have houtbank : ∀ q, separator≤q → out q=t q := by
    intro q hq
    exact hframe q (Or.inr (by omega))
  refine ⟨path.tail.length+a,out,by omega,hword,houtleft,hx,hx1,?_,houtsep,houtbank,?_⟩
  · intro q hq hq'
    exact hcontrol q hq (by omega)
  · exact segAdd machine _ _ _ _ _ hdispatch hprepare

#print axioms prepare_from_parser
end Shared.Beeping.NPcoNP.Grammar284HalfPreparation
