import Shared.Beeping.NPcoNP.Native50Prepare
import Shared.Beeping.NPcoNP.NativeFourthNextPath

/-! Literal state-54 zero preparation for a finite, nonempty zero run followed
by a one. This local theorem records exact tape changes and finite silent
time; it does not assume that the layout is reachable. -/
namespace Shared.Beeping.NPcoNP.Native54Prepare
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerReturns
open Shared.Beeping.NPcoNP.NativeFirstZeroOperation
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

theorem step54_zero (x : Int) (t : Int → Bool) (ht : t x=false) :
    machine.step (cfg 54 x t)=(cfg 9 (x+1) (setAt x t),false) := by
  have row : machine.table.row 54 false=⟨true,.right,9,false⟩ := by decide
  have hw : (⟨54,x,t⟩ : Config 284).write true=setAt x t := rfl
  simp [cfg,Machine.step,ht,row,Move.apply,hw]

/-- Equal first transitions have identical positive-length silent segments. -/
theorem replace_equal_first {n : Nat} (M : Machine n) (c d e : Config n) (k : Nat)
    (h : M.step c=M.step d) :
    silentSegment M c e (k+1) ↔ silentSegment M d e (k+1) := by
  have hs : (W M).step c=(W M).step d := by
    exact congrArg (fun v : Config n × Bool => (v.1, if v.2 then [()] else [])) h
  have ha : (W M).advance c 1=(W M).advance d 1 := by
    simpa [WordEventSystem.advance] using congrArg Prod.fst hs
  have hw : (W M).wordFrom c 1=(W M).wordFrom d 1 := by
    simpa [WordEventSystem.wordFrom,WordEventSystem.advance] using congrArg Prod.snd hs
  have hn : k+1=1+k := by omega
  simp only [silentSegment,hn,WordEventSystem.advance_add,WordEventSystem.wordFrom_add,ha,hw]

/-- State 54 has the same zero row as state 50, so it inherits the checked
finite preparation, including the exact tape effect and duration. -/
theorem zero_prepare_to83 (x : Int) (t : Int → Bool) (k : Nat)
    (hk : 0<k)
    (h0 : t x=false) (h1 : t (x+1)=false) (h2 : t (x+2)=false)
    (zeros : ∀ i : Nat, i<k → t (x+3+(i : Int))=false)
    (marker : t (x+3+(k : Int))=true) :
    let out := fillRange (setAt x t) (x+3) (x+3+(k : Int))
    out x=true ∧
    (∀ q, q≠x → (q<x+3 ∨ x+3+(k : Int)≤q) → out q=t q) ∧
    silentSegment machine (cfg 54 x t) (cfg 83 (x+3+(k : Int)-2) out) (k+5) := by
  dsimp only
  obtain ⟨hm,hframe,hseg⟩ := Native50Prepare.zero_prepare_to83 x t k hk h0 h1 h2 zeros marker
  have he : machine.step (cfg 50 x t)=machine.step (cfg 54 x t) := by
    rw [Native50Prepare.step50_zero x t h0,step54_zero x t h0]
  have hr := (replace_equal_first machine (cfg 50 x t) (cfg 54 x t)
    (cfg 83 (x+3+(k : Int)-2) (fillRange (setAt x t) (x+3) (x+3+(k : Int))))
    (k+4) he).mp (by simpa [Nat.add_assoc] using hseg)
  exact ⟨hm,hframe,by simpa [Nat.add_assoc] using hr⟩

#print axioms replace_equal_first
#print axioms zero_prepare_to83
end Shared.Beeping.NPcoNP.Native54Prepare
