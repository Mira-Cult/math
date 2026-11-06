import Shared.Beeping.NPcoNP.Bootstrap284PackedStep
import Shared.Beeping.NPcoNP.Bootstrap284Certificate

/-! Bit-packed implementations of the bootstrap's leftward scan updates.
All writes are required to remain in the declared snapshot span. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284PackedScans
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.Bootstrap284Scans
open Shared.Beeping.NPcoNP.Bootstrap284BitSnapshot
open Shared.Beeping.NPcoNP.Bootstrap284BitWrite
open Shared.Beeping.NPcoNP.Bootstrap284PackedStep
open Shared.Beeping.NPcoNP.Bootstrap284Certificate

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- Apply the left-scan's two bit writes for each pair. -/
def leftBits : Nat → Int → Int → Nat → Nat
  | 0,_,_,bits => bits
  | n+1,base,h,bits =>
      leftBits n base (h-2) (bitPut (bitPut bits (h-base).toNat false) (h-1-base).toNat true)

/-- Apply the filling scan's one bit write for each pair. -/
def fillBits : Nat → Int → Int → Nat → Nat
  | 0,_,_,bits => bits
  | n+1,base,h,bits => fillBits n base (h-2) (bitPut bits (h-1-base).toNat true)

/-- Packed pair rewrites represent exactly the unbounded tape effect. -/
theorem leftBits_correct (n : Nat) (base h : Int) (span bits : Nat)
    (hlo : base≤h-2*(n : Int)+1) (hhi : h<base+(span : Int)) :
    bitSnapshot base span (leftBits n base h bits) =
      leftEffect n (bitSnapshot base span bits) h := by
  induction n generalizing h bits with
  | zero => rfl
  | succ n ih =>
    have h0 : base≤h ∧ h<base+(span : Int) := by push_cast at hlo; omega
    have h1 : base≤h-1 ∧ h-1<base+(span : Int) := by push_cast at hlo; omega
    have hlo' : base≤(h-2)-2*(n : Int)+1 := by push_cast at hlo; omega
    have hhi' : h-2<base+(span : Int) := by omega
    simp only [leftBits,leftEffect]
    rw [ih (h-2) _ hlo' hhi',snapshot_bitPut base (h-1) span _ true h1,
      snapshot_bitPut base h span bits false h0]

/-- Packed filling rewrites represent exactly the unbounded tape effect. -/
theorem fillBits_correct (n : Nat) (base h : Int) (span bits : Nat)
    (hlo : base≤h-2*(n : Int)+1) (hhi : h<base+(span : Int)) :
    bitSnapshot base span (fillBits n base h bits) =
      fillEffect n (bitSnapshot base span bits) h := by
  induction n generalizing h bits with
  | zero => rfl
  | succ n ih =>
    have h1 : base≤h-1 ∧ h-1<base+(span : Int) := by push_cast at hlo; omega
    have hlo' : base≤(h-2)-2*(n : Int)+1 := by push_cast at hlo; omega
    have hhi' : h-2<base+(span : Int) := by omega
    simp only [fillBits,fillEffect]
    rw [ih (h-2) _ hlo' hhi',snapshot_bitPut base (h-1) span bits true h1]

/-- Execute one positive silent macrostep on packed data. A scan's visited
cells must lie within the declared span, and its finite bit pattern is checked. -/
def executePacked (base : Int) (span : Nat) (op : Op) (c : Packed) : Option (Packed × Nat) :=
  match op with
  | .single =>
    match stepPacked base span c with
    | some (d,false) => some (d,1)
    | _ => none
  | .right n =>
    if 0<n ∧ c.state=4 ∧ base≤c.head ∧ c.head+2*(n : Int)≤base+(span : Int) ∧
      rightOK n c.head (bitSnapshot base span c.bits) then
      some (⟨4,c.head+2*(n : Int),c.bits⟩,2*n) else none
  | .left n =>
    if 0<n ∧ c.state=2 ∧ base≤c.head-2*(n : Int)+1 ∧ c.head<base+(span : Int) ∧
      leftOK n c.head (bitSnapshot base span c.bits) then
      some (⟨2,c.head-2*(n : Int),leftBits n base c.head c.bits⟩,2*n) else none
  | .fill n =>
    if 0<n ∧ c.state=0 ∧ base≤c.head-2*(n : Int)+1 ∧ c.head<base+(span : Int) ∧
      leftOK n c.head (bitSnapshot base span c.bits) then
      some (⟨0,c.head-2*(n : Int),fillBits n base c.head c.bits⟩,2*n) else none

/-- Each accepted packed macrostep represents a strictly positive silent
segment of the actual literal machine with its complete tape. -/
theorem executePacked_sound (base : Int) (span : Nat) (op : Op) (c d : Packed) (n : Nat)
    (he : executePacked base span op c=some (d,n)) :
    0<n ∧ silentSegment machine (toConfig base span c) (toConfig base span d) n := by
  cases op with
  | single =>
    simp only [executePacked] at he
    cases hs : stepPacked base span c with
    | none => simp [hs] at he
    | some x =>
      rcases x with ⟨e,b⟩
      cases b with
      | true => simp [hs] at he
      | false =>
        simp [hs] at he
        obtain ⟨rfl,rfl⟩ := he
        exact ⟨by omega,oneSeg machine _ _ (stepPacked_sound base span c e false hs)⟩
  | right k =>
    simp only [executePacked] at he
    split at he
    · rename_i hg
      obtain ⟨hk,hq,_,_,ht⟩ := hg
      simp only [Option.some.injEq,Prod.mk.injEq] at he
      obtain ⟨rfl,rfl⟩ := he
      constructor
      · omega
      · have hs := scan_right k c.head (bitSnapshot base span c.bits) (rightOK_sound ht)
        simpa [toConfig,hq] using hs
    · contradiction
  | left k =>
    simp only [executePacked] at he
    split at he
    · rename_i hg
      obtain ⟨hk,hq,hlo,hhi,ht⟩ := hg
      simp only [Option.some.injEq,Prod.mk.injEq] at he
      obtain ⟨rfl,rfl⟩ := he
      constructor
      · omega
      · have hs := scan_left k c.head (bitSnapshot base span c.bits) (leftOK_sound ht)
        rw [← leftBits_correct k base c.head span c.bits hlo hhi] at hs
        simpa [toConfig,hq] using hs
    · contradiction
  | fill k =>
    simp only [executePacked] at he
    split at he
    · rename_i hg
      obtain ⟨hk,hq,hlo,hhi,ht⟩ := hg
      simp only [Option.some.injEq,Prod.mk.injEq] at he
      obtain ⟨rfl,rfl⟩ := he
      constructor
      · omega
      · have hs := scan_fill_left k c.head (bitSnapshot base span c.bits) (leftOK_sound ht)
        rw [← fillBits_correct k base c.head span c.bits hlo hhi] at hs
        simpa [toConfig,hq] using hs
    · contradiction

/-- Execute a finite list of packed macrosteps, accumulating literal time. -/
def replayPacked (base : Int) (span : Nat) : List Op → Packed → Option (Packed × Nat)
  | [],c => some (c,0)
  | op::ops,c => do
    let (d,n) ← executePacked base span op c
    let (e,m) ← replayPacked base span ops d
    pure (e,n+m)

/-- A successful packed replay is an exact silent literal run and cannot
use zero-duration actions. -/
theorem replayPacked_sound (base : Int) (span : Nat) (ops : List Op)
    (c d : Packed) (n : Nat) (hr : replayPacked base span ops c=some (d,n)) :
    ops.length≤n ∧ silentSegment machine (toConfig base span c) (toConfig base span d) n := by
  induction ops generalizing c d n with
  | nil =>
    simp only [replayPacked,Option.some.injEq,Prod.mk.injEq] at hr
    obtain ⟨rfl,rfl⟩ := hr
    exact ⟨by simp,by simp [silentSegment,W,WordEventSystem.advance,WordEventSystem.wordFrom]⟩
  | cons op ops ih =>
    cases hs : executePacked base span op c with
    | none => simp [replayPacked,hs] at hr
    | some x =>
      rcases x with ⟨mid,k⟩
      cases ht : replayPacked base span ops mid with
      | none => simp [replayPacked,hs,ht] at hr
      | some y =>
        rcases y with ⟨e,l⟩
        have ⟨hk,hfirst⟩ := executePacked_sound base span op c mid k hs
        have ⟨hl,hrest⟩ := ih mid e l ht
        simp [replayPacked,hs,ht] at hr
        obtain ⟨rfl,rfl⟩ := hr
        exact ⟨by simp only [List.length_cons]; omega,segAdd machine _ _ _ k l hfirst hrest⟩

end Shared.Beeping.NPcoNP.Bootstrap284PackedScans
