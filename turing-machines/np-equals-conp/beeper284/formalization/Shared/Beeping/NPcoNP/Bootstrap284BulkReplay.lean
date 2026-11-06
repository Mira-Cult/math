import Shared.Beeping.NPcoNP.Bootstrap284PackedMask

/-! Packed bootstrap replay with a single XOR for each guarded left scan.
Every accepted action still has a positive exact silent physical segment. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284BulkReplay
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.Bootstrap284BitSnapshot
open Shared.Beeping.NPcoNP.Bootstrap284PackedStep
open Shared.Beeping.NPcoNP.Bootstrap284Scans
open Shared.Beeping.NPcoNP.Bootstrap284Certificate
open Shared.Beeping.NPcoNP.Bootstrap284PackedScans
open Shared.Beeping.NPcoNP.Bootstrap284PackedMask

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

def executeBulk (base : Int) (span : Nat) (op : Op) (c : Packed) : Option (Packed × Nat) :=
  match op with
  | .left n =>
    if 0<n ∧ c.state=2 ∧ base≤c.head-2*(n : Int)+1 ∧ c.head<base+(span : Int) ∧
      leftOK n c.head (bitSnapshot base span c.bits) then
      some (⟨2,c.head-2*(n : Int),c.bits ^^^ intervalMask (c.head-2*(n : Int)+1-base).toNat (2*n)⟩,2*n)
    else none
  | other => executePacked base span other c

theorem executeBulk_sound (base : Int) (span : Nat) (op : Op) (c d : Packed) (n : Nat)
    (he : executeBulk base span op c=some (d,n)) :
    0<n ∧ silentSegment machine (toConfig base span c) (toConfig base span d) n := by
  cases op with
  | single => exact executePacked_sound base span .single c d n he
  | right k => exact executePacked_sound base span (.right k) c d n he
  | fill k => exact executePacked_sound base span (.fill k) c d n he
  | left k =>
    simp only [executeBulk] at he
    split at he
    · rename_i hg
      obtain ⟨hk,hq,hlo,hhi,ht⟩ := hg
      simp only [Option.some.injEq,Prod.mk.injEq] at he
      obtain ⟨rfl,rfl⟩ := he
      constructor
      · omega
      · have hpattern := leftOK_sound ht
        have hs := scan_left k c.head (bitSnapshot base span c.bits) hpattern
        rw [← bulkLeft_correct base c.head span c.bits k hlo hhi hpattern] at hs
        simpa [toConfig,hq] using hs
    · contradiction

def replayBulk (base : Int) (span : Nat) : List Op → Packed → Option (Packed × Nat)
  | [],c => some (c,0)
  | op::ops,c => do
    let (d,n) ← executeBulk base span op c
    let (e,m) ← replayBulk base span ops d
    pure (e,n+m)

theorem replayBulk_sound (base : Int) (span : Nat) (ops : List Op)
    (c d : Packed) (n : Nat) (hr : replayBulk base span ops c=some (d,n)) :
    ops.length≤n ∧ silentSegment machine (toConfig base span c) (toConfig base span d) n := by
  induction ops generalizing c d n with
  | nil =>
    simp only [replayBulk,Option.some.injEq,Prod.mk.injEq] at hr
    obtain ⟨rfl,rfl⟩ := hr
    exact ⟨by simp,by simp [silentSegment,W,WordEventSystem.advance,WordEventSystem.wordFrom]⟩
  | cons op ops ih =>
    cases hs : executeBulk base span op c with
    | none => simp [replayBulk,hs] at hr
    | some x =>
      rcases x with ⟨mid,k⟩
      cases ht : replayBulk base span ops mid with
      | none => simp [replayBulk,hs,ht] at hr
      | some y =>
        rcases y with ⟨e,l⟩
        have ⟨hk,hfirst⟩ := executeBulk_sound base span op c mid k hs
        have ⟨hl,hrest⟩ := ih mid e l ht
        simp [replayBulk,hs,ht] at hr
        obtain ⟨rfl,rfl⟩ := hr
        exact ⟨by simp only [List.length_cons]; omega,segAdd machine _ _ _ k l hfirst hrest⟩
end Shared.Beeping.NPcoNP.Bootstrap284BulkReplay
