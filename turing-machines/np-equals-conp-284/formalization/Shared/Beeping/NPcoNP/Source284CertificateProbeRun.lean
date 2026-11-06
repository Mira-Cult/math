import Shared.Beeping.NPcoNP.Source284CertificateProbe

/-! Exact finite run of the marker-controlled certificate probe. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284CertificateProbeRun

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284CertificateProbe

def body (z1 z2 frame : Nat) : Nat :=
  2^z1*(2*(2^z2*(2*(4*frame)+1))+1)

def mode (frame : Nat) : Nat := if frame.testBit 0 then 1 else 0

def cost (z1 z2 : Nat) : Nat := 2*(z1+z2)+12

/-- The probe reads a bit from beyond both sentinels and the gap, and then
restores the complete raw frame and scratch tape. -/
theorem probe (continuation : Nat → Bool → Row) (z1 z2 frame stream : Nat) :
    run (table continuation) ⟨body z1 z2 frame,2*stream,some 0⟩ (cost z1 z2) =
      ⟨body z1 z2 frame,2*stream,some (18+mode frame)⟩ := by
  have hm : mode frame<2 := by unfold mode; split <;> omega
  have h1 : table continuation 1 false = ⟨false,false,some 1⟩ := rfl
  have h2 : table continuation 2 false = ⟨false,false,some 2⟩ := rfl
  have h12 : table continuation (12+mode frame) false = ⟨false,false,some (12+mode frame)⟩ := by
    rcases show mode frame=0 ∨ mode frame=1 by omega with h | h <;> rw [h] <;> rfl
  have h14 : table continuation (14+mode frame) false = ⟨false,false,some (14+mode frame)⟩ := by
    rcases show mode frame=0 ∨ mode frame=1 by omega with h | h <;> rw [h] <;> rfl
  have ht : cost z1 z2 = 1+(z1+(1+(z2+(1+(5+(1+(z2+(1+(z1+2))))))))) := by
    simp [cost]; omega
  rw [ht,Source284ScratchScanner.run_add]
  change run (table continuation) (step (table continuation)
    ⟨body z1 z2 frame,2*stream,some 0⟩) _ = _
  rw [start]
  unfold body
  rw [Source284ScratchScanner.run_add,zeros _ 1 z1 _ _ h1,
    Source284ScratchScanner.run_add]
  change run (table continuation) (step (table continuation)
    ⟨2^z1*(2*stream+1),2*(2^z2*(2*(4*frame)+1))+1,some 1⟩) _ = _
  rw [first_marker,Source284ScratchScanner.run_add,zeros _ 2 z2 _ _ h2,Source284ScratchScanner.run_add]
  change run (table continuation) (step (table continuation)
    ⟨2^z2*(2*(2^z1*(2*stream+1))+1),2*(4*frame)+1,some 2⟩) _ = _
  rw [second_marker,Source284ScratchScanner.run_add,read_and_return_two,Source284ScratchScanner.run_add]
  change run (table continuation) (step (table continuation)
    ⟨4*frame,2*(2^z2*(2*(2^z1*(2*stream+1))+1))+1,some (10+mode frame)⟩) _ = _
  rw [return_first _ _ _ _ hm,Source284ScratchScanner.run_add,zeros _ _ z2 _ _ h12,Source284ScratchScanner.run_add]
  change run (table continuation) (step (table continuation)
    ⟨2^z2*(2*(4*frame)+1),2*(2^z1*(2*stream+1))+1,some (12+mode frame)⟩) _ = _
  rw [return_second _ _ _ _ hm,Source284ScratchScanner.run_add,zeros _ _ z1 _ _ h14,finish _ _ _ _ hm]

/-- Continue immediately after the finite probe with the read bit in the
continuation state. -/
theorem probe_then (continuation : Nat → Bool → Row) (z1 z2 frame stream fuel : Nat) :
    run (table continuation) ⟨body z1 z2 frame,2*stream,some 0⟩ (cost z1 z2+fuel) =
    shiftConfig 18 (run continuation ⟨body z1 z2 frame,2*stream,some (mode frame)⟩ fuel) := by
  rw [Source284ScratchScanner.run_add,probe]
  change run (table continuation)
    (shiftConfig 18 ⟨body z1 z2 frame,2*stream,some (mode frame)⟩) fuel = _
  exact relocated_run continuation _ fuel

end Shared.Beeping.NPcoNP.Source284CertificateProbeRun
