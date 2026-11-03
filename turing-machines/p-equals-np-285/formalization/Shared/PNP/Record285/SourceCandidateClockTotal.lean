import Shared.PNP.Record285.SourceCandidateClock

/-! Termination of the actual candidate clock builder on arbitrary finite
stores. Its output need not equal the clean-scratch polynomial clock. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.SourceCandidateClockTotal
open Shared.Beeping
open Shared.PNP.Record285.OwnershipCore
open Shared.PNP.Record285.RegisterProjection
open Shared.PNP.Record285.SourceBegin
open Shared.PNP.Record285.SourceReferenceStart
open Shared.PNP.Record285.SourceUnarySkip
open Shared.PNP.Record285.SourceCandidateClock

/-- One positive multiplication-loop iteration always decreases register 20;
scratch register 4 may initially be arbitrary. -/
theorem multiply_cycle_total (bank : Nat → Nat) (hp : 0 < bank 20) :
    ∃ out duration, 0 < duration ∧ Silent originalRows ⟨81,bank⟩ ⟨81,out⟩ duration ∧
      out 20 = bank 20-1 ∧ out 12 = bank 12 := by
  let first := update (.dec 20) bank
  let mid := clockCopy first
  let one := update (.inc 7) mid
  let two := update (.inc 7) one
  have hn : bank 20 ≠ 0 := by omega
  have hs : step originalRows ⟨81,bank⟩ = (⟨82,first⟩,false) := by
    simp [step,originalRows,observe,hn,first]
  have hcopy := clock_copy_run first
  have h87 : step originalRows ⟨87,mid⟩ = (⟨88,one⟩,false) := by
    simp [step,originalRows,observe,one]
  have h88 : step originalRows ⟨88,one⟩ = (⟨81,two⟩,false) := by
    simp [step,originalRows,observe,two]
  have h := silent_trans originalRows _ _ _ 1 _ (silent_one _ _ _ hs) hcopy
  have h := silent_trans originalRows _ _ _ _ 1 h (silent_one _ _ _ h87)
  have h := silent_trans originalRows _ _ _ _ 1 h (silent_one _ _ _ h88)
  refine ⟨two,1+(3*first 13+1+(2*(first 4+first 13)+1))+1+1,by omega,h,?_,?_⟩
  · simp [two,one,mid,clockCopy,splitResult,first,update]
  · simp [two,one,mid,clockCopy,splitResult,first,update]

/-- The complete multiplication loop terminates on any natural-valued bank
and preserves the outer exponent counter. -/
theorem multiply_loop_total (n : Nat) (bank : Nat → Nat) (hn : bank 20 = n) :
    ∃ out duration, 0 < duration ∧ Silent originalRows ⟨81,bank⟩ ⟨89,out⟩ duration ∧
      out 12 = bank 12 := by
  induction n generalizing bank with
  | zero =>
    have hz : bank 20 = 0 := hn
    have hid := dec_at_zero 20 bank hz
    have hs : step originalRows ⟨81,bank⟩ = (⟨89,bank⟩,false) := by
      simp [step,originalRows,observe,hz,hid]
    exact ⟨bank,1,by decide,silent_one originalRows _ _ hs,rfl⟩
  | succ n ih =>
    have hp : 0 < bank 20 := by omega
    obtain ⟨mid,d,hd,hcycle,h20,h12⟩ := multiply_cycle_total bank hp
    have hn' : mid 20 = n := by omega
    obtain ⟨out,e,he,hrest,hout⟩ := ih mid hn'
    refine ⟨out,d+e,by omega,silent_trans originalRows _ _ _ _ _ hcycle hrest,?_⟩
    exact hout.trans h12

/-- One outer power iteration always decreases register 12, regardless of
the initial scratch registers or the intermediate multiplication output. -/
theorem power_cycle_total (bank : Nat → Nat) (hp : 0 < bank 12) :
    ∃ out duration, 0 < duration ∧ Silent originalRows ⟨79,bank⟩ ⟨79,out⟩ duration ∧
      out 12 = bank 12-1 := by
  let first := update (.inc 6) (update (.dec 12) bank)
  have hn : bank 12 ≠ 0 := by omega
  have hs : step originalRows ⟨79,bank⟩ = (⟨80,update (.dec 12) bank⟩,false) := by
    simp [step,originalRows,observe,hn]
  have ht : step originalRows ⟨80,update (.dec 12) bank⟩ = (⟨81,first⟩,false) := by
    simp [step,originalRows,observe,first]
  have hfirst := silent_trans originalRows _ _ _ 1 1 (silent_one _ _ _ hs) (silent_one _ _ _ ht)
  obtain ⟨mid,d,hd,hmul,h12⟩ := multiply_loop_total (first 20) first rfl
  have h89 : originalRows[89]? = some ⟨.dec 7,90,79⟩ := by decide
  have h90 : originalRows[90]? = some ⟨.inc 20,89,89⟩ := by decide
  have hmove := expanded_move_run originalRows 89 90 79 7 20 (mid 7) mid h89 h90 (by decide) rfl
  let last := update (.move 7 20) mid
  have h := silent_trans originalRows _ _ _ _ _ hfirst hmul
  have h := silent_trans originalRows _ _ _ _ _ h hmove
  refine ⟨last,2+d+(2*mid 7+1),by omega,h,?_⟩
  simp [last,update,h12,first]

theorem power_loop_total (n : Nat) (bank : Nat → Nat) (hn : bank 12 = n) :
    ∃ out duration, 0 < duration ∧ Silent originalRows ⟨79,bank⟩ ⟨91,out⟩ duration := by
  induction n generalizing bank with
  | zero =>
    have hz : bank 12 = 0 := hn
    have hid := dec_at_zero 12 bank hz
    have hs : step originalRows ⟨79,bank⟩ = (⟨91,bank⟩,false) := by
      simp [step,originalRows,observe,hz,hid]
    exact ⟨bank,1,by decide,silent_one originalRows _ _ hs⟩
  | succ n ih =>
    have hp : 0 < bank 12 := by omega
    obtain ⟨mid,d,hd,hcycle,h12⟩ := power_cycle_total bank hp
    have hn' : mid 12 = n := by omega
    obtain ⟨out,e,he,hrest⟩ := ih mid hn'
    exact ⟨out,d+e,by omega,silent_trans originalRows _ _ _ _ _ hcycle hrest⟩

/-- The real clock builder finishes silently on every finite bank, without
assuming any scratch register is initially zero. -/
theorem clock_build_terminates (bank : Nat → Nat) :
    ∃ out duration, 0 < duration ∧ Silent originalRows ⟨77,bank⟩ ⟨93,out⟩ duration := by
  let cleared := clear 20 bank
  let init := clockInitial bank
  have h77 : originalRows[77]? = some ⟨.dec 20,77,78⟩ := by decide
  have hc := clear_run originalRows 77 78 20 (bank 20) bank h77 rfl
  have heffect : update (.inc 20) cleared = init := by
    funext j
    by_cases hj : j=20 <;> simp [init,clockInitial,cleared,clear,put,update,hj]
  have h78 : step originalRows ⟨78,cleared⟩ = (⟨79,init⟩,false) := by
    simp [step,originalRows,observe,heffect]
  obtain ⟨mid,d,hd,hpow⟩ := power_loop_total (init 12) init rfl
  have h91 : originalRows[91]? = some ⟨.dec 6,92,93⟩ := by decide
  have h92 : originalRows[92]? = some ⟨.inc 12,91,91⟩ := by decide
  have hm := expanded_move_run originalRows 91 92 93 6 12 (mid 6) mid h91 h92 (by decide) rfl
  have h := silent_trans originalRows _ _ _ _ 1 hc (silent_one _ _ _ h78)
  have h := silent_trans originalRows _ _ _ _ _ h hpow
  have h := silent_trans originalRows _ _ _ _ _ h hm
  exact ⟨update (.move 6 12) mid,(bank 20+1)+1+d+(2*mid 6+1),by omega,h⟩

/-- Clock construction, frame setup and the bounded candidate evaluator all
terminate on the actual graph for an arbitrary initial bank. The clean-scratch
theorem separately supplies the intended numerical result. -/
theorem candidate_pipeline_terminates (bank : Nat → Nat) :
    ∃ out duration, 0 < duration ∧ Silent originalRows ⟨77,bank⟩ ⟨154,out⟩ duration := by
  obtain ⟨clockBank,d,hd,hclock⟩ := clock_build_terminates bank
  obtain ⟨e,he,hframe⟩ := Shared.PNP.Record285.SourceCandidateFrame.frame_raw_terminates clockBank
  let frameBank := Shared.PNP.Record285.SourceCandidateFrame.frameOutput clockBank
  obtain ⟨out,f,hf,heval⟩ := Shared.PNP.Record285.SourceCandidateStep.candidate_raw_terminates
    (frameBank 20) frameBank rfl
  have h := silent_trans originalRows _ _ _ _ _ hclock hframe
  exact ⟨out,d+e+f,by omega,silent_trans originalRows _ _ _ _ _ h heval⟩

/-- The complete reference-and-candidate computation reaches its comparison
dispatch on every initial bank, with no clean-scratch assumption. -/
theorem comparison_compute_terminates (bank : Nat → Nat) :
    ∃ out duration, 0 < duration ∧ Silent originalRows ⟨6,bank⟩ ⟨154,out⟩ duration := by
  obtain ⟨mid,d,hd,href,_⟩ := Shared.PNP.Record285.SourceVirtualStep.raw_reference_phase_terminates bank
  obtain ⟨out,e,he,hcandidate⟩ := candidate_pipeline_terminates mid
  exact ⟨out,d+e,by omega,silent_trans originalRows _ _ _ _ _ href hcandidate⟩

end Shared.PNP.Record285.SourceCandidateClockTotal
