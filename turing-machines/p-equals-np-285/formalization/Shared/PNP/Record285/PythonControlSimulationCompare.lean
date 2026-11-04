import Shared.PNP.Record285.PythonControlSimulationLocal

/-! Local silent simulation of one complete source comparison and dispatch. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonControlSimulationCompare
open Shared.Beeping
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.PythonStraight
open Shared.PNP.Record285.PythonControl
open Shared.PNP.Record285.PythonControlSkip (Silent silent_trans)
open Shared.PNP.Record285.PythonControlComparison
open Shared.PNP.Record285.PythonControlDispatch
open Shared.PNP.Record285.PythonControlBegin
open Shared.PNP.Record285.PythonControlLocal
open Shared.PNP.Record285.PythonControlSimulationLocal
open Shared.PNP.Record285.PythonControlReferenceComplete (initial)

theorem compare_sim (q : SearchState) (s : Store) (hphase : q.phase=.compare)
    (hprog : s "program"=q.program) (hexp : s "exponent"=q.exponent)
    (hname : s "n"=q.n) (hradix : s "radix"=q.radix)
    (hremaining : s "remaining"=q.remaining) (hpos : 0<q.radix) :
    StepWitness q (initial s) := by
  have hsr : 0<s "radix" := by omega
  obtain ⟨m,out,hm,hcompare,houtprog,houtexp,houtname,houtref,houtrem,hvalue⟩ :=
    comparison_complete s hsr
  change Silent (initial s) (dispatch out) m at hcompare
  rw [hprog,hexp,hname,hradix,hremaining] at hvalue
  by_cases hbad : mismatch q.program q.exponent q.n q.radix q.remaining = true
  · have he : out "expected" ≠ 0 := by
      have hv : out "expected" = 1 := by simpa [hbad] using hvalue
      omega
    have hfail := failed out he
    have hadvance := candidate_advance out
    have hquiet := silent_trans (silent_trans hcompare hfail) hadvance
    let v := nextCandidateStore out
    refine ⟨m+2+(if out "program"=0 then 4 else 5),beforeBeep v,by omega,?_,?_⟩
    · simpa [controllerStep,hphase,hbad,v] using silent_local hquiet
    · right
      refine ⟨v,?_,?_,?_⟩ <;>
        simp [controllerStep,hphase,hbad,v,nextCandidateStore,put,houtprog,houtexp,hprog,hexp]
  · have hgood : mismatch q.program q.exponent q.n q.radix q.remaining = false := Bool.eq_false_iff.mpr hbad
    have he : out "expected"=0 := by simpa [hgood] using hvalue
    by_cases hz : q.remaining=0
    · have hzero : out "remaining"=0 := by omega
      have hgood0 : mismatch q.program q.exponent q.n q.radix 0 = false := by
        simpa [hz] using hgood
      have hrad : 0<out "radix" := by omega
      have hsuccess := successful_block out he hzero hrad
      have hnext := input_next (nextBlockStore out)
      have hquiet := silent_trans (silent_trans hcompare hsuccess) hnext
      let v := nextBlockStore out
      refine ⟨m+6+1,initial v,by omega,?_,?_⟩
      · simpa [controllerStep,hphase,hgood,hgood0,hz,v] using silent_local hquiet
      · right
        refine ⟨v,?_,?_,?_⟩ <;>
          simp [controllerStep,hphase,hgood,hgood0,hz,v,nextBlockStore,put,
            houtprog,houtexp,houtname,houtref,houtrem,hprog,hexp,hname,hradix,hremaining] <;> omega
    · have hrem : 0<out "remaining" := by omega
      have hsuccess := successful_remaining out he hrem
      have hnext := input_next (remainingStore out)
      have hquiet := silent_trans (silent_trans hcompare hsuccess) hnext
      let v := remainingStore out
      refine ⟨m+4+1,initial v,by omega,?_,?_⟩
      · simpa [controllerStep,hphase,hgood,hz,v] using silent_local hquiet
      · right
        refine ⟨v,?_,?_,?_⟩ <;>
          simp [controllerStep,hphase,hgood,hz,v,remainingStore,put,
            houtprog,houtexp,houtname,houtref,houtrem,hprog,hexp,hname,hradix,hremaining,hpos]

end Shared.PNP.Record285.PythonControlSimulationCompare
