import Shared.PNP.Record285.PythonControlLocal

/-! Relate full typed interpreter configurations to the verified abstract
controller. Store entries not mentioned by the controller remain arbitrary. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonControlSimulationLocal
open Shared.Beeping
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.PythonStraight
open Shared.PNP.Record285.PythonControl
open Shared.PNP.Record285.PythonControlSkip (pySystem Silent silent_trans)
open Shared.PNP.Record285.PythonControlComparison
open Shared.PNP.Record285.PythonControlDispatch
open Shared.PNP.Record285.PythonControlBegin
open Shared.PNP.Record285.PythonControlLocal
open Shared.PNP.Record285.PythonControlReferenceComplete (initial)

def Rel (q : SearchState) (x : Status) : Prop :=
  (q=controller.initial ∧ x=mainSystem.initial) ∨
  ∃ s : Store, s "program"=q.program ∧ s "exponent"=q.exponent ∧
    match q.phase with
    | .begin => x=beforeBeep s
    | .compare => x=initial s ∧ s "n"=q.n ∧ s "radix"=q.radix ∧
        s "remaining"=q.remaining ∧ 0<q.radix

def StepWitness (q : SearchState) (x : Status) : Prop :=
  ∃ n y, 0<n ∧ Local x y n (controllerStep q).2 ∧ Rel (controllerStep q).1 y

theorem startup_sim : StepWitness controller.initial mainSystem.initial := by
  refine ⟨5,initial (reset startStore),by decide,?_ ,?_⟩
  · exact marked_local startup_segment (by decide)
  · right
    refine ⟨reset startStore,?_,?_,?_⟩ <;>
      simp [controller,controllerStep,reset,startStore,put]

theorem begin_sim (q : SearchState) (s : Store) (hp : q.phase=.begin)
    (hprog : s "program"=q.program) (hexp : s "exponent"=q.exponent) :
    StepWitness q (beforeBeep s) := by
  refine ⟨3,initial (reset s),by decide,?_ ,?_⟩
  · simpa [controllerStep,hp] using marked_local (begin_segment s) (by decide)
  · right
    refine ⟨reset s,?_,?_,?_⟩ <;>
      simp [controllerStep,hp,reset,put,hprog,hexp]

end Shared.PNP.Record285.PythonControlSimulationLocal
