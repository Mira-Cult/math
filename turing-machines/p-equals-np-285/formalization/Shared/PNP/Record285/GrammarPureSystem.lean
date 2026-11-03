import Shared.PNP.Record285.GrammarPureDecode

/-! A physical-tape-independent executable interpreter for the frozen grammar.
Its equivalence with the selected Python source remains an open obligation. -/
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.GrammarPure
open Shared.Beeping
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.GrammarReady
open Shared.PNP.Record285.GrammarExact
open Shared.PNP.Record285.GrammarOperationalRun
open Shared.PNP.Record285.CleanBank

structure State where
  control : List Bool
  fields : List Nat
  deriving DecidableEq, Repr

def initial : State := ⟨[false],List.replicate 1909 0⟩

/-- The fallback makes the definition total on malformed control words. Every
reachable state below has a successful grammar descent and successor. -/
def step (s : State) : State × Bool :=
  let (e,len) := (descend 163 rootIndex (pureBits s.control) 0).getD (.beep,0)
  let code := window (pureBits s.control) 0 len
  (⟨(controlStep e s.fields code).getD [],applyUpdate e s.fields⟩,decide (e = .beep))

def system : EventSystem State := ⟨initial,step⟩

/-- The whole physical tape matches this control and bank representation;
the zero margin is real, before the bank anchor. -/
def Related (p : State) (s : GrammarOperationalRun.State) : Prop :=
  p.fields = s.fields ∧
  ∃ word marker origin leftTail gap,
    p.control = word++[marker] ∧ 163 ≤ gap ∧
    Rel (denote (rightWord treeRoot (-(word.length:Int)) word marker rootLeft [false])
      origin leftTail (runPattern false gap true (2*IncrementSelector.blocksBits p.fields 0))) s.physical

theorem initial_related : Related initial GrammarOperationalRun.initial := by
  refine ⟨rfl,[],false,-3818,0,3819,rfl,by decide,?_⟩
  change Rel (denote (rightWord treeRoot 0 [] false rootLeft [false]) (-3818) 0
    (runPattern false 3819 true (2*IncrementSelector.blocksBits (List.replicate 1909 0) 0))) _
  rw [← candidate_clean_numeric]
  exact InitializationComplete.blank_start_entry.1

theorem anchored_physical_head (s : GrammarOperationalRun.State) : s.physical.head = -3818 := by
  obtain ⟨word,marker,origin,leftTail,gap,_,hhead,_,hrel⟩ := s.anchored
  have hp := hrel.2.1
  have hpos : (denote (rightWord treeRoot (-(word.length:Int)) word marker rootLeft [false])
      origin leftTail (runPattern false gap true (2*IncrementSelector.blocksBits s.fields 0))).head =
      origin-word.length := by
    cases word <;> simp [denote,rightWord] <;> omega
  rw [hpos] at hp
  omega

/-- One pure grammar action makes precisely the bank, control, and event
transition of the literal machine's certified exact action boundary. -/
theorem step_related (p : State) (s : GrammarOperationalRun.State) (h : Related p s) :
    (step p).2 = (operationSystem.step s).2 ∧ Related (step p).1 (GrammarOperationalRun.next s) := by
  obtain ⟨hfields,word,marker,origin,leftTail,gap,hcontrol,hgap,hrel⟩ := h
  let w := chooseStep s
  have hhead := anchored_physical_head s
  have hwindow := represented_window word marker origin leftTail gap
    (IncrementSelector.blocksBits p.fields 0) s.physical hgap hrel
  rw [← hcontrol,hhead] at hwindow
  have hdesc := descend_window_congr _ _ hwindow
  have hphysical := zero_leaf_decodes s.fields (-3818) 3 w.edge w.code w.head w.leftTail w.gap s.physical w.leaf
  rw [hphysical] at hdesc
  have hpure : descend 163 rootIndex (pureBits p.control) 0 = some (w.edge,w.code.length) := by
    simpa only [← hcontrol] using hdesc.symm
  have hlen : w.code.length ≤ 163 :=
    GrammarPrefix.valid_length_bound w.code ⟨w.edge,GrammarPrefix.walk_follow w.code rootIndex w.edge w.leaf.1⟩
  have htake := congrArg (List.take w.code.length) hwindow
  rw [window_take _ _ _ _ hlen,window_take _ _ _ _ hlen] at htake
  have hcode := zero_leaf_window s.fields (-3818) 3 w.edge w.code w.head w.leftTail w.gap s.physical w.leaf
  rw [hcode] at htake
  have hcodePure : window (pureBits p.control) 0 w.code.length = w.code := by
    simpa only [← hcontrol] using htake.symm
  have hstep := exact_control_effect w.edge s.fields w.code w.gap w.duration (-3818) 3 w.head w.leftTail
    s.physical w.leaf (by decide) w.exactDuration
  obtain ⟨control,hnext,hout⟩ := hstep
  have hupdate := update_sound w.edge s.fields w.fields w.update
  have hnext' : controlStep w.edge p.fields w.code = some control := by simpa only [hfields] using hnext
  have hupdate' : applyUpdate w.edge p.fields = w.fields := by simpa only [hfields] using hupdate
  have hcalc : step p = (⟨control,w.fields⟩,decide (w.edge = .beep)) := by
    simp only [step,hpure,Option.getD_some,hcodePure,hnext',hupdate']
  rw [hcalc]
  constructor
  · rfl
  · obtain ⟨word',origin',leftTail',gap',hcontrol',hgap',hout'⟩ := hout
    refine ⟨rfl,word',true,origin',leftTail',gap',hcontrol',by omega,?_⟩
    rw [hupdate] at hout'
    exact hout'

/-- Neither fallback in the total pure step is used when the full physical
representation relation holds. -/
theorem related_step_defined (p : State) (s : GrammarOperationalRun.State) (h : Related p s) :
    ∃ e len control, 0 < len ∧
      descend 163 rootIndex (pureBits p.control) 0 = some (e,len) ∧
      controlStep e p.fields (window (pureBits p.control) 0 len) = some control := by
  obtain ⟨hfields,word,marker,origin,leftTail,gap,hcontrol,hgap,hrel⟩ := h
  let w := chooseStep s
  have hhead := anchored_physical_head s
  have hwindow := represented_window word marker origin leftTail gap
    (IncrementSelector.blocksBits p.fields 0) s.physical hgap hrel
  rw [← hcontrol,hhead] at hwindow
  have hdesc := descend_window_congr _ _ hwindow
  have hphysical := zero_leaf_decodes s.fields (-3818) 3 w.edge w.code w.head w.leftTail w.gap s.physical w.leaf
  rw [hphysical] at hdesc
  have hpure : descend 163 rootIndex (pureBits p.control) 0 = some (w.edge,w.code.length) := hdesc.symm
  have hlen : w.code.length ≤ 163 :=
    GrammarPrefix.valid_length_bound w.code ⟨w.edge,GrammarPrefix.walk_follow w.code rootIndex w.edge w.leaf.1⟩
  have htake := congrArg (List.take w.code.length) hwindow
  rw [window_take _ _ _ _ hlen,window_take _ _ _ _ hlen] at htake
  have hcode := zero_leaf_window s.fields (-3818) 3 w.edge w.code w.head w.leftTail w.gap s.physical w.leaf
  rw [hcode] at htake
  have hcodePure : window (pureBits p.control) 0 w.code.length = w.code := htake.symm
  have hstep := exact_control_effect w.edge s.fields w.code w.gap w.duration (-3818) 3 w.head w.leftTail
    s.physical w.leaf (by decide) w.exactDuration
  obtain ⟨control,hnext,_⟩ := hstep
  have hpositive : 0 < w.code.length := by
    cases hc : w.code with
    | nil =>
      have hw := w.leaf.1
      rw [hc] at hw
      simp [walk] at hw
    | cons b bs => simp
  refine ⟨w.edge,w.code.length,control,hpositive,hpure,?_⟩
  simpa only [hcodePure,hfields] using hnext

theorem related_run (n : Nat) : Related (system.run n) (operationSystem.run n) := by
  induction n with
  | zero => exact initial_related
  | succ n ih =>
    have h := (step_related (system.run n) (operationSystem.run n) ih).2
    simpa only [EventSystem.run_succ,system,operationSystem] using h

theorem reachable_step_defined (n : Nat) :
    ∃ e len control, 0 < len ∧
      descend 163 rootIndex (pureBits (system.run n).control) 0 = some (e,len) ∧
      controlStep e (system.run n).fields (window (pureBits (system.run n).control) 0 len) = some control :=
  related_step_defined _ _ (related_run n)

/-- The executable grammar interpreter refines the cofinal literal-machine
operation system without stuttering or extra events. -/
noncomputable def simulation : SegmentSimulation system operationSystem where
  Rel := Related
  initial := initial_related
  duration := fun _ _ => 1
  positive := by intros; decide
  next := by
    intro p s h
    have hs := (step_related p s h).2
    simpa [system,operationSystem,EventSystem.advance] using hs
  event_iff := by
    intro p s h
    have hs := (step_related p s h).1
    change ((step p).2 = true ↔ ∃ j, j < 1 ∧ operationSystem.BeepFrom s j)
    constructor
    · intro he
      refine ⟨0,by decide,?_⟩
      simpa [EventSystem.BeepFrom,EventSystem.advance] using hs.symm.trans he
    · rintro ⟨j,hj,he⟩
      have hz : j = 0 := by omega
      subst j
      have hh : (operationSystem.step s).2 = true := by
        simpa [EventSystem.BeepFrom,EventSystem.advance] using he
      exact hs.trans hh
  event_unique := by
    intro p s h j k hj hk _ _
    omega

noncomputable def refinement : EventRefinement system operationSystem := simulation.toEventRefinement

noncomputable def physicalRefinement : EventRefinement system physicalSystem :=
  refinement.trans GrammarOperationalRun.refinement

theorem eventuallySilent_iff_blank_start :
    system.EventuallySilent ↔ Record285.machine.system.EventuallySilent :=
  refinement.eventuallySilent_iff.trans operation_eventuallySilent_iff_blank_start

theorem infinitelyMany_iff_blank_start :
    system.InfinitelyManyBeeps ↔ Record285.machine.system.InfinitelyManyBeeps :=
  refinement.infinitelyManyBeeps_iff.trans operation_infinitelyMany_iff_blank_start

end Shared.PNP.Record285.GrammarPure
