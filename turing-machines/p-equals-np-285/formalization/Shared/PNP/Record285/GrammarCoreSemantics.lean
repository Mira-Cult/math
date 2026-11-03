import Shared.PNP.Record285.GrammarCoreGraph

/-! Operational meaning of the finite control-only contraction checker. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.GrammarCoreGraph
open Shared.Beeping
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.GrammarExact
open Shared.PNP.Record285.GrammarAdministrative
open Shared.PNP.Record285.GrammarControlGraph

theorem admin_test (e : Edge) (fields : List Nat) (h : isAdministrative e = true) :
    test e fields = false := by
  cases e <;> simp_all [isAdministrative,test]

theorem admin_not_beep (e : Edge) (h : isAdministrative e = true) :
    decide (e = .beep) = false := by
  cases e <;> simp_all [isAdministrative]

/-- A control-only graph row preserves the whole bank and emits no event. -/
theorem admin_step (pc next : List Bool) (fields : List Nat) (row : Row)
    (hlookup : lookup pc = some row) (hadmin : isAdministrative row.edge = true)
    (hnext : row.no = some next) :
    GrammarControlGraph.step ⟨pc,fields⟩ = (⟨next,fields⟩,false) := by
  have hi := admin_ignores_bank row.edge fields pc hadmin
  have ht := admin_test row.edge fields hadmin
  have hb := admin_not_beep row.edge hadmin
  simp [GrammarControlGraph.step,hlookup,ht,hnext,hi.2,hb]

theorem advance_after_one (s : GrammarControlGraph.State) (n : Nat) :
    GrammarControlGraph.system.advance s (n+1) =
      GrammarControlGraph.system.advance (GrammarControlGraph.step s).1 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (GrammarControlGraph.system.step (GrammarControlGraph.system.advance s (n+1))).1 = _
    rw [ih]
    rfl

/-- Successful control normalization means an actual finite silent run; all
registers are preserved, and the step bound is strict in the supplied fuel. -/
theorem settle_sound (fuel : Nat) (pc next : List Bool) (fields : List Nat)
    (h : settle fuel pc = some next) :
    ∃ steps, steps < fuel ∧
      GrammarControlGraph.system.advance ⟨pc,fields⟩ steps = ⟨next,fields⟩ ∧
      ∀ j, j < steps → ¬ GrammarControlGraph.system.BeepFrom ⟨pc,fields⟩ j := by
  induction fuel generalizing pc with
  | zero => simp [settle] at h
  | succ fuel ih =>
    cases hr : lookup pc with
    | none => simp [settle,hr] at h
    | some row =>
      cases ha : isAdministrative row.edge with
      | false =>
        have hn : next = pc := by simpa [settle,hr,ha] using h.symm
        subst next
        exact ⟨0,by omega,rfl,by simp⟩
      | true =>
        cases hn : row.no with
        | none => simp [settle,hr,ha,hn] at h
        | some mid =>
          have hs : settle fuel mid = some next := by simpa [settle,hr,ha,hn] using h
          obtain ⟨steps,hsteps,hadvance,hquiet⟩ := ih mid hs
          have hfirst := admin_step pc mid fields row hr ha hn
          refine ⟨steps+1,by omega,?_,?_⟩
          · rw [advance_after_one]
            simpa [hfirst] using hadvance
          · intro j hj hbeep
            cases j with
            | zero =>
              simp [EventSystem.BeepFrom,EventSystem.advance,GrammarControlGraph.system,hfirst] at hbeep
            | succ j =>
              have hj' : j < steps := by omega
              apply hquiet j hj'
              change (GrammarControlGraph.step
                (GrammarControlGraph.system.advance ⟨pc,fields⟩ (j+1))).2 = true at hbeep
              rw [advance_after_one,hfirst] at hbeep
              exact hbeep

/-- Execute one nonadministrative row followed by its checked silent
control normalization. The result contains the full updated bank. -/
theorem primitive_then_settle (spec : CoreRow) (pc mid target : List Bool)
    (fields : List Nat) (row : Row) (hrow : lookup pc = some row)
    (hedge : row.edge = spec.edge)
    (hnext : (if test spec.edge fields then row.yes else row.no) = some mid)
    (hsettle : settle 3 mid = some target) :
    ∃ k, k < 3 ∧
      GrammarControlGraph.system.advance ⟨pc,fields⟩ (k+1) =
        ⟨target,applyUpdate spec.edge fields⟩ ∧
      (GrammarControlGraph.step ⟨pc,fields⟩).2 = decide (spec.edge = .beep) ∧
      ∀ j, j < k → ¬ GrammarControlGraph.system.BeepFrom ⟨pc,fields⟩ (j+1) := by
  have hfirst : GrammarControlGraph.step ⟨pc,fields⟩ =
      (⟨mid,applyUpdate spec.edge fields⟩,decide (spec.edge = .beep)) := by
    simp only [GrammarControlGraph.step,hrow,Option.getD_some,hedge]
    rw [hnext]
    rfl
  obtain ⟨k,hk,hadvance,hquiet⟩ := settle_sound 3 mid target (applyUpdate spec.edge fields) hsettle
  refine ⟨k,hk,?_,?_,?_⟩
  · rw [advance_after_one,hfirst]
    exact hadvance
  · simp [hfirst]
  · intro j hj
    have hq := hquiet j hj
    change ¬ (GrammarControlGraph.step
      (GrammarControlGraph.system.advance ⟨pc,fields⟩ (j+1))).2 = true
    rw [advance_after_one,hfirst]
    exact hq

structure CoreState where
  index : Nat
  fields : List Nat
  deriving DecidableEq, Repr

def coreStep (source : Array CoreRow) (s : CoreState) : CoreState × Bool :=
  let spec := source[s.index]?.getD ⟨.beep,0,0⟩
  (⟨if test spec.edge s.fields then spec.yes else spec.no,
    applyUpdate spec.edge s.fields⟩,decide (spec.edge = .beep))

def coreSystem (source : Array CoreRow) : EventSystem CoreState :=
  ⟨⟨0,List.replicate 1909 0⟩,coreStep source⟩

def CoreRel (source : Array CoreRow) (positions : Array (List Bool))
    (s : CoreState) (g : GrammarControlGraph.State) : Prop :=
  positions[s.index]? = some g.pc ∧ s.fields = g.fields ∧ s.index < source.size

theorem check_sizes (source : Array CoreRow) (positions : Array (List Bool))
    (h : check source positions = true) :
    source.size = positions.size ∧ positions[0]? = some [false] := by
  simp only [check,Bool.and_eq_true_iff,decide_eq_true_eq] at h
  exact h.1

theorem core_initial_related (source : Array CoreRow) (positions : Array (List Bool))
    (h : check source positions = true) :
    CoreRel source positions (coreSystem source).initial GrammarControlGraph.system.initial := by
  obtain ⟨hsize,hentry⟩ := check_sizes source positions h
  have hpositive : 0 < positions.size := by
    obtain ⟨hi,_⟩ := Array.getElem?_eq_some_iff.mp hentry
    exact hi
  refine ⟨hentry,rfl,?_⟩
  change 0 < source.size
  omega

/-- One checked core action is realized by one graph operation followed by
at most two silent control actions. -/
theorem core_local_progress (source : Array CoreRow) (positions : Array (List Bool))
    (hcheck : check source positions = true) (s : CoreState) (g : GrammarControlGraph.State)
    (hrel : CoreRel source positions s g) :
    ∃ k, k < 3 ∧
      CoreRel source positions (coreStep source s).1
        (GrammarControlGraph.system.advance g (k+1)) ∧
      (coreStep source s).2 = (GrammarControlGraph.step g).2 ∧
      ∀ j, j < k → ¬ GrammarControlGraph.system.BeepFrom g (j+1) := by
  obtain ⟨hpc,hfields,hi⟩ := hrel
  obtain ⟨spec,hspec⟩ : ∃ spec, source[s.index]? = some spec := by
    exact ⟨source[s.index],by simp⟩
  have hrowcheck := check_at source positions hcheck s.index hi
  obtain ⟨row,no,yes,hrow,hedge,hadmin,hno,hyes,hno',hyes'⟩ :=
    checkRow_sound source positions s.index spec g.pc hspec hpc hrowcheck
  let b := test spec.edge s.fields
  let index := if b then spec.yes else spec.no
  let target := if b then yes else no
  have hpos : positions[index]? = some target := by
    dsimp [index,target]
    cases b <;> simp_all
  have hbound : index < source.size := by
    obtain ⟨hp,_⟩ := Array.getElem?_eq_some_iff.mp hpos
    have hsizes := (check_sizes source positions hcheck).1
    omega
  have hbind : (if b then row.yes else row.no).bind (settle 3) = some target := by
    dsimp [target]
    cases b <;> simp_all
  cases hn : (if b then row.yes else row.no) with
  | none => simp [hn] at hbind
  | some mid =>
    have hsettle : settle 3 mid = some target := by simpa [hn] using hbind
    have hnext : (if test spec.edge g.fields then row.yes else row.no) = some mid := by
      simpa [b,hfields] using hn
    obtain ⟨k,hk,hadvance,hevent,hquiet⟩ :=
      primitive_then_settle spec g.pc mid target g.fields row hrow hedge hnext hsettle
    have hs : coreStep source s =
        (⟨index,applyUpdate spec.edge s.fields⟩,decide (spec.edge = .beep)) := by
      simp [coreStep,hspec,index,b]
    refine ⟨k,hk,?_,?_,hquiet⟩
    · rw [hs]
      cases g with
      | mk pc fields =>
        change CoreRel source positions ⟨index,applyUpdate spec.edge s.fields⟩
          (GrammarControlGraph.system.advance ⟨pc,fields⟩ (k+1))
        rw [hadvance]
        exact ⟨hpos,by simp [hfields],hbound⟩
    · rw [hs]
      exact hevent.symm

theorem quiet_only_first (g : GrammarControlGraph.State) (k j : Nat)
    (hq : ∀ n, n < k → ¬ GrammarControlGraph.system.BeepFrom g (n+1))
    (hj : j < k+1) (he : GrammarControlGraph.system.BeepFrom g j) : j = 0 := by
  cases j with
  | zero => rfl
  | succ j =>
    exfalso
    apply hq j (by omega)
    simpa using he

noncomputable def coreDuration (source : Array CoreRow) (positions : Array (List Bool))
    (hcheck : check source positions = true) (s : CoreState) (g : GrammarControlGraph.State) : Nat := by
  classical
  exact if h : CoreRel source positions s g then
    Classical.choose (core_local_progress source positions hcheck s g h) + 1
  else 1

/-- A checked graph certificate yields a cofinal event-exact refinement, with
one to three target actions for each core action. -/
noncomputable def coreSimulation (source : Array CoreRow) (positions : Array (List Bool))
    (hcheck : check source positions = true) :
    SegmentSimulation (coreSystem source) GrammarControlGraph.system where
  Rel := CoreRel source positions
  initial := core_initial_related source positions hcheck
  duration := coreDuration source positions hcheck
  positive := by
    intro s g h
    simp only [coreDuration,dif_pos h]
    omega
  next := by
    intro s g h
    have hp := Classical.choose_spec (core_local_progress source positions hcheck s g h)
    simp only [coreDuration,dif_pos h]
    exact hp.2.1
  event_iff := by
    intro s g h
    have hp := Classical.choose_spec (core_local_progress source positions hcheck s g h)
    simp only [coreDuration,dif_pos h]
    constructor
    · intro he
      refine ⟨0,by omega,?_⟩
      change (GrammarControlGraph.step g).2 = true
      change (coreStep source s).2 = true at he
      exact hp.2.2.1.symm.trans he
    · rintro ⟨j,hj,he⟩
      have hz := quiet_only_first g _ j hp.2.2.2 hj he
      subst j
      change (GrammarControlGraph.step g).2 = true at he
      change (coreStep source s).2 = true
      exact hp.2.2.1.trans he
  event_unique := by
    intro s g h j k hj hk hjbeep hkbeep
    have hp := Classical.choose_spec (core_local_progress source positions hcheck s g h)
    simp only [coreDuration,dif_pos h] at hj hk
    have hj0 := quiet_only_first g _ j hp.2.2.2 hj hjbeep
    have hk0 := quiet_only_first g _ k hp.2.2.2 hk hkbeep
    omega

noncomputable def coreRefinement (source : Array CoreRow) (positions : Array (List Bool))
    (hcheck : check source positions = true) :
    EventRefinement (coreSystem source) GrammarControlGraph.system :=
  (coreSimulation source positions hcheck).toEventRefinement

end Shared.PNP.Record285.GrammarCoreGraph
