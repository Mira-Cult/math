import Shared.PNP.Record285.OwnershipSemantics

/-! Progress-sensitive coalescing simulation, retaining all logical class
sums and the verified physical bank invariant. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.OwnershipCore
open Shared.Beeping
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.GrammarExact
open Shared.PNP.Record285.GrammarCoreGraph
open Shared.PNP.Record285.GrammarCoreZero

def CoalescedRel (logical : Array Row) (masks : Array (Array Nat))
    (physical : Array CoreRow) (physicalMasks : Array (Array Nat))
    (classes mapping : Array Nat) (s : State) (p : CoreState) : Prop :=
  s.index < logical.size ∧ mapping[s.index]? = some p.index ∧ Valid logical masks s ∧
    GrammarCoreZero.Valid physical physicalMasks p ∧ BankRel classes s.bank p.fields

theorem advance_valid (rows : Array CoreRow) (masks : Array (Array Nat))
    (hcheck : GrammarCoreZero.check rows masks = true) (s : CoreState)
    (hvalid : GrammarCoreZero.Valid rows masks s) (n : Nat) :
    GrammarCoreZero.Valid rows masks ((coreSystem rows).advance s n) := by
  induction n with
  | zero => exact hvalid
  | succ n ih =>
    have hs := GrammarCoreZero.step_preserves rows masks hcheck ((coreSystem rows).advance s n) ih
    simpa only [EventSystem.advance,coreSystem] using hs

theorem single_wellFormed (action : Action) (e : Edge) (i : Nat)
    (he : singleEdge action = some e) (hindex : operationIndex e = some i) (h : WellFormed action) : i < 18 := by
  cases action <;> simp only [singleEdge,Option.some.injEq] at he
  all_goals try contradiction
  all_goals subst e
  all_goals simp_all [operationIndex,WellFormed]

theorem single_no_beep (action : Action) (e : Edge) (he : singleEdge action = some e) (classes : Array Nat) :
    decide (action = .beep) = false ∧ decide (targetEdge classes action = .beep) = false := by
  cases action <;> simp_all [singleEdge,targetEdge]

theorem single_localMatch (physical : Array CoreRow) (classes mask : Array Nat)
    (row : Row) (pc : Nat) (target : CoreRow) (no yes : Nat) (e : Edge) (i : Nat)
    (hmatch : LocalMatch physical classes mask row pc target no yes)
    (he : singleEdge row.action = some e) (hi : operationIndex e = some i) :
    peerZero classes mask i = true ∧ target.no = no ∧ target.yes = yes := by
  cases row with
  | mk action rn ry =>
    cases action <;> simp only [singleEdge,Option.some.injEq] at he
    all_goals try contradiction
    all_goals subst e
    all_goals simp_all [operationIndex,LocalMatch]

theorem row_equal (row : CoreRow) (edge : Edge) (no yes : Nat)
    (he : row.edge = edge) (hn : row.no = no) (hy : row.yes = yes) :
    row = ⟨edge,no,yes⟩ := by cases row <;> simp_all

/-- A non-move logical operation is implemented in exactly one physical
core step, preserving all fifteen class sums. -/
theorem single_progress (logical : Array Row) (masks : Array (Array Nat))
    (physical : Array CoreRow) (physicalMasks : Array (Array Nat))
    (classes mapping : Array Nat) (hlogic : invariantCheck logical masks = true)
    (hphysical : GrammarCoreZero.check physical physicalMasks = true)
    (s : State) (p : CoreState) (hrel : CoalescedRel logical masks physical physicalMasks classes mapping s p)
    (row : Row) (mask : Array Nat) (target : CoreRow) (no yes : Nat) (e : Edge) (i : Nat)
    (hrow : logical[s.index]? = some row) (hmask : masks[s.index]? = some mask)
    (htarget : physical[p.index]? = some target) (hno : mapping[row.no]? = some no)
    (hyes : mapping[row.yes]? = some yes) (hmatch : LocalMatch physical classes mask row p.index target no yes)
    (he : singleEdge row.action = some e) (hi : operationIndex e = some i)
    (hclass : classAt classes i < 15) :
    CoalescedRel logical masks physical physicalMasks classes mapping (step logical s).1 (coreStep physical p).1 ∧
      (step logical s).2 = (coreStep physical p).2 := by
  obtain ⟨_,_,hlvalid,hpvalid,hbank⟩ := hrel
  have hwf := valid_row_wellFormed logical masks hlogic s hlvalid row hrow
  have hsmall := single_wellFormed row.action e i he hi hwf
  have hm := single_localMatch physical classes mask row p.index target no yes e i hmatch he hi
  have hbankMask : validBank mask s.bank := by
    obtain ⟨_,m,hm',hv⟩ := hlvalid
    rw [hmask] at hm'
    have hmEq : m = mask := Option.some.inj hm'.symm
    simpa [hmEq] using hv
  have hiso : Isolated classes s.bank i := by
    intro j hj hne hclass'
    exact peerZero_sound classes mask i s.bank hm.1 hbankMask j hj hne hclass'
  have htest := single_test_matches classes s.bank p.fields row.action e i he hi hsmall hclass hiso hbank
  have hnewBank := single_bankRel classes s.bank p.fields row.action e i he hi hsmall hclass hiso hbank
  have htarget' : physical[p.index]? = some ⟨targetEdge classes row.action,no,yes⟩ := by
    rw [row_equal target _ _ _ hmatch.1 hm.2.1 hm.2.2] at htarget
    exact htarget
  let branch := observe row.action s.bank
  let nextLogical := if branch then row.yes else row.no
  let nextPhysical := if branch then yes else no
  have hnextmap : mapping[nextLogical]? = some nextPhysical := by
    dsimp [nextLogical,nextPhysical]
    cases branch <;> simp_all
  have hlstep : step logical s = (⟨nextLogical,update row.action s.bank⟩,decide (row.action = .beep)) := by
    simp [step,hrow,nextLogical,branch]
  have hpstep : coreStep physical p =
      (⟨nextPhysical,applyUpdate (targetEdge classes row.action) p.fields⟩,
        decide (targetEdge classes row.action = .beep)) := by
    simp [coreStep,htarget',nextPhysical,branch,htest]
  have hlvalid' := step_preserves logical masks hlogic s hlvalid
  have hpvalid' := GrammarCoreZero.step_preserves physical physicalMasks hphysical p hpvalid
  rw [hlstep] at hlvalid'
  rw [hpstep] at hpvalid'
  have hnext : nextLogical < logical.size := hlvalid'.1
  have hb := single_no_beep row.action e he classes
  rw [hlstep,hpstep]
  refine ⟨?_,?_⟩
  · change CoalescedRel logical masks physical physicalMasks classes mapping
      ⟨nextLogical,update row.action s.bank⟩
      ⟨nextPhysical,applyUpdate (targetEdge classes row.action) p.fields⟩
    exact ⟨hnext,hnextmap,hlvalid',hpvalid',hnewBank⟩
  · exact hb.1.trans hb.2.symm

/-- A logical move takes a positive finite, completely silent physical
segment and preserves the coalesced relation. -/
theorem move_local_progress (logical : Array Row) (masks : Array (Array Nat))
    (physical : Array CoreRow) (physicalMasks : Array (Array Nat))
    (classes mapping : Array Nat) (hlogic : invariantCheck logical masks = true)
    (hphysical : GrammarCoreZero.check physical physicalMasks = true)
    (s : State) (p : CoreState) (hrel : CoalescedRel logical masks physical physicalMasks classes mapping s p)
    (row : Row) (mask : Array Nat) (target : CoreRow) (no yes src dst : Nat)
    (hrow : logical[s.index]? = some row) (hmask : masks[s.index]? = some mask)
    (htarget : physical[p.index]? = some target) (hno : mapping[row.no]? = some no)
    (hmatch : LocalMatch physical classes mask row p.index target no yes)
    (hmove : row.action = .move src dst) (hcs : classAt classes src < 15)
    (hcd : classAt classes dst < 15) :
    CoalescedRel logical masks physical physicalMasks classes mapping (step logical s).1
        ((coreSystem physical).advance p (2*s.bank src+1)) ∧
      (step logical s).2 = false ∧
      ∀ t, t < 2*s.bank src+1 → ¬ (coreSystem physical).BeepFrom p t := by
  obtain ⟨_,_,hlvalid,hpvalid,hbank⟩ := hrel
  have hwf := valid_row_wellFormed logical masks hlogic s hlvalid row hrow
  have hwd : src < 18 ∧ dst < 18 ∧ src ≠ dst := by simpa [hmove,WellFormed] using hwf
  have hm : ∃ body, physical[target.no]? = some body ∧ peerZero classes mask src = true ∧
      peerZero classes mask dst = true ∧ classAt classes src ≠ classAt classes dst ∧
      body.edge = .inc (classAt classes dst) ∧ body.no = p.index ∧ body.yes = p.index ∧
      target.yes = no ∧ row.no = row.yes := by
    simpa [hmove,LocalMatch] using hmatch.2
  obtain ⟨body,hbody,hpeerS,hpeerD,hclasses,hbodyEdge,hbodyNo,hbodyYes,hexit,_⟩ := hm
  have hbankMask : validBank mask s.bank := by
    obtain ⟨_,m,hm',hv⟩ := hlvalid
    rw [hmask] at hm'
    have hmEq : m = mask := Option.some.inj hm'.symm
    simpa [hmEq] using hv
  have hisoS : Isolated classes s.bank src := by
    intro j hj hne hclass'
    exact peerZero_sound classes mask src s.bank hpeerS hbankMask j hj hne hclass'
  have hisoD : Isolated classes s.bank dst := by
    intro j hj hne hclass'
    exact peerZero_sound classes mask dst s.bank hpeerD hbankMask j hj hne hclass'
  have hedge : target.edge = .dec (classAt classes src) := by simpa [hmove,targetEdge] using hmatch.1
  have hhead : physical[p.index]? = some ⟨.dec (classAt classes src),target.no,no⟩ := by
    rw [row_equal target _ _ _ hedge rfl hexit] at htarget
    exact htarget
  have hbody' : physical[target.no]? = some ⟨.inc (classAt classes dst),p.index,p.index⟩ := by
    rw [row_equal body _ _ _ hbodyEdge hbodyNo hbodyYes] at hbody
    exact hbody
  obtain ⟨out,hrun,hnewBank,hquiet⟩ := move_progress physical classes s.bank p.fields
    p.index target.no no src dst hwd.1 hwd.2.1 hcs hcd hclasses hisoS hisoD hbank hhead hbody'
  have hlstep : step logical s = (⟨row.no,update (.move src dst) s.bank⟩,false) := by
    simp [step,hrow,hmove,observe]
  have hlvalid' := step_preserves logical masks hlogic s hlvalid
  rw [hlstep] at hlvalid'
  have hpvalid' := advance_valid physical physicalMasks hphysical p hpvalid (2*s.bank src+1)
  rw [hrun] at hpvalid'
  have hnext : row.no < logical.size := hlvalid'.1
  rw [hlstep,hrun]
  refine ⟨?_,rfl,hquiet⟩
  change CoalescedRel logical masks physical physicalMasks classes mapping
    ⟨row.no,update (.move src dst) s.bank⟩ ⟨no,out⟩
  exact ⟨hnext,hno,hlvalid',hpvalid',hnewBank⟩

theorem beep_progress (logical : Array Row) (masks : Array (Array Nat))
    (physical : Array CoreRow) (physicalMasks : Array (Array Nat))
    (classes mapping : Array Nat) (hlogic : invariantCheck logical masks = true)
    (hphysical : GrammarCoreZero.check physical physicalMasks = true)
    (s : State) (p : CoreState) (hrel : CoalescedRel logical masks physical physicalMasks classes mapping s p)
    (row : Row) (mask : Array Nat) (target : CoreRow) (no yes : Nat)
    (hrow : logical[s.index]? = some row) (htarget : physical[p.index]? = some target)
    (hno : mapping[row.no]? = some no) (hmatch : LocalMatch physical classes mask row p.index target no yes)
    (hbeep : row.action = .beep) :
    CoalescedRel logical masks physical physicalMasks classes mapping (step logical s).1 (coreStep physical p).1 ∧
      (step logical s).2 = (coreStep physical p).2 := by
  obtain ⟨_,_,hlvalid,hpvalid,hbank⟩ := hrel
  have hedge : target.edge = .beep := by simpa [hbeep,targetEdge] using hmatch.1
  have hbranches : target.no = no ∧ target.yes = yes := by simpa [hbeep,LocalMatch] using hmatch.2
  have htarget' : physical[p.index]? = some ⟨.beep,no,yes⟩ := by
    rw [row_equal target _ _ _ hedge hbranches.1 hbranches.2] at htarget
    exact htarget
  have hu : update .beep s.bank = s.bank := by funext j; rfl
  have hlstep : step logical s = (⟨row.no,s.bank⟩,true) := by
    simp [step,hrow,hbeep,observe,hu]
  have hpstep : coreStep physical p = (⟨no,p.fields⟩,true) := by
    simp [coreStep,htarget',GrammarControlGraph.test,applyUpdate]
  have hlvalid' := step_preserves logical masks hlogic s hlvalid
  have hpvalid' := GrammarCoreZero.step_preserves physical physicalMasks hphysical p hpvalid
  rw [hlstep] at hlvalid'
  rw [hpstep] at hpvalid'
  have hnext : row.no < logical.size := hlvalid'.1
  rw [hlstep,hpstep]
  exact ⟨⟨hnext,hno,hlvalid',hpvalid',hbank⟩,rfl⟩

theorem oneStep_segment (logical : Array Row) (masks : Array (Array Nat))
    (physical : Array CoreRow) (physicalMasks : Array (Array Nat))
    (classes mapping : Array Nat) (s : State) (p : CoreState)
    (hnext : CoalescedRel logical masks physical physicalMasks classes mapping (step logical s).1 (coreStep physical p).1)
    (hevent : (step logical s).2 = (coreStep physical p).2) :
    ∃ d, 0 < d ∧ CoalescedRel logical masks physical physicalMasks classes mapping
        (step logical s).1 ((coreSystem physical).advance p d) ∧
      ((step logical s).2 = true ↔ ∃ j, j < d ∧ (coreSystem physical).BeepFrom p j) ∧
      ∀ j k, j < d → k < d → (coreSystem physical).BeepFrom p j →
        (coreSystem physical).BeepFrom p k → j = k := by
  refine ⟨1,by decide,?_,?_,?_⟩
  · exact hnext
  · constructor
    · intro h
      refine ⟨0,by decide,?_⟩
      change (coreStep physical p).2 = true
      exact hevent.symm.trans h
    · rintro ⟨j,hj,h⟩
      have hz : j = 0 := by omega
      subst j
      change (coreStep physical p).2 = true at h
      exact hevent.trans h
  · intro j k hj hk _ _
    omega

/-- Every checked logical action has a finite, positive, event-exact physical
segment. The bound for a move depends on its arbitrary source value. -/
theorem coalescing_local_progress (logical : Array Row) (masks : Array (Array Nat))
    (physical : Array CoreRow) (physicalMasks : Array (Array Nat))
    (classes mapping : Array Nat) (hlogic : invariantCheck logical masks = true)
    (hphysical : GrammarCoreZero.check physical physicalMasks = true)
    (hmap : mappingCheck logical physical masks classes mapping = true)
    (s : State) (p : CoreState) (hrel : CoalescedRel logical masks physical physicalMasks classes mapping s p) :
    ∃ d, 0 < d ∧ CoalescedRel logical masks physical physicalMasks classes mapping
        (step logical s).1 ((coreSystem physical).advance p d) ∧
      ((step logical s).2 = true ↔ ∃ j, j < d ∧ (coreSystem physical).BeepFrom p j) ∧
      ∀ j k, j < d → k < d → (coreSystem physical).BeepFrom p j →
        (coreSystem physical).BeepFrom p k → j = k := by
  have hrel' := hrel
  obtain ⟨hindex,hposition,hvalid,_,_⟩ := hrel'
  have hvalid' := hvalid
  obtain ⟨_,mask,hmask,_⟩ := hvalid'
  obtain ⟨row,hrow⟩ : ∃ row, logical[s.index]? = some row := ⟨logical[s.index],by simp⟩
  have hparts := mapping_parts logical physical masks classes mapping hmap
  have hrowcheck := hparts.2.2.2.2 s.index hindex
  obtain ⟨target,no,yes,htarget,hno,hyes,hmatch⟩ :=
    mappingRow_sound logical physical masks classes mapping s.index p.index row mask hrow hmask hposition hrowcheck
  have hwf := valid_row_wellFormed logical masks hlogic s hvalid row hrow
  cases ha : row.action with
  | inc i =>
    have he : singleEdge row.action = some (.inc i) := by simp [ha,singleEdge]
    have hi : operationIndex (.inc i) = some i := rfl
    have hsmall : i < 18 := single_wellFormed row.action (.inc i) i he hi hwf
    have hc := hparts.2.2.2.1 i hsmall
    have hp := single_progress logical masks physical physicalMasks classes mapping hlogic hphysical
      s p hrel row mask target no yes (.inc i) i hrow hmask htarget hno hyes hmatch he hi hc
    exact oneStep_segment logical masks physical physicalMasks classes mapping s p hp.1 hp.2
  | dec i =>
    have he : singleEdge row.action = some (.dec i) := by simp [ha,singleEdge]
    have hi : operationIndex (.dec i) = some i := rfl
    have hsmall : i < 18 := single_wellFormed row.action (.dec i) i he hi hwf
    have hc := hparts.2.2.2.1 i hsmall
    have hp := single_progress logical masks physical physicalMasks classes mapping hlogic hphysical
      s p hrel row mask target no yes (.dec i) i hrow hmask htarget hno hyes hmatch he hi hc
    exact oneStep_segment logical masks physical physicalMasks classes mapping s p hp.1 hp.2
  | half i =>
    have he : singleEdge row.action = some (.half i) := by simp [ha,singleEdge]
    have hi : operationIndex (.half i) = some i := rfl
    have hsmall : i < 18 := single_wellFormed row.action (.half i) i he hi hwf
    have hc := hparts.2.2.2.1 i hsmall
    have hp := single_progress logical masks physical physicalMasks classes mapping hlogic hphysical
      s p hrel row mask target no yes (.half i) i hrow hmask htarget hno hyes hmatch he hi hc
    exact oneStep_segment logical masks physical physicalMasks classes mapping s p hp.1 hp.2
  | beep =>
    have hp := beep_progress logical masks physical physicalMasks classes mapping hlogic hphysical
      s p hrel row mask target no yes hrow htarget hno hmatch ha
    exact oneStep_segment logical masks physical physicalMasks classes mapping s p hp.1 hp.2
  | move src dst =>
    have hwd : src < 18 ∧ dst < 18 ∧ src ≠ dst := by simpa [ha,WellFormed] using hwf
    have hcs := hparts.2.2.2.1 src hwd.1
    have hcd := hparts.2.2.2.1 dst hwd.2.1
    obtain ⟨hnext,hnoevent,hquiet⟩ := move_local_progress logical masks physical physicalMasks
      classes mapping hlogic hphysical s p hrel row mask target no yes src dst hrow hmask htarget hno hmatch ha hcs hcd
    refine ⟨2*s.bank src+1,by omega,hnext,?_,?_⟩
    · constructor
      · intro h
        rw [hnoevent] at h
        contradiction
      · rintro ⟨j,hj,hbeep⟩
        exact False.elim (hquiet j hj hbeep)
    · intro j k hj hk hjbeep _
      exact False.elim (hquiet j hj hjbeep)

theorem coalescing_initial (logical : Array Row) (masks : Array (Array Nat))
    (physical : Array CoreRow) (physicalMasks : Array (Array Nat))
    (classes mapping : Array Nat) (hlogic : invariantCheck logical masks = true)
    (hphysical : GrammarCoreZero.check physical physicalMasks = true)
    (hmap : mappingCheck logical physical masks classes mapping = true)
    (hl : 0 < logical.size) (hp : 0 < physical.size) :
    CoalescedRel logical masks physical physicalMasks classes mapping (system logical).initial
      (coreSystem physical).initial := by
  refine ⟨hl,?_,initial_valid logical masks hlogic hl,
    GrammarCoreZero.initial_valid physical physicalMasks hphysical hp,initial_bankRel classes⟩
  exact (mapping_parts logical physical masks classes mapping hmap).2.2.1

noncomputable def coalescingDuration (logical : Array Row) (masks : Array (Array Nat))
    (physical : Array CoreRow) (physicalMasks : Array (Array Nat)) (classes mapping : Array Nat)
    (hlogic : invariantCheck logical masks = true) (hphysical : GrammarCoreZero.check physical physicalMasks = true)
    (hmap : mappingCheck logical physical masks classes mapping = true) (s : State) (p : CoreState) : Nat := by
  classical
  exact if h : CoalescedRel logical masks physical physicalMasks classes mapping s p then
    Classical.choose (coalescing_local_progress logical masks physical physicalMasks classes mapping hlogic hphysical hmap s p h)
  else 1

/-- The checked ownership/class mapping gives a cofinal event-exact
simulation, with each move paid by its finite decrement/increment loop. -/
noncomputable def coalescingSimulation (logical : Array Row) (masks : Array (Array Nat))
    (physical : Array CoreRow) (physicalMasks : Array (Array Nat)) (classes mapping : Array Nat)
    (hlogic : invariantCheck logical masks = true) (hphysical : GrammarCoreZero.check physical physicalMasks = true)
    (hmap : mappingCheck logical physical masks classes mapping = true)
    (hl : 0 < logical.size) (hp : 0 < physical.size) :
    SegmentSimulation (system logical) (coreSystem physical) where
  Rel := CoalescedRel logical masks physical physicalMasks classes mapping
  initial := coalescing_initial logical masks physical physicalMasks classes mapping hlogic hphysical hmap hl hp
  duration := coalescingDuration logical masks physical physicalMasks classes mapping hlogic hphysical hmap
  positive := by
    intro s p h
    have hs := Classical.choose_spec
      (coalescing_local_progress logical masks physical physicalMasks classes mapping hlogic hphysical hmap s p h)
    simp only [coalescingDuration,dif_pos h]
    exact hs.1
  next := by
    intro s p h
    have hs := Classical.choose_spec
      (coalescing_local_progress logical masks physical physicalMasks classes mapping hlogic hphysical hmap s p h)
    simp only [coalescingDuration,dif_pos h]
    exact hs.2.1
  event_iff := by
    intro s p h
    have hs := Classical.choose_spec
      (coalescing_local_progress logical masks physical physicalMasks classes mapping hlogic hphysical hmap s p h)
    simp only [coalescingDuration,dif_pos h]
    exact hs.2.2.1
  event_unique := by
    intro s p h j k hj hk hjbeep hkbeep
    have hs := Classical.choose_spec
      (coalescing_local_progress logical masks physical physicalMasks classes mapping hlogic hphysical hmap s p h)
    simp only [coalescingDuration,dif_pos h] at hj hk
    exact hs.2.2.2 j k hj hk hjbeep hkbeep

noncomputable def coalescingRefinement (logical : Array Row) (masks : Array (Array Nat))
    (physical : Array CoreRow) (physicalMasks : Array (Array Nat)) (classes mapping : Array Nat)
    (hlogic : invariantCheck logical masks = true) (hphysical : GrammarCoreZero.check physical physicalMasks = true)
    (hmap : mappingCheck logical physical masks classes mapping = true)
    (hl : 0 < logical.size) (hp : 0 < physical.size) :
    EventRefinement (system logical) (coreSystem physical) :=
  (coalescingSimulation logical masks physical physicalMasks classes mapping hlogic hphysical hmap hl hp).toEventRefinement

end Shared.PNP.Record285.OwnershipCore
