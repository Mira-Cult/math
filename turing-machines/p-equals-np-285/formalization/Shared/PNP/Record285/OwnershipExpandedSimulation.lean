import Shared.PNP.Record285.OwnershipExpandedCertificate
import Shared.PNP.Record285.OwnershipExpandedLoop

/-! Progress-sensitive, full-bank correctness of ownership contraction. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.OwnershipCore
open Shared.Beeping

def ExpansionRel (logical : Array Row) (mapping : Array Nat) (s p : State) : Prop :=
  s.index < logical.size ∧ mapping[s.index]? = some p.index ∧ s.bank = p.bank

theorem expansion_parts (logical expanded : Array Row) (mapping : Array Nat)
    (h : expansionCheck logical expanded mapping = true) :
    logical.size = mapping.size ∧ mapping[0]? = some 0 ∧
      ∀ i, i < logical.size → expansionRow logical expanded mapping i = true := by
  simp only [expansionCheck,Bool.and_eq_true_iff,decide_eq_true_eq] at h
  refine ⟨h.1.1,h.1.2,?_⟩
  intro i hi
  exact List.all_eq_true.mp h.2 i (List.mem_range.mpr hi)

theorem logical_row_equal (row : Row) (action : Action) (no yes : Nat)
    (ha : row.action = action) (hn : row.no = no) (hy : row.yes = yes) :
    row = ⟨action,no,yes⟩ := by cases row <;> simp_all

/-- A noncontracted operation preserves the entire logical bank in one step. -/
theorem ordinary_progress (logical expanded : Array Row) (mapping : Array Nat)
    (hcheck : expansionCheck logical expanded mapping = true)
    (s p : State) (hrel : ExpansionRel logical mapping s p)
    (row target : Row) (no yes : Nat)
    (hrow : logical[s.index]? = some row) (htarget : expanded[p.index]? = some target)
    (hno : mapping[row.no]? = some no) (hyes : mapping[row.yes]? = some yes)
    (ha : target.action = row.action) (hn : target.no = no) (hy : target.yes = yes) :
    ExpansionRel logical mapping (step logical s).1 (step expanded p).1 ∧
      (step logical s).2 = (step expanded p).2 := by
  have hbank := hrel.2.2
  have htarget' : expanded[p.index]? = some ⟨row.action,no,yes⟩ := by
    rw [logical_row_equal target row.action no yes ha hn hy] at htarget
    exact htarget
  let branch := observe row.action s.bank
  let sourceNext := if branch then row.yes else row.no
  let targetNext := if branch then yes else no
  have hmap : mapping[sourceNext]? = some targetNext := by
    dsimp [sourceNext,targetNext]
    cases branch <;> simp_all
  have hbound : sourceNext < logical.size := by
    obtain ⟨hm,_⟩ := Array.getElem?_eq_some_iff.mp hmap
    have hs := (expansion_parts logical expanded mapping hcheck).1
    omega
  have hs : step logical s =
      (⟨sourceNext,update row.action s.bank⟩,decide (row.action = .beep)) := by
    simp [step,hrow,sourceNext,branch]
  have hp : step expanded p =
      (⟨targetNext,update row.action p.bank⟩,decide (row.action = .beep)) := by
    simp [step,htarget',targetNext,branch,hbank]
  rw [hs,hp]
  exact ⟨⟨hbound,hmap,by simp [hbank]⟩,rfl⟩

/-- A contracted move equals its whole finite primitive loop, including all
bank locations and all event flags. -/
theorem contracted_move_progress (logical expanded : Array Row) (mapping : Array Nat)
    (hcheck : expansionCheck logical expanded mapping = true)
    (s p : State) (hrel : ExpansionRel logical mapping s p)
    (row target body : Row) (no src dst : Nat)
    (hrow : logical[s.index]? = some row) (htarget : expanded[p.index]? = some target)
    (hbody : expanded[target.no]? = some body) (hno : mapping[row.no]? = some no)
    (hmove : row.action = .move src dst) (hne : src ≠ dst)
    (hedge : target.action = .dec src) (hexit : target.yes = no)
    (hbodyEdge : body.action = .inc dst) (hbodyNo : body.no = p.index) (hbodyYes : body.yes = p.index) :
    ExpansionRel logical mapping (step logical s).1
        ((system expanded).advance p (2*s.bank src+1)) ∧
      (step logical s).2 = false ∧
      ∀ t, t < 2*s.bank src+1 → ¬ (system expanded).BeepFrom p t := by
  have hbank := hrel.2.2
  have hhead : expanded[p.index]? = some ⟨.dec src,target.no,no⟩ := by
    rw [logical_row_equal target _ _ _ hedge rfl hexit] at htarget
    exact htarget
  have hbody' : expanded[target.no]? = some ⟨.inc dst,p.index,p.index⟩ := by
    rw [logical_row_equal body _ _ _ hbodyEdge hbodyNo hbodyYes] at hbody
    exact hbody
  have hrun := expanded_move_run expanded p.index target.no no src dst (s.bank src) p.bank
    hhead hbody' hne (by rw [← hbank])
  have hsource : step logical s = (⟨row.no,update (.move src dst) s.bank⟩,false) := by
    simp [step,hrow,hmove,observe]
  have hbound : row.no < logical.size := by
    obtain ⟨hm,_⟩ := Array.getElem?_eq_some_iff.mp hno
    have hs := (expansion_parts logical expanded mapping hcheck).1
    omega
  rw [hsource,hrun.1]
  refine ⟨?_,rfl,hrun.2⟩
  change ExpansionRel logical mapping ⟨row.no,update (.move src dst) s.bank⟩
    ⟨no,update (.move src dst) p.bank⟩
  exact ⟨hbound,hno,by simp [hbank]⟩

theorem expanded_oneStep_segment (logical expanded : Array Row) (mapping : Array Nat) (s p : State)
    (hnext : ExpansionRel logical mapping (step logical s).1 (step expanded p).1)
    (hevent : (step logical s).2 = (step expanded p).2) :
    ∃ d, 0 < d ∧ ExpansionRel logical mapping (step logical s).1 ((system expanded).advance p d) ∧
      ((step logical s).2 = true ↔ ∃ j, j < d ∧ (system expanded).BeepFrom p j) ∧
      ∀ j k, j < d → k < d → (system expanded).BeepFrom p j → (system expanded).BeepFrom p k → j = k := by
  refine ⟨1,by decide,?_,?_,?_⟩
  · exact hnext
  · constructor
    · intro he
      refine ⟨0,by decide,?_⟩
      change (step expanded p).2 = true
      exact hevent.symm.trans he
    · rintro ⟨j,hj,he⟩
      have hz : j = 0 := by omega
      subst j
      change (step expanded p).2 = true at he
      exact hevent.trans he
  · intro j k hj hk _ _
    omega

/-- Every checked contraction corresponds to a positive, finite and
event-exact expanded segment. -/
theorem expansion_local_progress (logical expanded : Array Row) (mapping : Array Nat)
    (hcheck : expansionCheck logical expanded mapping = true) (s p : State)
    (hrel : ExpansionRel logical mapping s p) :
    ∃ d, 0 < d ∧ ExpansionRel logical mapping (step logical s).1 ((system expanded).advance p d) ∧
      ((step logical s).2 = true ↔ ∃ j, j < d ∧ (system expanded).BeepFrom p j) ∧
      ∀ j k, j < d → k < d → (system expanded).BeepFrom p j → (system expanded).BeepFrom p k → j = k := by
  have hi := hrel.1
  have hp := hrel.2.1
  obtain ⟨row,hrow⟩ : ∃ row, logical[s.index]? = some row := ⟨logical[s.index],by simp⟩
  have hrowcheck := (expansion_parts logical expanded mapping hcheck).2.2 s.index hi
  obtain ⟨target,no,yes,htarget,hno,hyes,hmatch⟩ :=
    expansionRow_sound logical expanded mapping s.index p.index row hrow hp hrowcheck
  by_cases hm : ∃ src dst, row.action = .move src dst
  · obtain ⟨src,dst,hmove⟩ := hm
    have hbody : ∃ body, expanded[target.no]? = some body ∧ src ≠ dst ∧ target.action = .dec src ∧
        target.yes = no ∧ row.no = row.yes ∧ body.action = .inc dst ∧ body.no = p.index ∧ body.yes = p.index := by
      simpa [ExpansionMatch,hmove] using hmatch
    obtain ⟨body,hbody,hne,hedge,hexit,_,hbodyEdge,hbodyNo,hbodyYes⟩ := hbody
    obtain ⟨hnext,hnoevent,hquiet⟩ := contracted_move_progress logical expanded mapping hcheck s p hrel
      row target body no src dst hrow htarget hbody hno hmove hne hedge hexit hbodyEdge hbodyNo hbodyYes
    refine ⟨2*s.bank src+1,by omega,hnext,?_,?_⟩
    · constructor
      · intro he
        rw [hnoevent] at he
        contradiction
      · rintro ⟨j,hj,he⟩
        exact False.elim (hquiet j hj he)
    · intro j k hj hk he _
      exact False.elim (hquiet j hj he)
  · have hordinary : target.action = row.action ∧ target.no = no ∧ target.yes = yes := by
      cases ha : row.action with
      | inc i => simpa [ExpansionMatch,ha] using hmatch
      | dec i => simpa [ExpansionMatch,ha] using hmatch
      | half i => simpa [ExpansionMatch,ha] using hmatch
      | beep => simpa [ExpansionMatch,ha] using hmatch
      | move src dst => exact False.elim (hm ⟨src,dst,ha⟩)
    have hstep := ordinary_progress logical expanded mapping hcheck s p hrel row target no yes
      hrow htarget hno hyes hordinary.1 hordinary.2.1 hordinary.2.2
    exact expanded_oneStep_segment logical expanded mapping s p hstep.1 hstep.2

theorem expansion_initial (logical expanded : Array Row) (mapping : Array Nat)
    (hcheck : expansionCheck logical expanded mapping = true) (hne : 0 < logical.size) :
    ExpansionRel logical mapping (system logical).initial (system expanded).initial := by
  refine ⟨hne,?_,rfl⟩
  exact (expansion_parts logical expanded mapping hcheck).2.1

noncomputable def expansionDuration (logical expanded : Array Row) (mapping : Array Nat)
    (hcheck : expansionCheck logical expanded mapping = true) (s p : State) : Nat := by
  classical
  exact if h : ExpansionRel logical mapping s p then
    Classical.choose (expansion_local_progress logical expanded mapping hcheck s p h)
  else 1

noncomputable def expansionSimulation (logical expanded : Array Row) (mapping : Array Nat)
    (hcheck : expansionCheck logical expanded mapping = true) (hne : 0 < logical.size) :
    SegmentSimulation (system logical) (system expanded) where
  Rel := ExpansionRel logical mapping
  initial := expansion_initial logical expanded mapping hcheck hne
  duration := expansionDuration logical expanded mapping hcheck
  positive := by
    intro s p h
    have hs := Classical.choose_spec (expansion_local_progress logical expanded mapping hcheck s p h)
    simp only [expansionDuration,dif_pos h]
    exact hs.1
  next := by
    intro s p h
    have hs := Classical.choose_spec (expansion_local_progress logical expanded mapping hcheck s p h)
    simp only [expansionDuration,dif_pos h]
    exact hs.2.1
  event_iff := by
    intro s p h
    have hs := Classical.choose_spec (expansion_local_progress logical expanded mapping hcheck s p h)
    simp only [expansionDuration,dif_pos h]
    exact hs.2.2.1
  event_unique := by
    intro s p h j k hj hk hjbeep hkbeep
    have hs := Classical.choose_spec (expansion_local_progress logical expanded mapping hcheck s p h)
    simp only [expansionDuration,dif_pos h] at hj hk
    exact hs.2.2.2 j k hj hk hjbeep hkbeep

noncomputable def expansionRefinement (logical expanded : Array Row) (mapping : Array Nat)
    (hcheck : expansionCheck logical expanded mapping = true) (hne : 0 < logical.size) :
    EventRefinement (system logical) (system expanded) :=
  (expansionSimulation logical expanded mapping hcheck hne).toEventRefinement

end Shared.PNP.Record285.OwnershipCore
