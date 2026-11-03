import Shared.PNP.Record285.ProducerGrammar

/-! Operational soundness of the producer grammar's finite graph checker. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.ProducerGrammar
open Shared.Beeping
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.OwnershipCore

structure State where
  pc : List Bool
  bank : Nat → Nat

def step (g : Data) (s : State) : State × Bool :=
  match walk g g.root s.pc with
  | none => (s,false)
  | some e =>
    let a := action e
    let branch := a.map (fun x => observe x s.bank) |>.getD false
    let next := (successor g e s.pc branch).getD s.pc
    let bank := a.map (fun x => update x s.bank) |>.getD s.bank
    (⟨next,bank⟩,decide (e = .beep))

def system (g : Data) : EventSystem State := ⟨⟨[false],fun _ => 0⟩,step g⟩

theorem admin_action (e : Edge) (h : administrative e = true) : action e = none := by
  cases e <;> simp_all [administrative,action]

theorem admin_silent (e : Edge) (h : administrative e = true) : decide (e = .beep) = false := by
  cases e <;> simp_all [administrative]

theorem action_event (e : Edge) (a : Action) (h : action e = some a) :
    decide (e = .beep) = decide (a = .beep) := by
  cases e <;> simp_all [action] <;> subst a <;> simp

theorem advance_after_one (g : Data) (s : State) (n : Nat) :
    (system g).advance s (n+1) = (system g).advance ((step g s).1) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((system g).step ((system g).advance s (n+1))).1 = _
    rw [ih]
    rfl

theorem settle_sound (g : Data) (fuel : Nat) (pc target : List Bool) (bank : Nat → Nat)
    (h : settle g fuel pc = some target) :
    ∃ k, k < fuel ∧ (system g).advance ⟨pc,bank⟩ k = ⟨target,bank⟩ ∧
      ∀ j, j < k → ¬ (system g).BeepFrom ⟨pc,bank⟩ j := by
  induction fuel generalizing pc with
  | zero => simp [settle] at h
  | succ fuel ih =>
    cases hw : walk g g.root pc with
    | none => simp [settle,hw] at h
    | some e =>
      cases ha : administrative e with
      | false =>
        have he : target = pc := by simpa [settle,hw,ha] using h.symm
        subst target
        exact ⟨0,by omega,rfl,by simp⟩
      | true =>
        cases hn : successor g e pc false with
        | none => simp [settle,hw,ha,hn] at h
        | some mid =>
          have hs : settle g fuel mid = some target := by simpa [settle,hw,ha,hn] using h
          obtain ⟨k,hk,hadv,hquiet⟩ := ih mid hs
          have hstep : step g ⟨pc,bank⟩ = (⟨mid,bank⟩,false) := by
            simp [step,hw,admin_action e ha,admin_silent e ha,hn]
          refine ⟨k+1,by omega,?_,?_⟩
          · rw [advance_after_one,hstep]
            exact hadv
          · intro j hj hb
            cases j with
            | zero => simp [EventSystem.BeepFrom,EventSystem.advance,system,hstep] at hb
            | succ j =>
              apply hquiet j (by omega)
              change (step g ((system g).advance ⟨pc,bank⟩ (j+1))).2 = true at hb
              rw [advance_after_one,hstep] at hb
              exact hb

theorem checkRow_sound (g : Data) (rows : Array OwnershipCore.Row) (positions : Array (List Bool))
    (i : Nat) (row : OwnershipCore.Row) (pc : List Bool)
    (hr : rows[i]? = some row) (hp : positions[i]? = some pc)
    (h : checkRow g rows positions i = true) :
    ∃ e no yes, walk g g.root pc = some e ∧ action e = some row.action ∧
      positions[row.no]? = some no ∧ positions[row.yes]? = some yes ∧
      (successor g e pc false).bind (settle g 32) = some no ∧
      (successor g e pc true).bind (settle g 32) = some yes := by
  simp only [checkRow,hr,hp] at h
  cases he : walk g g.root pc with
  | none => simp [he] at h
  | some e =>
    cases hn : positions[row.no]? with
    | none => simp [he,hn] at h
    | some no =>
      cases hy : positions[row.yes]? with
      | none => simp [he,hn,hy] at h
      | some yes =>
        simp only [he,hn,hy,Bool.and_eq_true_iff,decide_eq_true_eq] at h
        exact ⟨e,no,yes,rfl,h.1.1,rfl,rfl,h.1.2,h.2⟩

def Rel (rows : Array OwnershipCore.Row) (positions : Array (List Bool))
    (s : OwnershipCore.State) (t : State) : Prop :=
  positions[s.index]? = some t.pc ∧ s.bank = t.bank ∧ s.index < rows.size

theorem check_sizes (g : Data) (rows : Array OwnershipCore.Row) (positions : Array (List Bool))
    (h : check g rows positions = true) :
    rows.size = positions.size ∧ positions[0]? = some [false] := by
  simp only [check,Bool.and_eq_true_iff,decide_eq_true_eq] at h
  exact h.1

theorem initial_related (g : Data) (rows : Array OwnershipCore.Row) (positions : Array (List Bool))
    (h : check g rows positions = true) : Rel rows positions (OwnershipCore.system rows).initial (system g).initial := by
  obtain ⟨hs,hp⟩ := check_sizes g rows positions h
  have hb : 0 < positions.size := (Array.getElem?_eq_some_iff.mp hp).1
  exact ⟨hp,rfl,by change 0 < rows.size; omega⟩

theorem primitive_then_settle (g : Data) (e : Edge) (a : Action) (pc mid target : List Bool)
    (bank : Nat → Nat) (hw : walk g g.root pc = some e) (ha : action e = some a)
    (hn : successor g e pc (observe a bank) = some mid)
    (hs : settle g 32 mid = some target) :
    ∃ k, k < 32 ∧ (system g).advance ⟨pc,bank⟩ (k+1) = ⟨target,update a bank⟩ ∧
      (step g ⟨pc,bank⟩).2 = decide (a = .beep) ∧
      ∀ j, j < k → ¬ (system g).BeepFrom ⟨pc,bank⟩ (j+1) := by
  have hstep : step g ⟨pc,bank⟩ = (⟨mid,update a bank⟩,decide (a = .beep)) := by
    simp [step,hw,ha,hn,action_event e a ha]
  obtain ⟨k,hk,hadv,hquiet⟩ := settle_sound g 32 mid target (update a bank) hs
  refine ⟨k,hk,?_,?_,?_⟩
  · rw [advance_after_one,hstep]; exact hadv
  · simp [hstep]
  · intro j hj
    have hq := hquiet j hj
    change ¬ (step g ((system g).advance ⟨pc,bank⟩ (j+1))).2 = true
    rw [advance_after_one,hstep]
    exact hq

theorem local_progress (g : Data) (rows : Array OwnershipCore.Row) (positions : Array (List Bool))
    (hcheck : check g rows positions = true) (s : OwnershipCore.State) (t : State)
    (hrel : Rel rows positions s t) :
    ∃ k, k < 32 ∧ Rel rows positions (OwnershipCore.step rows s).1 ((system g).advance t (k+1)) ∧
      (OwnershipCore.step rows s).2 = (step g t).2 ∧
      ∀ j, j < k → ¬ (system g).BeepFrom t (j+1) := by
  obtain ⟨hp,hbank,hi⟩ := hrel
  obtain ⟨row,hr⟩ : ∃ row, rows[s.index]? = some row := ⟨rows[s.index],by simp⟩
  obtain ⟨e,no,yes,hw,ha,hno,hyes,hno',hyes'⟩ :=
    checkRow_sound g rows positions s.index row t.pc hr hp (check_at g rows positions hcheck s.index hi)
  let b := observe row.action s.bank
  let index := if b then row.yes else row.no
  let target := if b then yes else no
  have hpos : positions[index]? = some target := by
    dsimp [index,target]; cases b <;> simp_all
  have hbound : index < rows.size := by
    have hn := (Array.getElem?_eq_some_iff.mp hpos).1
    have hs := (check_sizes g rows positions hcheck).1
    omega
  have hbind : (successor g e t.pc b).bind (settle g 32) = some target := by
    dsimp [target]; cases b <;> simp_all
  cases hn : successor g e t.pc b with
  | none => simp [hn] at hbind
  | some mid =>
    have hsettle : settle g 32 mid = some target := by simpa [hn] using hbind
    have hnext : successor g e t.pc (observe row.action t.bank) = some mid := by
      simpa [b,hbank] using hn
    obtain ⟨k,hk,hadv,hevent,hquiet⟩ := primitive_then_settle g e row.action t.pc mid target t.bank hw ha hnext hsettle
    have hstep : OwnershipCore.step rows s = (⟨index,update row.action s.bank⟩,decide (row.action = .beep)) := by
      simp [OwnershipCore.step,hr,index,b]
    refine ⟨k,hk,?_,?_,hquiet⟩
    · rw [hstep]
      cases t with
      | mk pc bank =>
        change Rel rows positions ⟨index,update row.action s.bank⟩ ((system g).advance ⟨pc,bank⟩ (k+1))
        rw [hadv]
        exact ⟨hpos,by simp [hbank],hbound⟩
    · rw [hstep]
      exact hevent.symm

theorem quiet_only_first (g : Data) (t : State) (k j : Nat)
    (hq : ∀ n, n < k → ¬ (system g).BeepFrom t (n+1))
    (hj : j < k+1) (he : (system g).BeepFrom t j) : j = 0 := by
  cases j with
  | zero => rfl
  | succ j =>
    exfalso
    apply hq j (by omega)
    simpa using he

noncomputable def duration (g : Data) (rows : Array OwnershipCore.Row) (positions : Array (List Bool))
    (hcheck : check g rows positions = true) (s : OwnershipCore.State) (t : State) : Nat := by
  classical
  exact if h : Rel rows positions s t then Classical.choose (local_progress g rows positions hcheck s t h) + 1 else 1

/-- Every graph action has a positive, finite realization, with exactly its
one possible event and a complete equality of register banks. -/
noncomputable def simulation (g : Data) (rows : Array OwnershipCore.Row) (positions : Array (List Bool))
    (hcheck : check g rows positions = true) : SegmentSimulation (OwnershipCore.system rows) (system g) where
  Rel := Rel rows positions
  initial := initial_related g rows positions hcheck
  duration := duration g rows positions hcheck
  positive := by
    intro s t h
    simp only [duration,dif_pos h]
    omega
  next := by
    intro s t h
    have hp := Classical.choose_spec (local_progress g rows positions hcheck s t h)
    simp only [duration,dif_pos h]
    exact hp.2.1
  event_iff := by
    intro s t h
    have hp := Classical.choose_spec (local_progress g rows positions hcheck s t h)
    simp only [duration,dif_pos h]
    constructor
    · intro he
      refine ⟨0,by omega,?_⟩
      change (step g t).2 = true
      change (OwnershipCore.step rows s).2 = true at he
      exact hp.2.2.1.symm.trans he
    · rintro ⟨j,hj,he⟩
      have hz := quiet_only_first g t _ j hp.2.2.2 hj he
      subst j
      change (step g t).2 = true at he
      change (OwnershipCore.step rows s).2 = true
      exact hp.2.2.1.trans he
  event_unique := by
    intro s t h j k hj hk hjbeep hkbeep
    have hp := Classical.choose_spec (local_progress g rows positions hcheck s t h)
    simp only [duration,dif_pos h] at hj hk
    have hj0 := quiet_only_first g t _ j hp.2.2.2 hj hjbeep
    have hk0 := quiet_only_first g t _ k hp.2.2.2 hk hkbeep
    omega

end Shared.PNP.Record285.ProducerGrammar
