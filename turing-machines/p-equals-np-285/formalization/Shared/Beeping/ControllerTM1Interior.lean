import Shared.Beeping.ControllerTM1Progress

/-! Isolate the scan/return part of the TM2-to-TM1 emulator. Normal labels
are macrostep boundaries; the restricted transition function stops at them. -/
namespace Shared.Beeping.ControllerTM1Interior
open Turing Turing.PartrecToTM2 Turing.ToPartrec
open Shared.Beeping.ControllerTM2Loop Shared.Beeping.ControllerTM1Progress
open Shared.Beeping.ComparisonTM2 Shared.ComplexityBridge.TM2Symbols
open TM2to1 StateTransition Function

def micro (c : Code) (x : Conf1) : Option Conf1 :=
  match x.l with
  | some (.go _ _ _) | some (.ret _) => TM1.step (program1 c) x
  | _ => none

theorem go_walk (c : Code) {k : K'} (o : StAct K' (fun _ => Γ') (Option Γ') k)
    (q : TM2.Stmt (fun _ : K' => Γ') Label (Option Γ')) (v : Option Γ')
    {S : List Γ'} {L : ListBlank (∀ _ : K', Option Γ')}
    (hL : L.map (proj k) = ListBlank.mk (S.map some).reverse) (n : Nat) (H : n ≤ S.length) :
    Reaches₀ (micro c) ⟨some (.go k o q),v,Tape.mk' ∅ (addBottom L)⟩
      ⟨some (.go k o q),v,(Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply (ih (le_of_lt H)).tail
    rw [iterate_succ_apply']
    simp only [micro,TM1.step,TM1.stepAux,program1,TM2to1.tr,Tape.mk'_nth_nat,
      Tape.move_right_n_head,addBottom_nth_snd,Option.mem_def]
    rw [stk_nth_val _ hL,List.getElem?_eq_getElem]
    · rfl
    · rwa [List.length_reverse]

theorem ret_walk (c : Code) {q : TM2.Stmt (fun _ : K' => Γ') Label (Option Γ')}
    {v : Option Γ'} {L : ListBlank (∀ _ : K', Option Γ')} (n : Nat) :
    Reaches₀ (micro c) ⟨some (.ret q),v,(Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩
      ⟨some (.ret q),v,Tape.mk' ∅ (addBottom L)⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine Reaches₀.head ?_ ih
    simp only [micro,Option.mem_def,TM1.step]
    rw [Option.some_inj,program1,TM2to1.tr,TM1.stepAux,Tape.move_right_n_head,Tape.mk'_nth_nat,
      addBottom_nth_succ_fst,TM1.stepAux,iterate_succ',Function.comp_apply,Tape.move_right_left]
    rfl

theorem respects_aux (c : Code)
    {q : TM2.Stmt (fun _ : K' => Γ') Label (Option Γ')}
    {v : Option Γ'} {T : ListBlank (∀ _ : K', Option Γ')} {k : K'}
    {S : ∀ _ : K', List Γ'}
    (hT : ∀ k, ListBlank.map (proj k) T = ListBlank.mk ((S k).map some).reverse)
    (o : StAct K' (fun _ => Γ') (Option Γ') k)
    (IH : ∀ {v : Option Γ'} {S : ∀ _ : K', List Γ'}
      {T : ListBlank (∀ _ : K', Option Γ')},
      (∀ k, ListBlank.map (proj k) T = ListBlank.mk ((S k).map some).reverse) →
      ∃ b, TrCfg (TM2.stepAux q v S) b ∧
        Reaches (micro c) (TM1.stepAux (trNormal q) v (Tape.mk' ∅ (addBottom T))) b) :
    ∃ b, TrCfg (TM2.stepAux (stRun o q) v S) b ∧ Reaches (micro c)
      (TM1.stepAux (trNormal (stRun o q)) v (Tape.mk' ∅ (addBottom T))) b := by
  simp only [trNormal_run,step_run]
  have hgo := go_walk c o q v (hT k) _ le_rfl
  obtain ⟨T',hT',hrun⟩ := tr_respects_aux₂ (Λ := Label) hT o
  have hh := hgo.tail' rfl
  rw [program1,TM2to1.tr,TM1.stepAux,Tape.move_right_n_head,Tape.mk'_nth_nat,addBottom_nth_snd,
    stk_nth_val _ (hT k),List.getElem?_eq_none (le_of_eq List.length_reverse),
    Option.isNone,cond,hrun,TM1.stepAux] at hh
  obtain ⟨b,hb,hpath⟩ := IH hT'
  refine ⟨b,hb,(hh.to₀.trans (ret_walk c _) b (Relation.TransGen.head' rfl ?_)).to_reflTransGen⟩
  rw [program1,TM2to1.tr,TM1.stepAux,Tape.mk'_head,addBottom_head_fst]
  exact hpath

/-- A translated statement reaches its matching TM2 result while all steps
after the first use only the scan/return transition relation. -/
theorem restricted_statement (c : Code)
    (s : TM2.Stmt (fun _ : K' => Γ') Label (Option Γ'))
    {v : Option Γ'} {S : ∀ _ : K', List Γ'} {L : ListBlank (∀ _ : K', Option Γ')}
    (hL : ∀ k, L.map (proj k) = ListBlank.mk ((S k).map some).reverse) :
    ∃ b, TrCfg (TM2.stepAux s v S) b ∧
      Reaches (micro c) (TM1.stepAux (trNormal s) v (Tape.mk' ∅ (addBottom L))) b := by
  induction s using stmtStRec generalizing v S L hL with
  | run k op q IH => exact respects_aux c hL op @IH
  | load a q IH => exact IH hL
  | branch p q₁ q₂ IH₁ IH₂ =>
    unfold TM2.stepAux TM2to1.trNormal TM1.stepAux
    beta_reduce
    cases p v <;> [exact IH₂ hL; exact IH₁ hL]
  | goto => exact ⟨_,⟨_,hL⟩,Relation.ReflTransGen.refl⟩
  | halt => exact ⟨_,⟨_,hL⟩,Relation.ReflTransGen.refl⟩

theorem restricted_segment (c : Code) (x : Conf) (y : Conf1) (h : Rel x y) :
    ∃ first last, TM1.step (program1 c) y = some first ∧
      Rel ((system c).step x).1 last ∧ Reaches (micro c) first last := by
  obtain ⟨hrel,hlive⟩ := h
  cases hrel with
  | @mk l v S L hL =>
    cases l with
    | none => simp at hlive
    | some q =>
      obtain ⟨b,hb,hpath⟩ := restricted_statement c (program c q) hL
      refine ⟨_,b,rfl,?_,hpath⟩
      constructor
      · simpa [system,TM2.step] using hb
      · simpa [system,TM2.step] using program_step_live c q v S

theorem micro_step_real (c : Code) (x y : Conf1) (h : micro c x = some y) :
    TM1.step (program1 c) x = some y := by
  cases hx : x.l with
  | none => simp [micro,hx] at h
  | some q =>
    cases q with
    | normal q => simp [micro,hx] at h
    | go k op s => simpa [micro,hx] using h
    | ret s => simpa [micro,hx] using h

theorem micro_step_silent (c : Code) (x y : Conf1) (h : micro c x = some y) :
    ((system1 c).step x).2 = false := by
  cases hx : x.l with
  | none => simp [micro,hx] at h
  | some q =>
    cases q with
    | normal q => simp [micro,hx] at h
    | go k op s => simp [system1,hx,flag1]
    | ret s => simp [system1,hx,flag1]

theorem micro_run_real (c : Code) (x y : Conf1) (d : Nat)
    (h : runSteps (micro c) d x = some y) :
    runSteps (TM1.step (program1 c)) d x = some y := by
  induction d generalizing y with
  | zero => exact h
  | succ d ih =>
    change (runSteps (micro c) d x).bind (micro c) = some y at h
    cases hr : runSteps (micro c) d x with
    | none => simp [hr] at h
    | some mid =>
      have hm : micro c mid = some y := by simpa [hr] using h
      change (runSteps (TM1.step (program1 c)) d x).bind (TM1.step (program1 c)) = some y
      rw [ih mid hr]
      exact micro_step_real c mid y hm

/-- Every interior transition of the least matching segment is a scan or
return transition. -/
theorem interior_micro_live (c : Code) (x : Conf) (y : Conf1) (h : Rel x y)
    (j : Nat) (hj : 0 < j) (hd : j < duration c x y) :
    ∃ z, micro c ((system1 c).advance y j) = some z := by
  classical
  obtain ⟨first,last,hfirst,hlast,hpath⟩ := restricted_segment c x y h
  obtain ⟨n,hn⟩ := reaches_runSteps hpath
  have hreal : runSteps (TM1.step (program1 c)) n first = some last :=
    micro_run_real c first last n hn
  have hwhole : runSteps (TM1.step (program1 c)) (n+1) y = some last := by
    rw [show n+1 = 1+n by omega,Shared.Codes.TM2Program.runSteps_add]
    change (TM1.step (program1 c) y).bind _ = _
    rw [hfirst]
    exact hreal
  have hmin : duration c x y ≤ n+1 := by
    unfold duration
    rw [dif_pos h]
    exact Nat.find_min' (local_progress c x y h) ⟨last,by omega,hwhole,hlast⟩
  let k := j-1
  have hk : k < n := by omega
  obtain ⟨mid,hm⟩ := ComparisonCommit.run_prefix (micro c) first last n k hn (by omega)
  obtain ⟨next,hnext⟩ := ComparisonCommit.run_prefix (micro c) first last n (k+1) hn (by omega)
  have hstep : micro c mid = some next := by
    change (runSteps (micro c) k first).bind (micro c) = some next at hnext
    simpa [hm] using hnext
  have hmreal := micro_run_real c first mid k hm
  have hprefix : runSteps (TM1.step (program1 c)) (1+k) y = some mid := by
    rw [Shared.Codes.TM2Program.runSteps_add]
    change (TM1.step (program1 c) y).bind _ = _
    rw [hfirst]
    exact hmreal
  have ha := advance_run (TM1.step (program1 c)) initial1 (fun a => a.l.elim false flag1)
    y mid (1+k) hprefix
  change (system1 c).advance y (1+k) = mid at ha
  have hjk : j = 1+k := by dsimp [k]; omega
  rw [hjk,ha]
  exact ⟨next,hstep⟩

/-- The least matching TM1 segment contains no marked label after its
initial boundary. This discharges the event-isolation obligation. -/
theorem interior_silent (c : Code) : InteriorSilent c := by
  intro x y h j hj hd
  obtain ⟨z,hz⟩ := interior_micro_live c x y h j hj hd
  unfold EventSystem.BeepFrom
  rw [micro_step_silent c _ z hz]
  decide

theorem run_interior_silent (c : Code) : RunInteriorSilent c :=
  interior_implies_run c (interior_silent c)

/-- The library translation preserves the controller's entire event stream
up to finite positive stuttering. -/
noncomputable def refinement (c : Code) : EventRefinement (system c) (system1 c) :=
  (simulation c (interior_silent c)).toEventRefinement

theorem pnp (c : Code) (hc : ControllerTM2Refinement.CodeCorrect Shared.PNP.TM2Candidate.compareSAT c) :
    (system1 c).EventuallySilent ↔
      ∃ candidate : Shared.Codes.TM2Candidate.Candidate, ∀ x,
        Shared.Codes.TM2CheckedCandidate.evaluate candidate x =
          some (Shared.ComplexityBridge.CNF.sat x) :=
  pnp_conditional c hc (run_interior_silent c)

theorem npconp (c : Code) (hc : ControllerTM2Refinement.CodeCorrect Shared.NPCONP.TM2Verifier.compare c) :
    (system1 c).EventuallySilent ↔
      ∃ verifier : Shared.NPCONP.TM2Verifier.Verifier, ∀ x,
        Shared.NPCONP.TM2Verifier.test verifier x = true :=
  npconp_conditional c hc (run_interior_silent c)

theorem pnp_exists : ∃ c : Code,
    (∀ t, ((system1 c).run t).l ≠ none) ∧
    ((system1 c).EventuallySilent ↔
      ∃ candidate : Shared.Codes.TM2Candidate.Candidate, ∀ x,
        Shared.Codes.TM2CheckedCandidate.evaluate candidate x =
          some (Shared.ComplexityBridge.CNF.sat x)) := by
  obtain ⟨c,hc⟩ := Shared.Beeping.ControllerCode.has_update_code
    Shared.PNP.TM2Candidate.compareSAT Shared.PNP.TM2Candidate.compareSAT_computable
  exact ⟨c,run_never_halts c,pnp c hc⟩

theorem npconp_exists : ∃ c : Code,
    (∀ t, ((system1 c).run t).l ≠ none) ∧
    ((system1 c).EventuallySilent ↔
      ∃ verifier : Shared.NPCONP.TM2Verifier.Verifier, ∀ x,
        Shared.NPCONP.TM2Verifier.test verifier x = true) := by
  obtain ⟨c,hc⟩ := Shared.Beeping.ControllerCode.has_update_code
    Shared.NPCONP.TM2Verifier.compare Shared.NPCONP.TM2Verifier.compare_computable
  exact ⟨c,run_never_halts c,npconp c hc⟩

end Shared.Beeping.ControllerTM1Interior
