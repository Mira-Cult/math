import Shared.Codes.TM2ProgramHalt
import Shared.ComplexityBridge.TM2GenericStackBound

/-! Quantitative translation of arbitrary TM2 statements to TM1 blocks.
No finiteness of internal stack alphabets is required. -/
namespace Shared.ComplexityBridge.TM2GeneralTM1Costs
open Turing TM2to1 StateTransition Function Shared.Codes.TM2Program Shared.ComplexityBridge.TM2Symbols

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K]

abbrev Conf1 := TM1.Cfg (TM2to1.Γ' K Γ) (TM2to1.Λ' K Γ Λ σ) σ

def micro (M : Λ → TM2.Stmt Γ Λ σ) (x : Conf1 (K := K) (Γ := Γ) (Λ := Λ) (σ := σ)) : Option (Conf1 (K := K) (Γ := Γ) (Λ := Λ) (σ := σ)) :=
  match x.l with
  | some (.go _ _ _) | some (.ret _) => TM1.step (TM2to1.tr M) x
  | _ => none

theorem micro_step_real (M : Λ → TM2.Stmt Γ Λ σ) (x y : Conf1) (h : micro M x = some y) :
    TM1.step (TM2to1.tr M) x = some y := by
  cases hx : x.l with
  | none => simp [micro,hx] at h
  | some q => cases q <;> simpa [micro,hx] using h

theorem micro_run_real (M : Λ → TM2.Stmt Γ Λ σ) (x y : Conf1) (d : Nat)
    (h : runSteps (micro M) d x = some y) :
    runSteps (TM1.step (TM2to1.tr M)) d x = some y := by
  induction d generalizing y with
  | zero => exact h
  | succ d ih =>
    change (runSteps (micro M) d x).bind (micro M) = some y at h
    cases hr : runSteps (micro M) d x with
    | none => simp [hr] at h
    | some mid =>
      have hm : micro M mid = some y := by simpa [hr] using h
      change (runSteps (TM1.step (TM2to1.tr M)) d x).bind (TM1.step (TM2to1.tr M)) = some y
      rw [ih mid hr]
      exact micro_step_real M mid y hm

theorem go_scan (M : Λ → TM2.Stmt Γ Λ σ) {k : K} (o : StAct K Γ (σ) k)
    (q : TM2.Stmt Γ Λ (σ)) (v : σ)
    {S : List (Γ k)} {L : ListBlank ((i : K) → Option (Γ i))}
    (hL : L.map (proj k) = ListBlank.mk (S.map some).reverse) (n : Nat) (H : n ≤ S.length) :
    runSteps (micro M) n ⟨some (.go k o q),v,Tape.mk' ∅ (addBottom L)⟩ =
      some ⟨some (.go k o q),v,(Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (runSteps (micro M) n _).bind (micro M) = _
    rw [ih (le_of_lt H)]
    change micro M ⟨some (.go k o q),v,(Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ = _
    rw [iterate_succ_apply']
    simp only [micro,TM1.step,TM1.stepAux,TM2to1.tr,Tape.mk'_nth_nat,
      Tape.move_right_n_head,addBottom_nth_snd,Option.some.injEq]
    rw [stk_nth_val _ hL,List.getElem?_eq_getElem]
    · rfl
    · rwa [List.length_reverse]

theorem ret_scan (M : Λ → TM2.Stmt Γ Λ σ) {q : TM2.Stmt Γ Λ (σ)}
    {v : σ} {L : ListBlank ((i : K) → Option (Γ i))} (n : Nat) :
    runSteps (micro M) n ⟨some (.ret q),v,(Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ =
      some ⟨some (.ret q),v,Tape.mk' ∅ (addBottom L)⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show n+1 = 1+n by omega,runSteps_add]
    simp only [show 1+n = n+1 by omega,runSteps,Option.bind_some]
    have hstep : micro M ⟨some (.ret q),v,(Tape.move Dir.right)^[n+1] (Tape.mk' ∅ (addBottom L))⟩ =
        some ⟨some (.ret q),v,(Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
      simp only [micro,TM1.step]
      rw [Option.some_inj,TM2to1.tr,TM1.stepAux,Tape.move_right_n_head,Tape.mk'_nth_nat,
        addBottom_nth_succ_fst,TM1.stepAux,iterate_succ',Function.comp_apply,Tape.move_right_left]
      rfl
    rw [hstep]
    exact ih

/-- One stack operation scans out to the old top, executes the operation,
returns from the new top, and dispatches the continuation. Its exact cost is
old length + 1 + new length + 1 TM1 blocks. -/
theorem stack_action (M : Λ → TM2.Stmt Γ Λ σ)
    {q : TM2.Stmt Γ Λ (σ)}
    {v : σ} {T : ListBlank ((i : K) → Option (Γ i))} {k : K}
    {S : (i : K) → List (Γ i)}
    (hT : ∀ k, ListBlank.map (proj k) T = ListBlank.mk ((S k).map some).reverse)
    (o : StAct K Γ (σ) k) :
    ∃ T' : ListBlank ((i : K) → Option (Γ i)),
      (∀ k', T'.map (proj k') =
        ListBlank.mk (((update S k (stWrite v (S k) o)) k').map some).reverse) ∧
      runSteps (micro M) ((S k).length + 1 +
        ((update S k (stWrite v (S k) o)) k).length + 1)
        ⟨some (.go k o q),v,Tape.mk' ∅ (addBottom T)⟩ =
          some (TM1.stepAux (trNormal q) (stVar v (S k) o) (Tape.mk' ∅ (addBottom T'))) := by
  obtain ⟨T',hT',hrun⟩ := tr_respects_aux₂ (Λ := Λ)
    (q := TM1.Stmt.goto (fun _ _ => .ret q)) (v := v) hT o
  refine ⟨T',hT',?_⟩
  let n := (S k).length
  let n' := ((update S k (stWrite v (S k) o)) k).length
  let v' := stVar v (S k) o
  have htop : micro M ⟨some (.go k o q),v,(Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom T))⟩ =
      some ⟨some (.ret q),v',(Tape.move Dir.right)^[n'] (Tape.mk' ∅ (addBottom T'))⟩ := by
    dsimp [n,n',v']
    simp only [micro,TM1.step,TM2to1.tr,TM1.stepAux,Tape.move_right_n_head,Tape.mk'_nth_nat,
      addBottom_nth_snd,stk_nth_val _ (hT k),List.getElem?_eq_none (le_of_eq List.length_reverse),
      Option.isNone,cond]
    rw [hrun]
    rfl
  have hbottom : micro M ⟨some (.ret q),v',Tape.mk' ∅ (addBottom T')⟩ =
      some (TM1.stepAux (trNormal q) v' (Tape.mk' ∅ (addBottom T'))) := by
    simp [micro,TM1.step,TM2to1.tr,TM1.stepAux,Tape.mk'_head,addBottom_head_fst]
  change runSteps (micro M) (n+1+n'+1) _ = _
  rw [show n+1+n'+1 = n+(1+(n'+1)) by omega,runSteps_add]
  rw [go_scan M o q v (hT k) n (by dsimp [n]; exact le_rfl)]
  simp only [Option.bind_some]
  rw [runSteps_add]
  simp only [runSteps,Option.bind_some]
  rw [htop]
  simp only [Option.bind_some]
  rw [ret_scan]
  exact hbottom

theorem stack_action_cost_bound {k : K} (v : σ) (S : (i : K) → List (Γ i))
    (o : StAct K Γ (σ) k) :
    (S k).length + 1 + ((update S k (stWrite v (S k) o)) k).length + 1 ≤
      2 * (S k).length + 3 := by
  rw [Function.update_self]
  cases o with
  | push f => simp [stWrite]; omega
  | peek f => simp [stWrite]; omega
  | pop f =>
    cases h : S k <;> simp [stWrite,h]
    omega

/-- The exact stack-action segment has a linear upper bound in the old
stack length; execution of the continuation is a separate segment. -/
theorem stack_action_bounded (M : Λ → TM2.Stmt Γ Λ σ)
    {q : TM2.Stmt Γ Λ (σ)}
    {v : σ} {T : ListBlank ((i : K) → Option (Γ i))} {k : K}
    {S : (i : K) → List (Γ i)}
    (hT : ∀ k, ListBlank.map (proj k) T = ListBlank.mk ((S k).map some).reverse)
    (o : StAct K Γ (σ) k) :
    ∃ T' : ListBlank ((i : K) → Option (Γ i)), ∃ d,
      d ≤ 2*(S k).length+3 ∧
      (∀ k', T'.map (proj k') =
        ListBlank.mk (((update S k (stWrite v (S k) o)) k').map some).reverse) ∧
      runSteps (micro M) d ⟨some (.go k o q),v,Tape.mk' ∅ (addBottom T)⟩ =
        some (TM1.stepAux (trNormal q) (stVar v (S k) o) (Tape.mk' ∅ (addBottom T'))) := by
  obtain ⟨T',hT',hrun⟩ := stack_action M hT o
  exact ⟨T',_,stack_action_cost_bound v S o,hT',hrun⟩


/-- Maximum number of stack operations along a statement branch. -/
def actions : TM2.Stmt Γ Λ σ → Nat
  | .push _ _ q | .peek _ _ q | .pop _ _ q => 1 + actions q
  | .load _ q => actions q
  | .branch _ q₁ q₂ => max (actions q₁) (actions q₂)
  | .goto _ | .halt => 0

def blockCost (N a : Nat) : Nat := a * (2*(N+a)+3)

theorem blockCost_mono (N a b : Nat) (h : a ≤ b) : blockCost N a ≤ blockCost N b := by
  apply Nat.mul_le_mul h
  omega

theorem stack_after_bound {k : K} (o : StAct K Γ (σ) k)
    (v : σ) (S : (i : K) → List (Γ i)) (N : Nat)
    (hS : ∀ i, (S i).length ≤ N) :
    ∀ i, ((update S k (stWrite v (S k) o)) i).length ≤ N+1 := by
  intro i
  by_cases h : i = k
  · subst i
    rw [Function.update_self]
    have hk := hS k
    cases o with
    | push f => simp [stWrite]; omega
    | peek f => simp [stWrite]; omega
    | pop f =>
      cases hs : S k <;> simp [stWrite,hs] at *
      omega
  · rw [Function.update_of_ne h]
    have hi := hS i
    omega

/-- Starting just after the boundary transition, the rest of a TM2 statement
runs in at most `blockCost N (actions s)` TM1 blocks whenever all source
stacks initially have length at most `N`. -/
theorem statement_bounded (M : Λ → TM2.Stmt Γ Λ σ) (s : TM2.Stmt Γ Λ σ)
    {v : σ} {S : (i : K) → List (Γ i)} {T : ListBlank ((i : K) → Option (Γ i))}
    (N : Nat) (hS : ∀ k, (S k).length ≤ N)
    (hT : ∀ k, T.map (proj k) = ListBlank.mk ((S k).map some).reverse) :
    ∃ d z, d ≤ blockCost N (actions s) ∧ TrCfg (TM2.stepAux s v S) z ∧
      runSteps (micro M) d (TM1.stepAux (trNormal s) v (Tape.mk' ∅ (addBottom T))) = some z := by
  induction s using stmtStRec generalizing v S T N with
  | run k o q ih =>
    have hS' := stack_after_bound o v S N hS
    obtain ⟨T',d,hd,hT',hfirst⟩ := stack_action_bounded M hT o
    obtain ⟨e,z,he,hz,hrest⟩ := ih (N+1) hS' hT'
    refine ⟨d+e,z,?_,?_,?_⟩
    · have hd' : d ≤ 2*N+3 := by have hh := hS k; omega
      have heq : 2*((N+1)+actions q)+3 = 2*(N+(1+actions q))+3 := by omega
      change e ≤ actions q * (2*((N+1)+actions q)+3) at he
      rw [heq] at he
      have ha : actions (stRun o q) = 1+actions q := by cases o <;> rfl
      rw [ha]
      change d+e ≤ (1+actions q) * (2*(N+(1+actions q))+3)
      rw [Nat.add_mul]
      simp only [one_mul]
      omega
    · simpa [step_run] using hz
    · simp only [trNormal_run,TM1.stepAux]
      rw [runSteps_add,hfirst]
      exact hrest
  | load f q ih =>
    simpa [TM2.stepAux,TM2to1.trNormal,TM1.stepAux,actions] using
      (ih N hS hT (v := f v))
  | branch f q₁ q₂ ih₁ ih₂ =>
    cases hf : f v with
    | false =>
      obtain ⟨d,z,hd,hz,hr⟩ := ih₂ N hS hT
      refine ⟨d,z,?_,?_,?_⟩
      · exact le_trans hd (blockCost_mono N _ _ (Nat.le_max_right _ _))
      · simpa [TM2.stepAux,hf] using hz
      · simpa [TM2to1.trNormal,TM1.stepAux,hf] using hr
    | true =>
      obtain ⟨d,z,hd,hz,hr⟩ := ih₁ N hS hT
      refine ⟨d,z,?_,?_,?_⟩
      · exact le_trans hd (blockCost_mono N _ _ (Nat.le_max_left _ _))
      · simpa [TM2.stepAux,hf] using hz
      · simpa [TM2to1.trNormal,TM1.stepAux,hf] using hr
  | goto f => exact ⟨0,_,by simp [blockCost,actions],⟨_,hT⟩,rfl⟩
  | halt => exact ⟨0,_,by simp [blockCost,actions],⟨_,hT⟩,rfl⟩


/-- A live source block is simulated by a finite positive segment of the
actual TM1 transition function, ending in a related configuration. -/
theorem one_block_bounded (M : Λ → TM2.Stmt Γ Λ σ)
    (x x' : TM2.Cfg Γ Λ σ) (y : Conf1) (q : Λ) (hq : x.l = some q)
    (hrel : TrCfg x y) (hstep : TM2.step M x = some x') (N : Nat)
    (hS : ∀ k, (x.stk k).length ≤ N) :
    ∃ d z, 0 < d ∧ d ≤ 1 + blockCost N (actions (M q)) ∧
      runSteps (TM1.step (TM2to1.tr M)) d y = some z ∧ TrCfg x' z := by
  cases hrel with
  | @mk l v S L hL =>
    cases l with
    | none => simp at hq
    | some q' =>
      simp only [Option.some.injEq] at hq
      subst q'
      obtain ⟨d,z,hd,hz,hr⟩ := statement_bounded M (M q) N hS hL
      refine ⟨1+d,z,by omega,by omega,?_,?_⟩
      · rw [runSteps_add]
        change (some (TM1.stepAux (trNormal (M q)) v (Tape.mk' ∅ (addBottom L)))).bind _ = _
        exact micro_run_real M _ _ d hr
      · have hx : TM2.stepAux (M q) v S = x' := by simpa [TM2.step] using hstep
        simpa [hx] using hz

open Shared.ComplexityBridge.TM2GenericStackBound

theorem push_le_actions (s : TM2.Stmt Γ Λ σ) : pushBound s ≤ actions s := by
  induction s with
  | push k f s ih => simp [pushBound,actions]; omega
  | peek k f s ih => simp [pushBound,actions]; omega
  | pop k f s ih => simp [pushBound,actions]; omega
  | load f s ih => exact ih
  | branch f s t ihs iht =>
    simp only [pushBound,actions]
    exact max_le (le_trans ihs (le_max_left _ _)) (le_trans iht (le_max_right _ _))
  | goto f => rfl
  | halt => rfl

/-- Maximum source-stack operations in a finite machine's statement table. -/
noncomputable def actionLimit (tm : FinTM2) : Nat := by
  classical
  letI := tm.ΛFin
  exact Finset.univ.sup (fun q : tm.Λ => actions (tm.m q))

theorem actionLimit_bound (tm : FinTM2) (q : tm.Λ) :
    actions (tm.m q) ≤ actionLimit tm := by
  classical
  letI := tm.ΛFin
  exact Finset.le_sup (f := fun q : tm.Λ => actions (tm.m q)) (Finset.mem_univ q)

theorem blockCost_mono_left (a b c : Nat) (h : a ≤ b) :
    blockCost a c ≤ blockCost b c := by
  unfold blockCost
  apply Nat.mul_le_mul_left
  omega

set_option backward.isDefEq.respectTransparency false in
/-- Any successful finite source run, even one ending at halt, is matched by
an actual TM1 run. The bound counts TM1 statement blocks, with `N` bounding
each initial source stack. -/
theorem run_bounded (tm : FinTM2) (n N : Nat) (x x' : tm.Cfg)
    (y : TM1.Cfg (TM2to1.Γ' tm.K tm.Γ) (TM2to1.Λ' tm.K tm.Γ tm.Λ tm.σ) tm.σ)
    (hrel : TrCfg x y) (hS : ∀ k, (x.stk k).length ≤ N)
    (hrun : runSteps tm.step n x = some x') :
    ∃ d z, n ≤ d ∧ d ≤ n * (1 + blockCost (N+n*actionLimit tm) (actionLimit tm)) ∧
      runSteps (TM1.step (TM2to1.tr tm.m)) d y = some z ∧ TrCfg x' z := by
  induction n generalizing x y N with
  | zero =>
    change some x = some x' at hrun
    cases Option.some.inj hrun
    exact ⟨0,y,by simp,by simp,rfl,hrel⟩
  | succ n ih =>
    rw [runSteps_front] at hrun
    change (tm.step x).bind (runSteps tm.step n) = some x' at hrun
    cases hs : tm.step x with
    | none => rw [hs] at hrun; contradiction
    | some mid =>
      rw [hs] at hrun
      have hrest : runSteps tm.step n mid = some x' := hrun
      cases hl : x.l with
      | none => cases x with | mk l v S => simp only at hl; subst l; contradiction
      | some q =>
        obtain ⟨d,z,hdpos,hd,ht,hz⟩ := one_block_bounded tm.m x mid y q hl hrel hs N hS
        have hstack : ∀ k, (mid.stk k).length ≤ N + actionLimit tm := by
          intro k
          cases hx : x with
          | mk l v S =>
            simp only [hx] at hl hs
            subst l
            change some (TM2.stepAux (tm.m q) v S) = some mid at hs
            cases Option.some.inj hs
            have hlen := stepAux_length (tm.m q) v S k
            have ha := push_le_actions (tm.m q)
            have hb := actionLimit_bound tm q
            have hc : (S k).length ≤ N := by simpa [hx] using hS k
            omega
        obtain ⟨e,w,hepos,he,hw,hrel'⟩ := ih (N+actionLimit tm) mid z hz hstack hrest
        refine ⟨d+e,w,by omega,?_,?_,hrel'⟩
        · have hact := actionLimit_bound tm q
          have hmono := blockCost_mono N _ _ hact
          have hmono' := blockCost_mono_left N (N+(n+1)*actionLimit tm) (actionLimit tm) (by omega)
          have heq : N + actionLimit tm + n * actionLimit tm = N + (n+1)*actionLimit tm := by
            simp [Nat.add_mul]; omega
          rw [heq] at he
          rw [Nat.succ_mul]
          omega
        · rw [runSteps_add,ht]
          exact hw

/-- The translated initial tape is the library's stack encoding. This is a
semantic input boundary, not yet a binary serialization or charged loader. -/
def translatedInitial (tm : FinTM2) (bits : List (tm.Γ tm.k₀)) :
    TM1.Cfg (TM2to1.Γ' tm.K tm.Γ) (TM2to1.Λ' tm.K tm.Γ tm.Λ tm.σ) tm.σ := by
  letI : Inhabited tm.Λ := ⟨tm.main⟩
  exact TM1.init (TM2to1.trInit tm.k₀ bits)

theorem initial_related (tm : FinTM2) (bits : List (tm.Γ tm.k₀)) :
    TrCfg (Turing.initList tm bits) (translatedInitial tm bits) := by
  letI : Inhabited tm.Λ := ⟨tm.main⟩
  have h := TM2to1.trCfg_init (Λ := tm.Λ) (σ := tm.σ) tm.k₀ bits
  have he : (TM2.init tm.k₀ bits : tm.Cfg) = Turing.initList tm bits := by
    classical
    simp only [TM2.init,Turing.initList]
    congr 1
    funext k
    by_cases hk : k = tm.k₀
    · subst k; simp
    · simp [Function.update_of_ne hk,hk]
  rw [he] at h
  exact h

/-- Polynomial-time simulation from the encoded TM1 initial configuration.
The bound records both source input length and source block count. -/
theorem run_from_input_bounded (tm : FinTM2) (bits : List (tm.Γ tm.k₀))
    (n : Nat) (last : tm.Cfg)
    (hrun : runSteps tm.step n (Turing.initList tm bits) = some last) :
    ∃ d z, n ≤ d ∧ d ≤ n * (1 + blockCost (bits.length+n*actionLimit tm) (actionLimit tm)) ∧
      runSteps (TM1.step (TM2to1.tr tm.m)) d (translatedInitial tm bits) = some z ∧
      TrCfg last z := by
  exact run_bounded tm n bits.length (Turing.initList tm bits) last (translatedInitial tm bits)
    (initial_related tm bits) (init_length tm bits) hrun

/-- Fixed-machine polynomial obtained by substituting a source-time
polynomial into the explicit quadratic simulation bound. -/
noncomputable def simulationPolynomial (tm : FinTM2) (p : Polynomial Nat) : Polynomial Nat :=
  let x : Polynomial Nat := Polynomial.X
  let d : Polynomial Nat := Polynomial.C (actionLimit tm)
  p * (1 + d * (2*(x+p*d+d)+3))

theorem simulationPolynomial_eval (tm : FinTM2) (p : Polynomial Nat) (m : Nat) :
    (simulationPolynomial tm p).eval m =
      p.eval m * (1 + blockCost (m+p.eval m*actionLimit tm) (actionLimit tm)) := by
  simp [simulationPolynomial,blockCost,Polynomial.eval_add,Polynomial.eval_mul]

/-- A source polynomial time bound induces the displayed TM1-block
polynomial bound, with no assumption that every internal alphabet is finite. -/
theorem run_from_input_polynomial (tm : FinTM2) (p : Polynomial Nat)
    (bits : List (tm.Γ tm.k₀)) (n : Nat) (last : tm.Cfg)
    (hrun : runSteps tm.step n (Turing.initList tm bits) = some last)
    (htime : n ≤ p.eval bits.length) :
    ∃ d z, n ≤ d ∧ d ≤ (simulationPolynomial tm p).eval bits.length ∧
      runSteps (TM1.step (TM2to1.tr tm.m)) d (translatedInitial tm bits) = some z ∧
      TrCfg last z := by
  obtain ⟨d,z,hdpos,hd,hr,hrel⟩ := run_from_input_bounded tm bits n last hrun
  refine ⟨d,z,hdpos,?_,hr,hrel⟩
  rw [simulationPolynomial_eval]
  apply le_trans hd
  apply Nat.mul_le_mul htime
  apply Nat.add_le_add_left
  apply blockCost_mono_left
  have hh := Nat.mul_le_mul_right (actionLimit tm) htime
  omega

end Shared.ComplexityBridge.TM2GeneralTM1Costs
