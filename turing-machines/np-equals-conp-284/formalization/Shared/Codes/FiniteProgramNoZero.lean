import Shared.Codes.FiniteProgramPhase

/-! A structural control-flow property of the tagged serializer's one-cycle
phase. Every continuing row has a nonzero destination, so after the first
step the phase cannot visit its entry state. This is independent of tape data
and does not by itself establish the complete monitored serializer trace. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Codes.FiniteProgramNoZero

open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (shiftRow shiftPair link)
open Shared.Codes.FiniteProgramSelectWord (outRow outRows selectRows dispatch finish)
open Shared.Codes.FiniteProgramExtendAdvance (branch bridge)

def SafeRow (r : Row) : Prop := r.2.2.2 = 0 → r.2.2.1 ≠ 0
def SafePair (r : Row × Row) : Prop := SafeRow r.1 ∧ SafeRow r.2
def Safe (p : Program) : Prop := ∀ r ∈ p, SafePair r

instance (r : Row) : Decidable (SafeRow r) := inferInstanceAs (Decidable (_ → _))
instance (r : Row × Row) : Decidable (SafePair r) := inferInstanceAs (Decidable (_ ∧ _))
instance (p : Program) : Decidable (Safe p) := inferInstanceAs (Decidable (∀ r ∈ p, SafePair r))

theorem safe_append {p q : Program} (hp : Safe p) (hq : Safe q) : Safe (p++q) := by
  intro r hr
  rcases List.mem_append.mp hr with h | h
  · exact hp r h
  · exact hq r h

theorem safe_set (p : Program) (i : Nat) (r : Row × Row) (hp : Safe p) (hr : SafePair r) :
    Safe (p.set i r) := by
  intro row hrow
  rcases List.mem_or_eq_of_mem_set hrow with h | h
  · exact hp row h
  · simpa [h] using hr

theorem safe_shift (p : Program) (d : Nat) (hd : 0 < d) : Safe (p.map (shiftPair d)) := by
  intro r hr
  obtain ⟨r',_,rfl⟩ := List.mem_map.mp hr
  rcases r' with ⟨a,b⟩
  rcases a with ⟨wa,da,na,ta⟩
  rcases b with ⟨wb,db,nb,tb⟩
  simp [SafePair,SafeRow,shiftPair,shiftRow]
  omega

theorem safe_outRows (q dest : Nat) (bits : List Bool) (hq : 0 < q) (hd : 0 < dest) :
    Safe (outRows q bits dest) := by
  induction bits generalizing q with
  | nil => simp [outRows,Safe]
  | cons b bs ih =>
    cases bs with
    | nil => simp [outRows,outRow,Safe,SafePair,SafeRow,Nat.ne_of_gt hd]
    | cons c cs =>
      intro r hr
      simp only [outRows,List.mem_cons] at hr
      rcases hr with he | he
      · subst r; simp [outRow,SafePair,SafeRow]
      · exact ih (q+1) (by omega) r he

theorem safe_selectRows (q : Nat) (zero one : List Bool) (hq : 0 < q) :
    Safe (selectRows q zero one) := by
  have hf : 0 < finish q zero one := by simp [finish]
  have h0 := safe_outRows (q+1) (finish q zero one) zero (by omega) hf
  have h1 := safe_outRows (q+1+zero.length) (finish q zero one) one (by omega) hf
  intro r hr
  simp only [selectRows,List.mem_cons,List.mem_append] at hr
  rcases hr with he | he | he
  · subst r
    cases hz : zero.isEmpty <;> cases ho : one.isEmpty <;>
      simp [dispatch,SafePair,SafeRow,hz,ho,finish] <;> omega
  · exact h0 r he
  · exact h1 r he

theorem safe_shuttle_pre : Safe Shared.Codes.FiniteProgramShuttleSelect.pre := by decide +kernel

theorem safe_stagePre (zero one : List Bool) :
    Safe (Shared.Codes.FiniteProgramTaggedExtend.stagePre zero one) := by
  unfold Shared.Codes.FiniteProgramTaggedExtend.stagePre Shared.Codes.FiniteProgramShuttleSelect.program
  apply safe_append
  · exact safe_append safe_shuttle_pre (by
      simpa [Shared.Codes.FiniteProgramShuttleSelect.pre_length] using
        safe_selectRows 12 (Shared.Codes.FiniteProgramTaggedExtend.codeZero zero)
          (Shared.Codes.FiniteProgramTaggedExtend.codeZero one) (by omega))
  · simp [Safe]

theorem safe_stage (zero one : List Bool) :
    Safe (Shared.Codes.FiniteProgramTaggedExtend.stage zero one []) := by
  unfold Shared.Codes.FiniteProgramTaggedExtend.stage link
  apply safe_append
  · exact safe_append (safe_stagePre zero one) (safe_shift _ _ (by
      rw [Shared.Codes.FiniteProgramTaggedExtend.stagePre_length]
      simp [finish]))
  · simp [Safe]

theorem safe_branch (n : Nat) (hn : 0 < n) : SafePair (branch n) := by
  simp [branch,SafePair,SafeRow,hn.ne']

theorem safe_bridge (n : Nat) (hn : 0 < n) : SafePair (bridge n) := by
  simp [bridge,SafePair,SafeRow,hn.ne']

theorem safe_base (zero one : List Bool) :
    Safe (Shared.Codes.FiniteProgramTaggedLoop.base zero one) := by
  let old := Shared.Codes.FiniteProgramExtendAdvance.old zero one
  let pre := Shared.Codes.FiniteProgramExtendAdvance.handoffPre zero one
  have hold : Safe old := safe_stage zero one
  have hpos : 0 < old.length := by
    rw [Shared.Codes.FiniteProgramExtendAdvance.old_length]
    omega
  have hpre : Safe pre := by
    unfold pre Shared.Codes.FiniteProgramExtendAdvance.handoffPre
    exact safe_append (safe_set old _ _ hold (safe_branch old.length hpos))
      (by simpa [Safe] using safe_bridge (old.length+1) (by omega))
  have hplen : 0 < pre.length := by
    rw [Shared.Codes.FiniteProgramExtendAdvance.prefix_length]
    omega
  unfold Shared.Codes.FiniteProgramTaggedLoop.base Shared.Codes.FiniteProgramExtendAdvance.program link
  exact safe_append (safe_append hpre (safe_shift _ _ hplen)) (by simp [Safe])

theorem safe_phase (zero one : List Bool) : Safe (Shared.Codes.FiniteProgramPhase.program zero one) := by
  let base := Shared.Codes.FiniteProgramTaggedLoop.base zero one
  let stop := Shared.Codes.FiniteProgramTaggedLoop.stop zero one
  have hbase : Safe base := safe_base zero one
  have hpos : 0 < base.length := by
    rw [Shared.Codes.FiniteProgramTaggedLoop.base_length]
    omega
  have he : Shared.Codes.FiniteProgramPhase.program zero one =
      base.set stop (branch base.length) ++ [bridge (base.length+1)] ++
        [Shared.Codes.FiniteProgramPhase.dummy] := by
    unfold Shared.Codes.FiniteProgramPhase.program Shared.Codes.FiniteProgramTaggedLoop.program
    change ((base.set stop (branch base.length) ++ [bridge 0]).set base.length
      (bridge (base.length+1))) ++ [Shared.Codes.FiniteProgramPhase.dummy] = _
    rw [List.set_append_right _ _ (by simp)]
    simp
  rw [he]
  apply safe_append (safe_append (safe_set base stop _ hbase (safe_branch base.length hpos))
    (by simpa [Safe] using safe_bridge (base.length+1) (by omega)))
  simp [Safe,SafePair,SafeRow,Shared.Codes.FiniteProgramPhase.dummy]

/-- A continuing transition of a safe program cannot enter state zero. -/
theorem step_nonzero (p : Program) (hp : Safe p) (c d : Config)
    (h : step p c = some (.inr d)) : d.1 ≠ 0 := by
  cases hg : p[c.1]? with
  | none => simp [step,hg] at h
  | some rows =>
    have hm : rows ∈ p := by
      obtain ⟨hq,he⟩ := List.getElem?_eq_some_iff.mp hg
      rw [← he]
      exact List.getElem_mem hq
    have hs := hp rows hm
    cases hb : c.2.2.1 with
    | false =>
      have hr := hs.1
      simp only [step,hg,hb,Bool.false_eq_true,↓reduceIte] at h
      split at h <;> simp_all [SafeRow]
      cases h
      exact hr
    | true =>
      have hr := hs.2
      simp only [step,hg,hb,↓reduceIte] at h
      split at h <;> simp_all [SafeRow]
      cases h
      exact hr

/-- Every positive-time continuing state in a safe program is nonzero. -/
theorem run_nonzero (p : Program) (hp : Safe p) (c d : Config) (n : Nat)
    (h : run p c (n+1) = some (.inr d)) : d.1 ≠ 0 := by
  simp only [run_succ] at h
  cases hs : run p c n with
  | none => simp [hs,advance] at h
  | some v => cases v with
    | inl b => simp [hs,advance] at h
    | inr e =>
      simp only [hs,advance] at h
      exact step_nonzero p hp e d h

/-- The first-entry argument preserves every prefix, not just its endpoint. -/
theorem first_entry_prefix (p q : Program) (c last : Config) (n stop : Nat) (result : Bool)
    (hvalid : valid p = true) (hc : c.1 < p.length)
    (hstop : ∀ t, step p (stop,t) = some (.inl result))
    (hsame : ∀ d, d.1 < p.length → d.1 ≠ stop → step p d = step q d)
    (hfinal : run p c n = some (.inr last)) :
    ∀ i ≤ n, run p c i = run q c i := by
  have hnot := Shared.Codes.FiniteProgramFirstEntry.not_visited_before p c last n stop result hstop hfinal
  intro i hi
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [run_succ,run_succ,← ih (by omega)]
    cases hr : run p c i with
    | none => rfl
    | some v => cases v with
      | inl b => rfl
      | inr d =>
        change step p d = step q d
        have hin := Shared.Codes.FiniteProgramLink.run_in_range p hvalid c hc i
        rw [hr] at hin
        exact hsame d hin (hnot i (by omega) d hr)

/-- During one actual tagged-serializer cycle, no positive-time live state
before the returned entry is state zero. The proof applies uniformly to both
selected codewords and arbitrary finite tape contexts. -/
theorem tagged_cycle_no_early (zero one : List Bool) (b prior p : Bool)
    (xs L : List Bool) (i : Nat) (hi : 0 < i)
    (hlt : i < Shared.Codes.FiniteProgramTaggedLoop.cost zero one b xs)
    (d : Config)
    (hr : run (Shared.Codes.FiniteProgramTaggedLoop.program zero one)
      (0,Shared.ComplexityBridge.PairMarkedScanner.tapeAt (p::L)
        (b::false::Shared.Codes.FiniteProgramBitShuttle.tagged xs ++ [false,prior,false])) i = some (.inr d)) :
    d.1 ≠ 0 := by
  let base := Shared.Codes.FiniteProgramTaggedLoop.base zero one
  let loop := Shared.Codes.FiniteProgramTaggedLoop.program zero one
  let start : Config := (0,Shared.ComplexityBridge.PairMarkedScanner.tapeAt (p::L)
    (b::false::Shared.Codes.FiniteProgramBitShuttle.tagged xs ++ [false,prior,false]))
  let m := 16*xs.length+16*(if b then one else zero).length+29
  let output := Shared.Codes.FiniteProgramTaggedLoop.output zero one b xs
  let last : Config := (Shared.Codes.FiniteProgramTaggedLoop.stop zero one,
    Shared.ComplexityBridge.PairMarkedScanner.tapeAt L (p::false::
      Shared.Codes.FiniteProgramBitShuttle.tagged output ++ [false,false]))
  have hbase : run base start m = some (.inr last) := by
    have h := Shared.Codes.FiniteProgramExtendAdvance.extend_advance zero one [] b prior p xs L
    dsimp only at h
    change run base start m = some (.inr last) at h
    exact h
  have hprefix := first_entry_prefix base loop start last m
    (Shared.Codes.FiniteProgramTaggedLoop.stop zero one) false
    (Shared.Codes.FiniteProgramTaggedLoop.base_valid zero one)
    (by simp [start,base,Shared.Codes.FiniteProgramTaggedLoop.base_length])
    (Shared.Codes.FiniteProgramTaggedLoop.base_stop zero one)
    (Shared.Codes.FiniteProgramTaggedLoop.base_other zero one) hbase
  have hcost : Shared.Codes.FiniteProgramTaggedLoop.cost zero one b xs = m+2 := by
    simp [Shared.Codes.FiniteProgramTaggedLoop.cost,m]
  change run loop start i = some (.inr d) at hr
  by_cases hm : i ≤ m
  · rw [← hprefix i hm] at hr
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    exact run_nonzero base (safe_base zero one) start d j hr
  · have he : i = m+1 := by omega
    subst i
    have hlast : run loop start m = some (.inr last) := by rw [← hprefix m (by omega)]; exact hbase
    rw [run_succ,hlast] at hr
    have hrow := Shared.Codes.FiniteProgramTaggedLoop.stop_row zero one
    have hpos : 0 < base.length := by rw [Shared.Codes.FiniteProgramTaggedLoop.base_length]; omega
    cases p <;>
      simp [advance,step,loop,last,hrow,branch,
        Shared.ComplexityBridge.PairMarkedScanner.tapeAt] at hr <;>
      cases hr <;> exact Nat.ne_of_gt hpos

end Shared.Codes.FiniteProgramNoZero
