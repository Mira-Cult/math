import Shared.PNP.Record285.GrammarPureSystem

/-! A finite, kernel-checked no-administrative-cycle certificate for the
frozen grammar. A break/continue chain reaches an ordinary operation quickly. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.GrammarAdministrative
open Shared.Beeping
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.GrammarExact
open Shared.PNP.Record285.GrammarPure

def isAdministrative : Edge → Bool
  | .brk _ => true
  | .cont _ => true
  | _ => false

/-- Follow one administrative successor, then dispatch on its zero-padded
control. Register contents play no role in either control transfer. -/
def successorLeaf (code : List Bool) (e : Edge) : Option (List Bool × Edge) := do
  let control ← controlStep e [] code
  let (next,len) ← descend 163 rootIndex (pureBits control) 0
  pure (window (pureBits control) 0 len,next)

def leafSafe (code : List Bool) (e : Edge) : Bool :=
  if isAdministrative e then
    match successorLeaf code e with
    | none => false
    | some (next,nextEdge) =>
      if isAdministrative nextEdge then
        match successorLeaf next nextEdge with
        | none => false
        | some (_,thirdEdge) => !isAdministrative thirdEdge
      else true
  else true

/-- Traverse all unfolded grammar paths; fuel exhaustion or a missing node is
rejected. This checker does not execute any referenced external file. -/
def checkPaths : Nat → Nat → List Bool → Bool
  | 0,_,_ => false
  | fuel+1,n,pre =>
    [false,true].all fun b =>
      match nodeEdge n b with
      | none => false
      | some (.node j) => checkPaths fuel j (pre++[b])
      | some e => leafSafe (pre++[b]) e

/-- The finite traversal certifies every successful, arbitrarily specified
path; the proof does not assume that an emitted path list is exhaustive. -/
theorem checkPaths_sound (fuel n : Nat) (pre code : List Bool) (e : Edge)
    (hcheck : checkPaths fuel n pre = true) (hwalk : walk n code = some e) :
    leafSafe (pre++code) e = true := by
  induction fuel generalizing n pre code with
  | zero => simp [checkPaths] at hcheck
  | succ fuel ih =>
    cases code with
    | nil => simp [walk] at hwalk
    | cons bit rest =>
      have hbranch : (match nodeEdge n bit with
          | none => false
          | some (.node j) => checkPaths fuel j (pre++[bit])
          | some edge => leafSafe (pre++[bit]) edge) = true := by
        have ha := List.all_eq_true.mp hcheck bit
        apply ha
        cases bit <;> simp
      cases hedge : nodeEdge n bit with
      | none => simp [hedge] at hbranch
      | some found =>
        cases found with
        | node j =>
          have hs : checkPaths fuel j (pre++[bit]) = true := by simpa only [hedge] using hbranch
          have hw : walk j rest = some e := by simpa only [walk,hedge] using hwalk
          simpa only [List.append_assoc,List.singleton_append] using ih j (pre++[bit]) rest hs hw
        | inc i =>
          cases rest <;> simp [walk,hedge] at hwalk
          subst e
          simpa only [hedge,List.singleton_append] using hbranch
        | dec i =>
          cases rest <;> simp [walk,hedge] at hwalk
          subst e
          simpa only [hedge,List.singleton_append] using hbranch
        | half i =>
          cases rest <;> simp [walk,hedge] at hwalk
          subst e
          simpa only [hedge,List.singleton_append] using hbranch
        | beep =>
          cases rest <;> simp [walk,hedge] at hwalk
          subst e
          simpa only [hedge,List.singleton_append] using hbranch
        | brk i =>
          cases rest <;> simp [walk,hedge] at hwalk
          subst e
          simpa only [hedge,List.singleton_append] using hbranch
        | cont i =>
          cases rest <;> simp [walk,hedge] at hwalk
          subst e
          simpa only [hedge,List.singleton_append] using hbranch

/-- Kernel reduction checks the complete unfolded frozen grammar. -/
theorem all_paths_checked : checkPaths 43 162 [] = true := by decide

theorem every_leaf_safe (code : List Bool) (e : Edge)
    (hwalk : walk rootIndex code = some e) : leafSafe code e = true := by
  simpa only [List.nil_append,rootIndex] using checkPaths_sound 43 162 [] code e all_paths_checked hwalk

theorem leafSafe_sound (code : List Bool) (e : Edge) (hadmin : isAdministrative e = true)
    (h : leafSafe code e = true) :
    ∃ code₁ e₁, successorLeaf code e = some (code₁,e₁) ∧
      (isAdministrative e₁ = false ∨
        ∃ code₂ e₂, successorLeaf code₁ e₁ = some (code₂,e₂) ∧ isAdministrative e₂ = false) := by
  simp only [leafSafe,hadmin,if_true] at h
  cases hs : successorLeaf code e with
  | none => simp [hs] at h
  | some pair =>
    obtain ⟨code₁,e₁⟩ := pair
    refine ⟨code₁,e₁,rfl,?_⟩
    cases he : isAdministrative e₁ with
    | false => exact Or.inl rfl
    | true =>
      right
      simp only [hs,he,if_true] at h
      cases ht : successorLeaf code₁ e₁ with
      | none => simp [ht] at h
      | some pair =>
        obtain ⟨code₂,e₂⟩ := pair
        simp only [ht] at h
        exact ⟨code₂,e₂,rfl,by simpa using h⟩

theorem admin_ignores_bank (e : Edge) (fields : List Nat) (code : List Bool)
    (h : isAdministrative e = true) :
    controlStep e fields code = controlStep e [] code ∧ applyUpdate e fields = fields := by
  cases e with
  | brk i =>
    cases i with
    | zero => exact ⟨rfl,rfl⟩
    | succ i => cases i with
      | zero => exact ⟨rfl,rfl⟩
      | succ i => cases i <;> exact ⟨rfl,rfl⟩
  | cont i =>
    cases i with
    | zero => exact ⟨rfl,rfl⟩
    | succ i => cases i with
      | zero => exact ⟨rfl,rfl⟩
      | succ i => cases i <;> exact ⟨rfl,rfl⟩
  | node i => contradiction
  | inc i => contradiction
  | dec i => contradiction
  | half i => contradiction
  | beep => contradiction

/-- A certified administrative successor is the next pure interpreter leaf,
with the entire bank unchanged. -/
theorem successorLeaf_step (p : State) (e : Edge) (len : Nat) (code₁ : List Bool) (e₁ : Edge)
    (hdesc : descend 163 rootIndex (pureBits p.control) 0 = some (e,len))
    (hadmin : isAdministrative e = true)
    (hnext : successorLeaf (window (pureBits p.control) 0 len) e = some (code₁,e₁)) :
    (step p).1.fields = p.fields ∧
    descend 163 rootIndex (pureBits (step p).1.control) 0 = some (e₁,code₁.length) ∧
    window (pureBits (step p).1.control) 0 code₁.length = code₁ := by
  let code := window (pureBits p.control) 0 len
  have hindependent := admin_ignores_bank e p.fields code hadmin
  change successorLeaf code e = _ at hnext
  unfold successorLeaf at hnext
  cases hc : controlStep e [] code with
  | none => simp [hc] at hnext
  | some control =>
    cases hd : descend 163 rootIndex (pureBits control) 0 with
    | none => simp [hc,hd] at hnext
    | some pair =>
      obtain ⟨next,nextLen⟩ := pair
      simp [hc,hd] at hnext
      obtain ⟨hcode,hedge⟩ := hnext
      subst code₁
      subst e₁
      have hctrl : controlStep e p.fields code = some control := hindependent.1.trans hc
      have hstep : step p = (⟨control,p.fields⟩,decide (e = .beep)) := by
        simp only [step,hdesc,Option.getD_some]
        change (State.mk ((controlStep e p.fields code).getD []) (applyUpdate e p.fields),_) = _
        rw [hctrl,hindependent.2]
        rfl
      rw [hstep]
      have hlen : (window (pureBits control) 0 nextLen).length = nextLen := window_length _ _ _
      rw [hlen]
      exact ⟨rfl,hd,rfl⟩

def administrativeState (p : State) : Prop :=
  isAdministrative ((descend 163 rootIndex (pureBits p.control) 0).getD (.beep,0)).1 = true

/-- No reachable run can execute three consecutive break/continue actions. -/
theorem no_three_administrative (n : Nat) :
    ¬ (administrativeState (system.run n) ∧
       administrativeState (system.run (n+1)) ∧
       administrativeState (system.run (n+2))) := by
  intro ⟨ha,hb,hc⟩
  obtain ⟨e,len,control,_,hdesc,_⟩ := reachable_step_defined n
  have hadmin : isAdministrative e = true := by
    simpa only [administrativeState,hdesc,Option.getD_some] using ha
  obtain ⟨len',_,_,hend,hwalk⟩ := descend_trace 163 162 (pureBits (system.run n).control) 0 e len hdesc
  have hlen : len' = len := by omega
  subst len'
  have hsafe := every_leaf_safe (window (pureBits (system.run n).control) 0 len) e hwalk
  obtain ⟨code₁,e₁,hnext,hbranches⟩ := leafSafe_sound _ e hadmin hsafe
  have hs := successorLeaf_step (system.run n) e len code₁ e₁ hdesc hadmin hnext
  have hrun₁ : system.run (n+1) = (step (system.run n)).1 := rfl
  have hb' : isAdministrative e₁ = true := by
    rw [hrun₁] at hb
    simpa only [administrativeState,hs.2.1,Option.getD_some] using hb
  rcases hbranches with hnon | ⟨code₂,e₂,hnext₂,hnon⟩
  · rw [hnon] at hb'
    contradiction
  · have hs₂ := successorLeaf_step (step (system.run n)).1 e₁ code₁.length code₂ e₂
      hs.2.1 hb' (by simpa only [hs.2.2] using hnext₂)
    have hrun₂ : system.run (n+2) = (step (step (system.run n)).1).1 := by
      simp only [EventSystem.run_succ,system]
    have hc' : isAdministrative e₂ = true := by
      rw [hrun₂] at hc
      simpa only [administrativeState,hs₂.2.1,Option.getD_some] using hc
    rw [hnon] at hc'
    contradiction

/-- Every three reachable actions include an action other than break/continue. -/
theorem nonAdministrative_within_three (n : Nat) :
    ∃ k, n ≤ k ∧ k < n + 3 ∧ ¬ administrativeState (system.run k) := by
  classical
  by_cases ha : administrativeState (system.run n)
  · by_cases hb : administrativeState (system.run (n+1))
    · have hc : ¬ administrativeState (system.run (n+2)) := by
        intro hc
        exact no_three_administrative n ⟨ha,hb,hc⟩
      exact ⟨n+2, by omega, by omega, hc⟩
    · exact ⟨n+1, by omega, by omega, hb⟩
  · exact ⟨n, by omega, by omega, ha⟩

end Shared.PNP.Record285.GrammarAdministrative
