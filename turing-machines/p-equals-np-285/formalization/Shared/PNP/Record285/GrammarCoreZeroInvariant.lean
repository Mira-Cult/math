import Shared.PNP.Record285.GrammarCoreZeroBank
import Shared.PNP.Record285.GrammarCoreSemantics

/-! Lift a checked mask certificate to the actual list-bank core execution. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.GrammarCoreZero
open Shared.Beeping
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.GrammarExact
open Shared.PNP.Record285.GrammarCoreGraph

def Valid (rows : Array CoreRow) (masks : Array (Array Nat)) (s : CoreState) : Prop :=
  s.index < rows.size ∧ 15 ≤ s.fields.length ∧
    ∃ mask, masks[s.index]? = some mask ∧ validBank mask (fun i => s.fields.getD i 0)

theorem check_parts (rows : Array CoreRow) (masks : Array (Array Nat))
    (h : check rows masks = true) :
    rows.size = masks.size ∧
    (List.range 15).all (fun i => admits (slot (masks[0]?.getD #[]) i) 0) = true ∧
    (List.range rows.size).all (rowCheck rows masks) = true := by
  simp only [check,Bool.and_eq_true_iff,decide_eq_true_eq] at h
  exact ⟨h.1.1.1,h.1.2,h.2⟩

theorem initial_valid (rows : Array CoreRow) (masks : Array (Array Nat))
    (h : check rows masks = true) (hne : 0 < rows.size) : Valid rows masks (coreSystem rows).initial := by
  obtain ⟨hsize,hzero,_⟩ := check_parts rows masks h
  have hm : 0 < masks.size := by omega
  let mask := masks[0]
  have hmask : masks[0]? = some mask := by simp [mask]
  refine ⟨hne,?_,mask,hmask,?_⟩
  · change 15 ≤ (List.replicate 1909 0).length
    simp
  · intro i hi
    have hz := List.all_eq_true.mp hzero i (List.mem_range.mpr hi)
    change admits (slot mask i) ((List.replicate 1909 0).getD i 0) = true
    have hv : (List.replicate 1909 0).getD i 0 = 0 := by
      simp only [List.getD_eq_getElem?_getD,List.getElem?_replicate]
      split <;> rfl
    rw [hv]
    simpa [hmask] using hz

theorem rowCheck_sound (rows : Array CoreRow) (masks : Array (Array Nat))
    (i : Nat) (spec : CoreRow) (before : Array Nat)
    (hs : rows[i]? = some spec) (hm : masks[i]? = some before)
    (h : rowCheck rows masks i = true) :
    ∃ no yes, masks[spec.no]? = some no ∧ masks[spec.yes]? = some yes ∧
      transfers spec before no yes = true := by
  simp only [rowCheck,hs,hm] at h
  cases hn : masks[spec.no]? with
  | none => simp [hn] at h
  | some no =>
    cases hy : masks[spec.yes]? with
    | none => simp [hn,hy] at h
    | some yes => exact ⟨no,yes,rfl,rfl,by simpa [hn,hy] using h⟩

theorem transfers_index_bound (spec : CoreRow) (before no yes : Array Nat)
    (h : transfers spec before no yes = true) (i : Nat) (hi : operationIndex spec.edge = some i) :
    i < 15 := by
  simp only [transfers,hi,Bool.and_eq_true_iff,decide_eq_true_eq] at h
  exact h.1.1

/-- The actual core transition preserves the checked masks and the complete
finite-bank length invariant. -/
theorem step_preserves (rows : Array CoreRow) (masks : Array (Array Nat))
    (hcheck : check rows masks = true) (s : CoreState) (hvalid : Valid rows masks s) :
    Valid rows masks (coreStep rows s).1 := by
  obtain ⟨hindex,hlen,before,hbefore,hbank⟩ := hvalid
  obtain ⟨hsize,_,hrows⟩ := check_parts rows masks hcheck
  obtain ⟨spec,hspec⟩ : ∃ spec, rows[s.index]? = some spec :=
    ⟨rows[s.index],by simp⟩
  have hrow := List.all_eq_true.mp hrows s.index (List.mem_range.mpr hindex)
  obtain ⟨no,yes,hno,hyes,htransfer⟩ := rowCheck_sound rows masks s.index spec before hspec hbefore hrow
  have hoperand : ∀ i, operationIndex spec.edge = some i → i < s.fields.length := by
    intro i hi
    have hsmall := transfers_index_bound spec before no yes htransfer i hi
    omega
  let b := operationBranch spec.edge (operandValue spec.edge (fun i => s.fields.getD i 0))
  let nextIndex := if b then spec.yes else spec.no
  let nextMask := if b then yes else no
  have hmask : masks[nextIndex]? = some nextMask := by
    dsimp [nextIndex,nextMask]
    cases b <;> simp_all
  have hnext : nextIndex < rows.size := by
    obtain ⟨hm,_⟩ := Array.getElem?_eq_some_iff.mp hmask
    omega
  have hpreserve := transfers_sound spec before no yes (fun i => s.fields.getD i 0) htransfer hbank
  have hlength := bank_length_nondecreasing spec.edge s.fields hoperand
  have hstep : coreStep rows s =
      (⟨nextIndex,applyUpdate spec.edge s.fields⟩,decide (spec.edge = .beep)) := by
    simp [coreStep,hspec,nextIndex,b,graph_test_matches]
  rw [hstep]
  change Valid rows masks ⟨nextIndex,applyUpdate spec.edge s.fields⟩
  refine ⟨hnext,?_,nextMask,hmask,?_⟩
  · change 15 ≤ (applyUpdate spec.edge s.fields).length
    omega
  · intro j hj
    have hread := bank_update_correct spec.edge s.fields hoperand j (by omega)
    change admits (slot nextMask j) ((applyUpdate spec.edge s.fields).getD j 0) = true
    rw [hread]
    exact hpreserve j hj

theorem run_valid (rows : Array CoreRow) (masks : Array (Array Nat))
    (hcheck : check rows masks = true) (hne : 0 < rows.size) (n : Nat) :
    Valid rows masks ((coreSystem rows).run n) := by
  induction n with
  | zero => exact initial_valid rows masks hcheck hne
  | succ n ih =>
    have hs := step_preserves rows masks hcheck ((coreSystem rows).run n) ih
    simpa only [EventSystem.run_succ,coreSystem] using hs

theorem admits_only_zero (n : Nat) (h : admits 1 n = true) : n = 0 := by
  by_cases h0 : n = 0
  · exact h0
  · by_cases h1 : n = 1 <;> simp [admits,category,h0,h1] at h

/-- A selected occurrence tests a physically represented zero, provided the
actual core state satisfies the certified mask invariant. -/
theorem selectedZero_sound (rows : Array CoreRow) (masks : Array (Array Nat)) (s : CoreState)
    (hvalid : Valid rows masks s) (hselected : selectedZero rows masks s.index = true) :
    ∃ reg no yes, reg < 15 ∧ rows[s.index]? = some ⟨.dec reg,no,yes⟩ ∧
      (s.fields.drop reg).headD 0 = 0 := by
  obtain ⟨hindex,_,mask,hmask,hbank⟩ := hvalid
  obtain ⟨spec,hspec⟩ : ∃ spec, rows[s.index]? = some spec :=
    ⟨rows[s.index],by simp⟩
  cases spec with
  | mk e no yes =>
    cases e with
    | dec reg =>
      have hc : reg < 15 ∧ slot mask reg = 1 := by
        simpa [selectedZero,hspec,hmask] using hselected
      have hr := hbank reg hc.1
      rw [hc.2] at hr
      have hz := admits_only_zero _ hr
      exact ⟨reg,no,yes,hc.1,hspec,by simpa [drop_head_getD] using hz⟩
    | node i => simp [selectedZero,hspec,hmask] at hselected
    | inc i => simp [selectedZero,hspec,hmask] at hselected
    | half i => simp [selectedZero,hspec,hmask] at hselected
    | beep => simp [selectedZero,hspec,hmask] at hselected
    | brk i => simp [selectedZero,hspec,hmask] at hselected
    | cont i => simp [selectedZero,hspec,hmask] at hselected

end Shared.PNP.Record285.GrammarCoreZero
