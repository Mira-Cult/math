import Shared.Beeping.WordEventCoverageBoot

/-! Cofinal exact prefix matches preserve eventual silence. The hypothesis
is an infinite family of witnesses, not a finite-prefix computation. -/
namespace PASoundness.WordUnboundedPrefix
open Shared.Beeping
set_option autoImplicit false

/-- Silence bounds the lengths of all emitted finite prefixes. -/
theorem prefix_lengths_bounded_of_silent {C A : Type} (W : WordEventSystem C A)
    (silent : W.erase.EventuallySilent) :
    ∃ B : Nat, ∀ n, (W.prefixWord n).length ≤ B := by
  obtain ⟨T,hT⟩ := silent
  refine ⟨(W.prefixWord T).length, ?_⟩
  have hconst : ∀ d, W.prefixWord (T+d)=W.prefixWord T := by
    intro d
    have hempty : W.wordFrom (W.run T) d=[] := by
      apply (WordEventCoverage.wordFrom_eq_nil_iff W (W.run T) d).2
      intro j _
      by_contra h
      have hb : W.erase.BeepAt (T+j) := by
        apply (WordEventSystem.erase_beep_iff W (T+j)).2
        simpa only [WordEventSystem.run_add] using h
      exact hT (T+j) (by omega) hb
    rw [WordEventSystem.prefix_add,hempty,List.append_nil]
  intro n
  by_cases h : n≤T
  · obtain ⟨suffix,he⟩ := W.prefix_extends h
    have hl := congrArg List.length he
    simp only [List.length_append] at hl
    omega
  · have he : n=T+(n-T) := by omega
    rw [he,hconst]

/-- If silence fails, arbitrarily long event-word prefixes occur. -/
theorem prefix_lengths_unbounded_of_not_silent {C A : Type} (W : WordEventSystem C A)
    (notSilent : ¬ W.erase.EventuallySilent) :
    ∀ k : Nat, ∃ n, k ≤ (W.prefixWord n).length := by
  intro k
  induction k with
  | zero => exact ⟨0,by omega⟩
  | succ k ih =>
    obtain ⟨n,hn⟩ := ih
    have hevent : ∃ t, n≤t ∧ W.erase.BeepAt t := by
      by_contra h
      apply notSilent
      refine ⟨n, ?_⟩
      intro t ht hb
      exact h ⟨t,ht,hb⟩
    obtain ⟨t,ht,hb⟩ := hevent
    obtain ⟨suffix,he⟩ := W.prefix_extends ht
    have hlen := congrArg List.length he
    simp only [List.length_append] at hlen
    have hword : (W.step (W.run t)).2 ≠ [] := (WordEventSystem.erase_beep_iff W t).1 hb
    have hpos : 0 < (W.step (W.run t)).2.length := by
      cases hw : (W.step (W.run t)).2 with
      | nil => exact False.elim (hword hw)
      | cons a as => simp [hw]
    refine ⟨t+1, ?_⟩
    rw [WordEventSystem.prefix_succ,List.length_append]
    omega

theorem eventuallySilent_iff_prefix_lengths_bounded {C A : Type} (W : WordEventSystem C A) :
    W.erase.EventuallySilent ↔ ∃ B : Nat, ∀ n, (W.prefixWord n).length ≤ B := by
  constructor
  · exact prefix_lengths_bounded_of_silent W
  · rintro ⟨B,hB⟩
    by_contra h
    obtain ⟨n,hn⟩ := prefix_lengths_unbounded_of_not_silent W h (B+1)
    have hb := hB n
    omega

/-- A matching target time exists for every source prefix, and those times
are cofinal because each is at least the source index. -/
def CofinalPrefixMatch {S T A : Type} (source : WordEventSystem S A)
    (target : WordEventSystem T A) : Prop :=
  ∀ n, ∃ m, n≤m ∧ target.prefixWord m=source.prefixWord n

/-- Every positive-boundary word refinement supplies cofinal prefix matches. -/
theorem ofWordRefinement {S T A : Type} {source : WordEventSystem S A}
    {target : WordEventSystem T A} (r : WordRefinement source target) :
    CofinalPrefixMatch source target := by
  intro n
  refine ⟨r.boundary n, ?_,r.prefix_eq n⟩
  have h := r.boundary_ge n
  omega

/-- No coherence between the individual witnesses is needed for eventual
silence: the cofinal exact-prefix condition already controls both streams. -/
theorem eventuallySilent_iff {S T A : Type} (source : WordEventSystem S A)
    (target : WordEventSystem T A) (matchPrefixes : CofinalPrefixMatch source target) :
    source.erase.EventuallySilent ↔ target.erase.EventuallySilent := by
  rw [eventuallySilent_iff_prefix_lengths_bounded,eventuallySilent_iff_prefix_lengths_bounded]
  constructor
  · rintro ⟨B,hB⟩
    refine ⟨B, ?_⟩
    intro n
    obtain ⟨m,hnm,he⟩ := matchPrefixes n
    obtain ⟨suffix,hs⟩ := target.prefix_extends hnm
    have hl := congrArg List.length hs
    simp only [List.length_append] at hl
    have hb := hB n
    rw [he] at hl
    omega
  · rintro ⟨B,hB⟩
    refine ⟨B, ?_⟩
    intro n
    obtain ⟨m,_,he⟩ := matchPrefixes n
    have hb := hB m
    simpa only [he] using hb

/-- The same cofinal witnesses preserve the entire ordered output, including
finite streams and multiplicities. -/
theorem sameOutput {S T A : Type} (source : WordEventSystem S A)
    (target : WordEventSystem T A) (matchPrefixes : CofinalPrefixMatch source target) :
    SameOutput source target := by
  intro w
  constructor
  · rintro ⟨n,suffix,hn⟩
    obtain ⟨m,_,he⟩ := matchPrefixes n
    exact ⟨m,suffix,he.trans hn⟩
  · rintro ⟨m,suffix,hm⟩
    obtain ⟨k,hge,he⟩ := matchPrefixes m
    obtain ⟨extra,hs⟩ := target.prefix_extends hge
    refine ⟨m,suffix++extra, ?_⟩
    rw [←he,hs,hm,List.append_assoc]

/-- Both sets of matching times are cofinal. Matches need not exist at every
source step and the witnesses need not form a coherent sequence. -/
def CofinalPairMatch {S T A : Type} (source : WordEventSystem S A)
    (target : WordEventSystem T A) : Prop :=
  ∀ N, ∃ n k, N≤n ∧ N≤k ∧ target.prefixWord k=source.prefixWord n

theorem cofinalPairs_of_prefixMatch {S T A : Type} {source : WordEventSystem S A}
    {target : WordEventSystem T A} (h : CofinalPrefixMatch source target) :
    CofinalPairMatch source target := by
  intro N
  obtain ⟨k,hk,he⟩ := h N
  exact ⟨N,k,le_refl _,hk,he⟩

/-- Cofinal matches at selected times preserve the complete ordered output. -/
theorem sameOutput_of_cofinalPairs {S T A : Type} (source : WordEventSystem S A)
    (target : WordEventSystem T A) (h : CofinalPairMatch source target) :
    SameOutput source target := by
  intro w
  constructor
  · rintro ⟨n,suffix,hn⟩
    obtain ⟨i,k,hni,_,he⟩ := h n
    obtain ⟨extra,hs⟩ := source.prefix_extends hni
    refine ⟨k,suffix++extra, ?_⟩
    rw [he,hs,hn,List.append_assoc]
  · rintro ⟨k,suffix,hk⟩
    obtain ⟨i,j,_,hkj,he⟩ := h k
    obtain ⟨extra,hs⟩ := target.prefix_extends hkj
    refine ⟨i,suffix++extra, ?_⟩
    rw [←he,hs,hk,List.append_assoc]

/-- Cofinal matches at selected times preserve eventual silence in both
directions, without assuming any step-by-step simulation relation. -/
theorem eventuallySilent_iff_of_cofinalPairs {S T A : Type}
    (source : WordEventSystem S A) (target : WordEventSystem T A)
    (h : CofinalPairMatch source target) :
    source.erase.EventuallySilent ↔ target.erase.EventuallySilent := by
  rw [eventuallySilent_iff_prefix_lengths_bounded,eventuallySilent_iff_prefix_lengths_bounded]
  constructor
  · rintro ⟨B,hB⟩
    refine ⟨B, ?_⟩
    intro n
    obtain ⟨i,k,_,hnk,he⟩ := h n
    obtain ⟨suffix,hs⟩ := target.prefix_extends hnk
    have hl := congrArg List.length hs
    simp only [List.length_append] at hl
    rw [he] at hl
    have hb := hB i
    omega
  · rintro ⟨B,hB⟩
    refine ⟨B, ?_⟩
    intro n
    obtain ⟨i,k,hni,_,he⟩ := h n
    obtain ⟨suffix,hs⟩ := source.prefix_extends hni
    have hl := congrArg List.length hs
    simp only [List.length_append] at hl
    have hb := hB k
    rw [he] at hb
    omega

#print axioms sameOutput_of_cofinalPairs
#print axioms eventuallySilent_iff_of_cofinalPairs

#print axioms ofWordRefinement
#print axioms sameOutput

#print axioms eventuallySilent_iff
end PASoundness.WordUnboundedPrefix
