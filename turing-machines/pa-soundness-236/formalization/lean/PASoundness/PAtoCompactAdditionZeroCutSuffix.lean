import PASoundness.PAtoCompactAdditionEmptySuffix

/-! With an empty cut, the literal suffix graph has the same members as its
source. This is a finite K derivation with explicit zero and filter premises,
not a quotient isomorphism or an addition axiom. Compact negation is the
literal implication to code 1. All freshness assumptions below concern syntax
names; the represented values may coincide. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionZeroCutSuffix
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactFilterInstantiation
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdditionEmptySuffix
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- For an empty cut, the literal filter clauses reduce pointwise to the two
membership implications between the source and the suffix. -/
def zero_cut_suffix_at (z cut s t w v : Nat) (fresh : [z,cut,s,t,w,v].Nodup) :
    KDerivation (imp (zeroCode cut w)
      (imp (filterGraph z s t (neg (member cut t)))
        (both (imp (member s v) (member z v)) (imp (member z v) (member s v))))) := by
  have htz : t ≠ z := by intro h; subst t; simp at fresh
  have hts : t ≠ s := by intro h; subst t; simp at fresh
  have htv : t ≠ v := by intro h; subst t; simp at fresh
  have htc : t ≠ cut := by intro h; subst t; simp at fresh
  have hwv : w ≠ v := by intro h; subst w; simp at fresh
  have hwc : w ≠ cut := by intro h; subst w; simp at fresh
  let P : Formula := (Formula.member cut t).not
  have hi := filter_at z s t v P htz hts htv (by simp [P,Formula.not,Formula.binders])
    (by simp [P,Formula.not,Formula.binders])
  have hi' : KDerivation (imp (filterGraph z s t (neg (member cut t)))
      (both (imp (member s v) (both (member z v) (neg (member cut v))))
        (imp (both (member z v) (neg (member cut v))) (member s v)))) := by
    simpa [P,Formula.not,Formula.encode,replace,rename,htc,htv,Ne.symm htc,Ne.symm htv,
      CompactProof.neg] using hi
  let Z := zeroCode cut w
  let F := filterGraph z s t (neg (member cut t))
  let Γ := [F,Z]
  have hf : Context Γ F := .head _ _
  have hz : Context Γ Z := .hypothesis (by simp [Γ])
  have hinst := Context.mp hf (Context.closed hi')
  have hn : Context Γ (neg (member cut v)) := .mp hz (.closed (zero_excludes cut w v hwv hwc))
  have hforward : Context Γ (imp (member s v) (member z v)) := by
    apply Context.deduction
    have hm : Context (member s v :: Γ) (member s v) := .head _ _
    exact Context.conjunctionLeft (.mp hm (Context.under (Context.conjunctionLeft hinst) _))
  have hreverse : Context Γ (imp (member z v) (member s v)) := by
    apply Context.deduction
    have hm : Context (member z v :: Γ) (member z v) := .head _ _
    have hp := Context.conjunctionIntro hm (Context.under hn _)
    exact .mp hp (Context.under (Context.conjunctionRight hinst) _)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact Context.conjunctionIntro hforward hreverse

theorem zero_cut_suffix_at_certificate (z cut s t w v : Nat) (fresh : [z,cut,s,t,w,v].Nodup) :
    theoremCode (certificate (zero_cut_suffix_at z cut s t w v fresh)) =
      imp (zeroCode cut w) (imp (filterGraph z s t (neg (member cut t)))
        (both (imp (member s v) (member z v)) (imp (member z v) (member s v)))) :=
  certificate_correct (zero_cut_suffix_at z cut s t w v fresh)

/-- The pointwise result is uniformly quantified inside K, using explicit
vacuity of both premises at the fresh test name. -/
def zero_cut_suffix_all (z cut s t w v : Nat) (fresh : [z,cut,s,t,w,v].Nodup) :
    KDerivation (imp (zeroCode cut w)
      (imp (filterGraph z s t (neg (member cut t)))
        (allCode v (both (imp (member s v) (member z v)) (imp (member z v) (member s v)))))) := by
  have f5 : [z,cut,s,t,v].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or, not_false_eq_true, List.nodup_nil, and_true] at fresh ⊢
    tauto
  have hvc : v ≠ cut := by intro h; subst v; simp at fresh
  have hvw : v ≠ w := by intro h; subst v; simp at fresh
  let F := filterGraph z s t (neg (member cut t))
  let Z := zeroCode cut w
  let Γ := [F,Z]
  have hf : Context Γ F := .head _ _
  have hz : Context Γ Z := .hypothesis (by simp [Γ])
  have hp := Context.mp hf (Context.mp hz (.closed (zero_cut_suffix_at z cut s t w v fresh)))
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode v h)) := by
    intro h hh
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hh
    by_cases heq : h = F
    · subst h
      exact suffix_graph_vacuity z cut s t v f5
    · have heq' : h = Z := hh.resolve_left heq
      subst h
      let ZF : Formula := .all w (Formula.member cut w).not
      have hn : v ∉ ZF.names := by simp [ZF,Formula.not,Formula.names,hvc,hvw]
      have hd := ZF.vacuity v hn
      simpa [Z,ZF,Formula.not,Formula.encode,zeroCode,neg] using hd
  have ha := Context.generalize v hv hp
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact ha

theorem zero_cut_suffix_all_certificate (z cut s t w v : Nat) (fresh : [z,cut,s,t,w,v].Nodup) :
    theoremCode (certificate (zero_cut_suffix_all z cut s t w v fresh)) =
      imp (zeroCode cut w) (imp (filterGraph z s t (neg (member cut t)))
        (allCode v (both (imp (member s v) (member z v)) (imp (member z v) (member s v))))) :=
  certificate_correct (zero_cut_suffix_all z cut s t w v fresh)

end PASoundness.PAtoCompactAdditionZeroCutSuffix
#print axioms PASoundness.PAtoCompactAdditionZeroCutSuffix.zero_cut_suffix_at
#print axioms PASoundness.PAtoCompactAdditionZeroCutSuffix.zero_cut_suffix_at_certificate
#print axioms PASoundness.PAtoCompactAdditionZeroCutSuffix.zero_cut_suffix_all
#print axioms PASoundness.PAtoCompactAdditionZeroCutSuffix.zero_cut_suffix_all_certificate
