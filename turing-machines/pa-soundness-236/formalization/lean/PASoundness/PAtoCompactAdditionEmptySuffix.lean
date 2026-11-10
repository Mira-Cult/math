import PASoundness.PAtoCompactFilterInstantiation
import PASoundness.PAtoCompactZeroSuccessor

/-! A K proof that a suffix filtered from an object by nonmembership in an
equal cut is empty. This is an addition-identity ingredient under explicit
equality and filter-graph hypotheses; it is not a quotient or addition axiom.
Compact negation here is literally implication to code 1. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionEmptySuffix
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactFilterInstantiation
open PASoundness.PAtoCompactZeroSuccessor
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The literal suffix filter graph is vacuous at a fresh element name. -/
def suffix_graph_vacuity (z cut s t v : Nat) (fresh : [z,cut,s,t,v].Nodup) :
    KDerivation (imp (filterGraph z s t (neg (member cut t)))
      (allCode v (filterGraph z s t (neg (member cut t))))) := by
  let P : Formula := (Formula.member cut t).not
  let Q : Formula := namedBoth (.member z t) P
  let F : Formula := .all t (namedBoth (.imp (.member s t) Q) (.imp Q (.member s t)))
  have hv : v ∉ F.names := by
    have hvz : v ≠ z := by intro h; subst v; simp at fresh
    have hvc : v ≠ cut := by intro h; subst v; simp at fresh
    have hvs : v ≠ s := by intro h; subst v; simp at fresh
    have hvt : v ≠ t := by intro h; subst v; simp at fresh
    simp [F,Q,P,namedBoth,Formula.not,Formula.names,hvz,hvc,hvs,hvt]
  have h := F.vacuity v hv
  simpa [F,Q,P,namedBoth,Formula.not,Formula.encode,filterGraph,filterPredicate,
    CompactProof.both, CompactProof.neg] using h

/-- If `z=cut`, every member of a represented suffix would be both a member
and a nonmember of `cut`, so K derives the displayed zero graph for `s`. -/
def equal_cut_empty_suffix (z cut s t v : Nat) (fresh : [z,cut,s,t,v].Nodup) :
    KDerivation (imp (equal z cut)
      (imp (filterGraph z s t (neg (member cut t))) (zeroCode s v))) := by
  have htz : t ≠ z := by intro h; subst t; simp at fresh
  have hts : t ≠ s := by intro h; subst t; simp at fresh
  have htv : t ≠ v := by intro h; subst t; simp at fresh
  have htc : t ≠ cut := by intro h; subst t; simp at fresh
  have hvz : v ≠ z := by intro h; subst v; simp at fresh
  have hvc : v ≠ cut := by intro h; subst v; simp at fresh
  let P : Formula := (Formula.member cut t).not
  have hi := filter_at z s t v P htz hts htv (by simp [P,Formula.not,Formula.binders])
    (by simp [P,Formula.not,Formula.binders])
  have hi' : KDerivation (imp (filterGraph z s t (neg (member cut t)))
      (both (imp (member s v) (both (member z v) (neg (member cut v))))
        (imp (both (member z v) (neg (member cut v))) (member s v)))) := by
    simpa [P,Formula.not,Formula.encode,replace,rename,htc,htv,Ne.symm htc,Ne.symm htv,
      CompactProof.neg] using hi
  let E := equal z cut
  let F := filterGraph z s t (neg (member cut t))
  let Γ := [F,E]
  have hf : Context Γ F := .head _ _
  have he : Context Γ E := .hypothesis (by simp [Γ])
  have hp : Context Γ (neg (member s v)) := by
    apply Context.deduction
    have hm : Context (member s v :: Γ) (member s v) := .head _ _
    have hinst : Context (member s v :: Γ)
        (both (imp (member s v) (both (member z v) (neg (member cut v))))
          (imp (both (member z v) (neg (member cut v))) (member s v))) :=
      .mp (Context.under hf _) (.closed hi')
    have hboth : Context (member s v :: Γ) (both (member z v) (neg (member cut v))) :=
      .mp hm (Context.conjunctionLeft hinst)
    have hz : Context (member s v :: Γ) (member z v) := Context.conjunctionLeft hboth
    have hn : Context (member s v :: Γ) (neg (member cut v)) := Context.conjunctionRight hboth
    have hc : Context (member s v :: Γ) (member cut v) :=
      .mp hz (.mp (Context.under he _) (.closed (memberLeftEquality z cut v)))
    exact .mp hc hn
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode v h)) := by
    intro h hh
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hh
    by_cases heq : h = F
    · subst h
      exact suffix_graph_vacuity z cut s t v fresh
    · have heq' : h = E := hh.resolve_left heq
      subst h
      exact equalityVacuity z cut v hvz hvc
  have hall := Context.generalize v hv hp
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  simpa [zeroCode] using hall

theorem equal_cut_empty_suffix_certificate (z cut s t v : Nat) (fresh : [z,cut,s,t,v].Nodup) :
    theoremCode (certificate (equal_cut_empty_suffix z cut s t v fresh)) =
      imp (equal z cut) (imp (filterGraph z s t (neg (member cut t))) (zeroCode s v)) :=
  certificate_correct (equal_cut_empty_suffix z cut s t v fresh)

end PASoundness.PAtoCompactAdditionEmptySuffix

#print axioms PASoundness.PAtoCompactAdditionEmptySuffix.equal_cut_empty_suffix
#print axioms PASoundness.PAtoCompactAdditionEmptySuffix.equal_cut_empty_suffix_certificate
