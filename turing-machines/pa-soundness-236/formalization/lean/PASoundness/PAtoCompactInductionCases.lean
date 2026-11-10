import PASoundness.PAtoCompactLeastZero
import PASoundness.PAtoCompactLeastPredecessor

/-! Conditional, finite K induction-case composition. This does not establish
a domain, existential classification, quantified base/step schemas or
induction. Code 1 is literally `member 0 0`, not primitive falsity in an
arbitrary raw K model. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactInductionCases
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactCounterexampleSet
open PASoundness.PAtoCompactLeastCounterexample PASoundness.PAtoCompactLeastZero
open PASoundness.PAtoCompactLeastPredecessor

/-- The explicitly displayed local classification: m has the zero graph, or
this particular named y is an in-domain predecessor and m is transitive. -/
def localZeroOrPredecessor (x y m z w p q : Nat) : Nat :=
  either (zeroCode m z)
    (both (member x y) (both (successorCode y m w) (transitiveCode m p q)))

/-- At exposed names, a least counterexample is incompatible with the supplied
zero-or-specific-predecessor classification and the supplied local base and
step implications. The conclusion is literal code 1. This does not assert the
classification, leastness, a global step schema, or general induction. -/
def least_counterexample_local_cases (x t y m r z w p q : Nat) (f : CompactNamed.Formula)
    (hxt : x ≠ t) (hty : t ≠ y) (htm : t ≠ m) (hzm : z ≠ m)
    (htf : t ∉ f.binders) (hyf : y ∉ f.binders) (hmf : m ∉ f.binders)
    (hrc : r ≠ filterPredicate x t (neg f.encode)) (hrm : r ≠ m) (hry : r ≠ y)
    (hwy : w ≠ y) (hwm : w ≠ m)
    (hpm : p ≠ m) (hpy : p ≠ y) (hpq : p ≠ q) (hqm : q ≠ m) (hqy : q ≠ y) :
    let c := filterPredicate x t (neg f.encode)
    let fy := (CompactNamed.replace t y f).encode
    let fm := (CompactNamed.replace t m f).encode
    KDerivation (imp (filterGraph x c t (neg f.encode)) (imp (leastMemberCode c m r)
      (imp (localZeroOrPredecessor x y m z w p q)
        (imp (imp (zeroCode m z) fm) (imp (imp fy fm) 1))))) := by
  dsimp only
  let c := filterPredicate x t (neg f.encode)
  let fy := (CompactNamed.replace t y f).encode
  let fm := (CompactNamed.replace t m f).encode
  let G := filterGraph x c t (neg f.encode)
  let L := leastMemberCode c m r
  let Z := zeroCode m z
  let X := member x y
  let S := successorCode y m w
  let T := transitiveCode m p q
  let C := localZeroOrPredecessor x y m z w p q
  let B := imp Z fm
  let H := imp fy fm
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [H,B,C,L,G]
  have hh : Context Γ H := .hypothesis (by simp [Γ])
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have hl : Context Γ L := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  change Context Γ (either Z (both X (both S T))) at hc
  apply Context.disjunctionElim hc
  · have hz : Context (Z :: Γ) Z := Context.head Γ Z
    exact .mp (Context.under hb Z) (.mp hz (.mp (Context.under hl Z)
      (.mp (Context.under hg Z) (.closed (least_zero_contradiction x t m r z f hxt htm hzm htf hmf)))))
  · let D := both X (both S T)
    have hd : Context (D :: Γ) D := Context.head Γ D
    have hx : Context (D :: Γ) X := Context.conjunctionLeft hd
    have hst : Context (D :: Γ) (both S T) := Context.conjunctionRight hd
    have hs : Context (D :: Γ) S := Context.conjunctionLeft hst
    have ht : Context (D :: Γ) T := Context.conjunctionRight hst
    exact .mp (Context.under hh D) (.mp ht (.mp hs (.mp hx (.mp (Context.under hl D)
      (.mp (Context.under hg D) (.closed (least_predecessor_contradiction_transitive
        x t y m r w p q f hxt hty htm htf hyf hmf hrc hrm hry hwy hwm hpm hpy hpq hqm hqy)))))))

theorem least_counterexample_local_cases_certificate (x t y m r z w p q : Nat) (f : CompactNamed.Formula)
    (hxt : x ≠ t) (hty : t ≠ y) (htm : t ≠ m) (hzm : z ≠ m)
    (htf : t ∉ f.binders) (hyf : y ∉ f.binders) (hmf : m ∉ f.binders)
    (hrc : r ≠ filterPredicate x t (neg f.encode)) (hrm : r ≠ m) (hry : r ≠ y)
    (hwy : w ≠ y) (hwm : w ≠ m)
    (hpm : p ≠ m) (hpy : p ≠ y) (hpq : p ≠ q) (hqm : q ≠ m) (hqy : q ≠ y) :
    let c := filterPredicate x t (neg f.encode)
    let fy := (CompactNamed.replace t y f).encode
    let fm := (CompactNamed.replace t m f).encode
    theoremCode (certificate (least_counterexample_local_cases x t y m r z w p q f hxt hty htm hzm
      htf hyf hmf hrc hrm hry hwy hwm hpm hpy hpq hqm hqy)) =
      imp (filterGraph x c t (neg f.encode)) (imp (leastMemberCode c m r)
        (imp (localZeroOrPredecessor x y m z w p q)
          (imp (imp (zeroCode m z) fm) (imp (imp fy fm) 1)))) :=
  certificate_correct (least_counterexample_local_cases x t y m r z w p q f hxt hty htm hzm
    htf hyf hmf hrc hrm hry hwy hwm hpm hpy hpq hqm hqy)

/-- A universal refutation of the least-filter witness, if supplied as an
object-level K antecedent, combines with the existing least-counterexample
construction to refute an explicit counterexample. Establishing this universal
refutation from quantified domain/base/step hypotheses is a separate gap. -/
def refute_counterexample_from_universal (x t a u m r : Nat) (f : CompactNamed.Formula)
    (fresh : [x,t,a,u,m,r].Nodup)
    (htf : t ∉ f.binders) (haf : a ∉ f.binders)
    (hcOthers : filterPredicate x t (neg f.encode) ∉ [a,u,m,r])
    (hcf : filterPredicate x t (neg f.encode) ∉ f.names) :
    let c := filterPredicate x t (neg f.encode)
    let inst := (CompactNamed.replace t a f).encode
    let A := both (filterGraph x c t (neg f.encode)) (existsCode m (leastMemberCode c m r))
    KDerivation (imp (allCode c (neg A)) (imp (leastSubsetsCode x u t a m r)
      (imp (member x a) (imp (neg inst) 1)))) := by
  dsimp only
  let c := filterPredicate x t (neg f.encode)
  let inst := (CompactNamed.replace t a f).encode
  let A := both (filterGraph x c t (neg f.encode)) (existsCode m (leastMemberCode c m r))
  let H := allCode c (neg A)
  let L := leastSubsetsCode x u t a m r
  let X := member x a
  let N := neg inst
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [N,X,L,H]
  have hn : Context Γ N := .hypothesis (by simp [Γ])
  have hx : Context Γ X := .hypothesis (by simp [Γ])
  have hl : Context Γ L := .hypothesis (by simp [Γ])
  have hh : Context Γ H := .hypothesis (by simp [Γ])
  have hex : Context Γ (existsCode c A) :=
    .mp hn (.mp hx (.mp hl (.closed (least_counterexample_exists x t a u m r f fresh htf haf hcOthers hcf))))
  exact .mp hh hex

theorem refute_counterexample_from_universal_certificate (x t a u m r : Nat) (f : CompactNamed.Formula)
    (fresh : [x,t,a,u,m,r].Nodup)
    (htf : t ∉ f.binders) (haf : a ∉ f.binders)
    (hcOthers : filterPredicate x t (neg f.encode) ∉ [a,u,m,r])
    (hcf : filterPredicate x t (neg f.encode) ∉ f.names) :
    let c := filterPredicate x t (neg f.encode)
    let inst := (CompactNamed.replace t a f).encode
    let A := both (filterGraph x c t (neg f.encode)) (existsCode m (leastMemberCode c m r))
    theoremCode (certificate (refute_counterexample_from_universal x t a u m r f fresh htf haf hcOthers hcf)) =
      imp (allCode c (neg A)) (imp (leastSubsetsCode x u t a m r)
        (imp (member x a) (imp (neg inst) 1))) :=
  certificate_correct (refute_counterexample_from_universal x t a u m r f fresh htf haf hcOthers hcf)

end PASoundness.PAtoCompactInductionCases
