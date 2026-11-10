import PASoundness.PAtoCompactPairFresh
import PASoundness.PAtoCompactPairExistence
import PASoundness.PAtoCompactPairSingletonElim

/-! Closed K unordered-pair existence for distinct endpoint *names* with
explicit computed fresh labels. Represented endpoint values may be equal.
The repeated endpoint-name case is proved separately. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPairAuto
open PASoundness.CompactProof
open PASoundness.PAtoCompactSingletonSelector PASoundness.PAtoCompactPairSelector
open PASoundness.PAtoCompactUnorderedPair PASoundness.PAtoCompactPairFresh
open PASoundness.PAtoCompactPairExistence PASoundness.PAtoCompactPairSingletonElim

/-- K proves a pair exists using these computed witness and test names, when
its two endpoint names are distinct. -/
def distinct_pair_exists (a b : Nat) (hab : a ≠ b) :
    let r := pairTest a b
    let d := pairName a b
    KDerivation (existsCode d (pairCode a b d r)) := by
  dsimp only
  let t := point a b
  let c := pairWitness a b
  let c' := singletonWitness a b
  let q := singleTest a b
  let r := pairTest a b
  let s := singletonName a b
  let d := pairName a b
  have hn : [c,s,a,b,t,q,r,d].Nodup ∧ q ≠ c' ∧ s ≠ c' := construction_fresh a b hab
  have hlist : [pairPredicate a b t,s,a,b,t,q,r,d].Nodup := hn.1
  have hf := hn.1
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, not_false_eq_true] at hf
  have hta : t ≠ a := by aesop
  have hqt : q ≠ t := by aesop
  have hqa : q ≠ a := by aesop
  have hqc : q ≠ singletonPredicate a t := hn.2.1
  have hsa : s ≠ a := by aesop
  have hst : s ≠ t := by aesop
  have hsq : s ≠ q := by aesop
  have hsc : s ≠ singletonPredicate a t := hn.2.2
  have hsb : s ≠ b := by aesop
  have hsd : s ≠ d := by aesop
  have hsr : s ≠ r := by aesop
  have hlocal := pair_from_singleton_closed s a b t q r d hlist
  exact eliminate_singleton_for_pair a b s d q r t hta hqt hqa hqc hsa hst hsq
    hsc hsb hsd hsr hlocal

theorem distinct_pair_exists_certificate (a b : Nat) (hab : a ≠ b) :
    let r := pairTest a b
    let d := pairName a b
    theoremCode (certificate (distinct_pair_exists a b hab)) =
      existsCode d (pairCode a b d r) := certificate_correct (distinct_pair_exists a b hab)

end PASoundness.PAtoCompactPairAuto

#print axioms PASoundness.PAtoCompactPairAuto.distinct_pair_exists
#print axioms PASoundness.PAtoCompactPairAuto.distinct_pair_exists_certificate
