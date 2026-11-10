import PASoundness.PAtoCompactUnorderedPair

/-! The repeated-name unordered-pair case. A singleton of a already has the
same membership graph as the unordered pair with both endpoint names a.
This is syntactic K proof data; it does not assert uniqueness of witnesses. -/
set_option maxRecDepth 65536
namespace PASoundness.PAtoCompactPairRepeated
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactSingleton PASoundness.PAtoCompactSingletonSelector
open PASoundness.PAtoCompactUnorderedPair

/-- A singleton graph gives a pair graph with the same endpoint twice. -/
def singleton_self_pair (a s q : Nat) :
    KDerivation (imp (singletonCode a s q) (pairCode a a s q)) := by
  let M := member s q
  let E := equal q a
  let O := either E E
  let S := both (imp M E) (imp E M)
  let P := both (imp M O) (imp O M)
  have h : KDerivation (imp S P) := by
    apply Context.closeEmpty
    apply Context.deduction
    have hs : Context [S] S := Context.head [] S
    have hme : Context [S] (imp M E) := Context.conjunctionLeft hs
    have hem : Context [S] (imp E M) := Context.conjunctionRight hs
    have hmo : Context [S] (imp M O) := by
      apply Context.deduction
      have hm : Context (M :: [S]) M := Context.head _ _
      exact Context.disjunctionLeft (b := E) (.mp hm (Context.under hme M))
    have hom : Context [S] (imp O M) := by
      apply Context.deduction
      have ho : Context (O :: [S]) O := Context.head _ _
      apply Context.disjunctionElim ho
      · exact .mp (Context.head _ E) (Context.under (Context.under hem O) E)
      · exact .mp (Context.head _ E) (Context.under (Context.under hem O) E)
    exact Context.conjunctionIntro hmo hom
  exact allCongr q h

/-- K constructs an unordered pair whose endpoint names coincide. -/
def repeated_pair_exists (a : Nat) :
    let b := a+1
    let c := singletonPredicate a b
    let q := c+1
    let d := q+1
    KDerivation (existsCode d (pairCode a a d q)) := by
  dsimp only
  let b := a+1
  let c := singletonPredicate a b
  let q := c+1
  let d := q+1
  exact .mp (singleton_graph_exists a) (existsCongr d (singleton_self_pair a d q))

theorem repeated_pair_exists_certificate (a : Nat) :
    let b := a+1
    let c := singletonPredicate a b
    let q := c+1
    let d := q+1
    theoremCode (certificate (repeated_pair_exists a)) = existsCode d (pairCode a a d q) :=
  certificate_correct (repeated_pair_exists a)

end PASoundness.PAtoCompactPairRepeated

#print axioms PASoundness.PAtoCompactPairRepeated.singleton_self_pair
#print axioms PASoundness.PAtoCompactPairRepeated.repeated_pair_exists
#print axioms PASoundness.PAtoCompactPairRepeated.repeated_pair_exists_certificate
