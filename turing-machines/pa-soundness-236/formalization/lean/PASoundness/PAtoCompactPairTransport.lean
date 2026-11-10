import PASoundness.PAtoCompactUnorderedPair

/-! Equality transport for singleton and unordered-pair membership graphs as
finite K derivations. These are ordinary equality substitution instances;
no extensionality, unique representatives or quotient is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPairTransport
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactSingleton
open PASoundness.PAtoCompactUnorderedPair
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Equal container values preserve an explicit singleton membership graph. -/
def singleton_transport (a x y q : Nat) (fresh : [a,x,y,q].Nodup) :
    KDerivation (imp (equal x y) (imp (singletonCode a x q) (singletonCode a y q))) := by
  have hxy : x ≠ y := by intro h; subst x; simp at fresh
  have hxa : x ≠ a := by intro h; subst x; simp at fresh
  have hya : y ≠ a := by intro h; subst y; simp at fresh
  have hxq : x ≠ q := by intro h; subst x; simp at fresh
  have hyq : y ≠ q := by intro h; subst y; simp at fresh
  let f := namedSingleton a x q
  have h := (CompactNamed.equalityReplace x y f
    (by simp [f, namedSingleton, namedBoth, CompactNamed.Formula.binders, hxq])
    (by simp [f, namedSingleton, namedBoth, CompactNamed.Formula.binders, hyq])).1
  simpa [f, namedSingleton, namedBoth, singletonCode, CompactNamed.Formula.encode,
    CompactNamed.replace, CompactNamed.rename, CompactProof.both, CompactProof.neg,
    hxy, hxa, hya, hxq, hyq, Ne.symm hxy, Ne.symm hxa, Ne.symm hya,
    Ne.symm hxq, Ne.symm hyq] using h

/-- Equal displayed members preserve an explicit singleton membership graph. -/
def singleton_member_transport (a c x q : Nat) (fresh : [a,c,x,q].Nodup) :
    KDerivation (imp (equal a c) (imp (singletonCode a x q) (singletonCode c x q))) := by
  have hac : a ≠ c := by intro h; subst a; simp at fresh
  have hax : a ≠ x := by intro h; subst a; simp at fresh
  have hcx : c ≠ x := by intro h; subst c; simp at fresh
  have haq : a ≠ q := by intro h; subst a; simp at fresh
  have hcq : c ≠ q := by intro h; subst c; simp at fresh
  let f := namedSingleton a x q
  have h := (CompactNamed.equalityReplace a c f
    (by simp [f, namedSingleton, namedBoth, CompactNamed.Formula.binders, haq])
    (by simp [f, namedSingleton, namedBoth, CompactNamed.Formula.binders, hcq])).1
  simpa [f, namedSingleton, namedBoth, singletonCode, CompactNamed.Formula.encode,
    CompactNamed.replace, CompactNamed.rename, CompactProof.both, CompactProof.neg,
    hac, hax, hcx, haq, hcq, Ne.symm hac, Ne.symm hax, Ne.symm hcx,
    Ne.symm haq, Ne.symm hcq] using h

/-- Equal container values preserve an explicit unordered-pair graph. -/
def pair_container_transport (a b x y q : Nat) (fresh : [a,b,x,y,q].Nodup) :
    KDerivation (imp (equal x y) (imp (pairCode a b x q) (pairCode a b y q))) := by
  have hxy : x ≠ y := by intro h; subst x; simp at fresh
  have hxa : x ≠ a := by intro h; subst x; simp at fresh
  have hya : y ≠ a := by intro h; subst y; simp at fresh
  have hxb : x ≠ b := by intro h; subst x; simp at fresh
  have hyb : y ≠ b := by intro h; subst y; simp at fresh
  have hxq : x ≠ q := by intro h; subst x; simp at fresh
  have hyq : y ≠ q := by intro h; subst y; simp at fresh
  let f := namedPair a b x q
  have h := (CompactNamed.equalityReplace x y f
    (by simp [f, namedPair, namedBoth, namedEither, CompactNamed.Formula.binders, hxq])
    (by simp [f, namedPair, namedBoth, namedEither, CompactNamed.Formula.binders, hyq])).1
  simpa [f, namedPair, namedBoth, namedEither, pairCode, CompactNamed.Formula.encode,
    CompactNamed.replace, CompactNamed.rename, CompactProof.both, CompactProof.neg,
    CompactDerivations.either, hxy, hxa, hya, hxb, hyb, hxq, hyq,
    Ne.symm hxy, Ne.symm hxa, Ne.symm hya, Ne.symm hxb, Ne.symm hyb,
    Ne.symm hxq, Ne.symm hyq] using h

/-- Equal first-coordinate values preserve an explicit unordered-pair graph. -/
def pair_first_transport (a c b x q : Nat) (fresh : [a,c,b,x,q].Nodup) :
    KDerivation (imp (equal a c) (imp (pairCode a b x q) (pairCode c b x q))) := by
  have hac : a ≠ c := by intro h; subst a; simp at fresh
  have hab : a ≠ b := by intro h; subst a; simp at fresh
  have hcb : c ≠ b := by intro h; subst c; simp at fresh
  have hax : a ≠ x := by intro h; subst a; simp at fresh
  have hcx : c ≠ x := by intro h; subst c; simp at fresh
  have haq : a ≠ q := by intro h; subst a; simp at fresh
  have hcq : c ≠ q := by intro h; subst c; simp at fresh
  let f := namedPair a b x q
  have h := (CompactNamed.equalityReplace a c f
    (by simp [f, namedPair, namedBoth, namedEither, CompactNamed.Formula.binders, haq])
    (by simp [f, namedPair, namedBoth, namedEither, CompactNamed.Formula.binders, hcq])).1
  simpa [f, namedPair, namedBoth, namedEither, pairCode, CompactNamed.Formula.encode,
    CompactNamed.replace, CompactNamed.rename, CompactProof.both, CompactProof.neg,
    CompactDerivations.either, hac, hab, hcb, hax, hcx, haq, hcq,
    Ne.symm hac, Ne.symm hab, Ne.symm hcb, Ne.symm hax, Ne.symm hcx,
    Ne.symm haq, Ne.symm hcq] using h

theorem singleton_transport_certificate (a x y q : Nat) (fresh : [a,x,y,q].Nodup) :
    theoremCode (certificate (singleton_transport a x y q fresh)) =
      imp (equal x y) (imp (singletonCode a x q) (singletonCode a y q)) :=
  certificate_correct (singleton_transport a x y q fresh)

theorem singleton_member_transport_certificate (a c x q : Nat) (fresh : [a,c,x,q].Nodup) :
    theoremCode (certificate (singleton_member_transport a c x q fresh)) =
      imp (equal a c) (imp (singletonCode a x q) (singletonCode c x q)) :=
  certificate_correct (singleton_member_transport a c x q fresh)

theorem pair_container_transport_certificate (a b x y q : Nat) (fresh : [a,b,x,y,q].Nodup) :
    theoremCode (certificate (pair_container_transport a b x y q fresh)) =
      imp (equal x y) (imp (pairCode a b x q) (pairCode a b y q)) :=
  certificate_correct (pair_container_transport a b x y q fresh)

theorem pair_first_transport_certificate (a c b x q : Nat) (fresh : [a,c,b,x,q].Nodup) :
    theoremCode (certificate (pair_first_transport a c b x q fresh)) =
      imp (equal a c) (imp (pairCode a b x q) (pairCode c b x q)) :=
  certificate_correct (pair_first_transport a c b x q fresh)

end PASoundness.PAtoCompactPairTransport

#print axioms PASoundness.PAtoCompactPairTransport.singleton_transport
#print axioms PASoundness.PAtoCompactPairTransport.singleton_member_transport
#print axioms PASoundness.PAtoCompactPairTransport.pair_container_transport
#print axioms PASoundness.PAtoCompactPairTransport.pair_first_transport
#print axioms PASoundness.PAtoCompactPairTransport.singleton_transport_certificate
#print axioms PASoundness.PAtoCompactPairTransport.singleton_member_transport_certificate
#print axioms PASoundness.PAtoCompactPairTransport.pair_container_transport_certificate
#print axioms PASoundness.PAtoCompactPairTransport.pair_first_transport_certificate
