import PASoundness.PAtoCompactKuratowskiCoordinates
import PASoundness.PAtoCompactKuratowskiSyntax

/-! The fixed-binder relational Kuratowski formula is injective in its
coordinates, as an explicit K proof transformation. Input and witness names
are capture-safe. No relation collection, equality quotient, arithmetic, or
PA proof transport follows from this theorem. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactKuratowskiInjectivity
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactSingleton
open PASoundness.PAtoCompactUnorderedPair PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactKuratowskiSyntax PASoundness.PAtoCompactKuratowskiCoordinates

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def triple (p a b s d : Nat) : CompactNamed.Formula :=
  namedBoth (namedSingleton a s 22)
    (namedBoth (namedPair a b d 22) (namedPair s d p 22))

def pairRenamed (p a b : Nat) : CompactNamed.Formula :=
  .ex 23 (.ex 24 (triple p a b 23 24))

/-- The pair relation can be alpha-renamed to witnesses 23 and 24. -/
def pair_alpha (p a b : Nat)
    (fresh : [p,a,b,20,21,22,23,24].Nodup) :
    KDerivation (imp (pairFormula p a b).encode (pairRenamed p a b).encode) := by
  have hp20 : p ≠ 20 := by intro h; subst p; simp at fresh
  have ha20 : a ≠ 20 := by intro h; subst a; simp at fresh
  have hb20 : b ≠ 20 := by intro h; subst b; simp at fresh
  have hp21 : p ≠ 21 := by intro h; subst p; simp at fresh
  have ha21 : a ≠ 21 := by intro h; subst a; simp at fresh
  have hb21 : b ≠ 21 := by intro h; subst b; simp at fresh
  let f : CompactNamed.Formula := .ex 21 (triple p a b 20 21)
  have hx : 20 ∉ f.binders := by
    simp [f, triple, namedSingleton, namedPair, namedBoth, namedEither,
      CompactNamed.Formula.binders]
  have hy : 23 ∉ f.names := by
    simp [f, triple, namedSingleton, namedPair, namedBoth, namedEither,
      CompactNamed.Formula.names]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at fresh
    aesop
  have h20 := (CompactNamed.existentialAlpha 20 23 f (by decide) hx hy).1
  let g := triple p a b 23 21
  have hgx : 21 ∉ g.binders := by
    simp [g, triple, namedSingleton, namedPair, namedBoth, namedEither,
      CompactNamed.Formula.binders]
  have hgy : 24 ∉ g.names := by
    simp [g, triple, namedSingleton, namedPair, namedBoth, namedEither,
      CompactNamed.Formula.names]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at fresh
    aesop
  have h21 := (CompactNamed.existentialAlpha 21 24 g (by decide) hgx hgy).1
  have h21lift := existsCongr 23 h21
  have h20' : KDerivation (imp (pairFormula p a b).encode
      (existsCode 23 (existsCode 21 g.encode))) := by
    simpa [f, g, pair_formula_named, triple, namedSingleton, namedPair, namedBoth, namedEither,
      CompactNamed.replace, CompactNamed.rename, CompactNamed.Formula.encode,
      CompactProof.both, CompactProof.neg, CompactDerivations.either,
      hp20,ha20,hb20,hp21,ha21,hb21] using h20
  have h21' : KDerivation (imp (existsCode 23 (existsCode 21 g.encode))
      (pairRenamed p a b).encode) := by
    simpa [g, pairRenamed, triple, namedSingleton, namedPair, namedBoth, namedEither,
      CompactNamed.replace, CompactNamed.rename, CompactNamed.Formula.encode,
      CompactProof.both, CompactProof.neg, CompactDerivations.either,
      hp20,ha20,hb20,hp21,ha21,hb21] using h21lift
  exact compose h20' h21'

/-- Exchange two assumptions in a finite K proof. -/
def exchange {A B C : Nat} (h : KDerivation (imp A (imp B C))) :
    KDerivation (imp B (imp A C)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact .mp (Context.under (Context.head [] B) A)
    (.mp (Context.head [B] A) (.closed h))

/-- Eliminate an existential in the second assumption, with the exact
vacuity proofs for the retained first assumption and the conclusion. -/
def lift_exists_second (x A B C : Nat)
    (hvA : KDerivation (imp A (allCode x A)))
    (hvC : KDerivation (imp C (allCode x C)))
    (h : KDerivation (imp A (imp B C))) :
    KDerivation (imp A (imp (existsCode x B) C)) := by
  have hi : Context [A] (imp B C) := .mp (Context.head [] A) (.closed h)
  have hv : ∀ z, z ∈ [A] → KDerivation (imp z (allCode x z)) := by
    intro z hz
    have he : z = A := by simpa only [List.mem_singleton] using hz
    cases he
    exact hvA
  have hall : Context [A] (allCode x (imp B C)) :=
    Context.generalize x hv hi
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  have hall' : Context [existsCode x B,A] (allCode x (imp B C)) :=
    Context.weaken hall (by simp)
  exact Context.existsElim hvC hall' (Context.head [A] (existsCode x B))

/-- Two relational Kuratowski graphs for one output force both input
coordinates equal. The literal named formulas use witnesses 20–22; the
second pair is alpha-renamed to 23–24 before witness elimination. -/
def pair_coordinates (p a b a' b' : Nat)
    (fresh : [p,a,b,a',b',20,21,22,23,24].Nodup) :
    KDerivation (imp (pairFormula p a b).encode (imp (pairFormula p a' b').encode
      (both (equal a a') (equal b b')))) := by
  let T1 := triple p a b 20 21
  let T2 := triple p a' b' 23 24
  let E := namedBoth (.equal a a') (.equal b b')
  have hcoords : [a,a',b,b',20,23,21,24,p,22].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at fresh ⊢
    aesop
  have hpoint : KDerivation (imp T1.encode (imp T2.encode E.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    have h1 := Context.under (Context.head [] T1.encode) T2.encode
    have h2 := Context.head [T1.encode] T2.encode
    change Context [T2.encode,T1.encode] (both (singletonCode a 20 22)
      (both (pairCode a b 21 22) (pairCode 20 21 p 22))) at h1
    change Context [T2.encode,T1.encode] (both (singletonCode a' 23 22)
      (both (pairCode a' b' 24 22) (pairCode 23 24 p 22))) at h2
    have hs := Context.conjunctionLeft h1
    have hd := Context.conjunctionLeft (Context.conjunctionRight h1)
    have hp := Context.conjunctionRight (Context.conjunctionRight h1)
    have hs' := Context.conjunctionLeft h2
    have hd' := Context.conjunctionLeft (Context.conjunctionRight h2)
    have hp' := Context.conjunctionRight (Context.conjunctionRight h2)
    change Context [T2.encode,T1.encode] (both (equal a a') (equal b b'))
    exact .mp hp' (.mp hd' (.mp hs' (.mp hp (.mp hd (.mp hs (.closed
      (coordinates a a' b b' 20 23 21 24 p 22 hcoords)))))))
  have hvT1_24 : KDerivation (imp T1.encode (allCode 24 T1.encode)) := by
    apply T1.vacuity
    simp [T1, triple, namedSingleton, namedPair, namedBoth, namedEither, CompactNamed.Formula.names]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at fresh
    aesop
  have hvT1_23 : KDerivation (imp T1.encode (allCode 23 T1.encode)) := by
    apply T1.vacuity
    simp [T1, triple, namedSingleton, namedPair, namedBoth, namedEither, CompactNamed.Formula.names]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at fresh
    aesop
  have hvE : ∀ x ∈ [20,21,23,24], KDerivation (imp E.encode (allCode x E.encode)) := by
    intro x hx
    apply E.vacuity
    simp [E, namedBoth, CompactNamed.Formula.names]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at fresh
    aesop
  let R := pairRenamed p a' b'
  have hvR20 : KDerivation (imp R.encode (allCode 20 R.encode)) := by
    apply R.vacuity
    simp [R, pairRenamed, triple, namedSingleton, namedPair, namedBoth, namedEither, CompactNamed.Formula.names]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at fresh
    aesop
  have hvR21 : KDerivation (imp R.encode (allCode 21 R.encode)) := by
    apply R.vacuity
    simp [R, pairRenamed, triple, namedSingleton, namedPair, namedBoth, namedEither, CompactNamed.Formula.names]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at fresh
    aesop
  have h24 := lift_exists_second 24 T1.encode T2.encode E.encode hvT1_24 (hvE 24 (by simp)) hpoint
  have h23 := lift_exists_second 23 T1.encode (existsCode 24 T2.encode) E.encode hvT1_23 (hvE 23 (by simp)) h24
  have h23' : KDerivation (imp T1.encode (imp R.encode E.encode)) := by
    change KDerivation (imp T1.encode (imp R.encode E.encode)) at h23
    exact h23
  have h21 := lift_exists_second 21 R.encode T1.encode E.encode hvR21 (hvE 21 (by simp)) (exchange h23')
  have h20 := lift_exists_second 20 R.encode (existsCode 21 T1.encode) E.encode hvR20 (hvE 20 (by simp)) h21
  have hfinal := exchange h20
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(pairFormula p a' b').encode,(pairFormula p a b).encode]
  have hpair1 : Context Γ (existsCode 20 (existsCode 21 T1.encode)) := by
    have h := Context.under (Context.head [] (pairFormula p a b).encode) (pairFormula p a' b').encode
    change Context Γ (existsCode 20 (existsCode 21 T1.encode)) at h
    exact h
  have hpair2 : Context Γ (pairFormula p a' b').encode := Context.head _ _
  have hfresh : [p,a',b',20,21,22,23,24].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at fresh ⊢
    aesop
  have hR : Context Γ R.encode := .mp hpair2 (.closed (pair_alpha p a' b' hfresh))
  change Context Γ E.encode
  exact .mp hR (.mp hpair1 (.closed hfinal))

theorem pair_coordinates_certificate (p a b a' b' : Nat)
    (fresh : [p,a,b,a',b',20,21,22,23,24].Nodup) :
    theoremCode (certificate (pair_coordinates p a b a' b' fresh)) =
      imp (pairFormula p a b).encode (imp (pairFormula p a' b').encode
        (both (equal a a') (equal b b'))) :=
  certificate_correct (pair_coordinates p a b a' b' fresh)

end PASoundness.PAtoCompactKuratowskiInjectivity

#print axioms PASoundness.PAtoCompactKuratowskiInjectivity.pair_coordinates
#print axioms PASoundness.PAtoCompactKuratowskiInjectivity.pair_coordinates_certificate
