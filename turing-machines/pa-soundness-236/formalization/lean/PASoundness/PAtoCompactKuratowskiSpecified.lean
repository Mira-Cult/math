import PASoundness.PAtoCompactKuratowskiExists
import PASoundness.PAtoCompactKuratowskiRename

/-! Transport the fixed-name K Kuratowski existence proof to arbitrary
capture-safe endpoint and output names. No pair collection or quotient is
constructed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactKuratowskiSpecified
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactKuratowskiFresh
open PASoundness.PAtoCompactKuratowskiRename PASoundness.PAtoCompactKuratowskiExists
open PASoundness.PAtoCompactKuratowskiSyntax PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactSingleton PASoundness.PAtoCompactUnorderedPair
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Rename a free variable in a proved existential Kuratowski graph, provided
the source and target do not collide with its four binders. -/
def rename_endpoint (x y p a b : Nat)
    (hxy : x ≠ y) (hxp : x ≠ p) (hyp : y ≠ p)
    (hx20 : x ≠ 20) (hx21 : x ≠ 21) (hx22 : x ≠ 22)
    (hy20 : y ≠ 20) (hy21 : y ≠ 21) (hy22 : y ≠ 22)
    (h : KDerivation (existsCode p (pairFormula p a b).encode)) :
    KDerivation (existsCode p (pairFormula p (rename x y a) (rename x y b)).encode) := by
  let f : Formula := .ex p (pairFormula p a b)
  have hi := universalInstance x y f hxy
    (by simp [f, Formula.binders, pair_binders, hxp, hx20, hx21, hx22])
    (by simp [f, Formula.binders, pair_binders, hyp, hy20, hy21, hy22])
  have hi' : KDerivation (imp (allCode x f.encode)
      (existsCode p (pairFormula p (rename x y a) (rename x y b)).encode)) := by
    simpa [f, Formula.encode, replace, replace_pair, rename,
      hxp, Ne.symm hxp, hx20, hx21, hx22] using hi
  exact .mp (.generalize x h) hi'

/-- K alpha-renames the output binder in the displayed pair-existence formula. -/
def rename_output (p d a b : Nat)
    (hpd : p ≠ d) (hpa : p ≠ a) (hpb : p ≠ b)
    (hp20 : p ≠ 20) (hp21 : p ≠ 21) (hp22 : p ≠ 22)
    (hda : d ≠ a) (hdb : d ≠ b) (hd20 : d ≠ 20) (hd21 : d ≠ 21) (hd22 : d ≠ 22)
    (h : KDerivation (existsCode p (pairFormula p a b).encode)) :
    KDerivation (existsCode d (pairFormula d a b).encode) := by
  let f := pairFormula p a b
  have hi := (existentialAlpha p d f hpd
    (by simp [f, pair_binders, hp20, hp21, hp22])
    (by simp [f, pair_formula_named, namedSingleton, namedPair, namedBoth,
      namedEither, Formula.names, Ne.symm hpd, hda, hdb, hd20, hd21, hd22])).1
  have hi' : KDerivation (imp (existsCode p f.encode)
      (existsCode d (pairFormula d a b).encode)) := by
    simpa [f, replace_pair, rename, hpd, hpa, hpb, hp20, hp21, hp22,
      Ne.symm hpd, Ne.symm hpa, Ne.symm hpb, hda, hdb] using hi
  exact .mp h hi'

/-- From the fixed 2,3/19 pair theorem, construct the literal Kuratowski
pair formula with caller-selected endpoint and existential output names.
All displayed names avoid internal binders 20–22; endpoints may coincide. -/
def pair_exists_with_names (a b d : Nat)
    (ha19 : a ≠ 19) (ha20 : a ≠ 20) (ha21 : a ≠ 21) (ha22 : a ≠ 22)
    (hb19 : b ≠ 19) (hb20 : b ≠ 20) (hb21 : b ≠ 21) (hb22 : b ≠ 22)
    (hda : d ≠ a) (hdb : d ≠ b) (hd20 : d ≠ 20) (hd21 : d ≠ 21) (hd22 : d ≠ 22) :
    KDerivation (existsCode d (pairFormula d a b).encode) := by
  let w := a+b+d+50
  have hw2 : w ≠ 2 := by dsimp [w]; omega
  have hw3 : w ≠ 3 := by dsimp [w]; omega
  have hw19 : w ≠ 19 := by dsimp [w]; omega
  have hw20 : w ≠ 20 := by dsimp [w]; omega
  have hw21 : w ≠ 21 := by dsimp [w]; omega
  have hw22 : w ≠ 22 := by dsimp [w]; omega
  have hwa : w ≠ a := by dsimp [w]; omega
  have hwb : w ≠ b := by dsimp [w]; omega
  have h₁ : KDerivation (existsCode 19 (pairFormula 19 w 3).encode) := by
    have h := rename_endpoint 2 w 19 2 3 (Ne.symm hw2) (by decide) hw19
      (by decide) (by decide) (by decide) hw20 hw21 hw22 pair_exists
    simpa [rename] using h
  have h₂ : KDerivation (existsCode 19 (pairFormula 19 w b).encode) := by
    by_cases hb3 : b = 3
    · simpa [hb3] using h₁
    · have h := rename_endpoint 3 b 19 w 3 (Ne.symm hb3) (by decide) hb19
        (by decide) (by decide) (by decide) hb20 hb21 hb22 h₁
      simpa [rename, hw3] using h
  have h₃ : KDerivation (existsCode 19 (pairFormula 19 a b).encode) := by
    have h := rename_endpoint w a 19 w b hwa hw19 ha19 hw20 hw21 hw22
      ha20 ha21 ha22 h₂
    simpa [rename, hwb, Ne.symm hwb] using h
  by_cases hd19 : d = 19
  · simpa [hd19] using h₃
  · exact rename_output 19 d a b (Ne.symm hd19) (Ne.symm ha19) (Ne.symm hb19)
      (by decide) (by decide) (by decide) hda hdb hd20 hd21 hd22 h₃

theorem pair_exists_with_names_certificate (a b d : Nat)
    (ha19 : a ≠ 19) (ha20 : a ≠ 20) (ha21 : a ≠ 21) (ha22 : a ≠ 22)
    (hb19 : b ≠ 19) (hb20 : b ≠ 20) (hb21 : b ≠ 21) (hb22 : b ≠ 22)
    (hda : d ≠ a) (hdb : d ≠ b) (hd20 : d ≠ 20) (hd21 : d ≠ 21) (hd22 : d ≠ 22) :
    theoremCode (certificate (pair_exists_with_names a b d ha19 ha20 ha21 ha22
      hb19 hb20 hb21 hb22 hda hdb hd20 hd21 hd22)) =
      existsCode d (pairFormula d a b).encode :=
  certificate_correct (pair_exists_with_names a b d ha19 ha20 ha21 ha22
    hb19 hb20 hb21 hb22 hda hdb hd20 hd21 hd22)

end PASoundness.PAtoCompactKuratowskiSpecified

#print axioms PASoundness.PAtoCompactKuratowskiSpecified.rename_endpoint
#print axioms PASoundness.PAtoCompactKuratowskiSpecified.rename_output
#print axioms PASoundness.PAtoCompactKuratowskiSpecified.pair_exists_with_names
#print axioms PASoundness.PAtoCompactKuratowskiSpecified.pair_exists_with_names_certificate
