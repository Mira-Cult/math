import PASoundness.PAtoCompactKuratowskiSpecified

/-! Prescribed-name K Kuratowski existence without reserving the source
output label 19: it is first moved to a temporary fresh name. The internal
fixed binders 20–22 remain reserved. No graph collection or quotient property
is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactKuratowskiAnyNames
open PASoundness.CompactProof PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactKuratowskiExists
open PASoundness.PAtoCompactKuratowskiSpecified

/-- K constructs a represented Kuratowski pair using prescribed endpoint
names and output binder. All three avoid internal binders 20–22; d differs
from a and b. The endpoint names may coincide, and may equal 19. -/
def pair_exists_with_names (a b d : Nat)
    (ha20 : a ≠ 20) (ha21 : a ≠ 21) (ha22 : a ≠ 22)
    (hb20 : b ≠ 20) (hb21 : b ≠ 21) (hb22 : b ≠ 22)
    (hda : d ≠ a) (hdb : d ≠ b) (hd20 : d ≠ 20) (hd21 : d ≠ 21) (hd22 : d ≠ 22) :
    KDerivation (existsCode d (pairFormula d a b).encode) := by
  let w := a+b+d+50
  let p := w+1
  have hw2 : w ≠ 2 := by dsimp [w]; omega
  have hw3 : w ≠ 3 := by dsimp [w]; omega
  have hw20 : w ≠ 20 := by dsimp [w]; omega
  have hw21 : w ≠ 21 := by dsimp [w]; omega
  have hw22 : w ≠ 22 := by dsimp [w]; omega
  have hwa : w ≠ a := by dsimp [w]; omega
  have hwb : w ≠ b := by dsimp [w]; omega
  have hpw : p ≠ w := by dsimp [p]; omega
  have hp2 : p ≠ 2 := by dsimp [p,w]; omega
  have hp3 : p ≠ 3 := by dsimp [p,w]; omega
  have hp19 : p ≠ 19 := by dsimp [p,w]; omega
  have hp20 : p ≠ 20 := by dsimp [p,w]; omega
  have hp21 : p ≠ 21 := by dsimp [p,w]; omega
  have hp22 : p ≠ 22 := by dsimp [p,w]; omega
  have hpa : p ≠ a := by dsimp [p,w]; omega
  have hpb : p ≠ b := by dsimp [p,w]; omega
  have hpd : p ≠ d := by dsimp [p,w]; omega
  have h₀ : KDerivation (existsCode p (pairFormula p 2 3).encode) :=
    rename_output 19 p 2 3 (Ne.symm hp19) (by decide) (by decide)
      (by decide) (by decide) (by decide) hp2 hp3 hp20 hp21 hp22 pair_exists
  have h₁ : KDerivation (existsCode p (pairFormula p w 3).encode) := by
    have h := rename_endpoint 2 w p 2 3 (Ne.symm hw2) (Ne.symm hp2) (Ne.symm hpw)
      (by decide) (by decide) (by decide) hw20 hw21 hw22 h₀
    simpa [rename] using h
  have h₂ : KDerivation (existsCode p (pairFormula p w b).encode) := by
    by_cases hb3 : b = 3
    · simpa [hb3] using h₁
    · have h := rename_endpoint 3 b p w 3 (Ne.symm hb3) (Ne.symm hp3) (Ne.symm hpb)
        (by decide) (by decide) (by decide) hb20 hb21 hb22 h₁
      simpa [rename, hw3] using h
  have h₃ : KDerivation (existsCode p (pairFormula p a b).encode) := by
    have h := rename_endpoint w a p w b hwa (Ne.symm hpw) (Ne.symm hpa) hw20 hw21 hw22
      ha20 ha21 ha22 h₂
    simpa [rename, hwb, Ne.symm hwb] using h
  exact rename_output p d a b hpd hpa hpb hp20 hp21 hp22 hda hdb hd20 hd21 hd22 h₃

theorem pair_exists_with_names_certificate (a b d : Nat)
    (ha20 : a ≠ 20) (ha21 : a ≠ 21) (ha22 : a ≠ 22)
    (hb20 : b ≠ 20) (hb21 : b ≠ 21) (hb22 : b ≠ 22)
    (hda : d ≠ a) (hdb : d ≠ b) (hd20 : d ≠ 20) (hd21 : d ≠ 21) (hd22 : d ≠ 22) :
    theoremCode (certificate (pair_exists_with_names a b d ha20 ha21 ha22
      hb20 hb21 hb22 hda hdb hd20 hd21 hd22)) = existsCode d (pairFormula d a b).encode :=
  certificate_correct (pair_exists_with_names a b d ha20 ha21 ha22
    hb20 hb21 hb22 hda hdb hd20 hd21 hd22)

end PASoundness.PAtoCompactKuratowskiAnyNames

#print axioms PASoundness.PAtoCompactKuratowskiAnyNames.pair_exists_with_names
#print axioms PASoundness.PAtoCompactKuratowskiAnyNames.pair_exists_with_names_certificate
