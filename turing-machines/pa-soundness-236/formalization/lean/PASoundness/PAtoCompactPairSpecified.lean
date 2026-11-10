import PASoundness.PAtoCompactPairAllFresh
import PASoundness.PAtoCompactPairAlpha

/-! Unordered-pair existence with caller-specified capture-safe binder names.
Two intermediate fresh names avoid every collision with automatically selected
source labels and the final labels. No uniqueness, graph collection, quotient,
or PA interpretation is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPairSpecified
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactUnorderedPair PASoundness.PAtoCompactPairAlpha
open PASoundness.PAtoCompactPairAll PASoundness.PAtoCompactPairAllFresh

/-- The pair graph exists with any specified distinct witness and test labels
that avoid the endpoint names. The endpoint names a and b may coincide. -/
def pair_exists_with_names (a b d q : Nat)
    (hda : d ≠ a) (hdb : d ≠ b) (hdq : d ≠ q)
    (hqa : q ≠ a) (hqb : q ≠ b) :
    KDerivation (existsCode d (pairCode a b d q)) := by
  let w := witnessName a b
  let v := testName a b
  let t := a+b+w+v+d+q+1
  let s := t+1
  have hf := pair_names_fresh a b
  have hva : v ≠ a := hf.1
  have hvb : v ≠ b := hf.2.1
  have hwa : w ≠ a := hf.2.2.1
  have hwb : w ≠ b := hf.2.2.2.1
  have hwv : w ≠ v := hf.2.2.2.2
  have htw : t ≠ w := by dsimp [t]; omega
  have htv : t ≠ v := by dsimp [t]; omega
  have hta : t ≠ a := by dsimp [t]; omega
  have htb : t ≠ b := by dsimp [t]; omega
  have htd : t ≠ d := by dsimp [t]; omega
  have htq : t ≠ q := by dsimp [t]; omega
  have hst : s ≠ t := by dsimp [s]; omega
  have hsw : s ≠ w := by dsimp [s,t]; omega
  have hsa : s ≠ a := by dsimp [s,t]; omega
  have hsb : s ≠ b := by dsimp [s,t]; omega
  have hsd : s ≠ d := by dsimp [s,t]; omega
  have hsq : s ≠ q := by dsimp [s,t]; omega
  have h₁ : KDerivation (existsCode w (pairCode a b w t)) :=
    .mp (pair_exists a b) (pair_exists_test_alpha a b w v t hva hvb (Ne.symm hwv)
      htv hta htb htw)
  have h₂ : KDerivation (existsCode s (pairCode a b s t)) :=
    .mp h₁ (pair_witness_alpha a b w s t hwa hwb (Ne.symm htw) hsw hsa hsb hst)
  have h₃ : KDerivation (existsCode s (pairCode a b s q)) :=
    .mp h₂ (pair_exists_test_alpha a b s t q hta htb (Ne.symm hst)
      (Ne.symm htq) hqa hqb (Ne.symm hsq))
  exact .mp h₃ (pair_witness_alpha a b s d q hsa hsb hsq (Ne.symm hsd) hda hdb hdq)

theorem pair_exists_with_names_certificate (a b d q : Nat)
    (hda : d ≠ a) (hdb : d ≠ b) (hdq : d ≠ q)
    (hqa : q ≠ a) (hqb : q ≠ b) :
    theoremCode (certificate (pair_exists_with_names a b d q hda hdb hdq hqa hqb)) =
      existsCode d (pairCode a b d q) :=
  certificate_correct (pair_exists_with_names a b d q hda hdb hdq hqa hqb)

end PASoundness.PAtoCompactPairSpecified

#print axioms PASoundness.PAtoCompactPairSpecified.pair_exists_with_names
#print axioms PASoundness.PAtoCompactPairSpecified.pair_exists_with_names_certificate
