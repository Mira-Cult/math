import PASoundness.PAtoCompactAdditionZeroOperand

/-! Capture-safe simultaneous relocation of the two input labels of a
candidate-guarded addition-existence proof. This is a transformer of a
supplied finite K proof, not itself an existence proof. The inputs may alias;
the output binder must be distinct from each. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionTwoDomainRename
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactMapNamesCongr PASoundness.PAtoCompactTemplateBlockShift
open PASoundness.PAtoCompactAdditionZeroOperand
open PASoundness.PAtoCompactAdditionZeroOperand.M236AddMapOutputDesign
open PASoundness.PAtoCompactAdditionZeroOperand.M236FreshPair

def source (b out : Nat) : Formula :=
  .imp (domainAt b 30) (.imp (domainAt b 31)
    (.ex out (andF (domainAt b out) (addAt b 30 31 out))))

theorem outside_binders (b out k : Nat) (hk : k < b+2) (hne : k ≠ out) :
    k ∉ (source b out).binders := by
  intro h
  simp only [source, Formula.binders, andF_binders, Finset.mem_union,
    Finset.mem_insert] at h
  rcases h with h | h | h | h | h
  · have hh := domainAt_private b 30 k h; omega
  · have hh := domainAt_private b 31 k h; omega
  · exact hne h
  · have hh := domainAt_private b out k h; omega
  · have hh := addAt_private b 30 31 out k h; omega

theorem operand_map (b out x y : Nat) (hb : 31 < b)
    (ho0 : out ≠ 30) (ho1 : out ≠ 31) :
    mapNames (sigma x y) (source b out) =
      .imp (domainAt b x) (.imp (domainAt b y)
        (.ex out (andF (domainAt b out) (addAt b x y out)))) := by
  have hD0 := domainAt_shift (sigma x y) b b 30 (fixed_block x y b hb)
  have hD1 := domainAt_shift (sigma x y) b b 31 (fixed_block x y b hb)
  have hD := domainAt_shift (sigma x y) b b out (fixed_block x y b hb)
  have hA := addAt_shift (sigma x y) b b 30 31 out (fixed_block x y b hb)
  simp [sigma, ho0, ho1] at hD0 hD1 hD hA
  simp only [source, mapNames, mapNames_andF, sigma, ho0, ho1, if_false]
  rw [hD0, hD1, hD, hA]

/-- Simultaneously instantiate the two input names. The input names may be
identical; their denoted objects may also equal the output's denotation. -/
def rename_inputs (b out x y : Nat) (hb : 38 ≤ b) (houtlow : 32 < out)
    (_houtbound : out < b+2) (hx : x < b+2) (hy : y < b+2)
    (hxo : x ≠ out) (hyo : y ≠ out)
    (d : KDerivation (source b out).encode) :
    KDerivation (imp (domainAt b x).encode (imp (domainAt b y).encode
      (existsCode out (andF (domainAt b out) (addAt b x y out)).encode))) := by
  let f := source b out
  let u := firstFresh f x y
  let v := u+1
  have hs := fresh_pair f x y
  change 31 < u ∧ u < v ∧ x < v ∧ u ∉ f.names ∧ v ∉ f.names ∧
      u ∉ f.binders ∧ v ∉ f.binders at hs
  rcases hs with ⟨hu, huv, hxv, huN, hvN, huB, hvB⟩
  have h30 : 30 ∉ f.binders := outside_binders b out 30 (by omega) (by omega)
  have h31 : 31 ∉ f.binders := outside_binders b out 31 (by omega) (by omega)
  have hxB : x ∉ f.binders := outside_binders b out x hx hxo
  have hyB : y ∉ f.binders := outside_binders b out y hy hyo
  have k := simultaneous_derivation f u v x y h30 h31 huB hvB hxB hyB huN hvN hu huv hxv d
  change KDerivation (mapNames (sigma x y) f).encode at k
  rw [show f = source b out from rfl, operand_map b out x y (by omega) (by omega) (by omega)] at k
  exact k

theorem rename_inputs_certificate (b out x y : Nat) (hb : 38 ≤ b) (houtlow : 32 < out)
    (houtbound : out < b+2) (hx : x < b+2) (hy : y < b+2)
    (hxo : x ≠ out) (hyo : y ≠ out) (d : KDerivation (source b out).encode) :
    theoremCode (certificate (rename_inputs b out x y hb houtlow houtbound hx hy hxo hyo d)) =
      imp (domainAt b x).encode (imp (domainAt b y).encode
        (existsCode out (andF (domainAt b out) (addAt b x y out)).encode)) :=
  certificate_correct _
end PASoundness.PAtoCompactAdditionTwoDomainRename
#print axioms PASoundness.PAtoCompactAdditionTwoDomainRename.rename_inputs
#print axioms PASoundness.PAtoCompactAdditionTwoDomainRename.rename_inputs_certificate
