import PASoundness.PAtoCompactAdditionOutputSchedule
import PASoundness.PAtoCompactAdditionOutputFixedBase

/-! Transport a supplied fixed-label output proof to arbitrary free labels and
independent allocator bases. The fixed proof remains an explicit input. -/
namespace PASoundness.PAtoCompactAdditionOutputArbitraryBases
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactAdditionOutputFrame
open PASoundness.PAtoCompactAdditionOutputSchedule PASoundness.PAtoCompactAdditionOutputFixedBase
open PASoundness.PAtoCompactAddBaseMultiAlpha PASoundness.PAtoCompactEquivMultiAlpha
open PASoundness.PAtoCompactGuardBaseTransport
set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle
attribute [local irreducible] domainAt addAt equivAt

/-- Every allocator has its own explicit free-name freshness bounds. The
input proof is the displayed base-100 fixed-label frame; free labels and
object values may coincide. -/
noncomputable def output_at_independent_bases
    (dq dr dy dx a e o x y q r : Nat)
    (hqd : q < dq + 32) (hrd : r < dr + 32) (hyd : y < dy + 32) (hxd : x < dx + 32)
    (hax : x < a + 2) (hay : y < a + 2) (haq : q < a + 2)
    (heq : q < e + 2) (her : r < e + 2)
    (hox : x < o + 2) (hoy : y < o + 2) (hor : r < o + 2)
    (hfixed : KDerivation (frame 100 30 31 32 8).encode) :
    KDerivation (imp (addAt a x y q).encode (imp (domainAt dq q).encode
      (imp (domainAt dr r).encode (imp (domainAt dy y).encode
        (imp (domainAt dx x).encode (imp (equivAt e q r).encode (addAt o x y r).encode)))))) := by
  let b := highBase x y q r
  have hb : 100 ≤ b := by dsimp [b,highBase,temporary]; omega
  have hx : x < b + 2 := by dsimp [b,highBase,temporary]; omega
  have hy : y < b + 2 := by dsimp [b,highBase,temporary]; omega
  have hq : q < b + 2 := by dsimp [b,highBase,temporary]; omega
  have hr : r < b + 2 := by dsimp [b,highBase,temporary]; omega
  have hbase : KDerivation (frame b 30 31 32 8).encode := fixed_frame_at_base b hb hfixed
  have hframe : KDerivation (frame b x y q r).encode := by
    simpa only [b] using instantiate_at_high_base x y q r hbase
  have hp : KDerivation (imp (addAt b x y q).encode (imp (domainAt b q).encode
      (imp (domainAt b r).encode (imp (domainAt b y).encode
        (imp (domainAt b x).encode (imp (equivAt b q r).encode (addAt b x y r).encode)))))) := by
    simpa only [frame,Formula.encode] using hframe
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(equivAt e q r).encode,(domainAt dx x).encode,(domainAt dy y).encode,
    (domainAt dr r).encode,(domainAt dq q).encode,(addAt a x y q).encode]
  have he : Context Γ (equivAt e q r).encode := .head _ _
  have hdX : Context Γ (domainAt dx x).encode := .hypothesis (by simp [Γ])
  have hdY : Context Γ (domainAt dy y).encode := .hypothesis (by simp [Γ])
  have hdR : Context Γ (domainAt dr r).encode := .hypothesis (by simp [Γ])
  have hdQ : Context Γ (domainAt dq q).encode := .hypothesis (by simp [Γ])
  have ha : Context Γ (addAt a x y q).encode := .hypothesis (by simp [Γ])
  have ha' : Context Γ (addAt b x y q).encode := .mp ha
    (.closed (addAt_base_alpha a b x y q hax hay haq hx hy hq).forward)
  have hdQ' : Context Γ (domainAt b q).encode := .mp hdQ
    (.closed (domainAt_transport dq b q hqd (by omega)))
  have hdR' : Context Γ (domainAt b r).encode := .mp hdR
    (.closed (domainAt_transport dr b r hrd (by omega)))
  have hdY' : Context Γ (domainAt b y).encode := .mp hdY
    (.closed (domainAt_transport dy b y hyd (by omega)))
  have hdX' : Context Γ (domainAt b x).encode := .mp hdX
    (.closed (domainAt_transport dx b x hxd (by omega)))
  have he' : Context Γ (equivAt b q r).encode := .mp he
    (.closed (equivAt_base_alpha e b q r heq her hq hr).forward)
  have ht : Context Γ (addAt b x y r).encode :=
    .mp he' (.mp hdX' (.mp hdY' (.mp hdR' (.mp hdQ' (.mp ha' (.closed hp))))))
  exact .mp ht (.closed (addAt_base_alpha b o x y r hx hy hr hox hoy hor).forward)

theorem output_at_independent_bases_certificate
    (dq dr dy dx a e o x y q r : Nat)
    (hqd : q < dq + 32) (hrd : r < dr + 32) (hyd : y < dy + 32) (hxd : x < dx + 32)
    (hax : x < a + 2) (hay : y < a + 2) (haq : q < a + 2)
    (heq : q < e + 2) (her : r < e + 2)
    (hox : x < o + 2) (hoy : y < o + 2) (hor : r < o + 2)
    (hfixed : KDerivation (frame 100 30 31 32 8).encode) :
    theoremCode (certificate (output_at_independent_bases dq dr dy dx a e o x y q r
      hqd hrd hyd hxd hax hay haq heq her hox hoy hor hfixed)) =
      imp (addAt a x y q).encode (imp (domainAt dq q).encode
        (imp (domainAt dr r).encode (imp (domainAt dy y).encode
          (imp (domainAt dx x).encode (imp (equivAt e q r).encode (addAt o x y r).encode))))) :=
  certificate_correct _
end PASoundness.PAtoCompactAdditionOutputArbitraryBases

#print axioms PASoundness.PAtoCompactAdditionOutputArbitraryBases.output_at_independent_bases
#print axioms PASoundness.PAtoCompactAdditionOutputArbitraryBases.output_at_independent_bases_certificate
