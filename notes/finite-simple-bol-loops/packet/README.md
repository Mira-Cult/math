# Selected construction source packet

This packet preserves selected manuscripts and supporting sources. The audit
claims apply only to the statements identified in [the catalogue](../RESULTS.md),
not to every assertion in the supplementary sources. Full class-two exhaustion
and global classification have not been audited for this release.

Frozen source: `Mira-Cult/math-wip`, commit
`27d51e6a23363d6c0ae74b2f6f752db9bb5e5847`, problem 0323.

Start with `manuscripts/odd-rigid-center-nongloop.md`. Its required interfaces are:

- `proofs/C0001.md`: canonical faithful folders, isomorphisms, quotient criterion,
  and nucleus facts.
- `proofs/C0007.md`: the inverting automorphism for a simple nonassociative quotient.
- `manuscripts/odd-folder-radicals.md`: full-inverted-set/ratio and strict-defect
  simplicity criterion.
- `manuscripts/odd-class-two-classification.md`: construction, normal-subgroup
  test and isomorphism relation. **The exhaustion theorem is not required or
  included in this release's audit claim.**
- `manuscripts/exact-factorization-criterion.md`: principal-isotope transport and
  Bruck-isotopy stabilizer test, not a claim that exact factorizations exhaust Bol loops.
- `manuscripts/odd-unbounded-derived-class.md`: the fixed-central-coordinate
  subloop lemma used for the direct Moufang witness.

The group used in the particular construction is explicitly solvable. The audit
does not need a global solvability theorem or full class-two classification to
establish this particular example.

Finite checks, from this directory:

```sh
python3 code/verify_odd_rigid_center.py
python3 code/independent_bch_section_check.py
```

The second script was newly written during the release audit; all other listed
files were copied from the frozen source. [The manifest](MANIFEST.json) records original blob IDs, original and exported
SHA-256 hashes, and omitted contextual links. Internal reviewer thread identifiers are replaced with an explicit omission label;
model names, review scopes and source revisions are preserved. Mathematical text is unchanged;
links to omitted claim/navigation or unrelated source pages are rendered as
labeled text, not inaccessible private hyperlinks. The bibliography retains its
external primary-source links. Review names in source
manuscripts identify model reviewers, not human experts.

## Additional construction packets

The other selected constructions and their source dependencies are linked from
[the results catalogue](../RESULTS.md). Included supplementary sources can discuss
stronger claims and unrelated special cases: their inclusion ensures access to
used arguments, not blanket acceptance of those claims. Local imports of the
Python checks are included. Only the three checks explicitly reported in the
release audit were rerun for this release; historical test reports remain
historical reports. No external primary-source proof is independently reproved
merely by copying a citation.
