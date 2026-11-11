#!/usr/bin/env python3
"""Export the pinned Sude source package from existing Git objects only.

Usage: python3 export-sude-sources.py --source-repo REPO --output NEW_DIRECTORY
No network access, publication, build, generator, or replay is performed.
"""
import argparse, ast, collections, gzip, hashlib, io, json, os, re, shutil, subprocess, tarfile
from pathlib import Path

COMMIT = '927a770a92c4fb135498d73e46d8978f27ec081a'
EXPECTED_ROOT_TREE = '0b0d962fcc8fd0daa6b59532fac1f9adba600b0c'
EXPECTED_SUDE_TREE = 'f0fc5d8e02d94e20dfd3c498b70aee524c7f2b5b'
EXPECTED_MODULE_TREE = '7607df318e88a5d571dade857c6817a109441878'
PREFIX = 'formalizations/sude/'
PROBLEM = 'problems/prime-line-sums/'
EXCLUDED = {
    PREFIX+'RESEARCH_NOTES.md': 'Private running research commentary; not a proof or build input.',
    PREFIX+'handoff/HANDOFF.md': 'Obsolete historical coordination handoff; not a proof or build input.'
}
FINITE = {
    'PROBLEM.md',
    'code/cutoff2_finite_remainder_squares.cpp',
    'code/cutoff2_finite_remainder_squares.py',
    'code/cutoff2_finite_remainder_squares_verify.cpp',
    'inputs/cutoff2_finite_remainder_squares_inputs.json',
    'inputs/cutoff2_finite_remainder_squares_certificates.bin.gz',
    'manuscripts/cutoff2_finite_remainder_squares.md',
}
GENERATION_INPUTS = {
    '.python-version',
    PROBLEM+'inputs/cutoff2_finite_prefix_family_inputs.json',
    PROBLEM+'code/cutoff2_finite_prefix_family_generator.cpp',
    PROBLEM+'inputs/cutoff2_finite_target_table_data.json',
    PROBLEM+'inputs/cutoff2_finite_twin_seed_inputs.json',
}
PREPARE_SOURCE = "#!/usr/bin/env python3\n\"\"\"Verify release sources and copy them into a new original-layout scratch tree.\n\nThis does not run generators, Lean, or the finite replay. The output must not\nalready exist. No symlinks are created or accepted.\n\"\"\"\nimport argparse\nimport hashlib\nimport json\nfrom pathlib import Path\nimport shutil\n\ndef safe(root, relative):\n    rel = Path(relative)\n    if rel.is_absolute() or not rel.parts or '..' in rel.parts:\n        raise ValueError('unsafe relative path: ' + relative)\n    path = root / rel\n    if any(p.is_symlink() for p in (path, *path.parents)):\n        raise ValueError('symlink in source or destination: ' + str(path))\n    return path\n\ndef main():\n    parser = argparse.ArgumentParser(description=__doc__)\n    parser.add_argument('output', type=Path, help='new original-layout scratch directory')\n    args = parser.parse_args()\n    base = Path(__file__).resolve().parent\n    manifest = json.loads((base / 'source-manifest.json').read_text())\n    output = args.output.expanduser().absolute()\n    if output.exists() or any(p.is_symlink() for p in output.parents):\n        raise ValueError('output must be a new path without symlink ancestors')\n    rows = manifest['files']\n    seen = set()\n    for row in rows:\n        path = safe(base, row['export_path'])\n        if not path.is_file():\n            raise ValueError('missing source: ' + row['export_path'])\n        raw = path.read_bytes()\n        blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\\0' + raw).hexdigest()\n        if len(raw) != row['bytes'] or hashlib.sha256(raw).hexdigest() != row['sha256'] or blob != row['git_blob']:\n            raise ValueError('source identity mismatch: ' + row['export_path'])\n        safe(output, row['source_path'])\n        if row['source_path'] in seen:\n            raise ValueError('duplicate original path')\n        seen.add(row['source_path'])\n    output.mkdir(parents=True)\n    for row in rows:\n        dest = safe(output, row['source_path'])\n        dest.parent.mkdir(parents=True, exist_ok=True)\n        shutil.copyfile(safe(base, row['export_path']), dest)\n        dest.chmod(int(row['mode'], 8) & 0o777)\n    required = manifest['generation']['required_original_paths']\n    missing = [p for p in required if not safe(output, p).is_file()]\n    if missing:\n        raise ValueError('missing generator input: ' + repr(missing))\n    print(json.dumps({'status':'PASS_SOURCE_IDENTITIES_AND_LAYOUT', 'files':len(rows),\n                      'generator_input_paths':len(required), 'output':str(output),\n                      'executed_generators':False, 'executed_lean':False,\n                      'executed_finite_replay':False}, sort_keys=True))\n\nif __name__ == '__main__':\n    main()\n"
PACKAGE_README = "# Sude source package\n\nThis is a source export of commit 927a770a92c4fb135498d73e46d8978f27ec081a.\nThe package is prepared for release, not evidence that publication or a fresh full\nLean build has happened. The authoritative portable research narrative can be\nadded as research-writeup.md by the release editor.\n\n## Contents and trust boundary\n\n- formalization/: all 9,153 original Lean source modules, including committed\n  generated certificate source; the original generators, lockfiles, import ledger,\n  and selected technical diagnostics.\n- finite-replay/: the exact seven-file strict finite certificate replay closure\n  for all 1,000 positive odd orders below 2000. The gzip file is a mathematical\n  certificate INPUT, not a compiler cache or log.\n- regeneration-inputs/: the remaining original input/manuscript/source closure\n  referenced by the certificate generators and input source-binding manifests.\n- source-manifest.json: original paths, export paths, exact Git blobs, SHA-256,\n  upstream tree identities, exclusions, and public dependency checks.\n- prepare-regeneration.py: verify and reconstruct original relative paths in a\n  new scratch directory without running any proof or generator.\n- export-sude-sources.py: reproduce this source export from a local object-complete\n  checkout at the pinned commit; it never publishes, fetches, or changes that repo.\n\nThe Lean all-odd theorem is conditional on the explicit FiniteWitness input and\n15 published analytic propositions. The finite replay is separate executable\nverification, not a Lean discharge of FiniteWitness. No stronger claim follows\nfrom packaging or import-closure checks.\n\n## Build from the exported project\n\nWith the separately installed pinned Lean toolchain available:\n\n    cd formalization\n    lake exe cache get\n    lake build\n    lake env lean Sude/Audit.lean\n\nToolchain: leanprover/lean4:v4.33.1. The exact mathlib and eight transitive pins\nare in lake-manifest.json; all nine repositories and commit objects were checked\nas public when this package was prepared. No dependency cache is bundled.\nThese commands were NOT executed during source packaging, and no resource,\ntime, or full-build-success claim is made. Run in an isolated directory.\n\n## Finite replay\n\nWith Python 3.12.13 and a C++20 compiler installed:\n\n    python3 -B finite-replay/code/cutoff2_finite_remainder_squares.py\n\nThe source bindings have been checked during packaging; the full replay was\nnot rerun for this export. Its input manifest records the intended checks and\nscope. Do not substitute a direct verifier-only run for the strict wrapper.\n\n## Original-layout regeneration\n\nChoose a new path without symlink ancestors (on macOS use /private/tmp rather\nthan the /tmp symlink):\n\n    python3 prepare-regeneration.py /absolute/new/sude-regeneration\n\nThis copies each manifest-listed file back to its original relative path,\nincluding formalizations/sude, problems/prime-line-sums, and .python-version.\nIt preserves the original generator scripts byte for byte. Run any selected\ngenerator only inside that scratch tree, using the original instructions.\nGenerators may write or refuse to overwrite their certificate-source outputs.\nThis preparation step neither runs nor guarantees the byte-for-byte result of\nevery historical generator. Recheck generated changes and build their modules.\n\n## Historical material and licensing\n\nOnly RESEARCH_NOTES.md and handoff/HANDOFF.md are omitted from the original\nformalization subtree: they are running commentary and an obsolete handoff, not\nproof/build inputs. The original README and IMPORTS ledger are retained verbatim\nfor provenance. Some historical document links, old private commit provenance,\nand repository-integrity commands refer to the original wider research checkout;\nthey are not needed by lake build or the source reconstruction recipe. The\nportable research-writeup.md should be used as the release's current narrative.\nThe retained handoff/FWPhysicalFloorStock.lean.txt is an UNCHECKED historical draft,\nnot a Lean module in the exported build. Its preservation is not acceptance.\n\nNo source LICENSE exists in the original Sude subtree or repository root, so no\nnew license has been invented. Dependency license identifiers and public source\nlinks are recorded in source-manifest.json; dependency code/licenses are obtained\nfrom their pinned upstream packages, not vendored here. Bibliographic source\nURLs and citations in import-map.json and IMPORTS.md are preserved. No published\npaper PDF has been copied or relicensed.\n"
PUBLIC_CHECKS = json.loads("[{\"repository\":\"leanprover-community/mathlib4\",\"revision\":\"0df444a360eaa60ab8c11dca51a86af692955474\",\"resolved_sha\":\"0df444a360eaa60ab8c11dca51a86af692955474\",\"public\":true,\"license\":\"Apache-2.0\",\"url\":\"https://github.com/leanprover-community/mathlib4/commit/0df444a360eaa60ab8c11dca51a86af692955474\"},{\"repository\":\"leanprover-community/plausible\",\"revision\":\"b7eb3304aeae834b12dda98993a37f6a41f6f0bb\",\"resolved_sha\":\"b7eb3304aeae834b12dda98993a37f6a41f6f0bb\",\"public\":true,\"license\":\"Apache-2.0\",\"url\":\"https://github.com/leanprover-community/plausible/commit/b7eb3304aeae834b12dda98993a37f6a41f6f0bb\"},{\"repository\":\"leanprover-community/LeanSearchClient\",\"revision\":\"5f4d51b81cbd3f6b32b156bfad9056621a040404\",\"resolved_sha\":\"5f4d51b81cbd3f6b32b156bfad9056621a040404\",\"public\":true,\"license\":\"Apache-2.0\",\"url\":\"https://github.com/leanprover-community/LeanSearchClient/commit/5f4d51b81cbd3f6b32b156bfad9056621a040404\"},{\"repository\":\"leanprover-community/import-graph\",\"revision\":\"16f02aa7642864af59f1ff0e384a015994db9118\",\"resolved_sha\":\"16f02aa7642864af59f1ff0e384a015994db9118\",\"public\":true,\"license\":\"Apache-2.0\",\"url\":\"https://github.com/leanprover-community/import-graph/commit/16f02aa7642864af59f1ff0e384a015994db9118\"},{\"repository\":\"leanprover-community/ProofWidgets4\",\"revision\":\"4be2e3d5087eeb272cf5a8853b8f9dd025ef5957\",\"resolved_sha\":\"4be2e3d5087eeb272cf5a8853b8f9dd025ef5957\",\"public\":true,\"license\":\"Apache-2.0\",\"url\":\"https://github.com/leanprover-community/ProofWidgets4/commit/4be2e3d5087eeb272cf5a8853b8f9dd025ef5957\"},{\"repository\":\"leanprover-community/aesop\",\"revision\":\"3448c0bcc5ce01b2d1546e483ec3620e32df3d0e\",\"resolved_sha\":\"3448c0bcc5ce01b2d1546e483ec3620e32df3d0e\",\"public\":true,\"license\":\"Apache-2.0\",\"url\":\"https://github.com/leanprover-community/aesop/commit/3448c0bcc5ce01b2d1546e483ec3620e32df3d0e\"},{\"repository\":\"leanprover-community/quote4\",\"revision\":\"92c15be17b7caf78c2ad767ec40f89052d908d81\",\"resolved_sha\":\"92c15be17b7caf78c2ad767ec40f89052d908d81\",\"public\":true,\"license\":\"Apache-2.0\",\"url\":\"https://github.com/leanprover-community/quote4/commit/92c15be17b7caf78c2ad767ec40f89052d908d81\"},{\"repository\":\"leanprover-community/batteries\",\"revision\":\"4488d40d070b9700d4d5a6aa342f0d40c31b2a2d\",\"resolved_sha\":\"4488d40d070b9700d4d5a6aa342f0d40c31b2a2d\",\"public\":true,\"license\":\"Apache-2.0\",\"url\":\"https://github.com/leanprover-community/batteries/commit/4488d40d070b9700d4d5a6aa342f0d40c31b2a2d\"},{\"repository\":\"leanprover/lean4-cli\",\"revision\":\"6130a47896ce867c6a4a55373441e59e565bad0f\",\"resolved_sha\":\"6130a47896ce867c6a4a55373441e59e565bad0f\",\"public\":true,\"license\":\"MIT\",\"url\":\"https://github.com/leanprover/lean4-cli/commit/6130a47896ce867c6a4a55373441e59e565bad0f\"}]")
CHECK_DATE = '2026-11-11'

def sha(raw): return hashlib.sha256(raw).hexdigest()
def blob(raw): return hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--source-repo', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    a=ap.parse_args()
    repo=a.source_repo.resolve()
    out=a.output.expanduser().absolute()
    if out.exists() or any(p.is_symlink() for p in out.parents):
        raise ValueError('Output must be new, with no symlink ancestors.')
    env=dict(os.environ, GIT_NO_LAZY_FETCH='1', GIT_TERMINAL_PROMPT='0',
             GIT_OPTIONAL_LOCKS='0', GIT_ALLOW_PROTOCOL='')
    def git(*args):
        return subprocess.check_output(['git','-C',str(repo),*args],env=env)
    if git('rev-parse', COMMIT+'^{tree}').decode().strip()!=EXPECTED_ROOT_TREE:
        raise ValueError('Unexpected source root tree')
    if git('rev-parse',COMMIT+':'+PREFIX.rstrip('/')).decode().strip()!=EXPECTED_SUDE_TREE:
        raise ValueError('Unexpected formalization tree')
    entries={}
    for row in git('ls-tree','-rz',COMMIT).split(b'\0'):
        if not row: continue
        attrs,path=row.split(b'\t',1); mode,kind,identity=attrs.decode().split()
        if kind=='blob': entries[path.decode()]={'mode':mode,'git_blob':identity}
    source={}
    def read(path):
        if path not in source:
            if path not in entries: raise ValueError('Missing committed source path: '+path)
            source[path]=git('cat-file','blob',entries[path]['git_blob'])
        return source[path]
    upstream=sorted(p for p in entries if p.startswith(PREFIX))
    if len(upstream)!=9185: raise ValueError('Unexpected source subtree file count')
    selected=(set(upstream)-set(EXCLUDED)) | {PROBLEM+p for p in FINITE} | GENERATION_INPUTS
    while True:
        added=set()
        for p in sorted(selected):
            if p.startswith(PROBLEM) and p.endswith('.json'):
                obj=json.loads(read(p))
                bindings=obj.get('sources',{}) if isinstance(obj,dict) else {}
                for rel,want in bindings.items():
                    target=PROBLEM+rel
                    if not isinstance(want,str) or len(want)!=64:
                        raise ValueError('Unsupported source binding: '+p)
                    if sha(read(target))!=want: raise ValueError('Input source binding mismatch: '+target)
                    added.add(target)
        if added<=selected:break
        selected |= added
    # Stream all selected immutable blobs in one cat-file process. This does not fetch.
    process=subprocess.Popen(['git','-C',str(repo),'cat-file','--batch'],
        stdin=subprocess.PIPE,stdout=subprocess.PIPE,env=env)
    for p in sorted(selected):
        if p in source:continue
        process.stdin.write((entries[p]['git_blob']+'\n').encode());process.stdin.flush()
        header=process.stdout.readline().decode().split()
        if len(header)!=3 or header[1]!='blob':
            raise ValueError('Source object unavailable locally: '+p)
        raw=process.stdout.read(int(header[2]))
        if process.stdout.read(1)!=b'\n':raise ValueError('Malformed Git batch stream')
        if blob(raw)!=entries[p]['git_blob']:raise ValueError('Git object identity mismatch')
        source[p]=raw
    process.stdin.close()
    if process.wait()!=0:raise ValueError('Git source read failed')
    def exported(p):
        if p.startswith(PREFIX):return 'formalization/'+p[len(PREFIX):]
        if p.startswith(PROBLEM) and p[len(PROBLEM):] in FINITE:
            return 'finite-replay/'+p[len(PROBLEM):]
        if p=='.python-version':return p
        return 'regeneration-inputs/'+p
    records=[]
    findings=[]
    patterns={
      'private_key':r'-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----',
      'github_token':r'\b(?:gh[pousr]_[A-Za-z0-9]{30,}|github_pat_[A-Za-z0-9_]{40,})',
      'cloud_access_key':r'\b(?:AKIA|ASIA)[A-Z0-9]{16}\b',
      'secret_assignment':r'(?i)(?:password|api_key|client_secret|access_token)\s*[=:]\s*["\'][^"\'\s]{12,}["\']',
      'personal_machine_path':r'/(?:Users|home)/[^/\s]+/',
      'private_service_url':r'https?://[^\s)\]>"]*(?:math-wip|chatgpt\.com/c/|codex://)[^\s)\]>"]*'
    }
    private_urls=[]; absolute_paths=[]
    mods={p[len(PREFIX):-5].replace('/','.') : p for p in selected if p.startswith(PREFIX) and p.endswith('.lean')}
    edges={};external=set();missing={}
    for p in sorted(selected):
        raw=source[p]
        if blob(raw)!=entries[p]['git_blob']:raise ValueError('Source bytes changed: '+p)
        records.append(dict(source_path=p,export_path=exported(p),bytes=len(raw),sha256=sha(raw),**entries[p]))
        try:t=raw.decode()
        except UnicodeDecodeError:continue
        for number,line in enumerate(t.splitlines(),1):
            for category,pattern in patterns.items():
                if re.search(pattern,line):
                    findings.append({'file':exported(p),'line':number,'category':category})
        if p.startswith(PREFIX) and p.endswith('.lean'):
            m=p[len(PREFIX):-5].replace('/','.')
            imports=[]
            # Static import-line inventory only, not a Lean build or parser certification.
            for line in t.splitlines():
                mat=re.match(r'^\s*(?:public\s+)?import\s+(.+)',line)
                if mat:
                    for item in mat[1].split('--')[0].split():
                        if item in ('all','public','private') or not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*',item):continue
                        imports.append(item)
                        if item.startswith('Sude.'):
                            if item not in mods:missing.setdefault(item,[]).append(m)
                        elif item!='Sude':external.add(item)
            edges[m]=imports
    if missing:raise ValueError('Unresolved internal imports: '+repr(missing))
    if findings:raise ValueError('Publication safety findings require review: '+json.dumps(findings))
    closure=set();todo=['Sude']
    while todo:
        m=todo.pop()
        if m in closure:continue
        closure.add(m);todo.extend(x for x in edges.get(m,[]) if x in mods)
    out.mkdir(parents=True)
    for row in records:
        dest=out/row['export_path'];dest.parent.mkdir(parents=True,exist_ok=True)
        dest.write_bytes(source[row['source_path']])
        dest.chmod(int(row['mode'],8)&0o777)
    (out/'prepare-regeneration.py').write_text(PREPARE_SOURCE)
    (out/'SOURCE-PACKAGE.md').write_text(PACKAGE_README)
    shutil.copyfile(Path(__file__).resolve(),out/'export-sude-sources.py')
    exclusions=[]
    for p,why in EXCLUDED.items():
        raw=read(p)
        exclusions.append(dict(source_path=p,reason=why,bytes=len(raw),sha256=sha(raw),**entries[p]))
    input_checks=sum(len(json.loads(source[p]).get('sources',{})) for p in selected if p.startswith(PROBLEM) and p.endswith('.json'))
    manifest={
      'schema':'sude-source-export-v1',
      'source_commit':COMMIT,
      'source_root_tree':EXPECTED_ROOT_TREE,
      'source_formalization_tree':EXPECTED_SUDE_TREE,
      'source_module_tree':EXPECTED_MODULE_TREE,
      'source_subtree':{'path':PREFIX.rstrip('/'),'files':9185,'bytes':69887589,'lean_files':9153},
      'export_source_totals':{'files':len(records),'bytes':sum(r['bytes'] for r in records),
        'formalization_files':sum(r['export_path'].startswith('formalization/') for r in records),
        'finite_replay_files':sum(r['export_path'].startswith('finite-replay/') for r in records),
        'regeneration_input_files':sum(r['export_path'].startswith('regeneration-inputs/') for r in records)},
      'metadata_files':['SOURCE-PACKAGE.md','prepare-regeneration.py','export-sude-sources.py','source-manifest.json'],
      'files':records,'excluded':exclusions,
      'unchecked_historical_source':['formalization/handoff/FWPhysicalFloorStock.lean.txt'],
      'static_validation':{'internal_module_count':len(mods),'default_root_import_closure':len(closure),
        'missing_internal_imports':missing,'external_modules':sorted(external),
        'input_manifest_source_bindings_verified':input_checks,
        'publication_safety_scan_findings':findings,'publication_safety_scan_scope':list(patterns),
        'lean_build_performed':False,'finite_replay_performed':False,'generators_run':False},
      'generation':{'required_original_paths':sorted(GENERATION_INPUTS),
        'method':'prepare-regeneration.py reconstructs original paths without changing original scripts.'},
      'public_dependencies':{'checked_date_utc':CHECK_DATE,'packages':PUBLIC_CHECKS,
        'toolchain':'leanprover/lean4:v4.33.1',
        'release_url':'https://github.com/leanprover/lean4/releases/tag/v4.33.1',
        'all_commits_resolved_publicly':True,'vendored':False},
      'license_note':'No LICENSE in the source formalization subtree or source repository root; no new license assigned.',
      'limitations':['Static source/package checks are not a Lean build or mathematical review.',
        'FiniteWitness and the 15 analytic inputs remain explicit hypotheses.',
        'Historical retained source documents contain wider-checkout relative links and integrity commands; use the portable research writeup for the release narrative.',
        'Source reconstruction does not prove that every historical generator regenerates every committed certificate byte for byte.',
        'No compiled product, dependency cache, original Git metadata, private running commentary, or raw build log is included.']
    }
    (out/'source-manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
    archive=out.with_suffix('.tar.gz')
    if archive.exists():raise ValueError('Archive path already exists')
    with archive.open('wb') as target:
      with gzip.GzipFile(filename='',mode='wb',fileobj=target,mtime=0) as gz:
        with tarfile.open(fileobj=gz,mode='w',format=tarfile.PAX_FORMAT) as tar:
          for p in sorted(out.rglob('*')):
            if not p.is_file():continue
            info=tar.gettarinfo(str(p),arcname=out.name+'/'+str(p.relative_to(out)))
            info.uid=info.gid=0;info.uname=info.gname='';info.mtime=0
            with p.open('rb') as f:tar.addfile(info,f)
    print(json.dumps({'status':'PASS_SOURCE_EXPORT','source_files':len(records),
      'source_bytes':sum(r['bytes'] for r in records),'release_file_count':len(records)+4,
      'release_uncompressed_bytes':sum(p.stat().st_size for p in out.rglob('*') if p.is_file()),
      'archive':str(archive),'archive_bytes':archive.stat().st_size,'archive_sha256':sha(archive.read_bytes()),
      'manifest_sha256':sha((out/'source-manifest.json').read_bytes())},sort_keys=True))

if __name__=='__main__':main()
