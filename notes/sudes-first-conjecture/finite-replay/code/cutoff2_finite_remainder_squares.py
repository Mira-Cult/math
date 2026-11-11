#!/usr/bin/env python3
"""Strict finite-certificate closure, exact replay, and rejection controls."""
from itertools import permutations
from math import isqrt
from pathlib import Path
import copy
import gzip
import hashlib
import io
import json
import shutil
import struct
import subprocess
import sys
import tempfile
import zlib

ROOT = Path(__file__).resolve().parent.parent
SELF = 'code/cutoff2_finite_remainder_squares.py'
INPUT = 'inputs/cutoff2_finite_remainder_squares_inputs.json'
DATA = 'inputs/cutoff2_finite_remainder_squares_certificates.bin.gz'
VERIFY = 'code/cutoff2_finite_remainder_squares_verify.cpp'
GENERATE = 'code/cutoff2_finite_remainder_squares.cpp'
SOURCES = {
    'PROBLEM.md': '9632c547445ed661a5df4ccfdc14892a0aeaf3ed108203c08bf075df8720c023',
    'code/cutoff2_finite_remainder_squares.cpp': '5829a740e142e7a605e5a796410ed63941364b8042a7d606dd706752a2dcb69c',
    'code/cutoff2_finite_remainder_squares_verify.cpp': '60fb2cd11de8613780f7ed47abdd2d0a5707114ceaaa83e895b347fd93e058a8',
    'inputs/cutoff2_finite_remainder_squares_certificates.bin.gz': '5f8be996b548afac76e276088da5a094e3ff4375075ecea14aec77c71522b27c',
    'manuscripts/cutoff2_finite_remainder_squares.md': '66237ee26be79d9d82d1cdada0d576da0ece245e2d6a6d8613307ccdca0657e1',
}
SCHEMA = 'sude-finite-remainder-squares-v2-gzip'
PACKED_BYTES = 10500031
RAW_BYTES = 13522748
RAW_SHA = 'c8f41eb90f2a2d6d08428b5eb1d86cb373abf38467996920d9470e75045a40fd'
SCOPE = ('Exact finite certificates for every positive odd order from 1 through 1999, '
         'using each of the first n squared odd primes once and checking both diagonals; '
         'no infinite-tail theorem, independent review, or formal proof is asserted.')
PARAMETERS = {
    'first_order': 1, 'last_order': 1999, 'order_count': 1000,
    'certificate_magic': 'SUDEFR01', 'integer_encoding': 'unsigned little endian',
    'compression': {'format': 'single gzip member', 'mtime': 0, 'level': 9,
                    'header_hex': '1f8b08000000000002ff', 'compressed_bytes': PACKED_BYTES,
                    'raw_bytes': RAW_BYTES, 'raw_sha256': RAW_SHA},
    'per_order_fields': ['n:u32', 'seed:u64', 'direct:u32', 'main:u32', 'anti:u32', 'rows:u32', 'columns:u32'],
    'swap_fields': ['a:u32', 'b:u32'], 'pool_first_prime': 3,
    'prng': {'word_bits': 64, 'increment': '9e3779b97f4a7c15',
             'multiply1': 'bf58476d1ce4e5b9', 'multiply2': '94d049bb133111eb',
             'right_shifts': [30, 27, 31]},
    'compiler_flags': ['-O3', '-std=c++20', '-Wall', '-Wextra', '-pedantic'],
    'python_oracle_through': 101,
}
MASK = (1 << 64)-1


def need(ok, message):
    if not ok:
        raise ValueError(message)


def same(a, b):
    if type(a) is not type(b):
        return False
    if type(a) is dict:
        return a.keys() == b.keys() and all(same(a[k], b[k]) for k in a)
    if type(a) is list:
        return len(a) == len(b) and all(same(x, y) for x, y in zip(a, b))
    return a == b


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False).encode()


def parse_json(raw):
    def pairs(items):
        result = {}
        for k, v in items:
            need(k not in result, 'duplicate JSON key')
            result[k] = v
        return result
    def bad(value):
        raise ValueError('nonfinite JSON '+value)
    return json.loads(raw, object_pairs_hook=pairs, parse_constant=bad)


def regular(path):
    need(path.is_file() and not path.is_symlink()
         and all(not p.is_symlink() for p in path.parents), 'regular source with no symlink ancestors')
    raw = path.read_bytes()
    need(bool(raw), 'source file is not empty')
    return raw


def source_check(bindings, root=ROOT):
    need(bool(SOURCES) and type(bindings) is dict and set(bindings) == set(SOURCES)|{SELF},
         'complete exact nonempty source map')
    for name in sorted(bindings):
        h = bindings[name]
        need(type(h) is str and len(h) == 64 and all(c in '0123456789abcdef' for c in h),
             'canonical SHA-256 source digest')
        if name != SELF:
            need(h == SOURCES[name], 'fixed mathematical source identity')
        need(digest(regular(root/name)) == h, 'source bytes match manifest')


def unpack_certificate(packed):
    need(type(packed) is bytes and len(packed) == PACKED_BYTES,
         'exact compressed certificate byte count')
    need(packed[:10] == bytes.fromhex(PARAMETERS['compression']['header_hex']),
         'canonical gzip header with mtime zero and no name')
    decoder = zlib.decompressobj(31)
    # Never flush without a bound: malformed streams may expand indefinitely.
    raw = decoder.decompress(packed, RAW_BYTES+1)
    need(len(raw) == RAW_BYTES and decoder.eof and not decoder.unused_data
         and not decoder.unconsumed_tail, 'one complete gzip member with exact bounded raw size')
    need(digest(raw) == RAW_SHA, 'unchanged mathematical certificate bytes')
    return raw


def gzip_certificate(raw):
    target = io.BytesIO()
    with gzip.GzipFile(filename='', mode='wb', fileobj=target, compresslevel=9, mtime=0) as writer:
        writer.write(raw)
    return target.getvalue()


def compression_negatives(packed):
    attacks = [b'', packed[:-1], packed+b'\x00', packed+gzip_certificate(b'')]
    for offset in (0, 4, len(packed)-8):
        changed = bytearray(packed);changed[offset] ^= 1;attacks.append(bytes(changed))
    # A compact expansion beyond the exact raw bound cannot allocate beyond it.
    expansion = gzip_certificate(b'x'*(RAW_BYTES+1))
    need(len(expansion) < PACKED_BYTES, 'oversized-output rejection fixture fits compressed bound')
    attacks.append(expansion+b'\x00'*(PACKED_BYTES-len(expansion)))
    for altered in attacks:
        rejects(lambda altered=altered: unpack_certificate(altered))
    return len(attacks)


def records(raw, maximum=1999):
    need(type(raw) is bytes and type(maximum) is int and 1 <= maximum <= 1999 and maximum % 2 == 1,
         'bounded exact certificate domain')
    need(len(raw) >= 20 and raw[:8] == b'SUDEFR01', 'binary certificate header')
    need(struct.unpack_from('<III', raw, 8) == (1, maximum, (maximum+1)//2),
         'complete contiguous range header')
    result, offset = [], 20
    for expected in range(1, maximum+1, 2):
        need(offset+32 <= len(raw), 'complete per-order header')
        n, seed, *counts = struct.unpack_from('<IQ5I', raw, offset)
        need(n == expected, 'every consecutive odd order exactly once')
        swaps = sum(counts)
        if n == 1:
            need(swaps == 0, 'singleton has no swaps')
        elif n == 3:
            need(counts[0] <= 8 and swaps == counts[0], 'bounded direct order-three certificate')
        else:
            need(counts[0] == 0 and max(counts[1:3]) <= 1 and max(counts[3:]) <= n,
                 'bounded staged correction counts')
        end = offset+32+8*swaps
        need(end <= len(raw), 'complete accepted-swap sequence')
        result.append({'n': n, 'seed': seed, 'counts': counts, 'swaps': swaps,
                       'offset': offset, 'bytes': end-offset, 'sha256': digest(raw[offset:end])})
        offset = end
    need(offset == len(raw), 'no extra certificate orders or trailing bytes')
    return result


def permutation_from_record(raw, record):
    n, state = record['n'], record['seed']
    result = list(range(n*n))
    for j in range(n*n-1, 0, -1):
        state = (state+0x9e3779b97f4a7c15) & MASK
        z = state
        z = ((z ^ (z >> 30))*0xbf58476d1ce4e5b9) & MASK
        z = ((z ^ (z >> 27))*0x94d049bb133111eb) & MASK
        z ^= z >> 31
        selected = z % (j+1)
        result[j], result[selected] = result[selected], result[j]
    offset = record['offset']+32
    for _ in range(record['swaps']):
        a, b = struct.unpack_from('<II', raw, offset)
        need(0 <= a < n*n and 0 <= b < n*n and a != b, 'exact distinct Python swap positions')
        result[a], result[b] = result[b], result[a]
        offset += 8
    need(sorted(result) == list(range(n*n)), 'Python exact rank permutation')
    return result


def trial_pool(count):
    primes = [2]
    candidate = 3
    while len(primes) <= count:
        prime = True
        for p in primes:
            if p*p > candidate:
                break
            if candidate % p == 0:
                prime = False
                break
        if prime:
            primes.append(candidate)
        candidate += 2
    return primes[1:]


def trial_prime(value, primes):
    if value < 2:
        return False
    if value % 2 == 0:
        return value == 2
    for p in primes:
        if p*p > value:
            return True
        if value % p == 0:
            return value == p
    raise ValueError('independent trial-prime coverage')


def sums_of(n, values):
    return ([sum(values[r*n:(r+1)*n]) for r in range(n)]
            + [sum(values[r*n+c] for r in range(n)) for c in range(n)]
            + [sum(values[i*n+i] for i in range(n)), sum(values[i*n+n-1-i] for i in range(n))])


def python_oracle(raw, index, report):
    maximum = PARAMETERS['python_oracle_through']
    primes = trial_pool(maximum*maximum)
    checks, order_digests = 0, []
    for rec, expected in zip(index, report['orders']):
        if rec['n'] > maximum:
            break
        n = rec['n']
        ranks = permutation_from_record(raw, rec)
        values = [primes[i] for i in ranks]
        sums = sums_of(n, values)
        need(len(sums) == 2*n+2 and all(trial_prime(x, primes) for x in sums),
             'Python oracle verifies every required line exactly')
        actual = {'n': n, 'seed': rec['seed'], 'swaps': rec['swaps'],
                  'min_line': min(sums), 'max_line': max(sums), 'all_line_total': sum(sums)}
        need(same(actual, expected), 'independent Python and C++ line statistics agree')
        order_digests.append(digest(canonical({'n': n, 'pool': primes[:n*n], 'permutation': values,
                                            'line_sums': {'rows': sums[:n], 'columns': sums[n:2*n],
                                                          'diagonals': sums[-2:]}})))
        checks += len(sums)
    need(len(order_digests) == (maximum+1)//2, 'complete small-order independent oracle range')
    return {'first_order': 1, 'last_order': maximum, 'order_count': len(order_digests),
            'line_count': checks, 'canonical_certificate_digest_list_sha256': digest(canonical(order_digests))}


def compile_source(name, executable):
    compiler = shutil.which('g++')
    need(compiler is not None, 'GNU C++ compiler is required')
    command = [compiler]+PARAMETERS['compiler_flags']+[str(ROOT/name), '-o', str(executable)]
    done = subprocess.run(command, capture_output=True, text=True, timeout=120)
    need(done.returncode == 0, 'compiler failed: '+done.stderr)
    need(not done.stderr.strip(), 'unexpected compiler diagnostic: '+done.stderr)


def replay(executable, path, maximum=1999):
    done = subprocess.run([str(executable), str(path), str(maximum)], capture_output=True, text=True, timeout=600)
    need(done.returncode == 0, 'exact replay rejected: '+done.stderr)
    need(not done.stderr, 'unexpected replay diagnostic')
    report = parse_json(done.stdout)
    need(report['status'] == 'PASS_EXACT_CONTIGUOUS_PRIME_SQUARES'
         and report['first_order'] == 1 and report['last_order'] == maximum
         and [row['n'] for row in report['orders']] == list(range(1, maximum+1, 2)),
         'exact replay reports the whole requested interval')
    return report


def rejects(action):
    try:
        action()
    except (ValueError, TypeError, KeyError, OSError, UnicodeError, struct.error, IndexError, zlib.error):
        return
    raise ValueError('negative control unexpectedly accepted')


def three_record(target):
    n, seed = 3, 0
    empty = b'SUDEFR01'+struct.pack('<III', 1, 3, 2)
    empty += struct.pack('<IQ5I', 1, 0, 0, 0, 0, 0, 0)
    blank = struct.pack('<IQ5I', n, seed, 0, 0, 0, 0, 0)
    rec = {'n': n, 'seed': seed, 'offset': len(empty), 'swaps': 0}
    ranks = permutation_from_record(empty+blank, rec)
    moves = []
    for i in range(9):
        j = ranks.index(target[i])
        if i != j:
            ranks[i], ranks[j] = ranks[j], ranks[i]
            moves.append((i, j))
    return empty+struct.pack('<IQ5I', n, seed, len(moves), 0, 0, 0, 0)+b''.join(struct.pack('<II', *x) for x in moves)


def negative_certificates(raw, index, executable, temporary):
    end = index[2]['offset']+index[2]['bytes']
    small = raw[:8]+struct.pack('<III', 1, 5, 3)+raw[20:end]
    attacks = [b'', small[:7], b'WRONGFR1'+small[8:], small[:-1], small+b'\x00']
    def changed(offset, value):
        blob = bytearray(small)
        struct.pack_into('<I', blob, offset, value)
        return bytes(blob)
    attacks += [changed(8, 3), changed(12, 7), changed(16, 2), changed(20, 3),
                changed(20+12, 1), changed(index[1]['offset'], 5),
                changed(index[1]['offset']+12, 9),
                changed(index[1]['offset']+32, 9),
                changed(index[2]['offset']+24, 6)]
    # A u32 sum must not wrap to hide enormous order-three phase counts.
    overflow = bytearray(small)
    struct.pack_into('<II', overflow, index[1]['offset']+16, 0xffffffff, 1)
    attacks.append(bytes(overflow))
    same_index = bytearray(small)
    a = struct.unpack_from('<I', same_index, index[1]['offset']+32)[0]
    struct.pack_into('<I', same_index, index[1]['offset']+36, a)
    attacks.append(bytes(same_index))
    # Removing every correction is a well-formed permutation, not a prime square.
    fifth = index[2]
    no_repairs = small[:fifth['offset']]+struct.pack('<IQ5I', 5, fifth['seed'], 0, 0, 0, 0, 0)
    attacks.append(no_repairs)
    # The first actual antidiagonal correction must not use the common center.
    attacks.append(changed(fifth['offset']+32, 12))
    prime9 = trial_pool(9)
    flags = [all(v % d for d in range(2, isqrt(v)+1)) and v >= 2 for v in range(88)]
    isolated = {}
    for ranks in permutations(range(9)):
        sums = sums_of(3, [prime9[i] for i in ranks])
        if all(flags[v] for v in sums[:6]):
            if flags[sums[6]] and not flags[sums[7]]:
                isolated.setdefault('anti_only_composite', ranks)
            if flags[sums[7]] and not flags[sums[6]]:
                isolated.setdefault('main_only_composite', ranks)
        if len(isolated) == 2:
            break
    need(len(isolated) == 2, 'both isolated diagonal rejection controls found')
    tested = 0
    for blob in attacks:
        path = temporary/'negative.bin';path.write_bytes(blob)
        done = subprocess.run([str(executable), str(path), '5'], capture_output=True, text=True, timeout=20)
        need(done.returncode == 2 and 'FAIL:' in done.stderr, 'malformed or mathematically invalid certificate rejected')
        tested += 1
    for key, target in isolated.items():
        blob = three_record(target)
        path = temporary/'negative_diagonal.bin';path.write_bytes(blob)
        done = subprocess.run([str(executable), str(path), '3'], capture_output=True, text=True, timeout=20)
        need(done.returncode == 2 and 'required line sum is composite' in done.stderr,
             'isolated '+key+' is rejected on primality, not format')
        tested += 1
    return {'rejected_certificates': tested, 'isolated_diagonal_controls': sorted(isolated)}


def validate_manifest(data):
    need(type(data) is dict and set(data) == {'schema', 'scope', 'parameters', 'certificates',
                                          'exact_report', 'python_oracle', 'sources'},
         'complete exact manifest fields')
    need(data['schema'] == SCHEMA and data['scope'] == SCOPE and same(data['parameters'], PARAMETERS),
         'canonical typed manifest parameters')
    need(type(data['certificates']) is list and len(data['certificates']) == 1000,
         'all 1000 per-order certificate records are required')
    need(type(data['exact_report']) is dict and type(data['python_oracle']) is dict,
         'exact report and independent small-oracle fields')
    source_check(data['sources'])


def metadata_negatives(manifest):
    count = 0
    for key in manifest:
        bad = copy.deepcopy(manifest);del bad[key]
        rejects(lambda bad=bad: validate_manifest(bad));count += 1
    for key in PARAMETERS:
        bad = copy.deepcopy(manifest);bad['parameters'][key] = None
        rejects(lambda bad=bad: validate_manifest(bad));count += 1
    for wrong in ({}, [], None):
        rejects(lambda wrong=wrong: source_check(wrong));count += 1
    for name in manifest['sources']:
        bad = dict(manifest['sources']);del bad[name]
        rejects(lambda bad=bad: source_check(bad));count += 1
    for h in ('', '0'*63, 'X'*64, '0'*64, None, True):
        bad = dict(manifest['sources']);bad[DATA] = h
        rejects(lambda bad=bad: source_check(bad));count += 1
    rejects(lambda: source_check(dict(manifest['sources'], extra='0'*64)));count += 1
    for raw in ('', '{', '{"x":1,"x":2}', '{"x":NaN}', '{"x":Infinity}'):
        rejects(lambda raw=raw: parse_json(raw));count += 1
    for key, replacement in (('certificates', []), ('exact_report', []), ('python_oracle', [])):
        bad = copy.deepcopy(manifest);bad[key] = replacement
        rejects(lambda bad=bad: validate_manifest(bad));count += 1
    bad = copy.deepcopy(manifest);bad['parameters']['first_order'] = True
    rejects(lambda: validate_manifest(bad));count += 1
    return count


def physical_attacks(bindings, temporary):
    root = temporary/'source_attacks';root.mkdir()
    for name in bindings:
        target = root/name;target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT/name, target)
    count = 0
    for name in bindings:
        target = root/name;raw = target.read_bytes()
        for kind in ('missing', 'empty', 'changed', 'directory', 'symlink'):
            target.unlink()
            if kind == 'empty':target.write_bytes(b'')
            elif kind == 'changed':target.write_bytes(raw+b'\x00')
            elif kind == 'directory':target.mkdir()
            elif kind == 'symlink':target.symlink_to(ROOT/name)
            rejects(lambda: source_check(bindings, root));count += 1
            if target.is_symlink() or target.is_file():target.unlink()
            elif target.is_dir():target.rmdir()
            target.write_bytes(raw)
    for name in ('code', 'inputs', 'manuscripts'):
        target, backup = root/name, root/(name+'_saved')
        target.rename(backup);target.symlink_to(backup, target_is_directory=True)
        rejects(lambda: source_check(bindings, root));count += 1
        target.unlink();backup.rename(target)
    source_check(bindings, root)
    return count


def run(path, regenerate=False):
    need(__debug__, 'run without Python optimization')
    manifest_raw = regular(path);manifest = parse_json(manifest_raw.decode())
    validate_manifest(manifest)
    packed = regular(ROOT/DATA);blob = unpack_certificate(packed);index = records(blob)
    need(same(index, manifest['certificates']), 'all exact per-order offsets, seeds, swap counts and hashes agree')
    with tempfile.TemporaryDirectory(prefix='sude-finite-remainder-') as temporary_name:
        temporary = Path(temporary_name)
        executable = temporary/'verify';compile_source(VERIFY, executable)
        decoded = temporary/'certificate.bin';decoded.write_bytes(blob)
        report = replay(executable, decoded)
        need(same(report, manifest['exact_report']), 'complete freshly recomputed exact replay report agrees')
        oracle = python_oracle(blob, index, report)
        need(same(oracle, manifest['python_oracle']), 'independent small-order Python oracle agrees')
        negative = negative_certificates(blob, index, executable, temporary)
        compression = compression_negatives(packed)
        meta = metadata_negatives(manifest)
        physical = physical_attacks(manifest['sources'], temporary)
        regenerated = False
        if regenerate:
            generator = temporary/'generate';compile_source(GENERATE, generator)
            target = temporary/'regenerated.bin'
            with (temporary/'generation.jsonl').open('wb') as log:
                done = subprocess.run([str(generator), 'generate', '1999', str(target)], stdout=log,
                                      stderr=subprocess.PIPE, timeout=600)
            need(done.returncode == 0 and target.read_bytes() == blob,
                 'regenerated entire finite certificate is byte-identical')
            regenerated = True
    return {'status': 'PASS_EXACT_FINITE_REMAINDER_1_THROUGH_1999', 'scope': SCOPE,
            'exact_report': report, 'python_oracle': oracle, 'certificate_negatives': negative,
            'metadata_negative_controls': meta, 'physical_source_attacks': physical,
            'compression_negative_controls': compression, 'compressed_bytes': len(packed),
            'compressed_sha256': digest(packed),
            'certificate_bytes': len(blob), 'certificate_sha256': digest(blob),
            'required_sources': manifest['sources'], 'input_sha256': digest(manifest_raw),
            'regenerated_byte_identical': regenerated, 'infinite_tail_asserted': False,
            'independent_review_asserted': False, 'formal_proof': False}


if __name__ == '__main__':
    need(len(sys.argv) == 1 or sys.argv[1:] == ['--regenerate'], 'optional flag: --regenerate')
    print(json.dumps(run(ROOT/INPUT, len(sys.argv) == 2), indent=2, sort_keys=True, allow_nan=False))
