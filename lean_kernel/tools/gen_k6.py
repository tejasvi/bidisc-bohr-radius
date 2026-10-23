#!/usr/bin/env python3
"""K6 module generator (kernel-only S({0..6}) <= 2.363, hints as data).

Reads the frozen bb6/sh0..sh47.json, deduplicates the vertex keys over all shards (the first certificate of a key wins;
every certificate of a key certifies the same vertex), orders the distinct vertices by first use (root cells in index
order, leaves in walk order, keys in product order), computes the fixed-point hints with the k6hints helper (untrusted:
any hints are sound, the kernel checks them exactly) and writes

  Bohr59aK6V/<TAG>Vnnnn.lean  theorem w<TAG>_<idx> : vertexOKKh trigTT 6 2363 1000 KEY Y W X = true := by decide +kernel
  Bohr59aK6C/<TAG>Pnnnn.lean  def kc6_<i>_<p>_<c> (<= 81 keys of leaf p of cell i) and its linking theorem cv6_<i>_<p>_<c>
  Bohr59aK6C/Cnnn.lean        tree6_<i>, lv6_<i>_<p> (allP_app over the leaf's chunks), kls6_<i> (one key list per leaf),
                              cellw6_<i> (walkK2, decide +kernel), cellv6_<i> : allP (allP (fun key => ∃ Y Wr x,
                              vertexOKKh trigTT 6 2363 1000 key Y Wr x = true)) kls6_<i>

Negative integers are written as `Int.negSucc k` (much cheaper to elaborate than `-n`); every key literal comes from one
formatter, so the key in kls6_<i> is byte-identical to the key in its w_ statement.

usage: gen_k6.py FROZEN_DIR OUT_DIR K6HINTS_BIN NPROC PER_V PER_C FIRST:NCELLS:TAG[,FIRST:NCELLS:TAG...]
The shards are loaded once; each block (FIRST, NCELLS) is self-contained: its vertices are deduplicated and numbered
within the block, written as Bohr59aK6V/<TAG>Vnnnn.lean with theorems w<TAG>_<idx> (vertices on block boundaries are
certified once per block), its key chunks as Bohr59aK6C/<TAG>Pnnnn.lean (kc6_<i>_<leaf>_<chunk>, cv6_<i>_<leaf>_<chunk>)
and its root cells as Bohr59aK6C/Cnnn.lean (cell module index = cell index / PER_C, so FIRST must be a multiple of PER_C).
"""
import gc, hashlib, itertools, json, multiprocessing as mp, os, subprocess, sys
from fractions import Fraction

if sys.flags.optimize:
    sys.exit('refusing to run with python -O')

K, N0, D, NSH = 6, 8, 5, 48
BNUM, BDEN = 2363, 1000


def die(msg):
    sys.exit('GEN FAILED: ' + msg)


def comp_of_json(kk):
    if isinstance(kk, list) and len(kk) == 2 and kk[0] == 'c':
        q = Fraction(kk[1]); tan, j = False, 0
    elif isinstance(kk, list) and len(kk) == 3 and kk[0] == 't':
        q, h = Fraction(kk[1]), Fraction(kk[2]); tan = True
        if not (0 < h <= Fraction(1, 4)) or h.numerator != 1 or h.denominator & (h.denominator - 1):
            die('tangent half-width not 1/2^j in (0, 1/4]: %s' % (kk,))
        j = h.denominator.bit_length() - 1
    else:
        die('bad key component %s' % (kk,))
    m = q * 512
    if m.denominator != 1 or not (-512 <= m.numerator <= 512) or j > 9:
        die('key component out of range %s' % (kk,))
    return (tan, m.numerator, j)


def y_ints(y):
    """y at scale 2^128; values not on that grid are rounded to nearest: returns the integers and the largest rounding
    change (None if all exact). Any y is sound, since the kernel re-checks every inequality exactly for the y it is given"""
    if not (isinstance(y, list) and len(y) == 2 * K and all(isinstance(v, float) for v in y)):
        die('bad y')
    out, dmax = [], None
    for v in y:
        f = Fraction(*v.as_integer_ratio()) * 2 ** 128
        if f.denominator != 1:
            r = round(f)
            d = abs(f - r) / 2 ** 128
            dmax = d if dmax is None else max(dmax, d)
            out.append(int(r))
        else:
            out.append(f.numerator)
    return out, dmax


def load_shard(arg):
    """one shard: header checks, its root cells, and its first certificate of each key (in file order)"""
    frozen, s = arg
    path = os.path.join(frozen, 'bb6', 'sh%d.json' % s)
    raw = open(path, 'rb').read()
    sha = hashlib.sha256(raw).hexdigest()
    sh = json.loads(raw)
    del raw
    if not (sh['k'] == K and sh['n0'] == N0 and sh['nshards'] == NSH and sh['shard'] == s):
        die('bad shard header %d' % s)
    cells = {}
    for key_, tree in sh['cells'].items():
        i = int(key_)
        if i % NSH != s or i in cells:
            die('bad or duplicate root cell %d' % i)
        cells[i] = tree
    seen, ents = set(), []
    for ent in sh['verts']:
        key = tuple(comp_of_json(kk) for kk in ent[0])
        if len(key) != D:
            die('bad key length')
        if key not in seen:
            seen.add(key)
            y, d = y_ints(ent[1])
            ents.append((key, y, d))
    return s, sha, cells, ents


def opts(m, j):
    return [(False, m - 2 ** (9 - j), 0), (False, m + 2 ** (9 - j), 0), (True, m, j)]


def walk(node, ms, js, out, depth=0):
    """per-leaf key lists in walkK2 order (lo subtree before hi; keys in product order)"""
    if depth > 400:
        die('tree too deep')
    if node == 'L':
        if not all(2 <= j <= 9 for j in js):
            die('leaf half-width exponent out of [2, 9]')
        out.append([tuple(t) for t in itertools.product(*[opts(m, j) for m, j in zip(ms, js)])])
        return
    if not (isinstance(node, list) and len(node) == 4 and node[0] == 'S' and isinstance(node[1], int) and 0 <= node[1] < D):
        die('bad node')
    d = node[1]
    if js[d] > 8:
        die('split below half-width 2^-9')
    step = 2 ** (8 - js[d])
    lo = list(ms); lo[d] -= step
    hi = list(ms); hi[d] += step
    js2 = list(js); js2[d] += 1
    walk(node[2], lo, js2, out, depth + 1)
    walk(node[3], hi, js2, out, depth + 1)


def root_ms(i):
    digits = []
    for _ in range(D):
        digits.append(i % N0); i //= N0
    digits.reverse()
    return [-512 + (2 * a + 1) * 64 for a in digits]


def fint(v):
    return str(v) if v >= 0 else 'Int.negSucc %d' % (-v - 1)


def fmt_comp(c):
    return '⟨%s, %s, %d⟩' % ('true' if c[0] else 'false', fint(c[1]), c[2])


def fmt_key(k):
    return '[' + ', '.join(fmt_comp(c) for c in k) + ']'


def fmt_gi(a, b):
    return '⟨%s, %s⟩' % (fint(a), fint(b))


def fmt_tree(node):
    if node == 'L':
        return '.leaf'
    return '(.split %d %s %s)' % (node[1], fmt_tree(node[2]), fmt_tree(node[3]))


HEADER_V = {
    'lit': ('import Bohr59aCoreK.VertexH\nimport Bohr59aCoreK.TrigTab\n\n'
            '/-! Generated by tools/gen_k6.py: k = 6 vertex certificates, hints as data (kernel decide per vertex). -/\n\n'
            'open Bohr59aK Bohr59aCore\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
            'set_option Elab.async false\n\n'),
    'pack': ('import Bohr59aCoreK.Packed\nimport Bohr59aCoreK.TrigTab\n\n'
             '/-! Generated by tools/gen_k6.py: k = 6 vertex certificates, hints as packed data (kernel decide per vertex). -/\n\n'
             'open Bohr59aK Bohr59aCore\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
             'set_option Elab.async false\n\n')}

G = {}  # shared with forked workers


def zz(v):
    return 2 * v if v >= 0 else -2 * v - 1


def pack(y, W, X):
    """y (2K ints), the rows of W, x as one natural number: width w in the low 10 bits, then the zigzag fields of w bits,
    least significant first (decoded by Bohr59aCoreK.Packed.unpackGI)"""
    fs = [zz(v) for v in y] + [zz(t) for row in W for g in row for t in g] + [zz(t) for g in X for t in g]
    if len(fs) != 2 * K + (K + 1) * (K + 2) + 2 * (K + 1):
        die('pack: field count')
    w = max(1, max(f.bit_length() for f in fs))
    if w >= 1024:
        die('pack: width')
    n = 0
    for f in reversed(fs):
        n = (n << w) | f
    return (n << 10) | w


def write_vmod(mi):
    keys, ys, hints, per_v, vdir, tag, fmt = G['keys'], G['ys'], G['hints'], G['per_v'], G['vdir'], G['tag'], G['fmt']
    lines = [HEADER_V[fmt]]
    for idx in range(mi * per_v, min(len(keys), (mi + 1) * per_v)):
        y = ys[idx]
        W, X = hints[idx]
        if fmt == 'pack':
            lines.append('noncomputable def h%s_%d : Nat := 0x%x\n' % (tag, idx, pack(y, W, X)))
            lines.append('theorem w%s_%d : vertexOKKp trigTT %d %d %d %s h%s_%d = true := by decide +kernel\n'
                         % (tag, idx, K, BNUM, BDEN, fmt_key(keys[idx]), tag, idx))
            continue
        ys_s = ', '.join(fmt_gi(y[2 * j], y[2 * j + 1]) for j in range(K))
        w_s = ', '.join('[' + ', '.join(fmt_gi(a, b) for a, b in row) + ']' for row in W)
        x_s = ', '.join(fmt_gi(a, b) for a, b in X)
        lines.append('theorem w%s_%d : vertexOKKh trigTT %d %d %d %s [%s] [%s] [%s] = true := by decide +kernel\n'
                     % (tag, idx, K, BNUM, BDEN, fmt_key(keys[idx]), ys_s, w_s, x_s))
    path = os.path.join(vdir, '%sV%04d.lean' % (tag, mi))
    open(path + '.part', 'w').write(''.join(lines)); os.replace(path + '.part', path)
    return mi


def parse_hint_line(line):
    if line == 'ERR' or '|' not in line:
        die('k6hints error line')
    wpart, xpart = line.split('|')
    W = [[tuple(int(t) for t in g.split(',')) for g in row.split(' ')] for row in wpart.split(';')]
    X = [tuple(int(t) for t in g.split(',')) for g in xpart.split(' ')]
    if len(W) != K + 1 or len(X) != K + 1 or any(len(W[i]) != i + 1 for i in range(K + 1)):
        die('k6hints shape')
    return W, X


def main():
    if len(sys.argv) not in (8, 9):
        die('usage: gen_k6.py FROZEN_DIR OUT_DIR K6HINTS_BIN NPROC PER_V PER_C FIRST:NCELLS:TAG[,FIRST:NCELLS:TAG...] [pack|lit]')
    fmt = sys.argv[8] if len(sys.argv) == 9 else 'pack'
    if fmt not in HEADER_V:
        die('bad format')
    frozen, out, helper = sys.argv[1], sys.argv[2], sys.argv[3]
    nproc, per_v, per_c = int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6])
    blocks = []
    for b in sys.argv[7].split(','):
        f_, n_, t_ = b.split(':')
        first, ncells, tag = int(f_), int(n_), t_
        if not tag.isalnum() or first % per_c or ncells <= 0 or first + ncells > N0 ** D:
            die('bad block %s' % b)
        blocks.append((first, ncells, tag))
    if len(set(t for _, _, t in blocks)) != len(blocks):
        die('duplicate block tag')
    ytab, cells, shas, rounded = {}, {}, {}, [0, Fraction(0)]
    # shards parsed in parallel, merged in shard order: the first certificate of a key wins, exactly as a sequential pass
    with mp.get_context('fork').Pool(min(nproc, NSH)) as pool:
        for s, sha, cs, ents in pool.imap(load_shard, [(frozen, s) for s in range(NSH)]):
            shas['sh%d' % s] = sha
            for i, tree in cs.items():
                if i in cells:
                    die('duplicate root cell %d' % i)
                cells[i] = tree
            for key, y, d in ents:
                if key not in ytab:
                    ytab[key] = y
                    if d is not None:
                        rounded[0] += 1; rounded[1] = max(rounded[1], d)
            print('loaded shard', s, 'distinct keys so far', len(ytab), flush=True)
    if len(cells) != N0 ** D:
        die('root cells missing: %d' % len(cells))
    for first, ncells, tag in blocks:
        gen_block(out, helper, nproc, per_v, per_c, first, ncells, tag, cells, ytab, shas, rounded, fmt)


def gen_block(out, helper, nproc, per_v, per_c, first, ncells, tag, cells, ytab, shas, rounded, fmt):
    # first-use order over the selected cells
    order, cell_leaves = {}, []
    for i in range(first, first + ncells):
        leaves = []
        walk(cells[i], root_ms(i), [3] * D, leaves)
        li = []
        for leaf in leaves:
            idxs = []
            for key in leaf:
                if key not in ytab:
                    die('root cell %d: missing vertex certificate %s' % (i, key))
                j = order.get(key)
                if j is None:
                    j = len(order); order[key] = j
                idxs.append(j)
            li.append(idxs)
        cell_leaves.append(li)
    keys = [None] * len(order)
    for key, j in order.items():
        keys[j] = key
    ys = [ytab[key] for key in keys]
    print('distinct vertices used', len(keys), 'leaf key refs', sum(len(l) for c in cell_leaves for l in c), flush=True)
    # hints (untrusted) from the native helper, in parallel chunks
    hdir = os.path.join(out, 'tmp_hints_' + tag); os.makedirs(hdir, exist_ok=True)
    nch = max(1, min(nproc, len(keys) // 2000 + 1))
    bounds = [len(keys) * c // nch for c in range(nch + 1)]
    procs = []
    for c in range(nch):
        fin = os.path.join(hdir, 'in_%03d.txt' % c)
        with open(fin, 'w') as f:
            for idx in range(bounds[c], bounds[c + 1]):
                k = keys[idx]; y = ys[idx]
                f.write(' '.join('%d,%d,%d' % (1 if t else 0, m, j) for t, m, j in k) + '|' +
                        ' '.join('%d,%d' % (y[2 * q], y[2 * q + 1]) for q in range(K)) + '\n')
        procs.append(subprocess.Popen([helper, str(K)], stdin=open(fin), stdout=open(os.path.join(hdir, 'out_%03d.txt' % c), 'w')))
    for p in procs:
        if p.wait() != 0:
            die('k6hints failed')
    hints = []
    for c in range(nch):
        for line in open(os.path.join(hdir, 'out_%03d.txt' % c)):
            hints.append(parse_hint_line(line.rstrip('\n')))
    if len(hints) != len(keys):
        die('hint count %d != %d' % (len(hints), len(keys)))
    print('hints done', flush=True)
    # vertex modules (forked workers share the data)
    vdir = os.path.join(out, 'Bohr59aK6V'); os.makedirs(vdir, exist_ok=True)
    G.update(keys=keys, ys=ys, hints=hints, per_v=per_v, vdir=vdir, tag=tag, fmt=fmt)
    gc.freeze()  # forked workers then leave the parent's pages shared
    nvmod = (len(keys) + per_v - 1) // per_v
    with mp.get_context('fork').Pool(nproc) as pool:
        for _ in pool.imap_unordered(write_vmod, range(nvmod), chunksize=4):
            pass
    print('vertex modules', nvmod, flush=True)
    # chunk modules: each leaf's 3^5 keys in 3 chunks of 81, one linking theorem per chunk (the kernel cost of a
    # declaration grows quadratically with the distinct vertex theorems it references)
    cdir = os.path.join(out, 'Bohr59aK6C'); os.makedirs(cdir, exist_ok=True)
    CH = 81
    chunks = []  # (cell i, leaf p, chunk c, list of vertex indices)
    for i in range(first, first + ncells):
        for p, idxs in enumerate(cell_leaves[i - first]):
            for c in range(0, len(idxs), CH):
                chunks.append((i, p, c // CH, idxs[c:c + CH]))
    PER_P = 48
    link = 'exists_of_vertexOKKp w%s_%d' if fmt == 'pack' else '⟨_, _, _, w%s_%d⟩'
    chunk_mod = {}
    npmod = (len(chunks) + PER_P - 1) // PER_P
    for pm in range(npmod):
        body, need = [], set()
        for (i, p, c, idxs) in chunks[pm * PER_P:(pm + 1) * PER_P]:
            chunk_mod[(i, p, c)] = pm
            for r in idxs:
                need.add(r // per_v)
            body.append('def kc6_%d_%d_%d : List (List Comp) := [%s]\n' % (i, p, c, ', '.join(fmt_key(keys[r]) for r in idxs)))
            body.append('theorem cv6_%d_%d_%d : allP (fun key => ∃ Y Wr x, vertexOKKh trigTT %d %d %d key Y Wr x = true) '
                        'kc6_%d_%d_%d :=\n  ⟨%s⟩\n' % (i, p, c, K, BNUM, BDEN, i, p, c,
                                                      ', '.join([link % (tag, r) for r in idxs] + ['trivial'])))
        head = ['import Bohr59aCoreK.Walk\n'] + ['import Bohr59aK6V.%sV%04d\n' % (tag, m) for m in sorted(need)]
        head.append('\n/-! Generated by tools/gen_k6.py: k = 6 key chunks with their linking theorems. -/\n\n'
                    'open Bohr59aK Bohr59aCore\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
                    'set_option Elab.async false\n\n')
        path = os.path.join(cdir, '%sP%04d.lean' % (tag, pm))
        open(path + '.part', 'w').write(''.join(head + body)); os.replace(path + '.part', path)
    print('chunk modules', npmod, 'chunks', len(chunks), flush=True)
    # cell modules: tree, per-leaf key lists from the chunks, the walk, per-leaf append proofs, the cell link
    ncmod = (ncells + per_c - 1) // per_c
    max_imp = 0
    for ci in range(ncmod):
        body, need = [], set()
        for i in range(first + ci * per_c, min(first + ncells, first + (ci + 1) * per_c)):
            li = cell_leaves[i - first]
            leaf_lists, leaf_thms = [], []
            for p, idxs in enumerate(li):
                nc = (len(idxs) + CH - 1) // CH
                for c in range(nc):
                    need.add(chunk_mod[(i, p, c)])
                names = ['kc6_%d_%d_%d' % (i, p, c) for c in range(nc)]
                prfs = ['cv6_%d_%d_%d' % (i, p, c) for c in range(nc)]
                lst, prf = names[-1], prfs[-1]
                for nm, pf in zip(reversed(names[:-1]), reversed(prfs[:-1])):
                    lst = '%s ++ (%s)' % (nm, lst) if '++' in lst else '%s ++ %s' % (nm, lst)
                    prf = 'allP_app %s (%s)' % (pf, prf)
                leaf_lists.append(lst)
                body.append('theorem lv6_%d_%d : allP (fun key => ∃ Y Wr x, vertexOKKh trigTT %d %d %d key Y Wr x = true) '
                            '(%s) :=\n  %s\n' % (i, p, K, BNUM, BDEN, lst, prf))
                leaf_thms.append('lv6_%d_%d' % (i, p))
            body.append('def tree6_%d : Tree := %s\n' % (i, fmt_tree(cells[i])))
            body.append('def kls6_%d : List (List (List Comp)) := [%s]\n' % (i, ', '.join('(%s)' % l for l in leaf_lists)))
            body.append('theorem cellw6_%d : walkK2 tree6_%d (rootMs %d %d) (List.replicate %d 3) kls6_%d = some [] := by\n'
                        '  decide +kernel\n' % (i, i, D, i, D, i))
            body.append('theorem cellv6_%d : allP (allP (fun key => ∃ Y Wr x, vertexOKKh trigTT %d %d %d key Y Wr x = true)) '
                        'kls6_%d :=\n  ⟨%s⟩\n\n' % (i, K, BNUM, BDEN, i, ', '.join(leaf_thms + ['trivial'])))
        max_imp = max(max_imp, len(need))
        head = ['import Bohr59aCoreK.Walk2\nimport Bohr59aCoreK.AllP\n'] + \
            ['import Bohr59aK6C.%sP%04d\n' % (tag, m) for m in sorted(need)]
        head.append('\n/-! Generated by tools/gen_k6.py: k = 6 root cells (per-leaf key lists, chunked links). -/\n\n'
                    'open Bohr59aK Bohr59aCore\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
                    'set_option Elab.async false\n\n')
        path = os.path.join(cdir, 'C%03d.lean' % ((first // per_c) + ci))
        open(path + '.part', 'w').write(''.join(head + body)); os.replace(path + '.part', path)
    st = dict(k=K, n0=N0, tag=tag, format=fmt, first_cell=first, ncells=ncells, nverts=len(keys), vertex_modules=nvmod, cell_modules=ncmod,
              chunk_modules=npmod, chunks=len(chunks),
              per_v=per_v, per_c=per_c, max_cell_imports=max_imp,
              leaf_key_refs=sum(len(l) for c in cell_leaves for l in c), shard_sha256=shas,
              y_rounded_to_grid_all_shards=rounded[0], y_max_rounding=float(rounded[1]))
    os.makedirs(os.path.join(out, 'stats'), exist_ok=True)
    json.dump(st, open(os.path.join(out, 'stats', 'K6K_%s.json' % tag), 'w'), indent=1)
    print(json.dumps({k: v for k, v in st.items() if k != 'shard_sha256'}))


if __name__ == '__main__':
    main()
