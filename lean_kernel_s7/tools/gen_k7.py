#!/usr/bin/env python3
"""K7 module generator (kernel-only S({0..7}) <= 2.552 on the half domain [0, 1] x [-1, 1]^5; hints as packed data, keys
as Nat codes).

Global vertex layer: every distinct vertex key of the frozen v3b certificate (bb7/sh0..sh575.json) gets ONE vertex
theorem, numbered by first appearance (shards in order, each shard's verts in file order); the first certificate of a key
wins (every certificate of a key certifies the same vertex: the vertex check does not depend on the cell). Keys are written
as codes, `encK` of tools' Bohr59aSplitK/CodeWalk.lean (16 bits per component, first component lowest: tan in bit 0, j in
bits 1-4, m + 512 in bits 5-15), decoded by `Bohr59aSplitK.decK`.

  Bohr59aK7V/Ssss_kkkk.lean  the vertices owned by shard sss (first appearance there), 1000 per module, in idx order:
                          h7_<idx> : Nat (y, W, x packed) and
                          v7_<idx> : PF7C (nat_lit c) := pf7c_of (m := h7_<idx>) (by decide +kernel)
                          (PF7C c: some packed hint makes vertexOKKpF3 trigTT 7 2552 1000 (decK c) true)
  Bohr59aK7K/Cnnnn_mm.lean  kc7_<i>_<p>_<c> : List Nat, the <= 81 key codes of chunk c of leaf p of root cell i
  Bohr59aK7L/Cnnnn_mm.lean  cv7_<i>_<p>_<c> : allP PF7C kc7_<i>_<p>_<c> := ⟨v7_<idx>, …⟩ (links)
  Bohr59aK7C/Cnnnn.lean     tree7_<i>, lv7_<i>_<p>, cls7_<i> (one code list per leaf),
                            cellw7_<i> : walkKC tree7_<i> (rootMsH 5 <i>) (List.replicate 6 2) cls7_<i> = some [] (decide +kernel),
                            cellv7_<i> : allP (allP PF7C) cls7_<i>
  (the split cells 301 and 626 come from tools/gen_k7split.py; the glue and Final from gen_k7_final.py)

usage:
  gen_k7.py index  FROZEN_DIR OUT_DIR NPROC [SHARDS]   global key index -> OUT/index/{codes.bin,first.bin,sorted.bin,
                                                       vmap.txt,trees.json,index.json} (SHARDS: a,b-c,... for tests only)
  gen_k7.py vertex FROZEN_DIR OUT_DIR K6HINTS NPROC SHARDS  the vertex modules of the vertices owned by SHARDS
  gen_k7.py cells  OUT_DIR NPROC CELLS                 chunk, link and cell modules of the root cells CELLS (a,b-c,...)
  gen_k7.py need   OUT_DIR CELLS FILE                  the global indices of the vertices CELLS use (pilots: with
                                                       GEN_K7_ONLY_IDX=FILE the vertex stage writes only those)
"""
import gc, hashlib, itertools, json, mmap, multiprocessing as mp, os, struct, subprocess, sys
from array import array
from fractions import Fraction

if sys.flags.optimize:
    sys.exit('refusing to run with python -O')

K, N0, D, NSH, NCELL = 7, 4, 6, 576, 2048
BNUM, BDEN = 2552, 1000
PER_V = 1000          # vertex theorems per vertex module
CH = 81               # key codes per chunk (one link theorem per chunk: its kernel cost grows like N^2 in the theorems used)
PER_KL = 48           # chunks per K / L module
HEAVY = (301, 626)    # split cells (tools/gen_k7split.py)
REC = 16              # sorted.bin record: code (12 bytes, little endian) + idx (4 bytes)


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


def encC(c):
    tan, m, j = c
    return (1 if tan else 0) + 2 * j + 32 * (m + 512)


def encK(key):
    if len(key) != D:
        die('key length %d' % len(key))
    return sum(encC(c) << (16 * q) for q, c in enumerate(key))


def y_ints(y):
    """y at scale 2^128; values off that grid are rounded to nearest (any y is sound: the kernel re-checks every
    inequality exactly for the y it is given); returns the integers and the largest change (None if all exact)"""
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


def parse_ranges(s, top):
    out = []
    for part in s.split(','):
        if '-' in part:
            a, b = part.split('-'); out.extend(range(int(a), int(b) + 1))
        else:
            out.append(int(part))
    if any(not 0 <= x < top for x in out) or len(set(out)) != len(out):
        die('bad range list %s' % s)
    return sorted(out)


def read_shard(frozen, s):
    raw = open(os.path.join(frozen, 'bb7', 'sh%d.json' % s), 'rb').read()
    sha = hashlib.sha256(raw).hexdigest()
    sh = json.loads(raw)
    del raw
    if not (sh['k'] == K and sh['n0'] == N0 and sh['nshards'] == NSH and sh['shard'] == s and sh['domain'] == 'half'):
        die('bad shard header %d' % s)
    return sha, sh


# ---------------------------------------------------------------- index
_CC = {}


def comp_cached(kk):
    """comp_of_json, memoized on the component's JSON form (few distinct components: the hot loop of the index stage)"""
    t = tuple(kk)
    c = _CC.get(t)
    if c is None:
        c = _CC[t] = comp_of_json(kk)
    return c


def index_shard(arg):
    frozen, s = arg
    sha, sh = read_shard(frozen, s)
    cells = {}
    for key_, tree in sh['cells'].items():
        i = int(key_)
        if i % NSH != s or i in cells or not 0 <= i < NCELL:
            die('bad or duplicate root cell %d in shard %d' % (i, s))
        cells[i] = tree
    codes = [encK(tuple(comp_cached(kk) for kk in ent[0])) for ent in sh['verts']]
    return s, sha, cells, codes


def cmd_index(frozen, out, nproc, shards):
    idir = os.path.join(out, 'index'); os.makedirs(idir, exist_ok=True)
    first = {}                       # code -> idx
    fsh, fpos = array('H'), array('I')
    cells, shas, nent = {}, {}, 0
    with mp.get_context('fork').Pool(nproc) as pool:
        for s, sha, cs, codes in pool.imap(index_shard, [(frozen, s) for s in shards]):   # in shard order
            shas['sh%d' % s] = sha
            cells.update(cs)
            nent += len(codes)
            for p, c in enumerate(codes):
                if c not in first:
                    first[c] = len(first); fsh.append(s); fpos.append(p)
            print('indexed shard', s, 'entries', nent, 'distinct', len(first), flush=True)
    n = len(first)
    codes = [0] * n
    for c, i in first.items():
        codes[i] = c
    with open(os.path.join(idir, 'codes.bin'), 'wb') as f:
        for c in codes:
            f.write(c.to_bytes(12, 'little'))
    with open(os.path.join(idir, 'first.bin'), 'wb') as f:
        fsh.tofile(f); fpos.tofile(f)
    srt = sorted(range(n), key=codes.__getitem__)
    with open(os.path.join(idir, 'sorted.bin'), 'wb') as f:
        for i in srt:
            f.write(codes[i].to_bytes(12, 'little') + struct.pack('<I', i))
    json.dump({str(i): cells[i] for i in sorted(cells)}, open(os.path.join(idir, 'trees.json'), 'w'), separators=(',', ':'))
    a = {}                            # owning shard -> its first idx (idx are assigned shard by shard)
    for i in range(n):
        a.setdefault(fsh[i], i)
    with open(os.path.join(idir, 'vmap.txt'), 'w') as f:          # for tools/gen_k7split.py: "code idx module"
        for i in srt:
            f.write('%d %d S%03d_%04d\n' % (codes[i], i, fsh[i], (i - a[fsh[i]]) // PER_V))
    own = {}
    for i in range(n):
        own.setdefault(fsh[i], [i, 0])[1] += 1
    vm = sum((c + PER_V - 1) // PER_V for _, c in own.values())
    st = dict(k=K, n0=N0, shards=len(shards), entries=nent, distinct=n, vertex_modules=vm, cells=len(cells),
              owned={str(sh): v for sh, v in sorted(own.items())}, shard_sha256=shas)
    json.dump(st, open(os.path.join(idir, 'index.json'), 'w'), indent=1)
    print(json.dumps({k: v for k, v in st.items() if k not in ('shard_sha256', 'owned')}), flush=True)


class Index:
    """code -> global idx (binary search in sorted.bin), idx -> code (codes.bin), idx -> (shard, pos) (first.bin)"""
    def __init__(self, out):
        idir = os.path.join(out, 'index')
        self.meta = json.load(open(os.path.join(idir, 'index.json')))
        self.n = self.meta['distinct']
        self.srt = mmap.mmap(os.open(os.path.join(idir, 'sorted.bin'), os.O_RDONLY), 0, prot=mmap.PROT_READ)
        self.cod = mmap.mmap(os.open(os.path.join(idir, 'codes.bin'), os.O_RDONLY), 0, prot=mmap.PROT_READ)
        fb = open(os.path.join(idir, 'first.bin'), 'rb').read()
        self.fsh = array('H'); self.fsh.frombytes(fb[:2 * self.n])
        self.fpos = array('I'); self.fpos.frombytes(fb[2 * self.n:])
        if len(self.fpos) != self.n:
            die('first.bin size')
        self.own = {int(sh): tuple(v) for sh, v in self.meta['owned'].items()}   # shard -> (first idx, count)

    def vmod(self, i):
        """the vertex module holding vertex i: shard, module number within the shard"""
        s = self.fsh[i]
        return s, (i - self.own[s][0]) // PER_V

    def code(self, i):
        return int.from_bytes(self.cod[12 * i:12 * i + 12], 'little')

    def idx(self, c):
        lo, hi = 0, self.n
        while lo < hi:
            mid = (lo + hi) // 2
            cm = int.from_bytes(self.srt[REC * mid:REC * mid + 12], 'little')
            if cm < c:
                lo = mid + 1
            elif cm > c:
                hi = mid
            else:
                return struct.unpack_from('<I', self.srt, REC * mid + 12)[0]
        return None


# ---------------------------------------------------------------- vertex modules
def pack(y, W, X):
    """y (2K ints), the rows of W, x as one natural number: width w in the low 10 bits, then the zigzag fields of w bits,
    least significant first (decoded by Bohr59aCoreK.Packed.unpackGI)"""
    zz = lambda v: 2 * v if v >= 0 else -2 * v - 1
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


def parse_hint_line(line):
    if line == 'ERR' or '|' not in line:
        die('k6hints error line')
    wpart, xpart = line.split('|')
    W = [[tuple(int(t) for t in g.split(',')) for g in row.split(' ')] for row in wpart.split(';')]
    X = [tuple(int(t) for t in g.split(',')) for g in xpart.split(' ')]
    if len(W) != K + 1 or len(X) != K + 1 or any(len(W[i]) != i + 1 for i in range(K + 1)):
        die('k6hints shape')
    return W, X


HEADER_V = ('import Bohr59aSplitK.CodeWalk\n\n'
            '/-! Generated by tools/gen_k7.py: k = 7 vertex certificates (global vertex layer), packed hints, keys as codes. -/\n\n'
            'open Bohr59aK Bohr59aCore Bohr59aSplitK\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
            'set_option Elab.async false\n\n')
G = {}


def vertex_work(k):
    """hints and the text of vertex module k of the current shard (forked worker; G holds the shard's owned entries)"""
    s, first, ents, helper, tdir, vdir = G['s'], G['first'], G['ents'], G['helper'], G['tdir'], G['vdir']
    if os.path.exists(os.path.join(vdir, 'S%03d_%04d.lean' % (s, k))) and 'groups' not in G:
        return k                                       # written by an earlier (interrupted) run: modules appear atomically
    part = G['groups'][k] if 'groups' in G else ents[k * PER_V:(k + 1) * PER_V]
    fin = os.path.join(tdir, 'in_%03d_%04d.txt' % (s, k))
    with open(fin, 'w') as f:
        for (_, key, y, _) in part:
            f.write(' '.join('%d,%d,%d' % (1 if t else 0, mm, j) for t, mm, j in key) + '|' +
                    ' '.join('%d,%d' % (y[2 * q], y[2 * q + 1]) for q in range(K)) + '\n')
    res = subprocess.run([helper, str(K)], stdin=open(fin), capture_output=True, text=True)
    if res.returncode != 0:
        die('k6hints failed on shard %d module %d' % (s, k))
    hints = [parse_hint_line(l) for l in res.stdout.splitlines()]
    if len(hints) != len(part):
        die('hint count')
    lines = [HEADER_V]
    for (i, key, y, _), (W, X) in zip(part, hints):
        lines.append('noncomputable def h7_%d : Nat := 0x%x\n' % (i, pack(y, W, X)))
        lines.append('theorem v7_%d : PF7C (nat_lit %d) := pf7c_of (m := h7_%d) (by decide +kernel)\n' % (i, encK(key), i))
    path = os.path.join(vdir, 'S%03d_%04d.lean' % (s, k))
    open(path + '.part', 'w').write(''.join(lines)); os.replace(path + '.part', path)
    os.remove(fin)
    return k


def cmd_vertex(frozen, out, helper, nproc, shards):
    ix = Index(out)
    vdir = os.path.join(out, 'Bohr59aK7V'); os.makedirs(vdir, exist_ok=True)
    tdir = os.path.join(out, 'tmp_hints'); os.makedirs(tdir, exist_ok=True)
    os.makedirs(os.path.join(out, 'stats'), exist_ok=True)
    if os.environ.get('GEN_K7_ONLY_IDX'):             # pilot only: write just these vertices (file of idx, one per line)
        G['only'] = set(int(x) for x in open(os.environ['GEN_K7_ONLY_IDX']))
    for s in shards:
        if s not in ix.own:
            print('shard', s, 'owns no vertex', flush=True); continue
        first, cnt = ix.own[s]
        only = G.get('only')
        _, sh = read_shard(frozen, s)
        verts = sh['verts']
        ents = []                                  # (idx, key, y, rounding) of the vertices shard s owns, idx order
        for i in range(first, first + cnt):
            if only is not None and i not in only:
                continue
            if ix.fsh[i] != s:
                die('ownership is not contiguous at %d' % i)
            key = tuple(comp_of_json(kk) for kk in verts[ix.fpos[i]][0])
            if encK(key) != ix.code(i):
                die('vertex %d: code mismatch' % i)
            y, d = y_ints(verts[ix.fpos[i]][1])
            ents.append((i, key, y, d))
        del sh, verts
        nmod = (cnt + PER_V - 1) // PER_V
        if os.environ.get('GEN_K7_TEST_MAXMOD'):      # tests only: the first few modules of the shard
            nmod = min(nmod, int(os.environ['GEN_K7_TEST_MAXMOD']))
        G.update(s=s, first=first, ents=ents, helper=helper, tdir=tdir, vdir=vdir)
        if only is not None:                           # pilot only: the module numbers stay those of the full layer
            groups = {}
            for e in ents:
                groups.setdefault((e[0] - first) // PER_V, []).append(e)
            G['groups'] = groups
            nmod = None
        gc.collect(); gc.freeze()
        with mp.get_context('fork').Pool(nproc) as pool:
            for _ in pool.imap_unordered(vertex_work, sorted(G['groups']) if nmod is None else range(nmod)):
                pass
        gc.unfreeze()
        G.pop('groups', None)
        rnd = [e[3] for e in ents if e[3] is not None]
        st = dict(shard=s, first_idx=first, vertices=cnt, modules=nmod, y_rounded=len(rnd), y_max_rounding=max(rnd) if rnd else 0.0)
        json.dump(st, open(os.path.join(out, 'stats', 'K7V_S%03d.json' % s), 'w'), indent=1)
        print(json.dumps(st), flush=True)


# ---------------------------------------------------------------- cells
def opts(m, j):
    return [(False, m - 2 ** (9 - j), 0), (False, m + 2 ** (9 - j), 0), (True, m, j)]


def walk(node, ms, js, out, depth=0):
    """per-leaf key lists in walkKC order (lo subtree before hi; keys in product order, first coordinate outermost)"""
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


def root_ms_h(i):
    """rootMsH 5 i: the base-4 digits of i (six, most significant first), centres in units of pi/512"""
    digits = []
    for _ in range(D):
        digits.append(i % N0); i //= N0
    digits.reverse()
    if digits[0] > 1:
        die('root cell outside the half domain')
    return [128 + 256 * digits[0]] + [-384 + 256 * b for b in digits[1:]]


def fmt_tree(node):
    if node == 'L':
        return '.leaf'
    return '(.split %d %s %s)' % (node[1], fmt_tree(node[2]), fmt_tree(node[3]))


HDR = ('\nopen Bohr59aK Bohr59aCore Bohr59aSplitK\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
       'set_option Elab.async false\n\n')
HDR_K = '\nopen Bohr59aCore\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nset_option Elab.async false\n\n'


def cell_work(i):
    ix, out, trees = G['ix'], G['out'], G['trees']
    leaves = []
    walk(trees[str(i)], root_ms_h(i), [2] * D, leaves)
    chunks = []                          # (leaf p, chunk c, codes, idxs)
    for p, leaf in enumerate(leaves):
        codes = [encK(key) for key in leaf]
        idxs = [ix.idx(c) for c in codes]
        if None in idxs:
            die('root cell %d leaf %d: a vertex key has no certificate' % (i, p))
        for c in range(0, len(codes), CH):
            chunks.append((p, c // CH, codes[c:c + CH], idxs[c:c + CH]))
    kdir, ldir, cdir = (os.path.join(out, d) for d in ('Bohr59aK7K', 'Bohr59aK7L', 'Bohr59aK7C'))
    nkl = (len(chunks) + PER_KL - 1) // PER_KL
    vneed_all = set()
    for mm in range(nkl):
        part = chunks[mm * PER_KL:(mm + 1) * PER_KL]
        kl = ['import Bohr59aCore.Format\n\n/-! Generated by tools/gen_k7.py: k = 7 leaf key chunks (codes). -/\n', HDR_K]
        ll, vneed = [], set()
        for (p, c, codes, idxs) in part:
            kl.append('noncomputable def kc7_%d_%d_%d : List Nat := [%s]\n'
                      % (i, p, c, ', '.join('nat_lit %d' % x for x in codes)))
            ll.append('theorem cv7_%d_%d_%d : allP PF7C kc7_%d_%d_%d :=\n  ⟨%s⟩\n'
                      % (i, p, c, i, p, c, ', '.join(['v7_%d' % r for r in idxs] + ['trivial'])))
            vneed.update(ix.vmod(r) for r in idxs)
        vneed_all |= vneed
        kpath = os.path.join(kdir, 'C%04d_%02d.lean' % (i, mm))
        open(kpath + '.part', 'w').write(''.join(kl)); os.replace(kpath + '.part', kpath)
        lh = ['import Bohr59aSplitK.CodeWalk\nimport Bohr59aK7K.C%04d_%02d\n' % (i, mm)] + \
             ['import Bohr59aK7V.S%03d_%04d\n' % v for v in sorted(vneed)] + \
             ['\n/-! Generated by tools/gen_k7.py: links of k = 7 key chunks to the global vertex theorems. -/\n', HDR]
        lpath = os.path.join(ldir, 'C%04d_%02d.lean' % (i, mm))
        open(lpath + '.part', 'w').write(''.join(lh + ll)); os.replace(lpath + '.part', lpath)
    # the cell module: tree, per-leaf code lists from the chunks, the walk, per-leaf append proofs, the cell link
    body = ['def tree7_%d : Tree := %s\n' % (i, fmt_tree(trees[str(i)]))]
    leaf_lists, leaf_thms = [], []
    nch = {}
    for (p, c, _, _) in chunks:
        nch[p] = max(nch.get(p, 0), c + 1)
    for p in range(len(leaves)):
        names = ['kc7_%d_%d_%d' % (i, p, c) for c in range(nch[p])]
        prfs = ['cv7_%d_%d_%d' % (i, p, c) for c in range(nch[p])]
        lst, prf = names[-1], prfs[-1]
        for nm, pf in zip(reversed(names[:-1]), reversed(prfs[:-1])):
            lst = '%s ++ (%s)' % (nm, lst) if '++' in lst else '%s ++ %s' % (nm, lst)
            prf = 'allP_app %s (%s)' % (pf, prf)
        body.append('theorem lv7_%d_%d : allP PF7C (%s) :=\n  %s\n' % (i, p, lst, prf))
        leaf_lists.append(lst); leaf_thms.append('lv7_%d_%d' % (i, p))
    body.append('noncomputable def cls7_%d : List (List Nat) := [%s]\n' % (i, ', '.join('(%s)' % l for l in leaf_lists)))
    body.append('theorem cellw7_%d : walkKC tree7_%d (rootMsH 5 %d) (List.replicate 6 2) cls7_%d = some [] := by\n'
                '  decide +kernel\n' % (i, i, i, i))
    body.append('theorem cellv7_%d : allP (allP PF7C) cls7_%d :=\n  ⟨%s⟩\n' % (i, i, ', '.join(leaf_thms + ['trivial'])))
    head = ['import Bohr59aSplitK.CodeWalk\nimport Bohr59aCore.CheckHalf\nimport Bohr59aCoreK.AllP\n'] + \
           ['import Bohr59aK7L.C%04d_%02d\n' % (i, mm) for mm in range(nkl)] + \
           ['\n/-! Generated by tools/gen_k7.py: k = 7 root cell %d (code walk, chunked links). -/\n' % i, HDR]
    cpath = os.path.join(cdir, 'C%04d.lean' % i)
    open(cpath + '.part', 'w').write(''.join(head + body)); os.replace(cpath + '.part', cpath)
    return i, len(leaves), len(chunks), nkl, len(vneed_all)


def cmd_cells(out, nproc, cells):
    if any(i in HEAVY for i in cells):
        die('cells 301 and 626 are split cells (tools/gen_k7split.py)')
    ix = Index(out)
    trees = json.load(open(os.path.join(out, 'index', 'trees.json')))
    for d in ('Bohr59aK7K', 'Bohr59aK7L', 'Bohr59aK7C'):
        os.makedirs(os.path.join(out, d), exist_ok=True)
    G.update(ix=ix, out=out, trees=trees)
    gc.freeze()
    rows = []
    with mp.get_context('fork').Pool(nproc) as pool:
        for r in pool.imap_unordered(cell_work, cells):
            rows.append(r)
    rows.sort()
    st = dict(cells=[dict(cell=i, leaves=nl, chunks=nc, kl_modules=nk, vertex_modules_used=nv) for i, nl, nc, nk, nv in rows])
    os.makedirs(os.path.join(out, 'stats'), exist_ok=True)
    json.dump(st, open(os.path.join(out, 'stats', 'K7C_%04d_%04d.json' % (cells[0], cells[-1])), 'w'), indent=1)
    print('cells', len(rows), 'leaves', sum(r[1] for r in rows), 'chunks', sum(r[2] for r in rows),
          'max vertex modules used by a cell', max(r[4] for r in rows), flush=True)


def cmd_need(out, cells, path):
    """the global indices of every vertex key the given root cells use (one per line) and, on stdout, their owning shards"""
    ix = Index(out)
    trees = json.load(open(os.path.join(out, 'index', 'trees.json')))
    need = set()
    for i in cells:
        leaves = []
        walk(trees[str(i)], root_ms_h(i), [2] * D, leaves)
        for leaf in leaves:
            for key in leaf:
                r = ix.idx(encK(key))
                if r is None:
                    die('root cell %d: a vertex key has no certificate' % i)
                need.add(r)
    with open(path, 'w') as f:
        for r in sorted(need):
            f.write('%d\n' % r)
    owners = sorted({ix.fsh[r] for r in need})
    mods = sorted({ix.vmod(r) for r in need})
    print('vertices', len(need), 'owner shards', len(owners), 'vertex modules', len(mods))
    print(','.join(str(x) for x in owners))


def main():
    if len(sys.argv) < 2:
        die(__doc__)
    cmd = sys.argv[1]
    if cmd == 'index' and len(sys.argv) in (5, 6):
        shards = parse_ranges(sys.argv[5], NSH) if len(sys.argv) == 6 else list(range(NSH))
        cmd_index(sys.argv[2], sys.argv[3], int(sys.argv[4]), shards)
    elif cmd == 'vertex' and len(sys.argv) == 7:
        cmd_vertex(sys.argv[2], sys.argv[3], sys.argv[4], int(sys.argv[5]), parse_ranges(sys.argv[6], NSH))
    elif cmd == 'need' and len(sys.argv) == 5:
        cmd_need(sys.argv[2], parse_ranges(sys.argv[3], NCELL), sys.argv[4])
    elif cmd == 'cells' and len(sys.argv) == 5:
        cmd_cells(sys.argv[2], int(sys.argv[3]), parse_ranges(sys.argv[4], NCELL))
    else:
        die(__doc__)


if __name__ == '__main__':
    main()
