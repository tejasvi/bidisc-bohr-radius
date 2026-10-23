#!/usr/bin/env python3
"""Split k = 7 cell generator: kernel-only proof of S({0..7}) <= 2.552 on the half domain, with heavy root cells cut
into sub-boxes (the Lean API is in Bohr59aCoreK/Split.lean and Bohr59a/CertSplit.lean).

Reads one shard of the frozen k = 7 certificate (bb7/sh<S>.json) and, for the selected root cells i of that shard, cuts
each cell's tree into sub-boxes: a subtree with at most LCAP leaves becomes one sub-box, a larger one is a split node of
the cell's top tree. Vertex keys are deduplicated over the selected cells (the first certificate of a key in the shard
wins; every certificate of a key certifies the same vertex) and numbered by first use (cells in the given order, leaves
in walk order, keys in product order). Hints come from the untrusted helper `k6hints 7` (any hints are sound: the kernel
re-checks every vertex exactly).

Modules (T = run tag, i = cell, p = leaf index in the cell's walk order, c = chunk, b = sub-box, g = glue group), code format:
  Bohr59aK7HV/<T>Vnnnn  h7<T>_<v> : Nat (packed y, W, x);
                        w7<T>_<v> : PF7C (nat_lit code) := pf7c_of (m := h7<T>_<v>) (by decide +kernel)
                        (none with --vmap: the links then use the global layer v7_<idx>, stated the same way)
  Bohr59aK7HK/<T>Knnnn  kc7_<i>_<p>_<c> : List Nat                       (codes of chunk c, 81 keys, of the 729 keys of leaf p)
  Bohr59aK7HL/<T>Lnnnn  cv7_<i>_<p>_<c> : allP PF7C kc7_<i>_<p>_<c> := ⟨w7<T>_<v>, ...⟩ (bare constants)
  Bohr59aK7HW/<T>Wnnnn  tree7_<i>_<b>, kls7_<i>_<b> (one code list per leaf),
                        sw7_<i>_<b> : walkKC tree7_<i>_<b> MS JS kls7_<i>_<b> = some [] := by decide +kernel
  Bohr59aK7HA/<T>Annnn  lv7_<i>_<p> : allP PF7C (leaf list); sv7_<i>_<b> : allP (allP PF7C) kls7_<i>_<b>
  Bohr59aK7HG/<T>C<i>Gnn bsg7_<i>_<g> (<= GCAP sub-boxes); gok7_<i>_<g> : allP (fun b => BoxOK 6 B b.1 b.2) bsg7_<i>_<g> (boxOK7C)
  Bohr59aK7HG/<T>C<i>   top7_<i>; topok7_<i> : boxesOf top7_<i> (rootMsH 5 i) (List.replicate 6 2) = some (bsg ++ ...);
                        cellH7_<i> : CellOKH 5 B i,   B = ((2552 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ)
The lit format writes keys as literals (List (List Comp) chunks, PF7, walkK2, boxOK7); see --keyfmt.

Literal conventions (keys, trees, negative integers as `Int.negSucc`) are those of tools/gen_k6.py, imported
from a byte-identical copy next to this file. W modules import only K modules, so the walks can be built without the
vertex theorems.

usage: gen_k7split.py SHARD_JSON OUT_DIR HELPER NPROC TAG CELLS [options]
  CELLS: comma-separated root cell indices of the shard.
  --keyfmt code (default; Nat key codes, walkKC, links pf7c_of, glue boxOK7C: Bohr59aSplitK/CodeWalk*.lean),
           lit (literal keys, walkK2, glue boxOK7) or packed (decK keys with walkK2; measured slow, kept for the record).
  --lcap N (leaves per sub-box, 64: a walk declaration needs ~50 KB per key ref), --per-v N (vertices per V module, 400),
  --per-k N (chunks per K module, 200), --per-l N (chunks per L module, 90), --wcap N (key refs per W/A module, 200000),
  --gcap N (sub-boxes per glue group, 64)
  --vmap FILE: link to the global vertex layer instead of writing V modules: text lines "code idx module" (decimal,
           sorted by code), constants --vname (v7_%d : PF7C (nat_lit code)) in modules --vprefix.<module> (Bohr59aK7V);
           code format only.
  --novert: only K and W modules (and the stats): no hints, V, L, A, G.
  --sample-subs N: K and W for every sub-box; V, L, A only for the first N sub-boxes of each cell; no G.
Vertex theorems (own V modules) use vertexOKKpF3 (Bohr59aCoreK/FastArith3.lean) with packed hints; in the code format they are stated as
PF7C (via pf7c_of), so links are bare constants.
"""
import argparse, gc, hashlib, importlib.util, itertools, json, multiprocessing as mp, os, subprocess, sys

if sys.flags.optimize:
    sys.exit('refusing to run with python -O')

HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location('gk6', os.path.join(HERE, 'gen_k6.py'))
gk = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(gk)
gk.K, gk.D, gk.BNUM, gk.BDEN = 7, 6, 2552, 1000

K, D, BNUM, BDEN, N0, NSH, NCELLS = 7, 6, 2552, 1000, 4, 576, 2048
CH = 81
B_EXPR = '(((2552 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ))'
OPTS = 'set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nset_option Elab.async false\n\n'


def die(msg):
    sys.exit('GEN FAILED: ' + msg)


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for blk in iter(lambda: f.read(1 << 24), b''):
            h.update(blk)
    return h.hexdigest()


def root_ms_h(i):
    """rootMsH 5 i: base-4 digits a, b1..b5 of i (most significant first); centres 128 + 256 a, -384 + 256 b"""
    digits = []
    for _ in range(D):
        digits.append(i % 4); i //= 4
    digits.reverse()
    return [128 + 256 * digits[0]] + [-384 + 256 * b for b in digits[1:]]


def child_boxes(ms, js, d):
    if not (0 <= d < D) or js[d] > 8:
        die('invalid split d=%d js=%s' % (d, js))
    step = 2 ** (8 - js[d])
    lo = list(ms); lo[d] -= step
    hi = list(ms); hi[d] += step
    js2 = list(js); js2[d] += 1
    return lo, hi, js2


def is_split(node):
    return isinstance(node, list) and len(node) == 4 and node[0] == 'S' and isinstance(node[1], int)


def count_leaves(node, memo):
    if node == 'L':
        return 1
    if not is_split(node):
        die('bad node')
    k = id(node)
    if k not in memo:
        memo[k] = count_leaves(node[2], memo) + count_leaves(node[3], memo)
    return memo[k]


def cut(node, ms, js, lcap, memo, subs, depth=0):
    """the top tree (certificate format) of the cut; appends the sub-boxes (subtree, ms, js) in walk order"""
    if depth > 400:
        die('tree too deep')
    if count_leaves(node, memo) <= lcap:
        subs.append((node, list(ms), list(js)))
        return 'L'
    lo, hi, js2 = child_boxes(ms, js, node[1])
    return ['S', node[1], cut(node[2], lo, js2, lcap, memo, subs, depth + 1), cut(node[3], hi, js2, lcap, memo, subs, depth + 1)]


def boxes_of(top, ms, js):
    """Python mirror of Bohr59aK.boxesOf"""
    if top == 'L':
        return [(list(ms), list(js))]
    lo, hi, js2 = child_boxes(ms, js, top[1])
    return boxes_of(top[2], lo, js2) + boxes_of(top[3], hi, js2)


def leaves_of(node, ms, js, out, depth=0):
    """leaf boxes (ms, js) of a subtree in walkK2 order"""
    if depth > 400:
        die('tree too deep')
    if node == 'L':
        if not all(2 <= j <= 9 for j in js):
            die('leaf half-width exponent out of [2, 9]')
        out.append((list(ms), list(js)))
        return
    if not is_split(node):
        die('bad node')
    lo, hi, js2 = child_boxes(ms, js, node[1])
    leaves_of(node[2], lo, js2, out, depth + 1)
    leaves_of(node[3], hi, js2, out, depth + 1)


def leaf_keys(ms, js):
    return list(itertools.product(*[gk.opts(m, j) for m, j in zip(ms, js)]))


def pack_key(k):
    """16 bits per component, first component lowest: tan (bit 0), j (bits 1-4), m + 512 (bits 5-15); see Bohr59aSplitK.decK"""
    n = 0
    for q, (t, m, j) in enumerate(k):
        if not (-512 <= m <= 512 and 0 <= j <= 9):
            die('key component out of range %s' % ((t, m, j),))
        n |= ((1 if t else 0) | (j << 1) | ((m + 512) << 5)) << (16 * q)
    return n


FMTS = {
    'lit': dict(kel=lambda k: gk.fmt_key(k), vkey=lambda k: gk.fmt_key(k), kty='List (List Comp)', klsty='List (List (List Comp))',
                pred='PF7', walk='walkK2', box='boxOK7', glueimp='Bohr59aSplitK.Glue7', predimp='Bohr59aSplitK.Pred',
                walkimp='Bohr59aCoreK.Walk2', kimp='', vimp='', vopen='', kopen='', wopen='', kdef='def', link='⟨_, w7%s_%d⟩', pf7cv=False),
    'packed': dict(kel=lambda k: 'decK (nat_lit %d)' % pack_key(k), vkey=lambda k: '(decK (nat_lit %d))' % pack_key(k),
                   kty='List (List Comp)', klsty='List (List (List Comp))', pred='PF7', walk='walkK2', box='boxOK7',
                   glueimp='Bohr59aSplitK.Glue7', predimp='Bohr59aSplitK.Pred', walkimp='Bohr59aCoreK.Walk2',
                   kimp='import Bohr59aSplitK.Key\n', vimp='import Bohr59aSplitK.Key\n', vopen=' Bohr59aSplitK',
                   kopen=' Bohr59aSplitK', wopen='', kdef='noncomputable def', link='⟨_, w7%s_%d⟩', pf7cv=False),
    'code': dict(kel=lambda k: 'nat_lit %d' % pack_key(k), vkey=lambda k: '(decK (nat_lit %d))' % pack_key(k),
                 kty='List Nat', klsty='List (List Nat)', pred='PF7C', walk='walkKC', box='boxOK7C',
                 glueimp='Bohr59aSplitK.CodeWalkSound', predimp='Bohr59aSplitK.CodeWalk', walkimp='Bohr59aSplitK.CodeWalk',
                 kimp='', vimp='import Bohr59aSplitK.CodeWalk\n', vopen=' Bohr59aSplitK', kopen='', wopen=' Bohr59aSplitK', kdef='noncomputable def', link='w7%s_%d', pf7cv=True)}
FMT = {}


def fmt_k(k):
    return FMT['kel'](k)


def fmt_ints(v):
    return '[' + ', '.join(gk.fint(x) for x in v) + ']'


def fmt_nats(v):
    return '[' + ', '.join('%d' % x for x in v) + ']'


def chain(names, op):
    """right-nested `a op (b op (c ...))`, as in gen_k6"""
    s = names[-1]
    for nm in reversed(names[:-1]):
        s = '%s %s (%s)' % (nm, op, s) if op in s else '%s %s %s' % (nm, op, s)
    return s


def app_chain(prfs):
    s = prfs[-1]
    for pf in reversed(prfs[:-1]):
        s = 'allP_app %s (%s)' % (pf, s)
    return s


def write(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    open(path + '.part', 'w').write(text)
    os.replace(path + '.part', path)


G = {}


def write_vmod(mi):
    keys, ys, hints, per_v, out, tag = G['keys'], G['ys'], G['hints'], G['per_v'], G['out'], G['tag']
    lines = ['import Bohr59aCoreK.FastArith3\nimport Bohr59aCoreK.TrigTab\n' + FMT['vimp'] + '\n'
             '/-! Generated by tools/gen_k7split.py: k = 7 vertex certificates, packed hints (kernel decide per vertex). -/\n\n'
             'open Bohr59aK Bohr59aCore' + FMT['vopen'] + '\n' + OPTS]
    for v in range(mi * per_v, min(len(keys), (mi + 1) * per_v)):
        W, X = hints[v]
        lines.append('noncomputable def h7%s_%d : Nat := 0x%x\n' % (tag, v, gk.pack(ys[v], W, X)))
        if FMT['pf7cv']:
            lines.append('theorem w7%s_%d : PF7C (nat_lit %d) := pf7c_of (m := h7%s_%d) (by decide +kernel)\n'
                         % (tag, v, pack_key(keys[v]), tag, v))
        else:
            lines.append('theorem w7%s_%d : vertexOKKpF3 trigTT 7 2552 1000 %s h7%s_%d = true := by decide +kernel\n'
                         % (tag, v, FMT['vkey'](keys[v]), tag, v))
    write(os.path.join(out, 'Bohr59aK7HV', '%sV%04d.lean' % (tag, mi)), ''.join(lines))
    return mi


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('shard'); ap.add_argument('out'); ap.add_argument('helper'); ap.add_argument('nproc', type=int)
    ap.add_argument('tag'); ap.add_argument('cells')
    ap.add_argument('--lcap', type=int, default=64); ap.add_argument('--per-v', type=int, default=400)
    ap.add_argument('--per-k', type=int, default=200); ap.add_argument('--per-l', type=int, default=90)
    ap.add_argument('--wcap', type=int, default=200000); ap.add_argument('--gcap', type=int, default=64)
    ap.add_argument('--novert', action='store_true'); ap.add_argument('--sample-subs', type=int, default=0)
    ap.add_argument('--keyfmt', choices=['lit', 'packed', 'code'], default='code')
    ap.add_argument('--vmap', default='', help='global vertex layer: text file of "code idx module" lines (code format only)')
    ap.add_argument('--vprefix', default='Bohr59aK7V'); ap.add_argument('--vname', default='v7_%d')
    a = ap.parse_args()
    tag, out = a.tag, a.out
    if not tag.isalnum() or a.lcap < 1 or a.gcap < 1 or a.per_v < 1 or a.per_k < 1 or a.per_l < 1:
        die('bad arguments')
    cells_sel = [int(x) for x in a.cells.split(',')]
    if len(set(cells_sel)) != len(cells_sel):
        die('duplicate cell')
    full = not a.novert and a.sample_subs == 0
    FMT.update(FMTS[a.keyfmt])
    if a.vmap and (a.keyfmt != 'code' or a.novert):
        die('--vmap needs --keyfmt code and vertex links')

    sha = sha256_file(a.shard)
    sh = json.load(open(a.shard))
    s = sh.get('shard')
    if not (sh['k'] == K and sh['n0'] == N0 and sh['domain'] == 'half' and sh['nshards'] == NSH and sh['target'] == '2.552'
            and isinstance(s, int) and 0 <= s < NSH):
        die('bad shard header')
    cells = {}
    for key_, tree in sh['cells'].items():
        i = int(key_)
        if i % NSH != s or not (0 <= i < NCELLS) or i in cells:
            die('bad or duplicate root cell %d' % i)
        cells[i] = tree
    for i in cells_sel:
        if i not in cells:
            die('cell %d not in shard %d' % (i, s))
    print('shard', s, 'sha256', sha, 'cells', sorted(cells), 'verts', len(sh['verts']), flush=True)

    # cut, leaves, first-use vertex numbering
    cinfo = []          # per cell: dict
    order = {}          # key -> vertex index
    gchunk = 0          # global chunk counter (K/L module ranges)
    for i in cells_sel:
        memo, subs = {}, []
        top = cut(cells[i], root_ms_h(i), [2] * D, a.lcap, memo, subs)
        bl = boxes_of(top, root_ms_h(i), [2] * D)
        if bl != [(ms, js) for _, ms, js in subs]:
            die('boxesOf mirror mismatch, cell %d' % i)
        sinfo, p = [], 0
        for b, (node, ms, js) in enumerate(subs):
            lv = []
            leaves_of(node, ms, js, lv)
            sinfo.append(dict(node=node, ms=ms, js=js, p0=p, n=len(lv), leaves=lv))
            p += len(lv)
        nleaves = p
        if nleaves != count_leaves(cells[i], {}):
            die('leaf count')
        cinfo.append(dict(i=i, top=top, subs=sinfo, nleaves=nleaves, chunk0=gchunk))
        gchunk += nleaves * 9
    # vertices: every key of every leaf in full mode; the sampled sub-boxes' keys otherwise
    leaf_vidx = {}      # (i, p) -> list of 729 vertex indices (only where vertices are generated)
    for c in cinfo:
        for b, sb in enumerate(c['subs']):
            if a.novert or (a.sample_subs and b >= a.sample_subs):
                continue
            for q, (lms, ljs) in enumerate(sb['leaves']):
                idxs = []
                for key in leaf_keys(lms, ljs):
                    v = order.get(key)
                    if v is None:
                        v = len(order); order[key] = v
                    idxs.append(v)
                leaf_vidx[(c['i'], sb['p0'] + q)] = idxs
    nv = len(order)
    print('cells', [(c['i'], c['nleaves'], len(c['subs'])) for c in cinfo], 'distinct vertices', nv, flush=True)
    vmap_info = None
    if a.vmap:
        # global vertex layer: map every distinct key to its global index (code -> idx lines), no own vertex modules
        need = {pack_key(k): k for k in order}
        glob, vmod_of = {}, {}
        with open(a.vmap) as f:
            for line in f:
                cs, ix, mod = line.split()
                c_ = int(cs)
                if c_ in need:
                    if c_ in glob:
                        die('duplicate code in vertex map: %d' % c_)
                    if not mod.replace('_', '').isalnum():
                        die('bad vertex module name %s' % mod)
                    glob[c_] = int(ix)
                    vmod_of[int(ix)] = mod
        miss = [c_ for c_ in need if c_ not in glob]
        if miss:
            die('keys missing from the vertex map: %d (first code %d)' % (len(miss), miss[0]))
        loc2glob = [0] * nv
        for k, v in order.items():
            loc2glob[v] = glob[pack_key(k)]
        for key_ in leaf_vidx:
            leaf_vidx[key_] = [loc2glob[v] for v in leaf_vidx[key_]]
        vmap_info = dict(file=a.vmap, sha256=sha256_file(a.vmap), keys=nv)
        print('vertex map: %d keys mapped to the global layer' % nv, flush=True)
        nv_own = 0
    else:
        nv_own = nv

    ys = keys = hints = None
    if nv_own:
        # y of the first certificate of each needed key (sequential: ~45 us per entry)
        ytab = {}
        for ent in sh['verts']:
            key = tuple(gk.comp_of_json(kk) for kk in ent[0])
            if len(key) != D:
                die('bad key length')
            if key in order and key not in ytab:
                ytab[key] = gk.y_ints(ent[1])[0]
        del sh
        keys = [None] * nv
        for key, v in order.items():
            keys[v] = key
        missing = [k for k in keys if k not in ytab]
        if missing:
            die('missing vertex certificates: %d (first %s)' % (len(missing), missing[0]))
        ys = [ytab[k] for k in keys]
        del ytab
        # hints (untrusted), parallel helper processes
        hdir = os.path.join(out, 'tmp_hints_' + tag); os.makedirs(hdir, exist_ok=True)
        nch = max(1, min(a.nproc, nv // 2000 + 1))
        bounds = [nv * c // nch for c in range(nch + 1)]
        procs = []
        for c in range(nch):
            fin = os.path.join(hdir, 'in_%03d.txt' % c)
            with open(fin, 'w') as f:
                for v in range(bounds[c], bounds[c + 1]):
                    k, y = keys[v], ys[v]
                    f.write(' '.join('%d,%d,%d' % (1 if t else 0, m, j) for t, m, j in k) + '|' +
                            ' '.join('%d,%d' % (y[2 * q], y[2 * q + 1]) for q in range(K)) + '\n')
            procs.append(subprocess.Popen([a.helper, str(K)], stdin=open(fin),
                                          stdout=open(os.path.join(hdir, 'out_%03d.txt' % c), 'w')))
        for pr in procs:
            if pr.wait() != 0:
                die('hint helper failed')
        hints = []
        for c in range(nch):
            for line in open(os.path.join(hdir, 'out_%03d.txt' % c)):
                hints.append(gk.parse_hint_line(line.rstrip('\n')))
        if len(hints) != nv:
            die('hint count %d != %d' % (len(hints), nv))
        print('hints done', flush=True)
        G.update(keys=keys, ys=ys, hints=hints, per_v=a.per_v, out=out, tag=tag)
        gc.freeze()
        nvmod = (nv + a.per_v - 1) // a.per_v
        with mp.get_context('fork').Pool(a.nproc) as pool:
            for _ in pool.imap_unordered(write_vmod, range(nvmod), chunksize=4):
                pass
        print('vertex modules', nvmod, flush=True)
    else:
        nvmod = 0

    # K modules: every chunk of every selected cell (global chunk index = chunk0 + 9 p + c), written in order
    nkmod = (gchunk + a.per_k - 1) // a.per_k
    khead = ('import Bohr59aCore.Format\n' + FMT['kimp'] + '\n/-! Generated by tools/gen_k7split.py: k = 7 leaf key chunks (81 keys each). -/\n\n'
             'open Bohr59aCore' + FMT['kopen'] + '\n' + OPTS)
    cur_km, kbuf = 0, []
    for c in cinfo:
        i = c['i']
        for sb in c['subs']:
            for q, (lms, ljs) in enumerate(sb['leaves']):
                p = sb['p0'] + q
                ks = leaf_keys(lms, ljs)
                if len(ks) != 9 * CH:
                    die('leaf key count')
                for cc in range(9):
                    km = (c['chunk0'] + 9 * p + cc) // a.per_k
                    if km != cur_km:
                        write(os.path.join(out, 'Bohr59aK7HK', '%sK%04d.lean' % (tag, cur_km)), khead + ''.join(kbuf))
                        cur_km, kbuf = km, []
                    kbuf.append('%s kc7_%d_%d_%d : %s := [%s]\n'
                                % (FMT['kdef'], i, p, cc, FMT['kty'], ', '.join(fmt_k(k) for k in ks[cc * CH:(cc + 1) * CH])))
    write(os.path.join(out, 'Bohr59aK7HK', '%sK%04d.lean' % (tag, cur_km)), khead + ''.join(kbuf))
    if cur_km != nkmod - 1:
        die('key module count')
    del kbuf
    print('key modules', nkmod, 'chunks', gchunk, flush=True)

    def kmods_of_chunks(g0, g1):
        return sorted(set(x // a.per_k for x in range(g0, g1)))

    def leaf_expr(i, p):
        return chain(['kc7_%d_%d_%d' % (i, p, cc) for cc in range(9)], '++')

    # L modules (chunks with generated vertices only), grouped by global chunk index
    lmod_of = {}
    lbody = {}
    for c in cinfo:
        i = c['i']
        for sb in c['subs']:
            for q in range(sb['n']):
                p = sb['p0'] + q
                if (i, p) not in leaf_vidx:
                    continue
                idxs = leaf_vidx[(i, p)]
                for cc in range(9):
                    gidx = c['chunk0'] + 9 * p + cc
                    lm = gidx // a.per_l
                    lmod_of[gidx] = lm
                    ent = lbody.setdefault(lm, [[], set(), set()])
                    vs = idxs[cc * CH:(cc + 1) * CH]
                    if a.vmap:
                        links = [a.vname % v for v in vs]
                        ent[1].update(vmod_of[v] for v in vs)
                    else:
                        links = [FMT['link'] % (tag, v) for v in vs]
                        ent[1].update(v // a.per_v for v in vs)
                    ent[0].append('theorem cv7_%d_%d_%d : allP %s kc7_%d_%d_%d :=\n  ⟨%s⟩\n'
                                  % (i, p, cc, FMT['pred'], i, p, cc, ', '.join(links + ['trivial'])))
                    ent[2].add(gidx // a.per_k)
    for lm, (body, vneed, kneed) in sorted(lbody.items()):
        vimps = (['import %s.%s\n' % (a.vprefix, m) for m in sorted(vneed)] if a.vmap else
                 ['import Bohr59aK7HV.%sV%04d\n' % (tag, m) for m in sorted(vneed)])
        head = ['import %s\n' % FMT['predimp']] + ['import Bohr59aK7HK.%sK%04d\n' % (tag, m) for m in sorted(kneed)] + vimps
        write(os.path.join(out, 'Bohr59aK7HL', '%sL%04d.lean' % (tag, lm)),
              ''.join(head) + '\n/-! Generated by tools/gen_k7split.py: links of k = 7 key chunks to their vertex theorems. -/\n\n'
              'open Bohr59aK Bohr59aCore Bohr59aSplitK\n' + OPTS + ''.join(body))
    nlmod = len(lbody)
    del lbody
    print('link modules', nlmod, flush=True)

    # W and A modules: consecutive sub-boxes of one cell, at most WCAP key refs per module (at least one sub-box)
    wmods = []          # (cell index position, [sub-box indices])
    for ci, c in enumerate(cinfo):
        cur, refs = [], 0
        for b, sb in enumerate(c['subs']):
            r = sb['n'] * 9 * CH
            if cur and refs + r > a.wcap:
                wmods.append((ci, cur)); cur, refs = [], 0
            cur.append(b); refs += r
        if cur:
            wmods.append((ci, cur))
    amod_of = {}
    nwmod = namod = 0
    for wm, (ci, bl) in enumerate(wmods):
        c = cinfo[ci]; i = c['i']
        g0 = c['chunk0'] + 9 * c['subs'][bl[0]]['p0']
        g1 = c['chunk0'] + 9 * (c['subs'][bl[-1]]['p0'] + c['subs'][bl[-1]]['n'])
        body = []
        for b in bl:
            sb = c['subs'][b]
            body.append('def tree7_%d_%d : Tree := %s\n' % (i, b, gk.fmt_tree(sb['node'])))
            body.append('%s kls7_%d_%d : %s := [%s]\n'
                        % (FMT['kdef'], i, b, FMT['klsty'], ', '.join('(%s)' % leaf_expr(i, sb['p0'] + q) for q in range(sb['n']))))
            body.append('theorem sw7_%d_%d : %s tree7_%d_%d %s %s kls7_%d_%d = some [] := by\n  decide +kernel\n\n'
                        % (i, b, FMT['walk'], i, b, fmt_ints(sb['ms']), fmt_nats(sb['js']), i, b))
        head = ['import %s\n' % FMT['walkimp']] + ['import Bohr59aK7HK.%sK%04d\n' % (tag, m) for m in kmods_of_chunks(g0, g1)]
        write(os.path.join(out, 'Bohr59aK7HW', '%sW%04d.lean' % (tag, wm)),
              ''.join(head) + '\n/-! Generated by tools/gen_k7split.py: k = 7 sub-box trees, per-leaf key lists and kernel walks. -/\n\n'
              'open Bohr59aK Bohr59aCore' + FMT['wopen'] + '\n' + OPTS + ''.join(body))
        nwmod += 1
        # A module: the sub-boxes of the group whose vertices were generated
        abl = [b for b in bl if (i, c['subs'][b]['p0']) in leaf_vidx]
        if not abl:
            continue
        body, lneed = [], set()
        for b in abl:
            sb = c['subs'][b]
            lvs = []
            for q in range(sb['n']):
                p = sb['p0'] + q
                cvs = ['cv7_%d_%d_%d' % (i, p, cc) for cc in range(9)]
                lneed.update(lmod_of[c['chunk0'] + 9 * p + cc] for cc in range(9))
                body.append('theorem lv7_%d_%d : allP %s (%s) :=\n  %s\n' % (i, p, FMT['pred'], leaf_expr(i, p), app_chain(cvs)))
                lvs.append('lv7_%d_%d' % (i, p))
            body.append('theorem sv7_%d_%d : allP (allP %s) kls7_%d_%d :=\n  ⟨%s⟩\n\n' % (i, b, FMT['pred'], i, b, ', '.join(lvs + ['trivial'])))
            amod_of[(i, b)] = wm
        head = ['import %s\nimport Bohr59aK7HW.%sW%04d\n' % (FMT['predimp'], tag, wm)] + \
            ['import Bohr59aK7HL.%sL%04d\n' % (tag, m) for m in sorted(lneed)]
        write(os.path.join(out, 'Bohr59aK7HA', '%sA%04d.lean' % (tag, wm)),
              ''.join(head) + '\n/-! Generated by tools/gen_k7split.py: k = 7 per-leaf and per-sub-box links. -/\n\n'
              'open Bohr59aK Bohr59aCore Bohr59aSplitK\n' + OPTS + ''.join(body))
        namod += 1
    print('walk modules', nwmod, 'link-assembly modules', namod, flush=True)

    # G modules and the cell modules (full mode)
    ngmod = 0
    if full:
        for c in cinfo:
            i, subs = c['i'], c['subs']
            groups = [list(range(x, min(len(subs), x + a.gcap))) for x in range(0, len(subs), a.gcap)]
            for gi, bl in enumerate(groups):
                bs = ', '.join('(%s, %s)' % (fmt_ints(subs[b]['ms']), fmt_nats(subs[b]['js'])) for b in bl)
                prf = ', '.join(['%s sw7_%d_%d sv7_%d_%d' % (FMT['box'], i, b, i, b) for b in bl] + ['trivial'])
                head = ['import %s\n' % FMT['glueimp']] + ['import Bohr59aK7HA.%sA%04d\n' % (tag, m) for m in sorted(set(amod_of[(i, b)] for b in bl))]
                write(os.path.join(out, 'Bohr59aK7HG', '%sC%dG%02d.lean' % (tag, i, gi)),
                      ''.join(head) + '\n/-! Generated by tools/gen_k7split.py: box property of the sub-boxes of a k = 7 cell. -/\n\n'
                      'open Bohr59aK Bohr59aCore Bohr59aSplitK Bohr59a.Cert Bohr59a.CertK\n' + OPTS +
                      'def bsg7_%d_%d : List (List Int × List Nat) := [%s]\n\n' % (i, gi, bs) +
                      'theorem gok7_%d_%d : allP (fun b : List Int × List Nat => BoxOK 6 %s b.1 b.2) bsg7_%d_%d :=\n  ⟨%s⟩\n'
                      % (i, gi, B_EXPR, i, gi, prf))
                ngmod += 1
            rhs = chain(['bsg7_%d_%d' % (i, gi) for gi in range(len(groups))], '++')
            hb = app_chain(['gok7_%d_%d' % (i, gi) for gi in range(len(groups))])
            head = ['import %s\n' % FMT['glueimp']] + ['import Bohr59aK7HG.%sC%dG%02d\n' % (tag, i, gi) for gi in range(len(groups))]
            write(os.path.join(out, 'Bohr59aK7HG', '%sC%d.lean' % (tag, i)),
                  ''.join(head) + '\n/-! Generated by tools/gen_k7split.py: the k = 7 half-domain cell %d from its sub-boxes. -/\n\n' % i +
                  'open Bohr59aK Bohr59aCore Bohr59aSplitK Bohr59a.Cert Bohr59a.CertK\n' + OPTS +
                  'def top7_%d : Tree := %s\n\n' % (i, gk.fmt_tree(c['top'])) +
                  'theorem topok7_%d : boxesOf top7_%d (rootMsH 5 %d) (List.replicate 6 2) = some (%s) := by\n  decide +kernel\n\n'
                  % (i, i, i, rhs) +
                  'theorem cellH7_%d : CellOKH 5 %s %d :=\n  cellOKH_of_boxesOf (D := 5) topok7_%d (%s)\n' % (i, B_EXPR, i, i, hb))
    print('glue modules', ngmod, flush=True)

    st = dict(k=K, tag=tag, shard=s, shard_sha256=sha, cells=[
        dict(i=c['i'], leaves=c['nleaves'], subboxes=len(c['subs']), max_sub_leaves=max(sb['n'] for sb in c['subs']),
             top_depth=max(sum(sb['js']) - 2 * D for sb in c['subs']), key_refs=c['nleaves'] * 9 * CH,
             sub_leaves=[sb['n'] for sb in c['subs']]) for c in cinfo],
        mode='full' if full else ('novert' if a.novert else 'sample%d' % a.sample_subs), keyfmt=a.keyfmt, distinct_vertices=nv,
        vertex_map=vmap_info,
        lcap=a.lcap, per_v=a.per_v, per_k=a.per_k, per_l=a.per_l, wcap=a.wcap, gcap=a.gcap,
        modules=dict(V=nvmod, K=nkmod, L=nlmod, W=nwmod, A=namod, G=ngmod + (len(cinfo) if full else 0)),
        generator_sha256=sha256_file(os.path.abspath(__file__)), gen_k6_sha256=sha256_file(os.path.join(HERE, 'gen_k6.py')))
    os.makedirs(os.path.join(out, 'stats'), exist_ok=True)
    json.dump(st, open(os.path.join(out, 'stats', 'K7H_%s.json' % tag), 'w'), indent=1)
    print(json.dumps({k: v for k, v in st.items() if k != 'cells'}))
    for cs in st['cells']:
        print('cell', cs['i'], 'leaves', cs['leaves'], 'subboxes', cs['subboxes'], 'max_sub_leaves', cs['max_sub_leaves'])


if __name__ == '__main__':
    main()
