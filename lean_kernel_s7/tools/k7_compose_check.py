#!/usr/bin/env python3
"""Composition record for the 59a K2 bound from separately frozen packages: sidon5K (K5), sidon6K (K6), sidon7K (K7) and
Bohr59a.K2_ge_of_sidon7 (Bohr59a/FinalV3b.lean, in the N7 tree; also present in the K7 tree). The types of the four
theorems mention SidonBound (Bohr59a/Slice.lean), K2 (Bohr59a/Statement.lean) and PatelColligation
(Bohr59a/Hypotheses.lean); they are Expr-equal across the trees when these files and everything they import are
byte-identical and the toolchain and Mathlib commit are the same.

  type core:  the project files (outside Mathlib, Lean and their dependencies) in the import closure of Bohr59a.Slice,
              Bohr59a.Statement and Bohr59a.Hypotheses in the reference tree; required, byte-identical, in EVERY tree.
  lemma core: the same for Bohr59a.FinalV3b; required in the reference tree, byte-identical in every tree that has it.
For every tree: the counts, the toolchain, the Mathlib rev; then the sha256 of every core file and one verdict line.

usage: k7_compose_check.py REFERENCE_TREE NAME=TREE...   (trees are package roots: lean-toolchain, lake-manifest.json there)
"""
import hashlib, json, os, re, sys

TYPE_ROOTS = ['Bohr59a.Slice', 'Bohr59a.Statement', 'Bohr59a.Hypotheses']
LEMMA_ROOTS = ['Bohr59a.FinalV3b']
EXTERNAL = ('Mathlib', 'Lean', 'Std', 'Init', 'Batteries', 'Aesop', 'Qq', 'ProofWidgets', 'Plausible', 'LeanSearchClient',
            'ImportGraph', 'Lake')


def sha(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()


def imports(path):
    """the modules imported by a Lean file: the import lines before the first other code line (block comments /- -/,
    nested, and line comments -- skipped)"""
    out, depth = [], 0
    for line in open(path, encoding='utf-8'):
        i, n, code = 0, len(line), []
        while i < n:
            if depth == 0 and line.startswith('--', i):
                break
            if line.startswith('/-', i):
                depth += 1; i += 2; continue
            if depth > 0 and line.startswith('-/', i):
                depth -= 1; i += 2; continue
            if depth == 0:
                code.append(line[i])
            i += 1
        t = ''.join(code).strip()
        if not t or t == 'prelude' or t == 'module':
            continue
        if t.startswith('import '):
            out.extend(t.split()[1:])
        else:
            break
    return out

def closure(tree, roots):
    seen, todo = set(), list(roots)
    while todo:
        m = todo.pop()
        if m in seen or m.split('.')[0] in EXTERNAL:
            continue
        seen.add(m)
        p = os.path.join(tree, *m.split('.')) + '.lean'
        if not os.path.exists(p):
            sys.exit('COMPOSE CHECK FAILED: %s not found in the reference tree' % p)
        todo.extend(imports(p))
    return sorted(os.path.join(*m.split('.')) + '.lean' for m in seen)


def mathlib_rev(tree):
    for pkg in json.load(open(os.path.join(tree, 'lake-manifest.json'))).get('packages', []):
        if pkg.get('name') == 'mathlib':
            return pkg.get('rev')
    return None


def main():
    ref = sys.argv[1]
    trees = [a.split('=', 1) for a in sys.argv[2:]]
    tcore = closure(ref, TYPE_ROOTS)
    lcore = [f for f in closure(ref, LEMMA_ROOTS) if f not in tcore]
    want = {f: sha(os.path.join(ref, f)) for f in tcore + lcore}
    tc_ref, mr_ref = open(os.path.join(ref, 'lean-toolchain')).read().strip(), mathlib_rev(ref)
    print('reference tree %s: type core %d files (closure of %s); lemma core %d more files (closure of %s)'
          % (ref, len(tcore), ', '.join(TYPE_ROOTS), len(lcore), ', '.join(LEMMA_ROOTS)))
    ok = True
    for name, tree in trees:
        st = {f: (sha(os.path.join(tree, f)) if os.path.exists(os.path.join(tree, f)) else None) for f in tcore + lcore}
        t_same = all(st[f] == want[f] for f in tcore)
        l_present = [f for f in lcore if st[f] is not None]
        l_same = all(st[f] == want[f] for f in l_present)
        l_note = ('all %d present, identical' % len(lcore) if len(l_present) == len(lcore) and l_same else
                  'absent (the lemma is not in this tree)' if not l_present else
                  '%d of %d present, %s' % (len(l_present), len(lcore), 'identical' if l_same else 'DIFFERENT'))
        tc, mr = open(os.path.join(tree, 'lean-toolchain')).read().strip(), mathlib_rev(tree)
        same = t_same and l_same and tc == tc_ref and mr == mr_ref
        ok = ok and same
        print('%-4s %s\n     type core %s | lemma core %s | toolchain %s | mathlib %s | %s'
              % (name, tree, 'identical' if t_same else 'DIFFERENT', l_note, tc, mr, 'SAME' if same else 'DIFFERENT'))
        for f in tcore + lcore:
            if st[f] is not None and st[f] != want[f]:
                print('     differs: %s' % f)
            elif st[f] is None and f in tcore:
                print('     missing: %s' % f)
    print('type core files:')
    for f in tcore:
        print('  %s  %s' % (want[f], f))
    print('lemma core files:')
    for f in lcore:
        print('  %s  %s' % (want[f], f))
    print('COMPOSE_CHECK', 'OK' if ok else 'FAILED')


if __name__ == '__main__':
    main()
