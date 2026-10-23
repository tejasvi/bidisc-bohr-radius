#!/usr/bin/env python3
"""Write six altered copies of a Sidon-constant certificate into DIR; check_sidon.py must reject each of them.

usage: python3 -I make_controls.py CERTIFICATE.json DIR

drop_vertex: one vertex certificate removed. drop_subtree: the first split cell of the initial grid replaced by its lower
subtree. drop_cell: the last cell of the initial grid removed. zero_y: one y set to zero, so that T(y) = I and
v^* v >= 6 exceeds the bound squared (v_0 = v_1 = 1 and |v_j| >= 1). bad_halfwidth: a vertex key with half-width 1/2. malformed: k is not an integer."""
import json, sys, os
cert, out = sys.argv[1], sys.argv[2]
os.makedirs(out, exist_ok=True)
d = json.load(open(cert))
def save(name, obj): json.dump(obj, open(os.path.join(out, name + '.json'), 'w'))
e = json.loads(json.dumps(d)); e['verts'] = e['verts'][:len(e['verts']) // 2] + e['verts'][len(e['verts']) // 2 + 1:]; save('drop_vertex', e)
e = json.loads(json.dumps(d))
for i, t in enumerate(e['tree']):
    if isinstance(t, list): e['tree'][i] = t[2]; break
save('drop_subtree', e)
e = json.loads(json.dumps(d)); e['tree'] = e['tree'][:-1]; save('drop_cell', e)
e = json.loads(json.dumps(d)); e['verts'][123][1] = [0.0] * len(e['verts'][123][1]); save('zero_y', e)   # T = I: v^*v >= 6 > B^2
e = json.loads(json.dumps(d)); e['verts'][5][0][0] = ['t', e['verts'][5][0][0][1], '1/2'] if e['verts'][5][0][0][0] == 't' else ['t', e['verts'][5][0][0][1], '1/2']; save('bad_halfwidth', e)
e = json.loads(json.dumps(d)); e['k'] = 'three'; save('malformed', e)
print('controls written to', out)
