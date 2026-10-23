# Format of the Sidon-constant certificates

`s5_certificate.json` certifies S({0,1,...,5}) <= 2.187 (Proposition 4.2 of the paper). It is a JSON object with these fields.

- `k`: the degree, here 5. The certificate concerns polynomials c_0 + c_1 z + ... + c_k z^k.
- `target`: the bound, as a decimal string ("2.187"). The checker takes the bound from its command line and ignores
  this field.
- `n0`: the number of cells per coordinate in the initial grid, here 8.
- `tree`: a list of n0^(k-1) = 4096 nodes, one for each cell of the initial grid. The cells are listed in the order of
  `itertools.product(range(n0), repeat=k-1)`. Cell (i_1, ..., i_{k-1}) has centre -1 + (2 i_d + 1)/n0 and half-width
  1/n0 in coordinate d. Coordinates are phases in units of pi, so the cells tile [-1, 1]^(k-1), that is, the phases
  (phi_2, ..., phi_k) in [-pi, pi]^(k-1).
  A node is either the string `"L"` (a leaf box) or a list `["S", d, low, high]`: the box is cut in half at the
  midpoint of coordinate d (0-based), and `low` and `high` are the nodes of the lower and upper halves.
- `verts`: a list of entries `[key, y]`, one for each vertex label that occurs. A vertex with a coordinate equal to -1
  occurs with two labels, phase -pi and phase pi, and has an entry for each.
  - `key` has k-1 components, one per coordinate. `["c", "p/q"]` is the point exp(i pi p/q) on the unit circle, an end
    of an arc. `["t", "c", "h"]` is the point exp(i pi c)/cos(pi h), the third vertex of the triangle around the arc of
    centre pi c and half-width pi h (Lemma 4.1(d)). The numbers are exact fractions written as strings.
  - `y` is a list of 2k floating-point numbers, the real and imaginary parts of y_1, ..., y_k. They define the Hermitian
    Toeplitz matrix T(y) of size k+1 with unit diagonal and T(y)_{jl} = y_{l-j} for l > j. The checker reads each float
    as an exact binary number and works with it in ball arithmetic.

For a leaf with centre c and half-widths h, the 3^(k-1) vertices are all combinations, one per coordinate, of
`["c", c_d - h_d]`, `["c", c_d + h_d]` and `["t", c_d, h_d]`. With w_0 = w_1 = 1 and w_{d+2} the point of component d, the
checker requires for each vertex w that T(y) is positive definite (all leading principal minors positive) and that
w* T(y)^{-1} w < 2.187^2.

## The sharded certificate for S({0, ..., 6})

The certificate for S({0,1,...,6}) <= 2.363 is split into 48 files `s6_certificate/sh0.json`, ..., `sh47.json`. Each is a
JSON object with the fields `k` (6), `target` ("2.363"), `n0` (8), `shard` and `nshards` (48), `cells` and `verts`.
`cells` maps the index of a cell of the initial grid (as a string; cells are numbered in the order of
`itertools.product(range(n0), repeat=k-1)`) to its tree, in the format of `tree` above. Shard s holds the cells with
index congruent to s modulo 48. `verts` holds the vertex certificates that the boxes of these cells need, in the format
above; a vertex shared by cells of different shards has a certificate in each shard. `check/check_shard.py` checks one
shard and prints the cells it covered, together with the name of the file and its SHA-256 checksum, and
`check/check_cover.py` checks that the 48 shards cover all 8^5 = 32,768 cells exactly once.

## The sharded certificate for S({0, ..., 7})

The certificate for S({0,1,...,7}) <= 2.552 is split into 576 files `s7_certificate/sh0.json`, ..., `sh575.json`, in the
format of the previous section with `k` 7, `target` "2.552", `n0` 4, `nshards` 576 and the extra field `domain` with value
"half". It covers only phi_2 in [0, pi], which suffices by Lemma 4.1(e) of the paper: conjugation maps the phases
(phi_2, ..., phi_7) to (-phi_2, ..., -phi_7) and does not change the value. The initial grid has n0/2 = 2 cells in the
first coordinate, with centres 1/4 and 3/4 (in units of pi), and n0 = 4 cells on [-1, 1] in each of the other five; all
cells have half-width 1/4. The cells are numbered in the order of
`itertools.product(range(n0 // 2), range(n0), ..., range(n0))`, so there are 2 * 4^5 = 2,048 of them, and shard s holds
the cells with index congruent to s modulo 576. `check/check_cover.py` checks that the 576 shards cover all 2,048 cells
exactly once.
