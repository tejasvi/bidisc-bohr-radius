# Kernel-only Lean proof of S₇ ≤ 2.552

This directory contains a proof in Lean 4 of the bound S₇ ≤ 2.552 for the Sidon constant S₇ = S({0, 1, …, 7}), from the
certificate for S₇ of the paper. Every check runs in the Lean kernel: the proof does not use `native_decide`, so its
trusted base is Lean's kernel, including the kernel's built-in arithmetic on natural numbers. Section 7 of the paper
describes it.

The main theorem is in `Bohr59aK7G/Final.lean`, one of the generated files described below:

    theorem Bohr59aK.sidon7K : Bohr59a.SidonBound 7 (2552 / 1000)

`SidonBound` is the definition of `../lean/` (`Bohr59a/Slice.lean`).

## The bound for K₂

Under the hypothesis `PatelColligation` (Lemma 3.4 of the paper), K₂ ≥ 0.301665 follows from four theorems in which
every check is run by the kernel; they are not combined into a single Lean theorem:

- `Bohr59aK.sidon5K : SidonBound 5 (2187 / 1000)` and `Bohr59aK.sidon6K : SidonBound 6 (2363 / 1000)`, in
  `../lean_kernel/`;
- `Bohr59aK.sidon7K : SidonBound 7 (2552 / 1000)`, in this directory;
- `Bohr59a.K2_ge_of_sidon7 : PatelColligation → SidonBound 5 (2187 / 1000) → SidonBound 6 (2363 / 1000) →
  SidonBound 7 (2552 / 1000) → 60333 / 200000 ≤ K2` (`Bohr59a/FinalV3b.lean`, in `../lean/` and in this directory),
  which uses only the three standard axioms.

The four statements fit together because the files that define `SidonBound`, `K2` and `PatelColligation` (the import
closure of `Bohr59a/Slice.lean`, `Statement.lean` and `Hypotheses.lean`), and the further files that `FinalV3b.lean`
imports, are the same in `../lean/`, `../lean_kernel/` and this directory, and the three projects use the same Lean
toolchain and Mathlib commit. `COMPOSITION/compose_check.txt`, written by `tools/k7_compose_check.py` on the three
directories of this repository, lists the checksums of these files and the result of the comparison.
`COMPOSITION/AxCompose.lean` prints the type of `Bohr59a.K2_ge_of_sidon7` and its axioms in this project, and the types
of `SidonBound`, `K2` and `PatelColligation`; `COMPOSITION/AxCompose.out` is the expected output. The 21 source files
that this directory shares with `../lean/`, including the 15 files under `Bohr59a/`, are the same in both.

## Axioms

`lake env lean AxK7.lean` prints the statement of the main theorem and its axioms; `AXIOMS.txt` is the expected output.
The axioms are only the three standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## How the proof works

The certificate for S₇ consists of 576 files (shards). It covers the phases with φ₂ in [0, π] (in the notation of the
paper) by 2,048 cells of the initial grid, which its trees divide into 210,960 boxes, and it holds 65,041,100 vertex
certificates. A vertex that occurs in several shards has a certificate in each; there are 46,344,804 distinct vertex
labels. The proof has 94,510 generated modules.

- `Bohr59aK7V/` has one theorem for each distinct vertex, in 46,634 modules of at most 1,000 vertices each; the
  vertices that first occur in shard `sss` are in its modules `Ssss_kkkk`. Each theorem is proved by `decide +kernel`:
  the kernel evaluates the vertex check `vertexOKKpF3` (`Bohr59aCoreK/FastArith3.lean`) on the vertex certificate,
  whose entries of y are packed into one natural number together with a matrix W and a vector x, as in
  `../lean_kernel/`. Any W and x would do, since the kernel checks every inequality exactly for the values it is given.
- Each of the 1,594 cells with at most 64 boxes has a module in `Bohr59aK7C/` with the tree of its boxes, the vertex keys
  of each box and a theorem, proved by `decide +kernel`, that the walk over the boxes of the cell uses exactly these
  keys. `Bohr59aK7K/` splits the keys of each box into chunks of at most 81, and `Bohr59aK7L/` gives each key of a chunk
  its vertex theorem (9,888 modules each). `Bohr59aSplitK.cellOK_of_KC7` turns this into the bound on the cell.
- The other 454 cells, with 162,097 boxes, are cut into sub-boxes of at most 64 boxes each (`tools/gen_k7split.py`,
  one run per shard; the cells and shards are listed in `split_plan.json`). Their modules are in `Bohr59aK7HK/` (7,452
  modules, the key chunks), `Bohr59aK7HL/` (16,346, the links to the same vertex theorems), `Bohr59aK7HW/` (870, the
  trees of the sub-boxes and their walks), `Bohr59aK7HA/` (870, the assembly of each sub-box) and `Bohr59aK7HG/` (935,
  the bound on each cell from the tree of its sub-boxes, by `Bohr59a.CertK.cellOKH_of_boxesOf`). A walk theorem needs
  about 50 KB of kernel memory for each key it refers to, and the limit of 64 boxes keeps each walk module at about
  2.6 GiB or less.
- The 32 modules `Bohr59aK7G/G00`, …, `G31` collect the bounds on the cells, and `Bohr59aK7G/Final.lean` proves
  `sidon7K` with `Bohr59a.Cert.sidon_of_cells_half` (`Bohr59a/CertHalf.lean`), which covers the other half of the phases
  by Lemma 4.1(e) of the paper. The generator also writes `Bohr59aK7G/Headline.lean`, which applies
  `Bohr59a.K2_ge_of_sidon7` to the three Sidon theorems. It imports modules of `../lean_kernel/` that this project does
  not contain, so it was never built or checked, and it is not one of the 94,510 modules of the proof. It is in the
  archive, but its theorem `K2_ge_K7` and its docstring are not claims of this release; the claim is the composition of
  four theorems described in "The bound for K₂".
- The checking program is in `Bohr59aCoreK/` and `Bohr59aSplitK/`, in core Lean with only integers and structural
  recursion. Its correctness is proved, with the standard axioms only, in `Bohr59a/CertK.lean`, `CertFast.lean`,
  `CertFast2.lean`, `CertFast3.lean`, `CertHalfK.lean`, `CertSplit.lean`, `CertHalf.lean` and
  `Bohr59aSplitK/CodeWalkSound.lean`.

## Files

- `Bohr59a/`, `Bohr59aCore/`, `C64Core/`, `C64/`, `Bohr59aCoreK/`, `Bohr59aSplitK/`: the sources described above.
- `tools/`: `gen_k7.py` writes the vertex modules, the global index of the vertex keys and the modules of the cells with
  at most 64 boxes; `k7_split_plan.py` lists the cells of each kind; `gen_k7split.py` writes the modules of the other
  cells, with the conventions of `gen_k6.py`, a copy of the generator of `../lean_kernel/`; `gen_k7_final.py` writes
  `Bohr59aK7G/`; `k7_compose_check.py` writes `COMPOSITION/compose_check.txt`. `KHints.lean` is the main file of the
  program `k6hints` of `../lean_kernel/`, which computes W and x for the generators. None of these programs is part of
  the proof.
- `stats/`: for each shard, the number of vertices it owns and of their modules (`K7V_S<sss>.json`); for the cells with
  at most 64 boxes, their boxes, chunks and modules (`K7C_0000_2047.json`); for each run of `gen_k7split.py`, the cells,
  sub-boxes and modules with the checksums of the shard and of the generators (`K7H_H<sss>.json`).
- `split_plan.json`: the cells with at most 64 boxes and, for each shard, the cells that are cut into sub-boxes.
- `generated_k7_SHA256SUMS`: the SHA-256 checksums of the 94,511 generated files, the 94,510 modules of the proof and
  `Bohr59aK7G/Headline.lean`.
- `COMPOSITION/`: the composition check and the axiom query described above.
- `AxK7.lean`, `AXIOMS.txt`: the axiom query and its expected output.
- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`: the project configuration.

The generated modules are not included. The 47,877 generated files other than the vertex modules are in
`generated_k7_nonvertex.tar.zst` in the archive record (612,416,942 bytes, SHA-256
`721fff8747f7e09b98d02777f988bf71e7c3344295e7b9968808b06a65ada272`), together with `index/split_plan.json`. The 46,634
vertex modules (about 160 GB as source files) are not distributed; they are generated from the certificate as
described below.

## Generating the modules

As with `../lean/`, install `elan`; `lean-toolchain` and `lake-manifest.json` select Lean `v4.35.0-rc3` and Mathlib
commit `c55e6e786f49471c72fbddbec5415808896aec1e`. Unpack the 576 files of the certificate for S₇ into
`../certificate/s7_certificate/`, as described in `../README.md`, and build the program `k6hints` in `../lean_kernel/`
(`lake exe cache get`, then `lake build k6hints` there). Copy this directory to a new working directory and run, in
the copy, with `R` set to the absolute path of the repository,

    lake exe cache get
    H=$R/lean_kernel/.lake/build/bin/k6hints
    mkdir -p v3b
    ln -s "$R/certificate/s7_certificate" v3b/bb7
    python3 -I -B tools/gen_k7.py index v3b . 60
    python3 -I -B tools/gen_k7.py vertex v3b . "$H" 60 0-575
    python3 -I -B tools/k7_split_plan.py index index/split_plan.json
    D=$(python3 -I -B -c 'import json; print(",".join(map(str, json.load(open("index/split_plan.json"))["direct"])))')
    python3 -I -B tools/gen_k7.py cells . 60 "$D"
    python3 -I -B -c 'import json; d = json.load(open("index/split_plan.json"))["split"]; print("\n".join("%s %s" % (s, ",".join(map(str, c))) for s, c in d.items()))' |
      while read s c; do python3 -I -B tools/gen_k7split.py v3b/bb7/sh$s.json . "$H" 1 H$(printf %03d $s) "$c" --vmap index/vmap.txt; done
    python3 -I -B tools/gen_k7_final.py . index/split_plan.json
    sha256sum -c generated_k7_SHA256SUMS

The generators read the file names `bb7/sh0.json`, …, `bb7/sh575.json`, hence the link. The number 60 is the number of
processes. They also rewrite the files in `stats/`. The vertex modules do not depend on how the shards are divided
among runs, so the second command can also be run in parts, for example on several machines. Neither the generators
nor `k6hints` need be trusted: the walk theorems force the key list of each box to be exactly its vertex keys, each key
carries its own kernel-checked vertex theorem, and the kernel checks every vertex certificate with the W and x it is
given. To use the archived modules instead of generating the others, unpack the archive in the working directory with
`zstd -dc /path/to/generated_k7_nonvertex.tar.zst | tar -xf -` and run the commands above only up to the second Python
command, which writes the vertex modules; the final checksum check applies in both cases.

## Building

In the working directory, run

    lake build Bohr59aK7G.Final
    lake env lean AxK7.lean
    lake build Bohr59a.FinalV3b
    lake env lean COMPOSITION/AxCompose.lean

Plain `lake build` builds nothing here, since the default target is empty. The outputs of the two `lake env lean`
commands should agree with `AXIOMS.txt` and `COMPOSITION/AxCompose.out`.

The build is long. In the reference build the vertex modules ran 64 at a time on each machine. A vertex module took 293
seconds on average (291 seconds median, at most 375 seconds, over the 30,035 modules whose times were recorded) and
about 145 seconds and 0.8 GiB of memory when built alone; the vertex modules took about 3,800 hours in all. The other
modules took about 2.3 hours on one machine with 64 threads and 512 GiB of memory: the key and walk modules 30 minutes,
the links and cells 64 minutes, the 32 glue modules 27 minutes with four at a time, and `Bohr59aK7G/Final.lean` 229
seconds (993 seconds with lake's trace checks). In all, the build took about 3,900 hours of single-threaded processes.
In a sample of 29 generated modules built again one at a time after the build, the largest resident size was about 0.8
GiB for vertex, key and link modules (about 1.05 GiB for the links of cut cells), up to 2.5 GiB for cell modules, up to
2.6 GiB for walks, up to 3.6 GiB for the assemblies of cut cells, up to 11 GiB for their glue modules and 15 to 26 GiB
for the 32 glue modules of `Bohr59aK7G/`; these sizes are mostly compiled files mapped from disk. During the build,
sampled once a minute, the largest process reached 16 GiB in the cell phase, 60 GiB in the glue phase and 257 GiB in the
final module, while the memory in use on the machine never exceeded 80 GiB. Since `lake build` may start many glue
modules at once, building them a few at a time keeps the memory within bounds.

## Notes on the archived files

- `tools/gen_k7split.py` differs from the copy used for the reference build only in its module docstring, from which
  internal names were removed; `stats/K7H_H<sss>.json` record the SHA-256 checksum of the copy used (`6d847b8a…`), and a
  new run records that of this copy.
- `Bohr59aCoreK/TrigTab.lean` differs from the file used for the reference build only in a comment, and is the same as
  in `../lean_kernel/`.
- `generated_k7_nonvertex.tar.zst` and `generated_k7_SHA256SUMS` also contain `Bohr59aK7G/Headline.lean`, which was
  never built or checked; see "How the proof works".
