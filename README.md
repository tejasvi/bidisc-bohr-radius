# A lower bound for the Bohr radius of the bidisc (version 6)

This repository contains the computer-assisted parts of the paper of the same title by Tejasvi Singh Tomar (Zenodo,
[doi:10.5281/zenodo.23716439](https://doi.org/10.5281/zenodo.23716439)): certificates for upper bounds on three Sidon
constants, the programs that check them and the final inequality, a check of the computation in an earlier argument, the
programs that produced the certificates, and the Lean 4 proofs. The archive record
[doi:10.5281/zenodo.23716440](https://doi.org/10.5281/zenodo.23716440) contains this repository and, in
`s6_certificate.tar.gz` and `s7_certificate.tar.gz`, the files (shards) of the second and third certificates, which are
too large for this repository (3.4 GB and 26.8 GB unpacked). It also holds `generated_k7_nonvertex.tar.zst`, with
generated Lean files of the proof in `lean_kernel_s7/`.

Earlier versions of this record: [doi:10.5281/zenodo.23538814](https://doi.org/10.5281/zenodo.23538814) (version 1, K₂ >
0.301657), [doi:10.5281/zenodo.23547342](https://doi.org/10.5281/zenodo.23547342) (version 2, with a Lean proof of K₂ ≥
0.301657 and a kernel-only Lean proof of K₂ ≥ 0.301633),
[doi:10.5281/zenodo.23553495](https://doi.org/10.5281/zenodo.23553495) (version 3, K₂ > 0.301665, with two Lean proofs
of K₂ ≥ 0.301657), [doi:10.5281/zenodo.23559325](https://doi.org/10.5281/zenodo.23559325) (version 4, with a Lean proof
of K₂ ≥ 0.301665 and a kernel-only Lean proof of K₂ ≥ 0.301657) and
[doi:10.5281/zenodo.23579053](https://doi.org/10.5281/zenodo.23579053) (version 5, which added the kernel-only Lean
proof of S₇ ≤ 2.552). Version 6 revises the presentation of the paper; the results, certificates, programs and Lean
files are those of version 5.

## The result

The Bohr radius K₂ of the bidisc is the largest r such that every holomorphic f(z, w) = Σ c_jk z^j w^k on the bidisc
with |f| ≤ 1 satisfies Σ |c_jk| r^(j+k) ≤ 1. The paper proves

    K₂ > 0.301665.

The previous lower bounds were 0.3006, by G. Knese (Proc. Amer. Math. Soc. Ser. B 12 (2025)), and 0.30158758, by an
unrefereed argument that S. Patel posted on MathDB in August 2026 (problem 392062). The paper presents Patel's argument
in full detail and improves its estimates in degrees five, six and seven. The smallest known upper bound is K₂ <
0.302825279492, also by Patel and also unrefereed (Zenodo, doi:10.5281/zenodo.22341928).

## How the proof works

1. **Normalization** (Patel). If |f| ≤ 1 and f(0) = t lies in [0, 1), then H = (1 − f)/(1 − t) has positive real part
   and H(0) = 1, and the coefficients of positive degree of f are those of H times −(1 − t). So it suffices to show
   M_r(H) = Σ_n ‖H_n‖₁ rⁿ ≤ 1 for all such H, where ‖H_n‖₁ is the sum of the moduli of the coefficients of degree n.
2. **Degrees two and three** (Patel). Three coefficient inequalities, one of them from the unitary realization of Schur
   functions on the bidisc, give ‖H₂‖₁ + r‖H₃‖₁ ≤ B(r) for an explicit function B with parameters α, β, γ.
3. **The other degrees.** On each slice λ ↦ H(λζ₁, λζ₂), Carathéodory's inequality gives ‖H_n‖₁ ≤ 2 S_n, where S_n is the
   Sidon constant of {0, 1, ..., n}. The proof uses S₁ = 1, S₄ ≤ 2, the bounds S₅ ≤ 2.187, S₆ ≤ 2.363 and S₇ ≤ 2.552
   certified here, and S_n ≤ √n, a bound of D. J. Newman, for the other n.
4. **The final inequality.** With r* = 60333/200000 and explicit rational α, β, γ, the majorant E(r*) of Section 5 of the
   paper is a rational number below 1.

## Checking

The certificate checkers need Python 3 and `python-flint` (tested with Python 3.12.13 and python-flint 0.9.0, which
ships FLINT 3.6.0). With the option `-I`, Python ignores the user's site-packages, so `python-flint` must be installed
for the interpreter itself, system-wide or in a virtual environment. The other programs need only Python 3. The five
checking programs refuse to run under `python -O`. Download `s6_certificate.tar.gz` and `s7_certificate.tar.gz` from the
archive record into the root of the repository. Unpack the shards and check them against their checksums with

    tar -xzf s6_certificate.tar.gz -C certificate
    tar -xzf s7_certificate.tar.gz -C certificate
    (cd certificate && sha256sum -c s6_SHA256SUMS && sha256sum -c s7_SHA256SUMS)

Then, from the root of the repository, run

    python3 -I check/check_sidon.py certificate/s5_certificate.json 2.187
    for s in $(seq 0 47); do python3 -I check/check_shard.py certificate/s6_certificate/sh$s.json 2.363 > s6_sh$s.log; done
    for s in $(seq 0 575); do python3 -I check/check_shard.py certificate/s7_certificate/sh$s.json 2.552 > s7_sh$s.log; done
    python3 -I check/check_cover.py certificate/s6_certificate s6_sh*.log
    python3 -I check/check_cover.py certificate/s7_certificate s7_sh*.log
    python3 -I check/check_majorant.py 60333/200000 20674053/62500000 3901457/1562500000 101990031/1000000000 5=2187/1000 6=2363/1000 7=2552/1000
    python3 -I check/check_patel_values.py

The first command checks the certificate for S₅ ≤ 2.187 in about 30 seconds and 0.6 GB of memory on one core, and ends
with `VERIFIED: S({0..5}) <= 2.187 ...`. The runs of `check_shard.py` are independent. A shard of the certificate for S₆
≤ 2.363 takes under a minute and about 0.7 GB on one core. A shard of the certificate for S₇ ≤ 2.552 takes between a few
seconds and 15 minutes, with at most 11.1 GB, and the largest ones dominate. Each run ends with a line `VERIFIED SHARD:
...` that names the shard file, gives its SHA-256 checksum and lists the cells of the initial grid it covered. Then
`check_cover.py` recomputes the checksum of every shard file named in these lines, checks that the lines cover each cell
exactly once, 32,768 cells for S₆ and 2,048 for S₇, and prints `COVERED: ...`. The certificate for S₇ covers only the
phases with φ₂ in [0, π]; Lemma 4.1(e) of the paper shows that this suffices.

`check_majorant.py` prints E(r*) = 0.99999555680551974754... (truncated) with the bound E(r*) ≤ 0.99999556, followed by
the line `PASS: E(r*) < 1, hence K_2 >= r*`. Note that it exits with status 0 even when it prints `FAIL`, so read its
last line. Its last arguments give upper bounds for the Sidon constants of the listed degrees, here S₅ ≤ 2187/1000, S₆ ≤
2363/1000 and S₇ ≤ 2552/1000. For the other degrees n ≤ 40 it uses S₄ ≤ 2 and √n rounded up to eight decimals, and
beyond degree 40 it bounds √n by n and sums the series exactly.

`check_patel_values.py` checks the numbers displayed in Patel's computation: that B(r) equals his fraction, that his
rational upper bounds for √n are the integers ⌈10⁸√n⌉, that the two parts of his majorant lie below the two bounds he
displays, and that their sum is below 1 − 1/(5·10⁷). It prints `ALL CHECKS OK`. Unlike the other checking programs,
which come from the computation that produced the certificates, it was written for the paper.

`bash check/run_all.sh python3 > run_all.log 2>&1` runs the first check, the coverage checks on the shard logs in
`logs/s6_shards/` and `logs/s7_shards/` with rechecks of two shards of each certificate, the last two checks above, and
the consistency checks below. The coverage checks and the rechecks need the unpacked shards. With `run_all.sh python3
full` it rechecks all shards instead, followed by the coverage checks on the fresh output. The file `logs/run_all.log`
is its output, from a run with all shards unpacked. The logs in `logs/s6_shards/` and `logs/s7_shards/` come from full
runs of the shard checks.

Note that `check_cover.py` trusts that the lines it reads come from `check_shard.py`: the coverage check proves the
bound only for lines produced from the unpacked shards, as in the commands above. The checksums tie the lines to the
shard files, and the shipped logs are a record of such a run.

## Formal proofs in Lean

The directory `lean/` contains a proof of K₂ ≥ 0.301665 in Lean 4 (version v4.35.0-rc3) with Mathlib (commit
c55e6e786f49). The theorem `Bohr59aN7.K2_ge_N7 (hPC : PatelColligation) : (60333 / 200000 : ℝ) ≤ K2` states that the
inequality A₃ + B₂²/2 ≤ 2 of Lemma 3.4 of the paper, which is the hypothesis `PatelColligation`
(`lean/Bohr59a/Hypotheses.lean`), implies K₂ ≥ 60333/200000 = 0.301665, with `K2` defined in
`lean/Bohr59a/Statement.lean`. The proof of that inequality uses Andô's inequality and Agler's realization, which are
not in Mathlib. The certificate checks run as compiled code through `native_decide`, one for the S₅ certificate, one for
each of the 48 S₆ shards and one for each of the 576 S₇ shards, so `#print axioms` lists the three standard axioms and
625 auxiliary axioms (`lean/AXIOMS.txt`). The checking program contains no definitions marked `implemented_by`,
`extern`, `unsafe`, `opaque` or `partial`. The trusted base of these checks includes the Lean compiler, the C compiler
that it uses, the Lean runtime and the compiled core-library functions that the checks call. The theorem
`Bohr59a.K2_ge_patel`, which uses only the standard axioms, proves Patel's bound K₂ ≥ 0.30158758 under the same
hypothesis. The S₇ shards cover only the phases with φ₂ in [0, π]; for them the checking program uses the cells of that
half of the domain, and Lemma 4.1(e) of the paper, proved in Lean, covers the other half. The Lean files that hold the
certificate data are not included, and they need not be trusted, since the correctness proof of the checking program
covers every input that it accepts; `lean/README.md` explains how to generate them from the certificate files and
compare them with the recorded checksums, and how to build the proof.

The directory `lean_kernel/` contains a second proof under the same hypothesis, of the weaker bound K₂ ≥ 0.301657
(theorem `Bohr59aK.K2_ge_K`). It checks the certificates for S₅ and S₆ in the Lean kernel, without `native_decide`, so
`#print axioms` lists only the three standard axioms (`lean_kernel/AXIOMS.txt`), and its trusted base is Lean's kernel,
including the kernel's built-in arithmetic on natural numbers. It does not use the certificate for S₇. Its Lean files
generated from the certificates are not included either; `lean_kernel/README.md` explains how to generate them and build
the proof.

The directory `lean_kernel_s7/` proves the bound for S₇ in the kernel in the same way, as
`Bohr59aK.sidon7K : SidonBound 7 (2552 / 1000)`, with only the three standard axioms (`lean_kernel_s7/AXIOMS.txt`). For
S₇ it checks the same half of the phase domain as the first proof. The theorems `Bohr59aK.sidon5K` and
`Bohr59aK.sidon6K` of `lean_kernel/` give the bounds for S₅ and S₆ in the same way, and `Bohr59a.K2_ge_of_sidon7` of
`lean/`, which also uses only the standard axioms, derives K₂ ≥ 0.301665 from the hypothesis and the three bounds. So,
under the hypothesis, K₂ ≥ 0.301665 follows from four theorems in which every check is run by the Lean kernel; they are
in three separate Lean projects and are not combined into a single theorem. The generated Lean files of
`lean_kernel_s7/` are not included either: the 47,877 of them other than the vertex modules are in
`generated_k7_nonvertex.tar.zst` in the archive record (612,416,942 bytes, SHA-256
`721fff8747f7e09b98d02777f988bf71e7c3344295e7b9968808b06a65ada272`), and `lean_kernel_s7/README.md` explains how to
generate the 46,634 vertex modules from the certificate for S₇ and how to build the proof, which takes about 3,900 hours
of single-threaded processes. The archive also contains `Bohr59aK7G/Headline.lean`, which is not among the 94,510 built
modules: it was never built or checked, and its theorem `K2_ge_K7` is not a claim of this release, whose claim is the
composition of the four theorems above.

This project was checked a second time: all its generated modules were regenerated from the certificate byte for byte, a
complete rebuild gave compiled files byte-identical to those of the first build, and none of the 94,556 compiled modules
declares an axiom. Lean's kernel replayed 50,254 of the modules, namely all those without vertex theorems and every
twentieth vertex module, and nanoda, an independent implementation of the kernel, accepted exports of 580 sampled
modules. The theorems that turn checked cells into the bound were accepted by Lean's kernel through `leanchecker`, by
nanoda and by lean4lean, a second independent implementation; all three rejected copies in which proofs had been
swapped. Altered vertex and cell data were rejected.

## Consistency checks

`check/make_controls.py` writes six altered copies of the S₅ certificate: one vertex certificate removed, a subtree of
boxes removed, a cell of the initial grid removed, one matrix replaced by the identity, a half-width out of range, and a
malformed header. `check_sidon.py` rejects each of them, and also the unaltered certificate with the bound 2.186, which
is less than S₅ = 2.18652977... (Z. Ye et al., 2026). Likewise, `check_shard.py` rejects an S₆ shard with the bound
2.362 and an S₇ shard with the bound 2.551, below the numerical value 2.55166 of S₇, and `check_cover.py` rejects the
logs for S₇ when one is missing or when a log names a shard file that another log also names. Finally,
`check_majorant.py` gives E ≥ 1 at r* + 10⁻⁶, and also with √7, rounded up to eight decimals, in place of 2.552.

## Files

- `paper/`: the LaTeX source and the PDF of the paper.
- `certificate/s5_certificate.json`: the certificate for S₅ ≤ 2.187. `certificate/s6_SHA256SUMS` and
  `certificate/s7_SHA256SUMS`: the checksums of the 48 files of the certificate for S₆ ≤ 2.363 and of the 576 files of
  the certificate for S₇ ≤ 2.552, which are in the archive record. A vertex that occurs in several shards has a
  certificate in each; the certificate for S₆ has 4,333,585 distinct vertex labels. `certificate/FORMAT.md` describes
  the formats.
- `check/`: the five programs of Section 6.1 of the paper, the generator for the altered certificates and the driver
  `run_all.sh`.
- `search/`: the programs that produced the certificates. They are not part of the proof. They need `numpy`, `scipy` and
  `cvxpy` with the solver `clarabel`. The certificate for S₅ came from the 36 runs `python3 sidon_bb2.py 5 2.187 OUT 8
  1/16384 s 36` for s = 0, ..., 35, merged by `merge_bb.py`. The certificate for S₆ came from the 48 runs `python3
  sidon_bb2.py 6 2.363 OUT 8 1/16384 s 48` for s = 0, ..., 47. The certificate for S₇ came from the 576 runs `python3
  sidon_bb3.py 7 2.552 OUT 4 1/4096 s 576` for s = 0, ..., 575, which search the half domain. For the five shards sh50,
  sh289, sh300, sh301 and sh561 the shipped files were instead assembled by `assemble_sub2.py` from sub-box results of
  `sidon_sub.py`, after 6 and, where needed, 12 forced bisections of each cell; some of these sub-box runs used a
  variant of `sidon_sub.py` that skips sub-boxes whose result already exists. `logs/s7_search/` records which shards
  were assembled. `shard_stats.py` prints statistics of shard files. `cert_stats.py` prints statistics for a
  certificate. `sidon_max.py` computes numerical maxima.
- `logs/`: the output of `run_all.sh` (`run_all.log`), of the shard checks (`s6_shards/`, `s7_shards/`, each with the
  output `COVER.log` of the coverage check) and of the search for the certificate for S₇ (`s7_search/`).
- `lean/`: the Lean proof of K₂ ≥ 0.301665 of Section 6.2 of the paper, without the generated data modules (see
  `lean/README.md`).
- `lean_kernel/`: the kernel-only Lean proof of K₂ ≥ 0.301657, whose bounds for S₅ and S₆ Section 6.2 also uses,
  without the generated modules (see `lean_kernel/README.md`).
- `lean_kernel_s7/`: the kernel-only Lean proof of S₇ ≤ 2.552 of Section 6.2, without the generated modules (see
  `lean_kernel_s7/README.md`).
- `SHA256SUMS`: the SHA-256 checksums of all other files.

## Credits

The framework of the proof, that is, the normalization and the estimates in degrees two and three, is due to S. Patel
(MathDB problem 392062). The reduction of the coefficient sums of homogeneous polynomials to Sidon constants is due to
L. Bernal-González, H. J. Cabana, D. García, M. Maestre, G. A. Muñoz-Fernández and J. B. Seoane-Sepúlveda (RACSAM 115
(2021), Paper 44). The bound S_n ≤ √n is due to D. J. Newman (see H. S. Shapiro, MIT thesis, 1951). The Toeplitz bound
behind the certificates is also used by Z. Ye et al., who determined S₅ exactly. The proof does not use their value or
H. Yu et al.'s value S₃ = 5/3.

## License

The code is under the Apache License 2.0 (`LICENSE`). The paper, the certificates and the logs are under CC BY 4.0.
