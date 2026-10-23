# Lean proof of K₂ ≥ 0.301665

This directory contains a proof in Lean 4 of the bound K₂ ≥ 0.301665 for the Bohr radius of the bidisc, under one
hypothesis, the inequality A₃ + B₂²/2 ≤ 2 (Lemma 3.4 of the paper). Section 7 of the paper describes the proof.

The main theorem is in `Bohr59aN7/Final.lean`:

    theorem Bohr59aN7.K2_ge_N7 (hPC : PatelColligation) : (60333 / 200000 : ℝ) ≤ K2

- 60333/200000 = 0.301665. `K2` (`Bohr59a/Statement.lean`) is the supremum of the radii r > 0 at which Bohr's inequality
  holds for every family of coefficients whose power series converges absolutely on the bidisc to values of modulus less
  than 1 (`BohrClass`, `BohrIneq`).
- `PatelColligation` (`Bohr59a/Hypotheses.lean`) states A₃ + B₂²/2 ≤ 2 for the coefficients of every function H on the
  bidisc with H(0) = 1 and positive real part. Its proof in the paper uses Andô's inequality and Agler's realization,
  which are not in Mathlib.

## Axioms

`lake env lean AxN7.lean` prints the statement of the main theorem and the axioms of the main theorem and of
`Bohr59aN7.sidon7`, the bound S₇ ≤ 2.552; `AXIOMS.txt` is the expected output. The axioms of the main theorem are the
three standard axioms `propext`, `Classical.choice` and `Quot.sound`, and 625 auxiliary axioms
`Bohr59aCheck.<NAME>.ok._native.native_decide.ax_1_1`, one per part of the certificates: `NAME` is `K5` for the S₅
certificate, `K6S00`, ..., `K6S47` for the 48 shards of the S₆ certificate and `K7S000`, ..., `K7S575` for the 576
shards of the S₇ certificate. Each comes from a theorem `ok` in `Bohr59aCheck/<NAME>.lean`, proved by `native_decide`,
which runs the compiled checking program. So the trusted base includes the Lean compiler, the C compiler that it uses,
the Lean runtime and the compiled core-library functions that the checks call.

The checking program `checkShard` (`Bohr59aCore/Check.lean`, with the ball arithmetic of `C64Core/Ival.lean`) is written
in core Lean and contains no definitions marked `implemented_by`, `extern`, `unsafe`, `opaque` or `partial`. The S₇
certificate covers only the phases with φ₂ in [0, π] (in the notation of the paper), and its shards are checked by
`checkShardH` (`Bohr59aCore/CheckHalf.lean`), which runs the same checks on the cells of that half of the domain. Every
theorem of the proof that does not use the 625 checks depends only on the three standard axioms. Among them are the
correctness proof of the checking program (`Bohr59a/CertShard.lean`, `CertVertex.lean`, `CertGeom.lean` and
`C64/Ival/`), the reduction to half of the domain by Lemma 4.1(e) of the paper (`Bohr59a/CertHalf.lean`),
`Bohr59a.K2_ge_patel` (`Bohr59a/FinalPatel.lean`), which proves Patel's bound K₂ ≥ 0.30158758 under the same hypothesis,
and `Bohr59a.K2_ge_of_sidon7` (`Bohr59a/FinalV3b.lean`), which derives K₂ ≥ 0.301665 from the hypothesis and the bounds
S₅ ≤ 2.187, S₆ ≤ 2.363 and S₇ ≤ 2.552.

The main theorem takes the bounds for S₅ and S₆ from `Bohr59aN/Final.lean`. That file also contains the theorem of
versions 2 and 3, `Bohr59aN.K2_ge_N`, which derives K₂ ≥ 0.301657 from the first 49 checks alone.

## Files

- `Bohr59a/`: the definitions, the analytic part of the proof and the correctness proof of the checking program.
- `Bohr59aCore/`: the checking program (`Check.lean`, with `CheckHalf.lean` for the half domain), the data format
  (`Format.lean`) and the decoder for the certificate data (`Decode.lean`), compiled to native code.
- `C64Core/Ival.lean` and `C64/Ival/`: ball arithmetic and its correctness proof.
- `Bohr59aCheck/`: the 625 checks, one module per part, written by `tools/gen_checks.py` for S₅ and S₆ and by
  `tools/gen_checks_h.py` for S₇.
- `Bohr59aN/Final.lean` and `Bohr59aN7/Final.lean`: the theorems built on the checks, written by `tools/gen_final_n.py`
  and `tools/gen_final_n7.py`.
- `stats/`: per-part counts and data checksums (`<NAME>.json`), summaries (`DATA_SUMMARY.txt`, `DATA_SUMMARY_K7.txt`),
  and the time and memory that each check took in the reference build (`N_RUN_v2.txt`, `N7_RUN.txt`).
- `tools/`: `export59.py` and `export59h.py` write the data modules from the certificates; the other four write the
  check modules and the two `Final.lean` files.
- `data_SHA256SUMS`: the SHA-256 checksums of the 625 data modules `Bohr59aData/<NAME>.lean` and of the 625 files
  `stats/<NAME>.json` that the exporters rewrite.
- `AxN7.lean`, `AXIOMS.txt`: the axiom query and its expected output.
- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`: the project configuration.

The 625 data modules `Bohr59aData/<NAME>.lean` (about 13 GB) are not included. Each holds one part's data as a base64
string.

## Generating the data modules

Unpack `s6_certificate.tar.gz` and `s7_certificate.tar.gz` into the folder `certificate/` of the repository, as
described in the main README. Then, in this directory, run

    CERT=../certificate
    mkdir -p v3/bb6 v3b
    ln -s "$(cd "$CERT" && pwd)/s5_certificate.json" v3/bb5_t2187.json
    for s in $(seq 0 47); do ln -s "$(cd "$CERT" && pwd)/s6_certificate/sh$s.json" v3/bb6/sh$s.json; done
    ln -s "$(cd "$CERT" && pwd)/s7_certificate" v3b/bb7
    python3 -I -B tools/export59.py k5 v3 .
    python3 -I -B tools/export59.py k6 v3 . $(seq 0 47)
    python3 -I -B tools/export59h.py v3b . $(seq 0 575)
    sha256sum -c data_SHA256SUMS

The exporters read the file names `bb5_t2187.json`, `bb6/sh<s>.json` and `bb7/sh<s>.json`, hence the links. They need
only Python 3. The two runs of `export59.py` take about six minutes on one core, and the run of `export59h.py` about
half an hour, with up to 10 GB of memory for the largest S₇ shards. They also rewrite the files `stats/<NAME>.json`, and
the last command checks those as well. The data modules need not be trusted: the header of each part is fixed in its
check module, and the checking program validates the cells and every vertex certificate it reads.

## Building

Install `elan`, the Lean toolchain manager. `lean-toolchain` selects Lean `v4.35.0-rc3`, and `lake-manifest.json` pins
Mathlib at commit `c55e6e786f49471c72fbddbec5415808896aec1e` (tag `v4.35.0-rc3`). Then run

    lake exe cache get
    lake build Bohr59aN7.Final
    lake env lean AxN7.lean

`lake exe cache get` should download compiled Mathlib files; without them, `lake build` compiles Mathlib from source,
which takes much longer. Plain `lake build` does not work here: its default target needs the file `Bohr59a.lean`, which
is not part of the proof and not included. Each of the 625 check modules runs one check. In the reference build the 49
checks for S₅ and S₆ took between 643 and 1404 seconds and at most about 1 GB of memory each, about 14 CPU-hours in
total (`stats/N_RUN_v2.txt`). The 576 checks for S₇ ran with up to 64 at a time on one machine and took 167.9 hours in
total (`stats/N7_RUN.txt`). Most took minutes; the two largest shards, sh50 and sh301, took about 7.5 hours each, with
up to 7.7 GB of memory. The rest of the project builds quickly. The output of the last command should agree with
`AXIOMS.txt`.
