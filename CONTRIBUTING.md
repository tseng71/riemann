# Contributing and mathematical review

Adversarial review is welcome.  The most useful reports identify one exact
statement, file, line or declaration, and provide either a counterexample, a
failed reproduction transcript, or a replacement proof.

Please classify reports as one of:

- **certificate soundness** — interval enclosure, rounding, coverage,
  subdivision, Hessian, or basin logic;
- **finite-dimensional proof** — Lean statement mismatch, hidden assumption,
  or matrix/inertia error;
- **analytic integration** — simple-zero decomposition, endpoint/tail error,
  overlap limit, pinching, shifted windows, or asymptotics;
- **claim language** — any sentence that overstates what the evidence proves;
- **provenance/licensing** — missing attribution or incompatible terms.

Do not describe the repository as a proof of the Riemann hypothesis.  A
positive lower proportion of simple critical-line zeros would not imply RH.
The candidate numerical bound also remains open end-to-end under the release
gate in `CLAIMS.md`.
