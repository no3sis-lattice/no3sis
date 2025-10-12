# Problem Class: Bekenstein–Bound Unsolvable (BB‑UNREP)

Abstract
- We define a physically grounded problem class whose unsolvability is not derived from self-reference or logical paradox, but from the Bekenstein bound on maximum information capacity of any finite physical system. A problem belongs to this class when, for some instance size, the minimum amount of information that must be simultaneously represented by any correct solver exceeds the maximum information that can be contained in the allowed physical apparatus.

---

## 1) Physical Preliminaries

Bekenstein bound (information capacity):
- For any physical system of total energy E confined within radius R, the maximum number of classical bits it can contain is bounded by:
  $$
  I_{\max}(E,R) \;=\; \frac{2\pi E R}{\hbar c \ln 2} \quad \text{bits}.
  $$
  Where $\hbar$ is the reduced Planck constant, and $c$ the speed of light.

Practical scales (order-of-magnitude)
- Lab-scale example: E = 10 kJ, R = 1 m.
  - Numerator: 2πER ≈ 6.283 × 10^4 J·m
  - Denominator: ħ c ln 2 ≈ 1.054×10^-34 × 3×10^8 × 0.693 ≈ 2.19×10^-26 J·m
  - I_max ≈ 6.283×10^4 / 2.19×10^-26 ≈ 2.9×10^30 bits
- Observable universe: often quoted capacity ≈ 10^122 bits (holographic-entropy scale).

Interpretation
- Any physically realizable computation performed entirely within a region of radius R and energy budget E cannot have more than I_max(E,R) bits simultaneously present (including input held, internal state, working memory, and any retained output).

---

## 2) Minimal Simultaneous Representational Requirement

Let Π be a decision/search/enumeration problem with input size parameter n.

Definition (σΠ(n)):
- Define the minimal simultaneous representational requirement σΠ(n) as:
  - Consider all physically realizable, correct procedures A for Π.
  - For each such A, consider the worst-case input x of size n, and the maximum over all time t during A(x) of the number of information bits that must be simultaneously present for A to remain correct on x.
  - σΠ(n) is the infimum of that peak value across all correct A.

Intuition
- σΠ(n) lower-bounds the “peak concurrent information” any correct solver must hold at once on worst-case inputs of size n. This includes:
  - Retained output needed for correctness
  - Injective encodings of feasible sets that must be disambiguated
  - Certificates/witnesses and intermediate structures that cannot be lossy without risking error

Notes
- σΠ(n) is defined at a fixed encoding precision (see §6). Tightening precision can only increase σΠ(n).

---

## 3) Problem Class Definition

Fix a physical profile U = (E, R) describing the maximum apparatus and region allowed.

Definition (BB‑UNREP(U)):
- A problem Π is Bekenstein–Bound Unsolvable under U, written Π ∈ BB‑UNREP(U), if there exists an n* such that:
  $$
  \sigma_{\Pi}(n^\*) \;>\; I_{\max}(E,R).
  $$
- Equivalently: no physically realizable device constrained by U can solve Π on all inputs of size n*, even with unbounded time, because the solver would need to simultaneously represent more information than permitted by the Bekenstein bound.

Remarks
- This is a physical impossibility result, not a logical undecidability or self-referential paradox.
- Π can be Turing‑decidable in the abstract; the obstruction is purely the representational capacity required for correctness.

---

## 4) Sufficient Conditions

4.1 Output‑bounded subclass (BB‑OUT(U))
- If some instance x requires any correct solver to present or retain more than I_max(E,R) bits of output simultaneously at any time, then Π ∈ BB‑UNREP(U).
- Sufficient condition: ∃x with |output(x)| > I_max(E,R).

4.2 Representation‑bounded subclass (BB‑REP(U))
- If correctness forces an injective representation of a feasible or candidate state set F(x) of cardinality M (e.g., exact microstate identification or solution set disambiguation), then any correct solver must hold at least log2 M bits simultaneously.
- Sufficient condition: ∃x with log2 |F(x)| > I_max(E,R).

4.3 Mixed conditions
- Many tasks combine nontrivial outputs and necessary internal injection of large state spaces; either can force σΠ(n) above I_max.

---

## 5) Canonical Examples (Non‑paradoxical)

5.1 Exact exhaustive enumeration beyond capacity (BB‑OUT)
- Task: Enumerate all satisfying assignments for an instance engineered to have ≥ 2^m solutions.
- If m > I_max(E,R), then at some point any correct enumerator must hold more than I_max bits (as retained output, buffered stream, or necessary book‑keeping), implying Π ∈ BB‑UNREP(U).

5.2 High‑dimensional exact tomography at fixed precision (BB‑REP)
- Task: Reconstruct a d‑dimensional quantum state ρ to absolute precision ε in trace distance, outputting a classical description.
- A lossless classical representation of ρ typically needs Θ(d^2 log(1/ε)) bits. With d = 2^q (q qubits), for sufficiently large q, σΠ(n) exceeds I_max even before output streaming can help, as correctness demands injective disambiguation among ~exp(d^2) microstates at the chosen precision.

5.3 Microstate inventory with uniqueness certificate (BB‑REP)
- Task: On a constrained L^3 lattice with finite local state, output the lexicographically first valid global configuration and maintain a certificate that uniquely disambiguates it among all valid configurations.
- If |F(x)| ≥ 2^m valid configurations under constraints, correctness forces ≥ m bits simultaneously (the certificate must injectively identify one among |F(x)|). If m > I_max(E,R), the task falls in BB‑UNREP(U).

---

## 6) Precision, Streaming, and Quantum Notes

- Precision dependence: σΠ is defined relative to a fixed, lossless encoding and precision regime (e.g., rationals with bounded denominators, fixed ε). Higher precision strengthens σΠ and the impossibility claim.
- Streaming does not save injectivity: If correctness requires injective disambiguation among M states at any instant, then purely sequential output streaming cannot reduce the peak simultaneous information below log2 M.
- Quantum devices: While quantum systems store information differently, the Bekenstein/holographic bounds are on physical entropy; accessible classical information and distinguishability are still bounded. With careful accounting of measurement and accessible information, the same impossibility logic applies.

---

## 7) Meta‑Lemmas

Lemma (Output lower bound → BB membership)
- If there exists a sequence of instances x_n whose minimal correct output size f(n) satisfies lim sup f(n) > I_max(E,R), then Π ∈ BB‑UNREP(U).

Lemma (Injective feasible‑set encoding)
- If correctness on x forces an injective map from a feasible set F(x) with |F(x)| ≥ 2^m into the solver’s simultaneously present information, then σΠ(n) ≥ m. If m > I_max(E,R), Π ∈ BB‑UNREP(U).

---

## 8) Application to This Project (Scope and Goals)

- In this formalization effort, BB‑UNREP(U) provides a physically grounded upper bound on what classes of constraints and tasks are solvable within specified physical regimes (e.g., “lab‑scale GPU cluster” vs “observatory‑scale apparatus”).
- Use cases:
  - Validating de‑trivialization: Ensure newly introduced constraints do not implicitly force representations whose σΠ(n) exceed the intended U.
  - Spec discipline: When adding constraints whose semantics require exact microstate enumeration or injective identification among exponentially large sets, document whether this places the problem (for certain sizes) into BB‑UNREP(U).
  - CI flagging: A metadata field in the JSON constraint schema can declare a per‑constraint contribution to representational lower bounds (output size growth, feasible‑set injectivity), enabling automated alarms when σΠ estimates surpass the configured I_max.

Suggested workflow hooks
- Choose U profiles relevant to deployments, e.g.:
  - U_lab = (E=10 kJ, R=1 m) → I_max ≈ 3×10^30 bits
  - U_cloud = (effective aggregate E,R over rack footprint) → compute I_max via energy delivery and physical footprint assumptions
  - U_obs (observable universe) → ≈ 10^122 bits
- For each problem family or chunk:
  1) Estimate σΠ(n) from constraint semantics (output lower bounds, injective feasible‑set size, precision).
  2) Compare σΠ(n) to I_max(U). If σΠ(n) > I_max(U) for some n*, then formally classify as BB‑UNREP(U) beyond n*.
  3) Document thresholds (n*), precision assumptions, and whether approximations/relaxations bring σΠ(n) below I_max(U).

---

## 9) Quick Checklist for Authors

- [ ] Specify the physical profile U used for claims (E, R, precision model).
- [ ] Identify whether your task is output‑bound (BB‑OUT) or representation‑bound (BB‑REP), or both.
- [ ] Provide a lower‑bound estimate on σΠ(n) (e.g., log2 |F(x)| or minimal output size).
- [ ] Compare σΠ(n) vs I_max(E,R); record any threshold n* where σΠ(n*) > I_max.
- [ ] State precision and encoding assumptions explicitly.
- [ ] If claiming solvability within U, justify how σΠ(n) remains ≤ I_max for intended n.

---

## 10) References

- J. D. Bekenstein, “A Universal Upper Bound on the Entropy to Energy Ratio for Bounded Systems,” Physical Review D 23, 287 (1981).
- R. Bousso, “The Holographic Principle,” Reviews of Modern Physics 74, 825 (2002).
- S. Lloyd, “Ultimate physical limits to computation,” Nature 406, 1047–1054 (2000).

---
