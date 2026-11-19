# Equality in a binomial gcd bound of Erdős and Szekeres

**Yoshiharu Onishi · Preprint · November 20, 2026**

[Read the paper (PDF)](paper/erdos-700.pdf) · [LaTeX source](paper/erdos-700.tex) · [Lean proofs](Erdos700) · [Citation](CITATION.cff)

For a composite integer $n\ge 4$, let

$$
f(n)=\min_{2\leq k\leq\lfloor n/2\rfloor}\gcd\left(n,\binom{n}{k}\right).
$$

Erdős and Szekeres asked when $f(n)=n/Q(n)$, where $Q(n)$ is the largest prime power dividing $n$. The problem collection asks the same question with the largest prime factor $P(n)$ in the denominator. At $n=12$, the minimum is $3=12/Q(12)$, while $12/P(12)=4$. The paper gives a finite necessary and sufficient condition for each equality, using the base expansions of $n$ and its prime factorization. [Original paper, pp. 98–99](https://static.renyi.hu/~p_erdos/1978-46.pdf) · [Erdős Problem 700](https://www.erdosproblems.com/700)

## Results and formal proofs

| Result in the preprint | Lean source |
| --- | --- |
| Equality criterion for every composite $n$, including prime powers (Theorem 2.1) | [Classification](Erdos700/Classification.lean) · [Equality sets in the infimum formulation](Erdos700/AnswerSets.lean) |
| For fixed $m\ge2$, the primes $p>m$ with $f(mp)=m$ have relative density one (Theorem 3.2) | [Prime counts and density](Erdos700/Density.lean) |
| For fixed $m\ge2$, the number of exceptions $1\le e\le E$ to $f(mq^e)=m$ is $O_{m,q}(E^{1-\eta_m})$, with $\eta_m>0$ independent of the prime $q\nmid m$ (Theorem 4.2) | [Bounded candidate columns](Erdos700/PowerFamilies.lean) · [Exceptional exponents](Erdos700/ExponentDensity.lean) |
| An equality exponent above the cutoff gives an infinite arithmetic progression. Every residue class contains such a progression (Corollary 4.3) | [Arithmetic progressions](Erdos700/Progressions.lean) |
| Exact formulas for $8p$, $4q^e$, $6\cdot5^e$, and $9\cdot2^e$ under the hypotheses in Section 5 | [Cofactor eight](Erdos700/EightPrime.lean) · [Cofactors four and six](Erdos700/SmallCofactors.lean) · [Ternary digits](Erdos700/Families.lean) |

For example, when $p>8$ is prime, $f(8p)=4$ precisely when $p-1$ or $3p-1$ is a power of two. Otherwise $f(8p)=8$. For $e\ge4$, the exceptional value $f(9\cdot2^e)=4$ occurs exactly when the ternary expansion of $2^{e-1}$ omits the digit $2$. Finiteness of those exceptions is equivalent to the finiteness question in Problem 406. [Erdős Problem 406](https://www.erdosproblems.com/406)

The classification concerns part (a) of Problem 700. Parts (b) and (c) ask about infinitely many $n$ with $f(n)>\sqrt n$ and uniform logarithmic upper bounds. The formalization uses the same infimum definition of $f$ as the following version of the public problem statement. [Formal Conjectures, revision 2c24ebe](https://github.com/google-deepmind/formal-conjectures/blob/2c24ebe7eb2a79b47f9ffcab618cd611c2bc1ea6/FormalConjectures/ErdosProblems/700.lean)

## Reproducing the proofs and computations

Run the commands from the repository root. With Elan installed, the project selects Lean `v4.33.0-rc1`. The Lake manifest pins mathlib and the other dependencies.

```sh
lake exe cache get
lake build
```

To recheck individual compiled modules with the Lean kernel, for example, run

```sh
lake env leanchecker Erdos700.AnswerSets Erdos700.ExponentDensity Erdos700.Progressions Erdos700.SmallCofactors
```

The two numerical checks use Python 3.10 or newer and the standard library.

```sh
python -B verify_erdos700_general.py
python -B verify_large_prime.py
```

The first program compares the criterion with direct row minima for all 4,330 composite integers through 5,000. It finds 2,811 equalities with $n/Q(n)$ and 2,578 with $n/P(n)$. Through $n=144$ it also enumerates prime-power splits and compares their subset sums with the digit algorithm. [General verification script](verify_erdos700_general.py)

The second program checks all 9,588 primes $8<p\le100{,}000$ by the cofactor formula, including direct row minima for all 91 primes $8<p\le500$. It also checks 19,840 instances for cofactors four and six, with 130 direct row minima. [Family verification script](verify_large_prime.py)

## Building the paper

The manuscript is a single LaTeX file with its bibliography included. The following Tectonic command writes `paper/erdos-700.pdf`.

```sh
tectonic -X compile --untrusted paper/erdos-700.tex
```

The English preprint was built with Tectonic 0.17.0 and a fixed timestamp of November 20, 2026 UTC. To reproduce that build, set `$env:SOURCE_DATE_EPOCH='1795132800'` in PowerShell or `export SOURCE_DATE_EPOCH=1795132800` in a POSIX shell before compiling.

## Original research materials

The November 18 Japanese note contains the original criterion and an embedded copy of the general verification script. The November 19 notes record the subsequent density results and special families. [Original Japanese PDF](archive/erdos-700-general-criterion.pdf) · [Japanese research notes](archive/research-notes.ja.md)
