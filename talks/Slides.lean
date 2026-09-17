import VersoSlides

open VersoSlides

/-
  Template talk: intro to formal verification.

  Edit this file, then from `talks/`:
    lake exe generate-slides
    python3 -m http.server -d _slides

  Useful Verso bits (see also https://github.com/leanprover/verso-slides):
  * `#` heading           -> a new horizontal slide
  * `##` under `vertical` -> a vertical sub-slide
  * `:::fragment`         -> appear-on-click
  * `:::notes`            -> speaker notes (press S)
  * `{lean}`...``         -> inline elaborated Lean
  * ```lean               -> type-checked code with a clickable info panel
  * `$`...`` / `$$`...``  -> KaTeX math
-/

#doc (Slides) "An Introduction to Formal Verification" =>

# XMSS Verifier in RV, in Lean
%%%
state := "title-slide"
vertical := true
%%%

Derek Sorensen

## Collaborators

:::class "collab-cols"
- [@Abraxas1010](https://github.com/Abraxas1010)
- [@adrienlacombe](https://github.com/adrienlacombe)
- [@alexanderlhicks](https://github.com/alexanderlhicks)
- [@andreiburdusa](https://github.com/andreiburdusa)
- [@BoltonBailey](https://github.com/BoltonBailey)
- [@chung-thai-nguyen](https://github.com/chung-thai-nguyen)
- [@codygunton](https://github.com/codygunton)
- [@desmondcoles1](https://github.com/desmondcoles1)
- [@DimitriosMitsios](https://github.com/DimitriosMitsios)
- [@dtumad](https://github.com/dtumad)
- [@eliasjudin](https://github.com/eliasjudin)
- [@erdkocak](https://github.com/erdkocak)
- [@ErVinuelas](https://github.com/ErVinuelas)
- [@FawadHa1der](https://github.com/FawadHa1der)
- [@Ferinko](https://github.com/Ferinko)
- [@graikos](https://github.com/graikos)
- [@JuanCoRo](https://github.com/JuanCoRo)
- [@Julek](https://github.com/Julek)
- [@kim-em](https://github.com/kim-em)
- [@klausnat](https://github.com/klausnat)
- [@kobizk](https://github.com/kobizk)
- [@MavenRain](https://github.com/MavenRain)
- [@olympichek](https://github.com/olympichek)
- [@quangvdao](https://github.com/quangvdao)
- [@scaraven](https://github.com/scaraven)
- [@Sfgangloff](https://github.com/Sfgangloff)
- [@shreyas-londhe](https://github.com/shreyas-londhe)
- [@varunthakore](https://github.com/varunthakore)
- [@z-tech](https://github.com/z-tech)
:::

:::notes


dhsorens.com
:::


# Computable ...
%%%
vertical := true
%%%

Algebraic SNARK Primitives in Lean

- Polynomials
- Finite Fields
- Linear Algebra
- ...

:::notes

First section:
Intro to what is here, so people are aware.

:::

## Polynomials

:::::class "field-catalog"
:::table +colHeaders (cellGap := "0.12em 0.55em")
*
  * Representations
  * Univariate
  * Beyond
*
  *
    - `CPolynomial R` — dense coeffs
    - `CMvPolynomial n R` — sparse
    - `CMlPolynomial R n` — monomials
    - `CMlPolynomialEval R n` — $`\{0,1\}^n`
    - `CBivariate R` — $`R[X][Y]`
    - Mathlib `RingEquiv`s
  *
    - Lagrange, barycentric
    - batch eval, many-eval
    - NTT and NTTFast
    - division, extended Euclid
    - root finding
    - Reed-Solomon, Gao
  *
    - mv: eval, rename, restrict
    - ml: zeta / Möbius, MLE
    - Kronecker multiplication
    - Guruswami-Sudan
    - additive NTT
:::
:::::

:::notes
Three univariate views: Raw arrays, canonical CPolynomial (trimmed), and the quotient model. Bridges: ToPoly to Mathlib Polynomial, MvPolyEquiv, CMl Equiv, Bivariate ToPoly, plus CPolynomial ≃ CMv 1 and CBivariate ≃ CMv 2. NTTFast refines the NTT spec; write proofs against NTT. Gao is unique RS decoding; Guruswami-Sudan is list decoding on the bivariate layer. Additive NTT lives with the binary-field stack.
:::

## Finite Fields

:::::class "field-catalog"
:::table +colHeaders (cellGap := "0.12em 0.55em")
*
  * Prime
  * Extensions
  * Binary
*
  *
    - BabyBear — $`2^{31}-2^{27}+1`
    - KoalaBear — $`2^{31}-2^{24}+1`
    - Mersenne31 — $`2^{31}-1`
    - Goldilocks — $`2^{64}-2^{32}+1`
    - Hachi — $`2^{32}-99`
    - BN254, BLS12-381, BLS12-377
    - Pallas, Vesta
    - secp256k1 ($`p` and $`n`)
  *
    - BabyBear $`X^4-11`
    - KoalaBear $`X^4-3`
    - KoalaBear $`X^5+X^2-1`
    - KoalaBear $`X^6+X^3+1`
    - Hachi $`X^4-2`
    - BF64 $`y^3+y+1`
    - generic $`F[X]/f`
  *
    - $`\mathrm{GF}(2^{64})` poly basis
    - $`\mathrm{GF}(2^{192})` cubic
    - $`\mathrm{GF}(2^{128})` GHASH
    - towers $`\mathrm{GF}(2^{8})`–$`\mathrm{GF}(2^{128})`
:::
:::::

:::notes
The Extension/ stack is F adjoin a root of any monic f, with binomials X^d - W as the cheap case (Rabin collapses to two base-field exponentiations). Non-binomial KoalaBear Ext5 and Ext6 use kernel-checked Rabin certificates. BF64 Ext3 is the one char-2 consumer of that framework. The GHASH field and binary towers are a separate stack.
:::

## Linear Algebra

:::::class "field-catalog"
:::table +colHeaders (cellGap := "0.12em 0.55em")
*
  * Dense
  * Polynomial matrices
  * For decoding
*
  *
    - `DenseMatrix F` — row-major
    - Gauss-Jordan `rref`
    - homogeneous kernel
    - in-place fast path
    - no Mathlib `Matrix` bridge
  *
    - `PolynomialMatrix F` — rows of `CPolynomial`
    - shifted degrees
    - Mulders-Storjohann
    - row-span, shift-minimal
    - Strassen multiply
  *
    - PM-Basis approximants
    - modular key equations
    - partial linearization
    - Lee-O'Sullivan / hybrid GS
:::
:::::

:::notes
Two independent Array-backed layers, both built for Guruswami-Sudan interpolation but usable alone. Dense: prove against rref, run rrefInPlace (avoids O(n^4) copying). Polynomial: prove against the direct Mulders-Storjohann loop, call the Fast variants. Shape facts are propositions (WellFormed, PivotColumnsShaped), not type indices. Approximant/ is the quasi-linear interpolation engine for long RS codes.
:::

## The rest

:::::class "field-catalog"
:::table +colHeaders (cellGap := "0.12em 0.55em")
*
  * Certificates
  * Coding theory
  * Glue
*
  *
    - Pratt / Lucas primality
    - Rabin irreducibility
    - binomials: two base-field exps
    - else: kernel-checked certs
    - no `native_decide`
  *
    - RS encode = NTT
    - Gao unique decode
    - Guruswami-Sudan list decode
    - engines: roots $+$ matrices
  *
    - `AlgebraTower`
    - Frobenius $`X^q-X`
    - Euclidean domain
    - `ExtTreeMap` (sparse mv)
    - Mathlib bridges
:::
:::::

:::notes
Almost everything computational is already on the three previous slides. What remains is how fields and extensions are certified, how the coding stack is assembled from polynomials plus matrices plus roots, and the Data/ToMathlib support layer. Pratt certificates make the prime fields; Rabin makes the extension moduli irreducible. Binary AlgebraTower is the one nested-extension interface that exists today; composing odd-characteristic Ext towers is still open.
:::


# Applications of CompPoly
%%%
vertical := true
%%%

content

## Formal Specification

content

:::notes

content

:::


# Autoresearch
%%%
vertical := true
%%%

content

## second slide

content
