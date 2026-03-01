# algco

Paper: https://arxiv.org/abs/2301.09802

## Prerequisites

- Coq 8.20.x (tested with 8.20.1)
- Coq libraries: `coq-itree`, `coq-paco`

## Build
```sh
coq_makefile -f _CoqProject -o Makefile
make -j"$(nproc)"
```

## Conats

Defined in [theories/conat.v](theories/conat.v).

## Streams

Defined in [theories/colist.v](theories/colist.v), application to Sieve of Eratosthenes in [theories/sieve.v](theories/sieve.v) (extracted to [extract/sieve/](extract/sieve/)).

## Coinductive Tries

Defined in [theories/cotrie.v](theories/cotrie.v), regular expression test in [theories/RE_test.v](theories/RE_test.v) (extracted to [extract/re/](extract/re/)).

## Coinductive Binary Trees

Defined in [theories/cotree.v](theories/cotree.v), weakest pre-expectation semantics in [theories/cocwp.v](theories/cocwp.v), equidistribution theorem in [theories/equidistribution.v](theories/equidistribution.v).

## Extraction Demos

Sieve:
  ```sh
  cd extract/sieve && make && ./main
  ```
Regex:
  `theories/RE_test.v` extracts to `extract/re/RE.hs`.
  ```sh
  cd extract/re && make && ./main
  ```
