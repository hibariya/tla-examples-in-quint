# TLA+ Examples in Quint

Hand-written [Quint](https://quint-lang.org/) ports of selected specifications
from [tlaplus/Examples](https://github.com/tlaplus/Examples).

This is an unofficial educational project created while learning TLA+ and Quint.
The ports aim to preserve the behavior of the original specifications while
using Quint's types and idioms where appropriate.

## Specifications

| Specification | Original |
|---|---|
| DieHard | [TLA+](https://github.com/tlaplus/Examples/tree/master/specifications/DieHard) |
| CoffeeCan | [TLA+](https://github.com/tlaplus/Examples/tree/master/specifications/CoffeeCan) |
| ReadersWriters | [TLA+](https://github.com/tlaplus/Examples/tree/master/specifications/ReadersWriters) |

## Usage

Type-check a specification:

```sh
quint typecheck specifications/ReadersWriters/ReadersWriters.qnt
```

Verify every specification using the command at the top of each `.qnt` file:

```sh
python3 scripts/verify.py
```

The DieHard examples intentionally find a solution by checking `notSolved`.
Their `// expect: counterexample` comments tell the runner to require that result.
