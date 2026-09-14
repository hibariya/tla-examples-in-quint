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
