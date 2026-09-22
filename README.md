# TLA+ Examples in Quint

Hand-written [Quint](https://quint-lang.org/) ports of selected specifications
from [tlaplus/Examples](https://github.com/tlaplus/Examples).

This is an unofficial educational project created while learning TLA+ and Quint.
The ports aim to preserve the behavior of the original specifications while
using Quint's types and idioms where appropriate.

## Specifications

| Specification | Quint | Original |
|---|---|---|
| CoffeeCan | [CoffeeCan.qnt](specifications/CoffeeCan/CoffeeCan.qnt) | [CoffeeCan.tla](https://github.com/tlaplus/Examples/blob/master/specifications/CoffeeCan/CoffeeCan.tla) |
| DieHard | [DieHard.qnt](specifications/DieHard/DieHard.qnt) | [DieHard.tla](https://github.com/tlaplus/Examples/blob/master/specifications/DieHard/DieHard.tla) |
| DieHarder | [DieHarder.qnt](specifications/DieHard/DieHarder.qnt) | [DieHarder.tla](https://github.com/tlaplus/Examples/blob/master/specifications/DieHard/DieHarder.tla) |
| ReadersWriters | [ReadersWriters.qnt](specifications/ReadersWriters/ReadersWriters.qnt) | [ReadersWriters.tla](https://github.com/tlaplus/Examples/blob/master/specifications/ReadersWriters/ReadersWriters.tla) |
| SingleLaneBridge | [SingleLaneBridge.qnt](specifications/SingleLaneBridge/SingleLaneBridge.qnt) | [SingleLaneBridge.tla](https://github.com/tlaplus/Examples/blob/master/specifications/SingleLaneBridge/SingleLaneBridge.tla) |
| TCommit | [TCommit.qnt](specifications/transaction_commit/TCommit.qnt) | [TCommit.tla](https://github.com/tlaplus/Examples/blob/master/specifications/transaction_commit/TCommit.tla) |
| TwoPhase | [TwoPhase.qnt](specifications/transaction_commit/TwoPhase.qnt) | [TwoPhase.tla](https://github.com/tlaplus/Examples/blob/master/specifications/transaction_commit/TwoPhase.tla) |

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
