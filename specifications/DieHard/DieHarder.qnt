// quint verify DieHarder.qnt --backend tlc --main=dieharder259 --invariants typeOK notSolved
// expect: counterexample
module dieharder {
  type Jug = str
  const jugs: Set[jug]
  const capacity: Jug -> int
  const goal: int

  pure def min(m: int, n: int): int = if (m < n) m else n

  var contents: Jug -> int

  assume validParameters = and {
    capacity.keys() == jugs,
    jugs.forall(j => capacity.get(j) > 0),
    goal >= 0,
  }


  val typeOK = and {
    contents.keys() == jugs,
    jugs.forall(j => contents.get(j) >= 0),
  }

  action init =
    contents' = jugs.mapBy(_ => 0)

  action fillJug(j: Jug): bool =
    contents' = contents.set(j, capacity.get(j))

  action emptyJug(j: Jug): bool =
    contents' = contents.set(j, 0)

  action jugToJug(j: Jug, k: Jug): bool = {
    val amountPoured =
      min(contents.get(j), capacity.get(k) - contents.get(k))

    contents' = contents.set(j, contents.get(j) - amountPoured)
                        .set(k, contents.get(k) + amountPoured)
  }

  action step = {
    nondet j = jugs.oneOf()

    any {
      fillJug(j),
      emptyJug(j),
      {
        nondet k = jugs.filter(k => k != j).oneOf()
        jugToJug(j, k)
      }
    }
  }

  val notSolved =
    jugs.forall(j => contents.get(j) != goal)
}

module dieharder35 {
  import dieharder(
    jugs = Set("small", "big"),
    capacity = Map(
      "small" -> 3,
      "big" -> 5
    ),
    goal = 4,
  ).*
}

module dieharder259 {
  import dieharder(
    jugs = Set("s", "m", "l"),
    capacity = Map(
      "s" -> 2,
      "m" -> 5,
      "l" -> 9
    ),
    goal = 6,
  ).*
}
