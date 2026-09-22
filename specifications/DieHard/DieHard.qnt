// quint verify DieHard.qnt --backend tlc --invariants typeOK notSolved
// expect: counterexample
module diehard {
  var big: int
  var small: int

  val typeOK =
    big.in(0.to(5)) and small.in(0.to(3))

  action init = all {
    big' = 0,
    small' = 0,
  }

  action fillSmallJug = all {
    small' = 3,
    big' = big,
  }

  action fillBigJug = all {
    small' = small,
    big' = 5,
  }

  action emptySmallJug = all {
    small' = 0,
    big' = big,
  }

  action emptyBigJug = all {
    small' = small,
    big' = 0,
  }

  pure def min2(m: int, n: int): int =
    if (m < n) m else n

  action smallToBig = all {
    big' = min2(small + big, 5),
    small' = small - (min2(big + small, 5) - big),
  }

  action bigToSmall = all {
    small' = min2(big + small, 3),
    big' = big - (min2(big + small, 3) - small),
  }

  action step = any {
    fillSmallJug,
    fillBigJug,
    emptySmallJug,
    emptyBigJug,
    smallToBig,
    bigToSmall,
  }

  val notSolved = big != 4
}
