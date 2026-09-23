// alloy exec -c FourGallonsIsImpossible -t table -o - DieHard.als
open util/integer

one sig Jugs {
  var small: one Int,
  var big: one Int
}

fact capacities {
  always {
    Jugs.small >= 0
    Jugs.small <= 3

    Jugs.big >= 0
    Jugs.big <= 5
  }
}

pred init {
  Jugs.small = 0
  Jugs.big = 0
}

pred fillBig {
  Jugs.big < 5

  Jugs.big' = 5
  Jugs.small' = Jugs.small
}

pred emptySmall {
  Jugs.small > 0

  Jugs.small' = 0
  Jugs.big' = Jugs.big
}

pred pourBigToSmall {
  Jugs.big > 0
  Jugs.small < 3

  Jugs.big <= 3.sub[Jugs.small] implies {
    Jugs.small' = Jugs.small.add[Jugs.big]
    Jugs.big' = 0
  } else {
    Jugs.big' = Jugs.big.sub[3.sub[Jugs.small]]
    Jugs.small' = 3
  }
}

fact behavior {
  init
  always {
    fillBig or
    emptySmall or
    pourBigToSmall
  }
}

assert FourGallonsIsImpossible {
  not eventually (Jugs.big = 4)
}

check FourGallonsIsImpossible for 4 Int, 1..8 steps
