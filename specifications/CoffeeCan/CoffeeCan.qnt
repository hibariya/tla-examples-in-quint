// quint verify CoffeeCan.qnt --main=coffeeCan5 --init=init --step=step --invariant=typeInvariant --temporal=theorem --backend=tlc
module coffeecan {
  type Can = {
    black: int,
    white: int,
  }

  const maxBeanCount: int

  var can: Can

  val typeInvariant = and {
    can.black.in(0.to(maxBeanCount)),
    can.white.in(0.to(maxBeanCount)),
  }

  assume maxBeanFact = maxBeanCount >= 1

  action init = {
    nondet black = 0.to(maxBeanCount).oneOf()
    nondet white = 0.to(maxBeanCount).oneOf()

    all {
      (black + white).in(1.to(maxBeanCount)),
      can' = {
        black: black,
	white: white,
      },
    }
  }

  val beanCount = can.black + can.white

  action pickSameColorBlack = all {
    beanCount > 1,
    can.black >= 2,
    can' = can.with("black", can.black - 1),
  }

  action pickSameColorWhite = all {
    beanCount > 1,
    can.white >= 2,
    can' = can.with("white", can.white - 2)
              .with("black", can.black + 1),
  }

  action pickDifferentColor = all {
    beanCount > 1,
    can.white >= 1,
    can.black >= 1,
    can' = can.with("black", can.black - 1)
  }

  action termination = all {
    beanCount == 1,
    can' = can
  }

  action step = any {
    pickSameColorBlack,
    pickSameColorWhite,
    pickDifferentColor,
    termination,
  }

  temporal monotonicDecrease = 
    always(
      (next(beanCount) < beanCount) or (next(can) == can)
    )

  temporal eventuallyTerminates =
    eventually(enabled(termination))

  temporal loopInvariant =
    always(
      (can.white % 2 == 0)
      iff
      (next(can.white) % 2 == 0)
    )
    
  temporal terminationHypothesis = and {
    (can.white % 2 == 0) implies eventually(can.black == 1 and can.white == 0),
    (can.white % 2 != 0) implies eventually(can.black == 0 and can.white == 1),
  }

  // step.weakFair(Set(can)): If a step that changes `can` remains continuously possible, eventually such a step must occur.
  // - `Set(can)` = “use `can` to determine whether progress occurred”
  // - `weakFair` = “don’t postpone possible progress forever”
  temporal theorem = step.weakFair(Set(can)) implies and {
    eventuallyTerminates,
    terminationHypothesis,
  }
}

module coffeeCan5 {
  import coffeecan(
    maxBeanCount = 500
  ).*
}
