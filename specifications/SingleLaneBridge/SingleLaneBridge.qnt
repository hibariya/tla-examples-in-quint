// quint verify SingleLaneBridge.qnt \
//   --main=SingleLaneBridgeThreeCars \
//   --init=init \
//   --step=step \
//   --invariant=typeInvariant,noBridgeCollisions,bridgeCapacity,oneBridgeDirection \
//   --temporal=fairLiveness \
//   --backend=tlc
module SingleLaneBridge {
  type Car = str
  type Position = int

  const carsRight: Set[Car]
  const carsLeft: Set[Car]

  const bridge: Set[Position]
  const positions: Set[Position]

  var location: Car -> Position
  var waitingBeforeBridge: List[Car]

  val cars = carsRight.union(carsLeft)

  val startPos =
    positions
      .filter(candidate =>
        positions.forall(p => candidate <= p)
      )
      .chooseSome()

  val endPos =
    positions
      .filter(candidate =>
        positions.forall(p => candidate >= p)
      )
      .chooseSome()

  val startBridge =
    bridge
      .filter(candidate =>
        bridge.forall(p => candidate <= p)
      )
      .chooseSome()

  val endBridge =
    bridge
      .filter(candidate =>
        bridge.forall(p => candidate >= p)
      )
      .chooseSome()

  assume validParameters = and {
    carsRight.intersect(carsLeft) == Set(),
    cars.size() > 0,
    startPos < startBridge,
    endBridge < endPos,
    bridge.size() < positions.size(),

    // additional assumptions
    positions.size() > 0,
    bridge.size() > 0,
    bridge.subseteq(positions),
    positions == startPos.to(endPos),
    bridge == startBridge.to(endBridge),
  }

  val carsInBridge =
    cars.filter(car => location.get(car).in(bridge))

  val carsBeforeBridge =
    carsRight
      .filter(car => endPos - endBridge == 1)
      .union(
        carsLeft.filter(car => startBridge - startPos == 1)
      )

  pure def rMove(position: Position): Position =
    if (position > startPos)
      position - 1
    else
      endPos

  pure def lMove(position: Position): Position =
    if (position < endPos)
      position + 1
    else
      startPos

  def nextLocation(car: Car): Position =
    if (car.in(carsRight))
      rMove(location.get(car))
    else
      lMove(location.get(car))

  action changeLocation(car: Car): bool = all {
    waitingBeforeBridge' =
      if (
        (car.in(carsRight) and nextLocation(car) == endBridge + 1)
        or
        (car.in(carsLeft) and nextLocation(car) == startBridge - 1)
      )
        waitingBeforeBridge.append(car)
      else
        waitingBeforeBridge,

    location' = location.set(car, nextLocation(car)),
  }

  def haveSameDirection(car: Car): bool = or {
    car.in(carsRight) and carsInBridge.forall(c => c.in(carsRight)),
    car.in(carsLeft) and carsInBridge.forall(c => c.in(carsLeft)),
  }

  action moveOutsideBridge(car: Car): bool = all {
    not(nextLocation(car).in(bridge)),
    changeLocation(car),
  }

  action moveInsideBridge(car: Car): bool = all {
    car.in(carsInBridge),
    cars.forall(c => location.get(c) != nextLocation(car)),
    changeLocation(car),
  }

  action enterBridge: bool = any {
    // The bridge is empty: the first waiting car may enter.
    all {
      carsInBridge == Set(),
      waitingBeforeBridge.length() != 0,
      location' = location.set(waitingBeforeBridge.head(), nextLocation(waitingBeforeBridge.head())),
      waitingBeforeBridge' = waitingBeforeBridge.tail(),
    },
    // The bridge is occupied: another car may enter only in
    // the same direction and without colliding.
    all {
      waitingBeforeBridge.length() != 0,
      not(waitingBeforeBridge.head().in(carsInBridge)),
      haveSameDirection(waitingBeforeBridge.head()),
      cars.forall(c => location.get(c) != nextLocation(waitingBeforeBridge.head())),
      location' = location.set(waitingBeforeBridge.head(), nextLocation(waitingBeforeBridge.head())),
      waitingBeforeBridge' = waitingBeforeBridge.tail(),
    },
  }

  pure def listToSet(list: List[Car]): Set[Car] =
    list.foldl(Set(), (result, car) => result.union(Set(car)))

  action init: bool = all {
    location' = cars.mapBy(car =>
      if (car.in(carsRight))
        endPos
      else
        startPos
    ),

    waitingBeforeBridge' =
      carsBeforeBridge.fold(List(), (queue, car) => queue.append(car))
  }

  action step: bool = any {
    enterBridge,

    {
      nondet car = cars.oneOf()
      moveOutsideBridge(car)
    },

    {
      nondet car = cars.oneOf()
      moveInsideBridge(car)
    },
  }

  val typeInvariant = and {
    location.keys() == cars,
    cars.forall(car => location.get(car).in(positions)),
    waitingBeforeBridge.length() <= cars.size(),
    listToSet(waitingBeforeBridge).subseteq(cars),
    listToSet(waitingBeforeBridge).size() == waitingBeforeBridge.length(),
  }

  val noBridgeCollisions =
    cars.forall(a =>
      cars.forall(b =>
        (
          location.get(a).in(bridge) and location.get(a) == location.get(b)
        ) implies a == b
      )
    )

  val bridgeCapacity =
    carsInBridge.size() <= bridge.size()

  val oneBridgeDirection =
    carsRight.forall(a =>
      carsLeft.forall(b =>
        // not(location.get(a).in(bridge) and location.get(b).in(bridge))
        not(a.in(carsInBridge) and b.in(carsInBridge))
      )
    )

  val safety = and {
    noBridgeCollisions,
    bridgeCapacity,
    oneBridgeDirection,
  }

  temporal carsInBridgeExitBridge =
    cars.forall(car =>
      always(car.in(carsInBridge) implies eventually(not(car.in(carsInBridge))))
    )

  temporal carsEnterBridge =
    cars.forall(car =>
      always(not(car.in(carsInBridge)) implies eventually(car.in(carsInBridge)))
    )

  temporal fairness = and {
    cars.forall(car => moveOutsideBridge(car).weakFair(Set((location, waitingBeforeBridge)))),
    cars.forall(car => moveInsideBridge(car).weakFair(Set((location, waitingBeforeBridge)))),
    enterBridge.weakFair(Set((location, waitingBeforeBridge))),
  }

  temporal fairLiveness =
      fairness implies and {
        carsInBridgeExitBridge,
        carsEnterBridge,
      }
}

module SingleLaneBridgeExample {
  val modelCarsRight = Set("right-1")
  val modelCarsLeft = Set("left-1")

  val modelPositions = 1.to(6)
  val modelBridge = 3.to(4)

  import SingleLaneBridge(
    carsRight = modelCarsRight,
    carsLeft = modelCarsLeft,
    positions = modelPositions,
    bridge = modelBridge,
  ).*
}

module SingleLaneBridgeThreeCars {
  import SingleLaneBridge(
    carsRight = Set("right-1", "right-2"),
    carsLeft = Set("left-1"),
    positions = 1.to(6),
    bridge = 3.to(4),
  ).*
}