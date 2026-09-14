// quint verify ReadersWriters.qnt --main=readersWriters3 --init=init --step=step --invariant=typeInvariant,safety --temporal=theorem --backend=tlc
module ReadersWriters {
  type Actor = int

  type Request =
    | ReadRequest(Actor)
    | WriteRequest(Actor)

  const numActors: int

  var readers: Set[Actor]
  var writers: Set[Actor]
  var waiting: List[Request]

  val actors = 1.to(numActors)

  val waitingToRead: Set[Actor] =
    waiting.foldl(Set(), (result, request) =>
      match request {
        | ReadRequest(actor) => result.union(Set(actor))
        | WriteRequest(_) => result
      }
    )

  val waitingToWrite: Set[Actor] =
    waiting.foldl(Set(), (result, request) =>
      match request {
        | ReadRequest(_) => result
        | WriteRequest(actor) => result.union(Set(actor))
      }
    )

  action tryRead(actor: Actor): bool = all {
    not(actor.in(waitingToRead)),
    waiting' = waiting.append(ReadRequest(actor)),
    readers' = readers,
    writers' = writers,
  }

  action tryWrite(actor: Actor): bool = all {
    not(actor.in(waitingToWrite)),
    waiting' = waiting.append(WriteRequest(actor)),
    readers' = readers,
    writers' = writers,
  }

  action read(actor: Actor): bool = all {
    readers' = readers.union(Set(actor)),
    waiting' = waiting.tail(),
    writers' = writers,
  }

  action write(actor: Actor): bool = all {
    readers == Set(),
    writers' = writers.union(Set(actor)),
    waiting' = waiting.tail(),
    readers' = readers,
  }

  pure def requestActor(request: Request): Actor =
    match request {
      | ReadRequest(actor) => actor
      | WriteRequest(actor) => actor
    }
  
  pure def isReadRequest(request: Request): bool =
    match request {
      | ReadRequest(_) => true
      | WriteRequest(_) => false
    }

  action readOrWrite: bool = all {
    waiting.length() != 0,
    writers == Set(),

    any {
      all {
        isReadRequest(waiting.head()),
        read(requestActor(waiting.head())),
      },

      all {
        not(isReadRequest(waiting.head())),
        write(requestActor(waiting.head()))
      }
    }
  }

  action stopActivity(actor: Actor): bool = any {
    all {
      actor.in(readers),
      readers' = readers.exclude(Set(actor)),
      writers' = writers,
      waiting' = waiting
    },

    all {
      actor.in(writers),
      readers' = readers,
      writers' = writers.exclude(Set(actor)),
      waiting' = waiting,
    }
  }

  action stop: bool = {
    nondet actor = readers.union(writers).oneOf()
    stopActivity(actor)
  }

  action init: bool = all {
    readers' = Set(),
    writers' = Set(),
    waiting' = List(),
  }

  action step: bool = any {
    {
      nondet actor = actors.oneOf()
      tryRead(actor)
    },
    {
      nondet actor = actors.oneOf()
      tryWrite(actor)
    },
    readOrWrite,
    stop,
  }

  val typeInvariant = all {
    readers.subseteq(actors),
    writers.subseteq(actors),

    waiting.foldl(
      true,
      (valid, request) =>
        valid and requestActor(request).in(actors)
    )
  }

  val safety = all {
    not(readers != Set() and writers != Set()),
    writers.size() <= 1,
  }

  assume validParameters = numActors >= 1

  temporal liveness = and {
    actors.forall(actor => always(eventually(actor.in(readers)))),
    actors.forall(actor => always(eventually(actor.in(writers)))),
    actors.forall(actor => always(eventually(not(actor.in(readers))))),
    actors.forall(actor => always(eventually(not(actor.in(writers))))),
  }

  temporal fairness = and {
    actors.forall(actor => tryRead(actor).weakFair(Set((readers, writers, waiting)))),
    actors.forall(actor => tryWrite(actor).weakFair(Set((readers, writers, waiting)))),
    readOrWrite.weakFair(Set((readers, writers, waiting))),
    stop.weakFair(Set((readers, writers, waiting))),
  }

  temporal theorem = fairness implies liveness
}

module readersWriters3 {
  import ReadersWriters(
    numActors = 3
  ).*
}
