// quint verify TwoPhase.qnt --main=TwoPhaseTwoManagers --invariant=typeInvariant,consistency --temporal=implementsTCommit --backend=tlc
module TwoPhase {
  type ResourceManager = str

  type Message =
    | PreparedMessage(ResourceManager)
    | CommitMessage
    | AbortMessage

  type ResourceManagerState =
    | Working
    | Prepared
    | Committed
    | Aborted

  type TransactionManagerState =
    | Init
    | CommittedByManager
    | AbortedByManager

  const resourceManagers: Set[ResourceManager]

  var resourceManagerState: ResourceManager -> ResourceManagerState
  var transactionManagerState: TransactionManagerState

  var managerPrepared: Set[ResourceManager]

  var messages: Set[Message]

  action init: bool = all {
    resourceManagerState' = resourceManagers.mapBy(_ => Working),
    transactionManagerState' = Init,
    managerPrepared' = Set(),
    messages' = Set(),
  }

  action tmReceivePrepared(rm: ResourceManager): bool = all {
    transactionManagerState == Init,
    PreparedMessage(rm).in(messages),
    managerPrepared' = managerPrepared.union(Set(rm)),
    resourceManagerState' = resourceManagerState,
    transactionManagerState' = transactionManagerState,
    messages' = messages,
  }

  action tmCommit: bool = all {
    transactionManagerState == Init,
    managerPrepared == resourceManagers,
    transactionManagerState' = CommittedByManager,
    messages' = messages.union(Set(CommitMessage)),
    resourceManagerState' = resourceManagerState,
    managerPrepared' = managerPrepared,
  }

  action tmAbort: bool = all {
    transactionManagerState == Init,
    transactionManagerState' = AbortedByManager,
    messages' = messages.union(Set(AbortMessage)),
    resourceManagerState' = resourceManagerState,
    managerPrepared' = managerPrepared,
  }

  action rmPrepare(rm: ResourceManager): bool = all {
    resourceManagerState.get(rm) == Working,
    resourceManagerState' = resourceManagerState.set(rm, Prepared),
    messages' = messages.union(Set(PreparedMessage(rm))),
    transactionManagerState' = transactionManagerState,
    managerPrepared' = managerPrepared,
  }

  action rmChooseToAbort(rm: ResourceManager): bool = all {
    resourceManagerState.get(rm) == Working,
    resourceManagerState' = resourceManagerState.set(rm, Aborted),
    transactionManagerState' = transactionManagerState,
    managerPrepared' = managerPrepared,
    messages' = messages,
  }

  action rmReceiveCommitMessage(rm: ResourceManager): bool = all {
    CommitMessage.in(messages),
    resourceManagerState' = resourceManagerState.set(rm, Committed),
    transactionManagerState' = transactionManagerState,
    managerPrepared' = managerPrepared,
    messages' = messages,
  }

  action rmReceiveAbortMessage(rm: ResourceManager): bool = all {
    AbortMessage.in(messages),
    resourceManagerState' = resourceManagerState.set(rm, Aborted),
    transactionManagerState' = transactionManagerState,
    managerPrepared' = managerPrepared,
    messages' = messages,
  }

  action step: bool = any {
    tmCommit,
    tmAbort,
    {
      nondet rm = resourceManagers.oneOf()

      any {
        tmReceivePrepared(rm),
        rmPrepare(rm),
        rmChooseToAbort(rm),
        rmReceiveCommitMessage(rm),
        rmReceiveAbortMessage(rm),
      }
    }
  }

  val typeInvariant = and {
    resourceManagerState.keys() == resourceManagers,
    managerPrepared.subseteq(resourceManagers),
    messages.forall(message =>
      match message {
        | PreparedMessage(rm) => rm.in(resourceManagers)
        | CommitMessage => true
        | AbortMessage => true
      }
    ),
  }

  val consistency = resourceManagers.forall(rm1 =>
    resourceManagers.forall(rm2 =>
      not(and {
        resourceManagerState.get(rm1) == Committed,
        resourceManagerState.get(rm2) == Aborted,
      })
    )
  )


  // Abstract TCommit predicates and actions used for refinement checking.

  val tcCanCommit =
    resourceManagers.forall(rm => resourceManagerState.get(rm).in(Set(Prepared, Committed)))

  val tcNotCommitted =
    resourceManagers.forall(rm => resourceManagerState.get(rm) != Committed)

  action tcPrepare(rm: ResourceManager): bool = all {
    resourceManagerState.get(rm) == Working,
    resourceManagerState' = resourceManagerState.set(rm, Prepared),
  }

  action tcCommit(rm: ResourceManager): bool = all {
    resourceManagerState.get(rm) == Prepared,
    tcCanCommit,
    resourceManagerState' = resourceManagerState.set(rm, Committed),
  }

  action tcAbort(rm: ResourceManager): bool = all {
    resourceManagerState.get(rm).in(Set(Working, Prepared)),
    tcNotCommitted,
    resourceManagerState' = resourceManagerState.set(rm, Aborted),
  }

  action tcStep: bool = {
    nondet rm = resourceManagers.oneOf()

    any {
      tcPrepare(rm),
      tcCommit(rm),
      tcAbort(rm),
    }
  }

  val tcInitial =
    resourceManagers.forall(rm => resourceManagerState.get(rm) == Working)

  temporal implementsTCommit = and {
    tcInitial, // since it's outside `always` it is evaluated only at the first state of the behavior
    always(
      tcStep.orKeep(Set(resourceManagerState))
    )
  }
}

module TwoPhaseTwoManagers {
  import TwoPhase(
    resourceManagers = Set("rm-1", "rm-2"),
  ).*
}