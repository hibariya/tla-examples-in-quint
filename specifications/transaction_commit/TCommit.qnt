// quint verify TCommit.qnt --main=TCommitTwoManagers --invariant=typeInvariant,consistency --backend=tlc
module TCommit {
  type ResourceManager = str
  type ResourceManagerState =
    | Working
    | Prepared
    | Committed
    | Aborted

  const resourceManagers: Set[ResourceManager]

  var resourceManagerState: ResourceManager -> ResourceManagerState

  action init: bool = resourceManagerState' = resourceManagers.mapBy(_ => Working)

  val typeInvariant = resourceManagerState.keys() == resourceManagers

  action prepare(rm: ResourceManager): bool = all {
    resourceManagerState.get(rm) == Working,
    resourceManagerState' = resourceManagerState.set(rm, Prepared),
  }

  action decideToAbort(rm: ResourceManager): bool = all {
    resourceManagerState.get(rm).in(Set(Working, Prepared)),
    resourceManagers.forall(other => resourceManagerState.get(other) != Committed),
    resourceManagerState' = resourceManagerState.set(rm, Aborted),
  }

  action commit(rm: ResourceManager): bool = all {
    resourceManagerState.get(rm) == Prepared,
    resourceManagers.forall(other => resourceManagerState.get(other).in(Set(Prepared, Committed))),
    resourceManagerState' = resourceManagerState.set(rm, Committed),
  }

  action step: bool = {
    nondet rm = resourceManagers.oneOf()

    any {
      prepare(rm),
      commit(rm),
      decideToAbort(rm),
    }
  }

  val consistency =
    resourceManagers.forall(rm1 =>
      resourceManagers.forall(rm2 =>
        not(and {
          resourceManagerState.get(rm1) == Aborted,
          resourceManagerState.get(rm2) == Committed,
        })
      )
    )
}

module TCommitTwoManagers {
  import TCommit(
    resourceManagers = Set("rm-1", "rm-2"),
  ).*
}