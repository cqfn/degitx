package dgitx.frontend

import dgitx.Backend
import paxos.PaxosId
import paxos.State

/**
 * Voting Table contains all PaxosInstance that participate in transaction.
 * Voting Table is filled incrementally by TM every time it receives beginTx message from RM.
 * Every RM sends only its votes for all PaxosInstances, so by every beginTx message,
 * at most one vote for every PaxosInstance would be filled.
 */
class VotingTable(voters: Set<Backend>) {
    private val table = voters
        .groupBy { it.id() }
        .mapValues { (k, _) -> PaxosInstance(k, voters) }

    fun toState(): State {
        val states = table.values
            .map { it.state() }
            .groupBy { it }
            .mapValues { it.value.size }
        return when {
            atLeastOneAborted(states) -> State.ABORTED
            allPrepared(states) -> State.PREPARED
            else -> State.UNKNOWN
        }
    }

    private fun atLeastOneAborted(states: Map<State, Int>) = states.containsKey(State.ABORTED)
    private fun allPrepared(states: Map<State, Int>) = states[State.PREPARED] == table.size

    operator fun get(id: PaxosId): PaxosInstance {
        return table[id]!!
    }

    override fun toString(): String {
        return """
            |
            |VOTING TABLE:
            |${table.values.joinToString(separator = "\n")}
            |""".trimMargin()
    }
}