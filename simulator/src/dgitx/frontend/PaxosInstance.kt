package dgitx.frontend

import dgitx.Backend
import dgitx.NodeId
import paxos.PaxosId
import paxos.State

/**
 * PaxosInstance represents all votes for single paxos instance mapped to voter's id.
 */
class PaxosInstance(private val id: PaxosId, acceptors: Set<Backend>) {
    private val votes: MutableMap<NodeId, State> = acceptors
        .groupBy { it.id() }
        .mapValuesTo(HashMap(), { (_, _) -> State.UNKNOWN })
    private val quorum = (votes.size / 2) + 1

    fun state() =
        votes
            .values
            .groupBy { it }
            .mapValues { it.value.size }
            .filter { it.value >= quorum }
            .keys
            .ifEmpty { setOf(State.UNKNOWN) }
            .first()

    operator fun get(id: NodeId): State {
        return votes[id]!!
    }

    operator fun set(id: NodeId, vote: State) {
        votes[id] = vote
    }

    override fun toString(): String {
        return """
            votes for paxos-instance-$id
            ${
            votes.entries.joinToString(prefix = "| ", separator = "    |   ", postfix = " |") {
                "rm-${it.key}::vote-`${it.value}`"
            }
        }
        """.trimIndent()
    }
}