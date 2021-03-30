package transaction

import dgitx.BNode
import dgitx.FNode
import paxos.State

/**
 * Manager responsible for managing the transaction state,
 * collect [VotesFromNode] from [Resource]
 * and make decision when to commit or abort the [Transaction].
 */
interface Manager {
    fun begin(txn: Transaction, votes: VotesFromNode)
    fun finish(txID: TxID, resourceManager: BNode)
}

/**
 * Resource receives transaction notification updates from [git.RefTxHook],
 * uses Paxos-commit protocol to broadcast git transaction changes to [paxos.PxAcceptor],
 * begin the transaction using [Manager.begin],
 * handle transaction commands: [Resource.commit] or [Resource.abort]
 * from [Manager] to commit or abort the transaction,
 * notify [Manager.finish] on finish.
 */
interface Resource {
    fun commit(id: TxID)
    fun abort(id: TxID)
}

data class Transaction(val ID: TxID, val scope: Scope)

/**
 * Scope contains all Nodes that participate int [Transaction]
 * @property[acceptors] all Replicas that store an updatable [git.Repository]
 * @property[tms] main and set of secondaries Transaction Managers.
 */
data class Scope(val acceptors: Set<BNode>, val tms: List<FNode>) {
    override fun toString(): String {
        return "acceptors: {${acceptors.joinToString()}}\ntransaction managers: {${tms.joinToString()}}"
    }
}

/**
 * @property[serverId] Node Id that has the votes.
 * @property[votes] key: Node from which a vote should be received, value: see[State]
 */
data class VotesFromNode(val serverId: Int, val votes: Map<BNode, State>)

typealias TxID = String

