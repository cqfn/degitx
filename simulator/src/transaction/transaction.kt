package transaction

import dgitx.BNode
import dgitx.FNode
import paxos.State

interface Manager {
    fun begin(txn: Transaction, votes: VotesFromNode)
    fun finish(txID: TxID, resourceManager: BNode)
}

interface Resource {
    fun commit(id: TxID)
    fun abort(id: TxID)
}
data class Transaction(val ID: String, val scope: Scope)
data class Scope(val acceptors: Set<BNode>, val tms: List<FNode>) {
    override fun toString(): String {
        return "acceptors: {${acceptors.joinToString()}}\ntransaction managers: {${tms.joinToString()}}"
    }
}
data class VotesFromNode(val serverId: Int, val votes: Map<BNode, State>)
typealias TxID = String

