package transaction

import dgitx.*
import paxos.State

interface Manager {
    fun begin(txn: Transaction, votes: Votes)
    fun finish(txID: TxID, resourceManager: Backend)
}

interface Resource {
    fun commit(id: TxID)
    fun abort(id: TxID)
}
data class Transaction(val ID: String, val scope: Scope)
data class Scope(val acceptors: Set<Backend>, val TMs: List<Frontend>)
data class Votes(val serverId: Int, val votes: Map<Backend, State>)
typealias TxID = String

