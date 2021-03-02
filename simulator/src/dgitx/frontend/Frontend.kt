package dgitx.frontend

import dgitx.backend.Backend
import dgitx.LoadBalancer
import dgitx.NodeId
import kotlinx.coroutines.CompletableJob
import transaction.Manager
import transaction.Transaction
import transaction.TxID
import transaction.Votes
import java.util.concurrent.ConcurrentHashMap
import kotlin.system.exitProcess

class Frontend(val id: NodeId, private val lb: LoadBalancer, val job: CompletableJob) : Manager, LoadBalancer by lb {
    private val activeTxs = ConcurrentHashMap<TxID, TransactionManager>()

    override fun begin(txn: Transaction, votes: Votes) {
        val tm = activeTxs[txn.ID] ?: synchronized(activeTxs) {
            val empty = activeTxs[txn.ID]
            if (empty != null) return@synchronized empty
            val tmp = TransactionManager(txn, this)
            activeTxs[txn.ID] = tmp
            return@synchronized tmp
        }
        tm.collect(votes)
    }

    override fun finish(txID: TxID, resourceManager: Backend) {
        activeTxs[txID]?.finish(resourceManager)
    }

    internal fun transactionReady(txID: TxID) {
        synchronized(activeTxs) {
            activeTxs.remove(txID)
            exitProcess(0)
        }
    }

    override fun toString(): String {
        return "Frontend node-$id"
    }
}