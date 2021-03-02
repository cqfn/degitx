package dgitx.frontend

import dgitx.BNode
import dgitx.FNode
import dgitx.LoadBalancer
import dgitx.NodeId
import log.Level
import transaction.Manager
import transaction.Transaction
import transaction.TxID
import transaction.VotesFromNode
import java.util.concurrent.ConcurrentHashMap
import kotlin.system.exitProcess

class Frontend(val id: NodeId, private val lb: LoadBalancer) : FNode, Manager, LoadBalancer by lb {
    private val logger = log.of(this)
    private val activeTxs = ConcurrentHashMap<TxID, TransactionManager>()

    override fun begin(txn: Transaction, votes: VotesFromNode) {
        val tm = activeTxs[txn.ID] ?: synchronized(activeTxs) {
            val empty = activeTxs[txn.ID]
            if (empty != null) return@synchronized empty
            val tmp = TransactionManager(txn, this)
            activeTxs[txn.ID] = tmp
            return@synchronized tmp
        }
        tm.collect(votes)
    }

    override fun finish(txID: TxID, resourceManager: BNode) {
        activeTxs[txID]?.finish(resourceManager)
    }

    override fun transactionReady(txID: TxID) {
        logger.message("NotifyClient", "Client")
        log.count(Level.OVER_NETWORK)
        synchronized(activeTxs) {
            activeTxs.remove(txID)
            exitProcess(0)
        }
    }

    override fun toString(): String {
        return "Frontend node-$id"
    }

    override fun disaster() {
        logger.log("is crashproof")
    }
}