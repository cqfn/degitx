package dgitx

import paxos.State
import transaction.Manager
import transaction.Transaction
import transaction.TxID
import transaction.Votes
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.AtomicInteger

class Frontend(val id: NodeId, private val lb: LoadBalancer) : Manager, LoadBalancer by lb {
    private val activeTxs = ConcurrentHashMap<TxID, TransactionManager>()
    private val logger = log.of(this)

    override fun begin(txn: Transaction, votes: Votes) {
        val tm = activeTxs[txn.ID]?: synchronized(activeTxs) {
            val empty = activeTxs[txn.ID]
            if ( empty != null) return@synchronized empty
            val tmp = TransactionManager(txn)
            activeTxs[txn.ID] = tmp
            return@synchronized tmp
        }
        tm.collect(votes)
    }

    override fun finish(txID: TxID, resourceManager: Backend) {
        activeTxs[txID]?.finish(resourceManager)
    }

    override fun toString(): String {
        return "Frontend node-$id"
    }

    //TODO check for duplicate messages
    private inner class TransactionManager(val txn: Transaction) {
        val ready = AtomicInteger()
        val voted = AtomicInteger()
        val table: Map<Int, java.util.HashMap<Int, State>> =
                txn.scope.acceptors
                    .map { it.id() }
                    .associateWithTo(HashMap()) { State.UNKNOWN }
                    .let { votes ->
                        txn.scope.acceptors.
                        associate { Pair(it.id(), votes) }
                    }

        fun collect(votes: Votes) {
            votes.votes.forEach {
                table[it.key.id()]!![votes.serverId] = it.value
            }
            if (voted.incrementAndGet().also {
                        logger.log("[$it] begin-msg txn:${txn.ID} from Backend-${votes.serverId} received")
                    } == 3) {
                decide()
            }
        }

        //TODO check for duplicate messages
        fun finish(resourceManager: Backend) {
            if (ready.incrementAndGet().also {
                        logger.log("[$it]finish-msg txn:${txn.ID} from $resourceManager received")
                    } == 3) {
                synchronized(activeTxs) {
                    activeTxs.remove(txn.ID)
                    System.exit(0)
                }
            }
        }

        private fun decide() {
            logger.log("decide according vote table:")
            table()
            if (table.values.all { paxosInstance ->
                        paxosInstance.values.filter {
                            it == State.PREPARED
                        } .size >= 2
                    }) txn.scope.acceptors.also {
                        logger.log("decided to COMMIT")
            }.forEach { it.commit(txn.ID) }
            if (table.values.any { paxosInstance ->
                        paxosInstance.values.filter {
                            it == State.ABORTED
                        } .size >= 2
                    }) txn.scope.acceptors.also {
                logger.log("decided to ABORT")
            }.forEach { it.abort(txn.ID) }
        }

        private fun table() {
            println("---------RESULT VOTE TABLE ON ${this@Frontend}---------")
            table.forEach { line ->
                println("votes for paxos-instance ${line.key}: ")
                line.value
                        .forEach { raw ->
                            print("rm-${raw.key}::vote-`${raw.value}`    ")
                        }
                println()
            }
        }
    }
}