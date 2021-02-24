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

    override fun begin(txn: Transaction, votes: Votes) {
        val tm = activeTxs[txn.ID]?: synchronized(activeTxs) {
            val empty = activeTxs[txn.ID]
            if ( empty != null) return@synchronized empty
            println("inside")
            val tmp = TransactionManager(txn)
            activeTxs[txn.ID] = tmp
            return@synchronized tmp
        }
        tm.collect(votes)
    }

    override fun finish(txID: TxID, resourceManager: Backend) {
        activeTxs[txID]?.finish(resourceManager)
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
            println(voted.get())
            if (voted.incrementAndGet() == 3) {
                println(voted.get())
                decide()
            }
        }

        //TODO check for duplicate messages
        fun finish(resourceManager: Backend) {
            if (ready.incrementAndGet() == 3) {
                synchronized(activeTxs) {
                    activeTxs.remove(txn.ID)
                }
                table.forEach {
                    line ->
                        println("votes for paxos-instance ${line.key}: ")
                        line.value
                            .forEach { raw ->
                                print("rm-${raw.key}::vote-`${raw.value}`    ")
                            }
                        println()
                }
            }
        }

        private fun decide() {
            if (table.values.all { paxosInstance ->
                        paxosInstance.values.filter {
                            it == State.PREPARED
                        } .size >= 2
                    }) txn.scope.acceptors.forEach { it.commit(txn.ID) }
            if (table.values.any { paxosInstance ->
                        paxosInstance.values.filter {
                            it == State.ABORTED
                        } .size >= 2
                    }) txn.scope.acceptors.forEach { it.abort(txn.ID) }
        }
    }
}