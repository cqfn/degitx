package dgitx.frontend

import dgitx.backend.Backend
import paxos.State
import transaction.Transaction
import transaction.VotesFromNode
import java.util.concurrent.atomic.AtomicInteger

//TODO check for duplicate messages
class TransactionManager(private val txn: Transaction, private val frontend: Frontend) {
    private val logger = log.of(this)
    private val ready = AtomicInteger()
    private val voted = AtomicInteger()
    private val table: VotingTable = VotingTable(txn.scope.acceptors)

    fun collect(votes: VotesFromNode) {
        votes.votes.forEach {
            table[it.key.id()][votes.serverId] = it.value
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
            frontend.transactionReady(txn.ID)
        }
    }

    private fun decide() {
        logger.log("decide according vote table:")
        logger.log(table.toString())
        when (table.toState()) {
            State.PREPARED -> {
                logger.log("decided to COMMIT txn:${txn.ID}")
                txn.scope.acceptors.forEach { it.commit(txn.ID) }
            }
            State.ABORTED -> {
                logger.log("decided to ABORT txn:${txn.ID}")
                txn.scope.acceptors.forEach { it.abort(txn.ID) }
            }
            State.UNKNOWN -> {
            }
        }
    }

    override fun toString(): String {
        return "TM-(${frontend} , txn:${txn.ID})"
    }
}