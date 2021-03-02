package dgitx.backend

import git.Git
import git.RefTxHook
import git.TxStatus
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.Channel
import paxos.PxAcceptor
import paxos.State
import transaction.*
import wtf.g4s8.examples.spaxos.*
import java.util.concurrent.ConcurrentHashMap

class Backend(
    private val acceptor: AcceptorManager,
    private val serverId: Int,
    private val git: Git,
    private val txs: MutableMap<TxID, Tx>,
    private val runningAcceptors: ConcurrentHashMap<AcceptorId, Acceptor<State>>,
    private val resourceManager: ResourceManager
) :
    Git by git,
    Resource by resourceManager,
    PxAcceptor by acceptor {

    init {
        git.withRefTxHook(MeatHook())
    }

    private inner class MeatHook : RefTxHook {
        private val logger = log.of(this)
        override suspend fun invoke(status: TxStatus, transactionId: TxID, env: Scope): Boolean {
            when (status) {
                TxStatus.COMMITTED -> {
                    logger.log("TRANSACTION $transactionId COMMITTED \n Notify ${env.tms[0]}")
                    env.tms[0].finish(transactionId, this@Backend)
                    return true
                }
                TxStatus.ABORTED -> {
                    logger.log("TRANSACTION $transactionId ABORTED")
                    if (!txs.contains(transactionId)) {
                        synchronized(txs) {
                            txs[transactionId] = Tx(transactionId, State.ABORTED, null)
                        }
                        CoroutineScope(Dispatchers.Default).launch {
                            propose(State.ABORTED, transactionId, env)
                        }
                    }
                    env.tms[0].finish(transactionId, this@Backend)
                    return true
                }
                TxStatus.PREPARED -> {
                    logger.log("TRANSACTION $transactionId PREPARED\n ALL REFERENCE ARE LOCKED")
                    val channel = Channel<Boolean>()
                    synchronized(txs) {
                        txs[transactionId] = Tx(transactionId, State.PREPARED, channel)
                    }
                    propose(State.PREPARED, transactionId, env)
                    return channel.receive()
                }
            }
        }

        override fun toString(): String {
            return "refTxHook-(s:$serverId)"
        }
    }

    data class AcceptorId(val txId: TxID, val serverId: Int)
    class Tx(val id: TxID, val decision: State, val channel: Channel<Boolean>?)

    private val logger = log.of(this)

    private fun propose(state: State, transactionId: TxID, env: Scope) {
        Proposer(serverId, transactionId, env.acceptors.toList()).propose(state)
            .thenApplyAsync {
                val votes = collectVotes(transactionId, env)
                logger.log("""
                        |send votes for $transactionId 
                        |{
                        |${
                    votes.votes.map { "acc:$serverId for paxos instance on:${it.key} vote: ${it.value}" }
                        .joinToString(separator = "\n")
                }
                        |}
                        """.trimMargin())
                env.tms[0].begin(
                    Transaction(transactionId, env), votes
                )
            }
    }

    //TODO avoid filter over map, for ex: map key could be a single value: "txId-serverId"
    private fun collectVotes(transactionId: TxID, env: Scope): VotesFromNode {
        return VotesFromNode(
            serverId,
            runningAcceptors.filter { it.key.txId == transactionId }
                .map {
                    Pair(
                        env.acceptors.first { acc -> acc.id() == it.key.serverId },
                        it.value.state()
                    )
                }.toMap()
        )
    }

    override fun toString(): String {
        return "Backend Node-$serverId"
    }
}