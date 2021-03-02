package dgitx

import git.Git
import git.GitSimulator
import git.RefTxHook
import git.TxStatus
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.Channel
import paxos.PxAcceptor
import paxos.State
import transaction.*
import wtf.g4s8.examples.configuration.Config
import wtf.g4s8.examples.spaxos.*
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.Executors
import java.util.concurrent.atomic.AtomicReference

class Backend(private val serverId: Int, val job: CompletableJob, private val git: Git) : Git by git, Resource,
    PxAcceptor {
    private val logger = log.of(this)
    private val txs = HashMap<TxID, Tx>()
    private val exec = Executors.newCachedThreadPool()

    private data class AcceptorId(val txId: TxID, val serverId: Int)

    private val acceptors = ConcurrentHashMap<AcceptorId, Acceptor<State>>()

    constructor(serverId: Int, job: CompletableJob) : this(serverId, job, GitSimulator(serverId))

    init {
        git.withRefTxHook(MeatHook())
    }

    override fun commit(id: TxID) {
        logger.log("commit-msg for txn:$id received")
        runBlocking { txs[id]!!.chan?.send(true) }
        synchronized(txs) { txs.remove(id) }
    }

    override fun abort(id: TxID) {
        logger.log("abort-msg for txn:$id received")
        runBlocking { txs[id]!!.chan?.send(false) }
        synchronized(txs) { txs.remove(id) }
    }

    override fun toString(): String {
        return "Backend Node-$serverId"
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

    private class Tx(val id: TxID, val decision: State, val chan: Channel<Boolean>?)

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
    private fun collectVotes(transactionId: TxID, env: Scope): Votes {
        return Votes(
            serverId,
            acceptors.filter { it.key.txId == transactionId }
                .map {
                    Pair(
                        env.acceptors.first { acc -> acc.id() == it.key.serverId },
                        it.value.state()
                    )
                }.toMap()
        )
    }

    override fun id(): Int {
        return serverId
    }


    override fun prepare(txId: String?, prop: Proposal?, callback: Acceptor.PrepareCallback<State>?) {
        val acc = acceptor(txId, prop)
        acc.prepare(prop, callback)
    }

    override fun accept(txId: String?, prop: Proposal?, value: State?, callback: Acceptor.AcceptCallback<State>?) {
        val acc = acceptor(txId, prop)
        acc.accept(prop, value, callback)
    }

    private fun acceptor(txId: String?, prop: Proposal?): Acceptor<State> {
        val id = AcceptorId(txId!!, prop!!.server)
        return acceptors[id] ?: run {
            val tmp = startNewAcc(txId)
            acceptors[id] = tmp
            return@run tmp
        }
    }

    private fun startNewAcc(txId: String): Acceptor<State> {
        var acc: Acceptor<State> = InMemoryAcceptor(
            AtomicReference(State.UNKNOWN),
            serverId,
            txId
        )
        if (Config.cfg.withDrops) {
            acc = DropAcceptor(Config.cfg.dropRate, acc)
        }
        if (Config.cfg.withTimeout) {
            acc = TimeoutAcceptor(Config.cfg.timeoutMilliseconds, acc)
        }
        if (Config.cfg.async) {
            acc = AsyncAcceptor(exec, acc)
        }
        return acc
    }
}