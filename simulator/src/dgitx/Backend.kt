package dgitx

import git.Git
import git.GitSimulator
import git.RefTxHook
import git.TxStatus
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.launch
import kotlinx.coroutines.runBlocking
import paxos.PxAcceptor
import paxos.State
import transaction.*
import wtf.g4s8.examples.configuration.Config
import wtf.g4s8.examples.spaxos.*
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.AtomicReference

class Backend(private  val serverId: Int, private val git: Git): Git by git, Resource, PxAcceptor {
    private val txs = HashMap<TxID, Tx>()
    private data class AcceptorId(val txId: TxID, val serverId: Int)
    private val acceptors = ConcurrentHashMap<AcceptorId, Acceptor<State>>()

    constructor(serverId: Int) : this(serverId, GitSimulator())

    init {
        git.setRefTxHook(MeatHook())
    }

    override fun commit(id: TxID) {
        runBlocking {txs[id]!!.chan.send(true)}
    }

    override fun abort(id: TxID) {
        runBlocking {txs[id]!!.chan.send(false)}
    }

    private inner class MeatHook: RefTxHook {
        override suspend fun invoke(status: TxStatus, transactionId: TxID, env: Scope): Boolean {
            val channel = Channel<Boolean>()
            when(status) {
                TxStatus.COMMITTED -> {
                    env.TMs[0].finish(transactionId, this@Backend)
                    return true
                }
                TxStatus.ABORTED -> {
                   if (!txs.contains(transactionId)) {
                       synchronized(txs) {
                           txs[transactionId] = Tx(transactionId, State.ABORTED, channel)
                       }
                       CoroutineScope(Dispatchers.Main.immediate).launch {
                           propose(State.ABORTED, transactionId, env)
                       }
                   }
                    env.TMs[0].finish(transactionId, this@Backend)
                   return true
                }
                TxStatus.PREPARED -> {
                    synchronized(txs) {
                        txs[transactionId] = Tx(transactionId, State.PREPARED, channel)
                    }
                   propose(State.PREPARED, transactionId, env)
                   return channel.receive()
                }
            }
        }
    }

    private class Tx(val id: TxID, val descision: State, val chan: Channel<Boolean>)

    private fun propose(state: State, transactionId: TxID, env: Scope) {
        Proposer(serverId, transactionId, env.acceptors.toList()).propose(state)
                .thenApplyAsync {
                    env.TMs[0].begin(
                            Transaction(transactionId, env), collectVotes(transactionId, env)
                    )
                }
    }

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
        return  serverId
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