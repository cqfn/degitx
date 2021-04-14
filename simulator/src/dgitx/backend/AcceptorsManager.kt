package dgitx.backend

import dgitx.NodeId
import dgitx.frontend.TransactionManager
import paxos.PxAcceptor
import paxos.State
import wtf.g4s8.examples.configuration.Config
import wtf.g4s8.examples.spaxos.*
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.ExecutorService
import java.util.concurrent.atomic.AtomicReference

/**
 * AcceptorsManager launch new [Acceptor] for every [transaction.Transaction].
 * It stores working [Acceptor] for all actives [transaction.Transaction].
 * It redirects [TxAcceptor.prepare] and [TxAcceptor.accept] to corresponding [Acceptor]
 * that doesnt know transaction related information.
 */
//TODO rewrite java code
class AcceptorsManager(
    private val serverId: NodeId,
    private val runningAcceptors: ConcurrentHashMap<Backend.AcceptorId, Acceptor<State>>,
    private val exec: ExecutorService
) : PxAcceptor {
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
        val id = Backend.AcceptorId(txId!!, prop!!.server)
        return runningAcceptors[id] ?: run {
            val tmp = startNewAcc(txId)
            runningAcceptors[id] = tmp
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