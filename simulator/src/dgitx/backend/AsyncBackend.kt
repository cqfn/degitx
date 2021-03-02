package dgitx.backend

import dgitx.BNode
import dgitx.RepositoryId
import git.PktLines
import git.RefTxHook
import kotlinx.coroutines.*
import paxos.State
import transaction.Scope
import transaction.TxID
import wtf.g4s8.examples.spaxos.Acceptor
import wtf.g4s8.examples.spaxos.Proposal

class AsyncBackend(private val origin: BNode, private val cancel: CompletableJob) : BNode {
    override fun disaster() {
        cancel.cancel()
    }

    override fun commit(repoId: RepositoryId, pktLines: PktLines, env: Scope) {
        CoroutineScope(Dispatchers.Default).launch(cancel) {
            origin.commit(repoId, pktLines, env)
        }
    }

    override fun commit(id: TxID) {
        CoroutineScope(Dispatchers.Default).launch(cancel) {
            origin.commit(id)
        }
    }

    override fun abort(id: TxID) {
        CoroutineScope(Dispatchers.Default).launch(cancel) {
            origin.abort(id)
        }
    }

    override fun prepare(txId: String?, prop: Proposal?, callback: Acceptor.PrepareCallback<State>?) {
        CoroutineScope(Dispatchers.Default).launch(cancel) {
            origin.prepare(txId, prop, callback)
        }
    }

    override fun accept(txId: String?, prop: Proposal?, value: State?, callback: Acceptor.AcceptCallback<State>?) {
        CoroutineScope(Dispatchers.Default).launch(cancel) {
            origin.accept(txId, prop, value, callback)
        }
    }

    override fun id() = origin.id()

    override fun withRefTxHook(hook: RefTxHook) = origin.withRefTxHook(hook)

    override fun toString(): String {
        return origin.toString()
    }
}