package dgitx.backend

import kotlinx.coroutines.runBlocking
import transaction.Resource
import transaction.TxID

class ResourceManager(private val txs: MutableMap<TxID, Backend.Tx>) : Resource {
    private val logger = log.of(this)

    override fun commit(id: TxID) {
        logger.log("commit-msg for txn:$id received")
        runBlocking { txs[id]!!.channel?.send(true) }
        synchronized(txs) { txs.remove(id) }
    }

    override fun abort(id: TxID) {
        logger.log("abort-msg for txn:$id received")
        runBlocking { txs[id]!!.channel?.send(false) }
        synchronized(txs) { txs.remove(id) }
    }
}