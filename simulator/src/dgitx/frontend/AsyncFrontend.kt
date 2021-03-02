package dgitx.frontend

import dgitx.BNode
import dgitx.FNode
import dgitx.RepositoryId
import git.PktLines
import kotlinx.coroutines.CompletableJob
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.launch
import transaction.Transaction
import transaction.TxID
import transaction.VotesFromNode

class AsyncFrontend(private val origin: FNode, private val cancel: CompletableJob) : FNode {
    override fun disaster() {
        cancel.cancel()
    }

    override fun begin(txn: Transaction, votes: VotesFromNode) {
        CoroutineScope(Dispatchers.Default).launch(cancel) {
            origin.begin(txn, votes)
        }
    }

    override fun finish(txID: TxID, resourceManager: BNode) {
        CoroutineScope(Dispatchers.Default).launch(cancel) {
            origin.finish(txID, resourceManager)
        }
    }

    override fun push(repo: RepositoryId, data: PktLines) {
        CoroutineScope(Dispatchers.Default).launch(cancel) {
            origin.push(repo, data)
        }
    }

    override fun transactionReady(txID: TxID) {
        origin.transactionReady(txID)
    }

    override fun toString(): String {
        return origin.toString()
    }
}