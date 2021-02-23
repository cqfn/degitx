package dgitx

import transaction.Manager
import transaction.Transaction
import transaction.TxID
import transaction.Votes

class Frontend(val id: NodeId, private val lb: LoadBalancer) : Manager, LoadBalancer by lb {

    override fun begin(txn: Transaction, votes: Votes) {
        TODO("Not yet implemented")
    }

    override fun finish(txID: TxID, resourceManager: Backend) {
        TODO("Not yet implemented")
    }
}