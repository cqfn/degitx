package git

import dgitx.RepositoryId
import transaction.Scope
import transaction.TxID
import java.util.concurrent.ConcurrentHashMap

interface Git {
    fun commit(repoId: RepositoryId, pktLines: Set<PktLine>, env: Scope)
    fun setRefTxHook(hook: RefTxHook)
}

/**
 * Real hook receives on standard input a line of the format:
 * <old-value> SP <new-value> SP <ref-name> LF
 * for each reference update and then TxID is computed inside the hook,
 * but I need to compute it in GitSimulator to imitate lock,
 * so to not compute it twice, i pass already computed id here.
 */
interface RefTxHook {
    suspend fun invoke(status: TxStatus, transactionId: TxID, env: Scope) : Boolean
}

data class PktLine(val refName: GitRef, val compare: Blob, val swap: Blob) {
    private val hashCode = StringBuilder()
            .append(compare)
            .append(swap)
            .append(refName)
            .toString()
            .hashCode()

    override fun hashCode() = hashCode

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as PktLine

        if (refName != other.refName) return false
        if (compare != other.compare) return false
        if (swap != other.swap) return false

        return true
    }
}
typealias GitRef = String
typealias Blob = Int
typealias Repository = ConcurrentHashMap<GitRef, Reference>
typealias Repositories = ConcurrentHashMap<RepositoryId, Repository>

data class Reference(
        val repoId: RepositoryId,
        val name: GitRef,
        var lockedBy: TxID,
        var value: Blob = 0,
        var tmpValue: Blob?,
        var isTemporal: Boolean = true
)

enum class TxStatus() {PREPARED, ABORTED, COMMITTED}