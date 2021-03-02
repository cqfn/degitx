package git

import dgitx.RepositoryId
import transaction.Scope
import transaction.TxID
import java.util.concurrent.ConcurrentHashMap

interface Git {
    fun commit(repoId: RepositoryId, pktLines: PktLines, env: Scope)
    fun withRefTxHook(hook: RefTxHook)
}

/**
 * Real hook receives on standard input a line of the format:
 * <old-value> SP <new-value> SP <ref-name> LF
 * for each reference update and then TxID is computed inside the hook,
 * but I need to compute it in GitSimulator to imitate lock,
 * so to not compute it twice, i pass already computed id here.
 */
interface RefTxHook {
    suspend fun invoke(status: TxStatus, transactionId: TxID, env: Scope): Boolean
}

data class PktLine(val refName: GitRef, val oldValue: Blob, val newValue: Blob) {
    override fun toString(): String {
        return String.format("PKT-LINE (%05x %05x $refName)", oldValue, newValue)
    }
}

class PktLines(private val lines: Set<PktLine>) : Set<PktLine> by lines {
    constructor(vararg l: PktLine) : this(setOf(*l))

    override fun toString(): String {
        return """
            |----------------PKT-LINES---------------
            |${this.joinToString(separator = "\n")}
            |----------------FLUSH-PKT---------------
            """.trimMargin()
    }
}

enum class TxStatus { PREPARED, ABORTED, COMMITTED }
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