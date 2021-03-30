package git

import dgitx.RepositoryId
import transaction.Scope
import transaction.TxID
import java.util.concurrent.ConcurrentHashMap

/**
 * see[GitSimulator]
 */
interface Git {
    fun commit(repoId: RepositoryId, pktLines: PktFile, env: Scope)
    fun withRefTxHook(hook: RefTxHook)
}

/**
 * RefTxHook mocks git's reference transaction hook.
 * reference transaction hook triggered at reference transaction state changes,
 * responsible for communication with RM and waiting for signals from RM to continue or abort the transaction.
 * See https://git-scm.com/docs/githooks#_reference_transaction
 *
 * Real hook receives on standard input a line of the format:
 * <old-value> SP <new-value> SP <ref-name> LF
 * for each reference update and then [TxID] is computed inside the hook,
 * but I need to compute it in GitSimulator to imitate lock,
 * so to not compute it twice, I pass already computed id here.
 */
interface RefTxHook {
    suspend fun invoke(status: TxStatus, transactionId: TxID, env: Scope): Boolean
}

/**
 * PktLine represent a single reference update.
 * @property[refName] e.g: master, 42-feature-name
 * @property[oldValue] if old value is 0, new branch is created
 * @property[newValue] if new value is 0, a branch is deleted.
 * see https://git-scm.com/docs/pack-protocol
 */
data class PktLine(val refName: GitRefName, val oldValue: Blob, val newValue: Blob) {
    override fun toString(): String {
        return String.format("PKT-LINE (%05x %05x $refName)", oldValue, newValue)
    }
}

/**
 * PktLines is a set of [PktLine]
 * It emulates a Packetfile.
 * see https://git-scm.com/docs/pack-protocol#_packfile_negotiation
 */
class PktFile(private val lines: Set<PktLine>) : Set<PktLine> by lines {
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
typealias GitRefName = String
typealias Blob = Int
typealias Repository = ConcurrentHashMap<GitRefName, Reference>
typealias Repositories = ConcurrentHashMap<RepositoryId, Repository>

data class Reference(
    val repoId: RepositoryId,
    val name: GitRefName,
    var lockedBy: TxID,
    var value: Blob = 0,
    var tmpValue: Blob?,
)