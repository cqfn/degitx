package git

import dgitx.RepositoryId
import kotlinx.coroutines.CompletableJob
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.launch
import transaction.Scope
import transaction.TxID

/**
 * GitSimulator simulates git.
 * GitSimulator stores [Repositories] in its [storage].
 * It could create a new [Repository] or update existing one,
 * but it doesn't delete existing one if all references are set to 0. @see[PktLine]
 * It also invoke [RefTxHook] as original git does.
 * Each transaction eventually aborted or committed via git:
 *   - "prepared" with [Command.prepare]: All reference updates have been queued to the transaction and references were locked on disk.
 *   - "aborted" with [Command.abort]: The reference transaction was aborted, no changes were performed and the locks have been released.
 *   - "committed" with [Command.commit]: The reference transaction was committed and all references now have their respective new value.
 */
class GitSimulator(private val id: Int, private val cancel: CompletableJob) : Git {
    private var hook: RefTxHook? = null
    private val storage = Repositories()

    override fun commit(repoId: RepositoryId, pktLines: PktFile, env: Scope) {
        CoroutineScope(Dispatchers.Default).launch(cancel) {
            Command(repoId, pktLines, env)()
        }
    }

    override fun withRefTxHook(hook: RefTxHook) {
        this.hook = hook
    }

    private inner class Command(val repoId: RepositoryId, val pktLines: PktFile, val env: Scope) {
        private val newRefs = HashSet<GitRefName>()
        private val transactionId: TxID = txID()
        private val logger = log.of(this)

        suspend operator fun invoke() {
            //TODO remove this check after implementing uniqueness of the blob id
            if (pktLines.any { it.oldValue == it.newValue }) return abort()
            if (storage[repoId] == null) {
                logger.log("init new repository")
                createNewRepo()
            } else {
                logger.log("update existing repository")
                updateRepo()
            }
        }

        private suspend fun createNewRepo() {
            if (pktLines.all { it.oldValue == 0 }) {
                val refs = pktLines.map {
                    Reference(
                        repoId = repoId,
                        name = it.refName,
                        lockedBy = transactionId,
                        tmpValue = it.newValue,
                    )
                }.associateByTo(Repository()) { it.name }

                val ok = synchronized(storage) {
                    val repo = storage[repoId]
                    if (repo != null) {
                        logger.log("*concurrent* failed to init new repository `$repoId`. Already exist")
                        return@synchronized false
                    } else {
                        newRefs.addAll(refs.keys)
                        storage[repoId] = refs
                        return@synchronized true
                    }
                }
                if (!ok) return abort()
                return updateRepo()
            } else {
                logger.log("pkt-lines has not-null old-value, invalid for new repository:\n$pktLines")
                return abort()
            }
        }

        private suspend fun updateRepo() {
            val repo = storage[repoId] ?: run {
                logger.log("repository not found: $repoId")
                return abort()
            }
            pktLines.forEach {
                if (it.oldValue == 0) {
                    val ok = synchronized(repo) {
                        val ref = repo[it.refName] ?: run {
                            val tmp = Reference(
                                repoId = repoId,
                                name = it.refName,
                                lockedBy = transactionId,
                                tmpValue = it.newValue,
                            )
                            newRefs.add(it.refName)
                            repo[it.refName] = tmp
                            return@run tmp
                        }
                        if (ref.lockedBy != transactionId) {
                            logger.log("reference: ${ref.name} is already locked by ${ref.lockedBy}")
                            return@synchronized false
                        }
                        return@synchronized true
                    }
                    if (!ok) return abort()
                } else {
                    val ok = synchronized(repo) {
                        val ref = repo[it.refName] ?: run {
                            logger.log("reference ${it.refName} with not null old-value: ${it.oldValue} not found in repository: $repoId")
                            return@synchronized false
                        }
                        if (ref.value != it.oldValue) {
                            logger.log("comparison failed: expected old-value{${it.oldValue}} actual{${ref.value}}")
                            return@synchronized false
                        }
                        if (ref.lockedBy != "") {
                            logger.log("reference: ${ref.name} is already locked by ${ref.lockedBy}")
                            return@synchronized false
                        }
                        ref.lockedBy = transactionId
                        ref.tmpValue = it.newValue
                        return@synchronized true
                    }
                    if (!ok) return abort()
                }
            }
            if (repo !== storage[repoId]) return abort()
            return prepare()
        }

        private suspend fun prepare() {
            val ok = hook?.invoke(TxStatus.PREPARED, transactionId, env) ?: true
            if (ok) {
                commit()
            } else {
                abort()
            }
        }

        private suspend fun abort() {
            storage[repoId]?.let { repo ->
                newRefs.forEach {
                    repo.remove(it)
                }
                repo.values.filter { it.lockedBy == transactionId }
                    .forEach {
                        it.tmpValue = null
                        it.lockedBy = ""
                    }
            }
            synchronized(storage) {
                storage[repoId]?.let { repo ->
                    synchronized(repo) {
                        if (repo.isEmpty()) storage.remove(repoId)
                    }
                }
            }
            hook?.invoke(TxStatus.ABORTED, transactionId, env)
        }

        private suspend fun commit() {
            storage[repoId]!!.values
                .filter { it.lockedBy == transactionId }
                .forEach {
                    it.value = it.tmpValue!!
                    it.lockedBy = ""
                }
            hook?.invoke(TxStatus.COMMITTED, transactionId, env)
        }

        /**
         * A set of [PktLine] compose an unique txID
         * while two different pushes can never contain
         * a pkt-line with the same newValue (@todo not yet implemented in simulator)
         * new value is a blob id and it can't be same for multiple commiters
         */
        //TODO better hashCode & remove postfix
        private fun txID() = pktLines.sortedBy { it.refName }
            .map { it.hashCode().toString() }
            .joinToString(
                separator = "",
                prefix = "",
                postfix = repoId.hashCode().toString(),
                transform = { it }
            )

        override fun toString(): String {
            return "git-(txn:$transactionId, s:$id)"
        }
    }
}
