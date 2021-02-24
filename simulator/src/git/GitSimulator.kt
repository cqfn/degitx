package git

import dgitx.RepositoryId
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.launch
import transaction.Scope
import transaction.TxID

class GitSimulator(private var hook: RefTxHook? = null): Git {
    private val storage = Repositories()

    override fun commit(repoId: RepositoryId, pktLines: Set<PktLine>, env: Scope) {
        CoroutineScope(Dispatchers.Default).launch{
            Command(repoId, pktLines, env).apply()
        }
    }

    override fun setRefTxHook(hook: RefTxHook) {
        this.hook = hook
    }

    private inner class Command(val repoId: RepositoryId, val pktLines: Set<PktLine>, val env: Scope) {
        private val newRefs = HashSet<GitRef>()
        private val transactionId: TxID =
                pktLines.sortedBy { it.refName }
                        .map { it.hashCode().toString() }
                        .joinToString(
                                separator = "",
                                prefix = "",
                                postfix = repoId.hashCode().toString(),
                                transform = {it}
                        )

        suspend fun apply() {
            if (pktLines.any { it.compare == it.swap }) return abort()
            if (storage[repoId] == null) {
                createNewRepo()
            } else {
                update()
            }
        }

        private suspend fun createNewRepo() {
            if (pktLines.all { it.compare == 0 }) {
                val refs = pktLines.map {
                    Reference(
                            repoId = repoId,
                            name = it.refName,
                            lockedBy = transactionId,
                            tmpValue = it.swap,
                    )
                }.associateByTo(Repository()) { it.name }

                val ok = synchronized(storage) {
                    val repo = storage[repoId]
                    if (repo != null) {
                        return@synchronized false
                    } else {
                        newRefs.addAll(refs.keys)
                        storage[repoId] = refs
                        return@synchronized true
                    }
                }
                if (!ok) return abort()
                return update()
            } else {
                return abort()
            }
        }

        private suspend fun update() {
            val repo = storage[repoId]?: return abort()
            pktLines.forEach {
                if (it.compare  == 0) {
                    val ok = synchronized(repo) {
                        val ref = repo[it.refName]?: run {
                            val tmp = Reference(
                                    repoId = repoId,
                                    name = it.refName,
                                    lockedBy = transactionId,
                                    tmpValue = it.swap,
                            )
                            newRefs.add(it.refName)
                            repo[it.refName] = tmp
                            return@run tmp
                        }
                        if (ref.lockedBy != transactionId) {
                            return@synchronized false
                        }
                        return@synchronized true
                    }
                    if (!ok) return abort()
                } else {
                    val ok = synchronized(repo) {
                        val ref = repo[it.refName]?: return@synchronized false
                        if (ref.value != it.compare || ref.lockedBy != "") return@synchronized false
                        ref.lockedBy = transactionId
                        ref.tmpValue = it.swap
                        return@synchronized  true
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
                newRefs.forEach{
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
                        if (repo.isEmpty() ) storage.remove(repoId)
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
                        it.isTemporal = false
                        it.lockedBy = ""
                    }
            hook?.invoke(TxStatus.COMMITTED, transactionId, env)
        }
    }
}
