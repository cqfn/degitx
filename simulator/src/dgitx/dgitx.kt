package dgitx

import dgitx.backend.AcceptorsManager
import dgitx.backend.AsyncBackend
import dgitx.backend.Backend
import dgitx.backend.ResourceManager
import dgitx.frontend.AsyncFrontend
import dgitx.frontend.Frontend
import dgitx.frontend.RandomLoadBalancer
import git.Git
import git.GitSimulator
import git.PktFile
import kotlinx.coroutines.Job
import log.Log
import paxos.PxAcceptor
import paxos.State
import transaction.Manager
import transaction.Resource
import transaction.TxID
import wtf.g4s8.examples.spaxos.Acceptor
import java.util.*
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.Executors
import java.util.stream.Collectors
import java.util.stream.IntStream
import kotlin.collections.HashMap

/**
 * LoadBalancer is a software component
 * that accepts an update request [PktFile] for [git.Repository]
 * and redirects the traffic for git pack uploading towards back-end nodes’ endpoints.
 */
interface LoadBalancer {
    fun push(repo: RepositoryId, data: PktFile)
}

/**
 * FNode is a hardware component
 * with all software components: [Manager] and [LoadBalancer],
 * that should be deployed on Frontend node.
 */
interface FNode : Manager, LoadBalancer {
    fun disaster()
    fun transactionReady(txID: TxID)
}

/**
 * BNode is a hardware component
 * with all software components: [Git], [Resource] and [PxAcceptor],
 * that should be deployed on Backend node.
 */
interface BNode : Git, Resource, PxAcceptor {
    fun disaster()
}

typealias RepositoryId = String
typealias NodeId = Int

/**
 * Dgitx is a dgitx system instance.
 * @property[transactionManagers] all [FNode] that is in the system.
 * @property[resourceManagers] all [BNode] that is in the system.
 * @property[repositoryToNodes] storage.
 *
 */
object Dgitx : LoadBalancer {
    private val random: Random = Random()
    val transactionManagers: Map<NodeId, FNode> =
        IntStream.range(0, Config.nFrontendNodes)
            .boxed()
            .collect(
                Collectors.toMap(
                    { id -> id },
                    {
                        AsyncFrontend(
                            Frontend(
                                it,
                                RandomLoadBalancer(it)
                            ),
                            Job()
                        )
                    })
            )
    val resourceManagers: Map<NodeId, BNode> =
        IntStream.range(0, Config.nBackendNodes)
            .boxed()
            .collect(
                Collectors.toMap(
                    { id -> id },
                    {
                        val acc = ConcurrentHashMap<Backend.AcceptorId, Acceptor<State>>()
                        val txs: MutableMap<TxID, Backend.Tx> = HashMap()
                        val job = Job()
                        AsyncBackend(
                            Backend(
                                AcceptorsManager(
                                    it,
                                    acc,
                                    Executors.newCachedThreadPool()
                                ),
                                it,
                                GitSimulator(it, job),
                                txs,
                                acc,
                                ResourceManager(txs),
                                job
                            ),
                            job
                        )
                    })
            )
    val repositoryToNodes = HashMap<RepositoryId, Set<BNode>>()

    override fun push(repo: RepositoryId, data: PktFile) {
        val redirectTmId = random.nextInt(transactionManagers.size)
        val lb = transactionManagers[redirectTmId]
        logRequest(repo, data, lb!!)
        lb.push(repo, data)
    }

    private fun logRequest(repo: RepositoryId, data: PktFile, lb: FNode) {
        Log.log(
            """ 
                |Degitx: push request to `$repo` received
                |$data
                |redirecting to $lb
                """.trimMargin()
        )
        Log.message("Push   (From::Client", lb)
    }

    override fun toString(): String {
        return "Dgitx"
    }
}



