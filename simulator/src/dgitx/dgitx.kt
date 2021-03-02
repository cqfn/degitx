package dgitx

import dgitx.backend.AcceptorManager
import dgitx.backend.Backend
import dgitx.backend.ResourceManager
import dgitx.frontend.Frontend
import dgitx.frontend.RandomLoadBalancer
import git.GitSimulator
import git.PktLines
import kotlinx.coroutines.Job
import log.Log
import paxos.State
import transaction.TxID
import wtf.g4s8.examples.spaxos.Acceptor
import java.util.*
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.Executors
import java.util.stream.Collectors
import java.util.stream.IntStream
import kotlin.collections.HashMap

interface LoadBalancer {
    fun push(repo: RepositoryId, data: PktLines)
}

typealias RepositoryId = String
typealias NodeId = Int

object Dgitx : LoadBalancer {
    private val random: Random = Random()
    val transactionManagers: Map<NodeId, Frontend> =
        IntStream.rangeClosed(0, 2)
            .boxed()
            .collect(
                Collectors.toMap(
                    { id -> id },
                    {
                        Frontend(
                            it,
                            RandomLoadBalancer(it),
                            Job()
                        )
                    })
            )
    val resourceManagers: Map<NodeId, Backend> =
        IntStream.rangeClosed(0, 2)
            .boxed()
            .collect(
                Collectors.toMap(
                    { id -> id },
                    {
                        val acc = ConcurrentHashMap<Backend.AcceptorId, Acceptor<State>>()
                        val txs: MutableMap<TxID, Backend.Tx> = HashMap()
                        Backend(
                            AcceptorManager(
                                it,
                                acc,
                                Executors.newCachedThreadPool()
                            ),
                            it,
                            GitSimulator(it),
                            txs,
                            acc,
                            ResourceManager(txs)
                        )
                    })
            )
    val repositoryToNodes = HashMap<RepositoryId, Set<Backend>>()

    override fun push(repo: RepositoryId, data: PktLines) {
        val redirectTmId = random.nextInt(transactionManagers.size)
        val lb = transactionManagers[redirectTmId]
        logRequest(repo, data, lb!!)
        lb.push(repo, data)
    }

    private fun logRequest(repo: RepositoryId, data: PktLines, lb: Frontend) {
        Log.logf(
            """ 
                |Degitx: push request to `$repo` received
                |$data
                |redirecting to $lb
                """.trimMargin()
        )
    }
}



