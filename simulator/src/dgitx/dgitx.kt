package dgitx

import dgitx.frontend.Frontend
import dgitx.frontend.RandomLoadBalancer
import git.PktLines
import kotlinx.coroutines.Job
import log.Log
import java.util.*
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
                    { Backend(it, Job()) })
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



