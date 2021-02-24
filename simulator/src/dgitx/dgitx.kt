package dgitx

import git.PktLine
import nFrontendNodes
import java.util.*
import java.util.concurrent.Executors
import java.util.function.Function
import java.util.stream.Collectors
import java.util.stream.IntStream
import kotlin.collections.HashMap


interface LoadBalancer {
    fun push(repo: RepositoryId, data: Set<PktLine>)
}

typealias RepositoryId = String
typealias NodeId = Int
val exec = Executors.newCachedThreadPool()


object Dgitx : LoadBalancer {
    private val random: Random = Random()
    val transactionManagers: Map<NodeId, Frontend> =
            IntStream.rangeClosed(0, 2)
                    .boxed()
                    .collect(
                            Collectors.toMap(
                                    { id -> id },
                                    {Frontend(it, RandomLoadBalancer(it))})
                    )
    val resourceManagers: Map<NodeId, Backend> =
            IntStream.rangeClosed(0, 2)
                    .boxed()
                    .collect(
                            Collectors.toMap(
                                    { id -> id },
                                    {Backend(it)})
                    )
    val repositoryToNodes = HashMap<RepositoryId, Set<Backend>>()

    override fun push(repo: RepositoryId, data: Set<PktLine>) {
        transactionManagers[random.nextInt(transactionManagers.size)]!!
                .push(repo, data)
    }
}



