package dgitx

import git.PktLine
import nReplicas
import transaction.Scope
import java.util.*
import java.util.stream.Collectors
import java.util.stream.IntStream

private val random: Random = Random()
private val rmBound = Dgitx.resourceManagers.size
private val tmBound = Dgitx.transactionManagers.size

class RandomLoadBalancer(private val id: NodeId) : LoadBalancer {

    override fun push(repo: RepositoryId, data: Set<PktLine>) {
        val tms = primaryWithRandomSecondaryTm()
        val replicas = Dgitx.repositoryToNodes[repo]?: randomBackendNodes()
        val scope = Scope(replicas, tms)
        replicas.forEach {
            it.commit(repo, data, scope)
        }
    }

    private fun primaryWithRandomSecondaryTm()  =
            random.ints(0, tmBound)
            .distinct()
            .filter { it != id }
            .limit(1)
            .flatMap { IntStream.of(it, id) }
            .mapToObj { Dgitx.transactionManagers[it]!! }
            .collect(Collectors.toUnmodifiableList())

    /**
     * Choose nReplicas randomly to store new repo
     */
    private fun randomBackendNodes() =
        random.ints(0, rmBound)
                .distinct()
                .limit(nReplicas)
                .mapToObj { Dgitx.resourceManagers[it]!! }
                .collect(Collectors.toUnmodifiableSet())
}