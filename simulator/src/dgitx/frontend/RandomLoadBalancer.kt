package dgitx.frontend

import dgitx.Dgitx
import dgitx.LoadBalancer
import dgitx.NodeId
import dgitx.RepositoryId
import git.PktFile
import transaction.Scope
import java.util.*
import java.util.stream.Collectors
import java.util.stream.IntStream

class RandomLoadBalancer(private val id: NodeId) : LoadBalancer {
    companion object {
        private val random: Random = Random()
    }

    private val logger = log.of(this)

    override fun push(repo: RepositoryId, data: PktFile) {
        val tms = primaryWithRandomSecondaryTm()
        val replicas = Dgitx.repositoryToNodes[repo] ?: randomBackendNodes()
        val scope = Scope(replicas, tms)
        logger.log("transaction scope prepared:\n$scope\nredirect to backend nodes")
        replicas.forEach {
            logger.message("CompareAndSwap", it)
            it.commit(repo, data, scope)
        }
    }

    private fun primaryWithRandomSecondaryTm() =
        random.ints(0, Dgitx.transactionManagers.size)
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
        random.ints(0, Dgitx.resourceManagers.size)
            .distinct()
            .limit(Config.nReplicas.toLong())
            .mapToObj { Dgitx.resourceManagers[it]!! }
            .collect(Collectors.toUnmodifiableSet())

    override fun toString(): String {
        return "LB-$id"
    }
}