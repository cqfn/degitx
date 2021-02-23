package dgitx

import git.PktLine
import java.util.concurrent.Executors


interface LoadBalancer {
    fun push(repo: RepositoryId, data: Set<PktLine>)
}

typealias RepositoryId = String
typealias NodeId = Int
val RepositoryToNodes = HashMap<RepositoryId, Set<Backend>>()
val TransactionManagers = HashMap<NodeId, Frontend>()
val ResourceManagers = HashMap<NodeId, Backend>()

val exec = Executors.newCachedThreadPool()


