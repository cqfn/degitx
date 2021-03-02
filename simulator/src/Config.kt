import log.Level

object Config {
    val nReplicas = 3L
    val nRepository = 100
    val nBackendNodes = nReplicas * 10
    val nFrontendNodes = 6
    val logLevel = Level.ALL
}


