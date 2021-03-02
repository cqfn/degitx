import log.Level

object Config {
    val nReplicas = 3
    val nRepository = 100
    val nBackendNodes = nReplicas * 1
    val nFrontendNodes = 2
    val logLevel = Level.OVER_NETWORK
}


