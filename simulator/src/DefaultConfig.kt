import dgitx.Frontend


const val nRepository = 100
const val nReplicas = 3L
const val nBackendNodes = nReplicas * 10
const val nFrontendNodes = 6


data class MetadataStorage(val fronts: FrontendNodes, val backs: BackendNodes)
typealias FrontendNodes = Map<String, Frontend>
typealias BackendNodes = Map<String, Frontend>

