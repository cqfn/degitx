package production

import dgitx.Frontend
import dgitx.RandomLoadBalancer
import git.PktLine

fun main() {
    Frontend(
            1,
            RandomLoadBalancer(1)
    )
        .push(
            "stepan/degitx",
            setOf(
                PktLine(
                    "master",
                    24,
                    73
                )
            )
        )
}

