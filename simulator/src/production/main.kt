package production

import dgitx.Dgitx
import git.PktLine
import kotlinx.coroutines.runBlocking
import wtf.g4s8.examples.configuration.Config
import java.lang.Thread.sleep

fun main() {
    Config.cfg = Config.initConfig("simulator/resource/default_cfg.yml")
    runBlocking {
        Dgitx
                .push(
                        "stepan/degitx",
                        setOf(
                                PktLine(
                                        "master",
                                        0,
                                        73
                                )
                        )
                )
    }
    sleep(Long.MAX_VALUE)
}

