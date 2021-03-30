package main

import dgitx.Dgitx
import git.PktLine
import git.PktFile
import kotlinx.coroutines.runBlocking
import wtf.g4s8.examples.configuration.Config
import java.lang.Thread.sleep
import java.util.*

fun main() {
    Config.cfg = Config.initConfig("simulator/resource/default_cfg.yml")
    val rand = Random()
    runBlocking {
        Dgitx
            .push(
                "stepan/degitx",
                PktFile(
                    PktLine(
                        "master",
                        0,
                        rand.nextInt(0x100000)
                    ),
                    PktLine(
                        "experimental",
                        0,
                        rand.nextInt(0x100000)
                    )

                )
            )
    }
    sleep(Long.MAX_VALUE)
}

