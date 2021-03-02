package log

import java.util.concurrent.atomic.AtomicInteger

enum class Level { PAXOS, OVER_NETWORK, ALL }

interface Logger {
    fun log(msg: String)
    fun message(msg: String, to: Any)
    fun paxos(msg: String)
}

val nMsg: AtomicInteger = AtomicInteger(0)
val nPaxos: AtomicInteger = AtomicInteger(0)

object Log : Logger {
    override fun log(msg: String) {
        if (Config.logLevel == Level.ALL) {
            println(msg)
        }
    }

    override fun message(msg: String, to: Any) {
        if (Config.logLevel == Level.OVER_NETWORK) {
            nMsg.incrementAndGet()
            println("$msg   To::[$to])")
        }
    }

    override fun paxos(msg: String) {
        nPaxos.incrementAndGet()
        println(msg)
    }

}

class Prefixed(private val prefix: String) : Logger {
    override fun log(msg: String) {
        Log.log("$prefix: $msg")
    }

    override fun message(msg: String, to: Any) {
        Log.message("$msg   (From::$prefix", to)
    }

    override fun paxos(msg: String) {
        Log.paxos("$prefix: $msg")
    }

}

fun of(source: Any): Logger {
    return Prefixed(source.toString())
}

fun count(type: Level) {
    when(type) {
        Level.OVER_NETWORK -> println("Total messages sent over network by Degitx: ${nMsg.get()}")
        Level.PAXOS -> println("Total messages sent over network by Paxos: ${nPaxos.get()}")
        Level.ALL -> {}
    }
}
