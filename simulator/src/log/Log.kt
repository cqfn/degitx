package log

import java.util.concurrent.atomic.AtomicInteger

enum class Level{MESSAGE, ALL}

interface Logger {
    fun log(msg: String)
    fun logf(fmt: String, vararg args: Any)
    fun message(msg: String)
    fun messagef(fmt: String, vararg args: Any)
}

val nMsg: AtomicInteger = AtomicInteger(1)

object Log : Logger {
    override fun log(msg: String) {
        if (Config.logLevel == Level.ALL) {
            println(msg)
        }
    }

    override fun logf(fmt: String, vararg args: Any) {
        if (Config.logLevel == Level.ALL) {
            System.out.printf("$fmt\n", *args)
        }
    }

    override fun message(msg: String) {
        nMsg.incrementAndGet()
        println(msg)
    }

    override fun messagef(fmt: String, vararg args: Any) {
        nMsg.incrementAndGet()
        System.out.printf("$fmt\n", *args)
    }

}

class Prefixed(private val prefix: String) : Logger {
    override fun log(msg: String) {
        if (Config.logLevel == Level.ALL) {
            println("$prefix: $msg")
        }
    }

    override fun logf(fmt: String, vararg args: Any) {
        if (Config.logLevel == Level.ALL) {
            System.out.printf("$prefix: $fmt\n", *args)
        }
    }

    override fun message(msg: String) {
        nMsg.incrementAndGet()
        println("$prefix: $msg")
    }

    override fun messagef(fmt: String, vararg args: Any) {
        nMsg.incrementAndGet()
        System.out.printf("$prefix: $fmt\n", *args)
    }
}

fun of(source: Any): Logger {
    return Prefixed(source.toString())
}
