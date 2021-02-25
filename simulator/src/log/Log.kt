package log

interface Logger {
    fun log(msg: String)
    fun logf(fmt: String, vararg args: Any)
}

object Log : Logger {
    override fun log(msg: String) {
        println(msg)
    }

    override fun logf(fmt: String, vararg args: Any) {
        System.out.printf("$fmt\n", *args)
    }
}

class Prefixed(private val prefix: String) : Logger {
    override fun log(msg: String) {
        println("$prefix: $msg")
    }

    override fun logf(fmt: String, vararg args: Any) {
        System.out.printf("$prefix: $fmt\n", *args)
    }
}

fun of(source: Any): Logger {
    return Prefixed(source.toString())
}