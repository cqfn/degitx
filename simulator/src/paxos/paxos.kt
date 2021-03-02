package paxos

import wtf.g4s8.examples.spaxos.TxAcceptor


interface PxAcceptor : TxAcceptor<State> {
//    fun prepare(msg: Px1A)
//    fun accept(msg: Px2A)
    fun id() : Int
}

interface PxProposer {
    fun promised(msg: Px1B)
    fun accepted(msg: Px2B)
    fun rejected(bal: Ballot)
}

interface Proposal : Comparable<Proposal> {
    fun next()
    fun update(bal: Ballot)
}

typealias PaxosId = Int
typealias Ballot = Int
data class Px1A(val proposal: Proposal)
data class Px1B(val accepted: Proposal, val vote: State) //val max: Ballot,
data class Px2A(val proposal: Proposal, val vote: State)
typealias Px2B = Proposal
enum class State {UNKNOWN, ABORTED, PREPARED}


