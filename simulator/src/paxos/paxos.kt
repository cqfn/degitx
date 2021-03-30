package paxos

import wtf.g4s8.examples.spaxos.TxAcceptor

/**
 * Paxos acceptor.
 * <p>
 * The therminology:
 * <ul>
 * <li>minimal proposal - a proposal number for which the acceptor promised
 * to not accept any proposal less than minimal. It can be updated by any proposal
 * greater than minimal in prepare or accept phases.</li>
 * <li>accepted proposal - a proposal number which was accepted by acceptor,
 * it's always returned in prepare phase and can be changed in accept phase
 * by proposal greater that minimal proposal.</li>
 * <li>accepted value - a value accepted by proposal in accept phase,
 * this value is always returned by prepare phase and can be changed in accept
 * phase with proposal greater than minimal proposal.</li>
 * </ul>
 */
//TODO remove inheritance from Java class, when PxAcceptor will be implemented in Kotlin
interface PxAcceptor : TxAcceptor<State> {
//    fun prepare(msg: Px1A)
//    fun accept(msg: Px2A)
    fun id() : Int
}

/**
 * Paxos proposer.
 * <p>
 * The logic of proposer on proposing new value is follow:
 * <ol>
 * <li>It choses next proposal number by incrementing proposal.</li>
 * <li>It sends prepare request to quorum of live acceptors.</li>
 * <li>It checks the result of prepare, if any promise has accepted value,
 * greater than proposal number, then proposer changes inital value with
 * accepted value returned from acceptor.</li>
 * <li>It sends accept request to quorum of live acceptors using origin
 * proposal number and maybe updated value.</li>
 * <li>If any acceptor rejected accept request and returned proposal greater than
 * origin proposal, then proposer updates self proposal number with new proposal
 * and tries to propose possible updated value using next proposal again.</li>
 * </p>
 */
interface PxProposer {
    fun promised(msg: Px1B)
    fun accepted(msg: Px2B)
    fun rejected(bal: Ballot)
}

/**
 * A proposal is a number which proposer uses to identify the request,
 * it contains sequentially incremented ballot number and unique server id.
 * <p>
 * The proposal is compared by comparing ballot number first and server id second.
 * </p>
 */
interface Proposal : Comparable<Proposal> {
    fun next()
    fun update(bal: Ballot)
}

typealias PaxosId = Int
typealias Ballot = Int
data class Px1A(val proposal: Proposal)
data class Px1B(val accepted: Proposal, val vote: State)
data class Px2A(val proposal: Proposal, val vote: State)
typealias Px2B = Proposal

/**
 * State in what [PxAcceptor] is for current [transaction.Transaction]
 */
enum class State {UNKNOWN, ABORTED, PREPARED}


