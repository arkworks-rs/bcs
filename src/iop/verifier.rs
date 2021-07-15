/// The verifier for public coin IOP has two phases.
/// * **Commit Phase**: Verifier send message that is uniformly sampled from a random oracle. Verifier
/// will receive prover oracle, that can use used to query later.
/// * **Query And Decision Phase**: Verifier sends query and receive answer from message oracle.
trait IOPVerifier {

}