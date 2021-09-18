<h1 align="center">ark-bcs tutorial</h1>

In this tutorial, we are going to write a public coin RS-IOP for the sum of univariate polynomial.

##### Table of Contents

* [Background](#background)
* [Example Protocol Spec](#example-protocol-spec)
* [Build Simple Univariate Sumcheck](#build-simple-univariate-sumcheck)
* [Build Main Protocol](#build-main-protocol)
* [Put it together: Proof Generation](#put-it-together-proof-generation)

## Background

In `ark-bcs`, a public coin (RS-)IOP have two phases: 

- **Commit Phase:** Prover run the interactive proof generation code, where prover can send message oracles with or without degree bound, and short messages. Verifier can send message sampled uniformly without reading prover messages. Ideally, verifier delays all verifier messages to next phase. 
- **Query and decision phase:** Verifier starts in a clean state, can query prover's message in arbitrary order, and have access to all previously sent messages. Verifier will generate an user-defined output. Prover do not have query and decision phase. 

Here is a table summarizing what prover/verifier can do in each phase. 

|                                   | Commit Phase (Prover)         | Commit Phase (Verifier)                                      | Query Phase (Verifier)                               |
| --------------------------------- | ----------------------------- | ------------------------------------------------------------ | ---------------------------------------------------- |
|                                   | `prove`: send prover messages | `restore_from_commit_phase`: simulate the interaction from a SNARK | `query_and_decide`: query prover messages and decide |
| Previously Sent Prover Messages   | Yes                           | No                                                           | Oracle Access Only                                   |
| Previously Sent Verifier Messages | Yes                           | Yes*                                                         | Yes                                                  |
| Parameter                         | Yes                           | Yes                                                          | Yes                                                  |
| Public Input                      | Yes                           | No**                                                         | Yes                                                  |
| Private Input                     | Yes                           | No                                                           | No                                                   |

**: BCS Paper does not allow verifier to have access to previously sent verifier messages, but our implementation makes this possible for flexibility. Use with caution!*

***:  Although in BCS paper, public input can decide number of rounds, `ark-bcs` does not allow transcript structure (e.g. number of rounds, degree bound, etc) to depend on public input. Instead, user can specify verifier parameter that can change the transcript structure.*

## Example Protocol Spec

Here is the spec for the example protocol we will build!

**Private Input**: Coefficients of`poly1`, `Poly2`. *For this example, those two coefficients are selected arbitrarily. In real scenario, those coefficients can come from elsewhere.*

**Public Input:** asserted sum of `poly1` over summation domain, asserted sum of `poly2` over summation domain

**Prover & Parameters:** evaluations domain, summation domain, degree bound

**Satisfy Condition:** asserted sums are correct. 

| Prover                                                       | Verifier                                  |
| ------------------------------------------------------------ | ----------------------------------------- |
|                                                              | Send two random field elements `r1`, `r2` |
| Send evaluations`r1*poly1`, `r2*poly2`over evaluation domain in one round.* |                                           |
| Invoke univariate sumcheck on `r1*poly1`                     | Invoke univariate sumcheck on `r1*poly1`  |
| Invoke univariate sumcheck on `r2*poly2`                     | Invoke univariate sumcheck on `r2*poly2`  |

**: In real scenario, we probably do not send this message because same message may already present elsewhere (e.g.as witness assignment), and we can simply take a reference to that message.*

## Build Simple Univariate Sumcheck

Before we write the main protocol, let's build a subprotocol `SimpleSumcheck` so that the main protocol can simply invoke this subprotocol as a black box. Note that this protocol is solely a toy example and not optimized, so do not use it in production!

### Overview of Simple Univariate Sumcheck

In this simple univariate sumcheck, the verifier has oracle access to the evaluations of polynomial`f` over evaluation domain. We want to check if the sum of evaluations of `f` at summation domain equals to `gamma`. 

The sumcheck verifier needs to have `degree`, `evaluation_domain`, `summation_domain` as parameter. So, we define the following struct:

```rust
#[derive(Clone, Debug)]
pub struct SumcheckVerifierParameter<F: PrimeField> {
    /// Degree of the polynomial input
    pub degree: usize,
    /// evaluation domain
    pub evaluation_domain: Radix2EvaluationDomain<F>,
    /// summation domain
    pub summation_domain: Radix2EvaluationDomain<F>,
}
```

Prover's parameter in this protocol also needs the coefficients of the polynomial that we take the sum, so we define the prover parameter is below:

```rust
#[derive(Clone, Debug)]
pub struct SumcheckProverParameter<F: PrimeField> {
    /// he coefficients corresponding to the `poly` in `SumcheckOracleRef`
    pub coeffs: DensePolynomial<F>,
    /// Degree of the polynomial input
    pub degree: usize,
    /// evaluation domain
    pub evaluation_domain: Radix2EvaluationDomain<F>,
    /// summation domain
    pub summation_domain: Radix2EvaluationDomain<F>,
}
```

The (RS-)IOP interface requires that verifier parameter is the subset of prover parameter, and let's show the prover parameter is valid. 

```rust
impl<F: PrimeField> ProverParam for SumcheckProverParameter<F> {
    type VerifierParameter = SumcheckVerifierParameter<F>;

    fn to_verifier_param(&self) -> Self::VerifierParameter {
        Self::VerifierParameter {
            degree: self.degree,
            evaluation_domain: self.evaluation_domain,
            summation_domain: self.summation_domain,
        }
    }
}
```

Additionally, verifier needs to have oracle access to oracle evaluations. In almost all cases, the oracle evaluations is already sent by prover previously in the same transcript, so univariate sumcheck verifier only needs an oracle reference. In code: 

```rust
#[derive(Clone, Debug, Copy)]
pub struct SumcheckOracleRef {
    poly: MsgRoundRef,
}
```

Again, oracle reference for prover is a superset of oracle reference for verifier, in code, we need to implement this trait to show this fact: 

```rust
impl ProverOracleRefs for SumcheckOracleRef {
    type VerifierOracleRefs = Self;

    fn to_verifier_oracle_refs(&self) -> Self::VerifierOracleRefs {
        self.clone()
    }
}
```

The protocol reads **claimed sum** in public input. It is sometimes tricky to determine what puts to verifier parameter and what puts to public input. `ark-bcs` implementation requires that public-input should not change the structure of transcript, including number of rounds, type of message at each round, or degree bound. Therefore, verifier do not have access to public input in `restore_from_commit_phase` function, which simulates interaction with prover in commit phase using succinct proof. 

Also, one `MsgRoundRef` represents one round, and one round can have multiple oracles with same length sharing one merkle tree, sumcheck protocol also needs to know which oracle in that round is the oracle we want. In code, we need this as public input: 

```rust
#[derive(Clone)]
pub struct SumcheckPublicInput<F: PrimeField + Absorb> {
    claimed_sum: F,
    /// `SumcheckOracleRef` represents one round, which can contain multiple
    /// oracles. Which oracle do we want to look at?
    which: usize,
}
```

Ideally every implementation in a virtual struct that implements `IOPProver` and `IOPVerifier` trait. For `SimpleSumcheck`, we can define the following struct, and implement the two traits: 

```rust
pub struct SimpleSumcheck<F: PrimeField + Absorb> {
    _field: PhantomData<F>,
}

impl<F: PrimeField + Absorb> IOPProver<F> for SimpleSumcheck<F> {
    type ProverParameter = SumcheckProverParameter<F>;
    type RoundOracleRefs = SumcheckOracleRef;
    type PublicInput = SumcheckPublicInput<F>;
    type PrivateInput = ();

    fn prove<MT: Config<Leaf = [F]>, S: CryptographicSponge>(
        namespace: &NameSpace,
        oracle_refs: &Self::RoundOracleRefs,
        public_input: &Self::PublicInput,
        _private_input: &Self::PrivateInput,
        transcript: &mut Transcript<MT, S, F>,
        prover_parameter: &Self::ProverParameter,
    ) -> Result<(), ark_bcs::Error>
    where
        MT::InnerDigest: Absorb,
    {todo!();}
}

impl<S: CryptographicSponge, F: PrimeField + Absorb> IOPVerifier<S, F> for SimpleSumcheck<F> {
    type VerifierOutput = bool;
    type VerifierParameter = SumcheckVerifierParameter<F>;
    type OracleRefs = SumcheckOracleRef;
    type PublicInput = SumcheckPublicInput<F>;

    fn restore_from_commit_phase<MT: Config<Leaf = [F]>>(
        namespace: &NameSpace,
        transcript: &mut SimulationTranscript<MT, S, F>,
        verifier_parameter: &Self::VerifierParameter,
    ) where
        MT::InnerDigest: Absorb,
    {
        todo!();
    }

    fn query_and_decide<O: RoundOracle<F>>(
        namespace: &NameSpace,
        verifier_parameter: &Self::VerifierParameter,
        public_input: &Self::PublicInput,
        oracle_refs: &Self::OracleRefs, 
        random_oracle: &mut S,
        messages_in_commit_phase: &mut MessagesCollection<&mut O, VerifierMessage<F>>,
    ) -> Result<Self::VerifierOutput, Error> {
        todo!();
    }
}
```

Note that any protocol that does not need to access oracles from other protocols (i.e. `OracleRefs = ()`) can be automatically made into a succinct proof using BCS transform. For example, suppose we have protocol `A`, which uses subprotocol `B`. `A` does not uses any oracles outside its scope, but verifier of `B` needs to access one oracle sent in `A`. In this case, protocol `A` can be accepted by BCS transform, but protocol `B` cannot be transformed without defining a wrapper. For `SimpleSumcheck`, because it does need to access oracle outside its scope, `SimpleSumcheck` can only be used as a subprotocol and cannot directly be transformed to a succinct proof using BCS. 

Now let's build the main prover and verifier code! First, let's review what prover and verifier do in this protocol. Suppose the polynomial we takes some is `f(x)`, and let `H` be summation domain, `V_H(x)` be vanishing polynomial of the summation domain, `|H| `be size of summation domain. 

- Prover compute `h(x)` with `deg(h)=deg(f) - |H|`, and `p(x)` with `deg(p) < |H| - 1`, such that `f(x) = h(x)V_H(x) + (x*p(x) + claimed_sum/|H|)`. Prover send `h(x)` and `p(x)`, evaluated at evaluation domain. In this example, we simply use polynomial division algorithm defined in `ark-poly` but there'll be a lot of room to optimize if we want to use in production.
- Verifier sends **no** message in commit phase. 
- Verifier samples a random element `s` in evaluation domain, and queries `f(s)`, `h(s)`, `p(s)`, and computes `v_H(s)` locally. Then, it checks `f(s)` is equal to `h(s)*v_H(s) + (s*p(s) + claimed_sum/|H|)`
- LDT checks that `h(x)` enforces degree bound `deg(f) - |H|`; `p(x)` enforces degree bound `|H| - 2`. 

We will not go over proof of completeness and soundness for this protocol in this tutorial. Let's assume this protocol is correct. 

#### `prove`

Recall prover needs to write the prove function with the following signature: 

```rust
fn prove<MT: Config<Leaf = [F]>, S: CryptographicSponge>(
        namespace: &NameSpace,
        oracle_refs: &Self::RoundOracleRefs,
        public_input: &Self::PublicInput,
        _private_input: &Self::PrivateInput,
        transcript: &mut Transcript<MT, S, F>,
        prover_parameter: &Self::ProverParameter,
    ) -> Result<(), ark_bcs::Error> {
```

As a first step, prover can perform a sanity check to make sure the coefficients provided in prover parameter is consistent with the referenced oracle evaluation. 

```rust
// sanity check: `coeffs` in prover parameter matches the referenced oracle
let actual_eval = &transcript
    .get_previously_sent_prover_round(oracle_refs.poly)
    .reed_solomon_codes()[public_input.which]
    .0;
let expected_eval = prover_parameter
    .coeffs
    .clone()
    .evaluate_over_domain(prover_parameter.evaluation_domain)
    .evals;
assert_eq!(&expected_eval, actual_eval);
```

Then, we calculate `h(x)` and `p(x)` using basic polynomial division algorithm. 

```rust
let (hx, gx) = prover_parameter
            .coeffs
            .divide_by_vanishing_poly(prover_parameter.summation_domain)
            .unwrap();
let claim_sum_over_size = DensePolynomial::from_coefficients_vec(vec![
    public_input.claimed_sum / F::from(prover_parameter.summation_domain.size as u128),
]);
let x = DensePolynomial::from_coefficients_vec(vec![F::zero(), F::one()]);
let (px, r) = DenseOrSparsePolynomial::from(gx + (-claim_sum_over_size))
.divide_with_q_and_r(&DenseOrSparsePolynomial::from(x))
.unwrap();
// remainder should be zero
assert!(r.is_zero());
// degree bound information
let hx_degree_bound =
prover_parameter.degree - prover_parameter.summation_domain.size as usize;
println!("hx: degree {}, bound {}", hx.degree(), hx_degree_bound);
let px_degree_bound = prover_parameter.summation_domain.size as usize - 2;
println!("px: degree {}, bound {}", px.degree(), px_degree_bound);
```

Then, prover can add those two polynomial as oracles going to be sent in current round. 

```rust
transcript.send_univariate_polynomial(hx_degree_bound, &hx)?;
transcript.send_univariate_polynomial(px_degree_bound, &px)?;
```

The backend will automatically turns the coefficients to evaluations on evaluation domain. Transcript will get the evaluation domain from LDT parameter passed in to BCS, and it's caller's responsibility to make sure evaluation domain in parameter is consistent with evaluation domain in LDT. The protocol will fail otherwise. 

Then don't forget to submit this round! We can add a `&'static str` in `iop_trace!` here to help us debugging. When backend found something strange, it will this string and line number of the `iop_trace!` macro for assistance. 

```rust
transcript.submit_prover_current_round(namespace, iop_trace!("sumcheck hx, px"))?;
}
```

#### `restore_from_commit_phase`

Verifier needs to implement two functions, and one of them is `restore_from_commit_phase`. `restore_from_commit_phase` simulates interaction with prover, using the succinct proof. You can think this as the "`prove` code", but all prover message is already given for you.  All you need to do, is to replay the interaction and sample verifier message in commit phase as needed. For simple sumcheck example, let's start with function signature: 

```rust
fn restore_from_commit_phase<MT: Config<Leaf = [F]>>(
        namespace: &NameSpace,
        transcript: &mut SimulationTranscript<MT, S, F>,
        verifier_parameter: &Self::VerifierParameter,
    ) where
        MT::InnerDigest: Absorb,
    {
```

The verifier will tell the transcript that prover will send a message with a certain degree at this time, in code: 

```rust
let hx_degree_bound =
    verifier_parameter.degree - verifier_parameter.summation_domain.size as usize;
let px_degree_bound = verifier_parameter.summation_domain.size as usize - 1;
let expected_round_info = ProverRoundMessageInfo {
    num_message_oracles: 0,
    reed_solomon_code_degree_bound: vec![hx_degree_bound, px_degree_bound],
    oracle_length: verifier_parameter.evaluation_domain.size(),
    num_short_messages: 0,
    localization_parameter: 0, // ignored
};
```

Similar to `libiop`, In `ark-bcs` implementation, the backend will serialize a message into a number of cosets where each coset is encoded into a leaf. Doing so can greatly improve performance if verifier query is structured. `localization_parameter` is the size of each coset. Note that `localization_parameter` can be any arbitrary value here because we are sending an oracle with degree bound: in this case LDT will automatically manage the localization parameter. If current round contains only oracles without degree bound, then `localization_parameter` is meaningful. 

Again, remember to "submit" this round: 

```rust
transcript.receive_prover_current_round(
            namespace,
            expected_round_info,
            iop_trace!("sumcheck hx, px"),
        );
```

#### `query_and_decide`

In `query_and_decide` phase, verifier has oracle access to all prover messages sent in the transcript in commit phase, and access to all verifier messages (verifier messages from current protocol, and verifier messages from other protocols, using reference). Again, let's start with function signature

```rust
fn query_and_decide<O: RoundOracle<F>>(
    namespace: &NameSpace,
    verifier_parameter: &Self::VerifierParameter,
    public_input: &Self::PublicInput,
    oracle_refs: &Self::OracleRefs, /* in parent `query_and_decide`, parent can fill out
                                     * this `oracle_refs` using the message in current
                                     * protocol */
    random_oracle: &mut S,
    messages_in_commit_phase: &mut MessagesCollection<&mut O, VerifierMessage<F>>,
) -> Result<Self::VerifierOutput, Error> {
```

First, let define some useful variable here: 

```rust
let evaluation_domain = verifier_parameter.evaluation_domain;
let summation_domain = verifier_parameter.summation_domain;
let claimed_sum = public_input.claimed_sum;
let evaluation_domain_log_size = evaluation_domain.log_size_of_group;
```

Then, let's use the built in sponge to sample a random element in evaluation domain: 

```rust
let query: usize = random_oracle
    .squeeze_bits(evaluation_domain_log_size as usize)
    .into_iter()
    .enumerate()
    .map(|(k, v)| (v as usize) << k)
    .sum::<usize>();
let query_point: F = evaluation_domain.element(query);
```

Next, let query `h(s)`and`p(s)`. Adding `iop_trace!` here can help us debugging in case something does wrong. 

```rust
let queried_points = messages_in_commit_phase
    .prover_message(namespace, 0)
    .query(&[query], iop_trace!("sumcheck query"))
    .pop()
    .unwrap();
let h_point = queried_points[0];
let p_point = queried_points[1];
```

We can calculate `V_H(s)` locally: 

```rust
let vh_point = summation_domain
    .vanishing_polynomial()
    .evaluate(&query_point);
```

Then, we can query `f(s)`. We can pass `oracle_refs.poly` to `messages_in_commit_phase` to get a reference to the oracle of `f`. 

```rust
let expected = messages_in_commit_phase.prover_message_using_ref(oracle_refs.poly).query(&[query], iop_trace!("oracle access to poly in sumcheck"))
    .remove(0)// there's only one query, so always zero
    .remove(public_input.which); // we want to get `which` oracle in this round
                                 // h(s) * v_h(s) + (s * p(s) + claimed_sum/summation_domain.size)
```

The result returned by query is a 2D vector. The first axis is the query index. Since we have only one query here, we can simply call`remove(0)` to get what we want. The second axis is the the oracle index in this round. Caller already specifies which oracle we are going to use in `public_input.which`. 

Finally, just check that  `f(s)` is equal to `h(s)*v_H(s) + (s*p(s) + claimed_sum/|H|)`

```rust
let actual: F = h_point * vh_point
            + (query_point * p_point + claimed_sum / F::from(summation_domain.size as u128));
return Ok(expected == actual);
}
```

**Well done!** You got it! You now learned how to construct a univariate sumcheck protocol using `ark-bcs`. Now let's start implementing out main protocol using sumcheck as a subroutine. 

*Notice that univariate sumcheck is, indeed, a public coin PCP. But our main toy example will become an IOP.*

## Build Main Protocol

TODO

## Put it together: Proof Generation

TODO
