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

TODO

## Build Main Protocol

TODO

## Put it together: Proof Generation

TODO
