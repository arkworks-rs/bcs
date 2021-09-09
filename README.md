<h1 align="center">arkworks::bcs</h1>

<p align="center">
    <a href="https://github.com/arkworks-rs/sponge/blob/master/LICENSE-APACHE">
        <img src="https://img.shields.io/badge/license-APACHE-blue.svg"></a>
    <a href="https://github.com/arkworks-rs/sponge/blob/master/LICENSE-MIT">
        <img src="https://img.shields.io/badge/license-MIT-blue.svg"></a>
</p>

`ark-bcs` is a Rust library that provides implementations of public coin RS-IOP and BCS Transform. This library is released under the MIT License
and the Apache v2 License (see [License](#license)).

**WARNING:** This is an academic prototype, and in particular has not received careful code review.
This implementation is NOT ready for production use.

## Overview

An RS-IOP is an interactive protocol where prover can send message oracles with degree bound. 
This library provides an interface of public coin RS-IOP protocol, an efficient implementation of LDT to enforce degree bound, and a BCS transformation algorithm to convert RS-IOP to non-interactive proof. 

Also, this implementation uses public-coin IOP assumption that all verifier messages are sampled uniformly at random, and all verification logic can be delayed to query and decision phase. 

This implementation differs from [BCS Paper](https://eprint.iacr.org/2016/116) in several aspects: 
- Instead of explicitly using a hash chain, this implementation uses `CryptographicSponge` in [`ark-sponge`](https://github.com/arkworks-rs/sponge/) as random oracle.
- This implementation has low-degree test built-in, and can handle RS-IOP.  
- Multiple oracles with same evaluation domain share a merkle tree and be submitted in one round, which greatly reduces verification overhead and number of constraints. 
- Each leaf of an low-degree oracle is a coset instead of an individual field element, which significantly reduces merkle tree overhead on FRI query. 

## Build Guide

The library compiles on the `stable` toolchain of the Rust compiler. To install the latest version
of Rust, first install `rustup` by following the instructions [here](https://rustup.rs/), or via
your platform's package manager. Once `rustup` is installed, install the Rust toolchain by invoking:
```bash
rustup install stable
```

After that, use `cargo` (the standard Rust build tool) to build the library:
```bash
git clone https://github.com/arkworks-rs/bcs.git
cd bcs
cargo build --release
```

This library comes with some unit and integration tests. Run these tests with:
```bash
cargo test
```


## License

This library is licensed under either of the following licenses, at your discretion.

* [Apache License Version 2.0](LICENSE-APACHE)
* [MIT License](LICENSE-MIT)

Unless you explicitly state otherwise, any contribution that you submit to this library shall be
dual licensed as above (as defined in the Apache v2 License), without any additional terms or
conditions.

## Reference papers

[Aurora: Transparent Succinct Arguments for R1CS][bcrsvw19]<br>
Eli Ben-Sasson, Alessandro Chiesa, Michael Riabzev, Nicholas Spooner, Madars Virza, Nicholas P. Ward

[Fast Reed-Solomon Interactive Oracle Proofs of Proximity][bbhr17]<br>
Eli Ben-Sasson, Iddo Bentov, Ynon Horesh, Michael Riabzev

[Interactive Oracle Proofs][bcs16]<br>
Eli Ben-Sasson, Alessandro Chiesa, Nicolas Spooner



[bcs16]: https://eprint.iacr.org/2016/116
[bcrsvw19]: https://eprint.iacr.org/2018/828
[bbhr17]: https://eccc.weizmann.ac.il/report/2017/134/
