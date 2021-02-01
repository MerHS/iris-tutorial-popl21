# The Iris tutorial @ POPL'21

This tutorial comes in two versions:

- The folder `exercises`: skeletons of the exercises with parts left `admit`ted.
- The folder `solutions`: the exercises together with their solutions.

The slides for the tutorial's lecture component are at [talks/iris-popl21-tutorial.pdf](talks/iris-popl21-tutorial.pdf).
You can also watch the [recording of this talk from POPL'21](https://www.youtube.com/watch?v=LjXaffBpMag).

The Coq demo source is in [demo.v](talks/demo/demo.v).

The tutorial material is based on the earlier [POPL 2018 tutorial](https://gitlab.mpi-sws.org/iris/tutorial-popl18/) by Robbert Krebbers and Jacques-Henri Jourdan.

## Chat

For help with this tutorial, you can join the [POPL2021 Tutorial channel](https://mattermost.mpi-sws.org/iris/channels/popl2021-tutorial) on the MPI-SWS Mattermost.
To log in, you need to [create an MPI-SWS GitLab account](https://gitlab.mpi-sws.org/users/sign_up), either by logging in via GitHub or by registering a new account.

## Dependencies

For the tutorial material you need to have the following dependencies installed:

- Coq 8.12.2 or 8.13.0
- A development version of [Iris](https://gitlab.mpi-sws.org/iris/iris)

*Note:* the tutorial material will not work with earlier or later versions of
Iris, it is important to install the exact versions as described below.

### Installing Iris via opam

The easiest, and recommend, way of installing Iris and its dependencies is via
the OCaml package manager opam (2.0.0 or newer). After
[installing opam](https://opam.ocaml.org/doc/Install.html), you first have to
add the Coq opam repository and the Iris development repository (if you have not
already done so earlier):

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git

Once you have opam set up, run `make build-dep` to install the right versions
of the dependencies.

To update, do `git pull`.  After an update, the development may fail to compile
because of outdated dependencies.  To fix that, please run `opam update`
followed by `make build-dep`.

### Installing Iris without opam (not recommended)

You can also install Iris without opam, but this will increase the risk of build
failures due to incompatibilities.  Assuming you already have an appropriate
version of Coq installed, you need to install both std++ and Iris:

* Clone [std++](https://gitlab.mpi-sws.org/iris/stdpp/), then run `make -jN && make install`
  (where `N` is the number of CPU cores you wish to use for the build).
* Clone [Iris](https://gitlab.mpi-sws.org/iris/iris/), then run `make -jN && make install`.

We usually make sure that the latest commits of std++, Iris, and the tutorial
work together, but sometimes they can be temporarily broken.  The versions
installed via opam are always guaranteed to work.

## Working on the exercises

To work on the exercises, simply edit the files in the `exercises/` folder. Some
proofs in these files are admitted and marked as `(* exercise *)`; your task is
to complete those proofs all the way to a `Qed`.

After you are done with a file, run `make` to compile and check the
exercises. You need to have exercise 3 compiled to work on exercise 5.

If you are stuck, you can find solutions in the corresponding file in the
`solutions/` folder.

## Documentation

The files [`proof_mode.md`] and [`heap_lang.md`] in the Iris repository contain a
list of the Iris Proof Mode tactics as well as the specialized tactics for
reasoning about HeapLang programs.

[`proof_mode.md`]: https://gitlab.mpi-sws.org/iris/iris/blob/master/docs/proof_mode.md
[`heap_lang.md`]: https://gitlab.mpi-sws.org/iris/iris/blob/master/docs/heap_lang.md

If you would like to know more about Iris, we recommend to take a look at:

- [Lecture Notes on Iris: Higher-Order Concurrent Separation Logic](http://iris-project.org/tutorial-material.html)<br>
  Lars Birkedal and Aleš Bizjak<br>
  Used for an MSc course on concurrent separation logic at Aarhus University

- [Iris from the Ground Up: A Modular Foundation for Higher-Order Concurrent Separation Logic](https://www.mpi-sws.org/~dreyer/papers/iris-ground-up/paper.pdf)<br>
  Ralf Jung, Robbert Krebbers, Jacques-Henri Jourdan, Aleš Bizjak, Lars Birkedal, Derek Dreyer<br>
  A detailed description of the Iris logic and its model

## Generating the exercises

If you want to contribute to the tutorial, note that the files in `exercises/`
are generated from the corresponding files in `solutions/`. Run `make exercises`
to re-generate those files. This requires `gawk` to be installed (which should
usually be available on Linux, and on macOS can be installed with `brew install
gawk`).

The syntax for the solution files is as follows:
```
(* SOLUTION *) Proof.
  solution here.
Qed.
```
is replaced by
```
Proof.
  (* exercise *)
Admitted.
```
and the more powerful
```
(* BEGIN SOLUTION *)
  solution here.
(* END SOLUTION BEGIN TEMPLATE
  exercise template here.
END TEMPLATE *)
```
is replaced by
```
  exercise template here.
```
