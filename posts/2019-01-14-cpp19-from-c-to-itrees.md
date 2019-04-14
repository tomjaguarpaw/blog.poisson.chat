---
title: "From C to Interaction trees: Specifying, Verifying, and Testing a networked server (CPP 2019 talk transcript)"
keywords: [coq, formal verification, testing, itrees, VST, CertiKOS]
---

This is a transcript of my talk
at [CPP 2019](https://popl19.sigplan.org/track/CPP-2019)
(conference on Certified Programs and Proofs, co-hosted with POPL),
presenting our efforts towards verifying a networked server.

- To follow along:
  [`slides.pptx`](https://poisson.chat/cpp19/c-to-itrees-slides.pptx),
  [`slides.pdf`](https://poisson.chat/cpp19/c-to-itrees-slides.pdf).
- The paper is [on arXiv](https://arxiv.org/abs/1811.11911).
- Source code: [`swap_server.tgz`](https://poisson.chat/cpp19/swap_server.tgz).

---

DeepSpec
========

This work is part of [the *Expedition in the Science of Deep
Specification*](https://deepspec.org/main)
(DeepSpec). Led by four American universities (MIT, Yale, Princeton, Penn),
DeepSpec aims to develop techniques to verify whole systems.
DeepSpec encompasses many verification projects, and the work I'm going to
present today is the first step towards connecting them together to verify a
system from RFCs to transistors.

We will verify an application written in C using the [Verified
Software Toolchain](http://vst.cs.princeton.edu/) (VST for short).
It is a program logic for C, based on Hoare logic.
One important reason for using VST is that the properties we prove
are preserved by compilation with the CompCert compiler.
This verified application will run on a verified OS,
[CertiKOS](http://flint.cs.yale.edu/certikos/).
And all this software will run on hardware implemented and verified with
the [Kami](http://plv.csail.mit.edu/kami/) library.

Ultimately, we would like one theorem formalizing the correctness of the
complete system. The main challenge of the DeepSpec project is to connect these
components developed by different institutes to obtain such a unifying theorem.

Moreover, we would also like to make our specifications testable, as
a way to relate specifications to the real world. For that, we will use
[QuickChick](https://github.com/QuickChick/QuickChick/), a library for
*property-based testing*: that allows to formulate specifications as
automatically testable properties, producing concrete counterexamples
when they are not satisfied.

Especially in the context of verification, testing provides two benefits:

1. It can reveal bugs before proving, to gain confidence that the theorems being
   proved are indeed correct;

2. and it can make specifications applicable to other implementations in the wild,
   ensuring that our interpretation of informal documents such as
   [RFCs](https://en.wikipedia.org/wiki/Request_for_Comments)
   matches existing implementations. Implementations may also intentionally
   deviate from standard specifications, often for reasons related to
   performance or security.

A verified web server
---------------------

As a final demo of the Deep Specification project, we aim to verify an
HTTP server. By implementing such a widely used protocol we hope to show
the applicability of verification at an industrial scale.

But today, rather than a project as complex as an HTTP server, we will
instead focus on a simplified application. With this experiment we want to
illustrate at a small scale the challenges in integrating different components
to build a fully verified system.

And indeed, it still has the essential features allowing us to make
the following contributions:

- we verified a C program that talks over the network using VST,
  so that it can be compiled in a verified way and run in CertiKOS;

- and we made our specification testable: from it we can derive a test client,
  which can connect to a server, verified or not, and check whether it
  satisfies the specification.

---

Case study: Swap server
=======================

Let's see a simple example of what our server does.
A swap server exchanges messages with one or many clients,
and can store one message.

- When it receives a message, for example, `"Cat"` from client 1, the server
  stores it, and replies with the previously stored message
  `"Bat"` (an arbitrary initial message).

- Then, when it receives another message, for example, `"Dog"` from another
  client, it stores it and replies with the previously stored message, `"Cat"`.

- And so on.

It is like an "echo server", which repeats what it hears, but its responses
are shifted to the next exchange. The key motivation for the swap
server's behavior is to make the simplest example of a stateful server.

Networked swap server
---------------------

However, our server is implemented against a low-level socket interface.
This exposes a wide range of interactions that the previous specification
does not describe directly. The network, the hardware, and the OS can
buffer messages internally in various ways. For example, this leads to messages
being reordered, or delayed indefinitely.

These are behaviors that matter not only when we would run the server in
production, but also during testing.

Network refinement
------------------

To account for the network, we adapt notions of observational refinement
from the literature on concurrent and distributed systems.

The rough idea is to take a high-level specification of the server from
earlier, and through the semantics of the network, we can define the
observations that clients can make on the other side of the network.

In parallel, we also define the observable behavior of an implementation.
Then, the correctness property relating the implementation and the
specification is the inclusion of observable behaviors over the network,
which we call *network refinement*.

Proof architecture
------------------

Here is a picture summarizing our system. Starting from the bottom,
CertiKOS provides the environment to execute our server.

In particular, it provides a networking interface using sockets, against which
our server is implemented. The aim is to show that the implementation
respects the specification as illustrated in the previous slides.

First, we introduce an intermediate specification, the *implementation model*.
The toplevel specification is now called the *linear specification* to
distinguish those two forms of specifications.
The implementation model is a low-level description of the server's
interactions with the socket interface, describing for example how the server
buffers communications with many clients at the same time (whereas that kind of
details doesn't appear in the linear specification).

Using VST, we prove a *refinement* between the C program and the implementation
model. Then, we prove that the implementation model *network-refines* the
specification.

Of course, the fact that the C program refines the implementation model must
rely on some semantics of the socket interface, which we wrote down first using
VST.

Now, to relate the socket implementation to the VST specification,
we also started formalizing the interface in CertiKOS. The implementation
is however still not verified (thus we use a dashed arrow there in the diagram).
The bridge between VST and CertiKOS is work-in-progress (as shown by the dotted
line), and our paper gives a summary of our approach there.

As I said before, the long term goal of DeepSpec is to connect many components
together into a whole verified system. This comes with various challenges
that are already apparent in our simple experiment.

1. To describe the system at different abstraction levels.

2. To translate between varying specification styles already
in use by the existing tools.

3. To test the specification, both to reduce the engineering effort that will
   be required at a larger scale, and to be able to check whether our
   specification matches other existing implementations in the wild.

We propose *interaction trees* as a unifying structure to represent effectful
computations across our development while addressing those challenges.

---

Interaction trees (aka. *free monads*)[^1]
==========================================

[^1]: If you have a functor `F` and take its free monad `Free F`, its
     inhabitants are what we call *interaction trees* here.
     Furthermore, to actually get an free monad, you should make the `itree`
     type defined here inductive instead of coinductive.

Intuitively, a program interacting with the outside world can be described as a
tree, where nodes correspond to *effects* performed by the program, with
one branch for each possible result of that effect. In this example, the
program reads a bit, and if it is zero it goes to the left, if it is one
it goes to the right, and so on, and it may return some value as a final result.

We can define interaction trees with many different kinds of effects.
The simple example on the slide uses effects to read and write bits. Effects
can be easily defined for any particular application as a sum type,
whose constructors correspond to the effects that can be performed,
and the type index gives the result type of each effect.

Definition
----------

```coq
CoInductive itree (E : Type -> Type) (R : Type) : Type :=
| Vis : forall Y, E Y -> (Y -> itree E R) -> itree E R
| Ret : R -> itree E R
| Tau : itree E R -> itree E R
.
```

Programs such as web servers can run for indefinitely long,
so their interactions trees can be infinite.
This is why we declare the type of itrees to be coinductive.
It is parameterized by an effect type `E` and a result type `R`.

An itree can perform an *effect*, of type `E Y`, with a *continuation*
expecting a response of type `Y` from the environment.
We can see this as a node of type `E Y` whose arity is the cardinality of `Y`.

An itree can terminate, *returning* a result of type `R`.

An itree can take a silent step of internal computation, without any visible
effect. That last constructor is actually necessary to satisfy Coq's
guardedness condition when constructing nontrivial infinite trees.

To come back to the initial point,
itrees provide a general-purpose representation that can be used
at different abstraction levels and that seems compatible with many
existing verification frameworks.
At the same time since it is a simple coinductive type,
so it can be easily extracted for testing.

=== Swap server: linear specification

Here is the linear specification of a swap server, as an interaction tree
defined in Coq.
It is a recursively defined itree parameterized by a set of open connections
and the contents of the store, first nondeterministically choosing a connection
`c`, receiving a `new_msg` from it, and sending back the `last_msg` from the
store, before looping again with the `new_msg` in the store.
Since it is defined monadically, it looks almost like a reference
implementation, except for the nondeterminism at the top.

The implementation model is also an itree, but more complex since
it reflects the C program's logic of buffering and interleaving
exchanges on multiple connections.

---

Refinement in VST
=================

The other half of the proof is to show that the behavior of the C program
is contained in the behavior of the implementation model, using
VST's logic. VST is a Hoare-style logic for C programs: specifications
are given as pre- and postconditions on the program's memory.
Perhaps surprisingly, the implementation model appears in the precondition,
as part of an `ITree` predicate. The idea is that it describes the interactions
that are initially *allowed* by the external environment. A valid program under
this precondition is one that follows those allowed behaviors.

When the program performs an effect corresponding to a node in the allowed itree,
that itree gets replaced by the branch associated with the result of the
effect.
Here you can see a more concrete example of a C program allowed to perform
a `recv()`, a `send()`, followed by effects described by the itree `t`.

```
{ ITree(msg <- Recv c ;; (* Coq *)
        Send c msg ;;
        t) * ... }

  recv(c, buf, len); // C
  send(c, buf, len);

{ ITree(t) * ... (* Coq *) }
```

The top-level correctness theorem
=================================

We can now state the theorem formalizing the correctness of our server which we
proved. It relates the C program to the high-level linear
specification as follows. The *refinement* relation I just described provides a
*model* of the C program's use of the socket interface as an itree.
This implementation model is existentially quantified:
it is a detail of the proof, rather than the toplevel specification.
Finally, we show that the implementation model network-refines the linear
specification: seen from across the network, the observable behavior of the
former is included in that of the latter.

```coq
Theorem correct_server :
  exists impl_model,
            refines C_prog impl_model /\
    network_refines impl_model linear_spec.
```

---

Next steps
==========

All this is only the first step of our project. There is a lot more work
needed to apply the lessons we learned to a full HTTP server.

In the swap server we only talked to the socket interface.
We will soon need to tackle the question of composing more systems together,
such as a filesystem or a cryptographic library. The flexibility
of itrees seems particularly well-suited to this kind of composition.

The development of the swap server tested the limits of VST, motivating some
new features to model external effects, and there is certainly more work
to make the integration with CertiKOS smoother.

We currently have a quite simplistic model of the network.
We are certainly interested in techniques that will allow us to scale up,
towards more complicated servers that talk to more realistic networks.

Speaking of interaction trees, we are working on putting together a general
purpose library of itrees. At the moment our focus is on how to use paco to
make coinduction compose better.

Thanks for listening/reading!
