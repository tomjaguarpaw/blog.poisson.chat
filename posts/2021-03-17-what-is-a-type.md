---
title: What is a type?
keywords: [theory, misc]
---

My fascination for types rivals my inability to define the concept.

Even though I don't know what a type is, I can still recognize when a paper "is
about types": the paper usually contains many occurrences of formulas of the form
"`t : T`", where "`t`" is some piece of code, some program, and "`T`" is one of
these mysterious types. The colon in the middle is of no technical
significance, but it signals some cultural awareness on the part of authors.

Hypothesis: Types are a meme.

My experience is also that things are very very bad when "`t : T`" does not hold.
Types are a way to tell right from wrong, for some domain-specific definitions
of correctness.

Hypothesis: Types are specifications.

One idea that really narrows it down for me is that programming languages have
types. You can assign types to everything in a language: static types to source
code, dynamic types to run-time values.

Another way to look at this is to compare with other forms of specifications. How
do you prove a specification? A priori, you could use any method, and all you
care about is that it is somehow "sound", but otherwise the proof method is
a black box.

- Automated theorem proving, with an SMT solver as a black box.
- Interactive theorem proving, with PhD students as a black box.
- Testing, with the compiler/interpreter as a black box.[^sound]

[^sound]: Whereas most formal methods are sound for proving the absence
of certain bugs, testing is a sound method of finding bugs.

Approaches using "types" seem different. To prove a specification, a typing
judgement "`t : T`", the way forward is to prove more typing judgements by
following the rules of some "type system". Types tell me both "how to specify
things" and "how to verify things"---by specifying and verifying sub-things.

Hypothesis: Types are compositional specifications.

---

I originally posted this question on the recently created
[TYPES Zulip server](https://typ.zulipchat.com/#narrow/stream/279113-general/topic/What.20is.20a.20type.3F),
a spin-off of the [TYPES mailing list](https://lists.seas.upenn.edu/mailman/listinfo/types-list).
Those are nice hangouts for people who like types, whatever you believe they
are (and also for getting spammed with Calls-For-Papers).
