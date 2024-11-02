# project-euler-lambda

This repository explores how painful it is to program directly in the pure
lambda calculus.

## Why?

* Mainstream programming languages are incredibly complicated, which makes it
  hard to provide nice tooling for them.  I hope to be able to build tooling for
  the pure Lambda Calculus all on my own (of course any help would be much
  appreciated).

* It seems to be implicitly assumed that the Lambda Calculus is not suitable to
  use in anger , but it is difficult for me to point to concrete evidence for
  this. Hence, I decided to try it out and see what bugs me.

## Which Lambda Calculus?

There are many different variations of lambda calculus, so it is fair to ask
which Lambda Calculus I am using.

* We embed into Haskell, so we need to deal with Haskell's type system, which is
  based on System F. Using newtypes and higher rank types, we can write any
  untyped Lambda Calculus program in Haskell (in particular, we can define the Y
  combinator).

* While writing these programs, I actually found this type system pleasant to
  use, so perhaps System F + newtypes will be the language that I choose.

## How do you do I/O?

* We currently use an embedding of lambda calculus in Haskell, so it is easy to
  convert from Haskell types to Lambda Calculus values and back.

* In the future, I would like to make a standalone Lambda Calculus language. In
  that case, an option might be to wire the lambda calculus values to a C
  wrapper program.

* It is very important that all this wiring remains simple. Otherwise, we could no
  longer claim that all programs are written in pure lambda calculus.

* In the future, I would like to go beyond Project Euler problems and write real
  interactive programs like games or other apps. Then the I/O problem will be much
  more obvious and it will be harder to keep the wrapper as simple as possible. A good
  rule of thumb is perhaps that we want the Lambda Calculus to be the language we
  program in. The wrapper should not require frequent changes.
