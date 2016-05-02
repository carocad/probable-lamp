# kangaroo

A Clojure library designed to follow a basic implementation of regular expressions
*without backtracking* using [Thompson's contruction](https://en.wikipedia.org/wiki/Thompson's_construction) algorithm.

Inspired by Russ Cox blog post on [simple and fast regular expressions](https://swtch.com/~rsc/regexp/regexp1.html).

## Usage

Unlinke normal regular expressions, and using Clojure's powerful functional programming, this library is more oriented towards sequences, thus allowing a great flexibility of use through the use of functions. For example:

```Clojure
; use kangaroo.core
(def foo (alt (rep+ string?) list? map?))
```
would match all sequences that contains either: one or more string, one list or one map. To check if a given sequence match the regular expression simply run:
```Clojure
(exec foo '("hello" (a b) "world"))
; {:match false, :msg "Expected any of: string?; instead got: (() \"world\")"}
```
probable-lamp uses the name of the provided function to feedback a message with the expected input, plus a boolean with the final matching state.

**NOTE:** The implementation is extremely simple but very flexible such that you could implement a particular regular language on top of it. Regular expressions can be seen simply as an specific case of regular languages. Thus it could be implemented on top of this library.

## License

Copyright © 2016 Camilo Roca

Distributed under the LGPL v3.
