agda-stuff
==========
Just learning/playing with it.

bytesCount
----------
Calculates amount of bits (`bitsRequired`) or bytes (`bytesRequired`)
required to represent a given number. Uses Agda version 2.3.2.2 and
lib-0.7.

 Proven properties:

- `bitsRequiredIsEnough : ∀ n → BitsEnough (bitsRequired n) n`
- `bitsRequiredNotExcessive : ∀ n m → n > 0 → m < (bitsRequired n) → ¬ BitsEnough m n`
- `bytesRequiredIsEnough : ∀ n → bytesEnough (bytesRequired n) n`
- `bytesRequiredNotExcessive : ∀ n → 0 < n → ¬ (bytesEnough (bytesRequired n ∸ 1) n)`

where `BitsEnough` is defined as `∀ (bits for : ℕ) → for < (2 ^ bits)
→ BitsEnough bits for`, and `bytesEnough` is defined as `BitsEnough
(bytes * 8) for`

Formatting could be appaling, as well as some other aspects; I'm still
learning Agda, and never wrote such things before, except for
exercises.

Tree
----
A property-preserving tree structure: keeps a given relation between
every node and its subtrees. Uses Agda 2.3.3 (dev, almost 2.3.4).

No properties proven yet, though it'd be nice to prove that it does
not throw away nodes which shouldn't be thrown away.

Markov
------
Markov algorithm, just a quick implementation.
