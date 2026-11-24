# To Mock a Mockingbird, in Lean

A Lean 4 formalization of Raymond Smullyan's wonderful [*To Mock a Mockingbird*](https://en.wikipedia.org/wiki/To_Mock_a_Mockingbird).

My motivation and aims:
- Experiment and have fun with Lean.
- Have fun with Smullyan's puzzles.
- Make a highly readable formalization.

The formalization starts where the birds do: at chapter 9.

How far it goes, nobody knows.

Build with `lake build`.

# Extras

Results that go beyond the book.

## The shortest egocentric lark

[`Mockingbird/Extras/ShortestEgocentricLark.lean`](Mockingbird/Extras/ShortestEgocentricLark.lean)

In chapter 9, Smullyan shows that a forest with a lark L (`L x y = x (y y)`) must contain an
egocentric bird (`E E = E`), and that one can write it using only the letter L and
parentheses. His shortest expression has 12 L's, and he asks:

> Can you find a shorter expression than mine that works? Can it be proved that there is no
> shorter expression in L that works? I don't know!

In 1986, Glickfeld and Overbeek (not me, another Overbeek) found an expression with 8 L's using an
automated theorem prover, and left open whether an even shorter one exists.

This file proves:

**Proposition.** No expression with at most 7 L's names an egocentric bird in every forest that
contains a lark.

Together with Glickfeld and Overbeek's solution, this shows that the shortest solution has
exactly 8 L's.

I could not find this answer written down anywhere. If you know of a source, please let me know.
