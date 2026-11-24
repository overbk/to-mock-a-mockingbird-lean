/-!
# No egocentric lark expression has fewer than 8 L's

**This file is self-contained: it does not import the rest of the project.**

In Chapter 9 of

- R. Smullyan. To Mock a Mockingbird, and Other Logic Puzzles.
  Alfred A. Knopf, New York, 1985.

Smullyan defines

- an *egocentric bird* E as a combinator satisfying `E E = E` (i.e., E is its own fixed point); and
- a *lark* L as a combinator satisfying `L x y = x (y y)` for all x and y.

In Problem 29 of Chapter 9, he writes:

> Suppose we are given that the forest contains a lark L and we are not given any other
> information. From just this one fact alone, it can be proved that at least one bird in the
> forest must be egocentric!
>
> The proof of this is a bit tricky. Given the lark L, we can actually write down an expression
> for an egocentric bird—and we can write it using just the letter L, with parentheses, of
> course. The shortest expression that I have been able to find has a length of 12, not counting
> parentheses. That is, we can write L twelve times and then by parenthesizing it the right way,
> have the answer. Care to try it? Can you find a shorter expression than mine that works? Can it
> be proved that there is no shorter expression in L that works? I don't know! At any rate, see
> if you can find an egocentric bird, given the bird L.

The solution of length 12 that Smullyan provides is: `((L(LL))(L(LL)))((L(LL))(L(LL)))`.

One year later Glickfeld and Overbeek (NB: Ross Overbeek, not the present author) presented a
length 8 solution `LL(L(LL))(L(LL))` in:

- B. Glickfeld and R. Overbeek. A foray into combinatory logic.
  Journal of Automated Reasoning 2(4):419–431, 1986. doi:10.1007/BF00248251

They left open whether an even shorter solution exists.

I am now writing in 2026, and I still can't find a publicly available answer that settles this.
I also checked some of the papers that cite B. Glickfeld and R. Overbeek. According to Claude,
the solution likely follows by combining results from:

- R. Statman. The word problem for Smullyan's lark combinator is decidable.
  Journal of Symbolic Computation 7(2):103–112, 1989. doi:10.1016/S0747-7171(89)80044-6
- M. Sprenger and M. Wymann-Böni. How to decide the lark.
  Theoretical Computer Science 110(2):419–432, 1993. doi:10.1016/0304-3975(93)90015-L

But I did not verify Claude's claim (forgive me, reader, for I am but a hobbyist these days).

I asked Claude Opus 5.5 to solve the problem and formalize it in Lean. It quickly came up with the
answer.

**Proposition** (`no_egocentric_lark_expression_below_eight`). No expression with at most 7 L's
names an egocentric bird in every forest that contains a lark.

Together with Glickfeld and Overbeek's solution, this shows that the shortest solution has exactly
8 L's. Below is the proof, only slightly polished by me after it was generated.

The proof idea: a solution must name an egocentric bird in *every* forest with a lark.
So one forest with a lark in which the expression names a bird that is not egocentric
rules that expression out. The proof gives one forest of six birds that rules out
every expression with at most 7 L's at once.
-/
namespace ShortestEgocentricLark

/-! ## 1. Definitions -/

/-! ### Forests and birds, as in chapter 9 -/

/-- A forest: a type of birds with a response operation.
Or: a magma. -/
class Forest (α : Type) where
  /-- `app x y` is x's response to y. -/
  app : α → α → α

-- Write `x y` for x's response to y. Left-associative: `x y z` = `(x y) z`.
instance {Bird : Type} [Forest Bird] : CoeFun Bird (fun _ => Bird → Bird) := ⟨Forest.app⟩

variable {Bird : Type} [Forest Bird]

/-- E is egocentric: E is fond of itself.
Or: E is its own fixed point. -/
def IsEgocentric (E : Bird) : Prop := E E = E

/-- L is a lark.
Or: `L x y = x (y y)`. -/
def IsLark (L : Bird) : Prop := ∀ A B : Bird, L A B = A (B B)

/-! ### Lark expressions -/

/-- A lark expression: a bird written with only the letter L and parentheses. -/
inductive LarkExpr where
  /-- The letter L. -/
  | L : LarkExpr
  /-- `app e f` is the expression `e f`: e's response to f. -/
  | app : LarkExpr → LarkExpr → LarkExpr

/-- The number of L's in an expression. -/
def LarkExpr.size : LarkExpr → Nat
  | .L => 1
  | .app e f => e.size + f.size

/-- The bird an expression names, when the letter L stands for the bird `L`. -/
def LarkExpr.eval (L : Bird) : LarkExpr → Bird
  | .L => L
  | .app e f => e.eval L (f.eval L)

/-- e solves Smullyan's puzzle: in every forest, for every lark L,
the bird e names is egocentric. -/
def SolvesLarkPuzzle (e : LarkExpr) : Prop :=
  ∀ (Bird : Type) [Forest Bird] (L : Bird), IsLark L → IsEgocentric (e.eval L)

/-! ## 2. The countermodel

A forest of six birds `A, B, C, D, E, F` in which `A` is a lark. `E` is its only
egocentric bird, and no expression with at most 7 L's names `E`.

`rank x` is the price of bird `x`: a lower bound on the number of L's in an expression
naming `x`. It was computed by search and is only checked here, not trusted:
the letter L names the bird `A`, of price 1, and a response never costs more than
the two birds it comes from added together. So by induction, every expression has
at least as many L's as the price of the bird it names. `E` has price 8. -/

section SixBirds

/-- The six birds of the countermodel. -/
inductive SixBirds where
  | A | B | C | D | E | F
  deriving DecidableEq

open SixBirds

/-- One row of the table: a bird's responses to `A, B, C, D, E, F`, in that order. -/
def row (a b c d e f : SixBirds) : SixBirds → SixBirds
  | A => a | B => b | C => c | D => d | E => e | F => f

/-- Row x, column y holds x's response to y. -/
instance : Forest SixBirds where
  app
    --         A B C D E F
    | A => row B C B D F F
    | B => row C D F C F F
    | C => row D C F D F F
    | D => row B B C B C C
    | E => row C C C C E E
    | F => row C C E C E E

/-- The price of each bird: a lower bound on the number of L's needed to name it.

Computed outside Lean by relaxation, as in Bellman–Ford: start with price 1 for `A` and
price 8 for every other bird (8 is a cap meaning "8 or more"). Then, for every pair
`x y`, lower the price of `x y` to `price x + price y` whenever that is smaller. Repeat
until nothing changes. Since a response has two inputs instead of one, this is shortest
paths in a hypergraph: Knuth's "grammar problem" (1977).

The prices are the fewest L's needed, for example `B = A A`, `C = A (A A)`,
`D = A A A A`, `F = B C`.

Nothing here trusts the computation: `rank_app` and `rank_le_size` check the prices directly. -/
def rank : SixBirds → Nat
  | A => 1 | B => 2 | C => 3 | D => 4 | E => 8 | F => 5

theorem A_lark : IsLark A := by
  intro x y
  cases x <;> cases y <;> decide

theorem egocentric_is_E : ∀ x : SixBirds, x x = x → x = E := by
  intro x
  cases x <;> decide

theorem rank_app : ∀ x y : SixBirds, rank (x y) ≤ rank x + rank y := by
  intro x y
  cases x <;> cases y <;> decide

/-- An expression has at least as many L's as the price of the bird it names. -/
theorem rank_le_size (e : LarkExpr) : rank (e.eval A) ≤ e.size := by
  induction e with
  | L => exact Nat.le_refl 1
  | app e f e_rank f_rank =>
    have := rank_app (e.eval A) (f.eval A)
    simp only [LarkExpr.eval, LarkExpr.size]
    omega

end SixBirds

/-! ## 3. The result -/

/-- No expression with at most 7 L's solves Smullyan's lark puzzle.
Or: the shortest egocentric lark expression has at least 8 L's. -/
theorem no_egocentric_lark_expression_below_eight (e : LarkExpr)
    (e_short : e.size ≤ 7) :
    ¬ SolvesLarkPuzzle e := by
  intro e_solves
  -- In the six-bird forest, e names E, which costs 8 L's.
  have names_E := egocentric_is_E _ (e_solves SixBirds .A A_lark)
  have rank_le := rank_le_size e
  rw [names_E] at rank_le
  change 8 ≤ e.size at rank_le
  omega

end ShortestEgocentricLark
