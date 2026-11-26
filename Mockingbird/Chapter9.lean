/-!
# Chapter 9: To Mock a Mockingbird
-/
namespace Chapter9

/-! ## To Mock a Mockingbird -/

-- Intro material. Not stated by Smullyan in the scope of a problem.

/-- A forest: a type of birds with a response operation. Mathematically, a magma. -/
class Forest (α : Type) where
  /-- `app x y` is x's response to y. -/
  app : α → α → α

variable {Bird : Type} [Forest Bird]

-- Write `x y` for x's response to y. Left-associative: `x y z` = `(x y) z`.
instance : CoeFun Bird (fun _ => Bird → Bird) := ⟨Forest.app⟩

-- Display `Forest.app x y` as `x y` in goals.
@[app_unexpander Forest.app]
private def Forest.unexpandApp : Lean.PrettyPrinter.Unexpander
  | `($_app $x $y) => `($x $y)
  | _ => throw ()

/-- A is fond of B.
Or: B is a fixed point for A. -/
def IsFondOf (A B : Bird) : Prop := A B = B

/-- M is a mockingbird.
Or: M is the ω = λx.xx of lambda calculus. -/
def IsMockingbird (M : Bird) : Prop := ∀ x : Bird, M x = x x

/-- AB composes A with B.
Or: AB is the composition of A after B. -/
def Composes (AB A B : Bird) : Prop := ∀ x : Bird, AB x = A (B x)

/-! ### Problem 1 -/

-- C₁: for any A and B there exists a bird composing A with B.
-- Or: the forest is closed under composition.
variable (exists_composition : ∀ A B : Bird, ∃ AB : Bird, Composes AB A B)
-- C₂: the forest contains a mockingbird M.
variable {M : Bird} (m_mimics : IsMockingbird M)

include exists_composition m_mimics in
/-- Problem 1: Every bird is fond of at least one bird.
Or: Every element has a fixed point. -/
theorem every_bird_is_fond (A : Bird) :
    ∃ B : Bird, IsFondOf A B := by
  -- Define AM:
  --                ┌──────── AM ────────┐
  --  A (x x)  ◀──  │  A  ◀── x x ◀── M  │  ◀──  x
  --                └────────────────────┘
  --
  -- Feed AM to itself.
  --                ┌──────── AM ──────────┐
  --  A (AM AM) ◀── │  A  ◀── AM AM ◀── M  │  ◀── AM
  --                └──────────────────────┘
  --
  -- What does AM respond to AM?
  -- 1. Trivially, AM AM.
  -- 2. By running the box, A (AM AM).
  -- Hence A (AM AM) = AM AM.
  obtain ⟨AM, am_comp⟩ := exists_composition A M
  exists AM AM
  calc
    A (AM AM) = A (M AM) := by rw [m_mimics AM]
    _ = AM AM := (am_comp AM).symm

/-! ### Problem 2 -/

/-- E is egocentric.
Or: E is its own fixed point. -/
def IsEgocentric (E : Bird) : Prop := IsFondOf E E

include exists_composition m_mimics in
/-- Problem 2: At least one bird is egocentric.
Or: Some element is its own fixed point. -/
theorem exists_egocentric :
    ∃ A : Bird, IsEgocentric A := by
  -- By problem 1 with A := M, M is fond of some B:
  --      B  ◀── M ◀── B
  -- M is a mockingbird:
  --    B B  ◀── M ◀── B
  -- What does M respond to B? Two answers, so B B = B.
  obtain ⟨B, m_fond_b⟩ := every_bird_is_fond exists_composition m_mimics M
  exists B
  calc
    B B = M B := (m_mimics B).symm
    _ = B := m_fond_b

/-! ### Problem 3 -/

/-- A and B agree on C.
Or: C is a coincidence point of A and B. -/
def AgreeOn (A B C : Bird) : Prop := A C = B C

/-- A is agreeable: it agrees with every bird on some bird.
Or: A has a coincidence point with every bird. -/
def IsAgreeable (A : Bird) : Prop :=
  ∀ B : Bird, ∃ C : Bird, AgreeOn A B C

include exists_composition in
/-- Problem 3: Given composition and an agreeable bird, every bird is fond of at least one bird. -/
theorem every_bird_is_fond_alternative {G : Bird}
    (g_agreeable : IsAgreeable G)
    (A : Bird) :
    ∃ B : Bird, IsFondOf A B := by
  -- Define AG:
  --                ┌──────── AG ────────┐
  --  A (G x)  ◀──  │  A  ◀── G x ◀── G  │  ◀──  x
  --                └────────────────────┘
  --
  -- G is agreeable, so G and AG agree on some C:
  --                ┌──────── AG ────────┐
  --  A (G C)  ◀──  │  A  ◀── G C ◀── G  │  ◀──  C
  --                └────────────────────┘
  --      G C  ◀──            G             ◀──  C
  --
  -- What does AG respond to C?
  -- 1. By agreement with G, G C.
  -- 2. By running the box, A (G C).
  -- Hence A (G C) = G C.
  obtain ⟨AG, ag_comp⟩ := exists_composition A G
  obtain ⟨C, g_ag_agree⟩ := g_agreeable AG
  exists G C
  calc
    A (G C) = AG C := (ag_comp C).symm
    _ = G C := g_ag_agree.symm

include m_mimics in
/-- Problem 3, bonus: Mockingbirds are agreeable.
Or: ω has a coincidence point with every bird. -/
theorem mockingbirds_are_agreeable :
    IsAgreeable M := by
  intro B
  exact ⟨B, m_mimics B⟩

/-! ### Problem 4 -/

include exists_composition in
/-- Problem 4: If AB composes A with B and AB is agreeable, then A is agreeable.
Or: If A after B has a coincidence point with every bird, so does A. -/
theorem agreeability_is_inherited {A B AB : Bird}
    (ab_comp : Composes AB A B)
    (ab_agreeable : IsAgreeable AB) :
    IsAgreeable A := by
  intro D
  -- AB is first B, then A.
  --                ┌──────── AB ────────┐
  --  A (B x)  ◀──  │  A  ◀── B x ◀── B  │  ◀──  x
  --                └────────────────────┘
  --
  -- Build DB:
  --                ┌──────── DB ────────┐
  --  D (B x)  ◀──  │  D  ◀── B x ◀── B  │  ◀──  x
  --                └────────────────────┘
  --
  -- AB is agreeable, so on some E both boxes give the same output:
  -- A (B E) = D (B E). Thus A and D agree on B E.
  obtain ⟨DB, db_comp⟩ := exists_composition D B
  obtain ⟨E, ab_db_agree⟩ := ab_agreeable DB
  exists B E
  calc
    A (B E) = AB E := (ab_comp E).symm
    _ = DB E := ab_db_agree
    _ = D (B E) := db_comp E

/-! ### Problem 5 -/

include exists_composition in
/-- Problem 5: For any A, B, and C there exists a bird D with D x = A (B (C x)). -/
theorem three_composition (A B C : Bird) :
    ∃ D : Bird, ∀ x : Bird, D x = A (B (C x)) := by
  obtain ⟨BC, bc_comp⟩ := exists_composition B C
  obtain ⟨ABC, abc_comp⟩ := exists_composition A BC
  exists ABC
  intro y
  calc
    ABC y = A (BC y) := abc_comp y
    _ = A (B (C y)) := by rw [bc_comp y]

/-! ### Problem 6 -/

/-- A and B are compatible: for some x and y, A responds to x with y and B responds to y with x. -/
def AreCompatible (A B : Bird) : Prop := ∃ (x y : Bird), A x = y ∧ B y = x

/-- Compatibility without the intermediate bird: A and B are compatible iff B (A x) = x for some x.
This is a step in Smullyan's solution to problem 6, pulled out as its own lemma. -/
theorem are_compatible_iff {A B : Bird} :
    AreCompatible A B ↔ ∃ x : Bird, B (A x) = x := by
  constructor
  · intro ⟨C, D, ac_d, bd_c⟩
    exists C
    calc
      B (A C) = B D := by rw [ac_d]
      _ = C := bd_c
  · intro ⟨C, bac_c⟩
    exact ⟨C, A C, rfl, bac_c⟩

include exists_composition m_mimics in
/-- Problem 6: Any two birds are compatible. -/
theorem all_birds_are_compatible (A B : Bird) :
    AreCompatible A B := by
  rw [are_compatible_iff]
  obtain ⟨BA, ba_comp⟩ := exists_composition B A
  obtain ⟨C, ba_fond_c⟩ := every_bird_is_fond exists_composition m_mimics BA
  exists C
  calc
    B (A C) = BA C := (ba_comp C).symm
    _ = C := ba_fond_c

/-! ### Problem 7 -/

/-- A is happy: A is compatible with itself.
Or: A has a point of period at most 2. -/
def IsHappy (A : Bird) : Prop := AreCompatible A A

/-- A is normal: A is fond of at least one bird. Introduced in problem 8; defined here for readability.
Or: A has a fixed point. -/
def IsNormal (A : Bird) : Prop := ∃ B : Bird, IsFondOf A B

/-- Problem 7: Every normal bird is happy.
Or: An element with a fixed point has a point of period at most 2. -/
theorem normal_birds_are_happy {A : Bird}
    (a_normal : IsNormal A) :
    IsHappy A := by
  rw [IsHappy, are_compatible_iff]
  obtain ⟨B, a_fond_b⟩ := a_normal
  exists B
  calc
    A (A B) = A B := congrArg A a_fond_b
    _ = B := a_fond_b

/-! ### Problem 8 -/

/-!
Smullyan: "We have just proved that every normal bird is happy. The converse is not
necessarily true; a happy bird is not necessarily normal."

To prove this, we must construct a countermodel: a forest with a happy bird that isn't normal.
Smullyan does not cover countermodels in this book, but we define one here.
-/
section HappyNotNormal

-- A forest of two birds: `true` flips its argument, `false` returns it unchanged.
local instance : Forest Bool := { app := fun A x => xor A x }

-- The forest is closed under composition, so it satisfies the hypothesis of problem 8.
-- Not strictly required by Smullyan in his claim.
theorem bool_exists_composition :
    ∀ A B : Bool, ∃ AB : Bool, Composes AB A B
  -- identity after identity is the identity
  | false, false => ⟨false, by intro x; cases x <;> rfl⟩
  -- flip after identity, or identity after flip, is flip
  | false, true => ⟨true, by intro x; cases x <;> rfl⟩
  | true, false => ⟨true, by intro x; cases x <;> rfl⟩
  -- flip after flip is the identity
  | true, true => ⟨false, by intro x; cases x <;> rfl⟩

theorem true_happy : IsHappy true := ⟨false, true, rfl, rfl⟩

theorem true_not_normal : ¬ IsNormal true := by
  intro ⟨B, true_fond_b⟩
  cases B <;> contradiction

/-- A happy bird need not be normal, even in a forest closed under composition. -/
theorem happy_not_imp_normal :
    ¬ ∀ (Bird : Type) [Forest Bird],
      (∀ A B : Bird, ∃ AB : Bird, Composes AB A B) →
      ∀ A : Bird, IsHappy A → IsNormal A := by
  intro happy_imp_normal
  exact true_not_normal (happy_imp_normal Bool bool_exists_composition true true_happy)

end HappyNotNormal

include exists_composition in
/-- Problem 8: If some bird is happy, then some bird is normal. -/
theorem exists_normal_bird {A : Bird}
    (a_happy : IsHappy A) :
    ∃ B : Bird, IsNormal B := by
  obtain ⟨AA, aa_comp⟩ := exists_composition A A
  obtain ⟨B, aab_b⟩ := are_compatible_iff.mp a_happy
  exists AA, B
  calc
    AA B = A (A B) := aa_comp B
    _ = B := aab_b

/-! ## Hopeless Egocentricity -/

/-! ### Problem 9 -/

/-- B is hopelessly egocentric: B responds to every bird with B.
Or: B is a left zero. -/
def IsHopelesslyEgocentric (B : Bird) : Prop := ∀ x : Bird, B x = B

/-- A is fixated on B: A responds to every bird with B.
Or: A is a constant map with value B. -/
def IsFixatedOn (A B : Bird) : Prop := ∀ x : Bird, A x = B

/-- A bird is hopelessly egocentric iff it is fixated on itself. -/
theorem fixated_on_self_iff_hopelessly_egocentric {B : Bird} :
    IsFixatedOn B B ↔ IsHopelesslyEgocentric B := Iff.rfl

/-- K is a kestrel: K x y = x for all x and y.
Or: K is the K combinator. -/
def IsKestrel (K : Bird) : Prop := ∀ x y : Bird, K x y = x

variable {K : Bird} (k_kestrel : IsKestrel K)

include exists_composition m_mimics k_kestrel in
/-- Problem 9: Given composition, a mockingbird, and a kestrel, some bird is hopelessly egocentric.
Or: There exists a left zero. -/
theorem exists_hopelessly_egocentric :
    ∃ A : Bird, IsHopelesslyEgocentric A := by
  obtain ⟨H, k_fond_h⟩ := every_bird_is_fond exists_composition m_mimics K
  exists H
  intro x
  calc
    H x = K H x := by rw [k_fond_h]
    _ = H := k_kestrel H x

/-! ### Problem 10 -/

/-- Problem 10: If A is fixated on B, then A is fond of B. -/
theorem fixated_imp_fond {A B : Bird}
    (a_fixated_b : IsFixatedOn A B) :
    IsFondOf A B :=
  a_fixated_b B

/-! ### Problem 11 -/

include k_kestrel in
/-- Problem 11: An egocentric kestrel is hopelessly egocentric. -/
theorem kestrel_egocentric_imp_hopelessly_egocentric
    (k_egocentric : IsEgocentric K) :
    IsHopelesslyEgocentric K := by
  intro x
  calc
    K x = K K x := by rw [k_egocentric]
    _ = K := k_kestrel K x

/-! ### Problem 12 -/

include k_kestrel in
/-- Problem 12: If K x is egocentric, then K is fond of x. -/
theorem kx_egocentric_imp_k_fond_x {x : Bird}
    (kx_egocentric : IsEgocentric (K x)) :
    IsFondOf K x :=
  calc
    K x = K x (K x) := kx_egocentric.symm
    _ = x := k_kestrel x (K x)

/-! ### Problem 13 -/

/-- Problem 13: A hopelessly egocentric bird responds the same to every bird. -/
theorem hopelessly_egocentric_imp_responds_alike {A : Bird}
    (a_hopelessly_egocentric : IsHopelesslyEgocentric A)
    (x y : Bird) :
    A x = A y :=
  calc
    A x = A := a_hopelessly_egocentric x
    _ = A y := (a_hopelessly_egocentric y).symm

/-! ### Problem 14 -/

/-- Problem 14: A hopelessly egocentric bird A satisfies A x y = A for all x and y. -/
theorem hopelessly_egocentric_two_applications {A : Bird}
    (a_hopelessly_egocentric : IsHopelesslyEgocentric A)
    (x y : Bird) :
    A x y = A :=
  calc
    A x y = A y := by rw [a_hopelessly_egocentric x]
    _ = A := a_hopelessly_egocentric y

/-! ### Problem 15 -/

/-- Problem 15: If A is hopelessly egocentric, then so is A x for every x. -/
theorem hopeless_egocentricity_is_contagious {A : Bird}
    (a_hopelessly_egocentric : IsHopelesslyEgocentric A)
    (x : Bird) :
    IsHopelesslyEgocentric (A x) := by
  intro y
  calc
    A x y = A := by rw [hopelessly_egocentric_two_applications a_hopelessly_egocentric]
    _ = A x := (a_hopelessly_egocentric x).symm

/-! ### Problem 16 -/

include k_kestrel in
/-- Problem 16: Left cancellation for kestrels: if K x = K y, then x = y.
Or: x ↦ K x is injective. -/
theorem left_cancellation_law_for_kestrels {x y : Bird}
    (kx_ky : K x = K y) :
    x = y :=
  calc
    x = K x K := (k_kestrel x K).symm
    _ = K y K := by rw [kx_ky]
    _ = y := k_kestrel y K

/-! ### Problem 17 -/

/-- Problem 17: A bird is fixated on at most one bird. -/
theorem fixated_at_most_one {A B C : Bird}
    (a_fixated_b : IsFixatedOn A B)
    (a_fixated_c : IsFixatedOn A C) :
    B = C :=
  calc
    B = A A := (a_fixated_b A).symm
    _ = C := a_fixated_c A

/-! ### Problem 18 -/

include k_kestrel in
/-- Problem 18: If K is fond of K x, then K is fond of x. -/
theorem k_fond_kx_imp_k_fond_x {x : Bird}
    (k_fond_kx : IsFondOf K (K x)) :
    IsFondOf K x :=
  left_cancellation_law_for_kestrels k_kestrel k_fond_kx

/-! ### Problem 19 -/

include k_kestrel in
/-- Problem 19: If a kestrel is egocentric, it is the only bird.
Or: The forest is trivial. -/
theorem egocentric_kestrels_are_lonely
    (k_egocentric : IsEgocentric K)
    (x : Bird) :
    x = K :=
  calc
    x = K x K := (k_kestrel x K).symm
    _ = K K := by rw [kestrel_egocentric_imp_hopelessly_egocentric k_kestrel k_egocentric x]
    _ = K := k_egocentric

/-! ### An intermezzo problem

After problem 19, Smullyan moves on to identity birds. This intermezzo problem, which
is not in Smullyan, shows that there exists an identity bird given composition,
a mockingbird, and a kestrel.
-/

/-- I is an identity bird.
Or: I is a left identity. -/
def IsIdentity (I : Bird) : Prop := ∀ x : Bird, I x = x

include exists_composition m_mimics k_kestrel in
/-- Intermezzo: Given composition, a mockingbird, and a kestrel, some bird is an identity.
Or: There exists a left identity. -/
theorem exists_identity_bird :
    ∃ I : Bird, IsIdentity I := by
  obtain ⟨MK, mk_comp⟩ := exists_composition M K
  exists MK
  intro x
  calc
    MK x = M (K x) := mk_comp x
    _ = K x (K x) := m_mimics (K x)
    _ = x := k_kestrel x (K x)

/-! ## Identity Birds -/

variable {I : Bird} (i_identity : IsIdentity I)

/-! ### Problem 20 -/

include i_identity in
/-- Problem 20: If an identity bird is agreeable, every bird is fond
of at least one bird. -/
theorem every_bird_is_fond_agreeable_identity
    (i_agreeable : IsAgreeable I)
    (A : Bird) :
    ∃ B : Bird, IsFondOf A B := by
  obtain ⟨C, i_a_agree⟩ := i_agreeable A
  exists C
  calc
    A C = I C := i_a_agree.symm
    _ = C := i_identity C

/-! ### Problem 21 -/

include i_identity in
/-- Problem 21: If every bird is fond of at least one bird, then identity birds
are agreeable. -/
theorem fondness_imp_agreeableness_of_identity
    (every_bird_is_fond : ∀ A : Bird, ∃ B : Bird, IsFondOf A B) :
    IsAgreeable I := by
  intro A
  obtain ⟨B, a_fond_b⟩ := every_bird_is_fond A
  exists B
  calc
    I B = B := i_identity B
    _ = A B := a_fond_b.symm

/-! ### Problem 22 -/

include i_identity in
/-- Problem 22.1: Given I, if any two birds are compatible, then every bird is normal.
Or: Every element has a fixed point. -/
theorem identity_and_compatible_imp_is_normal
    (all_compatible : ∀ A B : Bird, AreCompatible A B)
    (A : Bird) :
    IsNormal A := by
  obtain ⟨B, iab_b⟩ := are_compatible_iff.mp (all_compatible A I)
  exists B
  calc
    A B = I (A B) := (i_identity (A B)).symm
    _ = B := iab_b

include i_identity in
/-- Problem 22.2: Given an identity bird, if any two birds are compatible,
then identity bird I is agreeable.
Or: I has a coincidence point with every bird. -/
theorem identity_and_compatible_imp_agreeable_identity
    (all_compatible : ∀ A B : Bird, AreCompatible A B) :
    IsAgreeable I := by
  intro A
  obtain ⟨B, iab_b⟩ := are_compatible_iff.mp (all_compatible A I)
  exists B
  calc
    I B = B := i_identity B
    _ = I (A B) := iab_b.symm
    _ = A B := i_identity (A B)

/-! ### Problem 23 -/

include i_identity in
/-- Problem 23: If an identity bird is hopelessly egocentric, it is the only bird.
Or: The forest is trivial. -/
theorem hopelessly_egocentric_identity_birds_are_lonely
    (i_hopelessly_egocentric : IsHopelesslyEgocentric I)
    (A : Bird) :
    I = A :=
  calc
    I = I A := (i_hopelessly_egocentric A).symm
    _ = A := i_identity A

/-! ## Larks -/

def IsLark (L : Bird) : Prop := ∀ A B : Bird, L A B = A (B B)

variable {L : Bird} (l_lark : IsLark L)

/-! ### Problem 24 -/

include i_identity l_lark in
/-- Problem 24: Given an identity bird and a lark, there exists a mockingbird, to wit: L I.
Or: L I = ω. -/
theorem identity_and_lark_imp_mockingbird : IsMockingbird (L I) := by
  intro A
  calc
    (L I) A = I (A A) := l_lark I A
    _ = A A := i_identity (A A)

/-! ### Problem 25 -/

include l_lark in
/-- Problem 25: Given a lark, every bird is happy. -/
theorem lark_imp_happy (A : Bird) : IsHappy A := by
  apply normal_birds_are_happy
  exists L A (L A)
  exact (l_lark A (L A)).symm

/-! ### Problem 26 -/

include l_lark in
/-- Problem 26: If a lark is hopelessly egocentric, every bird is fond of it. -/
theorem hopelessly_egocentric_larks_are_unusually_attractive
    (l_hopelessly_egocentric : IsHopelesslyEgocentric L)
    (A : Bird) :
    IsFondOf A L :=
  calc
    A L = A (L L) := by rw [l_hopelessly_egocentric L]
    _ = L A L := (l_lark A L).symm
    _ = L L := by rw [l_hopelessly_egocentric A]
    _ = L := l_hopelessly_egocentric L

/-! ### Problem 27 -/

-- TODO

/-! ### Problem 28 -/

-- TODO

/-! ### Problem 29 -/

-- TODO

/- In problem 29, Smullyan writes an egocentric bird using only L's, with 12 of them, and asks
whether a shorter expression exists. `Mockingbird/Extras/ShortestEgocentricLark.lean` shows that
the minimum is 8 -/

end Chapter9
