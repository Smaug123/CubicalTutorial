{-# OPTIONS --safe --warning=error --cubical --without-K #-}

open import Agda.Primitive
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Naturals
open import Basic

module File1 where

{-
Let's define the integers. Answers can be found in commit 4d7aad52e014daeb48fe5fb6854d3b6e0080012a.

If you want to learn how to type something, remember the Emacs action is M-x describe-char with the cursor on a character.
-}
data ℤ : Set where
  pos : ℕ → ℤ
  neg : ℕ → ℤ
  congZero : pos 0 ≡ neg 0

{-
A bit odd! We defined an integer to be "a natural tagged as positive", "a natural tagged as negative", or "a witness that pos 0 = neg 0".
This is obvious nonsense (how can two things be equal if they were made from different constructors?! what even does it mean for "pos 0 ≡ neg 0" to be an integer?!) until you let go of your preconceptions about what it means for two things to be equal.
-}

-- Just to help you realise how odd this is, we'll use some new Cubical definitions to manifest a really weird element of ℤ which is neither a `pos` nor a `neg`. Don't worry too much about this for now.
oddThing : ℤ
oddThing = congZero i1

-- Even odder, the integer we just made is equal to 0. Think how strange this is: it's not built using the only constructor that could build `pos 0`, but it's still equal to `pos 0`.
oddThing2 : pos 0 ≡ oddThing
oddThing2 = congZero

{-
Add 1 to an integer. The first cases are easy, but the last case is very odd and we will discuss it in detail.
-}
incr : ℤ → ℤ
incr (pos x) = pos (succ x)
incr (neg zero) = pos 1
incr (neg (succ x)) = neg x

-- First of all, we have in scope an "integer" `congZero` which is of type `pos 0 ≡ neg 0` - huh?!
incr (congZero i) = {!!}
{-
This one looks different from the non-cubical world.

Goal: ℤ
———— Boundary ——————————————————————————————————————————————
i = i0 ⊢ pos 1
i = i1 ⊢ pos 1
————————————————————————————————————————————————————————————
i : I
———— Constraints ———————————————————————————————————————————
pos 1 = ?0 (i = i1) : ℤ
pos 1 = ?0 (i = i0) : ℤ

The constraints look pretty normal, telling you that goal 0 needs to be equal to `pos 1`.
But there's stuff about this `i : I` here. What's that?

Recall that Cubical alters the definition of ≡. Given any element of X, an element of X ≡ Y contains content for how that element corresponds to a Y, and vice versa.
Homotopy type theory, and Cubical Agda, prefer to think of a more general structure on top of that data, though: not only can we go from an X to a Y, but we also store *how* we get there.
More abstractly, we store how to traverse a path from X to Y. The `i` here is telling us where along that path we are; the template goes from the special symbol `i0` to the special symbol `i1`, and `i` is notionally somewhere between those two points.

This gives some nice composability properties: if we know that X ≡ Y and that Y ≡ Z, we can compose the two paths to get a path X ≡ Z.
Cubical Agda's great innovation is that all this has computational content: proofs about X can be transported along the path to obtain for free proofs about Z.

Having told Agda that `incr (pos x) = pos (succ x)`, it can infer that `incr (pos 0) = pos 1`.
So our goal of constructing a path `incr congZero : incr (pos 0) ≡ incr (neg 0)` is in fact the requirement to construct a path `pos 1 ≡ incr (neg 0)`.
Similarly, we told it that `incr (neg 0) = pos 1`, so our path `incr congZero` is actually of type `pos 1 ≡ pos 1`
The `I` from the goal is the template of the path `congZero n` which we are trying to construct from `pos 1` to `pos 1`.
The `i0` and `i1` are the templates for the start and end points of the path, i.e. they both indicate `pos 1`.

What we really wanted to write here was `incr congZero`. For reasons I don't understand, Agda doesn't accept this.
We are forced to descend to the level of actually implementing the path from `pos 1` to `pos 1` by telling Agda where each `i` goes, even though there's an obvious way (`refl`) to specify the entire path at once.

Agda can automatically infer the correct hole-fill, but you can try it with `pos 1`.
-}

{-
Let's show that successors of naturals are nonzero.
We do this using a new technique that only makes sense in Cubical-land.

Given a path from `succ a` to `0`, we need to show False.
The assumed member of `succ a ≡ 0` is a path that tells us how to get from `succ a` to `0` in a way that is preserved by function application.
That is, it tells us how to show `f (succ a) ≡ f 0` for any `f`. (The function `subst` captures this ability to move functions from one end of a path to the other.)
So if we pick `f` appropriately so that it outputs `False` at 0 but something else (anything else, as long as we can construct it!) at `succ a`, we will be done.
-}
succNonzero : {a : ℕ} → succ a ≡ 0 → False
succNonzero {a} sa=0 = subst f sa=0 {!!}
  where
    f : ℕ → Set
    f zero = False
    f (succ i) = {!!}

{-
Let's show that these equality things aren't *too* weird. We'll show that even though `pos 0` is equal to `congZero i1`, it's actually the *only* other `pos` which is equal to `congZero i1`. (You'd hope this would be the case; otherwise we'd have several `pos` being equal to each other.)

Cubical Agda gives us a magical way to do this. Recall that we can move functions along paths (the `subst` from above, which lets us take an `x ≡ y` and an `f` to get `f x → f y`); we can actually also do the same thing viewed as transforming the *entire path* `x ≡ y` using `f` into `f x ≡ f y`.
This is the function `cong`.

If we can somehow create a function that "strips off `pos`", then that function can transform the path `pos a ≡ pos b` into a path `a ≡ b`.
-}
toNat : ℤ → ℕ
toNat z = {!!}

posInjective : {a b : ℕ} → pos a ≡ pos b → a ≡ b
posInjective pr = cong toNat pr

{-
Finally, we can use the injectivity of `pos` in the obvious way to prove that only `pos 0` is `congZero i1`.
-}
notTooOdd : (n : ℕ) → (pos n ≡ congZero i1) → n ≡ 0
notTooOdd zero pr = refl
notTooOdd (succ n) pr = posInjective (pr ∙ sym congZero)

{-
Let's show that `pos` is injective in a different way, inspired by how you might do this kind of thing in a non-Cubical world. We'll go by induction, which means the interesting case will be `pos (succ a) ≡ pos (succ b) → pos a ≡ pos b`.

This is a classic example of moving a path wholesale along a function; in this case, the function is "decrement".
-}
decr : ℤ → ℤ -- TODO hole this
decr z = {!!}

posDecr : {a b : ℕ} → pos (succ a) ≡ pos (succ b) → pos a ≡ pos b
posDecr {a} {b} pr = cong decr pr

posInjective' : {a b : ℕ} → pos a ≡ pos b → a ≡ b
-- The two easy cases first
posInjective' {zero} {zero} x = refl
posInjective' {succ a} {succ b} x = cong succ (posInjective (posDecr x))
{-
We need to transform `pos zero ≡ pos (succ b)` into `zero ≡ succ b`.
We could do this using the proof of `posInjective` - moving the path along `toNat` - but it is also interesting to construct the path `zero ≡ succ b` manually using `subst`.

To use `subst`, we need to construct a function from ℤ which is "a type we can populate" at `pos zero` (i.e. at one end of the path), and `zero ≡ succ b` at `pos (succ b)` (i.e. at the other end of the path); then we will be able to move from the populated type to `zero ≡ succ b` using that function.

These two are quite hard!
-}
posInjective' {zero} {succ b} x = subst t x {!!}
  where
    t : ℤ → Set
    t z = {!!}
posInjective' {succ a} {zero} x = subst t x {!!}
  where
    t : ℤ → Set
    t z = {!!}

{-
What does equality mean on the level of types, rather than values?
Univalence, the axiom which Cubical provides computational meaning to, basically says "identity really means isomorphism".
I will gloss over a lot of detail there, but here is a witness to `ℤ ≡ ℤ` that is not `refl`!
-}
incrDecrInverse1 : (a : ℤ) → incr (decr a) ≡ a
incrDecrInverse1 (pos zero) = sym congZero
incrDecrInverse1 (pos (succ x)) = refl
incrDecrInverse1 (neg x) = refl
{-
The remaining case is worth talking about.
We need a path from incr (decr (congZero j)) to congZero j.
That is, we need a path from incr (neg 1) to congZero j; i.e. from neg 0 to congZero j.
We already have a path from neg 0 to pos 0 - namely `sym congZero`.
But `sym congZero` goes from `neg 0` to every point along `sym congZero` - and `congZero j` is also a point along `sym congZero`, because `sym` just means "reverse the path"!
So we can get the path we need by truncating `sym congZero`, using the `∧` ("min") operation (a special builtin primitive in Cubical).
The path, parameterised by `i` with `j` fixed, is "go backwards (`sym`) along `congZero` to the min of `i` and where `j` lies on this path (`~ j`), but then don't go any further".
Here, `~` means essentially "negate"; if you got to position `i` travelling forward on path `p`, then you got to position `~ i` travelling backward on path `sym p`.

This is probably best done if you draw a little picture.
-}
incrDecrInverse1 (congZero j) i = sym congZero (i ∧ (~ j))

incrDecrInverse2 : (a : ℤ) → decr (incr a) ≡ a
incrDecrInverse2 x = {!!}

incrIso : ℤ ≡ ℤ
incrIso = isoToPath (iso incr decr incrDecrInverse1 incrDecrInverse2)

{-
Unexpected! Cubical has let us prove that ℤ ≡ ℤ in a very nonstandard way. What use is this? Who knows.
-}
