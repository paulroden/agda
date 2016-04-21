-- Andreas, AIM XXIII 2016-04-21 Overloaded projections

-- Milestone 1: Check overloaded projections on rhs (without postponing).

module _ (A : Set) (a : A) where

record R B : Set where
  field f : B
open R

record S B : Set where
  field f : B
open S

record T B : Set where
  field f : B → B
open T

r : R A
R.f r = a

s : S A
S.f s = f r

t : R A → S A
S.f (t r) = f r

u : _
u = f s

v = f s

w : ∀{A} → T A → A → A
w t x = f t x
