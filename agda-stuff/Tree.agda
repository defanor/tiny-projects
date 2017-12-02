module Tree where

open import Data.Maybe
open import Data.List
open import Data.List.Any
open Data.List.Any.Membership-≡
open import Level
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])
open import Data.Bool
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Unit


-- a property-preserving tree: keeps a given relation between every
-- node and it's subtrees

data Forest {a} (A : Set a) (P : Maybe A → A → Bool) (root : A) : Set a

data Tree {a} (A : Set a) (P : Maybe A → A → Bool) (root : Maybe A) : Set a where
  tree : (v : A) → (P root v ≡ true) → (Forest A P v) → Tree A P root

data Forest {a} A P root where
  forest : List (Tree A P (just root)) → Forest A P root


-- cut a tree: replace one property with another

tree-cut : {a : Level} → (A : Set a) → (P Q : Maybe A → A → Bool) → 
  (root : Maybe A) → Tree A P root →
  Maybe (Tree A Q root)

gfilter-tc : {a : Level} → (A : Set a) → (P Q : Maybe A → A → Bool) →
  (root : A) →
  List (Tree A P (just root)) →
  List (Tree A Q (just root))
gfilter-tc _ _ _ _ [] = []
gfilter-tc A P Q r (x ∷ xs) with tree-cut A P Q (just r) x
gfilter-tc A P Q r (x ∷ xs) | just x₁ = x₁ ∷ gfilter-tc A P Q r xs
gfilter-tc A P Q r (x ∷ xs) | nothing = gfilter-tc A P Q r xs

forest-cut : {a : Level} → {A : Set a} → {P Q : Maybe A → A → Bool} → {root : A} →
  Forest A P root →
  Forest A Q root
forest-cut {a} {A} {P} {Q} {r} (forest x) = forest (gfilter-tc A P Q r x)

tree-cut A P Q r (tree v Prv f) with ((Q r) v) | inspect (Q r) v
tree-cut A P Q r (tree v Prv lt) | true | PropEq.[ eq ] = just (tree v eq (forest-cut lt))
tree-cut A P Q r (tree v Prv f) | false | PropEq.[ eq ] = nothing

