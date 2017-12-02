module Markov where

open import Data.Nat
open import Coinduction
open import Data.Colist
open import Data.Char
open import Data.List
open import Data.String hiding (_==_)
open import Data.Bool
open import Data.Maybe
open import Category.Monad
open import Data.Unit
open import Data.Product
import IO
import Level
open RawMonad (Data.Maybe.monad {Level.zero}) public

_is-prefix-of_ : List Char → List Char → Bool
[] is-prefix-of b = true
(x ∷ a) is-prefix-of [] = false
(x ∷ a) is-prefix-of (y ∷ b) = (x == y) ∧ a is-prefix-of b

skip1 : List Char → List Char → List Char
skip1 [] s = s
skip1 (x ∷ t) [] = []
skip1 (x ∷ t) (x₁ ∷ s) = skip1 t s

replace1' : List Char → List Char → List Char → Maybe (List Char)
replace1' r w [] = nothing
replace1' [] w (x ∷ s) = nothing
replace1' (r ∷ rl) w (s ∷ sl) = 
  if (r ∷ rl) is-prefix-of (s ∷ sl)
  then just (w Data.List.++ skip1 rl sl)
  else replace1' (r ∷ rl) w sl >>= (λ x → just (s ∷ x))

replace1 : String → String → String → Maybe String
replace1 s1 s2 s3 = (replace1' (toList s1) (toList s2) (toList s3)) >>= λ x → just (Data.String.fromList x)

rules : List (String × String)
rules = ("|0" , "0||") ∷ ("1" , "0|") ∷ ("0" , "") ∷ Data.List.[]

iter : List (String × String) → String → Maybe String
iter r "" = nothing
iter [] s = nothing
iter ((r , w) ∷ rl) s =
  if is-just result
  then result
  else iter rl s
  where
    result = replace1 r w s

eval : String → Colist String
eval s with iter rules s
eval s | just x = x ∷ ♯ eval x
eval s | nothing = []

printColist : Colist String → IO.IO ⊤
printColist [] = IO.return tt
printColist (x ∷ xs) = ♯ IO.putStrLn x IO.>> ♯ printColist (♭ xs)

main = IO.run (printColist (eval "101"))
