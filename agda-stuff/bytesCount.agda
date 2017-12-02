module bytesCount where
open import Data.Nat
open import Data.Nat.DivMod
open import Relation.Binary.PropositionalEquality as PropEq
open import Data.Unit.Core
open import Relation.Nullary.Decidable
open import Data.Fin using (toℕ)
open import Relation.Nullary
open import Data.Nat.Properties
import Data.Unit as Unit
import Data.Bool as Bool
open import Data.Empty as Empty

-- helpers

-- pow
_^_ : ℕ → ℕ → ℕ
n ^ 0 = 1
n ^ (suc m) = n * (n ^ m)

-- binary logarithm
log₂-aux : ℕ → ℕ → ℕ
log₂-aux _ 0 = 0
log₂-aux 0 _ = 0
log₂-aux 1 _ = 0
log₂-aux n (suc m) = suc (log₂-aux ⌊ n /2⌋ m)

log₂ : ℕ → ℕ
log₂ n = log₂-aux n n

-- rounding up division
div-up-helper : ℕ → ℕ
div-up-helper 0 = 0
div-up-helper (suc _) = 1

_div-up_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → ℕ
_div-up_ x y {≢0} = _div_ x y {≢0} + div-up-helper (toℕ (_mod_ x y {≢0}))


-- functions

bitsRequired : ℕ → ℕ
bitsRequired n = suc (log₂ n)

bytesRequired : ℕ → ℕ
bytesRequired n = (bitsRequired n) div-up 8


-- postulates, from coq lib
-- would be nice to prove later

-- Nat.pow_nonzero: forall a b : nat, a <> 0 -> a ^ b <> 0
postulate pow-nonzero : ∀ a b → False (a ≟ 0) → False ((a ^ b) ≟ 0)
-- log2_spec: forall n : nat, 0 < n -> 2 ^ log2 n <= n < 2 ^ S (log2 n)
postulate log₂-spec-l : ∀ (n : ℕ) → 0 < n → 2 ^ (log₂ n) ≤ n
postulate log₂-spec-r : ∀ (n : ℕ) → 0 < n → n < 2 ^ (suc (log₂ n))
-- le_not_gt: forall n m : nat, n <= m -> ~ n > m
postulate le-not-gt : ∀ (n m : ℕ) → n ≤ m → ¬ n > m
-- le_not_lt: forall n m : nat, n <= m -> ~ m < n
postulate le-not-lt : ∀ (n m : ℕ) → n ≤ m → ¬ m < n
-- lt_le_trans: forall n m p : nat, n < m -> m <= p -> n < p
postulate lt-le-trans : ∀ (n m p : ℕ) → n < m → m ≤ p → n < p
-- Nat.pow_le_mono_r: forall a b c : nat, a <> 0 -> b <= c -> a ^ b <= a ^ c
postulate pow-le-mono-r : ∀ (a b c : ℕ) → a > 0 → b ≤ c → a ^ b ≤ a ^ c
-- lt_le_S: forall n m : nat, n < m -> S n <= m
postulate lt-le-suc : ∀ (n m : ℕ) → n < m → suc n ≤ m
-- Nat.succ_le_mono: forall n m : nat, n <= m <-> S n <= S m
postulate suc-le-le : ∀ (n m : ℕ) → suc n ≤ suc m → n ≤ m
-- le_trans: forall n m p : nat, n <= m -> m <= p -> n <= p
postulate le-trans : ∀ n m p → n ≤ m → m ≤ p → n ≤ p
-- Nat.neq_0_lt_0: forall n : nat, n <> 0 <-> 0 < n
postulate lt-0-neq-0 : ∀ n → 0 < n → False (n ≟ 0)
-- plus_n_O: forall n : nat, n = n + 0
postulate plus-n-O : ∀ n → n + 0 ≡ n
-- le_lt_or_eq_iff: forall n m : nat, n <= m <-> n < m \/ n = m
postulate lt-le : ∀ n m → n < m → n ≤ m
postulate le-eq : ∀ n m → n ≡ m → n ≤ m
postulate le-lt : ∀ a b → a ≤ b → a < (suc b)
-- Nat.div_exact: forall a b : nat, b <> 0 -> (a = b * (a / b) <-> a mod b = 0)
postulate div-exact₀ : ∀ a b → (≢0 : False (b ≟ 0)) → (toℕ (_mod_ a b {≢0}) ≡ 0) → (a ≡ b * (_div_ a b {‌≢0}))
-- mult_plus_distr_l: forall n m p : nat, n * (m + p) = n * m + n * p
postulate mult-plus-distr-l : ∀ (n m p : ℕ) → n * (m + p) ≡ n * m + n * p
-- Nat.mul_succ_div_gt: forall a b : nat, b <> 0 -> a < b * S (a / b)
postulate mult-suc-div-gt : ∀ (a b : ℕ) → (≢0 : False (b ≟ 0)) → a < b * suc (_div_ a b {≢0})
-- Nat.add_1_r: forall n : nat, n + 1 = S n
postulate add-1-r : ∀ n → n + 1 ≡ suc n
-- Nat.mul_comm: forall n m : nat, n * m = m * n
postulate *-comm : ∀ (n m : ℕ) → n * m ≡ m * n
-- Nat.le_sub_l: forall n m : nat, n - m <= n
postulate le-sub-l : ∀ n m → n ∸ m ≤ n
-- Nat.add_sub: forall n m : nat, n + m - m = n
postulate add-sub : ∀ n m → n + m ∸ m ≡ n
-- Nat.div_mod: forall x y : nat, y <> 0 -> x = y * (x / y) + x mod y
postulate div-mod : ∀ x y → (≢0 : False (y ≟ 0)) → x ≡ y * (_div_ x y {≢0}) + toℕ (_mod_ x y {≢0})
-- plus_Snm_nSm: forall n m : nat, S n + m = n + S m
plus-Snm-nSm : ∀ n m → suc n + m ≡ n + suc m
plus-Snm-nSm zero m = refl
plus-Snm-nSm (suc n) m = cong suc (plus-Snm-nSm n m)
-- plus_comm: forall n m : nat, n + m = m + n
plus-comm : ∀ n m → n + m ≡ m + n
plus-comm zero m = sym (plus-n-O m)
plus-comm (suc n) m = subst (λ x → suc (n + m) ≡ x) (plus-Snm-nSm m n) (cong suc (plus-comm n m))
-- Nat.le_add_r: forall n m : nat, n <= n + m
le-add-r : ∀ n m → n ≤ n + m
le-add-r zero m = z≤n
le-add-r (suc n) m = s≤s (le-add-r n m)
-- le_plus_trans: forall n m p : nat, n <= m -> n <= m + p
le-plus-trans : ∀ n m p → n ≤ m → n ≤ m + p
le-plus-trans .0 m p z≤n = z≤n
le-plus-trans .(suc m) .(suc n) p (s≤s {m} {n} n≤m) = s≤s (le-plus-trans m n p n≤m)
-- plus_le_compat: forall n m p q : nat, n <= m -> p <= q -> n + p <= m + q
plus-le-compat : ∀ n m p q → n ≤ m → p ≤ q → n + p ≤ m + q
plus-le-compat .0 m p q z≤n p≤q = subst (λ x → p ≤ x) (plus-comm q m) (le-plus-trans p q m p≤q)
plus-le-compat .(suc m) .(suc n) p q (s≤s {m} {n} n≤m) p≤q = s≤s (plus-le-compat m n p q n≤m p≤q)
-- mult_le_compat_l: forall n m p : nat, n <= m -> p * n <= p * m
mult-le-compat-l : ∀ n m p → n ≤ m → p * n ≤ p * m
mult-le-compat-l n m zero n≤m = z≤n
mult-le-compat-l n m (suc p) n≤m = plus-le-compat n m (p * n) (p * m) n≤m (mult-le-compat-l n m p n≤m)
-- lt_n_Sm_le: forall n m : nat, n < S m -> n <= m
lt-n-suc-m-le : ∀ n m → n < suc m → n ≤ m
lt-n-suc-m-le n m (s≤s n<sm) = n<sm
-- plus_n_Sm: forall n m : nat, S (n + m) = n + S m
plus-n-Sm : ∀ n m → suc (n + m) ≡ n + suc m
plus-n-Sm zero m = refl
plus-n-Sm (suc n) m = cong suc (plus-n-Sm n m)
-- le_plus_l: forall n m : nat, n <= n + m
le-plus-l : ∀ n m → n ≤ n + m
le-plus-l n zero = le-eq n (n + 0) (sym (plus-n-O n))
le-plus-l n (suc m) = lt-le n (n + suc m) (subst (λ x → suc n ≤ x) (plus-n-Sm n m) (s≤s (le-plus-l n m)))

-- lemmas and stuff

data BitsEnough : ℕ → ℕ → Set where
  be : ∀ (bits for : ℕ) → for < (2 ^ bits) → BitsEnough bits for

bytesEnough : ℕ → ℕ → Set
bytesEnough bytes for = BitsEnough (bytes * 8) for

z<sn : ∀ n → zero < suc n
z<sn n = s≤s z≤n

div-up-mul : ∀ x y → (≢0 : False (y ≟ 0)) → x ≤ y * (_div-up_ x y {≢0})
div-up-mul x y ≢0 with (toℕ (_mod_ x y {≢0})) | inspect toℕ (_mod_ x y {≢0})
div-up-mul x y ≢0 | zero | [ xmody ] = le-eq x 
                                             (y * ((x div y) {≢0} + 0))
                                             (trans (div-exact₀ x y ≢0 xmody)
                                                    (cong (λ x₁ → y * x₁) (sym (plus-n-O ((x div y) {≢0})))))
div-up-mul x y ≢0 | suc n | [ xmody ] = lt-le x 
                                              (y * ((x div y) {≢0} + 1))
                                              (subst (λ n₁ → suc x ≤ y * n₁)
                                                     (sym (add-1-r (x div y)))
                                                     (mult-suc-div-gt x y ≢0))


-- theorems

bitsRequiredIsEnough : ∀ n → BitsEnough (bitsRequired n) n
bitsRequiredIsEnough zero = be (suc zero) zero (s≤s z≤n)
bitsRequiredIsEnough (suc n) = be (bitsRequired (suc n)) (suc n) (log₂-spec-r (suc n) (s≤s z≤n))

moreBitsIsEnough : ∀ x y z → BitsEnough x y → x ≤ z → BitsEnough z y
moreBitsIsEnough x y z (be .x .y x₁) x≤z = be z y (le-trans (suc y)
                                                  (2 ^ x)
                                                  (2 ^ z)
                                                  x₁
                                                  (pow-le-mono-r 2 x z (s≤s z≤n) x≤z))

bitsRequiredNotExcessive : ∀ n m → n > 0 → m < (bitsRequired n) → ¬ BitsEnough m n
bitsRequiredNotExcessive n zero n>0 m<br (be .0 .n x) = le-not-gt (suc n) 1 x (s≤s n>0)
bitsRequiredNotExcessive n (suc m) n>0 m<br (be .(suc m) .n x) = 
  le-not-lt (2 ^ log₂ n)
            n
            (log₂-spec-l n n>0)
            (lt-le-trans n 
                         (2 ^ suc m)
                         (2 ^ log₂ n)
                         x
                         (pow-le-mono-r 2 (suc m) (log₂ n) (s≤s z≤n) (suc-le-le (suc m) (log₂ n) m<br)))

bytesRequiredIsEnough : ∀ n → bytesEnough (bytesRequired n) n
bytesRequiredIsEnough n = moreBitsIsEnough (bitsRequired n)
                                           n
                                           ((bytesRequired n) * 8)
                                           (bitsRequiredIsEnough n)
                                           (subst (λ x → bitsRequired n ≤ x)
                                                  (*-comm 8 (bytesRequired n))
                                                  (div-up-mul (bitsRequired n) 8 Unit.tt))

brne-lemma₀ : ∀ n → 0 < n → ((bytesRequired n ∸ 1) * 8) < bitsRequired n
brne-lemma₀ n 0<n with (toℕ (suc (log₂ n) mod 8)) | inspect toℕ (suc (log₂ n) mod 8)
brne-lemma₀ n 0<n | zero | [ lmeq ] = s≤s 
  (subst (λ x → (x ∸ 1) * 8 ≤ log₂ n) 
         (sym (plus-n-O (suc (log₂ n) div 8)))
         (subst (λ x → x ≤ log₂ n)
                (sym (*-distrib-∸ʳ 8 (suc (log₂ n) div 8) 1))
                (subst (λ x → x ∸ 1 * 8 ≤ log₂ n)
                       (*-comm 8 (suc (log₂ n) div 8))
                       (subst (λ x → x ∸ 1 * 8 ≤ log₂ n)
                              (div-exact₀ (suc (log₂ n)) 8 Unit.tt lmeq)
                              (le-sub-l (log₂ n) 7)))))
brne-lemma₀ n 0<n | suc lm | [ lmeq ] = 
  -- eliminate "+ 1 ∸ 1"
  (subst (λ x → suc (x * 8) ≤ suc (log₂ n)) 
         (sym (add-sub (suc (log₂ n) div 8) 1))
         -- turn suc (log₂ n) into 8 * suc (log₂ n) div 8 + toℕ (suc (log₂ n) mod 8)
         (subst (λ x → suc (suc (log₂ n) div 8 * 8) ≤ x)
                (sym (div-mod (suc (log₂ n)) 8 Unit.tt))
                -- toℕ (suc (log₂ n) mod 8) to suc lm
                (subst
                   (λ x → suc (suc (log₂ n) div 8 * 8) ≤ 8 * suc (log₂ n) div 8 + x) (sym lmeq)
                   -- now we have to prove suc (suc (log₂ n) div 8 * 8) ≤ 8 * suc (log₂ n) div 8 + suc lm
                   -- (suc (log₂ n) div 8 * 8) to 8 * suc (log₂ n) div 8
                   (subst (λ x → suc x ≤ 8 * suc (log₂ n) div 8 + suc lm)
                          (sym (*-comm (suc (log₂ n) div 8) 8))
                          -- suc (8 * suc (log₂ n) div 8) ≤ 8 * suc (log₂ n) div 8 + suc lm
                          (subst (λ x → suc (8 * suc (log₂ n) div 8) ≤ x) 
                                 (plus-n-Sm (8 * suc (log₂ n) div 8) lm)
                                 -- suc (8 * suc (log₂ n) div 8) ≤ suc (8 * suc (log₂ n) div 8 + lm)
                                 (s≤s (le-plus-l (8 * suc (log₂ n) div 8) lm)))))))

bytesRequiredNotExcessive : ∀ n → 0 < n → ¬ (bytesEnough (bytesRequired n ∸ 1) n)
bytesRequiredNotExcessive n h bep = 
  bitsRequiredNotExcessive n ((bytesRequired n ∸ 1) * 8) h (brne-lemma₀ n h) bep
