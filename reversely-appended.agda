open import Data.Bool
open import Data.List
open import Data.List.Properties using (length-++; length-reverse)
open import Data.Nat
open import Data.Nat.Properties using (+-suc)
open import Relation.Binary.PropositionalEquality as PropEq
open ≡-Reasoning

even? : ℕ → Bool
even? zero = true
even? (suc zero) = false
even? (suc (suc n)) = even? n

n+n-is-even : (n : ℕ) → even? (n + n) ≡ true
n+n-is-even zero = refl
n+n-is-even (suc n) rewrite +-suc n n = n+n-is-even n

lemma : {a : Set} (xs : List a) → length (xs ++ reverse xs) ≡ length (xs ++ xs)
lemma xs rewrite length-++ xs {ys = reverse xs} | cong (length xs +_) (length-reverse xs) | sym (length-++ xs {ys = xs}) = refl

theorem : {a : Set} (xs : List a) → even? (length (xs ++ reverse xs)) ≡ true
theorem xs rewrite lemma xs | length-++ xs {ys = xs} | n+n-is-even (length xs) = refl
