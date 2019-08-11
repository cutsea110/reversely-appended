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
lemma xs =
  begin
    length (xs ++ reverse xs)
  ≡⟨ length-++ xs ⟩
    length xs + length (reverse xs)
  ≡⟨ cong (λ n → length xs + n) (length-reverse xs) ⟩
    length xs + length xs
  ≡⟨ sym (length-++ xs) ⟩
    length (xs ++ xs)
  ∎

theorem : {a : Set} (xs : List a) → even? (length (xs ++ reverse xs)) ≡ true
theorem xs =
  begin
    even? (length (xs ++ reverse xs))
  ≡⟨ cong even? (lemma xs) ⟩
    even? (length (xs ++ xs))
  ≡⟨ cong even? (length-++ xs {ys = xs}) ⟩
    even? (length xs + length xs)
  ≡⟨ n+n-is-even (length xs) ⟩
    true
  ∎
