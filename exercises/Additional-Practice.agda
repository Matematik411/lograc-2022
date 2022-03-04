module Additional-Practice where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.Nat.Properties

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap zero n p = refl
+-swap (suc m) n p = 
    begin
        suc (m + (n + p)) ≡⟨ cong suc (+-swap m n p) ⟩
        suc (n + (m + p)) ≡⟨ sym (+-suc _ _ )⟩
        n + suc (m + p) 
    ∎

*-comm' : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm' zero n = sym (*-zeroʳ n)
*-comm' (suc m) n rewrite *-comm' m n = sym ( *-suc n m  )

