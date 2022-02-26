open import Relation.Binary.PropositionalEquality
open import Data.List hiding (reverse)
open import Data.Nat
open import Data.Nat.Properties

module length-reverse where

private
  rev : {A : Set} → List A → List A → List A
  rev xs [] = xs
  rev xs (x ∷ ys) = rev (x ∷ xs) ys

reverse : {A : Set} → List A → List A
reverse {A} zs = rev [] zs

length-reverse : {A : Set} {zs : List A} → length (reverse zs) ≡ length zs
length-reverse {A} {zs} = length-rev [] zs
  where 
    open ≡-Reasoning
    
    length-rev : (us vs : List A) → length (rev us vs) ≡ length us + length vs
    length-rev us [] = sym (+-identityʳ (length us))
    length-rev us (x ∷ vs) =
      begin
        length (rev us (x ∷ vs))      ≡⟨ length-rev (x ∷ us) vs ⟩
        length (x ∷ us) + length vs   ≡˘⟨ +-suc (length us) (length vs) ⟩
        length us + length (x ∷ vs)
        ∎

-- 1
-- this is reducing as induction wants it 
--  length (rev (x ∷ us) vs)  ≡ length us + suc (length vs)

-- 2 
-- suc (length us + length vs) ≡
--      length us + suc (length vs)
-- WE NEED suc (x + y) = x + suc y

-- !! ˘ ... it turns the proof around ... as sym
-- typed as u + { + } 