# Dependent sums and records

In today's lecture we shall first revisit some of the examples from the previous lecture in order to learn better how equality reasoning works. Then we shall learn about dependent sums and records.

```
open import Relation.Binary.PropositionalEquality
import Data.Empty
import Data.List
import Data.Nat
import Data.Nat.Properties
import Data.Bool
import Data.Fin
import Data.Product

module 03-dependent-sums-and-records where
```

## Revisiting equality examples

### List reversal preserves length

We shall not do this example in class, but it is included here for reference. It is recommended that you watch [this video](https://youtu.be/1kI12gC8hjU) to see how the proof of `length-reverse` is constructed.

We will start using modules inside modules to separate examples. This is good practice anyhow, and is necessary to avoid conflicts with multiple `open` statements.

```
module LengthReverse where
  open Data.List hiding (reverse)
  open Data.Nat.Properties

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
      open Data.Nat

      length-rev : (us vs : List A) → length (rev us vs) ≡ length us + length vs
      length-rev us [] = sym (+-identityʳ (length us))
      length-rev us (x ∷ vs) =
        begin
          length (rev us (x ∷ vs))     ≡⟨ length-rev (x ∷ us) vs ⟩
          length (x ∷ us) + length vs  ≡˘⟨ +-suc (length us) (length vs) ⟩
          length us + length (x ∷ vs)
        ∎
```

### The depth of a full tree

Recall the definition of binary trees whose nodes are labeled by the elements of `A`:

```
module FullTree where
  open Data.Nat
  open Data.Nat.Properties

  data Tree (A : Set) : Set where
    leaf : Tree A
    node : Tree A → A → Tree A → Tree A
```

We may define the depth of a tree as follows:

```
  depth : {A : Set} → Tree A → ℕ
  depth leaf = 0
  depth (node ℓ x r) = suc ((depth ℓ) ⊔ (depth r))
```

Do you know how what `⊔` is? Move the cursor on it and press `F12` or `Alt-.` to visit its definition.

The full tree of depth `n` whose nodes labeled by the given element `x`:

```
  full : {A : Set} → A → ℕ → Tree A
  full _ zero = leaf
  full x (suc n) = node (full x n) x (full x n)
```

We show that the depth of `full n` is indeed `n`. The solution given below may serve as a reference, but is hardly going
to help you learn how to actually find it. Once the video recording of the lecture is available, we will link to it
here.

```
  depth-full : {A : Set} (x : A) → (n : ℕ) → depth (full x n) ≡ n
  depth-full x 0 = refl
  depth-full x (suc n) =
    begin
      depth (full x (suc n))  ≡⟨ cong suc (⊔-idem ((depth (full x n)))) ⟩
      suc (depth (full x n))  ≡⟨ cong suc (depth-full x n) ⟩
      suc n
    ∎
    where open ≡-Reasoning
```

### Reversal of concatenated lists

Let us define a slightly different way of reversing lists:

```
module Opposite++ where

  open Data.List

  opposite : {A : Set} → List A → List A
  opposite [] = []
  opposite (x ∷ xs) = opposite xs ++ (x ∷ [])
```

Let us prove that `opposite (xs ++ ys) ≡ opposite ys ++ opposite xs`. For reference, here is a solution, but once again
you really should watch the video (which will be linked to once it is available):

```
  ++-[] : {A : Set} (xs : List A) → xs ++ [] ≡ xs
  ++-[] [] = refl
  ++-[] (x ∷ xs) = cong (x ∷_) (++-[] xs)

  ++-assoc : {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  ++-assoc [] ys zs = refl
  ++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

  opposite-++ : {A : Set} (xs ys : List A) → opposite (xs ++ ys) ≡ opposite ys ++ opposite xs
  opposite-++ [] ys = sym (++-[] (opposite ys))
  opposite-++ (x ∷ xs) ys =
    begin
     opposite ((x ∷ xs) ++ ys)                ≡⟨ cong (_++ x ∷ []) (opposite-++ xs ys) ⟩
     (opposite ys ++ opposite xs) ++ x ∷ []   ≡⟨ ++-assoc (opposite ys) (opposite xs) (x ∷ []) ⟩
     opposite ys ++ opposite (x ∷ xs)
     ∎

    where open ≡-Reasoning
```

## Dependent sums (`Σ`-types)

We shall have a look at a new type-theoretic construction, namely **dependent sums**, also known as **`Σ`-types** and
**dependent pair types**.

:::{seealso}

For more thorough understanding you should supplement the lecture with the following reading:

* The section “Existentials” in the [Quantifiers](https://plfa.github.io/Quantifiers/) section of PLFA.
* The section [Σ-types](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#sigmatypes) in IUFMA

:::


The dependent sums in Agda are defined in the module `Data.Product`. Unfortunately, the authors of the standard library decided to call the construction “dependent products”, while the rest of the planet dependent products with dependent function types.

### Using `Σ`-types

To get acquainted with `Σ`-types, we shall work through a simple example.

We start by defining the parity of a number: `0`, `2`, `4`, ... are even and `1`, `3`, `5`, ... are odd. One might do it as follows:

```
module ParityExample where

  open Data.Bool
  open Data.Nat
  open Data.Nat.Properties
  open Data.Fin hiding (_+_)
  open Data.List
  open Data.Product

  parity₁ : ℕ → Bool
  parity₁ 0 = true
  parity₁ (suc n) = not (parity₁ n)
```

However, this version suffers from [boolean blindness](https://existentialtype.wordpress.com/2011/03/15/boolean-blindness/). A more informative definition would go as follows:

```
  data Parity : Set where
    odd : Parity
    even : Parity

  parity₂ : ℕ → Parity
  parity₂ zero = even
  parity₂ (suc n) with parity₂ n
  ...                | odd = even
  ...                | even = odd
```

Now at least we can tell what `parity₂` is supposed to compute, but there is still missing mathematical content. Parity is about computing the lowest bit of a number. Expressed as a theorem, it says this:

:::{prf:theorem}
:nonumber: true

For every natural number $n \in \mathbb{N}$ there are $k \in \mathbb{N}$ and $b \in \{0, 1\}$ such that $n = 2 k + b$.

:::

We can use `Σ`-types to express the theorem in Agda:

```
  parity₃ : (n : ℕ) → Σ[ k ∈ ℕ ] Σ[ b ∈ Fin 2 ] (n ≡ 2 * k + toℕ b)
  parity₃ zero = 0 , zero , refl
  parity₃ (suc n) with parity₃ n
  ... | k , zero , ξ = k , (suc zero) , ζ
    where
      open ≡-Reasoning
      ζ : suc n ≡ k + (k + 0) + 1
      ζ = begin
            suc n                  ≡⟨ cong suc ξ ⟩
            suc (k + (k + 0) + 0)  ≡⟨ sym (+-suc _ _) ⟩
            k + (k + 0) + 1
          ∎
  ... | k , suc zero , ξ = (suc k) , zero , ζ
    where
      open ≡-Reasoning
      χ : k + (k + 0) + 1 ≡ k + (suc k + 0)
      χ = begin
            k + (k + 0) + 1    ≡⟨ +-assoc k (k + 0) 1 ⟩
            k + (k + 0 + 1)    ≡⟨ cong (k +_) (trans (+-assoc k 0 1) (+-suc k 0)) ⟩
            k + (suc k + 0)
          ∎

      ζ : suc n ≡ suc k + (suc k + 0) + 0
      ζ = begin
            suc n                   ≡⟨ cong suc ξ ⟩
            suc (k + (k + 0) + 1)   ≡⟨ cong suc χ ⟩
            suc (k + (suc k + 0))   ≡⟨ sym (+-identityʳ (suc (k + (suc k + 0)))) ⟩
            suc k + (suc k + 0) + 0
          ∎
```

We shall not dwell on the intricacies of the above equational proofs. The point of this example is rather that `Σ`-types can be used to package up information, in this case `k : ℕ`, `b : Fin 2` and a proof of `n ≡ 2 * k + toℕ b`.


### Dependent products (`Π`-types)

We already spoke about **dependent function types** in the last lecture. These are also known as **dependent products** and **`Π`-types**.
Recall that, given a type family `B : A → Set` we can form the type `(x : A) → B x` whose elements are function `f` taking each `x : A` to an element `f x : B x`.

The dependent function type is sometimes written as $\Pi (x : A) \,.\, B(x)$. We can introduce the same notation in Agda:

```
Π : (A : Set) → (A → Set) → Set
Π A B = (x : A) → B x

syntax Π A (λ x → B) = Π[ x ∈ A ] B
```


### Simple versus dependent

The **simple products** `A × B` and **simple sums** `A + B` are special cases of dependent sums and products. The correspondence can be a bit confusing from a terminological point of view because we can get `A × B` from `Σ` and `Π` in two ways:

* by applying `Σ` and `Π` to constant families
* by applying `Σ` and `Π` to a family `Bool → Set`

Let us explain these.

```
module ×-as-Π where
  open Data.Bool
  open Data.Product
```

Given types `A` and `B`, we define a family map `A ∥ B : Bool → Set` which takes `false` to `A` and `true` to `B`:

```
  _∥_ : Set → Set → Bool → Set
  (A ∥ B) false = A
  (A ∥ B) true = B
```

In the Agda standard library `A × B` is defined to be the dependent sum of the constant
family; `A × B = Σ [ x ∈ A ] B`. Let us show that `A × B` is isomorphic to `Π Bool (A ∥
B)`:

```
  ϕ : {A B : Set} → A × B → Π Bool (A ∥ B)
  ϕ (x , y) = λ { false → x ; true → y }

  ψ : {A B : Set} → Π _ (A ∥ B) → A × B
  ψ f = f false , f true
```

It is not hard to verify that `ψ (ϕ p) ≡ p` for all `p : A × B`:

```
  inverse-ψ-ϕ : {A B : Set} (p : A × B) → ψ (ϕ p) ≡ p
  inverse-ψ-ϕ (x , y) = refl
```

However, the reverse equation is not so easy. It depends on the principle of function extensionality.


:::{prf:definition} Function extensionality
:nonumber: true

Given $f, g : Π (x : A) \,.\, B(x)$, if $f(x) = g(x)$ for all $x \in A$ then $f = g$.

```
  postulate funext : {X : Set} {Y : X → Set} (f g : Π[ x ∈ X ] Y x) → ((x : X) → f x ≡ g x) → f ≡ g
```
:::

Function extensionality cannot be established in Agda. We *postulated* it above as an axiom, using the [`postulate` declaration](https://agda.readthedocs.io/en/latest/language/postulates.html).

```
  inverse-ϕ-ψ : {A B : Set} (f : Π _ (A ∥ B)) → ϕ (ψ f) ≡ f
  inverse-ϕ-ψ f = funext (ϕ (ψ f)) f (λ { false → refl ; true → refl })
```


:::{admonition} Exercise

Above we showed that `A × B` may be constructed either as `Σ[ x ∈ A ] B` or `Π Bool (A ∥
B)`. There are two additional possibilities:

1. the dependent product of the constant family `Π[ x ∈ A ] B`,
2. the dependent sum `Σ Bool (A ∥ B)` of the family `A ∥ B : Bool → Set`.

Which previously known constructions correspond to these? Construct suitable isomorphisms
to verify your answers.

:::


An isomorphism, such as the one above, has four parts: two functions, and two proofs of equality. It would be convenient to package them all together, which we can do using `Σ`-types:

```
  _≅_ : Set → Set → Set
  A ≅ B = Σ[ ϕ ∈ (A → B) ] Σ[ ψ ∈ (B → A) ] ((x : A) → ψ (ϕ x) ≡ x) × ((y : B) → ϕ (ψ y) ≡ y)
```

(This is a *triple* nested `Σ`-type because the inner `×` is a shorthand for `Σ`.)

Such nested dependent sums can get unwieldy. There is a better construction, namely record types, which are better suited for structuring mathematical and programming concepts. In fact, `Σ` is defined to be a record type.


## Record types

The elements of a simple product `A × B` are pairs `(a, b)`, which have two components, the *first* and the *second* component. We often give these components names, for example the real and imaginary parts of a complex number. Products whose components have names are called **record types**.

When the type of one component may depend on the previous components, we speak of **dependent record types**. These are supported by Agda.

:::{seealso}

Agda documentation on [record types](https://agda.readthedocs.io/en/latest/language/record-types.html).

:::

We shall learn how to work with record types by way of an example.

### Gaussian integers

A [Gaussian integer](https://en.wikipedia.org/wiki/Gaussian_integer) is a complex number whose real and imaginary parts are integers. Let us define them in Agda, using record types.

```
module GaussianIntegers where

  open import Data.Integer

  record ℤ[𝕚] : Set where
    constructor ⟨_,_⟩
    field
      re : ℤ
      im : ℤ
```

The above definition defines a record type `ℤ[𝕚]` (that's a single symbol) which has:

* A **constructor** `⟨_,_⟩` which allows us to form a Gaussian integer by writing `⟨ a , b ⟩`. The constructor may be omitted, in which case we can still form the record using the syntax `record { re = ... ; im = ... }`.

* The **fields** `re` and `im`, which are integers.

A record type is also a module (did you read the Agda documentation on record types, linked to above?). We can open it to get access to its parts:


```
  open ℤ[𝕚]
```

Now we can write `re` and `im` instead of `ℤ[𝕚].re` and `ℤ[𝕚].im`.
Next, let us define addition, subtraction, and multiplication of Gaussian integers. We use two different styles to showcase the possibilities. Addition is defined using the `record { ... }` notation:


```
  _+ᴳ_ : ℤ[𝕚] → ℤ[𝕚] → ℤ[𝕚]
  x +ᴳ y = record { re = re x + re y ; im = im x + im y }
```

Subtraction is defined using the constructor `⟨_,_⟩` and patterns:

```
  _-ᴳ_ : ℤ[𝕚] → ℤ[𝕚] → ℤ[𝕚]
  ⟨ x₁ , x₂ ⟩ -ᴳ ⟨ y₁ , y₂ ⟩ = ⟨ x₁ - y₁ , x₂ - y₂ ⟩
```

And here is multiplication, using [copatterns](https://agda.readthedocs.io/en/latest/language/copatterns.html):

```
  _*ᴳ_ : ℤ[𝕚] → ℤ[𝕚] → ℤ[𝕚]
  re (x *ᴳ y) = re x * re y - im x * im y
  im (x *ᴳ y) = re x * im y + im x * re y
```

You will learn the pros and cons of using copatterns in the exercises.

Let us define `𝕚` and show that its square is `-1`  (`+ n` is the notation used to write down a non-negative integer, and `-[1+ n ]` to write done the negative integer `-(1+n)`):

```
  𝕚 : ℤ[𝕚]
  𝕚 = ⟨ + 0 , + 1 ⟩

  𝕚²≡1 : 𝕚 *ᴳ 𝕚 ≡ ⟨ -[1+ 0 ] , + 0 ⟩
  𝕚²≡1 = cong₂ ⟨_,_⟩ refl refl
```

### The unit type as a record type

Before proceeding to the next example, let's take another peek at the definition of the unit type. It's a record with a constructor and no fields:

```
open import Data.Unit
look-at-me = ⊤
```

One noteworthy difference between `T` as a record type and the inductive datatype definition

```
data ⊤' : Set where
  ⋆ : ⊤'
```

is that the **extensionality principle for records** (also called **η-rule**) makes `⊤` better behaved. The principle says that two records are equal if they have the same fields. Since `⊤` has no fields, all element of `⊤` are equal, so the following works:

```
all-equal-⊤ : (x y : ⊤) → x ≡ y
all-equal-⊤ x y = refl
```

With the inductive version the story is different. There we use the principle that the type is generated by the constructors: in order to show that a statement holds for all elements of `⊤'`, we need to its constructors:

```
all-equal-⊤' : (x y : ⊤') → x ≡ y
all-equal-⊤' ⋆ ⋆ = refl
```

The above would not work if we kept `x` and `y` instead of replacing them with `⋆`.

:::{seealso}

If you are curious about the `instance` in the definition of `⊤`, consult Agda documentation on [constructor instances](https://agda.readthedocs.io/en/latest/language/instance-arguments.html#constructor-instances). However, this is a rather technical topic that you can safely skip on the first reading.

:::


### Isomorphisms

We observed above that isomorphisms consist of four parts. We can pack these into a record type.

```
module Isomorphisms where

  infix 0 _≃_

  record _≃_ (A B : Set) : Set where
    field
      to      : A → B
      from    : B → A
      from∘to : (x : A) → from (to x) ≡ x
      to∘from : (y : B) → to (from y) ≡ y
```

:::{seealso}

PLFA has a chapter on [isomorphisms](https://plfa.github.io/Isomorphism/).

:::

We can package up the isomorphism from above:

```
  open Data.Product
  open ×-as-Π
  open _≃_

  ×-iso-Π : {A B : Set} → A × B ≃ Π _ (A ∥ B)
  ×-iso-Π {A} {B} =
    record
      { to = ϕ
      ; from = ψ
      ; from∘to = inverse-ψ-ϕ
      ; to∘from = inverse-ϕ-ψ
      }
```

The identity isomorphism, defined using copatterns:

```
  𝟙 : {A : Set} → A ≃ A
  to 𝟙 = λ x → x
  from 𝟙 = λ x → x
  from∘to 𝟙 = λ x → refl
  to∘from 𝟙 = λ y → refl
```

The inverse isomorphism:

```
  _⁻¹ : {A B : Set} → A ≃ B → B ≃ A
  f ⁻¹ =
    record
    { to = from f
    ; from = to f
    ; from∘to = to∘from f
    ; to∘from = from∘to f
    }
```

Composition of isomorphisms is an isomorphism, using copatterns:

```
  open ≡-Reasoning

  infixl 5 _∘_

  _∘_ : {A B C : Set} → B ≃ C → A ≃ B → A ≃ C

  to (g ∘ f) = λ x → to g (to f x)

  from (g ∘ f) = λ y → from f (from g y)

  from∘to (g ∘ f) x =
    begin
      from (g ∘ f) (to (g ∘ f) x)  ≡⟨ cong (from f) (from∘to g _) ⟩
      from f (to f x)              ≡⟨ from∘to f _ ⟩
      x
    ∎

  to∘from (g ∘ f) y =
    begin
      to (g ∘ f) (from (g ∘ f) y)  ≡⟨ cong (to g) (to∘from f _) ⟩
      to g (from g y)              ≡⟨ to∘from g _ ⟩
      y
      ∎
```

### Decidable equality

In our last example we shall formalize types with decidable equality.

```
module DecidableEquality where

  open Data.Empty
  open Data.Nat
  open Data.Product
  open Data.List
```

:::{prf:definition} Decidable type
:nonumber: true

A type `A` is **decidable** if either it has an element, or it is empty.

:::

The above definition may seem odd, for is it not the case that every type either has an element or is empty? Well, yes, in the sense that we can never find a type which neither has an element nor is it empty. But in Agda we need to provide *evidence* of “has an element or is empty”. And since all evidence that can be written in Agda is computable, the above definition should be understood algorithmically: we can compute whether `A` is inhabited.

Here is the definition of decidable sets:

```
  data Dec (A : Set) : Set where
    yes : A → Dec A
    no  : (A → ⊥) → Dec A
```

:::{prf:example}
:nonumber: true

The computational aspect of decidability comes to light when we consider a type family `B : A → Set` and the statement “for all `x : A` the type `B x` is decidable”. You should contemplate the following question: is it the case that every `f : ℕ → Bool` either attains value `true` or does not?

```
  module AttainsTrue where
    open Data.Bool
    open Data.Product
    open Data.Nat

    attains-true : (ℕ → Bool) → Set
    attains-true f = Σ[ n ∈ ℕ ] f n ≡ true

    can-you-prove-this = (f : ℕ → Bool) → Dec (attains-true f)
```
:::

Of special importance are types whose equality relation is decidable:

:::{prf:definition} Decidable type
:nonumber: yes

A type `A` has **decidable equality** when for all `x, y : A`, the type `x ≡ y` is decidable.

:::

In words, a type has decidable equality if there is a *testing* function which takes `x` and `y` and decides whether `x ≡ y`.
We may define the notion of a type with decidable equality in Agda as a record type:

```
  record DecSet : Set₁ where
    field
      DSet   : Set
      test-≡ : (x y : DSet) → Dec (x ≡ y)

  open DecSet
```

As an exercise, let us show that the natural numbers have decidable equality:

```
  Dec-ℕ : DecSet
  Dec-ℕ =
    record
      { DSet = ℕ
      ; test-≡ = t
      }
    where
      t : (m n : ℕ) → Dec (m ≡ n)
      t zero zero = yes refl
      t zero (suc n) = no (λ ())
      t (suc m) zero = no (λ ())
      t (suc m) (suc n) with t m n
      ...                  | yes refl = yes refl
      ...                  | no p     = no (λ { refl → p refl })
```

Another exercise: if `A` and `B` have decidable equality then so does `A × B`:

```
  Dec-× : DecSet → DecSet → DecSet
  DSet (Dec-× A B) = DSet A × DSet B
  test-≡ (Dec-× A B) (x₁ , x₂) (y₁ , y₂) with test-≡ A x₁ y₁ | test-≡ B x₂ y₂
  ... | yes refl | yes refl = yes refl
  ... | yes refl | no p     = no (λ { refl → p refl})
  ... | no p     | _        = no (λ { refl → p refl })
```

For at least somewhat useful exercise, we implement a function `add` which adds an element to a list, but only if the
element does not appear in the list already. Because we need to test elements for equality, the underlying type must
have decidable equality.

```
  add : {A : DecSet} → List (DSet A) → DSet A → List (DSet A)
  add [] a = a ∷ []
  add {A} (x ∷ xs) a with test-≡ A a x 
  ... | yes _ = x ∷ xs
  ... | no _ = x ∷ add {A} xs a
```

Notice that the following holds: if the list `xs` has no duplicates, then `add xs x` has not duplicates either. You will prove this in the exercises to get a taste of how formal verification of data structures and algorithms works.

:::{seealso}

Study decidable predicates and equality in the Agda standard library:

```
module StudyThese where

  import Relation.Nullary
  import Relation.Binary

  decidable-predicate = Relation.Nullary.Dec
  decidable-equality = Relation.Binary.DecidableEquality

```
:::
