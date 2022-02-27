# Dependent types

In the second lecture we shall:

* Take a more systematic look at type theory and how we can use it to prove properties of functions.
* Pay special attention to equality
* Learn how to use the [Agda standard library](https://agda.github.io/agda-stdlib/) and several new Agda features.

Supplementary reading materaial for this lecture:

* [PLFA](https://plfa.github.io)
  * [Equality: Equality and eqational reasoning](https://plfa.github.io/Equality/)
  * The section “Lambda expressions”., “Function composition” and “Extensionality” from [Isomorphism: Isomorphism and Embedding](https://plfa.github.io/Isomorphism/)
* [IUFMA](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html):
  * [The one-element type `𝟙`](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#onepointtype)
  * [The empty type `𝟘`](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#emptytype)
  * [The binary sum type constructor `_+_`](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#binarysum)
  * [The identity type former `Id`, also written `_≡_`](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#identitytype)
  * [Basic constructions with the identity type](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#basicidentity)

## Importing modules with `import`

Rather than defining everything from scracth, let us include the definition of natural numbers and lists from the standard library.
This is done with the [`import` statement](https://agda.readthedocs.io/en/latest/language/module-system.html#splitting-a-program-over-multiple-files).

```
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _⊔_; _≤_; z≤n; s≤s; _≡ᵇ_)
open import Data.List using (List; []; _∷_; length)
```

You should read the following documentation to learn what `open` and `using` do:

* [Basics of modules](https://agda.readthedocs.io/en/latest/language/module-system.html#basics) explains `open`
* [Name modifiers](https://agda.readthedocs.io/en/latest/language/module-system.html#name-modifiers) explains `using`, as well as `renaming` and `hiding`.

In summary, the above two lines import specific parts of the modules `Data.Nat` and `Data.List` from the standard library. Here is one more, it imports the definition of the identity map and composition from the `Function` module (without `using`, the `import` statement imports the entire contents of the module).

```
open import Function using (id; _∘_)
```

We must also declare the module for the present lecture:

```
module 02-dependent-types where
```

## Simple and dependent types

You might be familiar with types from programming languages, such as `int`, `float`, `bool`, `int → int`, etc. These are called **simple** or **non-dependent types**. Let us practice defining them in Agda.


### Unit type

The unit type has a single element. In Agda it is called `⊤` because it also doubles for the true proposition (not to be confused with `true` which is an element of `Bool`):

```
data ⊤ : Set where
  ⋆ : ⊤

f_unit : ⊤ → ℕ 
f_unit ⋆ = 42
```

This definition is a bit different from the one in the standard library, which uses a `record` type. We will learn about those next time. Anyhow, you should compare the above definition with the one in the standard library:

```
import Agda.Builtin.Unit
```

The way to inspect the module is to load this file, place the cursor on the work `Unit`, and press “Alt-.” or “F12” to visit the module. You come back by pressing “Alt-,” or “Ctrl -”.

### Empty type

The empty type is the inductive type without any constructors. In Agda it is called `⊥` because it also doubles as falsehood.

```
data ⊥ : Set where
```

This time our definition agrees with that of the standard library:

```
import Data.Empty
```

It is instructive to define a map from the empty type to any other one;

```
from-empty : {A : Set} → ⊥ → A
from-empty ()
```

What happened? Agda determined that the definition does not require any cases (because there are no constructors for `⊥`), which it indicated with the notation `()`.

### Disjoint sums

A disjoint sum of types `A` and `B` is a type `A ⊎ B` (often written outside Agda as `A + B`) whose elements are of the form `inj₁ a` for `a : A` and `inj₂ b` for `b : B`. Let us see how this is defined in the standard library:

```
open import Data.Sum.Base
```

Notice that the standard library uses [universe levels](https://agda.readthedocs.io/en/latest/language/sort-system.html#introduction-to-universes) which we should get used to, but not right now.


### Cartesian products

The cartesian product of types `A` and `B` is the type `A × B` of ordered pairs `(a, b)` where `a : A` and `b : B`. It
is defined using records, which we have not yet learned about. Nevertheless, it does not hurt to take a quick look at the
definition in the standard library:

```
import Data.Product
```

This was weird. The product is defined in terms of something called `Σ`. We shall come back to it.


### Option type

In programming one often requires a value that signifies “no value” or “undefined”. That is, given a type `A` we construct a new type which has all the values of `A` (appropriately tagged so we can tell they came from `A`) and one additional “nothing” value. This is known as the **option type** and is defined as follows:

```
data Maybe' (A : Set) : Set where
  just'    : A → Maybe' A
  nothing' : Maybe' A
```

We used apostrophes in order to not encroach on the definition from the standard library:

```
import Agda.Builtin.Maybe
```

There are several modules involving `Maybe`, we imported the one that has the actual definition of the `Maybe` type. In practice you would import the following module to work with `Maybe`, as it contains more useful constructions.

```
open import Data.Maybe
```

The standard library is like an onion, with many layers that bring tears to one's eyes.


### Function types

The function type `A → B` of functions from `A` to `B` is built into Agda. Basic operations on functions are defined in the module `Functions`, which we already imported above.

You should familiarize yourself with [Lambda abstraction](https://agda.readthedocs.io/en/latest/language/lambda-abstraction.html), which is a notation for writing down functions. In mathematics we write a function as $x \mapsto e$ and read this as “$x$ maps to $e$”. In Agda the notation is `λ x → e`. You can read more about it in the section “Lambda expressions” of [Isomorphism: Isomorphism and Embedding](https://plfa.github.io/Isomorphism/) (PLFA).


## Dependent types

Dependent types capture a notion that is present everywhere in mathematics, even though students (and often their teachers) are not explicitly aware of its ubiquity and importance. Dependent types are a very powerful tool.

Let us pretend for a moment that types are just sets (what precisely is [the difference](https://cs.stackexchange.com/a/91345/1329), you ask?) and someone writes:

> Let $a, b \in \mathbb{R}$ be real numbers such that $a < b$. Consider a continuous map $f : [a, b] \to \mathbb{R}$.

Two sets are mentioned in the above text:

1. The set of real numbers $\mathbb{R}$. This one is **non-dependent** or **simple**.
2. The closed interval $[a, b]$. This one **depends** on parameters $a$ and $b$.

There is not one fixed set called “closed interval”, but rather a whole *family* of them:

$$[\_,\_] : \{ (a, b) \in \mathbb{R} \times \mathbb{R} \mid a < b\} \to \mathsf{Set}$$

Other examples of such dependencies are:

* the $n$-dimensional space $\mathbb{R}^n$ depends on the natural number $n$,
* the finite field $\mathbb{Z}_p$ depends on the prime number $p$,
* exercise: give one more example from mathematical practice

In general, a **family of sets** $A$ is a map from an indexing set to the class of all sets:

$$A : I \to \mathsf{Set}$$

Likewise, in Agda a **type family** is a map `A : I → Set`. Another name for `A` is **dependent type** (indexed by `I`).

### Dependent function types

Given a dependent type `A : I → Set` we may form the **dependent function type** `(i : I) → A i`. An element of this type is a function mapping each `i : I` to an element of `A i`. Another name for the type is **dependent product** because we can think of it as the cartesian product of all the `A i`'s.

Speaking set-theoretically, the corresponding construction is the cartesian product of a family: given a family of sets $A : I \to \mathsf{Set}$, its product is

$$\prod_{i \in I} A_i = \{ f \mid \forall i \in I \,.\, f(i) \in A_i \}.$$

We already used dependent function types, but now we have a name for them. Also note that the non-dependent function type `A → B` is a special case of the dependent function type where `B` is the constant type family.


### Standard finite types

Let us define for each natural number `n` the **standard finite type** `Fin n` with precisely `n` elements called
`zero'`, `suc' zero'`, `suc' (suc' zero')`, ..., `suc' (suc' ... (suc' zero')`:

```
data Fin' : ℕ → Set where
  zero' : {n : ℕ} → Fin' (suc n)
  suc'  : {n : ℕ} (i : Fin' n) → Fin' (suc n)
```

Note that `zero'` and `zero` are two different things: one is the constructor for `Fin n` and the other for `ℕ`; and similarly for `suc'` and `suc`. The Agda standard library already defined `Fin` so we shall use that one instead:

```
open import Data.Fin hiding (_+_) renaming (zero to zero'; suc to suc')
```

Note that the Agda standard library uses `zero` and `suc` for both `ℕ` and `Fin`. We used `renaming` to rename the `Fin` constructors,
and `hiding` to prevent `_+_` from `Data.Fin` clobbering `_+_` from `Nat`.


#### An example using `Fin` and `Maybe`

Let work through a realistic example that uses the both the finite types and the option
type. We would like to implement a search procedure which takes a boolean predicate `p :
Fin n → Bool` and returns `k : Fin n` such that `p k` is `true`. Actually, that is not
correct, because there may be no such `k`, so we should really ask for a result of type
`Maybe (Fin n)`, so that we may return `nothing` if no such `k` is found.

To give you some idea of what we are after, here are two Python implementations of the search function:

* `search` is implemented in idiomaticy Python using loops
* `find` is how we are going to implement it in Agda

:::{literalinclude} find.py
:language: python
:::

(Yes, `find` is convoluted, because it is designed to be recursive in a way that Agda understands it.)

We will implement the function three times, in order to learn Agda techniques. We need Booleans:

```
open import Data.Bool
```

The first solution is quite clumsy, because it uses auxiliary functions where in Python we simply used conditional statements:

```
find₁ : (n : ℕ) → (p : Fin n → Bool) → Maybe (Fin n)
find₁ zero p = nothing
find₁ (suc n) p = try₀ (p zero')
  where
    more-cases : Maybe (Fin n) → Maybe (Fin (suc n))
    more-cases (just x) = just (suc' x)
    more-cases nothing = nothing

    try₀ : Bool → Maybe (Fin (suc n))
    try₀ false = more-cases (find₁ n (p ∘ suc'))
    try₀ true = just zero'
```

It is quite common to consider cases and act on them, so Agda provides special [`with` abstraction](https://agda.readthedocs.io/en/latest/language/with-abstraction.html):

```
find₂ : (n : ℕ) → (p : Fin n → Bool) → Maybe (Fin n)
find₂ zero p = nothing
find₂ (suc n) p with p zero' | find₂ n (p ∘ suc')
... | false | just x = just (suc' x)
... | false | nothing = nothing
... | true | s = just zero' 
```

Agda also has `if_then_else_`, which we can combine with `Data.Maybe.map` to give a solution
that is looks more like a program and less like black magic:

```
find₃ : (n : ℕ) → (p : Fin n → Bool) → Maybe (Fin n)
find₃ zero p = nothing
find₃ (suc n) p = if p zero' then just zero' else Data.Maybe.map suc' (find₃ n (p ∘ suc'))
```

For example, we can search for square roots like this:

```
find-sqrt : (n : ℕ) → Maybe ℕ
find-sqrt n = Data.Maybe.map toℕ (find₁ (suc n) (λ k → toℕ k * toℕ k ≡ᵇ n))

just-eleven = find-sqrt 121
```

While we could perfectly well implement search, it suffers from a deficiency: it returns a result, but no evidence that the result is correct. We should either prove that our functions work correctly, or have them directly return results with proofs of correctness. But let us move on and save that exercise for the future.

### Vectors

The dependent version of lists are the vectors, which are like lists whose size is stored in the type, hence vectors form a *dependent* type:

```
infixr 5 _∷ⱽ_

data Vec (A : Set) : ℕ → Set where
  []ⱽ  : Vec A zero
  _∷ⱽ_ : {n : ℕ} → (x : A) → (xs : Vec A n) → Vec A (suc n)
```

When a vector is defined, its length is calculated by Agda (change `3` in `Vec ℕ 3` to `?` and let Agda fill it in):

```
one-two-three : Vec ℕ 3
one-two-three = 1 ∷ⱽ 2 ∷ⱽ 3 ∷ⱽ []ⱽ
```

### Comparison of lists and vectors

To contrast working with lists and vectors we look at how to define basic operations on them. The main difference is in the handling of size: any operation on vectors automatically keeps track of the size of the resulting vector.

The `map` function, which applies a given function `f` to the elements of a list or a vector looks the same in both cases:

```
list-map : {A B : Set} → (A → B) → List A → List B
list-map f [] = []
list-map f (x ∷ xs) = f x ∷ list-map f xs

vec-map : {A B : Set} → (A → B) → {n : ℕ} → Vec A n → Vec B n
vec-map f []ⱽ = []ⱽ
vec-map f (x ∷ⱽ xs) = f x ∷ⱽ vec-map f xs
```

Concatenation of lists and vectors is still pretty much the same, except that we need to keep track of the size of vectors:

```
infixl 5 _++_
_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)


infixl 5 _++ⱽ_
_++ⱽ_ : {A : Set} → {k m : ℕ} → Vec A k → Vec A m → Vec A (k + m)
[]ⱽ ++ⱽ ys = ys
(x ∷ⱽ xs) ++ⱽ ys = x ∷ⱽ (xs ++ⱽ ys)
```

Next, here is how we can define the reversal of a list:

```
private
  list-rev : {A : Set} → List A → List A → List A
  list-rev xs [] = xs
  list-rev xs (x ∷ ys) = list-rev (x ∷ xs) ys

list-reverse : {A : Set} → List A → List A
list-reverse {A} xs = list-rev [] xs
```

Above we defined the auxiliary function `list-rev` globally because we shall refer to it later. Note that it is marked `private` so that it becomes invisible outside the module. It is always a good idea to hide any auxiliary definitions that are not meant to for public consumption.

We get stuck when trying to reverse vectors. In the second clause for `rev` we have the goal `Vec A (k + 0)` which we would like to fill with `xs : Vec A k`, but Agda does not allow that because the types `Vec A (k + 0` and `Vec A k` are not equal.
In the third clause it refuses to see that `Vec A (k + suc n)` and `Vec A (suc (k + n))` are equal.

```
-- vec-reverse-stuck : {A : Set} → {n : ℕ} → Vec A n → Vec A n
-- vec-reverse-stuck {A} xs = rev []ⱽ xs
--   where
--     rev : {k m : ℕ} → Vec A k → Vec A m → Vec A (k + m)
--     rev xs []ⱽ = {!xs!}
--     rev xs (x ∷ⱽ ys) = {!rev (x ∷ⱽ xs) ys !}
```

We must deal with equality first.

## The identity type

The identity type is a dependent type which represents the equality relation. It is also an inductive type whose only constructor is `refl`, witnessing reflexivity. The chapter [Equality: Equality and eqational reasoning](https://plfa.github.io/Equality/) from PLFA explains the idea behind the identity type in more detail.

Let us import Agda's definition of the identity type, which is written as `_≡_`, as well as the module defining the special type `Level` of universe levels.

```
open import Relation.Binary.PropositionalEquality
open import Level hiding (_⊔_; suc)
```

### A quick explanation of universes

It is quite natural to think there should be the “type of types”. Such a type is called a **universe**. However, as was famously discovered by Jean-Yves Girad, the [Bourali-Forti paradox](https://ncatlab.org/nlab/show/Burali-Forti%27s+paradox#GirardParadox) arises in a type theory with a universe that contains all types, including itself.

Consequently, the type theory of Agda (and Coq and Lean) contains not just a single universe of types, but a whole hierachy of them, where the $n$-th universe is an element of the $(n+1)$-st universe.

In Agda, the `n`-th universe is `Set n`. So far we only ever used `Set`, which is a synonym for the lowest universe `Set 0`. Henceforth we shall use universes in general. Note that the `n` in `Set n` is *not* a natural number but rather an element of a special type `Level`!

### The basic properties of the identity type

The identity type may be read as a binary relation. It is an equivalence relation:

```
sym' : {ℓ : Level} → {A : Set ℓ} {x y : A} → x ≡ y → y ≡ x
sym' refl = refl

trans' : {ℓ : Level} → {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans' refl q = q
```

Equality is a **congruence** for any function (in algebra, a *congruence* is a relation
that is preserved by the algebraic operations):

```
cong' : {ℓ : Level} → {A B : Set ℓ} → (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong' = cong
```

Equality is **substitutive**: if $x = y$ and $P(x)$ holds then $y$ may be substituted for $x$ to obtain $P(y)$:

```
subst' : {ℓ : Level} {A : Set ℓ} {k : Level} (P : A → Set k) {x y : A} → x ≡ y → P x → P y
subst' = subst -- also called resp
```

It take a bit of exercise and practice to learn how to use these properties of equality. Agda has additional support for educational reasoning, which we look at next.

### Chains of equational reasoning.

Suppose we want to prove `a ≡ d` by performing several reasoning steps `a ≡ b ≡ c ≡ d`. We can do so using transitivity:

```
abcd-chain₁ : {A : Set} {a b c d : A} → a ≡ b → b ≡ c → c ≡ d → a ≡ d
abcd-chain₁ α β γ = trans α (trans β γ)
```

More complicated proofs may chain together several applications of `trans` and can get unreadable. To make the proofs
easier to read and write, the Agda standard library contains the functions `begin_`, `_≡⟨⟩_` and `_∎` which allow us to
display such proofs by transitivity in a more pleasant way.

```
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; subst; resp)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat.Properties


abcd-chain₂ : {A : Set} {a b c d : A} → a ≡ b → b ≡ c → c ≡ d → a ≡ d
abcd-chain₂ {A} {a} {b} {c} {d} α β γ =
  begin
    a ≡⟨ α ⟩
    b ≡⟨ β ⟩
    c ≡⟨ γ ⟩
    d
  ∎
```

Here is a slightly less artificial example:

```
some-example : {a b c : ℕ} → (a + b) * c ≡ c * b + c * a
some-example {a} {b} {c} =
  begin
    (a + b) * c      ≡⟨ *-distribʳ-+ c a b ⟩
    a * c + b * c    ≡⟨ +-comm (a * c) (b * c) ⟩
    b * c + a * c    ≡⟨ cong ((b * c) +_) (*-comm a c) ⟩
    b * c + c * a    ≡⟨ cong (_+ (c * a)) (*-comm b c) ⟩
    c * b + c * a
  ∎
```

## Proving properties of data structures and functions


Armed with the identity type, let us see how it can be used to prove properties of functions.

### Trees

To start with something simple, we consider binary trees whose nodes (but not leaves) are
labelled with the elements of a type `A`:

```
data Tree (A : Set) : Set where
  leaf : Tree A
  node : Tree A → A → Tree A → Tree A
```

The depth of a tree:

```
depth : {A : Set} → Tree A → ℕ
depth leaf = 0
depth (node ℓ x r) = suc ((depth ℓ) ⊔ (depth r))
```

Do you know how what `⊔` is? Move the cursor on it and press `F12` or `Alt-.` to visit its definition.

The full tree of depth `n`

```
full : ℕ → Tree ⊤
full zero = leaf
full (suc n) = node (full n) ⋆ (full n)
```

For practice, let us show that the depth of `full n` is indeed `n`.

```
depth-full : (n : ℕ) → depth (full n) ≡ n
depth-full 0 = refl
depth-full (suc n) =
  cong suc
  (begin
     depth (full n) ⊔ depth (full n) ≡⟨ ⊔-idem (depth (full n)) ⟩
     depth (full n)                  ≡⟨ depth-full n ⟩
     n
   ∎)
```


### Revisiting the vectors

Remember, we got stuck on defining the reverse of a vector because we did not know how to substitute numbers for equal
numbers, but now we do:

```
vec-reverse : {A : Set} → {n : ℕ} → Vec A n → Vec A n
vec-reverse {A} xs = rev []ⱽ xs
  where
    rev : {k m : ℕ} → Vec A k → Vec A m → Vec A (k + m)
    rev xs []ⱽ = subst (Vec A) (sym (+-identityʳ _)) xs
    rev xs (x ∷ⱽ ys) = subst (Vec A) (sym (+-suc _ _)) (rev (x ∷ⱽ xs) ys)
```

The second clause of `rev` uses `subst` to *rewrite* `xs : Vec k` to an element of `Vec (k + 0)`. As this is a common operation, Agda supports it directly with the ([`rewrite`] clause)[https://agda.readthedocs.io/en/latest/language/with-abstraction.html#with-rewrite]:

```
vec-reverse' : {A : Set} → {n : ℕ} → Vec A n → Vec A n
vec-reverse' {A} xs = rev []ⱽ xs
  where
    rev : {k m : ℕ} → Vec A k → Vec A m → Vec A (k + m)
    rev {k = k} xs []ⱽ rewrite +-identityʳ k = xs
    rev xs (x ∷ⱽ ys) = subst (Vec A) (sym (+-suc _ _)) (rev (x ∷ⱽ xs) ys)
```

### Intrinsic versus extrinsic properties of data structures


The implementation of data structures and functions that operate on them has two components:

* *definitions* of the data structure and the functions
* *proofs** of the desired properties of the data structures and the functions

For example, a binary search tree is a binary tree with the property that at every node, the nodes in the left (right) subtree are smaller (larger) than the root. In an standard programming language such trees are implemented as ordinary binary trees. The compiler does *not* check automatically that the property of being a search tree is preserved by the code.

With dependent types we can build the desired properties into the types themselves and make it impossible to construct an invalid search  tree. It becomes *impossible to write broken code*! You will explore this very interesting possibility in the exercises and class projects.

To summarize, we have two ways of implementing data structures and algorithms:

* **Exstrinsic:** The data structure and the functions are implemented separately from proofs of their properties. The proof of properties are written down separately.

* **Intrinsic:** The data structure and functons implement both the algorithm and its proof of correctness simultaneously.

We already saw an example, namely lists and vectors with the desired property “has length $n$”. List are extrinsic because the information about the length is not present in the type `List A`, whereas vectors are intrinsic because the length appears in `Vec A n`.

Consequently, the concatenation operator `_++_` for lists does not keep track of lengths, whereas `_++ⱽ_` does. A statement about the length of concatenated lists must be proved separately:

```
length-++ : {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
length-++ [] ys = refl
length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)
```

The same goes for the fact that reversal of lists preserves length:

```
-- private
--   list-rev : {A : Set} → List A → List A → List A
--   list-rev xs [] = xs
--   list-rev xs (x ∷ ys) = list-rev (x ∷ xs) ys

-- list-reverse : {A : Set} → List A → List A
-- list-reverse {A} xs = list-rev [] xs


length-reverse : {A : Set} {xs : List A} → length (list-reverse xs) ≡ length xs
length-reverse {A} {xs} = length-rev [] xs
  where
    length-rev : (us vs : List A) → length (list-rev us vs) ≡ length us + length vs
    length-rev us [] = sym (+-identityʳ (length us))
    length-rev us (x ∷ vs) =
      begin
        length (list-rev us (x ∷ vs))   ≡⟨ length-rev (x ∷ us) vs ⟩
        length (x ∷ us) + length vs     ≡⟨ sym (+-suc (length us) (length vs) ) ⟩
        length us + length (x ∷ vs)
      ∎
```

Judging just from these two examples, the intrinsic approach seems more principled and simpler. One should not rely too heavily on a statistical sample of size 2.

### Elements of a list

Let us define the relation “`x` is an element of the list `ℓ`”.


```
infix 3 _∈_

data _∈_ {A : Set} : A → List A → Set where
  ∈-here : {x : A} → {xs : List A} → x ∈ (x ∷ xs)
  ∈-there : {x y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs)
```

A proof that `5` is an element of `1 ∷ 2 ∷ 5 ∷ 2 ∷ []`:

```
element-example : 5 ∈ (1 ∷ 2 ∷ 5 ∷ 2 ∷ [])
element-example = ∈-there (∈-there ∈-here)
```

How do we prove that `4` is *not* an element of `1 ∷ 2 ∷ 5 ∷ 2 ∷ []`?
By showing that if it were, then false would hold (in other words, we use the fact that $\neg p$ is equivalent to $p \Rightarrow \bot$):

```
non-element-example₁ : (4 ∈ (1 ∷ 2 ∷ 5 ∷ 2 ∷ [])) → ⊥
non-element-example₁ (∈-there (∈-there (∈-there (∈-there ()))))

non-element-example₂ : (4 ∈ []) → ⊥
non-element-example₂ ()
```

Let us work through proofs showing the basic properties of `∈`. First, if a list contains an element then so does the reversed list:

```
∈-reverse : {A : Set} {x : A} {xs : List A} → x ∈ xs → x ∈ list-reverse xs
∈-reverse = ∈-rev-r _
  where
    ∈-rev-r : {A : Set} {x : A} (ys : List A) {zs : List A} → x ∈ zs → x ∈ list-rev ys zs
    ∈-rev-l : {A : Set} {x : A} {ys : List A} (zs : List A) → x ∈ ys → x ∈ list-rev ys zs

    ∈-rev-r ys {z ∷ zs} ∈-here = ∈-rev-l zs ∈-here
    ∈-rev-r ys {z ∷ zs} (∈-there p) = ∈-rev-r (z ∷ ys) p

    ∈-rev-l {ys = ys} [] p = p
    ∈-rev-l {ys = ys} (z ∷ zs) p = ∈-rev-l zs (∈-there p) 
```

Second, if `z` is an element of `xs` then it is also an element of `xs ++ ys`, and symmetrically for `ys`:

```
∈-++ʳ : {A : Set} {xs ys : List A} {z : A} → z ∈ ys → z ∈ xs ++ ys
∈-++ʳ {xs = []} p = p
∈-++ʳ {xs = x ∷ xs} p = ∈-there (∈-++ʳ p) 

∈-++ˡ : {A : Set} {xs ys : List A} {z : A} → z ∈ xs → z ∈ xs ++ ys
∈-++ˡ ∈-here = ∈-here
∈-++ˡ (∈-there p) = ∈-there ( ∈-++ˡ p)
```

Third, if `z` is an element of `xs ++ ys` then it is an element of `xs` or `ys`:

```
∈-++ : {A : Set} {xs ys : List A} {z : A} → z ∈ xs ++ ys → z ∈ xs ⊎ z ∈ ys
∈-++ {xs = []} p = inj₂ p 
∈-++ {xs = x ∷ xs} ∈-here = inj₁ ∈-here
∈-++ {xs = x ∷ xs} {ys} {z} (∈-there p) with ∈-++ p
...                                       | inj₁ x₁ = inj₁ (∈-there x₁)
...                                       | inj₂ y = inj₂ y

```

### Unit-testing with equality

The identity type may be used to conveniently write down tests that check correctness of functions, for example:

```

check-1 : 7 + 5 ≡ 12
check-1 = refl

check-2 : (1 ∷ 2 ∷ []) ++ (3 ∷ 4 ∷ []) ≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
check-2 = refl

check-3 : list-reverse ((1 ∷ 2 ∷ 3 ∷ []) ++ (4 ∷ 5 ∷ [])) ≡ list-reverse (4 ∷ 5 ∷ []) ++ list-reverse (1 ∷ 2 ∷ 3 ∷ [])
check-3 = refl
```

Programmers are used to writing such tests, which they call *unit tests*. But we can do much, much better and just prove
that the desired property holds for *all* cases. Can you do it?

```
reverse-++ : {A : Set} (xs ys : List A) → list-reverse (xs ++ ys) ≡ list-reverse ys ++ list-reverse xs
reverse-++ {A} xs ys = {!  !}
```
