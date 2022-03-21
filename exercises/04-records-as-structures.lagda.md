# Records as structures

In this lecture we shall practice using modules and records to formalize structures arising in computer
science and mathematics, namely dictionaries, monoids and monads. By doing so we

1. learn how to formally verify correctness of data structures,
2. learn how to formalize mathematics, and
3. appreciate what it takes to *really* verify correctness of statements that we often take for granted.

We begin with a bouquet of Agda modules, as ususal. Notice that most of the modules are
imported but not opened. We shall open them as needed in submodules.

```
open import Level        renaming (zero to lzero; suc to lsuc)
open import Data.Nat     using (ℕ; zero; suc; _+_; _*_)
import Data.Nat.Properties
import Data.List
import Data.List.Properties
import Data.Empty
import Data.Unit using (⊤; tt)
import Data.Maybe
import Data.Product
import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning      using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Function     using (id; _∘_)

module 04-records-as-structures where
```

## More about Agda Modules

Agda [module system](https://agda.readthedocs.io/en/latest/language/module-system.html) gives a flexible way of organizing code. Modules and records share some common features: they both contains named components, and they can be parameterized and nested. In fact, every record type defined a module, but not vice versa. They differ in their design: modules are intended to be used as units of code, whereas records are used as “structured data”.

### Nested modules

As you might have noticed already, modules can be nested:

```
module Foo where
  module Bar where
    private
      bull : ℕ
      bull = 20

      chicken : ℕ
      chicken = 21

    cow : ℕ
    cow = bull + chicken + 1
```

We can access `cow` from the outside by:

* writing `Foo.Bar.cow`, or
* `open Foo` and writing `Bar.cow`, or
* `open Foo.Bar` and writing `cow`.

We cannot access `bull` and `chicken` from outside module `Foo.Bar` because they are [`private` definitions](https://agda.readthedocs.io/en/latest/language/module-system.html#private-definitions).

Any `open` and `import` statements that are made inside a module are local to that module.

### Anonymous modules

An [anonymous module](https://agda.readthedocs.io/en/latest/language/module-system.html#anonymous-modules) is one whose name is `_`. It is used as a unit of organization,
for example, when several definitions share the same `private` definition or an `open` statement.

```
module Parrot where

  module _ where
    open Data.List -- valid inside this module

    private
      budgie : ℕ -- invisible outside this module
      budgie = 7

    foo : List ℕ
    foo = budgie ∷ []

    bar : List ℕ
    bar = budgie ∷ budgie ∷ []

  -- outside the anonymous module we have to write Data.List.length
  -- and we cannot access budgie
  baz : ℕ
  baz = Data.List.length bar
```

From outside, we can `Parrot.foo`, `Parrot.bar` and `Parrot.baz` (we do *not* write `Parrot._.foo`!)


### Parameterized modules

[Modules can take parameters](https://agda.readthedocs.io/en/latest/language/module-system.html#parameterised-modules):

```
module Rabbit (n : ℕ) where
  tail : ℕ
  tail = n + 7
```

Think of `Rabbit` as a map which takes a number and returns a module. Thus `Rabbit.tail`
is a function taking a number `n : ℕ` to `n + 7`. It can be accessed in several ways:

```
module _ where

  -- direct access
  small-tail : ℕ
  small-tail = Rabbit.tail 2 + Rabbit.tail 1

  -- open the module with a suplied fixed argument
  big-tail : ℕ
  big-tail = tail + tail   --- equal 107 + 107
    where open Rabbit 100

  -- open the module but do not supply the argument
  medium-tail : ℕ
  medium-tail = tail 10 + tail 20
    where open Rabbit
```

A particularly useful combination is a **parameterized anonymous** module. Consider this:

```
module ThreeSillyMaps₁ where
  open Data.Product

  one : {l : Level} (A : Set l) → A → A
  one A x = x

  two : {l : Level} (A : Set l) → A → A × A
  two A x = (x , x)

  three : {l : Level} (A : Set l) → A → A × A × A
  three A x = (x , x , x)
```

It is a bit annoying that we keep repeating `{l : Level} (A : Set l)` in all the
definitions. This can be avoided by factoring out the common arguments and making them
parameters of an anonymous module:

```
module ThreeSillyMaps₂ where
  open Data.Product

  module _ {l : Level} (A : Set l) where

    one : A → A
    one x = x

    two : A → A × A
    two x = (x , x)

    three : A → A × A × A
    three x = (x , x , x)
```

### Other modules functionality

You should read the documentation on how to:

* [give an `import`-ed module a new name](https://agda.readthedocs.io/en/latest/language/module-system.html#splitting-a-program-over-multiple-files) with `as`
* prename, hide or use only specific components](https://agda.readthedocs.io/en/latest/language/module-system.html#name-modifiers) of a module with `renaming`, `using`, and `hiding`
* [re-export a module from another module](https://agda.readthedocs.io/en/latest/language/module-system.html#re-exporting-names) using `public`

## Records for programming: dictionaries

Record types can be used to package together data structures and functions. A typical
example is a [dictionary](https://en.wikipedia.org/w/index.php?title=Dictionary_(data_structure)), which is a data structure represening a map from *keys* to *values*.

In a typical programming language the type of dictionaries and the functions for working with it can be organized into a unit, such as a class (Java), type class (Haskell), a  module (OCaml and SML), etc.
With dependent types we can do better by including not only all the tyes and functions, but also the **specification**, i.e., statements about how the functions should behave. This way any implementation of will automatically be correct.

First we have some preparatory code (notice that we are placing this section into an anonymous module so that it does
not interfere with the other sections):

```
module _ where
  open Data.Empty
  open Data.Maybe
  open Data.Product

  -- negation of equality
  _≢_ : {l : Level} {A : Set l} → A → A → Set l
  x ≢ y = x ≡ y → ⊥

  -- Decidable predicates
  data Dec {l : Level} (A : Set l) : Set l where
    yes : A → Dec A
    no  : (A → ⊥) → Dec A
```

A dictionary which maps `Keys` to values of type `A` needs to know something about the type of keys, namely the type of
keys has decidable equality. This is expressed with a suitable record type:

```
  record Key {l : Level} : Set (lsuc l) where
    field
      Keys      : Set l
      test-keys : (k k' : Keys) → Dec (k ≡ k')
```

Now we define the `Dictionary` record type which is parameterized by a decidable type of keys and values. We use general universe levels:

```
  record Dictionary {l₁ l₂ l₃ : Level}
                    (K : Key {l₁}) (A : Set l₂) : Set (lsuc (l₁ ⊔ l₂ ⊔ l₃)) where

    open Key K -- opening the `K` record to easily access its fields below
```

The following fields are expected (for simplicity we are ignoring removal of keys):

```
    field
      Dict      : Set l₃                 -- the underlying type (stores key-value pairs)
      emp       : Dict                   -- empty dictionary
      lkp       : Dict → Keys → Maybe A  -- look up a key in the dictionary
      add       : Dict → Keys × A → Dict -- add a key-value pair to the dictionary
```

But now we add more fields which specify the desired behavior of the functions above:

```
      -- behavioural properties
      lkp-emp   : (k : Keys) → lkp emp k ≡ nothing
      lkp-add-≡ : (k : Keys) (x : A) (d : Dict) → lkp (add d (k , x)) k ≡ just x
      lkp-add-≢ : (k k' : Keys) (x : A) (d : Dict) →
                  k ≢ k' → lkp (add d (k , x)) k' ≡ lkp d k'
```

A record type may additionally contain auxiliary definitions. Here is one, where you should note that

* the definition of `add-if-new` is indented to be *inside* `record Dictionary`
* it refers to the fields specified in `field` above

```
    -- derived dictionary operation (add key-value pair only if key not present)
    add-if-new : Dict → Keys × A → Dict
    add-if-new d (k , x) with lkp d k
    ... | just _  = d
    ... | nothing = add d (k , x)
```

### Partial maps as dictionaries

Above we defined what a dictionary is, i.e., we defined the type of all dictionaries. The next task is to given an element of this type, which amounts to implementing dictionaries in some way. There are many options: associative lists, balanced trees, hash tables, etc. We shall implement them directly as partial maps.

Recall that (one way of) to define “partial maps from `A` to `B`” is to treat tham as maps `A → Maybe B`. The value `nothing` indicates that the map is undefined, and the value `just y` that it is defined to be `y`.

```
  module _ {l₁ l₂ : Level} (K : Key {l₁}) (A : Set l₂) where
    open Dictionary
    open Key K

    update-key-map : {l : Level} {X : Set l} →  (Keys → X) → Keys → X → (Keys → X)
    update-key-map f k x k' with test-keys k k'
    ... | yes _ = x
    ... | no _ = f k'


    PartialMapDictionary : Dictionary K A
    PartialMapDictionary =
      record
        { Dict = Keys → Maybe A
        ; emp = λ _ → nothing
        ; lkp = λ d → d
        ; add = λ {d (k , x) → update-key-map d k (just x)}
        ; lkp-emp = λ _ → refl
        ; lkp-add-≡ = lkp-add-≡-aux
        ; lkp-add-≢ = lkp-add-≢-aux
        }
      where
        lkp-add-≡-aux : (k : Keys) (x : A) (d : Keys → Maybe A) →
                        update-key-map d k (just x) k ≡ just x
        lkp-add-≡-aux k x d with test-keys k k
        ... | yes refl = refl
        ... | no p = ⊥-elim (p refl)

        lkp-add-≢-aux : (k k' : Keys) (x : A) (d : Keys → Maybe A) →
                        k ≢ k' → update-key-map d k (just x) k' ≡ d k'
        lkp-add-≢-aux k k' x d k≢k' with test-keys k k'
        ... | yes k≡k' = ⊥-elim (k≢k' k≡k')
        ... | no _ = refl
```

The above implementation is not ideal. For example, when updating a new key-value pair, the previous one remains burried underneath. Consequently, the dictionary never gets smaller and take more and more memory. Another defficiency is linear-time lookup.


### Refining dictionaries

Apart from `lkp-add-≡` and `lkp-add-≢` there are other desirable equations that we could require, for example `add (add d
(k , x)) (k , x') ≡ add d (k , x')`. This can be done by defining a new record type which includes `Dictionary` and
imposes an additional property:


```
  record Dictionary' {l₁ l₂ l₃ : Level}
                     (K : Key {l₁}) (A : Set l₂) : Set (lsuc (l₁ ⊔ l₂ ⊔ l₃)) where

    open Key K

    field
      -- include Dictionary as a substructure
      Dict' : Dictionary {l₁} {l₂} {l₃} K A
    open Dictionary Dict'

    field
      -- an additional behavioural property
      add-add-≡ : (k : Keys) (x x' : A) (d : Dict)
                → add (add d (k , x)) (k , x') ≡ add d (k , x')
```

The above is just a toy example, which however shows how one might start building more complicated hierarchies of data
structures. (And there are other ways, of course.)

We extend our implementation of dictionaries accordingly.

```
  module _ {l₁ l₂ : Level} (K : Key {l₁}) (A : Set l₂) where
    open Key K
    open Dictionary'
    open import Axiom.Extensionality.Propositional using (Extensionality)

    postulate fun-ext : ∀ {a b} → Extensionality a b

    PartialMapDictionary' : Dictionary' K A

    PartialMapDictionary' =
      record
        { Dict' = PartialMapDictionary K A
        ; add-add-≡ = add-add-≡-aux }

      where
        open Dictionary (PartialMapDictionary K A)

        add-add-≡-aux : (k : Keys) (x x' : A) (d : Keys → Maybe A) →
                        add (add d (k , x)) (k , x') ≡ add d (k , x')
        add-add-≡-aux k x x' d = fun-ext eq
          where
            eq : (k' : Keys) → add (add d (k , x)) (k , x') k' ≡ add d (k , x') k'
            eq k' with test-keys k k' | inspect (test-keys k) k'
            ... | yes p | [ _ ] = refl
            ... | no p  | [ ξ ] rewrite ξ = refl
```

The above code uses function extensionality to show that maps are equal, which is a bit disadvantageous. There are alternatives:

1. Use some other implementation of dictionaries.

2. Replace equality of dictionaries with **observational equivalence**.

An observational equivalence is the equivalence relation stating that two entities, even though they may not be equal, behave the same way in *relevant situations*. In our case, the relevant situation is “look up the key associated to a value”, whose special caseal is the type of `eq` in the code above.

:::{admonition} Exercise

Define obsevational equivalence of dictionaries and show that partial map dictionaries satify `add-add-≡` *without*
function extensionality when observational equivalence is used instead of `≡`.

:::


## Records for mathematics: monoids

Mathematicians package up mathematical entities also. They call them **mathematical structures**, here is one:

:::{prf:definition}
:nonumber: true
:label: monoid

A **monoid** is a triple $(M, \epsilon, {\cdot})$ such that for all $x, y, z\in M$ we have
$\epsilon \cdot x = x = x \cdot \epsilon$ and $(x \cdot y) \cdot z = x \cdot (y \cdot z)$.

:::

The triple is really more like a record type, because its components have names: $M$ is the **carrier**, $\epsilon$ is the **unit** and $\cdot$ is the **multiplication**. When we translate the definition to Agda we need to name the axioms as well:

```
record Monoid l : Set (lsuc l) where
  infixl 7 _·_
  field

    M : Set l            -- carrier type of the monoid
    ε       : M          -- identity element (unicode with `\epsilon`)
    _·_     : M → M → M  -- binary operation (unicode with `\cdot`)

    -- the monoid laws
    ε-left  : (x : M) → ε · x ≡ x
    ε-right : (x : M) → x · ε ≡ x
    ·-assoc : (x y z : M) → (x · y) · z ≡ x · (y · z)
```

We include in the record type additional functions and statements that will be helpful later on.

```
  -- still part of the Monoid record
  module _ where
    open Data.List

    -- multiply a list of elements
    list-· : List M → M
    list-· = foldr _·_ ε

    list-·-∷ : (x : M) → (xs : List M) → list-· (x ∷ xs) ≡ x · list-· xs
    list-·-∷ x [] = refl
    list-·-∷ x (y ∷ ys) = cong (x ·_) (list-·-∷ y ys)

    list-·-++ : (xs ys : List M) → list-· (xs ++ ys) ≡ list-· xs · list-· ys
    list-·-++ [] ys = sym (ε-left (list-· ys))
    list-·-++ (x ∷ xs) ys = trans (cong (x ·_) (list-·-++ xs ys)) (sym (·-assoc x (list-· xs) (list-· ys)))

  -- the n-fold power of x
  power : M → ℕ → M
  power x zero = ε
  power x (suc n) = x · power x n

  power-+ : (x : M) (m n : ℕ) → power x (m + n) ≡ power x m · power x n
  power-+ x zero n = sym (ε-left _)
  power-+ x (suc m) n =
   begin
     power x (suc m + n)           ≡⟨ cong (x ·_) (power-+ x m n) ⟩
     x · (power x m · power x n)   ≡⟨ sym (·-assoc x (power x m) (power x n)) ⟩
     (x · power x m) · power x n
   ∎
```

### Monoid morphisms

A monoid morphism is a map between the carriers that preserves the unit and multiplication. This again is a record type (notice how we used `renaming` to refer to the components of the domain and the codomain):

```
infixl 6 _→ᴹ_ -- unicode with `\to\^M`

record _→ᴹ_ {l₁ l₂} (Mon₁ : Monoid l₁) (Mon₂ : Monoid l₂) : Set (l₁ ⊔ l₂) where
  open Monoid Mon₁ renaming (M to M₁; ε to ε₁; _·_ to _·₁_; ε-left to ε-left₁;
                             ε-right to ε-right₁; ·-assoc to ·-assoc₁;
                             power to power₁; list-· to list-·₁)
  open Monoid Mon₂ renaming (M to M₂; ε to ε₂; _·_ to _·₂_; ε-left to ε-left₂;
                             ε-right to ε-right₂; ·-assoc to ·-assoc₂;
                             power to power₂; list-· to list-·₂)
  field

    map   : M₁ → M₂                                     -- the map between the Ms of the monoids
    map-ε : map ε₁ ≡ ε₂                                 -- the map preserves identity element
    map-· : (x y : M₁) → map (x ·₁ y) ≡ map x ·₂ map y  -- the map preserves the binary operation
```

Once again we include auxiliary statements showing that a homomorphism preserves multiplication of lists of elements and powers:

```
  module _ where
    open Data.List renaming (map to list-map)

    map-list-· : (xs : List M₁) → map (list-·₁ xs) ≡ list-·₂ (list-map map xs)
    map-list-· [] = map-ε
    map-list-· (x ∷ xs) = trans (map-· x (list-·₁ xs)) (cong (map x ·₂_) (map-list-· xs))

  map-power : (x : M₁) (k : ℕ) → map (power₁ x k) ≡ power₂ (map x) k
  map-power x zero = map-ε
  map-power x (suc k) = trans (map-· x (power₁ x k)) (cong (map x ·₂_) (map-power x k))
```

According to Agda, homorphisms `f : M₁ →ᴹ M₂` and `g : M₁ →ᴹ M₂` are equal when they have equal components, *including*
equal `map-ε` and `mao-·`. The mathematically sensible definition of equality is coarser than that, namely observational equality:

```
infix 3 _≡ᴹ_

_≡ᴹ_ : ∀ {l} {Mon₁ Mon₂ : Monoid l} → (f : Mon₁ →ᴹ Mon₂) → (g : Mon₁ →ᴹ Mon₂) → Set l
f ≡ᴹ g = (x : _) → map₁ x ≡ map₂ x
  where open _→ᴹ_ f renaming (map to map₁)
        open _→ᴹ_ g renaming (map to map₂)
```

Homomorphisms and monoids form a category. The identity homomorphism is just the identity map (together with proofs that
it preserves the unit and the multiplication):

```
idᴹ : ∀ {l} {Mon : Monoid l} → Mon →ᴹ Mon
idᴹ = record {
  map   = id ;
  map-ε = refl ;
  map-· = λ _ _ → refl }
```

Composition of homomorphisms is a homomorphism:

```
infixl 5 _∘ᴹ_

_∘ᴹ_ : ∀ {l} {Mon₁ Mon₂ Mon₃ : Monoid l} → (Mon₂ →ᴹ Mon₃) → (Mon₁ →ᴹ Mon₂) → (Mon₁ →ᴹ Mon₃)
g ∘ᴹ f = record {
  map   = map₂ ∘ map₁ ;
  map-ε = trans (cong map₂ map-ε₁) map-ε₂ ;
  map-· = λ m₁ m₁' → trans (cong map₂ (map-·₁ m₁ m₁')) (map-·₂ (map₁ m₁) (map₁ m₁')) }

  where open _→ᴹ_ f renaming (map to map₁; map-ε to map-ε₁; map-· to map-·₁)
        open _→ᴹ_ g renaming (map to map₂; map-ε to map-ε₂; map-· to map-·₂)
```

We verify that the laws for having a category are satisfied:

```
idᴹ-left : ∀ {l} {Mon₁ Mon₂ : Monoid l} {f : Mon₁ →ᴹ Mon₂}
         → idᴹ ∘ᴹ f ≡ᴹ f

idᴹ-left = λ _ → refl

idᴹ-right : ∀ {l} {Mon₁ Mon₂ : Monoid l} {f : Mon₁ →ᴹ Mon₂}
         → f ∘ᴹ idᴹ ≡ᴹ f

idᴹ-right = λ _ → refl

∘ᴹ-assoc : ∀ {l} {Mon₁ Mon₂ Mon₃ Mon₄ : Monoid l}
             {f : Mon₁ →ᴹ Mon₂} {g : Mon₂ →ᴹ Mon₃} {h : Mon₃ →ᴹ Mon₄}
         → (h ∘ᴹ g) ∘ᴹ f ≡ᴹ h ∘ᴹ (g ∘ᴹ f)

∘ᴹ-assoc = λ _ → refl
```

:::{seealso}

We could define the type of **categories** and show that monoids and homomorphisms form one.
If you are interested in formalizing this sort of math, have a look at the [`agda-categories`](https://github.com/agda/agda-categories).

:::


### Examples of monoids

We give three examples of monoids. The first one is the natural numbers with $0$ and $+$. Notice that we are using `Data.Nat.Properties` to save us some work in proving that addition and zero have the desired properties:

```
module _ where
  open Data.Nat
  open Data.Nat.Properties

  Additive-Monoid-ℕ : Monoid lzero
  Additive-Monoid-ℕ =
    record
      { M = ℕ
      ; ε = zero
      ; _·_ = _+_
      ; ε-left = +-identityˡ
      ; ε-right = +-identityʳ
      ; ·-assoc = +-assoc
      }
```

Another monoid structure on $\mathbb{N}$ is induced by multiplication:

```
  Multiplicative-Monoid-ℕ : Monoid lzero
  Multiplicative-Monoid-ℕ =
    record
      { M = ℕ
      ; ε = 1
      ; _·_ = _*_
      ; ε-left = *-identityˡ
      ; ε-right = *-identityʳ
      ; ·-assoc = *-assoc
      }
```

The third example is the monoid of lists. The unit is the empty list and the operation is list concatenation:

```
module _ where
  open Data.List
  open Data.List.Properties

  Monoid-List : {l : Level} → (A : Set l) → Monoid l
  Monoid-List A =
    record
      { M = List A
      ; ε = []
      ; _·_ = _++_
      ; ε-left = ++-identityˡ
      ; ε-right = ++-identityʳ
      ; ·-assoc = ++-assoc
      }
```

### Free monoids

To give some mathematical substance to the lecture, let us define **free monoids** in terms of their [universal property](https://ncatlab.org/nlab/show/universal%20construction). (The mathematical meaning will be explained live in the lecture.)

```
module _ {l : Level} (M : Monoid l) where
  open Monoid renaming (M to carrier)
  open _→ᴹ_ using (map)

  record Free : Set (lsuc l) where
    field
      generator : Set l
      ι : generator → carrier M
      extend : (N : Monoid l) → (generator → carrier N) → M →ᴹ N
      extend-ι : (N : Monoid l) (f : generator → carrier N) (x : generator) →
                 map (extend N f) (ι x) ≡ f x
      extend-unique : (N : Monoid l) (f g : M →ᴹ N) →
                        ((x : generator) → map f (ι x) ≡ map g (ι x)) → f ≡ᴹ g
```

:::{seealso}

In the exercises you will verify that the cartesian product of two monoids has the universal property of products. Prepare for the exercise by digesting the notion as given in the [nLab page on products](https://ncatlab.org/nlab/show/universal%20construction#ConcreteExample).

:::


### Examples of free monoids

Two of our three monoids are free. The additive monoid of natural numbers is freely generated by $1$. Let us formalize this fact:


```
module _ where
  open Data.Unit
  open Free

  Free-Additive-Monoid-ℕ : Free Additive-Monoid-ℕ

  generator Free-Additive-Monoid-ℕ = ⊤

  ι Free-Additive-Monoid-ℕ _ = 1

  extend Free-Additive-Monoid-ℕ N f =
    record { map = power (f tt)
           ; map-ε = refl
           ; map-· = power-+ (f tt)
           }
    where open Monoid N

  extend-ι Free-Additive-Monoid-ℕ N f x = Monoid.ε-right N (f x)

  extend-unique Free-Additive-Monoid-ℕ N f g ξ n =
    begin
      map f n                                        ≡⟨ cong (map f) (sym (power-ℕ-1 n)) ⟩
      map f (power-ℕ 1 n)                            ≡⟨ map-power f 1 n ⟩
      powerᴺ (map f (ι Free-Additive-Monoid-ℕ tt)) n  ≡⟨ cong (λ y → powerᴺ y n) (ξ tt) ⟩
      powerᴺ (map g 1) n                             ≡⟨ sym (map-power g 1 n) ⟩
      map g (power-ℕ 1 n)                            ≡⟨ cong (map g) (power-ℕ-1 n) ⟩
      map g n
      ∎
    where
      open Monoid Additive-Monoid-ℕ renaming (power to power-ℕ)
      open Monoid N renaming (power to powerᴺ)
      open _→ᴹ_

      power-ℕ-1 : (n : ℕ) → power-ℕ 1 n ≡ n
      power-ℕ-1 zero = refl
      power-ℕ-1 (suc n) = cong suc (power-ℕ-1 n)
```

The second example is the monoid of lists of elements of type `A`, which is freely generated by lists of length 1. (As
always, almost nothing is gained by just staring at the above proofs. In the lecture we shall not have the time to carry
them out in detail, but we will discuss how one goes about finding them. The first step is pen and paper.)


```
module _ {l : Level} (A : Set l) where
  open Free
  open Data.List
  open Data.List.Properties

  Free-Monoid-List : Free (Monoid-List A)
  Free-Monoid-List =
    record
      { generator = A
      ; ι = _∷ []
      ; extend = extend-list
      ; extend-ι = extend-ι-list
      ; extend-unique = extend-unique-list
      }

   where
     open Data.List
     open _→ᴹ_ renaming (map to mapᴹ; map-ε to mapᴹ-ε; map-· to mapᴹ-·)

     extend-list : (N : Monoid l) → (A → Monoid.M N) → Monoid-List A →ᴹ N
     extend-list N f =
       record
         { map = λ xs → list-· (map f xs)
         ; map-ε = refl
         ; map-· = λ xs ys →
             begin
               list-· (map f (xs ++ ys))             ≡⟨ cong list-· (map-++-commute f xs ys) ⟩
               list-· (map f xs ++ map f ys)         ≡⟨ list-·-++ (map f xs) (map f ys) ⟩
               (list-· (map f xs) · list-· (map f ys))
             ∎
         }
       where
         open Monoid N

     extend-ι-list : (N : Monoid l) (f : A → Monoid.M N) (x : A) →
                     mapᴹ (extend-list N f) (x ∷ []) ≡ f x
     extend-ι-list N f x = Monoid.ε-right N (f x)

     extend-unique-list : (N : Monoid l) (f g : Monoid-List A →ᴹ N) →
                          ((x : A) → mapᴹ f (x ∷ []) ≡ mapᴹ g (x ∷ [])) → f ≡ᴹ g
     extend-unique-list N f g ξ [] = trans (mapᴹ-ε f) (sym (mapᴹ-ε g))
     extend-unique-list N f g ξ (x ∷ xs) =
       begin
         mapᴹ f (x ∷ xs)               ≡⟨ mapᴹ-· f (x ∷ []) xs ⟩
         mapᴹ f (x ∷ []) · mapᴹ f xs   ≡⟨ cong₂ _·_ (ξ x) (extend-unique-list N f g ξ xs) ⟩
         mapᴹ g (x ∷ []) · mapᴹ g xs   ≡⟨ sym (mapᴹ-· g (x ∷ []) xs ) ⟩
         mapᴹ g (x ∷ xs)
       ∎
      where
        open Monoid N

```


## Records for mathematics of programming: monads

Our last example is a mix of category theory and programming languages, namely [monads](https://ncatlab.org/nlab/show/monad+%28in+computer+science%29). These are structures that capture computational effects, such as expcetions, I/O, stateful memory, non-determinism etc.

[Haskell uses monads](https://wiki.haskell.org/Monad) to incorporate computational effects into a pure programming
languge. It has a special `do` notation, which Agda supports as well, as we shall see below.

We shall motivate monads in the lecture by consider several examples: exceptions, readers, and lists.

Monads are no different from other mathematical structures: they have several components and axioms, which we encode as
a record type.

```
record Monad (l : Level) : Set (lsuc l) where
  field
    T       : Set l → Set l         -- carrier type
    η       : {X : Set l} → X → T X -- unit
    _>>=_   : {X Y : Set l} → T X → (X → T Y) → T Y -- bind
    -- monad laws
    η-left  : {X Y : Set l} (x : X) (f : X → T Y) → η x >>= f ≡ f x
    η-right : {X : Set l} (c : T X) → c >>= η ≡ c
    >>=-assoc : {X Y Z : Set l} (c : T X) (f : X → T Y) (g : Y → T Z)
              → ((c >>= f) >>= g) ≡ c >>= (λ x → f x >>= g)

  -- the derived operation _>>_ is needed to make Agda do notation work
  _>>_ : {X Y : Set l} → T X → T Y → T Y
  m >> k = (m >>= λ _ → k)

  -- programers call η return, so we alias it
  return = η

```

### The reader monad

The reader monad is used whenever we have a read-only global “environment” that we can read from.

```
Monad-Reader : {l : Level} (R : Set l) → Monad l
Monad-Reader R =
  record
    { T = λ X → (R → X)
    ; η = λ x r → x
    ; _>>=_ = λ c f r → f (c r) r
    ; η-left = λ x f → refl
    ; η-right = λ c → refl
    ; >>=-assoc = λ c f g → refl
    }
```

It supports an operation `ask` which returns the value

```
ask : {l : Level} {R : Set l} → R → R
ask r = r
```

### The monad of lists

Lists form a monad which can be thought of as emodying non-deterministic computation.

```
Monad-List : (l : Level) → Monad l
Monad-List l =
  record
    { T = List
    ; η = _∷ []
    ; _>>=_ = λ xs f → concat (map f xs)
    ; η-left = λ xs f → ++-identityʳ (f xs)
    ; η-right = concat-[-]
    ; >>=-assoc = λ xs f g →
                    begin
                      concat (map g (concat (map f xs)))
                          ≡⟨ cong concat (sym (concat-map {f = g} (map f xs))) ⟩
                      concat (concat (map (map g) (map f xs)))
                          ≡⟨ cong (concat ∘ concat) (sym (map-∘ (map g) f xs)) ⟩
                      concat (concat (map (map g ∘ f) xs))
                          ≡⟨  sym (concat-concat (map (map g  ∘ f) xs)) ⟩
                      concat (map concat (map (map g ∘ f) xs))
                          ≡⟨  cong concat (sym (map-∘ concat (map g ∘ f) xs))  ⟩
                      concat (map (concat ∘ (map g ∘ f)) xs)
                    ∎
    }
  where
    open Data.List
    open Data.List.Properties

    -- map is functorial
    map-∘ : {X Y Z : Set l} (g : Y → Z) (f : X → Y) (xs : List X) →
            map (g ∘ f) xs ≡ map g (map f xs)
    map-∘ g f [] = refl
    map-∘ g f (x ∷ xs) = cong (g (f x) ∷_) (map-∘ g f xs)
```

### Agda `do` notation

The [Agda `do` notation](https://agda.readthedocs.io/en/latest/language/syntactic-sugar.html#do-notation) allows
Haskell-style programming in Agda.

```
module _ where
  demo₁ : Monad.T (Monad-Reader ℕ) ℕ
  demo₁ =
    do
      x ← return 5
      y ← ask
      return (x + y)
    where open Monad (Monad-Reader ℕ)
```

And one more example of a non-deterministic computation

```
module _ where
  open Data.List

  demo₂ : Monad.T (Monad-List lzero) ℕ
  demo₂ =
    do
      x ← 1 ∷ 2 ∷ 3 ∷ []
      y ← 4 ∷ 5 ∷ []
      return (10 * x + y)
    where open Monad (Monad-List lzero)
```
