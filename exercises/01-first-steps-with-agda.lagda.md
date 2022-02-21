# First steps with Agda

## Proof assistants and Agda

A **proof assistant** is a program which helps people carry out mathematical construction and prove theorems by guiding them and verifying the steps in complete detail. Some of the most popular proof assistants are [Coq](https://coq.inria.fr), [Isabelle](https://isabelle.in.tum.de), [Agda](https://wiki.portal.chalmers.se/agda/pmwiki.php) and [Lean](https://leanprover.github.io). Many decades of work have gone into the development of these tools, which have grown complex and powerful.

Proof assistants can be used to develop mathematics with computers, verify implementation of software and hardware, and to implement
software that is guaranteed to be correct with respect to a given implementation. Your class project will address one of these topics, but we shall begin by learning how to use Agda.

Of the aforementioned proof assistants Agda has the least amount of automation. It requires the user to actually write out proofs, which is good for learning how proof assistants work. Once you are familiar with the “manual work”, the automation provided by other proof assistants will look less like confusing magic.

(agda-installation)=
## Installing and obtaining Agda

If at all possible, you should install Agda before the first lecture. We are making every effort to equip the computers in the student lab 3.12 with the latest working version of Agda, but in the long run you will need to have Agda installed on your personal computer. If you get stuck, ask for help on the Discord server.

:::{seealso}
For detailed installation instructions, see the section [Installing agda](https://github.com/danelahman/lograc-2022#installing-agda) in the [course GitHub repository `lograc-2022`](https://github.com/danelahman/lograc-2022).
:::

## Agda files and modules

Agda code is stored in files with file extension `.agda`. Each file is also an **Agda module**, i.e., a basic unit of code. There can be submodules, modules with parameters, anonymous modules, etc., but for now we just have to remember:

:::{important}
Each Agda file `Foo.agda` must contain an Agda module named `Foo`.
:::

:::{warning}
Module names are case-sensitive: the file `foo.agda` must contain the module `foo` and not the module `Foo`.
:::

Agda code may contain comments:

```
{- Multi line comments
   are written like this.
   They may go on for many lines. -}

-- a single line comment
```

There is also **literate Agda** (see [literate programming](https://en.wikipedia.org/wiki/Literate_programming)), which is ordinary text with embedded Agda code. In fact, these notes are written in [Markdown](https://daringfireball.net/projects/markdown/) with literate Agda.
The text is stored in the file `01-first-steps-with-agda.lagda.md`, which means that Agda requires it to contain a module of the same name:

```
module 01-first-steps-with-agda where
```

The rest of the file is the contents of the module. (The module declaration may be preceded with `import` statements and pragmas,
which we will learn about later.)

Agda code must be properly indented, just like Python and Haskell code.


## Booleans

Agda is at its core a programming language. The user may define datatypes, structures, functions etc. Let us define the datatype of boolean values:

```
data Bool : Set where
  false : Bool
  true : Bool
```

The definition introduces a new type `Bool` In Agda `Set` is the collection of all types and predicates.
The above definition states that `Bool` is a new type with two *constructors*, namely `false` and `true`.

:::{seealso}
In reality there is a whole hierarchy of **universes** `Set₀`, `Set₁`, `Set₂`, ... and `Set` is just an abbreviation for `Set₀`. See [Type universes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#universes) in IUFMA and [Universe levels](https://agda.readthedocs.io/en/v2.6.2.1/language/universe-levels.html) in documentation.
:::

By the way, when you start up Agda it has almost *no* predefined types and functions. Even basic types such as booleans and natural numbers are defined by the user. Of course, there is a [standard library](https://agda.github.io/agda-stdlib/), which we shall use in due time, which saves the user from a lot of work.

We may define functions and other values by declaring their type and providing their definitions:

```
resnica : Bool
resnica = true
```

Let us define logical conjunction. Our first attempt would go like this:

```
and : Bool → Bool → Bool
and false false = false
and false true  = false
and true  false = false
and true  true  = true
```

The above code was not typed in manually, but with help of Agda **interactive mode**. It is a bit cumbersome to explain the interactive features in text, so we will see it live during the lecture.

:::{seealso}
To learn more about the interactive mode you may:

* watch [video recording](https://www.youtube.com/playlist?list=PL-47DDuiZOMA4vH2OzQpo2ATDLw29ATbv) of the lecture,
* read the [Interacting with Agda](https://github.com/danelahman/lograc-2022#interacting-with-agda) section in the course repository,
* read about the interactive mode in the [PLFA section “Writing definitions interactively”](https://plfa.github.io/Naturals/).
:::

:::{tip}
Here is a list of the most common keybindings, where `C-` means “Control key” and `M-` means “Alt key”. For instance `C-c C-l` means “Press `Control` and `c` together, then `Control` and `l` together”.

|Binding|Action|
|---------|--------|
| `C-c C-l` | load file |
| `C-c C-f` | next goal |
| `C-c C-b` | previous goal |
| `M-.` | go to the definition |
| `M-,` | go back to previous location |
| `C-c C-c` | split cases |
| `C-c C-s` | solve goal |
| `C-c C-a` | auto fill goal |
| `C-c C-r` | refine goal |
| `C-c C-SPC` | accept solution |
| `C-c C-n` | compute |
| `C-c C-,` | show current goal |
| `C-c C-.` | show current goal and infer the type of solution |
| `C-c C-;` | show current goal and check the type of solution |
These keybindings are what they are because they follow Emacs conventions.
:::

We may define conjunction by short-circuiting the second argument when possible:

```
and' : Bool → Bool → Bool
and' false q = false
and' true q = q
```

In the first clause we have no need for `q` so we can replace it with the **anonymous pattern** `_`:

```
and'' : Bool → Bool → Bool
and'' false _ = false
and'' true q = q
```

We may similarly define negation:

```
not : Bool → Bool
not false = true
not true  = false
```

Agda has very good support for UTF-8 characters. It is customary to use them, so negation would really be defined like this:

```
¬ : Bool → Bool
¬ false = true
¬ true = false
```

We typed `¬` as `\neg`. In general, symbols are typed using their LaTeX names. Next, let us define conjunction as the symbol `∧`, and let us also make it an infix operator.


### Mixfix syntax

An operator has **fixity**:

* **infix** when we write it between its arguments, e.g., conjunction `p ∧ q` and addition `a + b`
* **prefix** when we write it in front of its argument, e.g., negation `¬ p` and opposite value `- a`
* **postfix** when we write it after its argument, e.g., the factorial  `n !`
* **mixfix** when some other combination occurs, e.g., the conditional statement `if p then x else y`

An operator `⋆` has **associativity**:

* **left-associative** when `a ⋆ b ⋆ c` is interpreted as `(a ⋆ b) ⋆ c` (addition, subtraction)
* **right-associative** when `a ⋆ b ⋆ c` is interpreted as `a ⋆ (b ⋆ c)` (implication `⇒` )
* **non-associative** when `a ⋆ b ⋆ c` is considered to be ambiguous

An operator has **precedence** which determines how tightly it binds. We expect `×` to have higher precedence than `+`.

:::{seealso}
See Agda documentation on [mixfix operators](https://agda.readthedocs.io/en/latest/language/mixfix-operators.html) for further information and examples.
:::

In Agda there are no predefined operators. Symbols such as `-`, `+`, `*`, ... have no special meaning. Instead, the user can define their own operators by indicating the slots with `_`. For example, to define `∧` as an infix operator, we just have to define a function called `_∧_`. We may also indicate precedence and associativity with `infix`, `infixl` and `infixr`:

```
-- declare ∧ to be left-associative infix with precedence 10
infixl 10 _∧_

_∧_ : Bool → Bool → Bool
false ∧ _ = false
true ∧ q = q
```

Henceforth we can write `p ∧ q`, but `_∧_ p q` is also allowed.

Beware! If you use `_` anywhere in the name, you will get a mixfix operator. For example, if you define `sort_list` then you can write `sort_list ℓ` as `sort ℓ list`.

A name can have several slots. We may define the conditional statement as follows:

```
infix 5 if_then_else_

if_then_else_ : {A : Set} → Bool → A → A → A
if false then x else y = x
if true  then x else y = y
```

In the above definition we see an [implicit argument](https://agda.readthedocs.io/en/latest/language/implicit-arguments.html), which is indicated with curly braces `{⋯}`. An implicit argument is not provided by the user. Agda will deduce its value (or complain that it cannot do so). For example, Agda can tell that in the expression `if true then 4 else 5` the value of `A` is `ℕ` because the type of `4` and `5` is `ℕ` (the natural numbers are defined below).


## Natural numbers

The datatype of natural numbers may be defined as follows:

```
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
```

It says that there are two constructors for `ℕ`, namely the constant `zero` and the unary constructor `suc`.
The number 2 is defined as

```
one : ℕ
one = suc zero
```

This is not very practical, as one quickly gets tired of writing `suc`:

```
ten : ℕ
ten = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
```

We can tell Agda that it should interpret the usual numerals as elements of the datatype `ℕ`, by using the [`BUILTIN NATURAL` pragma ](https://agda.readthedocs.io/en/latest/language/built-ins.html#natural-numbers):

```
{-# BUILTIN NATURAL ℕ #-}
```

From now on, writing numbers in decimal notation is equivalent to iterated `suc (suc (suc ⋯ (suc zero)⋯))`:

```
fortytwo = 42
```

The unary numbers are very inefficient. The `BUILTIN NATURAL` pragma additionally tells Agda to use native representation of integers behind the scenes, so the following does not blow up:

```
trillion = 1000000000000
```

We also see that declaring the type of a defined value is optional (we did not write `trillion : ℕ`), although it is considered good practice to do so.

### Recursive functions

We may define recursive functions in Agda:

```
double : ℕ → ℕ
double zero = zero
double (suc n) = suc (suc (double n))
```

Agda is a *total* language: it insists that all functions be completely defined and terminating. It will reject a function that is missing some cases, or one it cannot determine to be terminating (Agda has a fancy [termination checker](https://agda.readthedocs.io/en/latest/language/termination-checking.html)).

The result of any expression is computed with the keybinding `C-c C-n`. For example `double 5` computes to `10` (again, behind the scenes `5` and `10` are translated to iterated `suc`s).

We may also define addition and multiplication:

```
infixl 6  _+_

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

infixl 7  _*_

_*_ : ℕ → ℕ → ℕ
zero * n = zero
suc m * n = (m * n) + n
```

It takes a very, very long time to compute `1000000 * 1000000`. Fortunately, Agda has pragmas with which we tell it to use
internally defined addition and multiplication:

```
{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
```


## Inductive generation

The datatypes defined using `data` are **inductive**, by which we mean that all of their elements are constructed by successive
applications of the constructors. For example, all natural numbers are defined starting with `zero` and applying `suc`.

Mathematically speaking, an inductively defined set is described by **inductive clauses** or **inference rules** which take the form

$$\frac{P_1 \quad P_2 \quad \cdots \quad P_n}{C}$$

Above the line are the **premises** $P_1, \ldots, P_n$ and below the line the **conclusion** $C$. We may read such a rule in two ways:

1. As an inference rule of logic: if the premises holds then the conclusion holds.
2. As a rule generating an element of a type: if the elements described by the premises are given, then there is an element described by the conclusion.

For example, the clauses for generating the natural numbers are

$$
\frac{ }{0 : \mathbb{N}}
\qquad
\frac{n : \mathbb{N}}{\mathsf{S} \, n : \mathbb{N}}
$$

It should be clear that our definition of `ℕ` as a datatype directly mirrors these rules.
Likewise, the inductive definition of booleans is expressed by the inductive clauses:

$$
\frac{ }{\mathsf{false} : \mathsf{Bool}}
\qquad
\frac{}{\mathsf{true} : \mathsf{Bool}}
$$

Inference rules may be used to specify predicates and relations. For example, the predicate stating that a number is even may be specified as follows:

$$
\frac{ }{\mathsf{even} \, 0}
\qquad
\frac{\mathsf{even} \, n}{\mathsf{even} \, (\mathsf{S}(\mathsf{S} \, n))}
$$

This is read as:

* $0$ is an even number,
* if $n$ is even then so is $\mathsf{S}(\mathsf{S} \, n)$.

A **proof** records how inference rules were used to arrive at a conclusion. For that purpose, all inference rules should have names. If we name the above rules $\mathsf{even}_0$ and $\mathsf{even}_{SS}$, then they would be written as follows:

$$
\frac{ }{\mathsf{even}_0 : \mathsf{even} \, 0}
\qquad
\frac{p : \mathsf{even} \, n}{\mathsf{even}_{SS} \, p : \mathsf{even} \, (\mathsf{S}(\mathsf{S}(n)))}
$$

Note that $\mathsf{even}_{SS}$ takes an argument, namely a proof $p$ showing that $n$ is even.
We may now write down the proof of “$S(S(S(S \, 0)))$ is even”:

$$
\mathsf{even}_{SS} (\mathsf{even}_{SS} \, \mathsf{even}_0) : \mathsf{even} \, S(S(S(S \, 0)))
$$

We have discovered an important fact.

:::{important}
There is no difference between inductive generation of sets and proofs of propositions.
:::

Now we know how to define a predicate in Agda – as a datatype:

```
data even : ℕ → Set where
  even-z : even zero
  even-ss : {n : ℕ} → even n → even (suc (suc n))
```

Note that the constructor `even-ss` takes an implicit argument `n`. When we use `even-ss` to show that `suc (suc n)` is even, we therefore provide *only* a proof `p` of `even n`. Agda will infer the implicit argument `n` from the type of `p`.

Four is even:

```
four-is-even : even (suc (suc (suc (suc zero))))
four-is-even = even-ss (even-ss even-z)
```

### Predicates versus boolean functions

There is another way of representing the `even` predicate, as a **boolean function** `evenᴮ : ℕ → Bool`, as follows.

```
evenᴮ : ℕ → Bool
oddᴮ : ℕ → Bool

evenᴮ 0 = true
evenᴮ (suc n) = oddᴮ n

oddᴮ 0 = false
oddᴮ (suc n) = evenᴮ n
```

The boolean function `evenᴮ : ℕ → Bool` has an advantage over the predicate `even : ℕ → Set`  because we can *compute* its result, e.g, `evenᴮ 42` computes to `true`. However, predicates are more general, as not every predicate may be represented by a boolean function, at least not in a computable way.

:::{prf:definition}
A predicate is **decidable** if it can be represented by a Boolean function.
More precisely, $P : A \to \mathsf{Set}$ is represented by $f : A \to \mathsf{Bool}$ when for all $x : A$

$$f \, x =
\begin{cases}
\mathsf{true} & \text{if $P \, x$ is inhabited} \\
\mathsf{false} & \text{if $P \, x$ is empty}
\end{cases}
$$

:::

The inductively defined predicate `even : ℕ → Set` provides *more* information than the corresponding boolean function:

* `even n` is the type of all the ways in which we can prove eveness of `n` (it may be empty, and it just so happens that the rules gives precisely one way of showing that an even number is even)
* `evenᴮ n` yields a single bit of information, namely whether `n` is even

In general predicates are therefore to be preferred to boolean functions. In specific cases and when possible, it may be quite convenient to express a predicate in terms of its boolean function.


## Further examples of inductively defined predicates

To practice inductively defined predicates and relations we consider some further examples.

### Non-zero numbers

The predicate “is not zero” is defined as follows:

```
data _≠0 : ℕ → Set where
  suc≠0 : {n : ℕ} → suc n ≠0
```

Note that the name of the predicate is `_≠0`, which is a postfix operator, and that the name of the constructor is `suc≠0` (without spaces), which is used as an ordinary name (identifier)
Consequently,  we write “42 is not zero” as `42 ≠0`. Beware, `42 ≠ 0` is *syntactically invalid* because `_≠0` is not infix! You have to write either `42 ≠0` or `_≠0 42`. Let us prove that 42 is not zero:

```
42≠0 : 42 ≠0
42≠0 = suc≠0
```

Pay attention to where spaces occur: we wrote `42≠0` *without* spaces and so Agda understands it as an ordinary name.

Non-zeroness can be represented as a boolean function:

```
non-zero : ℕ → Bool
non-zero zero = false
non-zero (suc n) = true
```
In fact, all predicates and relations in this section can be so represented, but we shall have no use for them today.


### Equality

How would we define equality as a relation (two-place predicate)? We can do it inductively as follows:

* $0$ is equal to $0$
* if $m$ and $n$ are equal, then so are $S\,m$ and $S\,n$

With inference rules this would be

$$
\frac{ }{ 0 = 0}
\qquad
\frac{m = n}{S\,m = S\, n}
$$

Because the `=` sign is already taken in Agda, we use `≡ᴺ` and transliterate the above to a definition:

```
infix 4 _≡ᴺ_

data _≡ᴺ_ : ℕ → ℕ → Set where
  z≡ᴺz : zero ≡ᴺ zero
  s≡ᴺs : {m n : ℕ} → m ≡ᴺ n → suc m ≡ᴺ suc n
```

Note that we again used implicit arguments `m` and `n` in the constructor. It takes a bit of experience to know which arguments should be implicit. A good rule of thumb is: an argument may be declared implicit when it appears in the type of a subsequent argument. In the case of `_≡ᴺ_` the arguments `m` and `n` appear in the type of the third argument.

Here is a proof of $2 + 2 = 1 + 3$ (note how we write the name of the theorem without spaces and its type with spaces):

```
2+2≡ᴺ1+3 : 2 + 2 ≡ᴺ 1 + 3
2+2≡ᴺ1+3 = s≡ᴺs (s≡ᴺs (s≡ᴺs (s≡ᴺs z≡ᴺz)))
```

More interesting are proofs of reflexivity, symmetry and transitivity of equality. You should study these. Observe that they are just recursive functions.


```
≡ᴺ-refl : {n : ℕ} → n ≡ᴺ n
≡ᴺ-refl {zero} = z≡ᴺz
≡ᴺ-refl {suc n} = s≡ᴺs ≡ᴺ-refl

≡ᴺ-trans : {k m n : ℕ} → k ≡ᴺ m → m ≡ᴺ n → k ≡ᴺ n
≡ᴺ-trans {zero} {zero} {zero} z≡ᴺz z≡ᴺz = z≡ᴺz
≡ᴺ-trans {suc k} {suc m} {suc n} (s≡ᴺs p) (s≡ᴺs q) = s≡ᴺs (≡ᴺ-trans p q)


≡ᴺ-sym : {m n : ℕ} → m ≡ᴺ n → n ≡ᴺ m
≡ᴺ-sym {zero} {zero} z≡ᴺz = z≡ᴺz
≡ᴺ-sym {suc m} {suc n} (s≡ᴺs p) = s≡ᴺs (≡ᴺ-sym p)
```

Our definition of equality is specific to the datatype `ℕ`. In the next lecture we shall see how to define equality on an arbitrary type.


### Comparison

The relation “less than or equal” is inductively generated by the rules:

* $0 \leq n$ for any $n \in \mathbb{N}$,
* if $m \leq n$ then $S \, m \leq S \, n$.

The corresponding Agda definition is:

```
infix 4 _≤_

data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} → zero ≤ n
  s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n
```

You will practice working with `≤` in the exercises. An example proof is:

```
5≤42 : 5 ≤ 42
5≤42 = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))
```

A slightly more general fact is that $n \leq S \, (S \, n)$:

```
n≤ssn : {n : ℕ} → n ≤ suc (suc n)
n≤ssn {zero} = z≤n
n≤ssn {suc n} = s≤s n≤ssn
```

Notice how we referred to the implicit argument `n` by writing `{zero}` and `{suc n}` in the definition of `n≤ssn`.

Finally, to combine two relations, here is antisymmetry of $\leq$:

```
antisym-≤ : {m n : ℕ} → m ≤ n → n ≤ m → n ≡ᴺ m
antisym-≤ z≤n z≤n = z≡ᴺz
antisym-≤ (s≤s p) (s≤s q) = s≡ᴺs (antisym-≤ p q)
```

## Other inductive datatypes

In the exercises you will work with two additional datatypes which we review briefly here.

### Binary natural numbers

In addition to the unary representation of natural numbers given above, one can represent natural numbers more compactly
and efficiently in binary as sequences of bits. Such sequences are generated inductively:

* the empty sequence $\langle\rangle$ is a sequence,
* if $s$ is a sequence then so is $s\,0$
* if $s$ is a sequence then so is $s\,1$

For example, the number $10$ in binary is $1010_2$.

The corresponding Agda definition is as follows, where we use the letters `O` and `I` in place of $0$ and $1$:

```
infixl 20 _O
infixl 20 _I

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin
```

We made the two constructors postfix so that $1010_2$ may be written as

```
binary-10 : Bin
binary-10 = ⟨⟩ I O I O
```

### Lists

Lists of elements of type $A$ are generated inductively by the rules

$$
\frac{ }{[] : \mathsf{List}\,A}
\qquad
\frac{a : A \quad \ell : \mathsf{List} \, A}{a \mathbin{{:}{:}} \ell : \mathsf{List} \, A}
$$

The operator ${:}{:}$ concatenates the *head* $a$ and the *tail* $\ell$. It is traditionally called “cons” because that was its original name in the Lisp programming language.

```
infixr 5 _∷_

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A
```

Beware, the cons operator should be types as `\::` to give `∷` and *not* as a double colon `::`.
The `BUILTIN LIST` pragma tells Agda to internally represent lists in an efficient way:

```
{-# BUILTIN LIST List #-}
```

The list $[\mathsf{false}, \mathsf{false}, \mathsf{true}]$ is written as

```
boring-list = false ∷ false ∷ true ∷ []
```

The list of all numbers below $n$ may be computed as follows:

```
range : ℕ → List ℕ
range zero = []
range (suc n) = n ∷ range n
```

Indeed, `range 30` computes to the list of numbers $29, 28, 27, \ldots, 1, 0$.

#### Local definitions and `where` clauses

In Agda **local definitions** are introduced with `let` and `where` constructs. Of these, the latter is more common and useful. We demonstrate it by defining the function that reverses a list.

```
reverse : {A : Set} → List A → List A
reverse {A} xs = rev [] xs
   where
     rev : List A → List A → List A
     rev acc [] = acc
     rev acc (x ∷ xs) = rev (x ∷ acc) xs


-- reverse {A} xs = rev [] xs
--   where
--     rev : List A → List A → List A
--     rev xs [] = xs
--     rev xs (x ∷ ys) = rev (x ∷ xs) ys
```

We see that the local definition of `rev` is in the `where` block that comes *after* its use. The block may contain multiple definitions, as well as `open` statements and other things, see [Agda documentation on `let` and `where`](https://agda.readthedocs.io/en/latest/language/let-and-where.html). Also observe that the definition of `rev` refers to `A`, which is an implicit argument to `reverse`. If we pull out the local definition of `rev` then it gets an extra argument:

```
rev' : {A : Set} → List A → List A → List A
rev' xs [] = xs
rev' xs (x ∷ ys) = rev' (x ∷ xs) ys

reverse' : {A : Set} → List A → List A
reverse' {A} xs = rev' [] xs
```

You should use `where` clauses and local definitions, unless the local definition has a reason to become global.

## Supplementary material

* [Getting Started](https://agda.readthedocs.io/en/v2.6.2.1/getting-started/index.html) form Agda documentation
* Sections [Naturals](https://plfa.github.io/Naturals/), [Induction](https://plfa.github.io/Induction/) and [Relations](https://plfa.github.io/Relations/) of [PLFA](https://plfa.github.io/)
* Sections [Getting started with Agda](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#gettingstartedagda)
  and [Natural numbers](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#naturalnumbers) of [IUFMA](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html)