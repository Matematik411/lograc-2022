# Logic

In today's lecture we shall review the basics of mathematical logic.
The traditional mathematical view of logic is that, together with set theory, logic provides a
*foundation* upon which mathematics is built. It is thus natural to expect there to be
just one foundation, for what would be the purpose of having several?

We shall remain true to the title of this course and deviate from the mathematical stance
by slanting heavily toward the computer science perspective, which takes logic to be a
*tool* for accomplishing various *engineering* tasks (no worries, you will not be required
to use a hammer).

There are [many different kinds of logic](https://plato.stanford.edu/search/search?query=logic) that we cannot properly
address in a single lecture. We shall only look at basic kinds of logic today:

* the **propositional logic**, which consists of atomic propositions, the constants
  $\bot$, $\top$ and the logical connectives $\land$, $\lor$, $\Rightarrow$.

* the **predicate logic** enriches the propositional calculus with predicates,
  relations and the quantifiers $\forall$ and $\exists$.

Logics are presented in different styles, depending on how the basic reasoning laws are formulated and how proofs are constructed:

* [**Hilbert system**](https://en.wikipedia.org/wiki/Hilbert_system): the connectives are governed by axioms; proofs are sequences of statements.

* [**Natural deduction**](https://en.wikipedia.org/wiki/Natural_deduction): the connectives and
  the quantifiers are governed by inference rules; proofs are well-founded trees,
  generated inductively by the inference rules.

* [**Sequent calculus**](https://en.wikipedia.org/wiki/Sequent_calculus): looks similar to
  natural deduction, because it also has inference rules and deduction trees. On closer
  inspection one notices important differences, such as multi-part conclusions and
  built-in symmetries that are not present in natural deduction.

Our presentation is in the natural deduction style, because it most closely resembles type theory. The resemblance is not at all accidental.

From traditional propositional and predicate logic many other kinds of logic have arisen, such as:

* [**Modal logic**](https://plato.stanford.edu/entries/logic-modal/) in which there are *modal operators* which express the *mode* of truth. For example, $\Box \phi$ might mean something like “$\phi$ is true in all states of the system that can be reached from the current state”.

* [**Linear logic**](https://plato.stanford.edu/entries/logic-linear/) in which every hypothesis must be used exactly once. Such logics are used to model situations in which we need to keep track of how many times each resource (a variable, a hypothesis) has been accessed.

* [**Temporal logic**](https://plato.stanford.edu/entries/logic-temporal/) is logic equipped with operators for expressing future and past truth values. For example, $F \phi$ might mean  “$\phi$ will be the case” (at some future time, or in every future time).

Such non-standard logics are used in computer science to specify, model, and reason about communication protocols, software correctness, hardware designs, etc.

```
{-# OPTIONS --overlapping-instances #-}

open import Data.List  using (List; []; _∷_; [_]; _++_; foldr)

module 05-logic where
```

## Propositional logic

In the first lecture we spoke about [inference
rules](./01-first-steps-with-agda.lagda#inductive-generation), which we use now to
specify the reasoning principle of the propositional logic.

### Propositional formulas

The **formulae of the propositional calculus** are built inductively from:

* a set of **atomic formulas**,
* the constants **false $\bot$** and **true $\top$**,
* the connectives **conjunction** $\land$, **disjunction** $\lor$, and **implication** $\Rightarrow$.

In Agda the formulae form an algebraic datatype:

```
module PropositionalLogic (AtomicFormula : Set) where

  infixr 6 _∧_
  infixr 5 _∨_
  infixr 4 _⇒_

  data Formula : Set where
    `_  : AtomicFormula → Formula           -- atomic formula
    ⊤   : Formula                           -- truth (unicode \top)
    ⊥   : Formula                           -- falsehood (unicode \bot)
    _∧_ : Formula → Formula → Formula       -- conjunction (unicode \wedge)
    _∨_ : Formula → Formula → Formula       -- disjunction (unicode \vee)
    _⇒_ : Formula → Formula → Formula       -- implication (unicode \=>)
```
We usually denote formulas with lower-case letters $\phi$, $\psi$, $\theta$, ...
We use the abbreviations:

* **equivalence** $\phi \Leftrightarrow \psi$ is short-hand for $(\phi \Rightarrow \psi) \land (\psi \Rightarrow \phi)$,
* **negation** $\neg \phi$ is short-hand for $\phi \Rightarrow \bot$.

```
  infix 3 _⇔_
  infix 7 ¬_

  _⇔_ : Formula → Formula → Formula
  ϕ ⇔ ψ = (ϕ ⇒ ψ) ∧ (ψ ⇒ ϕ)

  ¬_ : Formula → Formula
  ¬ ϕ = ϕ ⇒ ⊥
```

The basic **judgement form** of propositional calculus is

$$\phi_1, \phi_2, \ldots, \phi_n \vdash \psi,$$

which is read as “the hypotheses $\phi_1, \phi_2, \ldots, \phi_n$ entail the conclusion $\psi$”.


### Inference rules

Inference rules tell us which judgements are **derivable**.

There are three kinds of inference rules:

* **structural rules** for general manipulation of judgements
* each connective has **introduction** and **elimination** rules
* other special rules, such as excluded middle (which we do *not* include by default)

Let us begin to spell these out in Agda. The hypotheses are a list of formulas.

```
  Hypotheses = List Formula
```

The predicate `_∈_` expresses membership in a list:

```
  infix 3 _∈_
  data _∈_ {A : Set} : A → List A → Set where
    instance
      ∈-here  : {x : A} → {xs : List A} → x ∈ (x ∷ xs)
      ∈-there : {x y : A} {xs : List A} → {{x ∈ xs}} → x ∈ (y ∷ xs)
```

The keyword `instance` tells Agda that it should automatically use the constructors
`∈-here` and `∈-there` when trying to find an instance argument (see the rule `hyp` below
which has such an argument).

:::{seealso}

Read the documentation on [instance arguments](https://agda.readthedocs.io/en/latest/language/instance-arguments.html).

:::


Next come the rules of inference. (The long dashed lines are *comments*, inserted to make the syntax similar to inference rules.)

```
  infixl 2 _⊢_ -- unicode \vdash

  data _⊢_ : (Δ : Hypotheses) → (φ : Formula) → Set where
```

The structural rules for manipulation of hypotheses:

```
    weaken   : {Δ₁ Δ₂ : Hypotheses}
             → (φ : Formula)
             → {ψ : Formula}
             → Δ₁ ++ Δ₂ ⊢ ψ
             -----------------------
             → Δ₁ ++ [ φ ] ++ Δ₂ ⊢ ψ

    contract : {Δ₁ Δ₂ : Hypotheses}
             → (φ : Formula)
             → {ψ : Formula}
             → Δ₁ ++ [ φ ] ++ [ φ ] ++ Δ₂ ⊢ ψ
             --------------------------------
             → Δ₁ ++ [ φ ] ++ Δ₂ ⊢ ψ

    exchange : {Δ₁ Δ₂ : Hypotheses}
             → (φ₁ φ₂ : Formula)
             → {ψ : Formula}
             → Δ₁ ++ [ φ₁ ] ++ [ φ₂ ] ++ Δ₂ ⊢ ψ
             -----------------------------------------
             → Δ₁ ++ [ φ₂ ] ++ [ φ₁ ] ++ Δ₂ ⊢ ψ
```

:::{admonition} Exercise

Explain the structural rules in your own words.

:::

The remaining structural rule states that a hypothesis entails itself:

```
    hyp      : {Δ : Hypotheses}
             → (φ : Formula)
             → {{φ ∈ Δ}}
             -----------------
             → Δ ⊢ φ
```

Note that we used the double braces `{{⋯}}` which stand for an **instance
argument**. Agda can automagically derive these from given *instances*. This
way we are saved from manually writing proofs that witness list membership.

The connective for the logical constants are special in the sense that one only has an
introduction rule and the other only an elimination rule.

```
    ⊤-intro  : {Δ : Hypotheses}
             ------------------
             → Δ ⊢ ⊤

    ⊥-elim   : {Δ : Hypotheses}
             → {φ : Formula}
             → Δ ⊢ ⊥
             -------------------
             → Δ ⊢ φ
```

Conjunction has both kinds of rules:

```
    ∧-intro  : {Δ : Hypotheses}
             → {φ ψ : Formula}
             → Δ ⊢ φ
             → Δ ⊢ ψ
             -------------------
             → Δ ⊢ φ ∧ ψ

    ∧-elim₁  : {Δ : Hypotheses}
             → {φ ψ : Formula}
             → Δ ⊢ φ ∧ ψ
             -------------------
             → Δ ⊢ φ

    ∧-elim₂  : {Δ : Hypotheses}
             → {φ ψ : Formula}
             → Δ ⊢ φ ∧ ψ
             -------------------
             → Δ ⊢ ψ
```

Disjunction and implication follow a similar pattern:

```
    ∨-intro₁ : {Δ : Hypotheses}
             → {φ ψ : Formula}
             → Δ ⊢ φ
             ------------------
             → Δ ⊢ φ ∨ ψ

    ∨-intro₂ : {Δ : Hypotheses}
             → {φ ψ : Formula}
             → Δ ⊢ ψ
             -------------------
             → Δ ⊢ φ ∨ ψ

    ∨-elim   : {Δ : Hypotheses}
             → {φ₁ φ₂ ψ : Formula}
             → Δ ⊢ φ₁ ∨ φ₂
             → Δ ++ [ φ₁ ] ⊢ ψ
             → Δ ++ [ φ₂ ] ⊢ ψ
             ---------------------
             → Δ ⊢ ψ

    ⇒-intro  : {Δ : Hypotheses}
             → {φ ψ : Formula}
             → Δ ++ [ φ ] ⊢ ψ
             --------------------
             → Δ ⊢ φ ⇒ ψ

    ⇒-elim   : {Δ : Hypotheses}
             → {φ ψ : Formula}
             → Δ ⊢ φ ⇒ ψ
             → Δ ⊢ φ
             -------------------
             → Δ ⊢ ψ
```

For comparison, here is how one writes the inference rules for disjunction and implication on the walls of a cave:

\begin{gather*}
\frac{\Delta \vdash \phi}{\Delta \vdash \phi \lor \psi}
\qquad
\qquad
\frac{\Delta \vdash \psi}{\Delta \vdash \phi \lor \psi}
\qquad
\qquad
\frac{\Delta \vdash \phi_1 \lor \phi_2 \quad
      \Delta, \phi_1 \vdash \psi \quad
      \Delta, \phi_2 \vdash \psi
}{\Delta \vdash \psi}
\\[3ex]
\frac{\Delta, \phi \vdash \psi}{\Delta \phi \Rightarrow \psi}
\qquad
\qquad
\frac{\Delta \vdash \phi \Rightarrow \psi \qquad
      \Delta \vdash \phi
}{\Delta \vdash \psi}
\end{gather*}


:::{prf:example}
:nonumber: true
:label: disjunction-and-implication

We demonstrate how derivations are built by proving that $A \lor B \Rightarrow C$ is equivalent to $(A \Rightarrow C) \land (B \Rightarrow C)$.

```
  example₁ : (A B C : Formula) → [] ⊢ (A ∨ B ⇒ C) ⇔ (A ⇒ C) ∧ (B ⇒ C)
  example₁ A B C =
    ∧-intro
      (⇒-intro
        (∧-intro
          (⇒-intro
            (⇒-elim
              (hyp (A ∨ B ⇒ C))
              (∨-intro₁ (hyp A))
            )
          )
          (⇒-intro
            (⇒-elim
              (hyp (A ∨ B ⇒ C))
              (∨-intro₂ (hyp B))
            )
          )
        )
      )
      (⇒-intro
        (⇒-intro
          (∨-elim
            (hyp (A ∨ B))
            (⇒-elim
               (∧-elim₁
                 (hyp ((A ⇒ C) ∧ (B ⇒ C)))
               )
               (hyp A)
            )
            (⇒-elim
               (∧-elim₂
                 (hyp ((A ⇒ C) ∧ (B ⇒ C)))
               )
               (hyp B)
            )
          )
        )
      )
```
:::


:::{prf:example}
:nonumber: true
:label: example-derivation

The following somewhat silly example derives $A, B \land C, A \vdash B \land (A \land \top)$.
Its point is to demonstrates how Agda works with instances to find the witnesses for `hyp`.
(You should uncomment `example₄₂`)

```
-- example₄₂ : (A B C : Formula) → A ∷ B ∧ C ∷ A ∷ [] ⊢ B ∧ (A ∧ ⊤)
-- example₄₂ A B C = ∧-intro (∧-elim₁ (hyp (B ∧ C))) (∧-intro (hyp A) ⊤-intro)
```

Notice that `hyp A` above makes Agda unhappy because it sees that there are *two* ways of
proving that `A` is a hypothesis. We can avoid the complaints by telling Agda which `A` we
want by instantiating the instance argument of `hyp` explicitly:

```
  example₁₂ : (A B C : Formula) → A ∷ B ∧ C ∷ A ∷ [] ⊢ B ∧ (A ∧ ⊤)
  example₁₂ A B C = ∧-intro (∧-elim₁ (hyp (B ∧ C))) (∧-intro (hyp A {{∈-here}}) ⊤-intro)

  example₁₃ : (A B C : Formula) → A ∷ B ∧ C ∷ A ∷ [] ⊢ B ∧ (A ∧ ⊤)
  example₁₃ A B C = ∧-intro (∧-elim₁ (hyp (B ∧ C))) (∧-intro (hyp A {{∈-there {{∈-there {{∈-here}}}}}}) ⊤-intro)
```

If we think of `∈-here` as “zero” and `∈-there` as “successor” then the elements of `ϕ ∈
Δ` are seen to be the *position* at which `ϕ` appears in the list `Δ`.

:::


### Derivable and admissible rules

Once the basic inference rules are given, we can combine them to get new ones. There are
two ways of doing this, known as **derivable** and **admissible** rules.

:::{prf:example}
:nonumber: true

From the premise `ϕ ∧ ψ` we may conclude `ψ ∧ ϕ`:

```
  ∧-commute : {Δ : Hypotheses}
            → {ϕ ψ : Formula}
            → Δ ⊢ ϕ ∧ ψ
            -------------------
            → Δ ⊢ ψ ∧ ϕ

  ∧-commute p =
    ∧-intro
      (∧-elim₂ p)
      (∧-elim₁ p)
```

:::

The proof of `∧-commute` just packages up a combination of rules to give a derivation of
the conclusion from the premise, *without* inspecting the derivation `p` of the premise.

:::{prf:definition} Derivable rule
:nonumber: true
:label: derivable-rule

A rule of inference $R$ is **derivable** it there is a derivation tree whose leaves are
the premises of $R$ (and applications of `hyp`), and its conclusion is the conclusion of
$R$.

:::

You will derive more rules in the exercises.

Some rules cannot be established with such simple “template derivations” and require us to
actually inspect the derivations of the premises and transform them into derivations of
the conclusion by a recursive procedure. These are known as admissible rules.

:::{prf:definition} Admissible rule
:nonumber: true
:label: admissible-rule

An inference rule is **admissible** when all of its instances satisfy the property: if the
premises are derivable then the conclusion is derivable.

:::

:::{prf:example}
:nonumber: true
:label: admissible-and-left

The inference rule

$$\frac
{\Delta, \phi \land \psi \vdash \chi}
{\Delta, \phi, \psi \vdash \chi}
$$

is admissible. To see this, we must transform a derivation $\mathcal{D}$ of $\Delta, \phi
\land \psi \vdash \chi$ to a derivation of $\Delta, \phi, \psi \vdash \chi$, which we can
do by traversing $\mathcal{D}$ and replacing applications of `hyp (ϕ ∧ ψ)` with `∧-intro
(hyp ϕ) (hyp ψ)`.

*Remark:* If we are allowed to use `cut` or implications, the the rule is actually
derivable (exercise).

:::

In general it is advantageous to have few basic rules of inference, because that makes the
logic easier to study. As it turns out, weakening, contraction, and exchange are redundant
in the sense that they are admissible.

For instance, to see that weakening is admissible, consider a derivation $\mathcal{D}$ of
$\Delta_1, \Delta_2 \vdash \psi$. A derivation of $\Delta_1, \phi, \Delta_2 \vdash \psi$
is then constructed from $\mathcal{D}$ by insertion of $\phi$ into the list of hypotheses
everywhere in the derivation. (It shall be clearer how this is done in the lecture.)


### The difference between `⊢` and `⇒`

Almost every student of logic asks themselves at some point what is the difference between
entailment $\vdash$ and implication $\Rightarrow$. Is it not the case that we may convert
$\vdash$ to $\Rightarrow$ and vice versa:

$$\frac
  {\Delta, \phi \vdash \psi}
  {\Delta \vdash \phi \Rightarrow \psi}
\qquad
\qquad
\frac
  {\Delta \vdash \phi \Rightarrow \psi}
  {\Delta, \phi \vdash \psi}
$$

Indeed we can, but $\vdash$ and $\Rightarrow$ are quite different.
Entailment $\vdash$ constructs a *judgement*, it is always at the “top level” so to speak, and cannot be nested.
Implication $\Rightarrow$ constructs a *formula*, can be nested, and can appear in sub-formulas.

The learned way to explain the difference is that entailment $\vdash$ is a
*meta-theoretical* notion, whereas implication $\Rightarrow$ is *internal to predicate
logic*.


#### The cut rule

Let us continue the comparison between entailment and implication. The **cut rule**

$$
\frac{
  \Delta \vdash \phi
  \qquad
  \Delta, \phi \vdash \psi
}{
  \Delta \vdash \psi
}
$$

is a structural rule of natural deduction. We can read it as follows: “Under hypothesis $\Delta$, if $\phi$ holds and ($\Delta$ and) $\phi$ entails $\psi$, then $\psi$”. It is awfully similar to the elimination rule for implication: “Under hypotheses $\Delta$, if $\phi$ and $\phi \Rightarrow \psi$ then $\psi$”.

We have not included the cut rule because it is derivable with the help of $\Rightarrow$, as you will show in the exercises.


### Excluded middle

Our predicate calculus is **intuitionistic**. To get the classical calculus, we would also have to include the **law of excluded middle**:

$$
\frac{ }{\Delta \vdash \phi \lor \neg \phi}
$$

There are many applications of logic in computer science where excluded middle is invalid,
so we prefer to adopt it only when the situation calls for it. (This is a typical
engineering attitude, which should be contrasted with the notion that logic is about
truth, and that there is just one truth.)

Excluded middle is inter-derivable with **double negation elimination**:

$$
\frac{\Delta \vdash \neg \neg \phi}{\Delta \vdash \phi}
$$

:::{admonition} Exercise

Derive double-negation elimination from excluded middle, and vice versa.

:::


### Truth tables


**Semantics** is an interpretation of a formal system in a (suitable kind of) mathematical
structure. You are already familiar with one kind of semantics of propositional logic,
namely the truth table semantics.

$\newcommand{\sem}[1]{[\![#1]\!]}$
$\newcommand{\two}{\mathsf{2}}$

Let $A$ be the set of atomic propositions.
Recall that $\two = \{\bot, \top\}$ is a [Boolean algebra](https://en.wikipedia.org/wiki/Boolean_algebra).
To each formula $\phi$ we assign a Boolean function

$$\sem{\phi} : \two^A \to \two$$

which takes a mapping $\eta : A \to \two$ (called a **valuation** or an **environment**)
to an element of $\two$ by interpreting the connectives as the corresponding Boolean
operations on $\two$, and mapping the atomic formulas according to~$\eta$.

The **truth table** of $\phi$ is just $\sem{\phi}$ shown in tabular form.
From a more mathematical point of view, truth-table semantics is the interpretation of
propositional formulas in the Boolean algebra $\two$ (relative to an environment).

:::{prf:definition} Tautology
:nonumber: true
:label: tautology

A propositional formula $\phi$ is a **tautology** when $\sem{\phi}$ is constantly true.

We say that a formula $\phi$ is **valid** or **true** (with respect to truth-table semantics) when it is a tautology.
:::

The relationship between derivability in the propositional calculus and validity for
truth-table semantics is captured by the following two theorems.

:::{prf:theorem} Soundness of propositional calculus
:nonumber: true
:label: prop-soundness

If the propositional calculus derives $\vdash \phi$ then $\phi$ is a tautology.
:::

:::{prf:theorem} Completeness of classical propositional calculus
:nonumber: true
:label: prop-completeness

If $\phi$ is a tautology, then it has a derivation in the *classical* propositional logic.

:::

Other kinds of logic also have soundness and completeness theorems with respect to their
semantics. For example, the *intuitionistic* propositional calculus is sound and complete
for [Heyting algebras](https://en.wikipedia.org/wiki/Heyting_algebra).

Soundness tells us that we may safely use a formal system of deduction to establish truth
about mathematical structures. For instance, rather than checking the truth table for
$\phi$ (which has size $2^{|A|}$) we may instead provide a proof of $\phi$. (If you asked
yourself whether proofs can always be shorter than truth tables, you're a natural-born
theoretical computer scientist.)

Completeness tells us that there is a goodness-of-fit between logic and semantics, in the
sense that the logic can derive all truths. This is a particularly pleasing situation.

Sometimes we are given a mathematical structure of interest, for instance one describing
the transitions of a finite-state system or a communication protocol, and the task is to
devise a logic for reasoning about it. Soundness guarantees that the logic only proves
true statements. Completeness may not easily be achievable for a *single* mathematical
structure of interest.



## Predicate logic

Predicate logic, also known as **first-order logic**, arises from the propositional logic
when atomic formulas are replaced with predicates and relations. There are several steps,
let us explain them carefully. We focus on **single-sorted** logic for simplicity.

### Signatures

The language of a first-order theory is described by a **signature**, which consists of:

* a list of **function symbols** $\mathsf{f}_1, \ldots, \mathsf{f}_n$ each of which has an **arity** $n_i \in \mathbb{N}$,
* a list of **relation symbols** $\mathsf{R}_1, \ldots, \mathsf{R}_m$ each of which has an **arity** $k_j \in \mathbb{N}$.

:::{prf:example}
:nonumber: true
:label: signature-pa

The signature for [Peano arithmetic](https://en.wikipedia.org/wiki/Peano_axioms) consists of:

* function symbols:

   * $\mathsf{zero}$ of arity $0$
   * $\mathsf{succ}$ of arity $1$
   * $\mathsf{plus}$ of arity $2$
   * $\mathsf{times}$ of arity $2$

* there are no relation symbols

:::


### Terms

A **variable context** is a list of *distinct* variables $\vec{x} = (x_1, \ldots, x_n)$.

The **terms** in context $\vec{x}$ with respect to a given signature are built inductively:

* each variable $x_i$ is a term in $\vec{x}$,
* if $\mathsf{f}_i$ is a function symbol of arity $k$ and $t_1, \ldots, t_k$ are terms in context $\vec{x}$
  then so is $\mathsf{f}_i(t_1, \ldots, t_k)$.

A term is **closed** if it is a valid formula in the empty variable context.

:::{prf:example}
:nonumber: true
:label: terms-pa

In context $x, y$ we may build terms of Peano arithmetic:

$$
x, y, \mathsf{zero}, \mathsf{succ}(x), \mathsf{succ}(y), \mathsf{succ}(zero),
\mathsf{plus}(x,x), \ldots
$$

We use the following syntactic sugar:

* $0$ for $\mathsf{zero}$,
* $t^{+}$ for $\mathsf{succ}(t)$,
* $t_1 + t_2$ for $\mathsf{plus}(t_1, t_2)$,
* $t_1 \cdot t_2$ for $\mathsf{times}(t_1, t_2)$.

:::

### Formulas

Given a variable context $\vec{x} = (x_1, \ldots, x_n)$, the **logical formulas** in context $\vec{x}$ are built inductively:

* the logical constants $\bot$ and $\top$ are formulas
* the **primitive formulas** are:

   * $t_1 = t_2$ for any terms $t_1$ and $t_2$ in context $\vec{x}$
   * $\mathrm{R}_j(t_1, \ldots, t_k)$ for any relation symbol $\mathrm{R}_j$ of arity $k$ and terms $t_1, \ldots, t_k$ in context $\vec{x}$

* if $\phi$ and $\psi$ are formulas in context $\vec{x}$ then so are $\neg \phi$, $\phi
  \land \psi$, $\phi \lor \psi$ and $\phi \Rightarrow \psi$.

* if $\phi$ is a formula in context $\vec{x}, y$ then $\forall y \,.\, \phi$ and $\exists y
  \,.\, \phi$ are formulas in context $\vec{x}$. The variable $x$ is bound by $\forall$ and
  $\exists$.

A formula is **closed** if it is a valid formula in the empty variable context.

### Hypothetical judgements

The basic judgement form is

$$
x_1, \ldots, x_m \mid \phi_1, \ldots, \phi_n \vdash \psi
$$

where $x_1, \ldots, x_m$ is a variable context, and $\phi_1, \ldots, \phi_n$ and $\psi$ are formulas in context $x_1, \ldots, x_m$.
The formulas $\phi_i$ are the **hypotheses** and $\psi$ is the **conclusion**.

### Rules of inference

The rules of inference are those of propositional logic, adapted to the above judgement
form, as well as the rules for equality and the quantifiers.

#### Equality

For terms $s, t, u$ and hypotheses $\Delta$ in context $\vec{x}$:

$$
\frac{ }{\vec{x} \mid \Delta \vdash t = t}
\qquad\qquad
\frac
  {\vec{x} \mid \Delta \vdash t = u}
  {\vec{x} \mid \Delta \vdash u = t}
\qquad\qquad
\frac
  {\vec{x} \mid \Delta \vdash s = t \qquad \vec{x} \mid \Delta \vdash t = u}
  {\vec{x} \mid \Delta \vdash s = u}
$$

For terms $t, u$ and hypotheses $\Delta$ in context $\vec{x}$, and a formula $\phi$ in context $\vec{x}, y$:

$$
\frac
  {\vec{x} \mid \Delta \vdash \phi[t/y] \qquad
   \vec{x} \mid \Delta \vdash t = u}
  {\vec{x} \mid \Delta \vdash \phi[u/y]}
$$

#### Universal quantifier

$$
\frac{\vec{x}, y \mid \Delta \vdash \phi}{\vec{x} \mid \Delta \vdash \forall y \,.\, \phi}
\qquad\qquad
\frac{\vec{x} \mid \Delta \vdash \forall y \,.\, \phi}{\vec{x} \mid \Delta \vdash \phi[t/y]}
$$

In the above rules, it is assumed that $y$ does not appear in $\Delta$ because they appear in the variable context $\vec{x}$.

#### Existential quantifier

$$
\frac
  {\vec{x} \mid \Delta \vdash \phi[t/y]}
  {\vec{x} \mid \Delta \vdash \exists y \,.\, \phi}
\qquad
\qquad
\frac{
  \vec{x} \mid \Delta \vdash \exists y \,.\, \phi
  \qquad
  \vec{x}, y \mid \Delta, \phi \vdash \psi
}{
  \vec{x} \mid \Delta \vdash \psi
}
$$

In the above rules, it is assumed that $y$ does not appear in $t$ and $\psi$ because they appear in the variable context $\vec{x}$.

### Specific rules

There is a (possibly empty) set of additional **specific rules** that a first-order theory may posses.

:::{prf:example}
:nonumber: true
:label: axioms-pa

The specific rules of Peano arithmetic are as follows.

For terms $t$ and $u$ and hypotheses $\Delta$ in context $\vec{x}$:

\begin{gather*}
\frac{}{\vec{x} \mid \Delta \vdash \neg (t^{+} = 0)} \\[2ex]
\frac{}{\vec{x} \mid \Delta \vdash t^{+} = u^{+} \Rightarrow t = u} \\[2ex]
\frac{}{\vec{x} \mid \Delta \vdash 0 + u = u} \\[2ex]
\frac{}{\vec{x} \mid \Delta \vdash t^{+} + u = (t + u)^{+}} \\[2ex]
\frac{}{\vec{x} \mid \Delta \vdash 0 \cdot u = 0} \\[2ex]
\frac{}{\vec{x} \mid \Delta \vdash t^{+} \cdot u = t + t \cdot u}
\end{gather*}


For each formula $\phi$ in context $\vec{x}, z$, and a term $t$ in context $\vec{x}$, the **induction rule**

$$
\frac{
\vec{x} \mid \Delta \vdash \phi[0/z]
\qquad
\vec{x}, y \mid \Delta, \phi[y/z] \vdash \phi[y^{+}/z]
}{
\vec{x} \mid \Delta \vdash \phi[t/z]
}
$$

:::
