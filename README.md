## Formal Conjectures

A collection of formalized statements of conjectures in
[lean](https://leanprover.github.io/lean4/doc/whatIsLean.html), using
[mathlib](https://github.com/leanprover-community/mathlib4).

<!--TODO(firsching): insert link to autmatically generated documentation once docgen4 works-->

## Goals

While there is a growing corpus of formalized theorems including proofs, there
is a lack of open conjectures where only the statement has been formalized. This
would be useful for a few reasons. It could

*   Become a great benchmark for automated theorem provers and automated
    formalization tools.
*   Help clarify the precise meaning of conjectures through formalization.
*   Encourage the expansion of `mathlib` by highlighting needed definitions.

### Note on Formalisation Accuracy

Formalizing mathematical statements without proofs is inherently challenging.
Subtle inaccuracies can arise where the formal statement might not perfectly
capture the nuances of the original conjecture. To mitigate this issue, we will
rely on careful human review of contributions, and plan to periodically leverage
AlphaProof to help identify potential misformalisations.

## Contributing

Contributions are most welcome, consider adding (or even just opening an issue
describing) your favorite conjecture.

Unlike other conjecture lists (the Millenium problems, Smale's list, Yau's
problems, ...) the problems in this repo can come from various places and we
encourage all sorts of contributions. For example, conjectures can be sourced
from various places, including:

*   Mathematical Textbooks
*   Research Papers (including preprints on the
    [arxiv](https://arxiv.org/archive/math))
*   [MathOverflow](https://mathoverflow.net/) Questions
*   Dedicated Problem Lists (e.g.,
    [Erdős Problems](https://www.erdosproblems.com/),
    [Wikipedia's list of unsolved problems](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics),
    [the Scottish Book](https://en.wikipedia.org/wiki/Scottish_Book), ...)
*   ...

We are also interested in the formalized statement of solved variants of open
conjectures and solved statements from dedicated problem lists.

### How to Contribute

1.  Fork the repository on GitHub.
2.  Add your formalized conjecture(s) in the appropriate file/directory
    structure to a branch in your fork.
    *   Include comments linking to the source of the conjecture (paper,
        website, book).
    *   Use the attribute `@[category research open]` for unsolved conjectures.
3.  Ensure the code builds (`lake build`).
4.  Submit a Pull Request to the main repository.

## Usage, Structure & Features

This is a lean 4 project managed with `lake` and a dependency `mathlib`. You
first need to
[install elan, lake, lean and if you want vscode](https://leanprover-community.github.io/get_started.html)
and then run

```bash
lake exe cache get
lake build
```

### Directory structure

The directory structure is organized by the type of sources of the conjectures.
There are two special directories:

-   `Util` contains utilities like the
    [`category` attribute](./FormalConjectures/Util/Attributes.lean),
    the [`answer( )` elaborator](./FormalConjectures/Util/Answer.lean) and some
    linters.
-   `ForMathlib` contains code potentially suitable to be upstreamed to
    [mathlib](https://github.com/leanprover-community/mathlib4). Here we follow
    mathlib's directory structure.


### Two features

#### The `problem_status` tag:

A tag to mark the status of a problem statement: either `open` or `solved`.

The tag should be used as follows:

```lean4
@[category research open]
theorem foo : MyOpenProblem := by
  sorry

@[category research solved]
theorem bar : 1 + 1 = 2 := by
  sorry
```

#### The `answer( )` elaborator

Some open questions are formulated in a way that require a user provided answer,
for instance the
[Hadwiger–Nelson problem](https://en.wikipedia.org/wiki/Hadwiger%E2%80%93Nelson_problem)
asks for the minimum number of colors needed to color the plane such that no two
points exactly one unit distance apart have the same color. The `answer( )`
elaborator allows us to formulate the problem without deciding for an answer.

```lean4
@[category research open]
theorem HadwigerNelsonProblem :
    IsLeast { n : ℕ | ExistsColoring n } answer(sorry) :=
  sorry
```

## Style Guidelines

1.  Generally speaking, every problem should have its own file, though there is
    some flexibility here (e.g. variants and special cases should go in the same
    file).
2.  Bespoke definitions are allowed, as long as they help clarify problem
    statements. We also encourage contributors to provide some very basic API
    for such definitions as a way to test whether these behave as expected.
3.  Benchmark problems should be stated with the `theorem` keyword, and have a
    `problem_status` tag, while API and test statements should use `lemma` or
    `example`.
4.  Every file should come with a reference to where the problem was sourced
    from, and be put in the corresponding directory of the repository, e.g. a
    problem sourced from wikipedia should live in `FormalConjectures/Wikipedia`.

## Versioning

This repo will track the monthly tagged releases of mathlib (which correspond to
Lean releases), rather than tracking mathlib master.

To minimize friction when adding problem statements that need definitions that
are not yet in mathlib, such definitions can be added to the `ForMathlib`
directory. This ensures that the addition of these problems to
formal-conjectures is not locked to the mathlib release cadence.
