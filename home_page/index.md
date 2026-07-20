---
# Feel free to add content and custom Front Matter to this file.
# To modify the layout, see https://jekyllrb.com/docs/themes/#overriding-theme-defaults

# layout: home
usemathjax: true
---

This project is part of [Lean-Cluj Summer School 2026](https://github.com/Lean-Cluj/summer-school-2026/).


Tom, Jerry and Spike play the following game.
Tom generates a random binary code of length `n`,
which he sends to Spike along with a *secret number* `k`
between 0 and `n-1`. Spike flips exactly one bit in the code
and then sends only the modified binary code to Jerry.
Is there a pre-established strategy for Spike and Jerry
such that Jerry can determine the *secret number* `k`
solely by looking at the code sent by Spike?

We formalize in Lean 4, using Mathlib 4, the answer to this question, by characterizing all values of `n` for which such a strategy exists.

See [this paper](https://www.math.ubbcluj.ro/~didactica/pdfs/vadid.php?n=2025-13.pdf) and the references therein  for various solutions to the puzzle.
