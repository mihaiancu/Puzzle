# The (Almost) Impossible Puzzle

Tom, Jerry and Spike play the following game.
Tom generates a random binary code of length `n`,
which he sends to Spike along with a *secret number*
between `0` and `n-1`. Spike flips exactly one bit in the code
and then sends only the modified binary code to Jerry.
Is there a pre-established strategy for Spike and Jerry
such that Jerry can determine the *secret number*
solely by looking at the code sent by Spike?

Of course, you can play the role of Tom, but you can also play the role of Spike by running `puzzle_pos_flip.exe` and the role of Jerry by running `puzzle_fun.exe`. Do these functions *always* work as expected?

We formalize in Lean 4, using Mathlib 4, the characterization of all values of `n` for which such a strategy exists.

See [this paper](https://www.math.ubbcluj.ro/~didactica/pdfs/vadid.php?n=2025-13.pdf) and references therein for a discussion of the puzzle and its solution.
