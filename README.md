# The (Almost) Impossible Puzzle

Tom, Jerry and Spike play the following game.
Tom generates a random binary code of length `n`,
which he sends to Spike along with a *secret number*
between `0` and `n-1`. Spike flips exactly one bit in the code
and then sends only the modified binary code to Jerry.
Is there a pre-established strategy for Spike and Jerry
such that Jerry can determine the *secret number*
solely by looking at the code sent by Spike?


Of course, you can play the role of Tom, but you can also play the role of Spike by running `puzzle_pos_flip.exe` and the role of Jerry by running `puzzle_neg_flip.exe`. Do these functions *always* work as expected?

We formalize in Lean 4, using Mathlib 4, the characterization of all values of `n` for which such a strategy exists.

The puzzle and its solution(s) have been discussed,  mainly focusing on the case `n=64` (often formulated as a chessboard puzzle), in the following references:
* [Berry, N., *Impossible Escape?*, 2014](http://datagenetics.com/blog/december12014/index.html)
* [Iancu, M., *The (Almost) Impossible Puzzle*, 2025](https://www.math.ubbcluj.ro/~didactica/pdfs/vadid.php?n=2025-13.pdf)
* [Parker, M., *The almost impossible chessboard puzzle*, 2020](https://www.youtube.com/watch?v=as7Gkm7Y7h4)
* [Rahman, C.L., *Impossible Chessboard Escape Puzzle*, 2021](https://github.com/CoryLR/impossible-chessboard-escape-puzzle)
* [Sanderson, G., *The impossible chessboard puzzle*, 2020](https://www.3blue1brown.com/lessons/chessboard-puzzle)
* [Srivastava, K., *Generalised 'Almost Impossible' Chessboard Problem*, 2020](https://karansrivastava.com/files/Chess.pdf)
