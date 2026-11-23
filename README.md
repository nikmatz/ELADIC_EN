# Elements of Linear Algebra, Differential & Integral Calculus

### Digital Companion Material

Interactive digital activities that accompany the book **"Elements of Linear Algebra, Differential & Integral Calculus"** by N. Matzakos. They are reached through the **QR codes** in the printed book, or directly online.

🔗 **https://nikmatz.github.io/ELADIC_EN/**

### Contents

| Folder | Description |
|--------|-------------|
| `quizzes/` | Interactive self-assessment quizzes: 21 quizzes (`ch00`–`ch20`, one per chapter), 212 questions. Randomised questions and options, a hint for each question, feedback by topic, "retry the wrong ones", and the best score is saved. |
| `code/` | CAS activities (`ch00`–`ch20`, one per chapter): **Maxima** code and **Python code that runs inside the page** (Pyodide: NumPy/SciPy/SymPy/Matplotlib, nothing to install). |
| `prompts/` | 178 proof pages: each theorem opens with a ready prompt for a Large Language Model (ChatGPT / Claude / Grok / Perplexity), with references for independent verification. **New:** proofs checked by computer in **Lean 4** are being added, in a second tab on the page. |
| `lean/` | The Lean 4 code of the proofs, one file per theorem (`chNN/…lean`). |
| `hist_prompts/` | 39 historical notes written with the help of Large Language Models. |
| `askiseis/` | Additional exercises per chapter (`ch00`–`ch20`), 1,251 problems with hints. |
| `animations/` | 46 interactive visualisations of concepts (`ch00_ypovathro` … `ch20_dynamoseires`). |
| `appendices/` | Online guides to Maxima & Python. |
| `catalog.json` | Index of all the material (328 entries: path/url/chapter), used to generate the QR codes. |
| `_shared/` | Shared styles (`book.css`). |

### Chapter numbering

The `chNN` folders **follow the chapter numbering of the book (0–20)**:

| # | Chapter | | # | Chapter |
|---|---------|---|---|---------|
| 0 | Mathematical Background | | 10 | The Derivative of a Function |
| 1 | Linear Vector Spaces | | 11 | Monotonicity, Extrema and Convexity |
| 2 | Matrix Algebra | | 12 | Applications of the Derivative and Curve Sketching |
| 3 | Linear Systems | | 13 | The Indefinite Integral |
| 4 | Linear Transformations | | 14 | The Definite Integral |
| 5 | Eigenvalues and Eigenvectors | | 15 | The Fundamental Theorem of Calculus |
| 6 | Diagonalization of Matrices | | 16 | Techniques of Integration |
| 7 | Introduction to Dynamical Systems | | 17 | Applications of the Integral |
| 8 | Functions of One Real Variable | | 18 | Improper Integrals |
| 9 | Limits and Continuity of a Function | | 19 | Sequences and Infinite Series |
| | | | 20 | Power Series and Taylor Series |

### Proofs in Lean

[Lean](https://lean-lang.org/) is a language in which a proof is written so rigorously that a computer checks every step. Where a Lean proof exists, the theorem's page has a second tab, **"Proof in Lean"**, with:

- the statement in the book next to the statement in Lean,
- the proof step by step, with what remains to be proved after each step,
- an exercise for the reader, which opens ready in the [online Lean editor](https://live.lean-lang.org/),
- the complete code, exactly as it was checked (Lean 4 with the Mathlib library).

The Large Language Models tab stays first, as in the book. Lean proofs are being added gradually: 147 of the 178 proof pages have one so far, in every chapter except Ch. 7. Example: [Basic Properties of a Vector Space](https://nikmatz.github.io/ELADIC_EN/prompts/ch01/proof-grammikos-idiotites.html#lean) (Ch. 1).

### GitHub Pages

Available at: **https://nikmatz.github.io/ELADIC_EN/**

### Updates

- **23/11/2026:** Lean proofs for 146 more theorems, in Chapters 0–6 and 8–20 (147 in total).
- **22/11/2026:** First proof in Lean (Ch. 1, Basic Properties of a Vector Space). Display fix on all 178 proof pages: text in parentheses and formulas in the statements, Perplexity button.

### Citation

> Matzakos, N. (2026). *Elements of Linear Algebra, Differential & Integral Calculus*. Independently published.

---
*Author: Nikolaos M. Matzakos*
