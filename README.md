## SIAT: Structural Invariance and Algebraic Totality
A Formal Reduction of the Twin Prime Conjecture in Lean 4.

* **Author:** Kajani Kaunda

* **Lean Version:** Lean 4 (Mathlib)

* **Most recent Toolchain used:** leanprover/lean4:v4.30.0-rc2

* **Status:** Fully Verified.


## Overview
This repository provides a machine-checked reduction of the Twin Prime Conjecture (TPC) within the Lean 4 interactive theorem prover. The proof establishes the infinitude of twin primes as a *structural necessity* derived from the modular properties of the prime sieve.

The formalization leverages the **General Law of Invariance (GLI)**—a framework developed through **Cayley Table Theory (CTT)**—to execute the reduction. By applying GLI, the project establishes the infinitude of twin primes as a structural necessity within the prime sieve's modular mechanics.

------------------------------
## Accompanying Paper
The mathematical theory and formalization strategy are detailed in the following article:

* **Title:** Structural Invariance and Algebraic Totality: A Formal Reduction of the Twin Prime Conjecture
* **Archival Host:** [Zenodo](https://zenodo.org/)
* **Paper DOI:** [10.5281/zenodo.19919962](https://doi.org/10.5281/zenodo.19919962)
* **Repository DOI:** [10.5281/zenodo.19921378](https://doi.org/10.5281/zenodo.19921378)

This work supersedes the conceptual foundations explored in the author's previous preprints.

------------------------------
## Repository Structure
The formalization is organized into modular components to ensure transparency and maintainability:

   1. **Main.lean:**
   This file performs the master TPC reduction by applying the General Law of Invariance to the set of natural primes. 
   2. **Main_Standalone.lean:**
   A zero-setup, self-contained formalization of the Twin Prime Conjecture. This file consolidates all definitions, the GLI framework, and the final theorems into a single source to enable instant verification in the [Lean 4 Web Playground editor](https://live.lean-lang.org/). 
   3. **Invariance.lean:**
   The core "Engine" of the proof. It defines the General Law of Invariance (GLI) and proves pattern persistence in periodic systems via structural induction. 
   4. **Bedrock.lean:**
   Contains the foundational algebraic environment, including the construction of the Cayley Table (Set J), the Mapping Lemma, and Sieve-6 periodicity. 
------------------------------

## Source code location
The Lean source files are located in the **/SIAT** directory of this repository.

------------------------------

## Building and Verifying the Code

### Option A: Lean Web Editor (Zero Installation)
*Best for a quick, single-file review.*

1. Visit the [Lean 4 Web Playground](https://live.lean-lang.org/).
2. Open **Main_Standalone.lean** from this repository and copy its entire content.
3. Paste the code into the web editor.
4. The Lean kernel will automatically verify the code. A **"No goals"** message in the Infoview indicates a successful verification.

### Option B: Local Build with Lake (Windows/Linux/macOS)
*Best for verifying the entire project and checking cross-file dependencies.*

Ensure you have [Lean 4 installed](https://lean-lang.org). Then run:

```
# Clone the repository
git clone https://github.com
cd SIAT

# Download pre-compiled Mathlib binaries
lake exe cache get

# To verify the SIAT library and all proofs, run:

lake build SIAT
```

You can also use the shorthand `lake build`, provided your environment is configured for the default target.

**On single-file verification:**  
To verify only a specific file without a full project build, use:
```
lake env lean SIAT/<filename>.lean
```

---

**Note:** The source code is fully compatible with standard Lean 4 environments, such as VS Code (with the Lean 4 extension) or GitHub Codespaces.

A minimum of 8GB RAM is recommended for local builds. 

------------------------------
## Key Formalized Contributions

* **Interaction Totality:** Verification that the Cayley Table mapping exhaustively captures all prime distances.
* **The GLI Engine:** Formal proof that any localized modular configuration established at the origin must recur infinitely often.
* **The Adjacency Lock:** Algebraic verification that for a gap of 2, adjacency is a mandatory consequence of parity.
* **TPC Reduction:** A machine-checked proof path showing that Sieve Periodicity implies Twin Prime Infinitude.

<div style="border-left: 5px solid #2c3e50; background-color: #f8f9fa;
 padding: 15px; margin: 20px 0; font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif;">
    <h3 style="margin-top: 0; color: #2c3e50;">Technical Note: The Ground-State Exception</h3>
    <p style="line-height: 1.6;">
        The <strong>Adjacency Lock</strong> applies to all primes <i>p > 3</i>. The set <code>{3, 5, 7}</code> is the unique "Ground-State" exception where three primes exist with a gap of 2 because 3 is its own prime factor. 
    </p>
    <p style="line-height: 1.6; margin-bottom: 0;">
        For all subsequent configurations, the <strong>modular DNA</strong> of the Sieve ensures that in any sequence of three gap-2 candidates, at least one is a multiple of 3, and the intervening spaces are multiples of 2. Thus, the Adjacency Lock remains a <strong>Positional Constant</strong> for the remainder of the infinite series, ensuring that the <i>termination</i> of twin primes is a logical nullity.
    </p>
</div>

------------------------------
## Mathematical Context
The Structural Invariance and Algebraic Totality (SIAT) framework shifts the investigation from prime magnitudes to the DNA of the Sieve algorithm. By arranging primes in an infinite Cayley Table, we leverage Magnitude Independence to show that prime gaps are structural invariants. This methodology effectively resolves the "Adjacency Gap" and the "Parity Problem" by moving the TPC from the realm of probabilistic heuristics into the domain of verified Structural Algebraic Necessity.

------------------------------
## Future Work

* **Lean Blueprint:** An interactive dependency graph of the proof structure --- supplementary documentation.
* **Polignac Generalization:** Extending the ABLE Box geometry to higher-dimensional manifolds for all even gaps g > 2.

------------------------------ 
## References

* [Lean 4 Theorem Prover](https://lean-lang.org)

* [Lean Zulip community](https://leanprover.zulipchat.com/) An invaluable resource.

* [A Blueprint-driven Lean 4 Project Template](https://github.com/leanprover-community/LeanProject) by the Lean Prover Community.

* [LeanBlueprint](https://github.com/PatrickMassot/leanblueprint/) by Patrick Massot et al.

------------------------------
## Acknowledgements and Dedication

* **The Giants:** This work acknowledges the foundations laid by Euclid, Eratosthenes, de Polignac, and the modern breakthroughs  by the countless researchers whose collective efforts have advanced our understanding of prime distributions.

* **Dedication:** To all those without whom this work would not have been possible.

------------------------------
© 2026 Kajani Kaunda. This project is provided for academic advancement in formalized mathematics.

