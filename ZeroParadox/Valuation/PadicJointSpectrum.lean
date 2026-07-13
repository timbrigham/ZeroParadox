-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): the p-adic additive characters (the functions Kozyrev wavelets are built from) are simultaneous eigenfunctions of BOTH the odometer's Koopman (composition) operator and the Taibleson–Vladimirov operator D^α on ℤ_p — one eigenbasis diagonalizes both operators. Operator-level only; no dynamical or physical claim; no claim of mathematical novelty. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.PadicKozyrev
import ZeroParadox.Valuation.PadicKoopman
import ZeroParadox.Valuation.PadicKoopmanVladimirov
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The joint spectrum: Koopman ⋈ Vladimirov share the character eigenbasis

Experimental probe in the bottom-diagram mapping campaign — not a finalized layer. Curated results
are indexed in ZeroParadox/MANIFEST.md.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

The `BEAM` (`PadicKoopmanVladimirov`) showed that `D^α` *commutes* with the odometer's Koopman operator
`U_c`; commuting operators share eigenspaces. This file exhibits that shared eigenbasis explicitly: the
**p-adic additive characters** `paChar n φ` — the functions Kozyrev's wavelet basis is built from (a
Kozyrev wavelet is such a character *times a ball indicator*; Kozyrev, Izv. Math. 66 (2002) 367) — are
**simultaneous eigenfunctions** of both operators:

* of the **Taibleson–Vladimirov operator** `D^α` — eigenvalue `λ_n` (`vladimirov_paChar_eigenvalue`,
  needs a primitive `φ` and `n ≥ 1`);
* of the **odometer's Koopman operator** `U_c f = f(c + ·)` — eigenvalue the character phase
  `paChar n φ c` (this is exactly `paChar_add` — elementary: a character diagonalizes any translation).

`U_c f = f(c + ·)` is the composition operator of the measure-preserving map `x ↦ c + x` — the same map
`koopmanOdometer` (`PadicKoopman`) realizes as an `L²` isometry. So one basis diagonalizes both operators
at once: the odometer's Koopman operator and the Vladimirov operator `D^α`. ("Joint spectrum" is used
loosely here for this simultaneous diagonalization, not in the Taylor-joint-spectrum sense.)

**Fences.** Operator-level only. `D^α` is unbounded, so its eigen-relation is stated at the function level
(not as the bounded `L²` Koopman operator composed literally). The non-trivial content is the `D^α`
eigenvalue `λ_n` (`PadicKozyrev`); the Koopman half is elementary harmonic analysis on a compact abelian
group. Sharing an eigenbasis is a statement about the two operators; it is NOT an identification of the
odometer's orbits with any process — that orbit/process level is separately walled (the matched-rate /
no-orbit-correspondence result). No dynamical-equivalence or physical claim, and no claim of mathematical
novelty (this is an eigenbasis computation over standard p-adic harmonic analysis — Vladimirov, Kozyrev —
only that we are not aware of a prior formalization).

## Structure
- § I  The Koopman eigen-relation (odometer)
- § II The joint spectrum (simultaneous diagonalization)
-/

namespace ZeroParadox

open MeasureTheory

variable {p : ℕ} [Fact p.Prime]

/-! ## § I — The Koopman eigen-relation for the odometer -/

/-- **Characters are eigenfunctions of the odometer's Koopman operator.** `U_c(paChar n φ)(x) =
    paChar n φ (c + x) = paChar n φ c · paChar n φ x`: the composition operator `U_c f = f(c + ·)` scales
    the character by the constant phase `paChar n φ c` (a root of unity). This is exactly the character
    law `paChar_add` — no primitivity, any level. `U_c` is the composition operator of the measure-preserving
    odometer `x ↦ c + x` that `koopmanOdometer` realizes on `L²`. -/
theorem paChar_koopman_eigen (n : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ) (c x : ℤ_[p]) :
    paChar (p := p) n φ (c + x) = paChar (p := p) n φ c * paChar (p := p) n φ x :=
  paChar_add n φ c x

/-! ## § II — The joint spectrum -/

/-- **Simultaneous diagonalization ("joint spectrum", loosely).** For a primitive character `φ` (`n ≥ 1`),
    the character `paChar n φ` is a simultaneous eigenfunction of **both** operators:
    * `D^α (paChar n φ) x = λ_n · paChar n φ x` (the Vladimirov operator, eigenvalue `λ_n`);
    * for every `c`, `U_c (paChar n φ) x = paChar n φ c · paChar n φ x` (the odometer's Koopman operator,
      eigenvalue the phase `paChar n φ c`).
    One eigenbasis diagonalizes both operators at once — an operator-level statement, consistent with the
    commutation `vladimirov_koopman_commute`. -/
theorem paChar_joint_spectrum (n : ℕ) (hn : 0 < n) (φ : AddChar (ZMod (p ^ n)) ℂ)
    (hφ : φ.IsPrimitive) (α : ℝ) :
    (∀ x : ℤ_[p], vladimirov α (paChar (p := p) n φ) x
        = (((1 - (p : ℝ)⁻¹) * ∑ k ∈ Finset.range n, ((p : ℝ) ^ α) ^ k
            + ((p : ℝ) ^ α) ^ (n - 1) * (p : ℝ)⁻¹ : ℝ) : ℂ) * paChar (p := p) n φ x)
      ∧ (∀ c x : ℤ_[p], paChar (p := p) n φ (c + x)
          = paChar (p := p) n φ c * paChar (p := p) n φ x) :=
  ⟨fun x => vladimirov_paChar_eigenvalue n hn φ hφ α x, fun c x => paChar_add n φ c x⟩

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms paChar_koopman_eigen
#print axioms paChar_joint_spectrum
end PurityCheck
