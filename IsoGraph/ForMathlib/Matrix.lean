import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic.Common

/-!
# Lemmas about matrices and characteristic polynomials

Statements that mention nothing from this development.  They were proved here because
something in the library needed them, and they are collected in `ForMathlib` so that they
can be contributed upstream, or deleted when Mathlib grows its own.
-/

set_option autoImplicit false

open Polynomial Matrix
open scoped Classical

theorem scalar_eq_smul_one {n : Type} [Fintype n] [DecidableEq n] (x : ℝ) :
    Matrix.scalar n x = x • (1 : Matrix n n ℝ) := by
  rw [Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]

theorem charpoly_sub_one {m : Type} [Fintype m] [DecidableEq m] (M : Matrix m m ℝ) :
    (M - 1).charpoly = M.charpoly.comp (X + 1) := by
  refine Polynomial.funext fun t ↦ ?_
  rw [Matrix.eval_charpoly, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_one, Matrix.eval_charpoly]
  congr 1
  rw [scalar_eq_smul_one, scalar_eq_smul_one]
  module

/-- The characteristic polynomial of a conjugate of a diagonal matrix, for a bare matrix rather
than an adjacency matrix. -/
theorem charpoly_eq_prod_of_conj' {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M P Q : Matrix ι ι ℝ} {d : ι → ℝ} (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hM : M * P = P * Matrix.diagonal d) : M.charpoly = ∏ i, (X - C (d i)) := by
  have hA : M = P * Matrix.diagonal d * Q := by
    calc M = M * (P * Q) := by rw [hPQ, mul_one]
      _ = M * P * Q := by rw [mul_assoc]
      _ = P * Matrix.diagonal d * Q := by rw [hM]
  rw [hA, mul_assoc, Matrix.charpoly_mul_comm, mul_assoc, hQP, mul_one, Matrix.charpoly_diagonal]
