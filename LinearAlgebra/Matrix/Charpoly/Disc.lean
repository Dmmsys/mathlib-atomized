/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.RingTheory.Polynomial.Resultant.Basic


/-!
# The discriminant of a matrix
-/

@[expose] public section

open Polynomial

namespace Matrix

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/--
Definition of `discr` / `discr` 的定义

English:
definition discr
  signature: (A : Matrix n n R)
  body: A.charpoly.discr

@[simp]

中文:
定义 discr
  签名: (A : Matrix n n R)
  定义体: A.charpoly.discr

@[simp]

Depends on / 依赖: A.charpoly.discr, charpoly
-/
noncomputable def discr (A : Matrix n n R) : R := A.charpoly.discr

@[simp]
/--
lemma `discr_conj` / 引理 `discr_conj`

English:
lemma discr_conj
  given: (g : GL n R) (m : Matrix n n R)
  statement: (g.val * m * g.val⁻¹).discr = m.discr
  proof: by
  simp [discr]

@[simp]

中文:
引理 discr_conj
  条件: (g : GL n R) (m : Matrix n n R)
  结论: (g.val * m * g.val⁻¹).discr = m.discr
  证明: by
  simp [discr]

@[simp]
-/
lemma discr_conj (g : GL n R) (m : Matrix n n R) : (g.val * m * g.val⁻¹).discr = m.discr := by
  simp [discr]

@[simp]
/--
lemma `discr_conj'` / 引理 `discr_conj'`

English:
lemma discr_conj'
  given: (g : GL n R) (m : Matrix n n R)
  statement: (g.val⁻¹ * m * g.val).discr = m.discr
  proof: by
  simp [discr]

中文:
引理 discr_conj'
  条件: (g : GL n R) (m : Matrix n n R)
  结论: (g.val⁻¹ * m * g.val).discr = m.discr
  证明: by
  simp [discr]
-/
lemma discr_conj' (g : GL n R) (m : Matrix n n R) : (g.val⁻¹ * m * g.val).discr = m.discr := by
  simp [discr]

/--
lemma `discr_of_card_eq_two` / 引理 `discr_of_card_eq_two`

English:
lemma discr_of_card_eq_two
  given: (A : Matrix n n R) (hn : Fintype.card n = 2)
  proof: by
  nontriviality R
  rw [discr]; rw [Polynomial.discr_of_degree_eq_two (by simp; norm_cast)]
  simp [A.charpoly_of_card_eq_two hn]

中文:
引理 discr_of_card_eq_two
  条件: (A : Matrix n n R) (hn : Fintype.card n = 2)
  证明: by
  nontriviality R
  rw [discr]; rw [Polynomial.discr_of_degree_eq_two (by simp; norm_cast)]
  simp [A.charpoly_of_card_eq_two hn]

Depends on / 依赖: A.charpoly_of_card_eq_two, Polynomial, Polynomial.discr_of_degree_eq_two, charpoly_of_card_eq_two, discr_of_degree_eq_two, nontriviality
-/
lemma discr_of_card_eq_two (A : Matrix n n R) (hn : Fintype.card n = 2) :
    A.discr = A.trace ^ 2 - 4 * A.det := by
  nontriviality R
  rw [discr]; rw [Polynomial.discr_of_degree_eq_two (by simp; norm_cast)]
  simp [A.charpoly_of_card_eq_two hn]

/--
lemma `discr_fin_two` / 引理 `discr_fin_two`

English:
lemma discr_fin_two
  given: (A : Matrix (Fin 2) (Fin 2) R)
  proof: A.discr_of_card_eq_two Fintype.card_fin _

中文:
引理 discr_fin_two
  条件: (A : Matrix (Fin 2) (Fin 2) R)
  证明: A.discr_of_card_eq_two Fintype.card_fin _

Depends on / 依赖: A.discr_of_card_eq_two, Fintype, Fintype.card_fin, card_fin, discr_of_card_eq_two
-/
lemma discr_fin_two (A : Matrix (Fin 2) (Fin 2) R) :
    A.discr = A.trace ^ 2 - 4 * A.det :=
A.discr_of_card_eq_two Fintype.card_fin _

end Matrix
