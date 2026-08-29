/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
public import Mathlib.Data.Finsupp.MonomialOrder.DegLex

/-! # Some lemmas about the degree lexicographic monomial order on multivariate polynomials -/

public section

namespace MvPolynomial

open MonomialOrder Finsupp

open scoped MonomialOrder

variable {σ : Type*} {R : Type*}

section CommSemiring

variable [CommSemiring R] {f g : MvPolynomial σ R}

section LinearOrder

variable [LinearOrder σ] [WellFoundedGT σ]

/--
theorem `degree_degLexDegree` / 定理 `degree_degLexDegree`

English:
theorem degree_degLexDegree
  statement: (degLex.degree f).degree = f.totalDegree
  proof: by
  by_cases hf : f = 0
  · simp [hf]
  apply le_antisymm
  · exact le_totalDegree (degLex.degree_mem_support hf)
  · unfold MvPolynomial.totalDegree
    apply Finset.sup_le
    intro b hb
    exact DegLex.monotone_degree (degLex.le_degree hb)

中文:
定理 degree_degLexDegree
  结论: (degLex.degree f).degree = f.totalDegree
  证明: by
  by_cases hf : f = 0
  · simp [hf]
  apply le_antisymm
  · exact le_totalDegree (degLex.degree_mem_support hf)
  · unfold MvPolynomial.totalDegree
    apply Finset.sup_le
    intro b hb
    exact DegLex.monotone_degree (degLex.le_degree hb)

Depends on / 依赖: DegLex, DegLex.monotone_degree, Finset, Finset.sup_le, MvPolynomial, MvPolynomial.totalDegree, degLex, degLex.degree_mem_support, degLex.le_degree, degree_mem_support, le_antisymm, le_degree, le_totalDegree, monotone_degree, sup_le, totalDegree
-/
theorem degree_degLexDegree : (degLex.degree f).degree = f.totalDegree := by
  by_cases hf : f = 0
  · simp [hf]
  apply le_antisymm
  · exact le_totalDegree (degLex.degree_mem_support hf)
  · unfold MvPolynomial.totalDegree
    apply Finset.sup_le
    intro b hb
    exact DegLex.monotone_degree (degLex.le_degree hb)

/--
theorem `degLex_totalDegree_monotone` / 定理 `degLex_totalDegree_monotone`

English:
theorem degLex_totalDegree_monotone
  given: (h : degLex.degree f ≼[degLex] degLex.degree g)
  proof: by
  simp only [← MvPolynomial.degree_degLexDegree]
  exact DegLex.monotone_degree h

中文:
定理 degLex_totalDegree_monotone
  条件: (h : degLex.degree f ≼[degLex] degLex.degree g)
  证明: by
  simp only [← MvPolynomial.degree_degLexDegree]
  exact DegLex.monotone_degree h

Depends on / 依赖: DegLex, DegLex.monotone_degree, MvPolynomial, MvPolynomial.degree_degLexDegree, degree_degLexDegree, monotone_degree
-/
theorem degLex_totalDegree_monotone (h : degLex.degree f ≼[degLex] degLex.degree g) :
    f.totalDegree <= g.totalDegree := by
  simp only [← MvPolynomial.degree_degLexDegree]
  exact DegLex.monotone_degree h

end LinearOrder

end CommSemiring

end MvPolynomial
