/-
Copyright (c) 2023 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Polynomial.SeparableDegree

/-!

# Separable degree

This file contains basics about the separable degree of a field extension.

## Main definitions

- `Field.Emb F E`: the type of `F`-algebra homomorphisms from `E` to the algebraic closure of `E`
  (the algebraic closure of `F` is usually used in the literature, but our definition has the
  advantage that `Field.Emb F E` lies in the same universe as `E` rather than the maximum over `F`
  and `E`). Usually denoted by $\operatorname{Emb}_F(E)$ in textbooks.

- `Field.finSepDegree F E`: the (finite) separable degree $[E:F]_s$ of an extension `E / F`
  of fields, defined to be the number of `F`-algebra homomorphisms from `E` to the algebraic
  closure of `E`, as a natural number. It is zero if `Field.Emb F E` is not finite.
  Note that if `E / F` is not algebraic, then this definition makes no mathematical sense.

  **Remark:** the `Cardinal`-valued, potentially infinite separable degree `Field.sepDegree F E`
  for a general algebraic extension `E / F` is defined to be the degree of `L / F`, where `L` is
  the separable closure of `F` in `E`, which is not defined in this file yet. Later we
  will show that (`Field.finSepDegree_eq`), if `Field.Emb F E` is finite, then these two
  definitions coincide. If `E / F` is algebraic with infinite separable degree, we have
  `#(Field.Emb F E) = 2 ^ Field.sepDegree F E` instead.
  (See `Field.Emb.cardinal_eq_two_pow_sepDegree` in another file.) For example, if
  $F = \mathbb{Q}$ and $E = \mathbb{Q}( \mu_{p^\infty} )$, then $\operatorname{Emb}_F (E)$
  is in bijection with $\operatorname{Gal}(E/F)$, which is isomorphic to
  $\mathbb{Z}_p^\times$, which is uncountable, whereas $ [E:F] $ is countable.

- `Polynomial.natSepDegree`: the separable degree of a polynomial is a natural number,
  defined to be the number of distinct roots of it over its splitting field.

## Main results

- `Field.embEquivOfEquiv`, `Field.finSepDegree_eq_of_equiv`:
  a random bijection between `Field.Emb F E` and `Field.Emb F K` when `E` and `K` are isomorphic
  as `F`-algebras. In particular, they have the same cardinality (so their
  `Field.finSepDegree` are equal).

- `Field.embEquivOfAdjoinSplits`,
  `Field.finSepDegree_eq_of_adjoin_splits`: a random bijection between `Field.Emb F E` and
  `E →ₐ[F] K` if `E = F(S)` such that every element `s` of `S` is integral (= algebraic) over `F`
  and whose minimal polynomial splits in `K`. In particular, they have the same cardinality.

- `Field.embEquivOfIsAlgClosed`,
  `Field.finSepDegree_eq_of_isAlgClosed`: a random bijection between `Field.Emb F E` and
  `E →ₐ[F] K` when `E / F` is algebraic and `K / F` is algebraically closed.
  In particular, they have the same cardinality.

- `Field.embProdEmbOfIsAlgebraic`, `Field.finSepDegree_mul_finSepDegree_of_isAlgebraic`:
  if `K / E / F` is a field extension tower, such that `K / E` is algebraic,
  then there is a non-canonical bijection `Field.Emb F E × Field.Emb E K ≃ Field.Emb F K`.
  In particular, the separable degrees satisfy the tower law: $[E:F]_s [K:E]_s = [K:F]_s$
  (see also `Module.finrank_mul_finrank`).

- `Field.infinite_emb_of_transcendental`: `Field.Emb` is infinite for transcendental extensions.

- `Polynomial.natSepDegree_le_natDegree`: the separable degree of a polynomial is smaller than
  its degree.

- `Polynomial.natSepDegree_eq_natDegree_iff`: the separable degree of a non-zero polynomial is
  equal to its degree if and only if it is separable.

- `Polynomial.natSepDegree_eq_of_splits`: if a polynomial splits over `E`, then its separable degree
  is equal to the number of distinct roots of it over `E`.

- `Polynomial.natSepDegree_eq_of_isAlgClosed`: the separable degree of a polynomial is equal to
  the number of distinct roots of it over any algebraically closed field.

- `Polynomial.natSepDegree_expand`: if a field `F` is of exponential characteristic
  `q`, then `Polynomial.expand F (q ^ n) f` and `f` have the same separable degree.

- `Polynomial.HasSeparableContraction.natSepDegree_eq`: if a polynomial has separable
  contraction, then its separable degree is equal to its separable contraction degree.

- `Irreducible.natSepDegree_dvd_natDegree`: the separable degree of an irreducible
  polynomial divides its degree.

- `IntermediateField.finSepDegree_adjoin_simple_eq_natSepDegree`: the separable degree of
  `F⟮α⟯ / F` is equal to the separable degree of the minimal polynomial of `α` over `F`.

- `IntermediateField.finSepDegree_adjoin_simple_eq_finrank_iff`: if `α` is algebraic over `F`, then
  the separable degree of `F⟮α⟯ / F` is equal to the degree of `F⟮α⟯ / F` if and only if `α` is a
  separable element.

- `Field.finSepDegree_dvd_finrank`: the separable degree of any field extension `E / F` divides
  the degree of `E / F`.

- `Field.finSepDegree_le_finrank`: the separable degree of a finite extension `E / F` is smaller
  than the degree of `E / F`.

- `Field.finSepDegree_eq_finrank_iff`: if `E / F` is a finite extension, then its separable degree
  is equal to its degree if and only if it is a separable extension.

- `IntermediateField.isSeparable_adjoin_simple_iff_isSeparable`: `F⟮x⟯ / F` is a separable extension
  if and only if `x` is a separable element.

- `Algebra.IsSeparable.trans`: if `E / F` and `K / E` are both separable, then `K / F` is also
  separable.

## Tags

separable degree, degree, polynomial

-/

@[expose] public section

open Module Polynomial IntermediateField Field

noncomputable section

universe u v w

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
variable (K : Type w) [Field K] [Algebra F K]

namespace Field

/--
Definition of `Emb` / `Emb` 的定义

English:
abbreviation Emb
  body: E ->ₐ[F] AlgebraicClosure E

中文:
缩写 Emb
  定义体: E ->ₐ[F] AlgebraicClosure E

Depends on / 依赖: AlgebraicClosure
-/
abbrev Emb := E ->ₐ[F] AlgebraicClosure E

/--
Definition of `finSepDegree` / `finSepDegree` 的定义

English:
definition finSepDegree
  signature: : Nat
  body: Nat.card (Emb F E)

中文:
定义 finSepDegree
  签名: : 自然数
  定义体: Nat.card (Emb F E)

Depends on / 依赖: Nat.card
-/
def finSepDegree : Nat := Nat.card (Emb F E)

/--
Instance `instInhabitedEmb` / 实例 `instInhabitedEmb`

English:
instance instInhabitedEmb
  signature: : Inhabited (Emb F E)
  body: ⟨IsScalarTower.toAlgHom F E _⟩

中文:
实例 instInhabitedEmb
  签名: : Inhabited (Emb F E)
  定义体: ⟨IsScalarTower.toAlgHom F E _⟩

Depends on / 依赖: IsScalarTower, IsScalarTower.toAlgHom, toAlgHom
-/
instance instInhabitedEmb : Inhabited (Emb F E) := ⟨IsScalarTower.toAlgHom F E _⟩

/--
Instance `instNeZeroFinSepDegree` / 实例 `instNeZeroFinSepDegree`

English:
instance instNeZeroFinSepDegree
  signature: [FiniteDimensional F E]
  body: ⟨Nat.card_ne_zero.2 ⟨inferInstance, Fintype.finite minpoly.AlgHom.fintype _ _ _⟩⟩

中文:
实例 instNeZeroFinSepDegree
  签名: [FiniteDimensional F E]
  定义体: ⟨Nat.card_ne_zero.2 ⟨inferInstance, Fintype.finite minpoly.AlgHom.fintype _ _ _⟩⟩

Depends on / 依赖: AlgHom, Fintype, Fintype.finite, Nat.card_ne_zero, card_ne_zero, finite, fintype, minpoly, minpoly.AlgHom.fintype
-/
instance instNeZeroFinSepDegree [FiniteDimensional F E] : NeZero (finSepDegree F E) :=
⟨Nat.card_ne_zero.2 ⟨inferInstance, Fintype.finite minpoly.AlgHom.fintype _ _ _⟩⟩

/--
Definition of `embEquivOfEquiv` / `embEquivOfEquiv` 的定义

English:
definition embEquivOfEquiv
  signature: (i : E ≃ₐ[F] K)
  body: AlgEquiv.arrowCongr i AlgEquiv.symm by
  let _ : Algebra E K := i.toAlgHom.toRingHom.toAlgebra
  have : Algebra.IsAlgebraic E K := by
    constructor
    intro x
    have h := isAlgebraic_algebraMap (R := E) (A := K) (i.symm.toAlgHom x)
    rw [show forall y : E]; rw [(algebraMap E K) y = i.toAlgHom

中文:
定义 embEquivOfEquiv
  签名: (i : E ≃ₐ[F] K)
  定义体: AlgEquiv.arrowCongr i AlgEquiv.symm by
  let _ : Algebra E K := i.toAlgHom.toRingHom.toAlgebra
  have : Algebra.IsAlgebraic E K := by
    constructor
    intro x
    have h := isAlgebraic_algebraMap (R := E) (A := K) (i.symm.toAlgHom x)
    rw [show forall y : E]; rw [(algebraMap E K) y = i.toAlgHom

Depends on / 依赖: AlgEquiv, AlgEquiv.apply_symm_apply, AlgEquiv.arrowCongr, AlgEquiv.coe_toAlgHom, AlgEquiv.restrictScalars, AlgEquiv.symm, Algebra, Algebra.IsAlgebraic, AlgebraicClo, AlgebraicClosure, IsAlgClosure, IsAlgClosure.equivOfAlgebraic, IsAlgebraic, algebraMap, apply_symm_apply, arrowCongr, coe_toAlgHom, equivOfAlgebraic, i.symm.toAlgHom, i.toAlgHom
-/
def embEquivOfEquiv (i : E ≃ₐ[F] K) :
Emb F E ≃ Emb F K := AlgEquiv.arrowCongr i AlgEquiv.symm by
  let _ : Algebra E K := i.toAlgHom.toRingHom.toAlgebra
  have : Algebra.IsAlgebraic E K := by
    constructor
    intro x
    have h := isAlgebraic_algebraMap (R := E) (A := K) (i.symm.toAlgHom x)
    rw [show forall y : E]; rw [(algebraMap E K) y = i.toAlgHom y from fun y => rfl] at h
    simpa only [AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply] using h
  apply AlgEquiv.restrictScalars (R := F) (S := E)
  exact IsAlgClosure.equivOfAlgebraic E K (AlgebraicClosure K) (AlgebraicClosure E)

/--
theorem `finSepDegree_eq_of_equiv` / 定理 `finSepDegree_eq_of_equiv`

English:
theorem finSepDegree_eq_of_equiv
  given: (i : E ≃ₐ[F] K)
  proof: Nat.card_congr (embEquivOfEquiv F E K i)

@[simp]

中文:
定理 finSepDegree_eq_of_equiv
  条件: (i : E ≃ₐ[F] K)
  证明: Nat.card_congr (embEquivOfEquiv F E K i)

@[simp]

Depends on / 依赖: Nat.card_congr, card_congr, embEquivOfEquiv
-/
theorem finSepDegree_eq_of_equiv (i : E ≃ₐ[F] K) :
    finSepDegree F E = finSepDegree F K := Nat.card_congr (embEquivOfEquiv F E K i)

@[simp]
/--
theorem `finSepDegree_self` / 定理 `finSepDegree_self`

English:
theorem finSepDegree_self
  statement: finSepDegree F F = 1
  proof: by
  rw [finSepDegree]; rw [Nat.card_eq_one_iff_unique]
  constructor <;> infer_instance

中文:
定理 finSepDegree_self
  结论: finSepDegree F F = 1
  证明: by
  rw [finSepDegree]; rw [Nat.card_eq_one_iff_unique]
  constructor <;> infer_instance

Depends on / 依赖: Nat.card_eq_one_iff_unique, card_eq_one_iff_unique, finSepDegree, infer_instance
-/
theorem finSepDegree_self : finSepDegree F F = 1 := by
  rw [finSepDegree]; rw [Nat.card_eq_one_iff_unique]
  constructor <;> infer_instance

end Field

namespace IntermediateField

@[simp]
/--
theorem `finSepDegree_bot` / 定理 `finSepDegree_bot`

English:
theorem finSepDegree_bot
  statement: finSepDegree F (⊥ : IntermediateField F E) = 1
  proof: by
  rw [finSepDegree_eq_of_equiv _ _ _ (botEquiv F E)]; rw [finSepDegree_self]

中文:
定理 finSepDegree_bot
  结论: finSepDegree F (⊥ : 整数ermediateField F E) = 1
  证明: by
  rw [finSepDegree_eq_of_equiv _ _ _ (botEquiv F E)]; rw [finSepDegree_self]

Depends on / 依赖: botEquiv, finSepDegree_eq_of_equiv, finSepDegree_self
-/
theorem finSepDegree_bot : finSepDegree F (⊥ : IntermediateField F E) = 1 := by
  rw [finSepDegree_eq_of_equiv _ _ _ (botEquiv F E)]; rw [finSepDegree_self]

section Tower

variable {F}
variable [Algebra E K] [IsScalarTower F E K]

@[simp]
/--
theorem `finSepDegree_bot'` / 定理 `finSepDegree_bot'`

English:
theorem finSepDegree_bot'
  statement: finSepDegree F (⊥ : IntermediateField E K) = finSepDegree F E
  proof: finSepDegree_eq_of_equiv _ _ _ ((botEquiv E K).restrictScalars F)

@[simp]

中文:
定理 finSepDegree_bot'
  结论: finSepDegree F (⊥ : 整数ermediateField E K) = finSepDegree F E
  证明: finSepDegree_eq_of_equiv _ _ _ ((botEquiv E K).restrictScalars F)

@[simp]

Depends on / 依赖: botEquiv, finSepDegree_eq_of_equiv, restrictScalars
-/
theorem finSepDegree_bot' : finSepDegree F (⊥ : IntermediateField E K) = finSepDegree F E :=
  finSepDegree_eq_of_equiv _ _ _ ((botEquiv E K).restrictScalars F)

@[simp]
/--
theorem `finSepDegree_top` / 定理 `finSepDegree_top`

English:
theorem finSepDegree_top
  statement: finSepDegree F (⊤ : IntermediateField E K) = finSepDegree F K
  proof: finSepDegree_eq_of_equiv _ _ _ ((topEquiv (F := E) (E := K)).restrictScalars F)

中文:
定理 finSepDegree_top
  结论: finSepDegree F (⊤ : 整数ermediateField E K) = finSepDegree F K
  证明: finSepDegree_eq_of_equiv _ _ _ ((topEquiv (F := E) (E := K)).restrictScalars F)

Depends on / 依赖: finSepDegree_eq_of_equiv, restrictScalars, topEquiv
-/
theorem finSepDegree_top : finSepDegree F (⊤ : IntermediateField E K) = finSepDegree F K :=
  finSepDegree_eq_of_equiv _ _ _ ((topEquiv (F := E) (E := K)).restrictScalars F)

end Tower

/--
theorem `isSeparable_bot` / 定理 `isSeparable_bot`

English:
theorem isSeparable_bot
  statement: Algebra.IsSeparable F (⊥ : IntermediateField F E)
  proof: AlgEquiv.Algebra.isSeparable (IntermediateField.botEquiv F E).symm

中文:
定理 isSeparable_bot
  结论: Algebra.IsSeparable F (⊥ : 整数ermediateField F E)
  证明: AlgEquiv.Algebra.isSeparable (IntermediateField.botEquiv F E).symm

Depends on / 依赖: AlgEquiv, AlgEquiv.Algebra.isSeparable, Algebra, IntermediateField, IntermediateField.botEquiv, botEquiv, isSeparable
-/
theorem isSeparable_bot : Algebra.IsSeparable F (⊥ : IntermediateField F E) :=
  AlgEquiv.Algebra.isSeparable (IntermediateField.botEquiv F E).symm

/--
theorem `isSeparable_top` / 定理 `isSeparable_top`

English:
theorem isSeparable_top
  proof: Algebra.IsSeparable.iff_of_equiv_equiv (RingEquiv.refl F) topEquiv.toRingEquiv (by ext; simp)

中文:
定理 isSeparable_top
  证明: Algebra.IsSeparable.iff_of_equiv_equiv (RingEquiv.refl F) topEquiv.toRingEquiv (by ext; simp)

Depends on / 依赖: Algebra, Algebra.IsSeparable.iff_of_equiv_equiv, IsSeparable, RingEquiv, RingEquiv.refl, iff_of_equiv_equiv, toRingEquiv, topEquiv, topEquiv.toRingEquiv
-/
theorem isSeparable_top :
    Algebra.IsSeparable F (⊤ : IntermediateField F E) ↔ Algebra.IsSeparable F E :=
  Algebra.IsSeparable.iff_of_equiv_equiv (RingEquiv.refl F) topEquiv.toRingEquiv (by ext; simp)

end IntermediateField

namespace Field

/--
Definition of `embEquivOfAdjoinSplits` / `embEquivOfAdjoinSplits` 的定义

English:
definition embEquivOfAdjoinSplits
  signature: {S : Set E} (hS : adjoin F S = ⊤)
  body: have : Algebra.IsAlgebraic F (⊤ : IntermediateField F E) :=
    (hS ▸ isAlgebraic_adjoin (S := S) fun x hx => (hK x hx).1)
  have halg := (topEquiv (F := F) (E := E)).isAlgebraic
Classical.choice Function.Embedding.antisymm
    (halg.algHomEmbeddingOfSplits (fun _ => splits_of_mem_adjoin F E (S := S

中文:
定义 embEquivOfAdjoinSplits
  签名: {S : Set E} (hS : adjoin F S = ⊤)
  定义体: have : Algebra.IsAlgebraic F (⊤ : IntermediateField F E) :=
    (hS ▸ isAlgebraic_adjoin (S := S) fun x hx => (hK x hx).1)
  have halg := (topEquiv (F := F) (E := E)).isAlgebraic
Classical.choice Function.Embedding.antisymm
    (halg.algHomEmbeddingOfSplits (fun _ => splits_of_mem_adjoin F E (S := S

Depends on / 依赖: Algebra, Algebra.IsAlgebraic, Classical, Classical.choice, Embedding, Function, Function.Embedding.antisymm, IntermediateField, IsAlgClosed, IsAlgClosed.splits, IsAlgebraic, algHomEmbeddingOfSplits, antisymm, choice, halg.algHomEmbeddingOfSplits, isAlgebraic, isAlgebraic_adjoin, mem_top, splits, splits_of_mem_adjoin
-/
def embEquivOfAdjoinSplits {S : Set E} (hS : adjoin F S = ⊤)
    (hK : forall s in S, IsIntegral F s ∧ Splits ((minpoly F s).map (algebraMap F K))) :
    Emb F E ≃ (E ->ₐ[F] K) :=
  have : Algebra.IsAlgebraic F (⊤ : IntermediateField F E) :=
    (hS ▸ isAlgebraic_adjoin (S := S) fun x hx => (hK x hx).1)
  have halg := (topEquiv (F := F) (E := E)).isAlgebraic
Classical.choice Function.Embedding.antisymm
    (halg.algHomEmbeddingOfSplits (fun _ => splits_of_mem_adjoin F E (S := S) hK (hS ▸ mem_top)) _)
    (halg.algHomEmbeddingOfSplits (fun _ => IsAlgClosed.splits _) _)

/--
theorem `finSepDegree_eq_of_adjoin_splits` / 定理 `finSepDegree_eq_of_adjoin_splits`

English:
theorem finSepDegree_eq_of_adjoin_splits
  statement: {S : Set E} (hS : adjoin F S = ⊤)
  proof: Nat.card_congr (embEquivOfAdjoinSplits F E K hS hK)

中文:
定理 finSepDegree_eq_of_adjoin_splits
  结论: {S : Set E} (hS : adjoin F S = ⊤)
  证明: Nat.card_congr (embEquivOfAdjoinSplits F E K hS hK)

Depends on / 依赖: Nat.card_congr, card_congr, embEquivOfAdjoinSplits
-/
theorem finSepDegree_eq_of_adjoin_splits {S : Set E} (hS : adjoin F S = ⊤)
    (hK : forall s in S, IsIntegral F s ∧ Splits ((minpoly F s).map (algebraMap F K))) :
    finSepDegree F E = Nat.card (E ->ₐ[F] K) := Nat.card_congr (embEquivOfAdjoinSplits F E K hS hK)

/--
Definition of `embEquivOfIsAlgClosed` / `embEquivOfIsAlgClosed` 的定义

English:
definition embEquivOfIsAlgClosed
  signature: [Algebra.IsAlgebraic F E] [IsAlgClosed K]
  body: embEquivOfAdjoinSplits F E K (adjoin_univ F E) fun s _ =>
    ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩

中文:
定义 embEquivOfIsAlgClosed
  签名: [Algebra.IsAlgebraic F E] [IsAlgClosed K]
  定义体: embEquivOfAdjoinSplits F E K (adjoin_univ F E) fun s _ =>
    ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, IsAlgClosed, IsAlgClosed.splits, IsIntegral, adjoin_univ, embEquivOfAdjoinSplits, isIntegral, splits
-/
def embEquivOfIsAlgClosed [Algebra.IsAlgebraic F E] [IsAlgClosed K] :
    Emb F E ≃ (E ->ₐ[F] K) :=
  embEquivOfAdjoinSplits F E K (adjoin_univ F E) fun s _ =>
    ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩

/-- The `Field.finSepDegree F E` is equal to the cardinality of `E →ₐ[F] K` as a natural number,
when `E / F` is algebraic and `K / F` is algebraically closed. -/
@[stacks 09HJ "We use `finSepDegree` to state a more general result."]
/--
theorem `finSepDegree_eq_of_isAlgClosed` / 定理 `finSepDegree_eq_of_isAlgClosed`

English:
theorem finSepDegree_eq_of_isAlgClosed
  given: [Algebra.IsAlgebraic F E] [IsAlgClosed K]
  proof: Nat.card_congr (embEquivOfIsAlgClosed F E K)

中文:
定理 finSepDegree_eq_of_isAlgClosed
  条件: [Algebra.IsAlgebraic F E] [IsAlgClosed K]
  证明: Nat.card_congr (embEquivOfIsAlgClosed F E K)

Depends on / 依赖: Nat.card_congr, card_congr, embEquivOfIsAlgClosed
-/
theorem finSepDegree_eq_of_isAlgClosed [Algebra.IsAlgebraic F E] [IsAlgClosed K] :
    finSepDegree F E = Nat.card (E ->ₐ[F] K) := Nat.card_congr (embEquivOfIsAlgClosed F E K)

/--
Definition of `embProdEmbOfIsAlgebraic` / `embProdEmbOfIsAlgebraic` 的定义

English:
definition embProdEmbOfIsAlgebraic
  signature: [Algebra E K] [IsScalarTower F E K] [Algebra.IsAlgebraic E K]
  body: let e : forall f : E ->ₐ[F] AlgebraicClosure K,
      @AlgHom E K _ _ _ _ _ f.toRingHom.toAlgebra ≃ Emb E K := fun f =>
    (@embEquivOfIsAlgClosed E K _ _ _ _ _ f.toRingHom.toAlgebra).symm
  (algHomEquivSigma (A := F) (B := E) (C := K) (D := AlgebraicClosure K) |>.trans
.trans Equiv.prodCongrLeft (

中文:
定义 embProdEmbOfIsAlgebraic
  签名: [Algebra E K] [IsScalarTower F E K] [Algebra.IsAlgebraic E K]
  定义体: let e : forall f : E ->ₐ[F] AlgebraicClosure K,
      @AlgHom E K _ _ _ _ _ f.toRingHom.toAlgebra ≃ Emb E K := fun f =>
    (@embEquivOfIsAlgClosed E K _ _ _ _ _ f.toRingHom.toAlgebra).symm
  (algHomEquivSigma (A := F) (B := E) (C := K) (D := AlgebraicClosure K) |>.trans
.trans Equiv.prodCongrLeft (

Depends on / 依赖: AlgEquiv, AlgEquiv.arrowCongr, AlgEquiv.refl, AlgHom, AlgebraicClosure, Equiv.prodCongrLeft, Equiv.sigmaEquivProdOfEquiv, IsAlgClosure, IsAlgClosure.equivOfAlgebraic, algHomEquivSigma, arrowCongr, embEquivOfIsAlgClosed, equivOfAlgebraic, f.toRingHom.toAlgebra, prodCongrLeft, restrictScalars, sigmaEquivProdOfEquiv, toAlgebra, toRingHom
-/
def embProdEmbOfIsAlgebraic [Algebra E K] [IsScalarTower F E K] [Algebra.IsAlgebraic E K] :
    Emb F E × Emb E K ≃ Emb F K :=
  let e : forall f : E ->ₐ[F] AlgebraicClosure K,
      @AlgHom E K _ _ _ _ _ f.toRingHom.toAlgebra ≃ Emb E K := fun f =>
    (@embEquivOfIsAlgClosed E K _ _ _ _ _ f.toRingHom.toAlgebra).symm
  (algHomEquivSigma (A := F) (B := E) (C := K) (D := AlgebraicClosure K) |>.trans
.trans Equiv.prodCongrLeft (Equiv.sigmaEquivProdOfEquiv e)
fun _ : Emb E K => AlgEquiv.arrowCongr (@AlgEquiv.refl F E _ _ _)
        (IsAlgClosure.equivOfAlgebraic E K (AlgebraicClosure K)
          (AlgebraicClosure E)).restrictScalars F).symm

/--
Instance `infinite_emb_of_transcendental` / 实例 `infinite_emb_of_transcendental`

English:
instance infinite_emb_of_transcendental
  signature: [H : Algebra.Transcendental F E]
  body: by
  obtain ⟨ι, x, hx⟩ := exists_isTranscendenceBasis' F E
  have := hx.isAlgebraic_field
  rw [← (embProdEmbOfIsAlgebraic F (adjoin F (Set.range x)) E).infinite_iff]
  refine @Prod.infinite_of_left _ _ ?_ _
  rw [← (embEquivOfEquiv _ _ _ hx.1.aevalEquivField).infinite_iff]
  obtain ⟨i⟩ := hx.nonemp

中文:
实例 infinite_emb_of_transcendental
  签名: [H : Algebra.Transcendental F E]
  定义体: by
  obtain ⟨ι, x, hx⟩ := exists_isTranscendenceBasis' F E
  have := hx.isAlgebraic_field
  rw [← (embProdEmbOfIsAlgebraic F (adjoin F (Set.range x)) E).infinite_iff]
  refine @Prod.infinite_of_left _ _ ?_ _
  rw [← (embEquivOfEquiv _ _ _ hx.1.aevalEquivField).infinite_iff]
  obtain ⟨i⟩ := hx.nonemp

Depends on / 依赖: AlgebraicClosure, FractionRing, Function, Function.Injective, Injective, IsScalarTower, IsScalarTower.coe_toAlgHom, IsScalarTower.toAlgHom, MvPolynomial, Prod.infinite_of_left, Set.range, adjoin, aevalEquivField, coe_toAlgHom, embEquivOfEquiv, embProdEmbOfIsAlgebraic, exists_isTranscendenceBasis, hx.isAlgebraic_field, hx.nonempty_iff_transcendental, infinite_iff
-/
instance infinite_emb_of_transcendental [H : Algebra.Transcendental F E] : Infinite (Emb F E) := by
  obtain ⟨ι, x, hx⟩ := exists_isTranscendenceBasis' F E
  have := hx.isAlgebraic_field
  rw [← (embProdEmbOfIsAlgebraic F (adjoin F (Set.range x)) E).infinite_iff]
  refine @Prod.infinite_of_left _ _ ?_ _
  rw [← (embEquivOfEquiv _ _ _ hx.1.aevalEquivField).infinite_iff]
  obtain ⟨i⟩ := hx.nonempty_iff_transcendental.2 H
  let K := FractionRing (MvPolynomial ι F)
  let i1 := IsScalarTower.toAlgHom F (MvPolynomial ι F) (AlgebraicClosure K)
  have hi1 : Function.Injective i1 := by
    rw [IsScalarTower.coe_toAlgHom']; rw [IsScalarTower.algebraMap_eq _ K]
    exact (algebraMap K (AlgebraicClosure K)).injective.comp (IsFractionRing.injective _ _)
  let f (n : Nat) : Emb F K := IsFractionRing.liftAlgHom
(g := i1.comp <| MvPolynomial.aeval fun i : ι => MvPolynomial.X i ^ (n + 1)) hi1.comp by
      simpa [algebraicIndependent_iff_injective_aeval] using
        MvPolynomial.algebraicIndependent_polynomial_aeval_X _
          fun i : ι => (Polynomial.transcendental_X F).pow n.succ_pos
  refine Infinite.of_injective f fun m n h => ?_
replace h : (MvPolynomial.X i) ^ (m + 1) = (MvPolynomial.X i) ^ (n + 1) := hi1 by
    simpa [f, -map_pow] using congr($h (algebraMap _ K (MvPolynomial.X (R := F) i)))
  simpa using congr(MvPolynomial.totalDegree $h)

/--
theorem `finSepDegree_eq_zero_of_transcendental` / 定理 `finSepDegree_eq_zero_of_transcendental`

English:
theorem finSepDegree_eq_zero_of_transcendental
  given: [Algebra.Transcendental F E]
  proof: Nat.card_eq_zero_of_infinite

中文:
定理 finSepDegree_eq_zero_of_transcendental
  条件: [Algebra.Transcendental F E]
  证明: Nat.card_eq_zero_of_infinite

Depends on / 依赖: Nat.card_eq_zero_of_infinite, card_eq_zero_of_infinite
-/
theorem finSepDegree_eq_zero_of_transcendental [Algebra.Transcendental F E] :
    finSepDegree F E = 0 := Nat.card_eq_zero_of_infinite

/-- If `K / E / F` is a field extension tower, such that `K / E` is algebraic, then their
separable degrees satisfy the tower law
$[E:F]_s [K:E]_s = [K:F]_s$. See also `Module.finrank_mul_finrank`. -/
@[stacks 09HK "Part 1, `finSepDegree` variant"]
/--
theorem `finSepDegree_mul_finSepDegree_of_isAlgebraic` / 定理 `finSepDegree_mul_finSepDegree_of_isAlgebraic`

English:
theorem finSepDegree_mul_finSepDegree_of_isAlgebraic
  proof: by
  simpa only [Nat.card_prod] using! Nat.card_congr (embProdEmbOfIsAlgebraic F E K)

中文:
定理 finSepDegree_mul_finSepDegree_of_isAlgebraic
  证明: by
  simpa only [Nat.card_prod] using! Nat.card_congr (embProdEmbOfIsAlgebraic F E K)

Depends on / 依赖: Nat.card_congr, Nat.card_prod, card_congr, card_prod, embProdEmbOfIsAlgebraic
-/
theorem finSepDegree_mul_finSepDegree_of_isAlgebraic
    [Algebra E K] [IsScalarTower F E K] [Algebra.IsAlgebraic E K] :
    finSepDegree F E * finSepDegree E K = finSepDegree F K := by
  simpa only [Nat.card_prod] using! Nat.card_congr (embProdEmbOfIsAlgebraic F E K)

end Field

namespace Polynomial

variable {F E}
variable (f : F[X])

open scoped Classical in
/--
Definition of `natSepDegree` / `natSepDegree` 的定义

English:
definition natSepDegree
  signature: : Nat
  body: (f.aroots f.SplittingField).toFinset.card

中文:
定义 natSepDegree
  签名: : 自然数
  定义体: (f.aroots f.SplittingField).toFinset.card

Depends on / 依赖: SplittingField, aroots, f.SplittingField, f.aroots, toFinset, toFinset.card
-/
def natSepDegree : Nat := (f.aroots f.SplittingField).toFinset.card

/--
theorem `natSepDegree_le_natDegree` / 定理 `natSepDegree_le_natDegree`

English:
theorem natSepDegree_le_natDegree
  statement: f.natSepDegree <= f.natDegree
  proof: by
.card_roots' have := f.map (algebraMap F f.SplittingField)
  rw [← aroots_def]; rw [natDegree_map] at this
  classical
  exact (f.aroots f.SplittingField).toFinset_card_le.trans this

@[simp]

中文:
定理 natSepDegree_le_natDegree
  结论: f.natSepDegree <= f.natDegree
  证明: by
.card_roots' have := f.map (algebraMap F f.SplittingField)
  rw [← aroots_def]; rw [natDegree_map] at this
  classical
  exact (f.aroots f.SplittingField).toFinset_card_le.trans this

@[simp]

Depends on / 依赖: SplittingField, algebraMap, aroots, aroots_def, card_roots, classical, f.SplittingField, f.aroots, f.map, natDegree_map, toFinset_card_le, toFinset_card_le.trans
-/
theorem natSepDegree_le_natDegree : f.natSepDegree <= f.natDegree := by
.card_roots' have := f.map (algebraMap F f.SplittingField)
  rw [← aroots_def]; rw [natDegree_map] at this
  classical
  exact (f.aroots f.SplittingField).toFinset_card_le.trans this

@[simp]
/--
theorem `natSepDegree_X_sub_C` / 定理 `natSepDegree_X_sub_C`

English:
theorem natSepDegree_X_sub_C
  given: (x : F)
  statement: (X - C x).natSepDegree = 1
  proof: by
  simp only [natSepDegree, aroots_X_sub_C, Multiset.toFinset_singleton, Finset.card_singleton]

@[simp]

中文:
定理 natSepDegree_X_sub_C
  条件: (x : F)
  结论: (X - C x).natSepDegree = 1
  证明: by
  simp only [natSepDegree, aroots_X_sub_C, Multiset.toFinset_singleton, Finset.card_singleton]

@[simp]

Depends on / 依赖: Finset, Finset.card_singleton, Multiset, Multiset.toFinset_singleton, aroots_X_sub_C, card_singleton, natSepDegree, toFinset_singleton
-/
theorem natSepDegree_X_sub_C (x : F) : (X - C x).natSepDegree = 1 := by
  simp only [natSepDegree, aroots_X_sub_C, Multiset.toFinset_singleton, Finset.card_singleton]

@[simp]
/--
theorem `natSepDegree_X` / 定理 `natSepDegree_X`

English:
theorem natSepDegree_X
  statement: (X : F[X]).natSepDegree = 1
  proof: by
  simp only [natSepDegree, aroots_X, Multiset.toFinset_singleton, Finset.card_singleton]

中文:
定理 natSepDegree_X
  结论: (X : F[X]).natSepDegree = 1
  证明: by
  simp only [natSepDegree, aroots_X, Multiset.toFinset_singleton, Finset.card_singleton]

Depends on / 依赖: Finset, Finset.card_singleton, Multiset, Multiset.toFinset_singleton, aroots_X, card_singleton, natSepDegree, toFinset_singleton
-/
theorem natSepDegree_X : (X : F[X]).natSepDegree = 1 := by
  simp only [natSepDegree, aroots_X, Multiset.toFinset_singleton, Finset.card_singleton]

/--
theorem `natSepDegree_eq_zero` / 定理 `natSepDegree_eq_zero`

English:
theorem natSepDegree_eq_zero
  given: (h : f.natDegree = 0)
  statement: f.natSepDegree = 0
  proof: by
  linarith only [natSepDegree_le_natDegree f, h]

@[simp]

中文:
定理 natSepDegree_eq_zero
  条件: (h : f.natDegree = 0)
  结论: f.natSepDegree = 0
  证明: by
  linarith only [natSepDegree_le_natDegree f, h]

@[simp]

Depends on / 依赖: natSepDegree_le_natDegree
-/
theorem natSepDegree_eq_zero (h : f.natDegree = 0) : f.natSepDegree = 0 := by
  linarith only [natSepDegree_le_natDegree f, h]

@[simp]
/--
theorem `natSepDegree_C` / 定理 `natSepDegree_C`

English:
theorem natSepDegree_C
  given: (x : F)
  statement: (C x).natSepDegree = 0
  proof: natSepDegree_eq_zero _ (natDegree_C _)

@[simp]

中文:
定理 natSepDegree_C
  条件: (x : F)
  结论: (C x).natSepDegree = 0
  证明: natSepDegree_eq_zero _ (natDegree_C _)

@[simp]

Depends on / 依赖: natDegree_C, natSepDegree_eq_zero
-/
theorem natSepDegree_C (x : F) : (C x).natSepDegree = 0 := natSepDegree_eq_zero _ (natDegree_C _)

@[simp]
/--
theorem `natSepDegree_zero` / 定理 `natSepDegree_zero`

English:
theorem natSepDegree_zero
  statement: (0 : F[X]).natSepDegree = 0
  proof: by
  rw [← C_0]; rw [natSepDegree_C]

@[simp]

中文:
定理 natSepDegree_zero
  结论: (0 : F[X]).natSepDegree = 0
  证明: by
  rw [← C_0]; rw [natSepDegree_C]

@[simp]

Depends on / 依赖: natSepDegree_C
-/
theorem natSepDegree_zero : (0 : F[X]).natSepDegree = 0 := by
  rw [← C_0]; rw [natSepDegree_C]

@[simp]
/--
theorem `natSepDegree_one` / 定理 `natSepDegree_one`

English:
theorem natSepDegree_one
  statement: (1 : F[X]).natSepDegree = 0
  proof: by
  rw [← C_1]; rw [natSepDegree_C]

中文:
定理 natSepDegree_one
  结论: (1 : F[X]).natSepDegree = 0
  证明: by
  rw [← C_1]; rw [natSepDegree_C]

Depends on / 依赖: natSepDegree_C
-/
theorem natSepDegree_one : (1 : F[X]).natSepDegree = 0 := by
  rw [← C_1]; rw [natSepDegree_C]

/--
theorem `natSepDegree_ne_zero` / 定理 `natSepDegree_ne_zero`

English:
theorem natSepDegree_ne_zero
  given: (h : f.natDegree != 0)
  statement: f.natSepDegree != 0
  proof: by
  rw [natSepDegree]; rw [ne_eq]; rw [Finset.card_eq_zero]; rw [← ne_eq]; rw [← Finset.nonempty_iff_ne_empty]
  use rootOfSplits (SplittingField.splits f) (degree_ne_of_natDegree_ne (by rwa [natDegree_map]))
  classical
  rw [Multiset.mem_toFinset]; rw [mem_aroots]
  exact ⟨ne_of_apply_ne _ h, by 

中文:
定理 natSepDegree_ne_zero
  条件: (h : f.natDegree != 0)
  结论: f.natSepDegree != 0
  证明: by
  rw [natSepDegree]; rw [ne_eq]; rw [Finset.card_eq_zero]; rw [← ne_eq]; rw [← Finset.nonempty_iff_ne_empty]
  use rootOfSplits (SplittingField.splits f) (degree_ne_of_natDegree_ne (by rwa [natDegree_map]))
  classical
  rw [Multiset.mem_toFinset]; rw [mem_aroots]
  exact ⟨ne_of_apply_ne _ h, by 

Depends on / 依赖: Finset, Finset.card_eq_zero, Finset.nonempty_iff_ne_empty, Multiset, Multiset.mem_toFinset, SplittingField, SplittingField.splits, card_eq_zero, classical, degree_ne_of_natDegree_ne, eval_map_algebraMap, eval_rootOfSplits, mem_aroots, mem_toFinset, natDegree_map, natSepDegree, ne_eq, ne_of_apply_ne, nonempty_iff_ne_empty, rootOfSplits
-/
theorem natSepDegree_ne_zero (h : f.natDegree != 0) : f.natSepDegree != 0 := by
  rw [natSepDegree]; rw [ne_eq]; rw [Finset.card_eq_zero]; rw [← ne_eq]; rw [← Finset.nonempty_iff_ne_empty]
  use rootOfSplits (SplittingField.splits f) (degree_ne_of_natDegree_ne (by rwa [natDegree_map]))
  classical
  rw [Multiset.mem_toFinset]; rw [mem_aroots]
  exact ⟨ne_of_apply_ne _ h, by simp only [← eval_map_algebraMap, eval_rootOfSplits]⟩

/--
theorem `natSepDegree_eq_zero_iff` / 定理 `natSepDegree_eq_zero_iff`

English:
theorem natSepDegree_eq_zero_iff
  statement: f.natSepDegree = 0 ↔ f.natDegree = 0
  proof: ⟨(natSepDegree_ne_zero f).mtr, natSepDegree_eq_zero f⟩

中文:
定理 natSepDegree_eq_zero_iff
  结论: f.natSepDegree = 0 ↔ f.natDegree = 0
  证明: ⟨(natSepDegree_ne_zero f).mtr, natSepDegree_eq_zero f⟩

Depends on / 依赖: natSepDegree_eq_zero, natSepDegree_ne_zero
-/
theorem natSepDegree_eq_zero_iff : f.natSepDegree = 0 ↔ f.natDegree = 0 :=
  ⟨(natSepDegree_ne_zero f).mtr, natSepDegree_eq_zero f⟩

/--
theorem `natSepDegree_ne_zero_iff` / 定理 `natSepDegree_ne_zero_iff`

English:
theorem natSepDegree_ne_zero_iff
  statement: f.natSepDegree != 0 ↔ f.natDegree != 0
  proof: Iff.not natSepDegree_eq_zero_iff f

中文:
定理 natSepDegree_ne_zero_iff
  结论: f.natSepDegree != 0 ↔ f.natDegree != 0
  证明: Iff.not natSepDegree_eq_zero_iff f

Depends on / 依赖: Iff.not, natSepDegree_eq_zero_iff
-/
theorem natSepDegree_ne_zero_iff : f.natSepDegree != 0 ↔ f.natDegree != 0 :=
Iff.not natSepDegree_eq_zero_iff f

/--
theorem `natSepDegree_eq_natDegree_iff` / 定理 `natSepDegree_eq_natDegree_iff`

English:
theorem natSepDegree_eq_natDegree_iff
  given: (hf : f != 0)
  proof: by
  classical
  simp_rw [← card_rootSet_eq_natDegree_iff_of_splits hf (SplittingField.splits f),
    rootSet_def, Finset.coe_sort_coe, Fintype.card_coe]
  rfl

中文:
定理 natSepDegree_eq_natDegree_iff
  条件: (hf : f != 0)
  证明: by
  classical
  simp_rw [← card_rootSet_eq_natDegree_iff_of_splits hf (SplittingField.splits f),
    rootSet_def, Finset.coe_sort_coe, Fintype.card_coe]
  rfl

Depends on / 依赖: Finset, Finset.coe_sort_coe, Fintype, Fintype.card_coe, SplittingField, SplittingField.splits, card_coe, card_rootSet_eq_natDegree_iff_of_splits, classical, coe_sort_coe, rootSet_def, simp_rw, splits
-/
theorem natSepDegree_eq_natDegree_iff (hf : f != 0) :
    f.natSepDegree = f.natDegree ↔ f.Separable := by
  classical
  simp_rw [← card_rootSet_eq_natDegree_iff_of_splits hf (SplittingField.splits f),
    rootSet_def, Finset.coe_sort_coe, Fintype.card_coe]
  rfl

/--
theorem `natSepDegree_eq_natDegree_of_separable` / 定理 `natSepDegree_eq_natDegree_of_separable`

English:
theorem natSepDegree_eq_natDegree_of_separable
  given: (h : f.Separable)
  proof: (natSepDegree_eq_natDegree_iff f h.ne_zero).2 h

中文:
定理 natSepDegree_eq_natDegree_of_separable
  条件: (h : f.Separable)
  证明: (natSepDegree_eq_natDegree_iff f h.ne_zero).2 h

Depends on / 依赖: h.ne_zero, natSepDegree_eq_natDegree_iff, ne_zero
-/
theorem natSepDegree_eq_natDegree_of_separable (h : f.Separable) :
    f.natSepDegree = f.natDegree := (natSepDegree_eq_natDegree_iff f h.ne_zero).2 h

variable {f} in
/--
theorem `Separable.natSepDegree_eq_natDegree` / 定理 `Separable.natSepDegree_eq_natDegree`

English:
theorem Separable.natSepDegree_eq_natDegree
  given: (h : f.Separable)
  proof: natSepDegree_eq_natDegree_of_separable f h

中文:
定理 Separable.natSepDegree_eq_natDegree
  条件: (h : f.Separable)
  证明: natSepDegree_eq_natDegree_of_separable f h

Depends on / 依赖: natSepDegree_eq_natDegree_of_separable
-/
theorem Separable.natSepDegree_eq_natDegree (h : f.Separable) :
    f.natSepDegree = f.natDegree := natSepDegree_eq_natDegree_of_separable f h

/--
theorem `natSepDegree_eq_of_splits` / 定理 `natSepDegree_eq_of_splits`

English:
theorem natSepDegree_eq_of_splits
  given: [DecidableEq E] (h : (f.map (algebraMap F E)).Splits)
  proof: by
  classical
  rw [aroots]; rw [← (SplittingField.lift f h).comp_algebraMap]; rw [← map_map]; rw [(SplittingField.splits f).roots_map]; rw [Multiset.toFinset_map]; rw [Finset.card_image_of_injective _ (RingHom.injective _)]; rw [natSepDegree]

中文:
定理 natSepDegree_eq_of_splits
  条件: [DecidableEq E] (h : (f.map (algebraMap F E)).Splits)
  证明: by
  classical
  rw [aroots]; rw [← (SplittingField.lift f h).comp_algebraMap]; rw [← map_map]; rw [(SplittingField.splits f).roots_map]; rw [Multiset.toFinset_map]; rw [Finset.card_image_of_injective _ (RingHom.injective _)]; rw [natSepDegree]

Depends on / 依赖: Finset, Finset.card_image_of_injective, Multiset, Multiset.toFinset_map, RingHom, RingHom.injective, SplittingField, SplittingField.lift, SplittingField.splits, aroots, card_image_of_injective, classical, comp_algebraMap, injective, map_map, natSepDegree, roots_map, splits, toFinset_map
-/
theorem natSepDegree_eq_of_splits [DecidableEq E] (h : (f.map (algebraMap F E)).Splits) :
    f.natSepDegree = (f.aroots E).toFinset.card := by
  classical
  rw [aroots]; rw [← (SplittingField.lift f h).comp_algebraMap]; rw [← map_map]; rw [(SplittingField.splits f).roots_map]; rw [Multiset.toFinset_map]; rw [Finset.card_image_of_injective _ (RingHom.injective _)]; rw [natSepDegree]

variable (E) in
/--
theorem `natSepDegree_eq_of_isAlgClosed` / 定理 `natSepDegree_eq_of_isAlgClosed`

English:
theorem natSepDegree_eq_of_isAlgClosed
  given: [DecidableEq E] [IsAlgClosed E]
  proof: natSepDegree_eq_of_splits f (IsAlgClosed.splits _)

中文:
定理 natSepDegree_eq_of_isAlgClosed
  条件: [DecidableEq E] [IsAlgClosed E]
  证明: natSepDegree_eq_of_splits f (IsAlgClosed.splits _)

Depends on / 依赖: IsAlgClosed, IsAlgClosed.splits, natSepDegree_eq_of_splits, splits
-/
theorem natSepDegree_eq_of_isAlgClosed [DecidableEq E] [IsAlgClosed E] :
    f.natSepDegree = (f.aroots E).toFinset.card :=
  natSepDegree_eq_of_splits f (IsAlgClosed.splits _)

/--
theorem `natSepDegree_map` / 定理 `natSepDegree_map`

English:
theorem natSepDegree_map
  given: (f : E[X]) (i : E ->+* K)
  statement: (f.map i).natSepDegree = f.natSepDegree
  proof: by
  classical
  let _ := i.toAlgebra
  simp_rw [show i = algebraMap E K by rfl, natSepDegree_eq_of_isAlgClosed (AlgebraicClosure K),
    aroots_def, map_map, ← IsScalarTower.algebraMap_eq]

@[simp]

中文:
定理 natSepDegree_map
  条件: (f : E[X]) (i : E ->+* K)
  结论: (f.map i).natSepDegree = f.natSepDegree
  证明: by
  classical
  let _ := i.toAlgebra
  simp_rw [show i = algebraMap E K by rfl, natSepDegree_eq_of_isAlgClosed (AlgebraicClosure K),
    aroots_def, map_map, ← IsScalarTower.algebraMap_eq]

@[simp]

Depends on / 依赖: AlgebraicClosure, IsScalarTower, IsScalarTower.algebraMap_eq, algebraMap, algebraMap_eq, aroots_def, classical, i.toAlgebra, map_map, natSepDegree_eq_of_isAlgClosed, simp_rw, toAlgebra
-/
theorem natSepDegree_map (f : E[X]) (i : E ->+* K) : (f.map i).natSepDegree = f.natSepDegree := by
  classical
  let _ := i.toAlgebra
  simp_rw [show i = algebraMap E K by rfl, natSepDegree_eq_of_isAlgClosed (AlgebraicClosure K),
    aroots_def, map_map, ← IsScalarTower.algebraMap_eq]

@[simp]
/--
theorem `natSepDegree_C_mul` / 定理 `natSepDegree_C_mul`

English:
theorem natSepDegree_C_mul
  given: {x : F} (hx : x != 0)
  proof: by
  classical
  simp only [natSepDegree_eq_of_isAlgClosed (AlgebraicClosure F), aroots_C_mul _ hx]

@[simp]

中文:
定理 natSepDegree_C_mul
  条件: {x : F} (hx : x != 0)
  证明: by
  classical
  simp only [natSepDegree_eq_of_isAlgClosed (AlgebraicClosure F), aroots_C_mul _ hx]

@[simp]

Depends on / 依赖: AlgebraicClosure, aroots_C_mul, classical, natSepDegree_eq_of_isAlgClosed
-/
theorem natSepDegree_C_mul {x : F} (hx : x != 0) :
    (C x * f).natSepDegree = f.natSepDegree := by
  classical
  simp only [natSepDegree_eq_of_isAlgClosed (AlgebraicClosure F), aroots_C_mul _ hx]

@[simp]
/--
theorem `natSepDegree_smul_nonzero` / 定理 `natSepDegree_smul_nonzero`

English:
theorem natSepDegree_smul_nonzero
  given: {x : F} (hx : x != 0)
  proof: by
  classical
  simp only [natSepDegree_eq_of_isAlgClosed (AlgebraicClosure F), aroots_smul_nonzero _ hx]

@[simp]

中文:
定理 natSepDegree_smul_nonzero
  条件: {x : F} (hx : x != 0)
  证明: by
  classical
  simp only [natSepDegree_eq_of_isAlgClosed (AlgebraicClosure F), aroots_smul_nonzero _ hx]

@[simp]

Depends on / 依赖: AlgebraicClosure, aroots_smul_nonzero, classical, natSepDegree_eq_of_isAlgClosed
-/
theorem natSepDegree_smul_nonzero {x : F} (hx : x != 0) :
    (x • f).natSepDegree = f.natSepDegree := by
  classical
  simp only [natSepDegree_eq_of_isAlgClosed (AlgebraicClosure F), aroots_smul_nonzero _ hx]

@[simp]
/--
theorem `natSepDegree_pow` / 定理 `natSepDegree_pow`

English:
theorem natSepDegree_pow
  given: {n : Nat}
  statement: (f ^ n).natSepDegree = if n = 0 then 0 else f.natSepDegree
  proof: by
  classical
  simp only [natSepDegree_eq_of_isAlgClosed (AlgebraicClosure F), aroots_pow]
  by_cases h : n = 0
  · simp only [h, zero_smul, Multiset.toFinset_zero, Finset.card_empty, ite_true]
  simp only [h, Multiset.toFinset_nsmul _ n h, ite_false]

中文:
定理 natSepDegree_pow
  条件: {n : 自然数}
  结论: (f ^ n).natSepDegree = if n = 0 then 0 else f.natSepDegree
  证明: by
  classical
  simp only [natSepDegree_eq_of_isAlgClosed (AlgebraicClosure F), aroots_pow]
  by_cases h : n = 0
  · simp only [h, zero_smul, Multiset.toFinset_zero, Finset.card_empty, ite_true]
  simp only [h, Multiset.toFinset_nsmul _ n h, ite_false]

Depends on / 依赖: AlgebraicClosure, Finset, Finset.card_empty, Multiset, Multiset.toFinset_nsmul, Multiset.toFinset_zero, aroots_pow, card_empty, classical, ite_false, ite_true, natSepDegree_eq_of_isAlgClosed, toFinset_nsmul, toFinset_zero, zero_smul
-/
theorem natSepDegree_pow {n : Nat} : (f ^ n).natSepDegree = if n = 0 then 0 else f.natSepDegree := by
  classical
  simp only [natSepDegree_eq_of_isAlgClosed (AlgebraicClosure F), aroots_pow]
  by_cases h : n = 0
  · simp only [h, zero_smul, Multiset.toFinset_zero, Finset.card_empty, ite_true]
  simp only [h, Multiset.toFinset_nsmul _ n h, ite_false]

/--
theorem `natSepDegree_pow_of_ne_zero` / 定理 `natSepDegree_pow_of_ne_zero`

English:
theorem natSepDegree_pow_of_ne_zero
  given: {n : Nat} (hn : n != 0)
  proof: by simp_rw [natSepDegree_pow, hn, ite_false]

中文:
定理 natSepDegree_pow_of_ne_zero
  条件: {n : 自然数} (hn : n != 0)
  证明: by simp_rw [natSepDegree_pow, hn, ite_false]

Depends on / 依赖: ite_false, natSepDegree_pow, simp_rw
-/
theorem natSepDegree_pow_of_ne_zero {n : Nat} (hn : n != 0) :
    (f ^ n).natSepDegree = f.natSepDegree := by simp_rw [natSepDegree_pow, hn, ite_false]

/--
theorem `natSepDegree_X_pow` / 定理 `natSepDegree_X_pow`

English:
theorem natSepDegree_X_pow
  given: {n : Nat}
  statement: (X ^ n : F[X]).natSepDegree = if n = 0 then 0 else 1
  proof: by
  simp only [natSepDegree_pow, natSepDegree_X]

中文:
定理 natSepDegree_X_pow
  条件: {n : 自然数}
  结论: (X ^ n : F[X]).natSepDegree = if n = 0 then 0 else 1
  证明: by
  simp only [natSepDegree_pow, natSepDegree_X]

Depends on / 依赖: natSepDegree_X, natSepDegree_pow
-/
theorem natSepDegree_X_pow {n : Nat} : (X ^ n : F[X]).natSepDegree = if n = 0 then 0 else 1 := by
  simp only [natSepDegree_pow, natSepDegree_X]

/--
theorem `natSepDegree_X_sub_C_pow` / 定理 `natSepDegree_X_sub_C_pow`

English:
theorem natSepDegree_X_sub_C_pow
  given: {x : F} {n : Nat}
  proof: by
  simp only [natSepDegree_pow, natSepDegree_X_sub_C]

中文:
定理 natSepDegree_X_sub_C_pow
  条件: {x : F} {n : 自然数}
  证明: by
  simp only [natSepDegree_pow, natSepDegree_X_sub_C]

Depends on / 依赖: natSepDegree_X_sub_C, natSepDegree_pow
-/
theorem natSepDegree_X_sub_C_pow {x : F} {n : Nat} :
    ((X - C x) ^ n).natSepDegree = if n = 0 then 0 else 1 := by
  simp only [natSepDegree_pow, natSepDegree_X_sub_C]

/--
theorem `natSepDegree_C_mul_X_sub_C_pow` / 定理 `natSepDegree_C_mul_X_sub_C_pow`

English:
theorem natSepDegree_C_mul_X_sub_C_pow
  given: {x y : F} {n : Nat} (hx : x != 0)
  proof: by
  simp only [natSepDegree_C_mul _ hx, natSepDegree_X_sub_C_pow]

中文:
定理 natSepDegree_C_mul_X_sub_C_pow
  条件: {x y : F} {n : 自然数} (hx : x != 0)
  证明: by
  simp only [natSepDegree_C_mul _ hx, natSepDegree_X_sub_C_pow]

Depends on / 依赖: natSepDegree_C_mul, natSepDegree_X_sub_C_pow
-/
theorem natSepDegree_C_mul_X_sub_C_pow {x y : F} {n : Nat} (hx : x != 0) :
    (C x * (X - C y) ^ n).natSepDegree = if n = 0 then 0 else 1 := by
  simp only [natSepDegree_C_mul _ hx, natSepDegree_X_sub_C_pow]

/--
theorem `natSepDegree_mul` / 定理 `natSepDegree_mul`

English:
theorem natSepDegree_mul
  given: (g : F[X])
  proof: by
  by_cases h : f * g = 0
  · simp only [h, natSepDegree_zero, zero_le]
  classical
  simp_rw [natSepDegree_eq_of_isAlgClosed (AlgebraicClosure F), aroots_mul h, Multiset.toFinset_add]
  exact Finset.card_union_le _ _

中文:
定理 natSepDegree_mul
  条件: (g : F[X])
  证明: by
  by_cases h : f * g = 0
  · simp only [h, natSepDegree_zero, zero_le]
  classical
  simp_rw [natSepDegree_eq_of_isAlgClosed (AlgebraicClosure F), aroots_mul h, Multiset.toFinset_add]
  exact Finset.card_union_le _ _

Depends on / 依赖: AlgebraicClosure, Finset, Finset.card_union_le, Multiset, Multiset.toFinset_add, aroots_mul, card_union_le, classical, natSepDegree_eq_of_isAlgClosed, natSepDegree_zero, simp_rw, toFinset_add, zero_le
-/
theorem natSepDegree_mul (g : F[X]) :
    (f * g).natSepDegree <= f.natSepDegree + g.natSepDegree := by
  by_cases h : f * g = 0
  · simp only [h, natSepDegree_zero, zero_le]
  classical
  simp_rw [natSepDegree_eq_of_isAlgClosed (AlgebraicClosure F), aroots_mul h, Multiset.toFinset_add]
  exact Finset.card_union_le _ _

/--
theorem `natSepDegree_mul_eq_iff` / 定理 `natSepDegree_mul_eq_iff`

English:
theorem natSepDegree_mul_eq_iff
  given: (g : F[X])
  proof: by
  by_cases h : f * g = 0
  · rw [mul_eq_zero] at h
    wlog hf : f = 0 generalizing f g
    · simpa only [mul_comm, add_comm, and_comm,
        isCoprime_comm] using this g f h.symm (h.resolve_left hf)
    rw [hf]; rw [zero_mul]; rw [natSepDegree_zero]; rw [zero_add]; rw [isCoprime_zero_left]; rw

中文:
定理 natSepDegree_mul_eq_iff
  条件: (g : F[X])
  证明: by
  by_cases h : f * g = 0
  · rw [mul_eq_zero] at h
    wlog hf : f = 0 generalizing f g
    · simpa only [mul_comm, add_comm, and_comm,
        isCoprime_comm] using this g f h.symm (h.resolve_left hf)
    rw [hf]; rw [zero_mul]; rw [natSepDegree_zero]; rw [zero_add]; rw [isCoprime_zero_left]; rw

Depends on / 依赖: Ne.isUnit, add_comm, and_comm, eq_comm, generalizing, h.resolve_left, h.symm, isCoprime_comm, isCoprime_zero_left, isUnit, isUnit_iff, map_zero, mul_comm, mul_eq_zero, natDegree_eq_zero, natSepDegree_eq_zero_iff, natSepDegree_zero, resolve_left, zero_add, zero_mul
-/
theorem natSepDegree_mul_eq_iff (g : F[X]) :
    (f * g).natSepDegree = f.natSepDegree + g.natSepDegree ↔ (f = 0 ∧ g = 0) ∨ IsCoprime f g := by
  by_cases h : f * g = 0
  · rw [mul_eq_zero] at h
    wlog hf : f = 0 generalizing f g
    · simpa only [mul_comm, add_comm, and_comm,
        isCoprime_comm] using this g f h.symm (h.resolve_left hf)
    rw [hf]; rw [zero_mul]; rw [natSepDegree_zero]; rw [zero_add]; rw [isCoprime_zero_left]; rw [isUnit_iff]; rw [eq_comm]; rw [natSepDegree_eq_zero_iff]; rw [natDegree_eq_zero]
    refine ⟨fun ⟨x, h⟩ => ?_, ?_⟩
    · by_cases hx : x = 0
      · exact .inl ⟨rfl, by rw [← h, hx, map_zero]⟩
      exact .inr ⟨x, Ne.isUnit hx, h⟩
    rintro (⟨-, h⟩ | ⟨x, -, h⟩)
    · exact ⟨0, by rw [h, map_zero]⟩
    exact ⟨x, h⟩
  classical
  simp_rw [natSepDegree_eq_of_isAlgClosed (AlgebraicClosure F), aroots_mul h, Multiset.toFinset_add,
    Finset.card_union_eq_card_add_card, Finset.disjoint_iff_ne, Multiset.mem_toFinset, mem_aroots]
  rw [mul_eq_zero]; rw [not_or] at h
  refine ⟨fun H => .inr (isCoprime_of_irreducible_dvd (not_and.2 fun _ => h.2)
    fun u hu ⟨v, hf⟩ ⟨w, hg⟩ => ?_), ?_⟩
  · obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero
      (AlgebraicClosure F) _ (degree_pos_of_irreducible hu).ne'
    exact H x ⟨h.1, by simpa only [map_mul, hx, zero_mul] using congr(aeval x $hf)⟩
      x ⟨h.2, by simpa only [map_mul, hx, zero_mul] using congr(aeval x $hg)⟩ rfl
  rintro (⟨rfl, rfl⟩ | hc)
  · exact (h.1 rfl).elim
  rintro x hf _ hg rfl
  obtain ⟨u, v, hfg⟩ := hc
  simpa only [map_add, map_mul, map_one, hf.2, hg.2, mul_zero, add_zero,
zero_ne_one] using congr(aeval x hfg)

/--
theorem `natSepDegree_mul_of_isCoprime` / 定理 `natSepDegree_mul_of_isCoprime`

English:
theorem natSepDegree_mul_of_isCoprime
  given: (g : F[X]) (hc : IsCoprime f g)
  proof: (natSepDegree_mul_eq_iff f g).2 (.inr hc)

中文:
定理 natSepDegree_mul_of_isCoprime
  条件: (g : F[X]) (hc : IsCoprime f g)
  证明: (natSepDegree_mul_eq_iff f g).2 (.inr hc)

Depends on / 依赖: natSepDegree_mul_eq_iff
-/
theorem natSepDegree_mul_of_isCoprime (g : F[X]) (hc : IsCoprime f g) :
    (f * g).natSepDegree = f.natSepDegree + g.natSepDegree :=
  (natSepDegree_mul_eq_iff f g).2 (.inr hc)

/--
theorem `natSepDegree_le_of_dvd` / 定理 `natSepDegree_le_of_dvd`

English:
theorem natSepDegree_le_of_dvd
  given: (g : F[X]) (h1 : f ∣ g) (h2 : g != 0)
  proof: by
  classical
  simp_rw [natSepDegree_eq_of_isAlgClosed (AlgebraicClosure F)]
exact Finset.card_le_card Multiset.toFinset_subset.mpr
Multiset.Le.subset roots.le_of_dvd (map_ne_zero h2) map_dvd _ h1

中文:
定理 natSepDegree_le_of_dvd
  条件: (g : F[X]) (h1 : f ∣ g) (h2 : g != 0)
  证明: by
  classical
  simp_rw [natSepDegree_eq_of_isAlgClosed (AlgebraicClosure F)]
exact Finset.card_le_card Multiset.toFinset_subset.mpr
Multiset.Le.subset roots.le_of_dvd (map_ne_zero h2) map_dvd _ h1

Depends on / 依赖: AlgebraicClosure, Finset, Finset.card_le_card, Multiset, Multiset.Le.subset, Multiset.toFinset_subset.mpr, card_le_card, classical, le_of_dvd, map_dvd, map_ne_zero, natSepDegree_eq_of_isAlgClosed, roots.le_of_dvd, simp_rw, subset, toFinset_subset
-/
theorem natSepDegree_le_of_dvd (g : F[X]) (h1 : f ∣ g) (h2 : g != 0) :
    f.natSepDegree <= g.natSepDegree := by
  classical
  simp_rw [natSepDegree_eq_of_isAlgClosed (AlgebraicClosure F)]
exact Finset.card_le_card Multiset.toFinset_subset.mpr
Multiset.Le.subset roots.le_of_dvd (map_ne_zero h2) map_dvd _ h1

/--
theorem `natSepDegree_expand` / 定理 `natSepDegree_expand`

English:
theorem natSepDegree_expand
  given: (q : Nat) [hF : ExpChar F q] {n : Nat}
  proof: by
  obtain - | hprime := hF
  · simp only [one_pow, expand_one]
  have := Fact.mk hprime
  classical
  simpa only [natSepDegree_eq_of_isAlgClosed (AlgebraicClosure F), aroots_def, map_expand,
    Fintype.card_coe] using Fintype.card_eq.2
      ⟨(f.map (algebraMap F (AlgebraicClosure F))).rootsExpan

中文:
定理 natSepDegree_expand
  条件: (q : 自然数) [hF : ExpChar F q] {n : 自然数}
  证明: by
  obtain - | hprime := hF
  · simp only [one_pow, expand_one]
  have := Fact.mk hprime
  classical
  simpa only [natSepDegree_eq_of_isAlgClosed (AlgebraicClosure F), aroots_def, map_expand,
    Fintype.card_coe] using Fintype.card_eq.2
      ⟨(f.map (algebraMap F (AlgebraicClosure F))).rootsExpan

Depends on / 依赖: AlgebraicClosure, Fact.mk, Fintype, Fintype.card_coe, Fintype.card_eq, algebraMap, aroots_def, card_coe, card_eq, classical, expand_one, f.map, hprime, map_expand, natSepDegree_eq_of_isAlgClosed, one_pow, rootsExpandPowEquivRoots
-/
theorem natSepDegree_expand (q : Nat) [hF : ExpChar F q] {n : Nat} :
    (expand F (q ^ n) f).natSepDegree = f.natSepDegree := by
  obtain - | hprime := hF
  · simp only [one_pow, expand_one]
  have := Fact.mk hprime
  classical
  simpa only [natSepDegree_eq_of_isAlgClosed (AlgebraicClosure F), aroots_def, map_expand,
    Fintype.card_coe] using Fintype.card_eq.2
      ⟨(f.map (algebraMap F (AlgebraicClosure F))).rootsExpandPowEquivRoots q n⟩

/--
theorem `natSepDegree_X_pow_char_pow_sub_C` / 定理 `natSepDegree_X_pow_char_pow_sub_C`

English:
theorem natSepDegree_X_pow_char_pow_sub_C
  given: (q : Nat) [ExpChar F q] (n : Nat) (y : F)
  proof: by
  rw [← expand_X]; rw [← expand_C (q ^ n)]; rw [← map_sub]; rw [natSepDegree_expand]; rw [natSepDegree_X_sub_C]

中文:
定理 natSepDegree_X_pow_char_pow_sub_C
  条件: (q : 自然数) [ExpChar F q] (n : 自然数) (y : F)
  证明: by
  rw [← expand_X]; rw [← expand_C (q ^ n)]; rw [← map_sub]; rw [natSepDegree_expand]; rw [natSepDegree_X_sub_C]

Depends on / 依赖: expand_C, expand_X, map_sub, natSepDegree_X_sub_C, natSepDegree_expand
-/
theorem natSepDegree_X_pow_char_pow_sub_C (q : Nat) [ExpChar F q] (n : Nat) (y : F) :
    (X ^ q ^ n - C y).natSepDegree = 1 := by
  rw [← expand_X]; rw [← expand_C (q ^ n)]; rw [← map_sub]; rw [natSepDegree_expand]; rw [natSepDegree_X_sub_C]

variable {f} in
/--
theorem `IsSeparableContraction.natSepDegree_eq` / 定理 `IsSeparableContraction.natSepDegree_eq`

English:
theorem IsSeparableContraction.natSepDegree_eq
  statement: {g : Polynomial F} {q : Nat} [ExpChar F q]
  proof: by
  obtain ⟨h1, m, h2⟩ := h
  rw [← h2]; rw [natSepDegree_expand]; rw [h1.natSepDegree_eq_natDegree]

中文:
定理 IsSeparableContraction.natSepDegree_eq
  结论: {g : Polynomial F} {q : 自然数} [ExpChar F q]
  证明: by
  obtain ⟨h1, m, h2⟩ := h
  rw [← h2]; rw [natSepDegree_expand]; rw [h1.natSepDegree_eq_natDegree]

Depends on / 依赖: h1.natSepDegree_eq_natDegree, natSepDegree_eq_natDegree, natSepDegree_expand
-/
theorem IsSeparableContraction.natSepDegree_eq {g : Polynomial F} {q : Nat} [ExpChar F q]
    (h : IsSeparableContraction q f g) : f.natSepDegree = g.natDegree := by
  obtain ⟨h1, m, h2⟩ := h
  rw [← h2]; rw [natSepDegree_expand]; rw [h1.natSepDegree_eq_natDegree]

variable {f} in
/--
theorem `HasSeparableContraction.natSepDegree_eq` / 定理 `HasSeparableContraction.natSepDegree_eq`

English:
theorem HasSeparableContraction.natSepDegree_eq
  proof: hf.isSeparableContraction.natSepDegree_eq

中文:
定理 HasSeparableContraction.natSepDegree_eq
  证明: hf.isSeparableContraction.natSepDegree_eq

Depends on / 依赖: hf.isSeparableContraction.natSepDegree_eq, isSeparableContraction, natSepDegree_eq
-/
theorem HasSeparableContraction.natSepDegree_eq
    {q : Nat} [ExpChar F q] (hf : f.HasSeparableContraction q) :
    f.natSepDegree = hf.degree := hf.isSeparableContraction.natSepDegree_eq

end Polynomial

namespace Irreducible

variable {F}
variable {f : F[X]}

/--
theorem `natSepDegree_dvd_natDegree` / 定理 `natSepDegree_dvd_natDegree`

English:
theorem natSepDegree_dvd_natDegree
  given: (h : Irreducible f)
  proof: by
  obtain ⟨q, _⟩ := ExpChar.exists F
  have hf := h.hasSeparableContraction q
  rw [hf.natSepDegree_eq]
  exact hf.dvd_degree

中文:
定理 natSepDegree_dvd_natDegree
  条件: (h : Irreducible f)
  证明: by
  obtain ⟨q, _⟩ := ExpChar.exists F
  have hf := h.hasSeparableContraction q
  rw [hf.natSepDegree_eq]
  exact hf.dvd_degree

Depends on / 依赖: ExpChar, ExpChar.exists, dvd_degree, h.hasSeparableContraction, hasSeparableContraction, hf.dvd_degree, hf.natSepDegree_eq, natSepDegree_eq
-/
theorem natSepDegree_dvd_natDegree (h : Irreducible f) :
    f.natSepDegree ∣ f.natDegree := by
  obtain ⟨q, _⟩ := ExpChar.exists F
  have hf := h.hasSeparableContraction q
  rw [hf.natSepDegree_eq]
  exact hf.dvd_degree

/--
theorem `natSepDegree_eq_one_iff_of_monic'` / 定理 `natSepDegree_eq_one_iff_of_monic'`

English:
theorem natSepDegree_eq_one_iff_of_monic'
  statement: (q : Nat) [ExpChar F q] (hm : f.Monic)
  proof: by
  refine ⟨fun h => ?_, fun ⟨n, y, h⟩ => ?_⟩
  · obtain ⟨g, h1, n, rfl⟩ := hi.hasSeparableContraction q
    have h2 : g.natDegree = 1 := by
      rwa [natSepDegree_expand _ q, h1.natSepDegree_eq_natDegree] at h
    rw [((monic_expand_iff <| expChar_pow_pos F q n).mp hm).eq_X_add_C h2]
    exact ⟨n

中文:
定理 natSepDegree_eq_one_iff_of_monic'
  结论: (q : 自然数) [ExpChar F q] (hm : f.Monic)
  证明: by
  refine ⟨fun h => ?_, fun ⟨n, y, h⟩ => ?_⟩
  · obtain ⟨g, h1, n, rfl⟩ := hi.hasSeparableContraction q
    have h2 : g.natDegree = 1 := by
      rwa [natSepDegree_expand _ q, h1.natSepDegree_eq_natDegree] at h
    rw [((monic_expand_iff <| expChar_pow_pos F q n).mp hm).eq_X_add_C h2]
    exact ⟨n

Depends on / 依赖: eq_X_add_C, expChar_pow_pos, g.coeff, g.natDegree, h1.natSepDegree_eq_natDegree, hasSeparableContraction, hi.hasSeparableContraction, map_neg, monic_expand_iff, natDegree, natSepDegree_X_sub_C, natSepDegree_eq_natDegree, natSepDegree_expand, sub_neg_eq_add
-/
theorem natSepDegree_eq_one_iff_of_monic' (q : Nat) [ExpChar F q] (hm : f.Monic)
    (hi : Irreducible f) : f.natSepDegree = 1 ↔
    exists (n : Nat) (y : F), f = expand F (q ^ n) (X - C y) := by
  refine ⟨fun h => ?_, fun ⟨n, y, h⟩ => ?_⟩
  · obtain ⟨g, h1, n, rfl⟩ := hi.hasSeparableContraction q
    have h2 : g.natDegree = 1 := by
      rwa [natSepDegree_expand _ q, h1.natSepDegree_eq_natDegree] at h
    rw [((monic_expand_iff <| expChar_pow_pos F q n).mp hm).eq_X_add_C h2]
    exact ⟨n, -(g.coeff 0), by rw [map_neg, sub_neg_eq_add]⟩
  rw [h]; rw [natSepDegree_expand _ q]; rw [natSepDegree_X_sub_C]

/--
theorem `natSepDegree_eq_one_iff_of_monic` / 定理 `natSepDegree_eq_one_iff_of_monic`

English:
theorem natSepDegree_eq_one_iff_of_monic
  statement: (q : Nat) [ExpChar F q] (hm : f.Monic)
  proof: by
  simp_rw [hi.natSepDegree_eq_one_iff_of_monic' q hm, map_sub, expand_X, expand_C]

中文:
定理 natSepDegree_eq_one_iff_of_monic
  结论: (q : 自然数) [ExpChar F q] (hm : f.Monic)
  证明: by
  simp_rw [hi.natSepDegree_eq_one_iff_of_monic' q hm, map_sub, expand_X, expand_C]

Depends on / 依赖: expand_C, expand_X, hi.natSepDegree_eq_one_iff_of_monic, map_sub, natSepDegree_eq_one_iff_of_monic, simp_rw
-/
theorem natSepDegree_eq_one_iff_of_monic (q : Nat) [ExpChar F q] (hm : f.Monic)
    (hi : Irreducible f) : f.natSepDegree = 1 ↔ exists (n : Nat) (y : F), f = X ^ q ^ n - C y := by
  simp_rw [hi.natSepDegree_eq_one_iff_of_monic' q hm, map_sub, expand_X, expand_C]

end Irreducible

namespace Polynomial

namespace Monic

variable {F}
variable {f : F[X]}

alias natSepDegree_eq_one_iff_of_irreducible' := Irreducible.natSepDegree_eq_one_iff_of_monic'

alias natSepDegree_eq_one_iff_of_irreducible := Irreducible.natSepDegree_eq_one_iff_of_monic

/--
theorem `eq_X_sub_C_pow_of_natSepDegree_eq_one_of_splits` / 定理 `eq_X_sub_C_pow_of_natSepDegree_eq_one_of_splits`

English:
theorem eq_X_sub_C_pow_of_natSepDegree_eq_one_of_splits
  statement: (hm : f.Monic)
  proof: by
  classical
  have h1 := hs.eq_prod_roots_of_monic hm
  have h2 := (natSepDegree_eq_of_splits f (hs.map <| .id F)).symm
  rw [h]; rw [aroots_def]; rw [Algebra.algebraMap_self]; rw [map_id]; rw [Multiset.toFinset_card_eq_one_iff] at h2
  obtain ⟨h2, y, h3⟩ := h2
  exact ⟨_, y, h2, by rwa [h3, Mult

中文:
定理 eq_X_sub_C_pow_of_natSepDegree_eq_one_of_splits
  结论: (hm : f.Monic)
  证明: by
  classical
  have h1 := hs.eq_prod_roots_of_monic hm
  have h2 := (natSepDegree_eq_of_splits f (hs.map <| .id F)).symm
  rw [h]; rw [aroots_def]; rw [Algebra.algebraMap_self]; rw [map_id]; rw [Multiset.toFinset_card_eq_one_iff] at h2
  obtain ⟨h2, y, h3⟩ := h2
  exact ⟨_, y, h2, by rwa [h3, Mult

Depends on / 依赖: Algebra, Algebra.algebraMap_self, Multiset, Multiset.map_nsmul, Multiset.map_singleton, Multiset.prod_nsmul, Multiset.prod_singleton, Multiset.toFinset_card_eq_one_iff, algebraMap_self, aroots_def, classical, eq_prod_roots_of_monic, hs.eq_prod_roots_of_monic, hs.map, map_id, map_nsmul, map_singleton, natSepDegree_eq_of_splits, prod_nsmul, prod_singleton
-/
theorem eq_X_sub_C_pow_of_natSepDegree_eq_one_of_splits (hm : f.Monic)
    (hs : f.Splits)
    (h : f.natSepDegree = 1) : exists (m : Nat) (y : F), m != 0 ∧ f = (X - C y) ^ m := by
  classical
  have h1 := hs.eq_prod_roots_of_monic hm
  have h2 := (natSepDegree_eq_of_splits f (hs.map <| .id F)).symm
  rw [h]; rw [aroots_def]; rw [Algebra.algebraMap_self]; rw [map_id]; rw [Multiset.toFinset_card_eq_one_iff] at h2
  obtain ⟨h2, y, h3⟩ := h2
  exact ⟨_, y, h2, by rwa [h3, Multiset.map_nsmul, Multiset.map_singleton, Multiset.prod_nsmul,
    Multiset.prod_singleton] at h1⟩

/--
theorem `eq_X_pow_char_pow_sub_C_of_natSepDegree_eq_one_of_irreducible` / 定理 `eq_X_pow_char_pow_sub_C_of_natSepDegree_eq_one_of_irreducible`

English:
theorem eq_X_pow_char_pow_sub_C_of_natSepDegree_eq_one_of_irreducible
  statement: (q : Nat) [ExpChar F q]
  proof: by
  obtain ⟨n, y, hf⟩ := (hm.natSepDegree_eq_one_iff_of_irreducible q hi).1 h
  cases id ‹ExpChar F q› with
  | zero =>
    simp_rw [one_pow, pow_one] at hf ⊢
    exact ⟨0, y, .inl rfl, hf⟩
  | prime hq =>
    refine ⟨n, y, (em _).imp id fun hn ⟨z, hy⟩ => ?_, hf⟩
    have := expChar_of_injective_ri

中文:
定理 eq_X_pow_char_pow_sub_C_of_natSepDegree_eq_one_of_irreducible
  结论: (q : 自然数) [ExpChar F q]
  证明: by
  obtain ⟨n, y, hf⟩ := (hm.natSepDegree_eq_one_iff_of_irreducible q hi).1 h
  cases id ‹ExpChar F q› with
  | zero =>
    simp_rw [one_pow, pow_one] at hf ⊢
    exact ⟨0, y, .inl rfl, hf⟩
  | prime hq =>
    refine ⟨n, y, (em _).imp id fun hn ⟨z, hy⟩ => ?_, hf⟩
    have := expChar_of_injective_ri

Depends on / 依赖: C_injective, ExpChar, Nat.succ_pred, expChar_of_injective_ringHom, frobenius_def, hm.natSepDegree_eq_one_iff_of_irreducible, hq.ne_one, map_pow, natSepDegree_eq_one_iff_of_irreducible, ne_one, not_irreducible_pow, one_pow, pow_mul, pow_one, pow_succ, simp_rw, sub_pow_expChar, succ_pred
-/
theorem eq_X_pow_char_pow_sub_C_of_natSepDegree_eq_one_of_irreducible (q : Nat) [ExpChar F q]
    (hm : f.Monic) (hi : Irreducible f) (h : f.natSepDegree = 1) : exists (n : Nat) (y : F),
      (n = 0 ∨ y ∉ (frobenius F q).range) ∧ f = X ^ q ^ n - C y := by
  obtain ⟨n, y, hf⟩ := (hm.natSepDegree_eq_one_iff_of_irreducible q hi).1 h
  cases id ‹ExpChar F q› with
  | zero =>
    simp_rw [one_pow, pow_one] at hf ⊢
    exact ⟨0, y, .inl rfl, hf⟩
  | prime hq =>
    refine ⟨n, y, (em _).imp id fun hn ⟨z, hy⟩ => ?_, hf⟩
    have := expChar_of_injective_ringHom (R := F) C_injective q
    rw [hf]; rw [← Nat.succ_pred hn]; rw [pow_succ]; rw [pow_mul]; rw [← hy]; rw [frobenius_def]; rw [map_pow]; rw [← sub_pow_expChar] at hi
    exact not_irreducible_pow hq.ne_one hi

/--
theorem `eq_X_pow_char_pow_sub_C_pow_of_natSepDegree_eq_one` / 定理 `eq_X_pow_char_pow_sub_C_pow_of_natSepDegree_eq_one`

English:
theorem eq_X_pow_char_pow_sub_C_pow_of_natSepDegree_eq_one
  statement: (q : Nat) [ExpChar F q] (hm : f.Monic)
  proof: by
obtain ⟨p, hM, hI, hf⟩ := exists_monic_irreducible_factor _ not_isUnit_of_natDegree_pos _
 Nat.pos_of_ne_zero (natSepDegree_ne_zero_iff _).1 (h.symm ▸ Nat.one_ne_zero)
have hD := (h ▸ natSepDegree_le_of_dvd p f hf hm.ne_zero).antisymm
Nat.pos_of_ne_zero (natSepDegree_ne_zero_iff _).2 hI.natDegree

中文:
定理 eq_X_pow_char_pow_sub_C_pow_of_natSepDegree_eq_one
  结论: (q : 自然数) [ExpChar F q] (hm : f.Monic)
  证明: by
obtain ⟨p, hM, hI, hf⟩ := exists_monic_irreducible_factor _ not_isUnit_of_natDegree_pos _
 Nat.pos_of_ne_zero (natSepDegree_ne_zero_iff _).1 (h.symm ▸ Nat.one_ne_zero)
have hD := (h ▸ natSepDegree_le_of_dvd p f hf hm.ne_zero).antisymm
Nat.pos_of_ne_zero (natSepDegree_ne_zero_iff _).2 hI.natDegree

Depends on / 依赖: Nat.one_ne_zero, Nat.pos_of_ne_zero, antisymm, degree_pos_of_irreducible, eq_X_pow_char_pow_sub_C_of_natSepDegree_eq_one_of_irreducible, exists_monic_irreducible_factor, finiteMultiplicity_of_degree_pos_of_monic, h.symm, hI.natDegree_pos.ne, hM.eq_X_pow_char_pow_sub_C_of_natSepDegree_eq_one_of_irreducible, hm.ne_ze, hm.ne_zero, natDegree_pos, natSepDegree_le_of_dvd, natSepDegree_ne_zero_iff, ne_ze, ne_zero, not_isUnit_of_natDegree_pos, one_ne_zero, pos_of_ne_zero
-/
theorem eq_X_pow_char_pow_sub_C_pow_of_natSepDegree_eq_one (q : Nat) [ExpChar F q] (hm : f.Monic)
    (h : f.natSepDegree = 1) : exists (m n : Nat) (y : F),
      m != 0 ∧ (n = 0 ∨ y ∉ (frobenius F q).range) ∧ f = (X ^ q ^ n - C y) ^ m := by
obtain ⟨p, hM, hI, hf⟩ := exists_monic_irreducible_factor _ not_isUnit_of_natDegree_pos _
 Nat.pos_of_ne_zero (natSepDegree_ne_zero_iff _).1 (h.symm ▸ Nat.one_ne_zero)
have hD := (h ▸ natSepDegree_le_of_dvd p f hf hm.ne_zero).antisymm
Nat.pos_of_ne_zero (natSepDegree_ne_zero_iff _).2 hI.natDegree_pos.ne'
  obtain ⟨n, y, H, hp⟩ := hM.eq_X_pow_char_pow_sub_C_of_natSepDegree_eq_one_of_irreducible q hI hD
  have hF := finiteMultiplicity_of_degree_pos_of_monic (degree_pos_of_irreducible hI) hM hm.ne_zero
  have hne := (multiplicity_pos_of_dvd hf).ne'
  refine ⟨_, n, y, hne, H, ?_⟩
  obtain ⟨c, hf, H⟩ := hF.exists_eq_pow_mul_and_not_dvd
  rw [hf]; rw [natSepDegree_mul_of_isCoprime _ c <| IsCoprime.pow_left <|
    (hI.isCoprime_or_dvd c).resolve_right H]; rw [natSepDegree_pow_of_ne_zero _ hne]; rw [hD]; rw [add_eq_left]; rw [natSepDegree_eq_zero_iff] at h
  simpa only [eq_one_of_monic_natDegree_zero ((hM.pow _).of_mul_monic_left (hf ▸ hm)) h,
    mul_one, ← hp] using hf

/--
theorem `natSepDegree_eq_one_iff` / 定理 `natSepDegree_eq_one_iff`

English:
theorem natSepDegree_eq_one_iff
  given: (q : Nat) [ExpChar F q] (hm : f.Monic)
  proof: by
  refine ⟨fun h => ?_, fun ⟨m, n, y, hm, h⟩ => ?_⟩
  · obtain ⟨m, n, y, hm, -, h⟩ := hm.eq_X_pow_char_pow_sub_C_pow_of_natSepDegree_eq_one q h
    exact ⟨m, n, y, hm, h⟩
  simp_rw [h, natSepDegree_pow, hm, ite_false, natSepDegree_X_pow_char_pow_sub_C]

中文:
定理 natSepDegree_eq_one_iff
  条件: (q : 自然数) [ExpChar F q] (hm : f.Monic)
  证明: by
  refine ⟨fun h => ?_, fun ⟨m, n, y, hm, h⟩ => ?_⟩
  · obtain ⟨m, n, y, hm, -, h⟩ := hm.eq_X_pow_char_pow_sub_C_pow_of_natSepDegree_eq_one q h
    exact ⟨m, n, y, hm, h⟩
  simp_rw [h, natSepDegree_pow, hm, ite_false, natSepDegree_X_pow_char_pow_sub_C]

Depends on / 依赖: eq_X_pow_char_pow_sub_C_pow_of_natSepDegree_eq_one, hm.eq_X_pow_char_pow_sub_C_pow_of_natSepDegree_eq_one, ite_false, natSepDegree_X_pow_char_pow_sub_C, natSepDegree_pow, simp_rw
-/
theorem natSepDegree_eq_one_iff (q : Nat) [ExpChar F q] (hm : f.Monic) :
    f.natSepDegree = 1 ↔ exists (m n : Nat) (y : F), m != 0 ∧ f = (X ^ q ^ n - C y) ^ m := by
  refine ⟨fun h => ?_, fun ⟨m, n, y, hm, h⟩ => ?_⟩
  · obtain ⟨m, n, y, hm, -, h⟩ := hm.eq_X_pow_char_pow_sub_C_pow_of_natSepDegree_eq_one q h
    exact ⟨m, n, y, hm, h⟩
  simp_rw [h, natSepDegree_pow, hm, ite_false, natSepDegree_X_pow_char_pow_sub_C]

end Monic

end Polynomial

namespace minpoly

variable {F : Type u} {E : Type v} [Field F] [Ring E] [IsDomain E] [Algebra F E]
variable (q : Nat) [hF : ExpChar F q] {x : E}

/--
theorem `natSepDegree_eq_one_iff_eq_expand_X_sub_C` / 定理 `natSepDegree_eq_one_iff_eq_expand_X_sub_C`

English:
theorem natSepDegree_eq_one_iff_eq_expand_X_sub_C
  statement: (minpoly F x).natSepDegree = 1 ↔
  proof: by
  refine ⟨fun h => ?_, fun ⟨n, y, h⟩ => ?_⟩
  · have halg : IsIntegral F x := by_contra fun h' => by
      simp only [eq_zero h', natSepDegree_zero, zero_ne_one] at h
    exact (minpoly.irreducible halg).natSepDegree_eq_one_iff_of_monic' q
.1 h (minpoly.monic halg)
  rw [h]; rw [natSepDegree_expa

中文:
定理 natSepDegree_eq_one_iff_eq_expand_X_sub_C
  结论: (minpoly F x).natSepDegree = 1 ↔
  证明: by
  refine ⟨fun h => ?_, fun ⟨n, y, h⟩ => ?_⟩
  · have halg : IsIntegral F x := by_contra fun h' => by
      simp only [eq_zero h', natSepDegree_zero, zero_ne_one] at h
    exact (minpoly.irreducible halg).natSepDegree_eq_one_iff_of_monic' q
.1 h (minpoly.monic halg)
  rw [h]; rw [natSepDegree_expa

Depends on / 依赖: IsIntegral, eq_zero, irreducible, minpoly, minpoly.irreducible, minpoly.monic, natSepDegree_X_sub_C, natSepDegree_eq_one_iff_of_monic, natSepDegree_expand, natSepDegree_zero, zero_ne_one
-/
theorem natSepDegree_eq_one_iff_eq_expand_X_sub_C : (minpoly F x).natSepDegree = 1 ↔
    exists (n : Nat) (y : F), minpoly F x = expand F (q ^ n) (X - C y) := by
  refine ⟨fun h => ?_, fun ⟨n, y, h⟩ => ?_⟩
  · have halg : IsIntegral F x := by_contra fun h' => by
      simp only [eq_zero h', natSepDegree_zero, zero_ne_one] at h
    exact (minpoly.irreducible halg).natSepDegree_eq_one_iff_of_monic' q
.1 h (minpoly.monic halg)
  rw [h]; rw [natSepDegree_expand _ q]; rw [natSepDegree_X_sub_C]

/--
theorem `natSepDegree_eq_one_iff_eq_X_pow_sub_C` / 定理 `natSepDegree_eq_one_iff_eq_X_pow_sub_C`

English:
theorem natSepDegree_eq_one_iff_eq_X_pow_sub_C
  statement: (minpoly F x).natSepDegree = 1 ↔
  proof: by
  simp only [minpoly.natSepDegree_eq_one_iff_eq_expand_X_sub_C q, map_sub, expand_X, expand_C]

中文:
定理 natSepDegree_eq_one_iff_eq_X_pow_sub_C
  结论: (minpoly F x).natSepDegree = 1 ↔
  证明: by
  simp only [minpoly.natSepDegree_eq_one_iff_eq_expand_X_sub_C q, map_sub, expand_X, expand_C]

Depends on / 依赖: expand_C, expand_X, map_sub, minpoly, minpoly.natSepDegree_eq_one_iff_eq_expand_X_sub_C, natSepDegree_eq_one_iff_eq_expand_X_sub_C
-/
theorem natSepDegree_eq_one_iff_eq_X_pow_sub_C : (minpoly F x).natSepDegree = 1 ↔
    exists (n : Nat) (y : F), minpoly F x = X ^ q ^ n - C y := by
  simp only [minpoly.natSepDegree_eq_one_iff_eq_expand_X_sub_C q, map_sub, expand_X, expand_C]

/--
theorem `natSepDegree_eq_one_iff_pow_mem` / 定理 `natSepDegree_eq_one_iff_pow_mem`

English:
theorem natSepDegree_eq_one_iff_pow_mem
  statement: (minpoly F x).natSepDegree = 1 ↔
  proof: by
  convert_to _ ↔ exists (n : Nat) (y : F), Polynomial.aeval x (X ^ q ^ n - C y) = 0
  · simp_rw [RingHom.mem_range, map_sub, map_pow, aeval_C, aeval_X, sub_eq_zero, eq_comm]
  refine ⟨fun h => ?_, fun ⟨n, y, h⟩ => ?_⟩
  · obtain ⟨n, y, hx⟩ := (minpoly.natSepDegree_eq_one_iff_eq_X_pow_sub_C q).1 h

中文:
定理 natSepDegree_eq_one_iff_pow_mem
  结论: (minpoly F x).natSepDegree = 1 ↔
  证明: by
  convert_to _ ↔ exists (n : Nat) (y : F), Polynomial.aeval x (X ^ q ^ n - C y) = 0
  · simp_rw [RingHom.mem_range, map_sub, map_pow, aeval_C, aeval_X, sub_eq_zero, eq_comm]
  refine ⟨fun h => ?_, fun ⟨n, y, h⟩ => ?_⟩
  · obtain ⟨n, y, hx⟩ := (minpoly.natSepDegree_eq_one_iff_eq_X_pow_sub_C q).1 h

Depends on / 依赖: Polynomial, Polynomial.aeval, RingHom, RingHom.mem_range, X_pow_sub_C_ne_zero, aeval_C, aeval_X, convert_to, eq_comm, expChar_pow_pos, hnezero, map_pow, map_sub, mem_range, minpoly, minpoly.dvd, minpoly.natSepDegree_eq_one_iff_eq_X_pow_sub_C, natSepDegree_X_pow_char_pow_sub_C, natSepDegree_eq_one_iff_eq_X_pow_sub_C, natSepDegree_le_of_dvd
-/
theorem natSepDegree_eq_one_iff_pow_mem : (minpoly F x).natSepDegree = 1 ↔
    exists n : Nat, x ^ q ^ n in (algebraMap F E).range := by
  convert_to _ ↔ exists (n : Nat) (y : F), Polynomial.aeval x (X ^ q ^ n - C y) = 0
  · simp_rw [RingHom.mem_range, map_sub, map_pow, aeval_C, aeval_X, sub_eq_zero, eq_comm]
  refine ⟨fun h => ?_, fun ⟨n, y, h⟩ => ?_⟩
  · obtain ⟨n, y, hx⟩ := (minpoly.natSepDegree_eq_one_iff_eq_X_pow_sub_C q).1 h
    exact ⟨n, y, hx ▸ aeval F x⟩
  have hnezero := X_pow_sub_C_ne_zero (expChar_pow_pos F q n) y
  refine ((natSepDegree_le_of_dvd _ _ (minpoly.dvd F x h) hnezero).trans_eq <|
    natSepDegree_X_pow_char_pow_sub_C q n y).antisymm ?_
  rw [Nat.one_le_iff_ne_zero]; rw [natSepDegree_ne_zero_iff]; rw [← Nat.one_le_iff_ne_zero]
exact minpoly.natDegree_pos IsAlgebraic.isIntegral ⟨_, hnezero, h⟩

/--
theorem `natSepDegree_eq_one_iff_eq_X_sub_C_pow` / 定理 `natSepDegree_eq_one_iff_eq_X_sub_C_pow`

English:
theorem natSepDegree_eq_one_iff_eq_X_sub_C_pow
  statement: (minpoly F x).natSepDegree = 1 ↔
  proof: by
  have := expChar_of_injective_algebraMap (algebraMap F E).injective q
  have := expChar_of_injective_ringHom (C_injective (R := E)) q
  refine ⟨fun h => ?_, fun ⟨n, h⟩ => (natSepDegree_eq_one_iff_pow_mem q).2 ?_⟩
  · obtain ⟨n, y, h⟩ := (natSepDegree_eq_one_iff_eq_X_pow_sub_C q).1 h
    have hx 

中文:
定理 natSepDegree_eq_one_iff_eq_X_sub_C_pow
  结论: (minpoly F x).natSepDegree = 1 ↔
  证明: by
  have := expChar_of_injective_algebraMap (algebraMap F E).injective q
  have := expChar_of_injective_ringHom (C_injective (R := E)) q
  refine ⟨fun h => ?_, fun ⟨n, h⟩ => (natSepDegree_eq_one_iff_pow_mem q).2 ?_⟩
  · obtain ⟨n, y, h⟩ := (natSepDegree_eq_one_iff_eq_X_pow_sub_C q).1 h
    have hx 

Depends on / 依赖: C_injective, Polynomial, Polynomial.aeval, Polynomial.map_, Polynomial.map_sub, aeval_C, aeval_X, algebraMap, congr_arg, eq_comm, expChar_of_injective_algebraMap, expChar_of_injective_ringHom, h.symm, injective, map_, map_pow, map_sub, minpoly, minpoly.aeval, natSepDegree_eq_one_iff_eq_X_pow_sub_C
-/
theorem natSepDegree_eq_one_iff_eq_X_sub_C_pow : (minpoly F x).natSepDegree = 1 ↔
    exists n : Nat, (minpoly F x).map (algebraMap F E) = (X - C x) ^ q ^ n := by
  have := expChar_of_injective_algebraMap (algebraMap F E).injective q
  have := expChar_of_injective_ringHom (C_injective (R := E)) q
  refine ⟨fun h => ?_, fun ⟨n, h⟩ => (natSepDegree_eq_one_iff_pow_mem q).2 ?_⟩
  · obtain ⟨n, y, h⟩ := (natSepDegree_eq_one_iff_eq_X_pow_sub_C q).1 h
    have hx := congr_arg (Polynomial.aeval x) h.symm
    rw [minpoly.aeval]; rw [map_sub]; rw [map_pow]; rw [aeval_X]; rw [aeval_C]; rw [sub_eq_zero]; rw [eq_comm] at hx
    use n
    rw [h]; rw [Polynomial.map_sub]; rw [Polynomial.map_pow]; rw [map_X]; rw [map_C]; rw [hx]; rw [map_pow]; rw [← sub_pow_expChar_pow_of_commute _ _ (commute_X _)]
  apply_fun constantCoeff at h
  simp_rw [map_pow, map_sub, constantCoeff_apply, coeff_map, coeff_X_zero, coeff_C_zero] at h
  rw [zero_sub]; rw [neg_pow]; rw [neg_one_pow_expChar_pow] at h
  exact ⟨n, -(minpoly F x).coeff 0, by rw [map_neg, h, neg_mul, one_mul, neg_neg]⟩

end minpoly

namespace IntermediateField

/--
theorem `finSepDegree_adjoin_simple_eq_natSepDegree` / 定理 `finSepDegree_adjoin_simple_eq_natSepDegree`

English:
theorem finSepDegree_adjoin_simple_eq_natSepDegree
  given: {α : E} (halg : IsAlgebraic F α)
  proof: by
  have : finSepDegree F F⟮α⟯ = _ := Nat.card_congr
    (algHomAdjoinIntegralEquiv F (K := AlgebraicClosure F⟮α⟯) halg.isIntegral)
  classical
  rw [this]; rw [Nat.card_eq_fintype_card]; rw [natSepDegree_eq_of_isAlgClosed (E := AlgebraicClosure F⟮α⟯)]; rw [← Fintype.card_coe]
  simp_rw [Multiset.m

中文:
定理 finSepDegree_adjoin_simple_eq_natSepDegree
  条件: {α : E} (halg : IsAlgebraic F α)
  证明: by
  have : finSepDegree F F⟮α⟯ = _ := Nat.card_congr
    (algHomAdjoinIntegralEquiv F (K := AlgebraicClosure F⟮α⟯) halg.isIntegral)
  classical
  rw [this]; rw [Nat.card_eq_fintype_card]; rw [natSepDegree_eq_of_isAlgClosed (E := AlgebraicClosure F⟮α⟯)]; rw [← Fintype.card_coe]
  simp_rw [Multiset.m

Depends on / 依赖: AlgebraicClosure, Fintype, Fintype.card_coe, Multiset, Multiset.mem_toFinset, Nat.card_congr, Nat.card_eq_fintype_card, algHomAdjoinIntegralEquiv, card_coe, card_congr, card_eq_fintype_card, classical, finSepDegree, halg.isIntegral, isIntegral, mem_toFinset, natSepDegree_eq_of_isAlgClosed, simp_rw
-/
theorem finSepDegree_adjoin_simple_eq_natSepDegree {α : E} (halg : IsAlgebraic F α) :
    finSepDegree F F⟮α⟯ = (minpoly F α).natSepDegree := by
  have : finSepDegree F F⟮α⟯ = _ := Nat.card_congr
    (algHomAdjoinIntegralEquiv F (K := AlgebraicClosure F⟮α⟯) halg.isIntegral)
  classical
  rw [this]; rw [Nat.card_eq_fintype_card]; rw [natSepDegree_eq_of_isAlgClosed (E := AlgebraicClosure F⟮α⟯)]; rw [← Fintype.card_coe]
  simp_rw [Multiset.mem_toFinset]

-- The separable degree of `F⟮α⟯ / F` divides the degree of `F⟮α⟯ / F`.
-- Marked as `private` because it is a special case of `finSepDegree_dvd_finrank`.
/--
theorem `finSepDegree_adjoin_simple_dvd_finrank` / 定理 `finSepDegree_adjoin_simple_dvd_finrank`

English:
theorem finSepDegree_adjoin_simple_dvd_finrank
  given: (α : E)
  proof: by
  by_cases halg : IsAlgebraic F α
  · rw [finSepDegree_adjoin_simple_eq_natSepDegree F E halg, adjoin.finrank halg.isIntegral]
    exact (minpoly.irreducible halg.isIntegral).natSepDegree_dvd_natDegree
  have : finrank F F⟮α⟯ = 0 := finrank_of_infinite_dimensional fun _ =>
    halg ((AdjoinSimple

中文:
定理 finSepDegree_adjoin_simple_dvd_finrank
  条件: (α : E)
  证明: by
  by_cases halg : IsAlgebraic F α
  · rw [finSepDegree_adjoin_simple_eq_natSepDegree F E halg, adjoin.finrank halg.isIntegral]
    exact (minpoly.irreducible halg.isIntegral).natSepDegree_dvd_natDegree
  have : finrank F F⟮α⟯ = 0 := finrank_of_infinite_dimensional fun _ =>
    halg ((AdjoinSimple
-/
private theorem finSepDegree_adjoin_simple_dvd_finrank (α : E) :
    finSepDegree F F⟮α⟯ ∣ finrank F F⟮α⟯ := by
  by_cases halg : IsAlgebraic F α
  · rw [finSepDegree_adjoin_simple_eq_natSepDegree F E halg, adjoin.finrank halg.isIntegral]
    exact (minpoly.irreducible halg.isIntegral).natSepDegree_dvd_natDegree
  have : finrank F F⟮α⟯ = 0 := finrank_of_infinite_dimensional fun _ =>
    halg ((AdjoinSimple.isIntegral_gen F α).1 (IsIntegral.of_finite F _)).isAlgebraic
  rw [this]
  exact dvd_zero _

/--
theorem `finSepDegree_adjoin_simple_le_finrank` / 定理 `finSepDegree_adjoin_simple_le_finrank`

English:
theorem finSepDegree_adjoin_simple_le_finrank
  given: (α : E) (halg : IsAlgebraic F α)
  proof: by
  have := adjoin.finiteDimensional halg.isIntegral
exact Nat.le_of_dvd finrank_pos finSepDegree_adjoin_simple_dvd_finrank F E α

中文:
定理 finSepDegree_adjoin_simple_le_finrank
  条件: (α : E) (halg : IsAlgebraic F α)
  证明: by
  have := adjoin.finiteDimensional halg.isIntegral
exact Nat.le_of_dvd finrank_pos finSepDegree_adjoin_simple_dvd_finrank F E α

Depends on / 依赖: Nat.le_of_dvd, adjoin, adjoin.finiteDimensional, finSepDegree_adjoin_simple_dvd_finrank, finiteDimensional, finrank_pos, halg.isIntegral, isIntegral, le_of_dvd
-/
theorem finSepDegree_adjoin_simple_le_finrank (α : E) (halg : IsAlgebraic F α) :
    finSepDegree F F⟮α⟯ <= finrank F F⟮α⟯ := by
  have := adjoin.finiteDimensional halg.isIntegral
exact Nat.le_of_dvd finrank_pos finSepDegree_adjoin_simple_dvd_finrank F E α

/--
theorem `finSepDegree_adjoin_simple_eq_finrank_iff` / 定理 `finSepDegree_adjoin_simple_eq_finrank_iff`

English:
theorem finSepDegree_adjoin_simple_eq_finrank_iff
  given: (α : E) (halg : IsAlgebraic F α)
  proof: by
  rw [finSepDegree_adjoin_simple_eq_natSepDegree F E halg]; rw [adjoin.finrank halg.isIntegral]; rw [natSepDegree_eq_natDegree_iff _ (minpoly.ne_zero halg.isIntegral)]; rw [IsSeparable]

中文:
定理 finSepDegree_adjoin_simple_eq_finrank_iff
  条件: (α : E) (halg : IsAlgebraic F α)
  证明: by
  rw [finSepDegree_adjoin_simple_eq_natSepDegree F E halg]; rw [adjoin.finrank halg.isIntegral]; rw [natSepDegree_eq_natDegree_iff _ (minpoly.ne_zero halg.isIntegral)]; rw [IsSeparable]

Depends on / 依赖: Classical, Classical.indefiniteDescription, IsSeparable, adjoin, adjoin.finrank, exists_ne, finSepDegree_adjoin_simple_eq_natSepDegree, finrank, halg.isIntegral, indefiniteDescription, isIntegral, minpoly, minpoly.ne_zero, natSepDegree_eq_natDegree_iff, ne_zero
-/
theorem finSepDegree_adjoin_simple_eq_finrank_iff (α : E) (halg : IsAlgebraic F α) :
    finSepDegree F F⟮α⟯ = finrank F F⟮α⟯ ↔ IsSeparable F α := by
  rw [finSepDegree_adjoin_simple_eq_natSepDegree F E halg]; rw [adjoin.finrank halg.isIntegral]; rw [natSepDegree_eq_natDegree_iff _ (minpoly.ne_zero halg.isIntegral)]; rw [IsSeparable]

end IntermediateField

namespace Field

/--
theorem `finSepDegree_dvd_finrank` / 定理 `finSepDegree_dvd_finrank`

English:
theorem finSepDegree_dvd_finrank
  statement: finSepDegree F E ∣ finrank F E
  proof: by
  by_cases hfd : FiniteDimensional F E
  · rw [← finSepDegree_top F, ← finrank_top F E]
    refine induction_on_adjoin (fun K : IntermediateField F E => finSepDegree F K ∣ finrank F K)
      (by simp_rw [finSepDegree_bot, IntermediateField.finrank_bot, one_dvd]) (fun L x h => ?_) ⊤
have hdvd := m

中文:
定理 finSepDegree_dvd_finrank
  结论: finSepDegree F E ∣ finrank F E
  证明: by
  by_cases hfd : FiniteDimensional F E
  · rw [← finSepDegree_top F, ← finrank_top F E]
    refine induction_on_adjoin (fun K : IntermediateField F E => finSepDegree F K ∣ finrank F K)
      (by simp_rw [finSepDegree_bot, IntermediateField.finrank_bot, one_dvd]) (fun L x h => ?_) ⊤
have hdvd := m

Depends on / 依赖: FiniteDimensional, IntermediateField, IntermediateField.finrank_bot, Module, Module.finrank_mul_finrank, finSepDegree, finSepDegree_adjoin_simple_dvd_finrank, finSepDegree_bot, finSepDegree_mul_finSepDegree_of_isAlgebraic, finSepDegree_top, finrank, finrank_bot, finrank_mul_finrank, finrank_of_infinite_dimensional, finrank_top, induction_on_adjoin, mul_dvd_mul, one_dvd, simp_rw
-/
theorem finSepDegree_dvd_finrank : finSepDegree F E ∣ finrank F E := by
  by_cases hfd : FiniteDimensional F E
  · rw [← finSepDegree_top F, ← finrank_top F E]
    refine induction_on_adjoin (fun K : IntermediateField F E => finSepDegree F K ∣ finrank F K)
      (by simp_rw [finSepDegree_bot, IntermediateField.finrank_bot, one_dvd]) (fun L x h => ?_) ⊤
have hdvd := mul_dvd_mul h finSepDegree_adjoin_simple_dvd_finrank L E x
    set M := L⟮x⟯
    rwa [finSepDegree_mul_finSepDegree_of_isAlgebraic F L M,
      Module.finrank_mul_finrank F L M] at hdvd
  rw [finrank_of_infinite_dimensional hfd]
  exact dvd_zero _

/-- The separable degree of a finite extension `E / F` is smaller than the degree of `E / F`. -/
@[stacks 09HA "The inequality"]
/--
theorem `finSepDegree_le_finrank` / 定理 `finSepDegree_le_finrank`

English:
theorem finSepDegree_le_finrank
  given: [FiniteDimensional F E]
  proof: Nat.le_of_dvd finrank_pos finSepDegree_dvd_finrank F E

中文:
定理 finSepDegree_le_finrank
  条件: [FiniteDimensional F E]
  证明: Nat.le_of_dvd finrank_pos finSepDegree_dvd_finrank F E

Depends on / 依赖: Nat.le_of_dvd, finSepDegree_dvd_finrank, finrank_pos, le_of_dvd
-/
theorem finSepDegree_le_finrank [FiniteDimensional F E] :
finSepDegree F E <= finrank F E := Nat.le_of_dvd finrank_pos finSepDegree_dvd_finrank F E

/--
theorem `finSepDegree_eq_finrank_of_isSeparable` / 定理 `finSepDegree_eq_finrank_of_isSeparable`

English:
theorem finSepDegree_eq_finrank_of_isSeparable
  given: [Algebra.IsSeparable F E]
  proof: by
  wlog hfd : FiniteDimensional F E generalizing E with H
  · rw [finrank_of_infinite_dimensional hfd]
    obtain ⟨L, h, h'⟩ := exists_lt_finrank_of_infinite_dimensional hfd (finSepDegree F E)
    have hd := finSepDegree_mul_finSepDegree_of_isAlgebraic F L E
    rw [H L h] at hd
    by_cases hd' :

中文:
定理 finSepDegree_eq_finrank_of_isSeparable
  条件: [Algebra.IsSeparable F E]
  证明: by
  wlog hfd : FiniteDimensional F E generalizing E with H
  · rw [finrank_of_infinite_dimensional hfd]
    obtain ⟨L, h, h'⟩ := exists_lt_finrank_of_infinite_dimensional hfd (finSepDegree F E)
    have hd := finSepDegree_mul_finSepDegree_of_isAlgebraic F L E
    rw [H L h] at hd
    by_cases hd' :

Depends on / 依赖: FiniteDimensional, Nat.le_mul_of_pos_right, Nat.pos_of_ne_zero, exists_lt_finrank_of_infinite_dimensional, finSepDegree, finSepDegree_mul_finSepDegree_of_isAlgebraic, finSepDegree_top, finrank, finrank_of_infinite_dimensional, finrank_top, generalizing, induction_on_adjoin, le_mul_of_pos_right, mul_zero, pos_of_ne_zero
-/
theorem finSepDegree_eq_finrank_of_isSeparable [Algebra.IsSeparable F E] :
    finSepDegree F E = finrank F E := by
  wlog hfd : FiniteDimensional F E generalizing E with H
  · rw [finrank_of_infinite_dimensional hfd]
    obtain ⟨L, h, h'⟩ := exists_lt_finrank_of_infinite_dimensional hfd (finSepDegree F E)
    have hd := finSepDegree_mul_finSepDegree_of_isAlgebraic F L E
    rw [H L h] at hd
    by_cases hd' : finSepDegree L E = 0
    · rw [← hd, hd', mul_zero]
    linarith only [h', hd, Nat.le_mul_of_pos_right (finrank F L) (Nat.pos_of_ne_zero hd')]
  rw [← finSepDegree_top F]; rw [← finrank_top F E]
  refine induction_on_adjoin (fun K : IntermediateField F E => finSepDegree F K = finrank F K)
    (by simp_rw [finSepDegree_bot, IntermediateField.finrank_bot]) (fun L x h => ?_) ⊤
have heq : _ * _ = _ * _ := congr_arg₂ (· * ·) h
(finSepDegree_adjoin_simple_eq_finrank_iff L E x (IsAlgebraic.of_finite L x)).2
      IsSeparable.tower_top L (Algebra.IsSeparable.isSeparable F x)
  set M := L⟮x⟯
  rwa [finSepDegree_mul_finSepDegree_of_isAlgebraic F L M,
    Module.finrank_mul_finrank F L M] at heq

alias Algebra.IsSeparable.finSepDegree_eq := finSepDegree_eq_finrank_of_isSeparable

/-- If `E / F` is a finite extension, then its separable degree is equal to its degree if and
only if it is a separable extension. -/
@[stacks 09HA "The equality condition"]
/--
theorem `finSepDegree_eq_finrank_iff` / 定理 `finSepDegree_eq_finrank_iff`

English:
theorem finSepDegree_eq_finrank_iff
  given: [FiniteDimensional F E]
  proof: ⟨fun heq => ⟨fun x => by
    have halg := IsAlgebraic.of_finite F x
refine (finSepDegree_adjoin_simple_eq_finrank_iff F E x halg).1 le_antisymm
(finSepDegree_adjoin_simple_le_finrank F E x halg) le_of_not_gt fun h => ?_
    have := Nat.mul_lt_mul_of_lt_of_le' h (finSepDegree_le_finrank F⟮x⟯ E) Fin.p

中文:
定理 finSepDegree_eq_finrank_iff
  条件: [FiniteDimensional F E]
  证明: ⟨fun heq => ⟨fun x => by
    have halg := IsAlgebraic.of_finite F x
refine (finSepDegree_adjoin_simple_eq_finrank_iff F E x halg).1 le_antisymm
(finSepDegree_adjoin_simple_le_finrank F E x halg) le_of_not_gt fun h => ?_
    have := Nat.mul_lt_mul_of_lt_of_le' h (finSepDegree_le_finrank F⟮x⟯ E) Fin.p

Depends on / 依赖: Fin.pos, IsAlgebraic, IsAlgebraic.of_finite, Module, Module.finrank_mul_finrank, Nat.mul_lt_mul_of_lt_of_le, finSepDegree_adjoin_simple_eq_finrank_iff, finSepDegree_adjoin_simple_le_finrank, finSepDegree_eq_finrank_of_isSeparable, finSepDegree_le_finrank, finSepDegree_mul_finSepDegree_of_isAlgebraic, finrank_mul_finrank, le_antisymm, le_of_not_gt, mul_lt_mul_of_lt_of_le, of_finite
-/
theorem finSepDegree_eq_finrank_iff [FiniteDimensional F E] :
    finSepDegree F E = finrank F E ↔ Algebra.IsSeparable F E :=
  ⟨fun heq => ⟨fun x => by
    have halg := IsAlgebraic.of_finite F x
refine (finSepDegree_adjoin_simple_eq_finrank_iff F E x halg).1 le_antisymm
(finSepDegree_adjoin_simple_le_finrank F E x halg) le_of_not_gt fun h => ?_
    have := Nat.mul_lt_mul_of_lt_of_le' h (finSepDegree_le_finrank F⟮x⟯ E) Fin.pos'
    rw [finSepDegree_mul_finSepDegree_of_isAlgebraic F F⟮x⟯ E]; rw [Module.finrank_mul_finrank F F⟮x⟯ E] at this
    linarith only [heq, this]⟩, fun _ => finSepDegree_eq_finrank_of_isSeparable F E⟩

end Field

/--
lemma `IntermediateField.isSeparable_of_mem_isSeparable` / 引理 `IntermediateField.isSeparable_of_mem_isSeparable`

English:
lemma IntermediateField.isSeparable_of_mem_isSeparable
  statement: {L : IntermediateField F E}
  proof: by
  simpa only [IsSeparable, minpoly_eq] using Algebra.IsSeparable.isSeparable F (K := L) ⟨x, h⟩

中文:
引理 IntermediateField.isSeparable_of_mem_isSeparable
  结论: {L : 整数ermediateField F E}
  证明: by
  simpa only [IsSeparable, minpoly_eq] using Algebra.IsSeparable.isSeparable F (K := L) ⟨x, h⟩

Depends on / 依赖: Algebra, Algebra.IsSeparable.isSeparable, IsSeparable, isSeparable, minpoly_eq
-/
lemma IntermediateField.isSeparable_of_mem_isSeparable {L : IntermediateField F E}
    [Algebra.IsSeparable F L] {x : E} (h : x in L) : IsSeparable F x := by
  simpa only [IsSeparable, minpoly_eq] using Algebra.IsSeparable.isSeparable F (K := L) ⟨x, h⟩

/--
theorem `IntermediateField.isSeparable_adjoin_simple_iff_isSeparable` / 定理 `IntermediateField.isSeparable_adjoin_simple_iff_isSeparable`

English:
theorem IntermediateField.isSeparable_adjoin_simple_iff_isSeparable
  given: {x : E}
  proof: by
  refine ⟨fun _ => ?_, fun hsep => ?_⟩
· exact isSeparable_of_mem_isSeparable F E mem_adjoin_simple_self F x
  · have h := IsSeparable.isIntegral hsep
    have := adjoin.finiteDimensional h
    rwa [← finSepDegree_eq_finrank_iff,
      finSepDegree_adjoin_simple_eq_finrank_iff F E x h.isAlgebraic

中文:
定理 IntermediateField.isSeparable_adjoin_simple_iff_isSeparable
  条件: {x : E}
  证明: by
  refine ⟨fun _ => ?_, fun hsep => ?_⟩
· exact isSeparable_of_mem_isSeparable F E mem_adjoin_simple_self F x
  · have h := IsSeparable.isIntegral hsep
    have := adjoin.finiteDimensional h
    rwa [← finSepDegree_eq_finrank_iff,
      finSepDegree_adjoin_simple_eq_finrank_iff F E x h.isAlgebraic

Depends on / 依赖: IsSeparable, IsSeparable.isIntegral, adjoin, adjoin.finiteDimensional, finSepDegree_adjoin_simple_eq_finrank_iff, finSepDegree_eq_finrank_iff, finiteDimensional, h.isAlgebraic, isAlgebraic, isIntegral, isSeparable_of_mem_isSeparable, mem_adjoin_simple_self
-/
theorem IntermediateField.isSeparable_adjoin_simple_iff_isSeparable {x : E} :
    Algebra.IsSeparable F F⟮x⟯ ↔ IsSeparable F x := by
  refine ⟨fun _ => ?_, fun hsep => ?_⟩
· exact isSeparable_of_mem_isSeparable F E mem_adjoin_simple_self F x
  · have h := IsSeparable.isIntegral hsep
    have := adjoin.finiteDimensional h
    rwa [← finSepDegree_eq_finrank_iff,
      finSepDegree_adjoin_simple_eq_finrank_iff F E x h.isAlgebraic]

variable {E K} in
/--
theorem `IsSeparable.of_algebra_isSeparable_of_isSeparable` / 定理 `IsSeparable.of_algebra_isSeparable_of_isSeparable`

English:
theorem IsSeparable.of_algebra_isSeparable_of_isSeparable
  statement: [Algebra E K] [IsScalarTower F E K]
  proof: by
  set f := minpoly E x with hf
  let E' : IntermediateField F E := adjoin F f.coeffs
  have : FiniteDimensional F E' :=
    finiteDimensional_adjoin fun x _ => Algebra.IsSeparable.isIntegral F x
  let g : E'[X] := f.toSubring E'.toSubring (subset_adjoin F _)
  have h : g.map (algebraMap E' E) = f

中文:
定理 IsSeparable.of_algebra_isSeparable_of_isSeparable
  结论: [Algebra E K] [IsScalarTower F E K]
  证明: by
  set f := minpoly E x with hf
  let E' : IntermediateField F E := adjoin F f.coeffs
  have : FiniteDimensional F E' :=
    finiteDimensional_adjoin fun x _ => Algebra.IsSeparable.isIntegral F x
  let g : E'[X] := f.toSubring E'.toSubring (subset_adjoin F _)
  have h : g.map (algebraMap E' E) = f

Depends on / 依赖: Algebra, Algebra.IsSeparable.isIntegral, FiniteDimensional, IntermediateField, IsSeparable, adjoin, aeval_map_algebraMap, algebraMap, clear_value, coeffs, f.coeffs, f.map_toSubring, f.toSubring, finiteDimensional_adjoin, g.map, isIntegral, map_toSubring, mem_adjoin_simple_self, minpoly, restrictScalars
-/
theorem IsSeparable.of_algebra_isSeparable_of_isSeparable [Algebra E K] [IsScalarTower F E K]
    [Algebra.IsSeparable F E] {x : K} (hsep : IsSeparable E x) : IsSeparable F x := by
  set f := minpoly E x with hf
  let E' : IntermediateField F E := adjoin F f.coeffs
  have : FiniteDimensional F E' :=
    finiteDimensional_adjoin fun x _ => Algebra.IsSeparable.isIntegral F x
  let g : E'[X] := f.toSubring E'.toSubring (subset_adjoin F _)
  have h : g.map (algebraMap E' E) = f := f.map_toSubring E'.toSubring (subset_adjoin F _)
  clear_value g
  have hx : x in E'⟮x⟯.restrictScalars F := mem_adjoin_simple_self _ x
  have hzero : aeval x g = 0 := by
    simpa only [← hf, ← h, aeval_map_algebraMap] using minpoly.aeval E x
  have halg : IsIntegral E' x :=
.tower_top isIntegral_trans (R := F) (A := E) _ (IsSeparable.isIntegral hsep)
  simp only [IsSeparable, ← hf, ← h, separable_map] at hsep
replace hsep := hsep.of_dvd minpoly.dvd E' x hzero
  have : Algebra.IsSeparable F E' := Algebra.isSeparable_tower_bot_of_isSeparable F E' E
  have := (isSeparable_adjoin_simple_iff_isSeparable _ _).2 hsep
  have := adjoin.finiteDimensional halg
  have : FiniteDimensional F E'⟮x⟯ := FiniteDimensional.trans F E' E'⟮x⟯
  have := finSepDegree_mul_finSepDegree_of_isAlgebraic F E' E'⟮x⟯
  rw [finSepDegree_eq_finrank_of_isSeparable F E']; rw [finSepDegree_eq_finrank_of_isSeparable E' E'⟮x⟯]; rw [Module.finrank_mul_finrank F E' E'⟮x⟯]; rw [eq_comm]; rw [finSepDegree_eq_finrank_iff F E'⟮x⟯] at this
  change Algebra.IsSeparable F (restrictScalars F E'⟮x⟯) at this
  exact isSeparable_of_mem_isSeparable F K hx

/-- If `E / F` and `K / E` are both separable extensions, then `K / F` is also separable. -/
@[stacks 09HB]
/--
theorem `Algebra.IsSeparable.trans` / 定理 `Algebra.IsSeparable.trans`

English:
theorem Algebra.IsSeparable.trans
  statement: [Algebra E K] [IsScalarTower F E K]
  proof: ⟨fun x => IsSeparable.of_algebra_isSeparable_of_isSeparable F
    (Algebra.IsSeparable.isSeparable E x)⟩

中文:
定理 Algebra.IsSeparable.trans
  结论: [Algebra E K] [IsScalarTower F E K]
  证明: ⟨fun x => IsSeparable.of_algebra_isSeparable_of_isSeparable F
    (Algebra.IsSeparable.isSeparable E x)⟩

Depends on / 依赖: Algebra, Algebra.IsSeparable.isSeparable, IsSeparable, IsSeparable.of_algebra_isSeparable_of_isSeparable, isSeparable, of_algebra_isSeparable_of_isSeparable
-/
theorem Algebra.IsSeparable.trans [Algebra E K] [IsScalarTower F E K]
    [Algebra.IsSeparable F E] [Algebra.IsSeparable E K] : Algebra.IsSeparable F K :=
  ⟨fun x => IsSeparable.of_algebra_isSeparable_of_isSeparable F
    (Algebra.IsSeparable.isSeparable E x)⟩

/--
theorem `IntermediateField.isSeparable_adjoin_pair_of_isSeparable` / 定理 `IntermediateField.isSeparable_adjoin_pair_of_isSeparable`

English:
theorem IntermediateField.isSeparable_adjoin_pair_of_isSeparable
  statement: {x y : E}
  proof: by
  rw [← adjoin_simple_adjoin_simple]
  replace hy := IsSeparable.tower_top F⟮x⟯ hy
  rw [← isSeparable_adjoin_simple_iff_isSeparable] at hx hy
  exact Algebra.IsSeparable.trans F F⟮x⟯ F⟮x⟯⟮y⟯

中文:
定理 IntermediateField.isSeparable_adjoin_pair_of_isSeparable
  结论: {x y : E}
  证明: by
  rw [← adjoin_simple_adjoin_simple]
  replace hy := IsSeparable.tower_top F⟮x⟯ hy
  rw [← isSeparable_adjoin_simple_iff_isSeparable] at hx hy
  exact Algebra.IsSeparable.trans F F⟮x⟯ F⟮x⟯⟮y⟯

Depends on / 依赖: Algebra, Algebra.IsSeparable.trans, IsSeparable, IsSeparable.tower_top, adjoin_simple_adjoin_simple, isSeparable_adjoin_simple_iff_isSeparable, replace, tower_top
-/
theorem IntermediateField.isSeparable_adjoin_pair_of_isSeparable {x y : E}
    (hx : IsSeparable F x) (hy : IsSeparable F y) :
    Algebra.IsSeparable F F⟮x, y⟯ := by
  rw [← adjoin_simple_adjoin_simple]
  replace hy := IsSeparable.tower_top F⟮x⟯ hy
  rw [← isSeparable_adjoin_simple_iff_isSeparable] at hx hy
  exact Algebra.IsSeparable.trans F F⟮x⟯ F⟮x⟯⟮y⟯

namespace Field

variable {F E}

/--
theorem `isSeparable_mul` / 定理 `isSeparable_mul`

English:
theorem isSeparable_mul
  given: {x y : E} (hx : IsSeparable F x) (hy : IsSeparable F y)
  proof: haveI := isSeparable_adjoin_pair_of_isSeparable F E hx hy
isSeparable_of_mem_isSeparable F E F⟮x, y⟯.mul_mem (subset_adjoin F _ (.inl rfl))
    (subset_adjoin F _ (.inr rfl))

中文:
定理 isSeparable_mul
  条件: {x y : E} (hx : IsSeparable F x) (hy : IsSeparable F y)
  证明: haveI := isSeparable_adjoin_pair_of_isSeparable F E hx hy
isSeparable_of_mem_isSeparable F E F⟮x, y⟯.mul_mem (subset_adjoin F _ (.inl rfl))
    (subset_adjoin F _ (.inr rfl))

Depends on / 依赖: isSeparable_adjoin_pair_of_isSeparable, isSeparable_of_mem_isSeparable, mul_mem, subset_adjoin
-/
theorem isSeparable_mul {x y : E} (hx : IsSeparable F x) (hy : IsSeparable F y) :
    IsSeparable F (x * y) :=
  haveI := isSeparable_adjoin_pair_of_isSeparable F E hx hy
isSeparable_of_mem_isSeparable F E F⟮x, y⟯.mul_mem (subset_adjoin F _ (.inl rfl))
    (subset_adjoin F _ (.inr rfl))

/--
theorem `isSeparable_add` / 定理 `isSeparable_add`

English:
theorem isSeparable_add
  given: {x y : E} (hx : IsSeparable F x) (hy : IsSeparable F y)
  proof: haveI := isSeparable_adjoin_pair_of_isSeparable F E hx hy
isSeparable_of_mem_isSeparable F E F⟮x, y⟯.add_mem (subset_adjoin F _ (.inl rfl))
    (subset_adjoin F _ (.inr rfl))

中文:
定理 isSeparable_add
  条件: {x y : E} (hx : IsSeparable F x) (hy : IsSeparable F y)
  证明: haveI := isSeparable_adjoin_pair_of_isSeparable F E hx hy
isSeparable_of_mem_isSeparable F E F⟮x, y⟯.add_mem (subset_adjoin F _ (.inl rfl))
    (subset_adjoin F _ (.inr rfl))

Depends on / 依赖: add_mem, isSeparable_adjoin_pair_of_isSeparable, isSeparable_of_mem_isSeparable, subset_adjoin
-/
theorem isSeparable_add {x y : E} (hx : IsSeparable F x) (hy : IsSeparable F y) :
    IsSeparable F (x + y) :=
  haveI := isSeparable_adjoin_pair_of_isSeparable F E hx hy
isSeparable_of_mem_isSeparable F E F⟮x, y⟯.add_mem (subset_adjoin F _ (.inl rfl))
    (subset_adjoin F _ (.inr rfl))

/--
theorem `isSeparable_neg` / 定理 `isSeparable_neg`

English:
theorem isSeparable_neg
  given: {x : E} (hx : IsSeparable F x)
  proof: haveI := (isSeparable_adjoin_simple_iff_isSeparable F E).2 hx
isSeparable_of_mem_isSeparable F E F⟮x⟯.neg_mem mem_adjoin_simple_self F x

中文:
定理 isSeparable_neg
  条件: {x : E} (hx : IsSeparable F x)
  证明: haveI := (isSeparable_adjoin_simple_iff_isSeparable F E).2 hx
isSeparable_of_mem_isSeparable F E F⟮x⟯.neg_mem mem_adjoin_simple_self F x

Depends on / 依赖: isSeparable_adjoin_simple_iff_isSeparable, isSeparable_of_mem_isSeparable, mem_adjoin_simple_self, neg_mem
-/
theorem isSeparable_neg {x : E} (hx : IsSeparable F x) :
    IsSeparable F (-x) :=
  haveI := (isSeparable_adjoin_simple_iff_isSeparable F E).2 hx
isSeparable_of_mem_isSeparable F E F⟮x⟯.neg_mem mem_adjoin_simple_self F x

/--
theorem `isSeparable_sub` / 定理 `isSeparable_sub`

English:
theorem isSeparable_sub
  given: {x y : E} (hx : IsSeparable F x) (hy : IsSeparable F y)
  proof: haveI := isSeparable_adjoin_pair_of_isSeparable F E hx hy
isSeparable_of_mem_isSeparable F E F⟮x, y⟯.sub_mem (subset_adjoin F _ (.inl rfl))
    (subset_adjoin F _ (.inr rfl))

中文:
定理 isSeparable_sub
  条件: {x y : E} (hx : IsSeparable F x) (hy : IsSeparable F y)
  证明: haveI := isSeparable_adjoin_pair_of_isSeparable F E hx hy
isSeparable_of_mem_isSeparable F E F⟮x, y⟯.sub_mem (subset_adjoin F _ (.inl rfl))
    (subset_adjoin F _ (.inr rfl))

Depends on / 依赖: isSeparable_adjoin_pair_of_isSeparable, isSeparable_of_mem_isSeparable, sub_mem, subset_adjoin
-/
theorem isSeparable_sub {x y : E} (hx : IsSeparable F x) (hy : IsSeparable F y) :
    IsSeparable F (x - y) :=
  haveI := isSeparable_adjoin_pair_of_isSeparable F E hx hy
isSeparable_of_mem_isSeparable F E F⟮x, y⟯.sub_mem (subset_adjoin F _ (.inl rfl))
    (subset_adjoin F _ (.inr rfl))

/--
theorem `isSeparable_inv` / 定理 `isSeparable_inv`

English:
theorem isSeparable_inv
  given: {x : E} (hx : IsSeparable F x)
  statement: IsSeparable F x⁻¹
  proof: haveI := (isSeparable_adjoin_simple_iff_isSeparable F E).2 hx
isSeparable_of_mem_isSeparable F E F⟮x⟯.inv_mem mem_adjoin_simple_self F x

中文:
定理 isSeparable_inv
  条件: {x : E} (hx : IsSeparable F x)
  结论: IsSeparable F x⁻¹
  证明: haveI := (isSeparable_adjoin_simple_iff_isSeparable F E).2 hx
isSeparable_of_mem_isSeparable F E F⟮x⟯.inv_mem mem_adjoin_simple_self F x

Depends on / 依赖: inv_mem, isSeparable_adjoin_simple_iff_isSeparable, isSeparable_of_mem_isSeparable, mem_adjoin_simple_self
-/
theorem isSeparable_inv {x : E} (hx : IsSeparable F x) : IsSeparable F x⁻¹ :=
  haveI := (isSeparable_adjoin_simple_iff_isSeparable F E).2 hx
isSeparable_of_mem_isSeparable F E F⟮x⟯.inv_mem mem_adjoin_simple_self F x

end Field

/--
theorem `perfectField_iff_splits_of_natSepDegree_eq_one` / 定理 `perfectField_iff_splits_of_natSepDegree_eq_one`

English:
theorem perfectField_iff_splits_of_natSepDegree_eq_one
  given: (F : Type*) [Field F]
  proof: by
  refine ⟨fun ⟨h⟩ f hf => ?_, fun h => ?_⟩
  · have hf0 : f != 0 := by aesop
    obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hf0
    rw [← hu]
    refine (Splits.multisetProd fun g hg => ?_).mul u.isUnit.splits
    specialize h (UniqueFactorizationMonoid.irreducible_of_factor g hg)
 

中文:
定理 perfectField_iff_splits_of_natSepDegree_eq_one
  条件: (F : 类型) [Field F]
  证明: by
  refine ⟨fun ⟨h⟩ f hf => ?_, fun h => ?_⟩
  · have hf0 : f != 0 := by aesop
    obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hf0
    rw [← hu]
    refine (Splits.multisetProd fun g hg => ?_).mul u.isUnit.splits
    specialize h (UniqueFactorizationMonoid.irreducible_of_factor g hg)
 

Depends on / 依赖: ExpChar, ExpChar.exists, Splits, Splits.multisetProd, Splits.of_natDegree_le_one, UniqueFactorizationMonoid, UniqueFactorizationMonoid.dvd_of_mem_factors, UniqueFactorizationMonoid.factors_prod, UniqueFactorizationMonoid.irreducible_of_factor, dvd_of_mem_factors, factors_prod, h.natSepDegree_eq_natDegree, irreducible_of_factor, isUnit, multisetProd, natSepDegree_eq_natDegree, natSepDegree_le_of_dvd, of_natDegree_le_one, specialize, splits
-/
theorem perfectField_iff_splits_of_natSepDegree_eq_one (F : Type*) [Field F] :
    PerfectField F ↔ forall f : F[X], f.natSepDegree = 1 -> Splits f := by
  refine ⟨fun ⟨h⟩ f hf => ?_, fun h => ?_⟩
  · have hf0 : f != 0 := by aesop
    obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hf0
    rw [← hu]
    refine (Splits.multisetProd fun g hg => ?_).mul u.isUnit.splits
    specialize h (UniqueFactorizationMonoid.irreducible_of_factor g hg)
    have key := natSepDegree_le_of_dvd g f (UniqueFactorizationMonoid.dvd_of_mem_factors hg) hf0
    rw [h.natSepDegree_eq_natDegree]; rw [hf] at key
    exact Splits.of_natDegree_le_one key
  obtain ⟨p, _⟩ := ExpChar.exists F
  have := PerfectRing.ofSurjective F p fun x => by
    obtain ⟨y, hy⟩ := Splits.exists_eval_eq_zero
      (h _ (pow_one p ▸ natSepDegree_X_pow_char_pow_sub_C p 1 x))
      ((degree_X_pow_sub_C (expChar_pos F p) x).symm ▸ Nat.cast_pos.2 (expChar_pos F p)).ne'
    exact ⟨y, by rwa [eval_sub, eval_X_pow, eval_C, sub_eq_zero] at hy⟩
  exact PerfectRing.toPerfectField F p

variable {E K} in
/--
theorem `PerfectField.splits_of_natSepDegree_eq_one` / 定理 `PerfectField.splits_of_natSepDegree_eq_one`

English:
theorem PerfectField.splits_of_natSepDegree_eq_one
  statement: [PerfectField K] {f : E[X]}
  proof: (perfectField_iff_splits_of_natSepDegree_eq_one K).mp ‹_› _ (natSepDegree_map K f i ▸ hf)

中文:
定理 PerfectField.splits_of_natSepDegree_eq_one
  结论: [PerfectField K] {f : E[X]}
  证明: (perfectField_iff_splits_of_natSepDegree_eq_one K).mp ‹_› _ (natSepDegree_map K f i ▸ hf)

Depends on / 依赖: natSepDegree_map, perfectField_iff_splits_of_natSepDegree_eq_one
-/
theorem PerfectField.splits_of_natSepDegree_eq_one [PerfectField K] {f : E[X]}
    (i : E ->+* K) (hf : f.natSepDegree = 1) : (f.map i).Splits :=
  (perfectField_iff_splits_of_natSepDegree_eq_one K).mp ‹_› _ (natSepDegree_map K f i ▸ hf)
