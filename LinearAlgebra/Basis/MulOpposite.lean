/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Basis of an opposite space

This file defines the basis of an opposite space and shows
that the opposite space is finite-dimensional and free when the original space is.
-/

@[expose] public section

open Module MulOpposite

variable {R H : Type*}

namespace Module.Basis

variable {ι : Type*} [Semiring R] [AddCommMonoid H] [Module R H]

/--
Definition of `mulOpposite` / `mulOpposite` 的定义

English:
definition mulOpposite
  signature: (b : Basis ι R H)
  body: b.map (opLinearEquiv R)

@[simp]

中文:
定义 mulOpposite
  签名: (b : Basis ι R H)
  定义体: b.map (opLinearEquiv R)

@[simp]

Depends on / 依赖: b.map, opLinearEquiv
-/
noncomputable def mulOpposite (b : Basis ι R H) : Basis ι R Hᵐᵒᵖ :=
  b.map (opLinearEquiv R)

@[simp]
/--
theorem `mulOpposite_apply` / 定理 `mulOpposite_apply`

English:
theorem mulOpposite_apply
  given: (b : Basis ι R H) (i : ι)
  proof: rfl

中文:
定理 mulOpposite_apply
  条件: (b : Basis ι R H) (i : ι)
  证明: rfl
-/
theorem mulOpposite_apply (b : Basis ι R H) (i : ι) :
    b.mulOpposite i = op (b i) := rfl

/--
theorem `mulOpposite_repr_eq` / 定理 `mulOpposite_repr_eq`

English:
theorem mulOpposite_repr_eq
  given: (b : Basis ι R H)
  proof: rfl

@[simp]

中文:
定理 mulOpposite_repr_eq
  条件: (b : Basis ι R H)
  证明: rfl

@[simp]
-/
theorem mulOpposite_repr_eq (b : Basis ι R H) :
    b.mulOpposite.repr = (opLinearEquiv R).symm.trans b.repr := rfl

@[simp]
/--
theorem `repr_unop_eq_mulOpposite_repr` / 定理 `repr_unop_eq_mulOpposite_repr`

English:
theorem repr_unop_eq_mulOpposite_repr
  given: (b : Basis ι R H) (x : Hᵐᵒᵖ)
  proof: rfl

@[simp]

中文:
定理 repr_unop_eq_mulOpposite_repr
  条件: (b : Basis ι R H) (x : Hᵐᵒᵖ)
  证明: rfl

@[simp]
-/
theorem repr_unop_eq_mulOpposite_repr (b : Basis ι R H) (x : Hᵐᵒᵖ) :
    b.repr (unop x) = b.mulOpposite.repr x := rfl

@[simp]
/--
theorem `mulOpposite_repr_op` / 定理 `mulOpposite_repr_op`

English:
theorem mulOpposite_repr_op
  given: (b : Basis ι R H) (x : H)
  proof: rfl

中文:
定理 mulOpposite_repr_op
  条件: (b : Basis ι R H) (x : H)
  证明: rfl
-/
theorem mulOpposite_repr_op (b : Basis ι R H) (x : H) :
    b.mulOpposite.repr (op x) = b.repr x := rfl

end Module.Basis

namespace MulOpposite

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DivisionRing
  signature: R] [AddCommGroup H] [Module R H]
  body: FiniteDimensional.of_finite_basis
  (Basis.ofVectorSpace R H).mulOpposite (Basis.ofVectorSpaceIndex R H).toFinite

中文:
实例 [DivisionRing
  签名: R] [AddCommGroup H] [Module R H]
  定义体: FiniteDimensional.of_finite_basis
  (Basis.ofVectorSpace R H).mulOpposite (Basis.ofVectorSpaceIndex R H).toFinite

Depends on / 依赖: FiniteDimensional, FiniteDimensional.of_finite_basis, of_finite_basis
-/
instance [DivisionRing R] [AddCommGroup H] [Module R H]
    [FiniteDimensional R H] : FiniteDimensional R Hᵐᵒᵖ := FiniteDimensional.of_finite_basis
  (Basis.ofVectorSpace R H).mulOpposite (Basis.ofVectorSpaceIndex R H).toFinite

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: R] [AddCommMonoid H] [Module R H]
  body: let ⟨b⟩ := Module.Free.exists_basis (R := R) (M := H)
  Module.Free.of_basis b.2.mulOpposite

中文:
实例 [Semiring
  签名: R] [AddCommMonoid H] [Module R H]
  定义体: let ⟨b⟩ := Module.Free.exists_basis (R := R) (M := H)
  Module.Free.of_basis b.2.mulOpposite

Depends on / 依赖: Module, Module.Free.exists_basis, Module.Free.of_basis, exists_basis, mulOpposite, of_basis
-/
instance [Semiring R] [AddCommMonoid H] [Module R H]
    [Module.Free R H] : Module.Free R Hᵐᵒᵖ :=
  let ⟨b⟩ := Module.Free.exists_basis (R := R) (M := H)
  Module.Free.of_basis b.2.mulOpposite

/--
theorem `rank` / 定理 `rank`

English:
theorem rank
  statement: [Semiring R] [StrongRankCondition R] [AddCommMonoid H] [Module R H]
  proof: Module.nonempty_linearEquiv_iff_rank_eq.mp ⟨(opLinearEquiv R).symm⟩

中文:
定理 rank
  结论: [Semiring R] [StrongRankCondition R] [AddCommMonoid H] [Module R H]
  证明: Module.nonempty_linearEquiv_iff_rank_eq.mp ⟨(opLinearEquiv R).symm⟩

Depends on / 依赖: Module, Module.nonempty_linearEquiv_iff_rank_eq.mp, nonempty_linearEquiv_iff_rank_eq, opLinearEquiv
-/
theorem rank [Semiring R] [StrongRankCondition R] [AddCommMonoid H] [Module R H]
    [Module.Free R H] : Module.rank R Hᵐᵒᵖ = Module.rank R H :=
  Module.nonempty_linearEquiv_iff_rank_eq.mp ⟨(opLinearEquiv R).symm⟩

/--
theorem `finrank` / 定理 `finrank`

English:
theorem finrank
  given: [DivisionRing R] [AddCommGroup H] [Module R H]
  proof: by
  let b := Basis.ofVectorSpace R H
  rw [Module.finrank_eq_nat_card_basis b]; rw [Module.finrank_eq_nat_card_basis b.mulOpposite]

中文:
定理 finrank
  条件: [DivisionRing R] [AddCommGroup H] [Module R H]
  证明: by
  let b := Basis.ofVectorSpace R H
  rw [Module.finrank_eq_nat_card_basis b]; rw [Module.finrank_eq_nat_card_basis b.mulOpposite]

Depends on / 依赖: Basis.ofVectorSpace, Module, Module.finrank_eq_nat_card_basis, b.mulOpposite, finrank_eq_nat_card_basis, mulOpposite, ofVectorSpace
-/
theorem finrank [DivisionRing R] [AddCommGroup H] [Module R H] :
    Module.finrank R Hᵐᵒᵖ = Module.finrank R H := by
  let b := Basis.ofVectorSpace R H
  rw [Module.finrank_eq_nat_card_basis b]; rw [Module.finrank_eq_nat_card_basis b.mulOpposite]

end MulOpposite
