/-
Copyright (c) 2026 Leonid Ryvkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonid Ryvkin
-/
module

public import Mathlib.Algebra.Lie.Derivation.Basic
public import Mathlib.Algebra.Lie.Extension
public import Mathlib.Algebra.Lie.Prod

/-!
# Semi-direct products

This file defines the semi-direct sum of Lie algebras. These are the infinitesimal counterpart of
semidirect products of (Lie) groups. Given two Lie algebras `K` and `L` over `R` as well as a Lie
algebra homomorphism `ψ : L → LieDerivation R K K`, the underlying set of the semidirect sum is
`K × L`, however the bracket is twisted by `ψ`. In this file we show that `SemiDirectSum K L ψ` is
itself a Lie algebra and that it fits into an exact sequence `H → (SemiDirectSum K L ψ) → L`, i.e.
forms an extension of `L`.


## References

* https://en.wikipedia.org/wiki/Lie_algebra_extension#By_semidirect_sum

-/


@[expose] public section

namespace LieAlgebra

/--
Definition of `SemiDirectSum` / `SemiDirectSum` 的定义

English:
structure SemiDirectSum
  parameters: {R : Type*} [CommRing R] (K : Type*) [LieRing K] [LieAlgebra R K]
  axioms and operations (2):
    - left : K
    - right : L

中文:
结构 SemiDirectSum
  参数: {R : 类型} [交换环 R] (K : 类型) [Lie环 K] [Lie代数 R K]
  公理与运算 (2 个):
    - left : K
    - right : L
-/
@[ext] structure SemiDirectSum {R : Type*} [CommRing R] (K : Type*) [LieRing K] [LieAlgebra R K]
    (L : Type*) [LieRing L] [LieAlgebra R L] (_ : L ->ₗ⁅R⁆ LieDerivation R K K) where
  /-- The element of K -/
  left : K
  /-- The element of L -/
  right : L

@[inherit_doc]
notation:35 K " ⋊⁅" ψ:35 "⁆ " L:35 => SemiDirectSum K L ψ


namespace SemiDirectSum

variable {R : Type*} [CommRing R]
variable {K : Type*} [LieRing K] [LieAlgebra R K]
variable {L : Type*} [LieRing L] [LieAlgebra R L]

section
variable (ψ : L ->ₗ⁅R⁆ LieDerivation R K K)

variable {ψ} in
/--
Definition of `toProd` / `toProd` 的定义

English:
definition toProd
  signature: : K ⋊⁅ψ⁆ L ≃ K × L where
  body: ⟨x.left, x.right⟩
  invFun x := ⟨x.fst, x.snd⟩
  left_inv _ := rfl
  right_inv _ := rfl

中文:
定义 toProd
  签名: : K ⋊⁅ψ⁆ L ≃ K × L where
  定义体: ⟨x.left, x.right⟩
  invFun x := ⟨x.fst, x.snd⟩
  left_inv _ := rfl
  right_inv _ := rfl

Depends on / 依赖: x.left, x.right
-/
def toProd : K ⋊⁅ψ⁆ L ≃ K × L where
  toFun x := ⟨x.left, x.right⟩
  invFun x := ⟨x.fst, x.snd⟩
  left_inv _ := rfl
  right_inv _ := rfl

/--
lemma `toProd_apply` / 引理 `toProd_apply`

English:
lemma toProd_apply
  given: (x : K ⋊⁅ψ⁆ L)
  statement: toProd (x) = ⟨x.left, x.right⟩
  proof: rfl

中文:
引理 toProd_apply
  条件: (x : K ⋊⁅ψ⁆ L)
  结论: toProd (x) = ⟨x.left, x.right⟩
  证明: rfl
-/
@[simp] lemma toProd_apply (x : K ⋊⁅ψ⁆ L) : toProd (x) = ⟨x.left, x.right⟩ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (K ⋊⁅ψ⁆ L)
  body: toProd.addCommGroup

中文:
实例 :
  签名: 加法交换群 (K ⋊⁅ψ⁆ L)
  定义体: toProd.addCommGroup

Depends on / 依赖: addCommGroup, toProd, toProd.addCommGroup
-/
instance : AddCommGroup (K ⋊⁅ψ⁆ L) := toProd.addCommGroup

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module R (K ⋊⁅ψ⁆ L)
  body: toProd.module R

中文:
实例 :
  签名: 模 R (K ⋊⁅ψ⁆ L)
  定义体: toProd.module R

Depends on / 依赖: module, toProd, toProd.module
-/
instance : Module R (K ⋊⁅ψ⁆ L) := toProd.module R

/--
Definition of `toProdl` / `toProdl` 的定义

English:
definition toProdl
  signature: : (K ⋊⁅ψ⁆ L) ≃ₗ[R] K × L
  body: { __ := toProd
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

中文:
定义 toProdl
  签名: : (K ⋊⁅ψ⁆ L) ≃ₗ[R] K × L
  定义体: { __ := toProd
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

Depends on / 依赖: map_add, map_smul, toProd
-/
def toProdl : (K ⋊⁅ψ⁆ L) ≃ₗ[R] K × L :=
  { __ := toProd
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

/--
lemma `toProdl_coe` / 引理 `toProdl_coe`

English:
lemma toProdl_coe
  given: (x : K ⋊⁅ψ⁆ L)
  statement: toProdl ψ x = toProd x
  proof: rfl

中文:
引理 toProdl_coe
  条件: (x : K ⋊⁅ψ⁆ L)
  结论: toProdl ψ x = toProd x
  证明: rfl
-/
@[simp] lemma toProdl_coe (x : K ⋊⁅ψ⁆ L) : toProdl ψ x = toProd x := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bracket (K ⋊⁅ψ⁆ L) (K ⋊⁅ψ⁆ L)
  body: ⟨⁅x.left, y.left⁆ + ψ x.right y.left - ψ y.right x.left, ⁅x.right, y.right⁆⟩

中文:
实例 :
  签名: Bracket (K ⋊⁅ψ⁆ L) (K ⋊⁅ψ⁆ L)
  定义体: ⟨⁅x.left, y.left⁆ + ψ x.right y.left - ψ y.right x.left, ⁅x.right, y.right⁆⟩

Depends on / 依赖: x.left, x.right, y.left, y.right
-/
instance : Bracket (K ⋊⁅ψ⁆ L) (K ⋊⁅ψ⁆ L) where
  bracket x y := ⟨⁅x.left, y.left⁆ + ψ x.right y.left - ψ y.right x.left, ⁅x.right, y.right⁆⟩

/--
lemma `zero_eq_mk` / 引理 `zero_eq_mk`

English:
lemma zero_eq_mk
  statement: (0 : K ⋊⁅ψ⁆ L) = ⟨0, 0⟩
  proof: rfl

中文:
引理 zero_eq_mk
  结论: (0 : K ⋊⁅ψ⁆ L) = ⟨0, 0⟩
  证明: rfl
-/
@[simp] lemma zero_eq_mk : (0 : K ⋊⁅ψ⁆ L) = ⟨0, 0⟩ := rfl
/--
lemma `add_eq_mk` / 引理 `add_eq_mk`

English:
lemma add_eq_mk
  given: (x y : K ⋊⁅ψ⁆ L)
  statement: x + y = ⟨x.left + y.left, x.right + y.right⟩
  proof: rfl

中文:
引理 add_eq_mk
  条件: (x y : K ⋊⁅ψ⁆ L)
  结论: x + y = ⟨x.left + y.left, x.right + y.right⟩
  证明: rfl
-/
@[simp] lemma add_eq_mk (x y : K ⋊⁅ψ⁆ L) : x + y = ⟨x.left + y.left, x.right + y.right⟩ := rfl
/--
lemma `sub_eq_mk` / 引理 `sub_eq_mk`

English:
lemma sub_eq_mk
  given: (x y : K ⋊⁅ψ⁆ L)
  statement: x - y = ⟨x.left - y.left, x.right - y.right⟩
  proof: rfl

中文:
引理 sub_eq_mk
  条件: (x y : K ⋊⁅ψ⁆ L)
  结论: x - y = ⟨x.left - y.left, x.right - y.right⟩
  证明: rfl
-/
@[simp] lemma sub_eq_mk (x y : K ⋊⁅ψ⁆ L) : x - y = ⟨x.left - y.left, x.right - y.right⟩ := rfl
/--
lemma `neg_eq_mk` / 引理 `neg_eq_mk`

English:
lemma neg_eq_mk
  given: (x : K ⋊⁅ψ⁆ L)
  statement: -x = ⟨-x.left, -x.right⟩
  proof: rfl

中文:
引理 neg_eq_mk
  条件: (x : K ⋊⁅ψ⁆ L)
  结论: -x = ⟨-x.left, -x.right⟩
  证明: rfl
-/
@[simp] lemma neg_eq_mk (x : K ⋊⁅ψ⁆ L) : -x = ⟨-x.left, -x.right⟩ := rfl
/--
lemma `smul_eq_mk` / 引理 `smul_eq_mk`

English:
lemma smul_eq_mk
  given: (t : R) (x : K ⋊⁅ψ⁆ L)
  statement: t • x = ⟨t • x.left, t • x.right⟩
  proof: rfl

中文:
引理 smul_eq_mk
  条件: (t : R) (x : K ⋊⁅ψ⁆ L)
  结论: t • x = ⟨t • x.left, t • x.right⟩
  证明: rfl
-/
@[simp] lemma smul_eq_mk (t : R) (x : K ⋊⁅ψ⁆ L) : t • x = ⟨t • x.left, t • x.right⟩ := rfl
/--
lemma `lie_eq_mk` / 引理 `lie_eq_mk`

English:
lemma lie_eq_mk
  given: (x y : K ⋊⁅ψ⁆ L)
  proof: rfl

中文:
引理 lie_eq_mk
  条件: (x y : K ⋊⁅ψ⁆ L)
  证明: rfl
-/
@[simp] lemma lie_eq_mk (x y : K ⋊⁅ψ⁆ L) :
    ⁅x, y⁆ = ⟨⁅x.left, y.left⁆ + ψ x.right y.left - ψ y.right x.left, ⁅x.right, y.right⁆⟩ :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LieRing (K ⋊⁅ψ⁆ L)
  body: by simp; abel
  lie_add _ _ _ := by simp; abel
  lie_self _ := by simp
  leibniz_lie _ _ _ := by simp; grind [lie_skew]

中文:
实例 :
  签名: Lie环 (K ⋊⁅ψ⁆ L)
  定义体: by simp; abel
  lie_add _ _ _ := by simp; abel
  lie_self _ := by simp
  leibniz_lie _ _ _ := by simp; grind [lie_skew]

Depends on / 依赖: leibniz_lie, lie_add, lie_self, lie_skew
-/
instance : LieRing (K ⋊⁅ψ⁆ L) where
  add_lie _ _ _ := by simp; abel
  lie_add _ _ _ := by simp; abel
  lie_self _ := by simp
  leibniz_lie _ _ _ := by simp; grind [lie_skew]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LieAlgebra R (K ⋊⁅ψ⁆ L)
  body: by simp [smul_sub, smul_add]

中文:
实例 :
  签名: Lie代数 R (K ⋊⁅ψ⁆ L)
  定义体: by simp [smul_sub, smul_add]

Depends on / 依赖: smul_add, smul_sub
-/
instance : LieAlgebra R (K ⋊⁅ψ⁆ L) where
  lie_smul _ _ _ := by simp [smul_sub, smul_add]

/--
Definition of `inl` / `inl` 的定义

English:
definition inl
  signature: : K ->ₗ⁅R⁆ K ⋊⁅ψ⁆ L where
  body: ⟨x, 0⟩
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  map_lie' := by simp

中文:
定义 inl
  签名: : K ->ₗ⁅R⁆ K ⋊⁅ψ⁆ L where
  定义体: ⟨x, 0⟩
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  map_lie' := by simp
-/
def inl : K ->ₗ⁅R⁆ K ⋊⁅ψ⁆ L where
  toFun x := ⟨x, 0⟩
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  map_lie' := by simp

/--
Definition of `inr` / `inr` 的定义

English:
definition inr
  signature: : L ->ₗ⁅R⁆ K ⋊⁅ψ⁆ L where
  body: ⟨0, x⟩
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  map_lie' := by simp

中文:
定义 inr
  签名: : L ->ₗ⁅R⁆ K ⋊⁅ψ⁆ L where
  定义体: ⟨0, x⟩
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  map_lie' := by simp
-/
def inr : L ->ₗ⁅R⁆ K ⋊⁅ψ⁆ L where
  toFun x := ⟨0, x⟩
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  map_lie' := by simp

/--
lemma `inl_eq_mk` / 引理 `inl_eq_mk`

English:
lemma inl_eq_mk
  given: (x : K)
  statement: inl ψ x = ⟨x, 0⟩
  proof: rfl

中文:
引理 inl_eq_mk
  条件: (x : K)
  结论: inl ψ x = ⟨x, 0⟩
  证明: rfl
-/
@[simp] lemma inl_eq_mk (x : K) : inl ψ x = ⟨x, 0⟩ := rfl
/--
lemma `inr_eq_mk` / 引理 `inr_eq_mk`

English:
lemma inr_eq_mk
  given: (x : L)
  statement: inr ψ x = ⟨0, x⟩
  proof: rfl

@[simp]

中文:
引理 inr_eq_mk
  条件: (x : L)
  结论: inr ψ x = ⟨0, x⟩
  证明: rfl

@[simp]
-/
@[simp] lemma inr_eq_mk (x : L) : inr ψ x = ⟨0, x⟩ := rfl

@[simp]
/--
lemma `inl_injective` / 引理 `inl_injective`

English:
lemma inl_injective
  statement: Function.Injective (inl ψ)
  proof: by intro; simp [inl]

中文:
引理 inl_injective
  结论: 函数.单射 (inl ψ)
  证明: by intro; simp [inl]
-/
lemma inl_injective : Function.Injective (inl ψ) := by intro; simp [inl]

/--
Definition of `projr` / `projr` 的定义

English:
definition projr
  signature: : K ⋊⁅ψ⁆ L ->ₗ⁅R⁆ L where
  body: x.right
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  map_lie' := by simp

中文:
定义 projr
  签名: : K ⋊⁅ψ⁆ L ->ₗ⁅R⁆ L where
  定义体: x.right
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  map_lie' := by simp

Depends on / 依赖: x.right
-/
def projr : K ⋊⁅ψ⁆ L ->ₗ⁅R⁆ L where
  toFun x := x.right
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  map_lie' := by simp

/--
Definition of `projl` / `projl` 的定义

English:
definition projl
  signature: : K ⋊⁅ψ⁆ L ->ₗ[R] K where
  body: x.left
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

中文:
定义 projl
  签名: : K ⋊⁅ψ⁆ L ->ₗ[R] K where
  定义体: x.left
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

Depends on / 依赖: x.left
-/
def projl : K ⋊⁅ψ⁆ L ->ₗ[R] K where
  toFun x := x.left
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

/--
lemma `projr_mk` / 引理 `projr_mk`

English:
lemma projr_mk
  given: (x : K ⋊⁅ψ⁆ L)
  statement: projr ψ x = x.right
  proof: rfl

中文:
引理 projr_mk
  条件: (x : K ⋊⁅ψ⁆ L)
  结论: projr ψ x = x.right
  证明: rfl
-/
@[simp] lemma projr_mk (x : K ⋊⁅ψ⁆ L) : projr ψ x = x.right := rfl
/--
lemma `projl_mk` / 引理 `projl_mk`

English:
lemma projl_mk
  given: (x : K ⋊⁅ψ⁆ L)
  statement: projl ψ x = x.left
  proof: rfl

中文:
引理 projl_mk
  条件: (x : K ⋊⁅ψ⁆ L)
  结论: projl ψ x = x.left
  证明: rfl
-/
@[simp] lemma projl_mk (x : K ⋊⁅ψ⁆ L) : projl ψ x = x.left := rfl

/--
lemma `projr_inl_apply` / 引理 `projr_inl_apply`

English:
lemma projr_inl_apply
  given: {x : K}
  statement: projr ψ (inl ψ x) = 0
  proof: by simp

中文:
引理 projr_inl_apply
  条件: {x : K}
  结论: projr ψ (inl ψ x) = 0
  证明: by simp
-/
lemma projr_inl_apply {x : K} : projr ψ (inl ψ x) = 0 := by simp
/--
lemma `projr_inr_apply` / 引理 `projr_inr_apply`

English:
lemma projr_inr_apply
  given: {x : L}
  statement: projr ψ (inr ψ x) = x
  proof: by simp

中文:
引理 projr_inr_apply
  条件: {x : L}
  结论: projr ψ (inr ψ x) = x
  证明: by simp
-/
lemma projr_inr_apply {x : L} : projr ψ (inr ψ x) = x := by simp
/--
lemma `projl_inr_apply` / 引理 `projl_inr_apply`

English:
lemma projl_inr_apply
  given: {x : L}
  statement: projl ψ (inr ψ x) = 0
  proof: by simp

中文:
引理 projl_inr_apply
  条件: {x : L}
  结论: projl ψ (inr ψ x) = 0
  证明: by simp
-/
lemma projl_inr_apply {x : L} : projl ψ (inr ψ x) = 0 := by simp
/--
lemma `projl_inl_apply` / 引理 `projl_inl_apply`

English:
lemma projl_inl_apply
  given: {x : K}
  statement: projl ψ (inl ψ x) = x
  proof: by simp

@[simp]

中文:
引理 projl_inl_apply
  条件: {x : K}
  结论: projl ψ (inl ψ x) = x
  证明: by simp

@[simp]
-/
lemma projl_inl_apply {x : K} : projl ψ (inl ψ x) = x := by simp

@[simp]
/--
lemma `projr_surjective` / 引理 `projr_surjective`

English:
lemma projr_surjective
  statement: Function.Surjective (projr ψ)
  proof: fun x => ⟨inr ψ x, by simp⟩

中文:
引理 projr_surjective
  结论: 函数.满射 (projr ψ)
  证明: fun x => ⟨inr ψ x, by simp⟩
-/
lemma projr_surjective : Function.Surjective (projr ψ) :=
  fun x => ⟨inr ψ x, by simp⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LieAlgebra.IsExtension (inl ψ) (projr ψ)
  body: by simp [LieHom.ker_eq_bot]
  range_eq_top := by simp [LieHom.range_eq_top]
  exact := by ext ⟨x, y⟩; aesop

中文:
实例 :
  签名: Lie代数.是扩张 (inl ψ) (projr ψ)
  定义体: by simp [LieHom.ker_eq_bot]
  range_eq_top := by simp [LieHom.range_eq_top]
  exact := by ext ⟨x, y⟩; aesop

Depends on / 依赖: LieHom, LieHom.ker_eq_bot, LieHom.range_eq_top, ker_eq_bot, range_eq_top
-/
instance : LieAlgebra.IsExtension (inl ψ) (projr ψ) where
  ker_eq_bot := by simp [LieHom.ker_eq_bot]
  range_eq_top := by simp [LieHom.range_eq_top]
  exact := by ext ⟨x, y⟩; aesop

end

variable (R K L) in
/-- The product of two Lie algebras realized through a semidirect sum with trivial `ψ` -/
@[simps!]
/--
Definition of `prod_iso` / `prod_iso` 的定义

English:
definition prod_iso
  signature: : (K ⋊⁅(0 : L ->ₗ⁅R⁆ (LieDerivation R K K))⁆ L) ≃ₗ⁅R⁆ (K × L) where
  body: toProdl 0
  map_lie' {_ _} := by simp

中文:
定义 prod_iso
  签名: : (K ⋊⁅(0 : L ->ₗ⁅R⁆ (LieDerivation R K K))⁆ L) ≃ₗ⁅R⁆ (K × L) where
  定义体: toProdl 0
  map_lie' {_ _} := by simp

Depends on / 依赖: toProdl
-/
def prod_iso : (K ⋊⁅(0 : L ->ₗ⁅R⁆ (LieDerivation R K K))⁆ L) ≃ₗ⁅R⁆ (K × L) where
  __ := toProdl 0
  map_lie' {_ _} := by simp

end SemiDirectSum
end LieAlgebra
end
