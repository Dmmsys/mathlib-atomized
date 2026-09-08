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
algebra homomorphism  `ψ : L → LieDerivation  R K K`, the underlying set of the semidirect sum is
`K × L`, however the bracket is twisted by `ψ`. In this file we show that `SemiDirectSum K L ψ` is
itself a Lie algebra and that it fits into an exact sequence `H → (SemiDirectSum K L ψ) → L`, i.e.
forms an extension of `L`.


## References

* https://en.wikipedia.org/wiki/Lie_algebra_extension#By_semidirect_sum

-/


@[expose] public section

namespace LieAlgebra

/--
The semi-direct sum of two Lie algebras `K` and `L` over `R`, relative to a Lie algebra homomorphism
`ψ: L → LieDerivation R K K`. As a set, it is just `K × L`, however the Lie bracket is twisted by
`ψ`.
-/
/-
**LieAlgebra.SemiDirectSum** 是 Mathlib 中的一个归纳类型，位于命名空间 `LieAlgebra`。
形式化陈述：{R : Type u_1} →   [inst : CommRing R] →     (K : Type u_2) →       [inst_
1 : LieRing K] →         [inst_2 : LieAlgebra R K] →           (L : Type u_3) → 
            [inst_3 : LieRing L] → [inst_4 : LieAlgebra R L] → (L →ₗ⁅R⁆ LieDeriv
ation R K K) → Type (max u_2 u_3)
参数：K : Type u_2；L : Type u_3；L →ₗ⁅R⁆ LieDerivation R K K；max u_2 u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The semi-direct sum of two Lie algebras `K` and `L` over `R`, relative to a Lie 
algebra homomorphism
`ψ: L → LieDerivation R K K`. As a set, it is just `K × L`, however the Lie brac
ket is twisted by
`ψ`.
-/
@[ext] structure SemiDirectSum {R : Type*} [CommRing R] (K : Type*) [LieRing K] [LieAlgebra R K]
    (L : Type*) [LieRing L] [LieAlgebra R L] (_ : L →ₗ⁅R⁆ LieDerivation R K K) where
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
variable (ψ : L →ₗ⁅R⁆ LieDerivation R K K)

variable {ψ} in
/-- As raw types, the semidirect product is just a product. -/
/-
**LieAlgebra.SemiDirectSum.toProd** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.SemiDire
ctSum`。
形式化陈述：toProd : K ⋊⁅ψ⁆ L ≃ K × L where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
As raw types, the semidirect product is just a product.
-/
def toProd : K ⋊⁅ψ⁆ L ≃ K × L where
  toFun x := ⟨x.left, x.right⟩
  invFun x := ⟨x.fst, x.snd⟩
  left_inv _ := rfl
  right_inv _ := rfl
/-
**LieAlgebra.SemiDirectSum.toProd_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.Se
miDirectSum`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {K : Type u_2} [inst_1 : LieRing K] [
inst_2 : LieAlgebra R K] {L : Type u_3}   [inst_3 : LieRing L] [inst_4 : LieAlge
bra R L] (ψ : L →ₗ⁅R⁆ LieDerivation R K K) (x : K ⋊⁅ψ⁆ L),   LieAlgebra.SemiDire
ctSum.toProd x = (x.left, x.right)
参数：ψ : L →ₗ⁅R⁆ LieDerivation R K K；x : K ⋊⁅ψ⁆ L；x.left, x.right。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toProd_apply (x : K ⋊⁅ψ⁆ L) : toProd (x) = ⟨x.left, x.right⟩ := rfl
/-
**LieAlgebra.SemiDirectSum.** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra.SemiDirectSum`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (K ⋊⁅ψ⁆ L) := toProd.addCommGroup
/-
**LieAlgebra.SemiDirectSum.** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra.SemiDirectSum`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module R (K ⋊⁅ψ⁆ L) := toProd.module R

/-- `LieAlgebra.SemiDirectSum.toProd` as a linear equivalence. -/
/-
**LieAlgebra.SemiDirectSum.toProdl** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.SemiDir
ectSum`。
形式化陈述：toProdl : (K ⋊⁅ψ⁆ L) ≃ₗ[R] K × L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LieAlgebra.SemiDirectSum.toProd` as a linear equivalence.
-/
def toProdl : (K ⋊⁅ψ⁆ L) ≃ₗ[R] K × L :=
  { __ := toProd
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
/-
**LieAlgebra.SemiDirectSum.toProdl_coe** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.Sem
iDirectSum`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {K : Type u_2} [inst_1 : LieRing K] [
inst_2 : LieAlgebra R K] {L : Type u_3}   [inst_3 : LieRing L] [inst_4 : LieAlge
bra R L] (ψ : L →ₗ⁅R⁆ LieDerivation R K K) (x : K ⋊⁅ψ⁆ L),   (LieAlgebra.SemiDir
ectSum.toProdl ψ) x = LieAlgebra.SemiDirectSum.toProd x
参数：ψ : L →ₗ⁅R⁆ LieDerivation R K K；x : K ⋊⁅ψ⁆ L；LieAlgebra.SemiDirectSum.toProdl
 ψ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toProdl_coe (x : K ⋊⁅ψ⁆ L) : toProdl ψ x = toProd x := rfl
/-
**LieAlgebra.SemiDirectSum.** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra.SemiDirectSum`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bracket (K ⋊⁅ψ⁆ L) (K ⋊⁅ψ⁆ L) where
  bracket x y := ⟨⁅x.left, y.left⁆ + ψ x.right y.left - ψ y.right x.left, ⁅x.right, y.right⁆⟩
/-
**LieAlgebra.SemiDirectSum.zero_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.Semi
DirectSum`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {K : Type u_2} [inst_1 : LieRing K] [
inst_2 : LieAlgebra R K] {L : Type u_3}   [inst_3 : LieRing L] [inst_4 : LieAlge
bra R L] (ψ : L →ₗ⁅R⁆ LieDerivation R K K), 0 = { left := 0, right := 0 }
参数：ψ : L →ₗ⁅R⁆ LieDerivation R K K。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma zero_eq_mk : (0 : K ⋊⁅ψ⁆ L) = ⟨0, 0⟩ := rfl
/-
**LieAlgebra.SemiDirectSum.add_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.SemiD
irectSum`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {K : Type u_2} [inst_1 : LieRing K] [
inst_2 : LieAlgebra R K] {L : Type u_3}   [inst_3 : LieRing L] [inst_4 : LieAlge
bra R L] (ψ : L →ₗ⁅R⁆ LieDerivation R K K) (x y : K ⋊⁅ψ⁆ L),   x + y = { left :=
 x.left + y.left, right := x.right + y.right }
参数：ψ : L →ₗ⁅R⁆ LieDerivation R K K；x y : K ⋊⁅ψ⁆ L。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma add_eq_mk (x y : K ⋊⁅ψ⁆ L) : x + y = ⟨x.left + y.left, x.right + y.right⟩ := rfl
/-
**LieAlgebra.SemiDirectSum.sub_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.SemiD
irectSum`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {K : Type u_2} [inst_1 : LieRing K] [
inst_2 : LieAlgebra R K] {L : Type u_3}   [inst_3 : LieRing L] [inst_4 : LieAlge
bra R L] (ψ : L →ₗ⁅R⁆ LieDerivation R K K) (x y : K ⋊⁅ψ⁆ L),   x - y = { left :=
 x.left - y.left, right := x.right - y.right }
参数：ψ : L →ₗ⁅R⁆ LieDerivation R K K；x y : K ⋊⁅ψ⁆ L。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma sub_eq_mk (x y : K ⋊⁅ψ⁆ L) : x - y = ⟨x.left - y.left, x.right - y.right⟩ := rfl
/-
**LieAlgebra.SemiDirectSum.neg_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.SemiD
irectSum`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {K : Type u_2} [inst_1 : LieRing K] [
inst_2 : LieAlgebra R K] {L : Type u_3}   [inst_3 : LieRing L] [inst_4 : LieAlge
bra R L] (ψ : L →ₗ⁅R⁆ LieDerivation R K K) (x : K ⋊⁅ψ⁆ L),   -x = { left := -x.l
eft, right := -x.right }
参数：ψ : L →ₗ⁅R⁆ LieDerivation R K K；x : K ⋊⁅ψ⁆ L。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma neg_eq_mk (x : K ⋊⁅ψ⁆ L) : -x = ⟨-x.left, -x.right⟩ := rfl
/-
**LieAlgebra.SemiDirectSum.smul_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.Semi
DirectSum`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {K : Type u_2} [inst_1 : LieRing K] [
inst_2 : LieAlgebra R K] {L : Type u_3}   [inst_3 : LieRing L] [inst_4 : LieAlge
bra R L] (ψ : L →ₗ⁅R⁆ LieDerivation R K K) (t : R) (x : K ⋊⁅ψ⁆ L),   t • x = { l
eft := t • x.left, right := t • x.right }
参数：ψ : L →ₗ⁅R⁆ LieDerivation R K K；t : R；x : K ⋊⁅ψ⁆ L。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma smul_eq_mk (t : R) (x : K ⋊⁅ψ⁆ L) : t • x = ⟨t • x.left, t • x.right⟩ := rfl
/-
**LieAlgebra.SemiDirectSum.lie_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.SemiD
irectSum`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {K : Type u_2} [inst_1 : LieRing K] [
inst_2 : LieAlgebra R K] {L : Type u_3}   [inst_3 : LieRing L] [inst_4 : LieAlge
bra R L] (ψ : L →ₗ⁅R⁆ LieDerivation R K K) (x y : K ⋊⁅ψ⁆ L),   ⁅x, y⁆ = { left :
= ⁅x.left, y.left⁆ + (ψ x.right) y.left - (ψ y.right) x.left, right := ⁅x.right,
 y.right⁆ }
参数：ψ : L →ₗ⁅R⁆ LieDerivation R K K；x y : K ⋊⁅ψ⁆ L；ψ x.right；ψ y.right。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma lie_eq_mk (x y : K ⋊⁅ψ⁆ L) :
    ⁅x, y⁆ = ⟨⁅x.left, y.left⁆ + ψ x.right y.left - ψ y.right x.left, ⁅x.right, y.right⁆⟩ :=
  rfl
/-
**LieAlgebra.SemiDirectSum.** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra.SemiDirectSum`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LieRing (K ⋊⁅ψ⁆ L) where
  add_lie _ _ _ := by simp; abel
  lie_add _ _ _ := by simp; abel
  lie_self _ := by simp
  leibniz_lie _ _ _ := by simp; grind [lie_skew]

set_option backward.isDefEq.respectTransparency false in
/-
**LieAlgebra.SemiDirectSum.** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra.SemiDirectSum`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LieAlgebra R (K ⋊⁅ψ⁆ L) where
  lie_smul _ _ _ := by simp [smul_sub, smul_add]

/-- The canonical inclusion of K into the semi-direct sum K ⋊⁅ψ⁆ G. -/
/-
**LieAlgebra.SemiDirectSum.inl** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.SemiDirectS
um`。
形式化陈述：inl : K ->ₗ⁅R⁆ K ⋊⁅ψ⁆ L where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical inclusion of K into the semi-direct sum K ⋊⁅ψ⁆ G.
-/
def inl : K →ₗ⁅R⁆ K ⋊⁅ψ⁆ L where
  toFun x := ⟨x, 0⟩
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  map_lie' := by simp

/-- The canonical inclusion of L into the semi-direct sum K ⋊⁅ψ⁆ G. -/
/-
**LieAlgebra.SemiDirectSum.inr** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.SemiDirectS
um`。
形式化陈述：inr : L ->ₗ⁅R⁆ K ⋊⁅ψ⁆ L where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical inclusion of L into the semi-direct sum K ⋊⁅ψ⁆ G.
-/
def inr : L →ₗ⁅R⁆ K ⋊⁅ψ⁆ L where
  toFun x := ⟨0, x⟩
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  map_lie' := by simp
/-
**LieAlgebra.SemiDirectSum.inl_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.SemiD
irectSum`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {K : Type u_2} [inst_1 : LieRing K] [
inst_2 : LieAlgebra R K] {L : Type u_3}   [inst_3 : LieRing L] [inst_4 : LieAlge
bra R L] (ψ : L →ₗ⁅R⁆ LieDerivation R K K) (x : K),   (LieAlgebra.SemiDirectSum.
inl ψ) x = { left := x, right := 0 }
参数：ψ : L →ₗ⁅R⁆ LieDerivation R K K；x : K；LieAlgebra.SemiDirectSum.inl ψ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma inl_eq_mk (x : K) : inl ψ x = ⟨x, 0⟩ := rfl
/-
**LieAlgebra.SemiDirectSum.inr_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.SemiD
irectSum`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {K : Type u_2} [inst_1 : LieRing K] [
inst_2 : LieAlgebra R K] {L : Type u_3}   [inst_3 : LieRing L] [inst_4 : LieAlge
bra R L] (ψ : L →ₗ⁅R⁆ LieDerivation R K K) (x : L),   (LieAlgebra.SemiDirectSum.
inr ψ) x = { left := 0, right := x }
参数：ψ : L →ₗ⁅R⁆ LieDerivation R K K；x : L；LieAlgebra.SemiDirectSum.inr ψ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma inr_eq_mk (x : L) : inr ψ x = ⟨0, x⟩ := rfl

@[simp]
/-
**LieAlgebra.SemiDirectSum.inl_injective** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra.S
emiDirectSum`。
形式化陈述：inl_injective : Function.Injective (inl ψ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LieAlgebra.SemiDirectSum.mk.injEq`：∀ {R : Type u_1} [inst : CommRing R] 
{K : Type u_2} [inst_1 : LieRing K] [inst_2 : LieAlgebra R K] {L : Type u_3}   [
inst_3 : LieRing L] [in…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma inl_injective : Function.Injective (inl ψ) := by intro; simp [inl]

/-- The canonical projection of the semi-direct sum K ⋊⁅ψ⁆ L to G. -/
/-
**LieAlgebra.SemiDirectSum.projr** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.SemiDirec
tSum`。
形式化陈述：projr : K ⋊⁅ψ⁆ L ->ₗ⁅R⁆ L where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical projection of the semi-direct sum K ⋊⁅ψ⁆ L to G.
-/
def projr : K ⋊⁅ψ⁆ L →ₗ⁅R⁆ L where
  toFun x := x.right
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  map_lie' := by simp

/-- The canonical projection of the semi-direct sum K ⋊⁅ψ⁆ L to G.
It is not, in general, a Lie algebra homomorphism, just a linear map. -/
/-
**LieAlgebra.SemiDirectSum.projl** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.SemiDirec
tSum`。
形式化陈述：projl : K ⋊⁅ψ⁆ L ->ₗ[R] K where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical projection of the semi-direct sum K ⋊⁅ψ⁆ L to G.
It is not, in general, a Lie algebra homomorphism, just a linear map.
-/
def projl : K ⋊⁅ψ⁆ L →ₗ[R] K where
  toFun x := x.left
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
/-
**LieAlgebra.SemiDirectSum.projr_mk** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.SemiDi
rectSum`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {K : Type u_2} [inst_1 : LieRing K] [
inst_2 : LieAlgebra R K] {L : Type u_3}   [inst_3 : LieRing L] [inst_4 : LieAlge
bra R L] (ψ : L →ₗ⁅R⁆ LieDerivation R K K) (x : K ⋊⁅ψ⁆ L),   (LieAlgebra.SemiDir
ectSum.projr ψ) x = x.right
参数：ψ : L →ₗ⁅R⁆ LieDerivation R K K；x : K ⋊⁅ψ⁆ L；LieAlgebra.SemiDirectSum.projr ψ
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma projr_mk (x : K ⋊⁅ψ⁆ L) : projr ψ x = x.right := rfl
/-
**LieAlgebra.SemiDirectSum.projl_mk** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.SemiDi
rectSum`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {K : Type u_2} [inst_1 : LieRing K] [
inst_2 : LieAlgebra R K] {L : Type u_3}   [inst_3 : LieRing L] [inst_4 : LieAlge
bra R L] (ψ : L →ₗ⁅R⁆ LieDerivation R K K) (x : K ⋊⁅ψ⁆ L),   (LieAlgebra.SemiDir
ectSum.projl ψ) x = x.left
参数：ψ : L →ₗ⁅R⁆ LieDerivation R K K；x : K ⋊⁅ψ⁆ L；LieAlgebra.SemiDirectSum.projl ψ
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma projl_mk (x : K ⋊⁅ψ⁆ L) : projl ψ x = x.left := rfl
/-
**LieAlgebra.SemiDirectSum.projr_inl_apply** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra
.SemiDirectSum`。
形式化陈述：projr_inl_apply {x : K} : projr ψ (inl ψ x) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma projr_inl_apply {x : K} : projr ψ (inl ψ x) = 0 := by simp
/-
**LieAlgebra.SemiDirectSum.projr_inr_apply** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra
.SemiDirectSum`。
形式化陈述：projr_inr_apply {x : L} : projr ψ (inr ψ x) = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma projr_inr_apply {x : L} : projr ψ (inr ψ x) = x := by simp
/-
**LieAlgebra.SemiDirectSum.projl_inr_apply** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra
.SemiDirectSum`。
形式化陈述：projl_inr_apply {x : L} : projl ψ (inr ψ x) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma projl_inr_apply {x : L} : projl ψ (inr ψ x) = 0 := by simp
/-
**LieAlgebra.SemiDirectSum.projl_inl_apply** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra
.SemiDirectSum`。
形式化陈述：projl_inl_apply {x : K} : projl ψ (inl ψ x) = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma projl_inl_apply {x : K} : projl ψ (inl ψ x) = x := by simp

@[simp]
/-
**LieAlgebra.SemiDirectSum.projr_surjective** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebr
a.SemiDirectSum`。
形式化陈述：projr_surjective : Function.Surjective (projr ψ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma projr_surjective : Function.Surjective (projr ψ) :=
  fun x ↦ ⟨inr ψ x, by simp⟩
/-
**LieAlgebra.SemiDirectSum.** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra.SemiDirectSum`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LieAlgebra.IsExtension (inl ψ) (projr ψ) where
  ker_eq_bot := by simp [LieHom.ker_eq_bot]
  range_eq_top := by simp [LieHom.range_eq_top]
  exact := by ext ⟨x, y⟩; aesop

end

variable (R K L) in
/-- The product of two Lie algebras realized through a semidirect sum with trivial `ψ` -/
@[simps!]
/-
**LieAlgebra.SemiDirectSum.prod_iso** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.SemiDi
rectSum`。
形式化陈述：prod_iso : (K ⋊⁅(0 : L ->ₗ⁅R⁆ (LieDerivation R K K))⁆ L) ≃ₗ⁅R⁆ (K × L) whe
re __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of two Lie algebras realized through a semidirect sum with trivial `
ψ`
-/
def prod_iso : (K ⋊⁅(0 : L →ₗ⁅R⁆ (LieDerivation R K K))⁆ L) ≃ₗ⁅R⁆ (K × L) where
  __ := toProdl 0
  map_lie' {_ _} := by simp

end SemiDirectSum
end LieAlgebra
end

