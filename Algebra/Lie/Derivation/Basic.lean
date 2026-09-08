/-
Copyright (c) 2024 Frédéric Marbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Marbach
-/
module

public import Mathlib.Algebra.Lie.NonUnitalNonAssocAlgebra
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.RingTheory.Nilpotent.Exp
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Lie derivations

This file defines *Lie derivations* and establishes some basic properties.

## Main definitions

- `LieDerivation`: A Lie derivation `D` from the Lie `R`-algebra `L` to the `L`-module `M` is an
  `R`-linear map that satisfies the Leibniz rule `D [a, b] = [a, D b] - [b, D a]`.
- `LieDerivation.inner`: The natural map from a Lie module to the derivations taking values in it.

## Main statements

- `LieDerivation.eqOn_lieSpan`: two Lie derivations equal on a set are equal on its Lie span.
- `LieDerivation.instLieAlgebra`: the set of Lie derivations from a Lie algebra to itself is a Lie
  algebra.

## Implementation notes

- Mathematically, a Lie derivation is just a derivation on a Lie algebra. However, the current
  implementation of `RingTheory.Derivation` requires a commutative associative algebra, so is
  incompatible with the setting of Lie algebras. Initially, this file is a copy-pasted adaptation of
  the `RingTheory.Derivation.Basic.lean` file.
- Since we don't have right actions of Lie algebras, the second term in the Leibniz rule is written
  as `- [b, D a]`. Within Lie algebras, skew symmetry restores the expected definition `[D a, b]`.
-/

@[expose] public section

/-- A Lie derivation `D` from the Lie `R`-algebra `L` to the `L`-module `M` is an `R`-linear map
that satisfies the Leibniz rule `D [a, b] = [a, D b] - [b, D a]`. -/
/-
**LieDerivation** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) →   (L : Type u_2) →     (M : Type u_3) →       [inst : Com
mRing R] →         [inst_1 : LieRing L] →           [inst_2 : LieAlgebra R L] → 
            [inst_3 : AddCommGroup M] →               [inst_4 : _root_.Module R 
M] → [inst_5 : LieRingModule L M] → [LieModule R L M] → Type (max u_2 u_3)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Lie derivation `D` from the Lie `R`-algebra `L` to the `L`-module `M` is an `R
`-linear map
that satisfies the Leibniz rule `D [a, b] = [a, D b] - [b, D a]`.
-/
structure LieDerivation (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
    extends L →ₗ[R] M where
  protected leibniz' (a b : L) : toLinearMap ⁅a, b⁆ = ⁅a, toLinearMap b⁆ - ⁅b, toLinearMap a⁆

/-- The `LinearMap` underlying a `LieDerivation`. -/
add_decl_doc LieDerivation.toLinearMap

namespace LieDerivation

section

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable (D : LieDerivation R L M) {D1 D2 : LieDerivation R L M} (a b : L)

/-
**LieDerivation.** 是 Mathlib 中的一个实例，位于命名空间 `LieDerivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (LieDerivation R L M) L M where
  coe D := D.toFun
  coe_injective D1 D2 h := by cases D1; cases D2; congr; exact DFunLike.coe_injective h
/-
**LieDerivation.instLinearMapClass** 是 Mathlib 中的一个实例，位于命名空间 `LieDerivation`。
形式化陈述：instLinearMapClass : LinearMapClass (LieDerivation R L M) R L M where map_
add D
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddHom.map_add'`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [inst_
1 : Add N] (self : M →ₙ+ N) (x y : M),   self.toFun (x + y) = self.toFun x + sel
f.toF…
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
-/
instance instLinearMapClass : LinearMapClass (LieDerivation R L M) R L M where
  map_add D := D.toLinearMap.map_add'
  map_smulₛₗ D := D.toLinearMap.map_smul
/-
**LieDerivation.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `LieDerivation`。
形式化陈述：toFun_eq_coe : D.toFun = ⇑D
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe : D.toFun = ⇑D := rfl

/-- See Note [custom simps projection] -/
/-
**LieDerivation.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `LieDerivation.Simps`。
形式化陈述：{R : Type u_1} →   {L : Type u_2} →     {M : Type u_3} →       [inst : Com
mRing R] →         [inst_1 : LieRing L] →           [inst_2 : LieAlgebra R L] → 
            [inst_3 : AddCommGroup M] →               [inst_4 : _root_.Module R 
M] →                 [inst_5 : LieRingModule L M] → [inst_6 : LieModule R L M] →
 LieDerivation R L M → L → M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.apply (D : LieDerivation R L M) : L → M := D

initialize_simps_projections LieDerivation (toFun → apply)

attribute [coe] toLinearMap
/-
**LieDerivation.instCoeToLinearMap** 是 Mathlib 中的一个实例，位于命名空间 `LieDerivation`。
形式化陈述：instCoeToLinearMap : Coe (LieDerivation R L M) (L ->ₗ[R] M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCoeToLinearMap : Coe (LieDerivation R L M) (L →ₗ[R] M) :=
  ⟨fun D => D.toLinearMap⟩

@[simp]
/-
**LieDerivation.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `LieDerivation`。
形式化陈述：mk_coe (f : L ->ₗ[R] M) (h₁) : ((⟨f, h₁⟩ : LieDerivation R L M) : L -> M) 
= f
参数：f : L ->ₗ[R] M；h₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_coe (f : L →ₗ[R] M) (h₁) : ((⟨f, h₁⟩ : LieDerivation R L M) : L → M) = f :=
  rfl

@[simp, norm_cast]
/-
**LieDerivation.coeFn_coe** 是 Mathlib 中的一个定理，位于命名空间 `LieDerivation`。
形式化陈述：coeFn_coe (f : LieDerivation R L M) : ⇑(f : L ->ₗ[R] M) = f
参数：f : LieDerivation R L M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeFn_coe (f : LieDerivation R L M) : ⇑(f : L →ₗ[R] M) = f :=
  rfl
/-
**LieDerivation.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `LieDerivation`。
形式化陈述：coe_injective : @Function.Injective (LieDerivation R L M) (L -> M) DFunLik
e.coe
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem coe_injective : @Function.Injective (LieDerivation R L M) (L → M) DFunLike.coe :=
  DFunLike.coe_injective

@[ext]
/-
**LieDerivation.ext** 是 Mathlib 中的一个定理，位于命名空间 `LieDerivation`。
形式化陈述：ext (H : forall a, D1 a = D2 a) : D1 = D2
参数：H : forall a, D1 a = D2 a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext (H : ∀ a, D1 a = D2 a) : D1 = D2 :=
  DFunLike.ext _ _ H
/-
**LieDerivation.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `LieDerivation`。
形式化陈述：congr_fun (h : D1 = D2) (a : L) : D1 a = D2 a
参数：h : D1 = D2；a : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem congr_fun (h : D1 = D2) (a : L) : D1 a = D2 a :=
  DFunLike.congr_fun h a

@[simp]
/-
**LieDerivation.apply_lie_eq_sub** 是 Mathlib 中的一个引理，位于命名空间 `LieDerivation`。
形式化陈述：apply_lie_eq_sub (D : LieDerivation R L M) (a b : L) : D ⁅a, b⁆ = ⁅a, D b⁆
 - ⁅b, D a⁆
参数：D : LieDerivation R L M；a b : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieDerivation.leibniz'`：∀ {R : Type u_1} {L : Type u_2} {M : Type u_3} [
inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : Ad
dCommGroup M…
-/
lemma apply_lie_eq_sub (D : LieDerivation R L M) (a b : L) :
    D ⁅a, b⁆ = ⁅a, D b⁆ - ⁅b, D a⁆ :=
  D.leibniz' a b

/-- For a Lie derivation from a Lie algebra to itself, the usual Leibniz rule holds. -/
/-
**LieDerivation.apply_lie_eq_add** 是 Mathlib 中的一个引理，位于命名空间 `LieDerivation`。
形式化陈述：apply_lie_eq_add (D : LieDerivation R L L) (a b : L) : D ⁅a, b⁆ = ⁅a, D b⁆
 + ⁅D a, b⁆
参数：D : LieDerivation R L L；a b : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieDerivation.apply_lie_eq_sub`：apply_lie_eq_sub (D : LieDerivation R L 
M) (a b : L) : D ⁅a, b⁆ = ⁅a, D b⁆ - ⁅b, D a⁆
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `lie_skew`：lie_skew : -⁅y, x⁆ = ⁅x, y⁆

--- 原说明 ---
For a Lie derivation from a Lie algebra to itself, the usual Leibniz rule holds.
-/
lemma apply_lie_eq_add (D : LieDerivation R L L) (a b : L) :
    D ⁅a, b⁆ = ⁅a, D b⁆ + ⁅D a, b⁆ := by
  rw [LieDerivation.apply_lie_eq_sub, sub_eq_add_neg, lie_skew]

set_option backward.isDefEq.respectTransparency false in
/-- Two Lie derivations equal on a set are equal on its Lie span. -/
/-
**LieDerivation.eqOn_lieSpan** 是 Mathlib 中的一个定理，位于命名空间 `LieDerivation`。
形式化陈述：eqOn_lieSpan {s : Set L} (h : Set.EqOn D1 D2 s) : Set.EqOn D1 D2 (LieSubal
gebra.lieSpan R L s)
参数：h : Set.EqOn D1 D2 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.lieSpan_induction`：lieSpan_induction {p : (x : L) -> x in 
lieSpan R L s -> Prop} (mem : forall (x) (h : x in s), p x (subset_lieSpan h)) (
zero : p 0 (LieSubalg…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用引理 `LieDerivation.apply_lie_eq_sub`：apply_lie_eq_sub (D : LieDerivation R L 
M) (a b : L) : D ⁅a, b⁆ = ⁅a, D b⁆ - ⁅b, D a⁆

--- 原说明 ---
Two Lie derivations equal on a set are equal on its Lie span.
-/
theorem eqOn_lieSpan {s : Set L} (h : Set.EqOn D1 D2 s) :
    Set.EqOn D1 D2 (LieSubalgebra.lieSpan R L s) := by
  intro _ hx
  induction hx using LieSubalgebra.lieSpan_induction with
  | mem x hx => exact h hx
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul t x _ hx => simp [hx]
  | lie x y _ _ hx hy => simp [hx, hy]

/-- If the Lie span of a set is the whole Lie algebra, then two Lie derivations equal on this set
are equal on the whole Lie algebra. -/
/-
**LieDerivation.ext_of_lieSpan_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `LieDerivation`。
形式化陈述：ext_of_lieSpan_eq_top (s : Set L) (hs : LieSubalgebra.lieSpan R L s = ⊤) (
h : Set.EqOn D1 D2 s) : D1 = D2
参数：s : Set L；hs : LieSubalgebra.lieSpan R L s = ⊤；h : Set.EqOn D1 D2 s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieDerivation.ext`：ext (H : forall a, D1 a = D2 a) : D1 = D2
· 使用定理 `LieDerivation.eqOn_lieSpan`：eqOn_lieSpan {s : Set L} (h : Set.EqOn D1 D2
 s) : Set.EqOn D1 D2 (LieSubalgebra.lieSpan R L s)
· 使用定理 `trivial`：True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the Lie span of a set is the whole Lie algebra, then two Lie derivations equa
l on this set
are equal on the whole Lie algebra.
-/
theorem ext_of_lieSpan_eq_top (s : Set L) (hs : LieSubalgebra.lieSpan R L s = ⊤)
    (h : Set.EqOn D1 D2 s) : D1 = D2 :=
  ext fun _ => eqOn_lieSpan h <| hs.symm ▸ trivial

section

open Finset Nat

/-- The general Leibniz rule for Lie derivatives. -/
/-
**LieDerivation.iterate_apply_lie** 是 Mathlib 中的一个定理，位于命名空间 `LieDerivation`。
形式化陈述：iterate_apply_lie (D : LieDerivation R L L) (n : Nat) (a b : L) : D^[n] ⁅a
, b⁆ = ∑ ij in antidiagonal n, choose n ij.1 • ⁅D^[ij.1] a, D^[ij.2] b⁆
参数：D : LieDerivation R L L；n : Nat；a b : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.HasAntidiagonal.antidiagonal_zero`：∀ {A : Type u_1} [inst : AddCo
mmMonoid A] [inst_1 : PartialOrder A] [CanonicallyOrderedAdd A]   [inst_3 : Fins
et.HasAntidiagonal A], Finset.…
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.choose_self`：choose_self (n : Nat) : choose n n = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_antidiagonal_choose_succ_nsmul`：∀ {M : Type u_2} [inst : AddC
ommMonoid M] (f : ℕ → ℕ → M) (n : ℕ),   ∑ ij ∈ Finset.HasAntidiagonal.antidiagon
al (n + 1), (n + 1).choose ij.1…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `map_nsmul`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLik
e F G H] [inst_1 : AddMonoid G] [inst_2 : AddMonoid H]   [AddMonoidHomClass F G…
· 使用引理 `LieDerivation.apply_lie_eq_add`：apply_lie_eq_add (D : LieDerivation R L 
L) (a b : L) : D ⁅a, b⁆ = ⁅a, D b⁆ + ⁅D a, b⁆
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Nat.choose_symm_of_eq_add`：choose_symm_of_eq_add {n a b : Nat} (h : n = 
a + b) : Nat.choose n a = Nat.choose n b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.HasAntidiagonal.mem_antidiagonal`：∀ {A : Type u_1} {inst : AddMon
oid A} [self : Finset.HasAntidiagonal A] {n : A} {a : A × A},   a ∈ Finset.HasAn
tidiagonal.antidiagonal n ↔ a…

--- 原说明 ---
The general Leibniz rule for Lie derivatives.
-/
theorem iterate_apply_lie (D : LieDerivation R L L) (n : ℕ) (a b : L) :
    D^[n] ⁅a, b⁆ = ∑ ij ∈ antidiagonal n, choose n ij.1 • ⁅D^[ij.1] a, D^[ij.2] b⁆ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_antidiagonal_choose_succ_nsmul (M := L) (fun i j => ⁅D^[i] a, D^[j] b⁆) n]
    simp only [Function.iterate_succ_apply', ih, map_sum, map_nsmul, apply_lie_eq_add, smul_add,
      sum_add_distrib, add_right_inj]
    refine sum_congr rfl fun ⟨i, j⟩ hij ↦ ?_
    rw [n.choose_symm_of_eq_add (mem_antidiagonal.1 hij).symm]

/-- Alternate version of the general Leibniz rule for Lie derivatives. -/
/-
**LieDerivation.iterate_apply_lie'** 是 Mathlib 中的一个定理，位于命名空间 `LieDerivation`。
形式化陈述：iterate_apply_lie' (D : LieDerivation R L L) (n : Nat) (a b : L) : D^[n] ⁅
a, b⁆ = ∑ i in range (n + 1), n.choose i • ⁅D^[i] a, D^[n - i] b⁆
参数：D : LieDerivation R L L；n : Nat；a b : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieDerivation.iterate_apply_lie`：iterate_apply_lie (D : LieDerivation R 
L L) (n : Nat) (a b : L) : D^[n] ⁅a, b⁆ = ∑ ij in antidiagonal n, choose n ij.1 
• ⁅D^[ij.1] a, D^[ij.…
· 使用定理 `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`：∀ {M : Type u_3} [inst : 
AddCommMonoid M] (f : ℕ → ℕ → M) (n : ℕ),   ∑ ij ∈ Finset.HasAntidiagonal.antidi
agonal n, f ij.1 ij.2 = ∑ k ∈ Finse…

--- 原说明 ---
Alternate version of the general Leibniz rule for Lie derivatives.
-/
theorem iterate_apply_lie' (D : LieDerivation R L L) (n : ℕ) (a b : L) :
    D^[n] ⁅a, b⁆ = ∑ i ∈ range (n + 1), n.choose i • ⁅D^[i] a, D^[n - i] b⁆ := by
  rw [iterate_apply_lie D n a b]
  exact sum_antidiagonal_eq_sum_range_succ (fun i j ↦ n.choose i • ⁅D^[i] a, D^[j] b⁆) n

end

/-
**LieDerivation.instZero** 是 Mathlib 中的一个实例，位于命名空间 `LieDerivation`。
形式化陈述：instZero : Zero (LieDerivation R L M) where zero
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instZero : Zero (LieDerivation R L M) where
  zero :=
    { toLinearMap := 0
      leibniz' := fun a b => by simp only [LinearMap.zero_apply, lie_zero, sub_self] }

@[simp]
/-
**LieDerivation.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `LieDerivation`。
形式化陈述：coe_zero : ⇑(0 : LieDerivation R L M) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero : ⇑(0 : LieDerivation R L M) = 0 :=
  rfl

@[simp]
/-
**LieDerivation.coe_zero_linearMap** 是 Mathlib 中的一个定理，位于命名空间 `LieDerivation`。
形式化陈述：coe_zero_linearMap : ↑(0 : LieDerivation R L M) = (0 : L ->ₗ[R] M)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero_linearMap : ↑(0 : LieDerivation R L M) = (0 : L →ₗ[R] M) :=
  rfl
/-
**LieDerivation.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieDerivation`。
形式化陈述：zero_apply (a : L) : (0 : LieDerivation R L M) a = 0
参数：a : L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_apply (a : L) : (0 : LieDerivation R L M) a = 0 :=
  rfl
/-
**LieDerivation.** 是 Mathlib 中的一个实例，位于命名空间 `LieDerivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (LieDerivation R L M) :=
  ⟨0⟩
/-
**LieDerivation.instAdd** 是 Mathlib 中的一个实例，位于命名空间 `LieDerivation`。
形式化陈述：instAdd : Add (LieDerivation R L M) where add D1 D2
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAdd : Add (LieDerivation R L M) where
  add D1 D2 :=
    { toLinearMap := D1 + D2
      leibniz' := fun a b ↦ by
        simp only [LinearMap.add_apply, coeFn_coe, apply_lie_eq_sub, lie_add, add_sub_add_comm] }

@[simp]
/-
**LieDerivation.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `LieDerivation`。
形式化陈述：coe_add (D1 D2 : LieDerivation R L M) : ⇑(D1 + D2) = D1 + D2
参数：D1 D2 : LieDerivation R L M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_add (D1 D2 : LieDerivation R L M) : ⇑(D1 + D2) = D1 + D2 :=
  rfl

@[simp]
/-
**LieDerivation.coe_add_linearMap** 是 Mathlib 中的一个定理，位于命名空间 `LieDerivation`。
形式化陈述：coe_add_linearMap (D1 D2 : LieDerivation R L M) : ↑(D1 + D2) = (D1 + D2 : 
L ->ₗ[R] M)
参数：D1 D2 : LieDerivation R L M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_add_linearMap (D1 D2 : LieDerivation R L M) : ↑(D1 + D2) = (D1 + D2 : L →ₗ[R] M) :=
  rfl
/-
**LieDerivation.add_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieDerivation`。
形式化陈述：add_apply : (D1 + D2) a = D1 a + D2 a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_apply : (D1 + D2) a = D1 a + D2 a :=
  rfl
/-
**LieDerivation.map_neg** 是 Mathlib 中的一个定理，位于命名空间 `LieDerivation`。
形式化陈述：∀ {R : Type u_1} {L : Type u_2} {M : Type u_3} [inst : CommRing R] [inst_1
 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   (D : 
LieDerivation R L M) (a : L), D (-a) = -D a
参数：D : LieDerivation R L M；a : L；-a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
protected theorem map_neg : D (-a) = -D a :=
  map_neg D a
/-
**LieDerivation.map_sub** 是 Mathlib 中的一个定理，位于命名空间 `LieDerivation`。
形式化陈述：∀ {R : Type u_1} {L : Type u_2} {M : Type u_3} [inst : CommRing R] [inst_1
 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   (D : 
LieDerivation R L M) (a b : L), D (a - b) = D a - D b
参数：D : LieDerivation R L M；a b : L；a - b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
protected theorem map_sub : D (a - b) = D a - D b :=
  map_sub D a b
/-
**LieDerivation.instNeg** 是 Mathlib 中的一个实例，位于命名空间 `LieDerivation`。
形式化陈述：instNeg : Neg (LieDerivation R L M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNeg : Neg (LieDerivation R L M) :=
  ⟨fun D =>
    mk (-D) fun a b => by
      simp only [LinearMap.neg_apply, coeFn_coe, apply_lie_eq_sub,
        neg_sub, lie_neg, sub_neg_eq_add, add_comm, ← sub_eq_add_neg] ⟩

@[simp]
/-
**LieDerivation.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `LieDerivation`。
形式化陈述：coe_neg (D : LieDerivation R L M) : ⇑(-D) = -D
参数：D : LieDerivation R L M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_neg (D : LieDerivation R L M) : ⇑(-D) = -D :=
  rfl

@[simp]
/-
**LieDerivation.coe_neg_linearMap** 是 Mathlib 中的一个定理，位于命名空间 `LieDerivation`。
形式化陈述：coe_neg_linearMap (D : LieDerivation R L M) : ↑(-D) = (-D : L ->ₗ[R] M)
参数：D : LieDerivation R L M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_neg_linearMap (D : LieDerivation R L M) : ↑(-D) = (-D : L →ₗ[R] M) :=
  rfl
/-
**LieDerivation.neg_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieDerivation`。
形式化陈述：neg_apply : (-D) a = -D a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_apply : (-D) a = -D a :=
  rfl
/-
**LieDerivation.instSub** 是 Mathlib 中的一个实例，位于命名空间 `LieDerivation`。
形式化陈述：instSub : Sub (LieDerivation R L M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSub : Sub (LieDerivation R L M) :=
  ⟨fun D1 D2 =>
    mk (D1 - D2 : L →ₗ[R] M) fun a b => by
      simp only [LinearMap.sub_apply, coeFn_coe, apply_lie_eq_sub, lie_sub, sub_sub_sub_comm]⟩

@[simp]
/-
**LieDerivation.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `LieDerivation`。
形式化陈述：coe_sub (D1 D2 : LieDerivation R L M) : ⇑(D1 - D2) = D1 - D2
参数：D1 D2 : LieDerivation R L M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sub (D1 D2 : LieDerivation R L M) : ⇑(D1 - D2) = D1 - D2 :=
  rfl

@[simp]
/-
**LieDerivation.coe_sub_linearMap** 是 Mathlib 中的一个定理，位于命名空间 `LieDerivation`。
形式化陈述：coe_sub_linearMap (D1 D2 : LieDerivation R L M) : ↑(D1 - D2) = (D1 - D2 : 
L ->ₗ[R] M)
参数：D1 D2 : LieDerivation R L M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sub_linearMap (D1 D2 : LieDerivation R L M) : ↑(D1 - D2) = (D1 - D2 : L →ₗ[R] M) :=
  rfl
/-
**LieDerivation.sub_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieDerivation`。
形式化陈述：sub_apply {D1 D2 : LieDerivation R L M} : (D1 - D2) a = D1 a - D2 a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_apply {D1 D2 : LieDerivation R L M} : (D1 - D2) a = D1 a - D2 a :=
  rfl

section Scalar

/-- A typeclass mixin saying that scalar multiplication and Lie bracket are left commutative. -/
/-
**LieDerivation.SMulBracketCommClass** 是 Mathlib 中的一个归纳类型，位于命名空间 `LieDerivation`
。
形式化陈述：(S : Type u_4) →   (L : Type u_5) →     (α : Type u_6) → [SMul S α] → [ins
t : LieRing L] → [inst_1 : AddCommGroup α] → [LieRingModule L α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass mixin saying that scalar multiplication and Lie bracket are left com
mutative.
-/
class SMulBracketCommClass (S L α : Type*) [SMul S α] [LieRing L] [AddCommGroup α]
    [LieRingModule L α] : Prop where
  /-- `•` and `⁅⬝, ⬝⁆`  are left commutative -/
  smul_bracket_comm : ∀ (s : S) (l : L) (a : α), s • ⁅l, a⁆ = ⁅l, s • a⁆

variable {S T : Type*}
variable [Monoid S] [DistribMulAction S M] [SMulCommClass R S M] [SMulBracketCommClass S L M]
variable [Monoid T] [DistribMulAction T M] [SMulCommClass R T M] [SMulBracketCommClass T L M]
/-
**LieDerivation.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `LieDerivation`。
形式化陈述：instSMul : SMul S (LieDerivation R L M) where smul r D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMul : SMul S (LieDerivation R L M) where
  smul r D :=
    { toLinearMap := r • D
      leibniz' := fun a b => by simp only [LinearMap.smul_apply, coeFn_coe, apply_lie_eq_sub,
        smul_sub, SMulBracketCommClass.smul_bracket_comm] }

@[simp]
/-
**LieDerivation.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `LieDerivation`。
形式化陈述：coe_smul (r : S) (D : LieDerivation R L M) : ⇑(r • D) = r • ⇑D
参数：r : S；D : LieDerivation R L M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul (r : S) (D : LieDerivation R L M) : ⇑(r • D) = r • ⇑D :=
  rfl

@[simp]
/-
**LieDerivation.coe_smul_linearMap** 是 Mathlib 中的一个定理，位于命名空间 `LieDerivation`。
形式化陈述：coe_smul_linearMap (r : S) (D : LieDerivation R L M) : ↑(r • D) = r • (D :
 L ->ₗ[R] M)
参数：r : S；D : LieDerivation R L M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul_linearMap (r : S) (D : LieDerivation R L M) : ↑(r • D) = r • (D : L →ₗ[R] M) :=
  rfl
/-
**LieDerivation.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieDerivation`。
形式化陈述：smul_apply (r : S) (D : LieDerivation R L M) : (r • D) a = r • D a
参数：r : S；D : LieDerivation R L M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_apply (r : S) (D : LieDerivation R L M) : (r • D) a = r • D a :=
  rfl
/-
**LieDerivation.instSMulBase** 是 Mathlib 中的一个实例，位于命名空间 `LieDerivation`。
形式化陈述：instSMulBase : SMulBracketCommClass R L M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lie_smul`：lie_smul : ⁅x, t • m⁆ = t • ⁅x, m⁆
-/
instance instSMulBase : SMulBracketCommClass R L M := ⟨fun s l a ↦ (lie_smul s l a).symm⟩
/-
**LieDerivation.instSMulNat** 是 Mathlib 中的一个实例，位于命名空间 `LieDerivation`。
形式化陈述：instSMulNat : SMulBracketCommClass Nat L M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lie_nsmul`：lie_nsmul (n : Nat) : ⁅x, n • m⁆ = n • ⁅x, m⁆
-/
instance instSMulNat : SMulBracketCommClass ℕ L M := ⟨fun s l a => (lie_nsmul l a s).symm⟩
/-
**LieDerivation.instSMulInt** 是 Mathlib 中的一个实例，位于命名空间 `LieDerivation`。
形式化陈述：instSMulInt : SMulBracketCommClass Int L M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lie_zsmul`：lie_zsmul (a : Int) : ⁅x, a • m⁆ = a • ⁅x, m⁆
-/
instance instSMulInt : SMulBracketCommClass ℤ L M := ⟨fun s l a => (lie_zsmul l a s).symm⟩
/-
**LieDerivation.instAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `LieDerivation`。
形式化陈述：instAddCommGroup : AddCommGroup (LieDerivation R L M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LieDerivation.coe_injective`：coe_injective : @Function.Injective (LieDer
ivation R L M) (L -> M) DFunLike.coe
· 使用定理 `LieDerivation.coe_zero`：coe_zero : ⇑(0 : LieDerivation R L M) = 0
· 使用定理 `LieDerivation.coe_add`：coe_add (D1 D2 : LieDerivation R L M) : ⇑(D1 + D2
) = D1 + D2
· 使用定理 `LieDerivation.coe_neg`：coe_neg (D : LieDerivation R L M) : ⇑(-D) = -D
· 使用定理 `LieDerivation.coe_sub`：coe_sub (D1 D2 : LieDerivation R L M) : ⇑(D1 - D2
) = D1 - D2
-/
instance instAddCommGroup : AddCommGroup (LieDerivation R L M) :=
  coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

/-- `coe_fn` as an `AddMonoidHom`. -/
/-
**LieDerivation.coeFnAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `LieDerivation`。
形式化陈述：coeFnAddMonoidHom : LieDerivation R L M ->+ L -> M where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LieDerivation.coe_zero`：coe_zero : ⇑(0 : LieDerivation R L M) = 0
· 使用定理 `LieDerivation.coe_add`：coe_add (D1 D2 : LieDerivation R L M) : ⇑(D1 + D2
) = D1 + D2

--- 原说明 ---
`coe_fn` as an `AddMonoidHom`.
-/
def coeFnAddMonoidHom : LieDerivation R L M →+ L → M where
  toFun := (↑)
  map_zero' := coe_zero
  map_add' := coe_add

@[simp]
/-
**LieDerivation.coeFnAddMonoidHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `LieDerivation
`。
形式化陈述：coeFnAddMonoidHom_apply (D : LieDerivation R L M) : coeFnAddMonoidHom D = 
D
参数：D : LieDerivation R L M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coeFnAddMonoidHom_apply (D : LieDerivation R L M) : coeFnAddMonoidHom D = D := rfl
/-
**LieDerivation.** 是 Mathlib 中的一个实例，位于命名空间 `LieDerivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DistribMulAction S (LieDerivation R L M) :=
  Function.Injective.distribMulAction coeFnAddMonoidHom coe_injective coe_smul
/-
**LieDerivation.** 是 Mathlib 中的一个实例，位于命名空间 `LieDerivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul S T] [IsScalarTower S T M] : IsScalarTower S T (LieDerivation R L M) :=
  ⟨fun _ _ _ => ext fun _ => smul_assoc _ _ _⟩
/-
**LieDerivation.** 是 Mathlib 中的一个实例，位于命名空间 `LieDerivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMulCommClass S T M] : SMulCommClass S T (LieDerivation R L M) :=
  ⟨fun _ _ _ => ext fun _ => smul_comm _ _ _⟩

end Scalar

/-
**LieDerivation.instModule** 是 Mathlib 中的一个实例，位于命名空间 `LieDerivation`。
形式化陈述：instModule {S : Type*} [Semiring S] [Module S M] [SMulCommClass R S M] [SM
ulBracketCommClass S L M] : Module S (LieDerivation R L M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LieDerivation.coe_injective`：coe_injective : @Function.Injective (LieDer
ivation R L M) (L -> M) DFunLike.coe
-/
instance instModule {S : Type*} [Semiring S] [Module S M] [SMulCommClass R S M]
    [SMulBracketCommClass S L M] : Module S (LieDerivation R L M) :=
  Function.Injective.module S coeFnAddMonoidHom coe_injective coe_smul

end

section

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The commutator of two Lie derivations on a Lie algebra is a Lie derivation. -/
/-
**LieDerivation.instBracket** 是 Mathlib 中的一个实例，位于命名空间 `LieDerivation`。
形式化陈述：instBracket : Bracket (LieDerivation R L L) (LieDerivation R L L) where br
acket D1 D2
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The commutator of two Lie derivations on a Lie algebra is a Lie derivation.
-/
instance instBracket : Bracket (LieDerivation R L L) (LieDerivation R L L) where
  bracket D1 D2 := LieDerivation.mk ⁅(D1 : Module.End R L), (D2 : Module.End R L)⁆ (fun a b => by
    simp only [Ring.lie_def, apply_lie_eq_add, coeFn_coe,
      LinearMap.sub_apply, Module.End.mul_apply, map_add, sub_lie, lie_sub, ← lie_skew b]
    abel)

variable {D1 D2 : LieDerivation R L L}

@[simp]
/-
**LieDerivation.commutator_coe_linear_map** 是 Mathlib 中的一个引理，位于命名空间 `LieDerivati
on`。
形式化陈述：commutator_coe_linear_map : ↑⁅D1, D2⁆ = ⁅(D1 : Module.End R L), (D2 : Modu
le.End R L)⁆
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma commutator_coe_linear_map : ↑⁅D1, D2⁆ = ⁅(D1 : Module.End R L), (D2 : Module.End R L)⁆ :=
  rfl
/-
**LieDerivation.commutator_apply** 是 Mathlib 中的一个引理，位于命名空间 `LieDerivation`。
形式化陈述：commutator_apply (a : L) : ⁅D1, D2⁆ a = D1 (D2 a) - D2 (D1 a)
参数：a : L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma commutator_apply (a : L) : ⁅D1, D2⁆ a = D1 (D2 a) - D2 (D1 a) :=
  rfl
/-
**LieDerivation.** 是 Mathlib 中的一个实例，位于命名空间 `LieDerivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LieRing (LieDerivation R L L) where
  add_lie d e f := by
    ext a; simp only [commutator_apply, add_apply, map_add]; abel
  lie_add d e f := by
    ext a; simp only [commutator_apply, add_apply, map_add]; abel
  lie_self d := by
    ext a; simp only [commutator_apply, zero_apply]; abel
  leibniz_lie d e f := by
    ext a; simp only [commutator_apply, add_apply, map_sub]; abel

set_option backward.isDefEq.respectTransparency false in
/-- The set of Lie derivations from a Lie algebra `L` to itself is a Lie algebra. -/
/-
**LieDerivation.instLieAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `LieDerivation`。
形式化陈述：instLieAlgebra : LieAlgebra R (LieDerivation R L L) where lie_smul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of Lie derivations from a Lie algebra `L` to itself is a Lie algebra.
-/
instance instLieAlgebra : LieAlgebra R (LieDerivation R L L) where
  lie_smul := fun r d e => by ext a; simp only [commutator_apply, map_smul, smul_sub, smul_apply]
/-
**LieDerivation.lie_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieDerivation`。
形式化陈述：∀ {R : Type u_1} {L : Type u_2} [inst : CommRing R] [inst_1 : LieRing L] [
inst_2 : LieAlgebra R L]   (D₁ D₂ : LieDerivation R L L) (x : L), ⁅D₁, D₂⁆ x = D
₁ (D₂ x) - D₂ (D₁ x)
参数：D₁ D₂ : LieDerivation R L L；x : L；D₂ x；D₁ x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma lie_apply (D₁ D₂ : LieDerivation R L L) (x : L) :
    ⁅D₁, D₂⁆ x = D₁ (D₂ x) - D₂ (D₁ x) :=
  rfl

end

section

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false in
/-- The Lie algebra morphism from Lie derivations into linear endomorphisms. -/
/-
**LieDerivation.toLinearMapLieHom** 是 Mathlib 中的一个定义，位于命名空间 `LieDerivation`。
形式化陈述：toLinearMapLieHom : LieDerivation R L L ->ₗ⁅R⁆ L ->ₗ[R] L where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Lie algebra morphism from Lie derivations into linear endomorphisms.
-/
def toLinearMapLieHom : LieDerivation R L L →ₗ⁅R⁆ L →ₗ[R] L where
  toFun := toLinearMap
  map_add' := by intro D1 D2; dsimp
  map_smul' := by intro D1 D2; dsimp
  map_lie' := by intro D1 D2; dsimp

/-- The map from Lie derivations to linear endomorphisms is injective. -/
/-
**LieDerivation.toLinearMapLieHom_injective** 是 Mathlib 中的一个引理，位于命名空间 `LieDeriva
tion`。
形式化陈述：toLinearMapLieHom_injective : Function.Injective (toLinearMapLieHom R L)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieDerivation.ext`：ext (H : forall a, D1 a = D2 a) : D1 = D2
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
The map from Lie derivations to linear endomorphisms is injective.
-/
lemma toLinearMapLieHom_injective : Function.Injective (toLinearMapLieHom R L) :=
  fun _ _ h ↦ ext fun a ↦ congrFun (congrArg DFunLike.coe h) a

set_option backward.isDefEq.respectTransparency false in
/-- Lie derivations over a Noetherian Lie algebra form a Noetherian module. -/
/-
**LieDerivation.instNoetherian** 是 Mathlib 中的一个实例，位于命名空间 `LieDerivation`。
形式化陈述：instNoetherian [IsNoetherian R L] : IsNoetherian R (LieDerivation R L L)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isNoetherian_of_linearEquiv`：isNoetherian_of_linearEquiv {σ : R ->+* S} 
{σ' : S ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f : M ≃ₛₗ[σ] P) [Is
Noetherian R M] :…
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用引理 `LieDerivation.toLinearMapLieHom_injective`：toLinearMapLieHom_injective :
 Function.Injective (toLinearMapLieHom R L)
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…

--- 原说明 ---
Lie derivations over a Noetherian Lie algebra form a Noetherian module.
-/
instance instNoetherian [IsNoetherian R L] : IsNoetherian R (LieDerivation R L L) :=
  isNoetherian_of_linearEquiv (LinearEquiv.ofInjective _ (toLinearMapLieHom_injective R L)).symm

end

section Inner

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

set_option backward.isDefEq.respectTransparency false in
/-- The natural map from a Lie module to the derivations taking values in it. -/
@[simps!]
/-
**LieDerivation.inner** 是 Mathlib 中的一个定义，位于命名空间 `LieDerivation`。
形式化陈述：inner : M ->ₗ[R] LieDerivation R L M where toFun m
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural map from a Lie module to the derivations taking values in it.
-/
def inner : M →ₗ[R] LieDerivation R L M where
  toFun m :=
    { __ := (LieModule.toEnd R L M : L →ₗ[R] Module.End R M).flip m
      leibniz' := by simp }
  map_add' m n := by ext; simp
  map_smul' t m := by ext; simp
/-
**LieDerivation.instLieRingModule** 是 Mathlib 中的一个实例，位于命名空间 `LieDerivation`。
形式化陈述：instLieRingModule : LieRingModule L (LieDerivation R L M) where bracket x 
D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLieRingModule : LieRingModule L (LieDerivation R L M) where
  bracket x D := inner R L M (D x)
  add_lie x y D := by simp
  lie_add x D₁ D₂ := by simp
  leibniz_lie x y D := by simp
/-
**LieDerivation.lie_lieDerivation_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieDerivation
`。
形式化陈述：∀ (R : Type u_1) (L : Type u_2) (M : Type u_3) [inst : CommRing R] [inst_1
 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   (x y 
: L) (D : LieDerivation R L M), ⁅x, D⁆ y = ⁅y, D x⁆
参数：R : Type u_1；L : Type u_2；M : Type u_3；x y : L；D : LieDerivation R L M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma lie_lieDerivation_apply (x y : L) (D : LieDerivation R L M) :
    ⁅x, D⁆ y = ⁅y, D x⁆ :=
  rfl
/-
**LieDerivation.lie_coe_lieDerivation_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieDeriva
tion`。
形式化陈述：∀ (R : Type u_1) (L : Type u_2) (M : Type u_3) [inst : CommRing R] [inst_1
 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M] (x : L)
   (D : LieDerivation R L M), ⁅x, ↑D⁆ = ↑⁅x, D⁆
参数：R : Type u_1；L : Type u_2；M : Type u_3；x : L；D : LieDerivation R L M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieDerivation.apply_lie_eq_sub`：apply_lie_eq_sub (D : LieDerivation R L 
M) (a b : L) : D ⁅a, b⁆ = ⁅a, D b⁆ - ⁅b, D a⁆
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma lie_coe_lieDerivation_apply (x : L) (D : LieDerivation R L M) :
    ⁅x, (D : L →ₗ[R] M)⁆ = ⁅x, D⁆ := by
  ext; simp

set_option backward.isDefEq.respectTransparency false in
/-
**LieDerivation.instLieModule** 是 Mathlib 中的一个实例，位于命名空间 `LieDerivation`。
形式化陈述：instLieModule : LieModule R L (LieDerivation R L M) where smul_lie t x D
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LieDerivation.ext`：ext (H : forall a, D1 a = D2 a) : D1 = D2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `lie_smul`：lie_smul : ⁅x, t • m⁆ = t • ⁅x, m⁆
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance instLieModule : LieModule R L (LieDerivation R L M) where
  smul_lie t x D := by ext; simp
  lie_smul t x D := by ext; simp
/-
**LieDerivation.leibniz_lie** 是 Mathlib 中的一个定理，位于命名空间 `LieDerivation`。
形式化陈述：∀ (R : Type u_1) (L : Type u_2) [inst : CommRing R] [inst_1 : LieRing L] [
inst_2 : LieAlgebra R L] (x : L)   (D₁ D₂ : LieDerivation R L L), ⁅x, ⁅D₁, D₂⁆⁆ 
= ⁅⁅x, D₁⁆, D₂⁆ + ⁅D₁, ⁅x, D₂⁆⁆
参数：R : Type u_1；L : Type u_2；x : L；D₁ D₂ : LieDerivation R L L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieDerivation.ext`：ext (H : forall a, D1 a = D2 a) : D1 = D2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_neg_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), a - b = -b + a
· 使用定理 `lie_add`：lie_add : ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `lie_neg`：lie_neg : ⁅x, -m⁆ = -⁅x, m⁆
· 使用引理 `LieDerivation.apply_lie_eq_sub`：apply_lie_eq_sub (D : LieDerivation R L 
M) (a b : L) : D ⁅a, b⁆ = ⁅a, D b⁆ - ⁅b, D a⁆
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lie_skew`：lie_skew : -⁅y, x⁆ = ⁅x, y⁆
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `neg_add_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ -b + b = a
· 使用定理 `neg_add_cancel_left`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), -a 
+ (a + b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma leibniz_lie (x : L) (D₁ D₂ : LieDerivation R L L) :
    ⁅x, ⁅D₁, D₂⁆⁆ = ⁅⁅x, D₁⁆, D₂⁆ + ⁅D₁, ⁅x, D₂⁆⁆ := by
  ext y
  simp [-lie_skew, ← lie_skew (D₁ x) (D₂ y), ← lie_skew (D₂ x) (D₁ y), sub_eq_neg_add]

end Inner

section ExpNilpotent

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L]
  (D : LieDerivation R L L)

/-- In characteristic zero, the exponential of a nilpotent derivation is a Lie algebra
automorphism. -/
/-
**LieDerivation.exp** 是 Mathlib 中的一个定义，位于命名空间 `LieDerivation`。
形式化陈述：exp (h : IsNilpotent D.toLinearMap) : L ≃ₗ⁅R⁆ L
参数：h : IsNilpotent D.toLinearMap。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In characteristic zero, the exponential of a nilpotent derivation is a Lie algeb
ra
automorphism.
-/
noncomputable def exp (h : IsNilpotent D.toLinearMap) :
    L ≃ₗ⁅R⁆ L :=
  { toLinearMap := IsNilpotent.exp D.toLinearMap
    map_lie' := by
      let _i := LieRing.toNonUnitalNonAssocRing L
      have : SMulCommClass R L L := LieAlgebra.smulCommClass R L
      have : IsScalarTower R L L := LieAlgebra.isScalarTower R L
      exact Module.End.exp_mul_of_derivation R L D.toLinearMap D.apply_lie_eq_add h
    invFun x := IsNilpotent.exp (- D.toLinearMap) x
    left_inv x := by
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ← LinearMap.comp_apply,
        ← Module.End.mul_eq_comp, h.exp_neg_mul_exp_self, Module.End.one_apply]
    right_inv x := by
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ← LinearMap.comp_apply,
        ← Module.End.mul_eq_comp, h.exp_mul_exp_neg_self, Module.End.one_apply] }
/-
**LieDerivation.exp_apply** 是 Mathlib 中的一个引理，位于命名空间 `LieDerivation`。
形式化陈述：exp_apply (h : IsNilpotent D.toLinearMap) : exp D h = IsNilpotent.exp D.to
LinearMap
参数：h : IsNilpotent D.toLinearMap。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exp_apply (h : IsNilpotent D.toLinearMap) :
    exp D h = IsNilpotent.exp D.toLinearMap :=
  rfl
/-
**LieDerivation.exp_map_apply** 是 Mathlib 中的一个引理，位于命名空间 `LieDerivation`。
形式化陈述：exp_map_apply (h : IsNilpotent D.toLinearMap) (l : L) : exp D h l = IsNilp
otent.exp D.toLinearMap l
参数：h : IsNilpotent D.toLinearMap；l : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用引理 `LieDerivation.exp_apply`：exp_apply (h : IsNilpotent D.toLinearMap) : exp
 D h = IsNilpotent.exp D.toLinearMap
-/
lemma exp_map_apply (h : IsNilpotent D.toLinearMap) (l : L) :
    exp D h l = IsNilpotent.exp D.toLinearMap l :=
  DFunLike.congr_fun (exp_apply D h) l

end ExpNilpotent

end LieDerivation

