/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Regular.Basic

/-!
# Product of regular elements

## TODO

Move to `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`?
-/

public section


variable {R : Type*} {a b : R}

section CommMonoid

variable {ι R : Type*} [CommMonoid R] {s : Finset ι} {f : ι → R}

/-
**IsLeftRegular.prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLeftRegular.prod (h : forall i in s, IsLeftRegular (f i)) : IsLeftRegula
r (∏ i in s, f i)
参数：h : forall i in s, IsLeftRegular (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_induction`：prod_induction {M : Type*} [CommMonoid M] (f : ι 
-> M) (p : M -> Prop) (hom : forall a b, p a -> p b -> p (a * b)) (unit : p 1) (
base : fora…
· 使用定理 `IsLeftRegular.mul`：IsLeftRegular.mul (lra : IsLeftRegular a) (lrb : IsLe
ftRegular b) : IsLeftRegular (a * b)
· 使用定理 `IsRegular.left`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → I
sLeftRegular c
· 使用定理 `isRegular_one`：isRegular_one : IsRegular (1 : R)
-/
lemma IsLeftRegular.prod (h : ∀ i ∈ s, IsLeftRegular (f i)) :
    IsLeftRegular (∏ i ∈ s, f i) :=
  s.prod_induction _ _ (@IsLeftRegular.mul R _) isRegular_one.left h
/-
**IsRightRegular.prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsRightRegular.prod (h : forall i in s, IsRightRegular (f i)) : IsRightReg
ular (∏ i in s, f i)
参数：h : forall i in s, IsRightRegular (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_induction`：prod_induction {M : Type*} [CommMonoid M] (f : ι 
-> M) (p : M -> Prop) (hom : forall a b, p a -> p b -> p (a * b)) (unit : p 1) (
base : fora…
· 使用定理 `IsRightRegular.mul`：IsRightRegular.mul (rra : IsRightRegular a) (rrb : I
sRightRegular b) : IsRightRegular (a * b)
· 使用定理 `IsRegular.right`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → 
IsRightRegular c
· 使用定理 `isRegular_one`：isRegular_one : IsRegular (1 : R)
-/
lemma IsRightRegular.prod (h : ∀ i ∈ s, IsRightRegular (f i)) :
    IsRightRegular (∏ i ∈ s, f i) :=
  s.prod_induction _ _ (@IsRightRegular.mul R _) isRegular_one.right h
/-
**IsRegular.prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsRegular.prod (h : forall i in s, IsRegular (f i)) : IsRegular (∏ i in s,
 f i)
参数：h : forall i in s, IsRegular (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLeftRegular.prod`：IsLeftRegular.prod (h : forall i in s, IsLeftRegular
 (f i)) : IsLeftRegular (∏ i in s, f i)
· 使用定理 `IsRegular.left`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → I
sLeftRegular c
· 使用引理 `IsRightRegular.prod`：IsRightRegular.prod (h : forall i in s, IsRightRegu
lar (f i)) : IsRightRegular (∏ i in s, f i)
· 使用定理 `IsRegular.right`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → 
IsRightRegular c
-/
lemma IsRegular.prod (h : ∀ i ∈ s, IsRegular (f i)) :
    IsRegular (∏ i ∈ s, f i) :=
  ⟨IsLeftRegular.prod fun a ha ↦ (h a ha).left,
   IsRightRegular.prod fun a ha ↦ (h a ha).right⟩

end CommMonoid

