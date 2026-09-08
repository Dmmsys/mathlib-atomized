/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.GroupWithZero.Regular
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Opposite
public import Mathlib.Algebra.Regular.Opposite
public import Mathlib.Algebra.Regular.SMul

/-!
# Torsion-free modules

This files defines a torsion-free `R`-(semi)module `M` as a (semi)module where scalar multiplication
by a regular element `r : R` is injective as a map `M → M`.

In the case of a module (group over a ring), this is equivalent to saying that `r • m = 0` for
some `r : R`, `m : M` implies that `r` is a zero-divisor.
If furthermore the base ring is a domain, this is equivalent to the naïve
`r • m = 0 ↔ r = 0 ∨ m = 0` definition.
-/

public section

open Module

variable {R S M N : Type*}

section Semiring
variable [Semiring R] [Semiring S]

section AddCommMonoid
variable [AddCommMonoid M] [Module R M] [Module S M] [AddCommMonoid N] [Module R N]
  {r : R} {m m₁ m₂ : M}

variable (R M) in
/-- An `R`-module `M` is torsion-free if scalar multiplication by an element `r : R` is injective if
multiplication (on `R`) by `r` is.

For domains, this is equivalent to the usual condition of `r • m = 0 → r = 0 ∨ m = 0`.
See `smul_eq_zero`. -/
/-
**Module.IsTorsionFree** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：Module.IsTorsionFree where isSMulRegular ⦃r : R⦄ : IsRegular r -> IsSMulRe
gular M r  alias IsRegular.isSMulRegular
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `R`-module `M` is torsion-free if scalar multiplication by an element `r : R`
 is injective if
multiplication (on `R`) by `r` is.

For domains, this is equivalent to the usual condition of `r • m = 0 → r = 0 ∨ m
 = 0`.
See `smul_eq_zero`.
-/
class Module.IsTorsionFree where
  isSMulRegular ⦃r : R⦄ : IsRegular r → IsSMulRegular M r

alias IsRegular.isSMulRegular := IsTorsionFree.isSMulRegular
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTorsionFree R R where isSMulRegular _r hr := hr.1
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTorsionFree Rᵐᵒᵖ R where isSMulRegular _r hr := hr.unop.2

/-- Pullback an `IsTorsionFree` instance along an injective function. -/
/-
**Function.Injective.moduleIsTorsionFree** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Function.Injective.moduleIsTorsionFree [IsTorsionFree R N] (f : M -> N) (h
f : f.Injective) (smul : forall (r : R) (m : M), f (r • m) = r • f m) : IsTorsio
nFree R M where isSMulRegular r hr m₁ m₂ hm
参数：f : M -> N；hf : f.Injective；smul : forall (r : R) (m : M), f (r • m) = r • f 
m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRegular.isSMulRegular`：∀ {R : Type u_1} {M : Type u_3} {inst : Semirin
g R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Is
TorsionFree R…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
Pullback an `IsTorsionFree` instance along an injective function.
-/
lemma Function.Injective.moduleIsTorsionFree [IsTorsionFree R N] (f : M → N) (hf : f.Injective)
    (smul : ∀ (r : R) (m : M), f (r • m) = r • f m) : IsTorsionFree R M where
  isSMulRegular r hr m₁ m₂ hm := hf <| hr.isSMulRegular <| by simpa [smul] using congr(f $hm)

/-- Pullback an `IsTorsionFree` instance along a function preserving scalar multiplication and
regular elements. -/
/-
**Module.IsTorsionFree.comap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.IsTorsionFree.comap [IsTorsionFree S M] (f : R -> S) (isRegular : f
orall r, IsRegular r -> IsRegular (f r)) (smul : forall (r : R) (m : M), f r • m
 = r • m) : IsTorsionFree R M where isSMulRegular r hr
参数：f : R -> S；isRegular : forall r, IsRegular r -> IsRegular (f r)；smul : forall
 (r : R) (m : M), f r • m = r • m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSMulRegular.of_map`：∀ {R : Type u_1} {S : Type u_2} {M : Type u_3} {a 
: R} [inst : SMul R M] [inst_1 : SMul S M] (f : R → S),   (∀ (m : M), f a • m = 
a • m) → I…
· 使用定理 `IsRegular.isSMulRegular`：∀ {R : Type u_1} {M : Type u_3} {inst : Semirin
g R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Is
TorsionFree R…

--- 原说明 ---
Pullback an `IsTorsionFree` instance along a function preserving scalar multipli
cation and
regular elements.
-/
lemma Module.IsTorsionFree.comap [IsTorsionFree S M] (f : R → S)
    (isRegular : ∀ r, IsRegular r → IsRegular (f r)) (smul : ∀ (r : R) (m : M), f r • m = r • m) :
    IsTorsionFree R M where
  isSMulRegular r hr := (isRegular _ hr).isSMulRegular.of_map f (smul r)
/-
**IsAddTorsionFree.to_isTorsionFree_nat** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsAddTorsionFree.to_isTorsionFree_nat [IsAddTorsionFree M] : IsTorsionFree
 Nat M where isSMulRegular n hn
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `nsmul_right_injective`：∀ {M : Type u_1} [inst : AddMonoid M] [IsAddTorsi
onFree M] {n : ℕ}, n ≠ 0 → Function.Injective fun a => n • a
-/
instance IsAddTorsionFree.to_isTorsionFree_nat [IsAddTorsionFree M] : IsTorsionFree ℕ M where
  isSMulRegular n hn := nsmul_right_injective (by simpa [isRegular_iff_ne_zero] using hn)
/-
**Subsingleton.to_moduleIsTorsionFree** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subsingleton.to_moduleIsTorsionFree [Subsingleton M] : IsTorsionFree R M w
here isSMulRegular _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.injective_of_subsingleton`：∀ {α : Sort u_1} {β : Sort u_2} [Sub
singleton α] (f : α → β), Function.Injective f
-/
instance Subsingleton.to_moduleIsTorsionFree [Subsingleton M] : IsTorsionFree R M where
  isSMulRegular _ _ := Function.injective_of_subsingleton _

variable [IsTorsionFree R M]

variable (M) in
/-
**IsRegular.smul_right_injective** 是 Mathlib 中的一个定理，位于命名空间 `IsRegular`。
形式化陈述：∀ {R : Type u_1} (M : Type u_3) [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M] {r : R}   [Module.IsTorsionFree R M], IsRegula
r r → Function.Injective fun x => r • x
参数：M : Type u_3。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRegular.isSMulRegular`：∀ {R : Type u_1} {M : Type u_3} {inst : Semirin
g R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Is
TorsionFree R…
-/
protected lemma IsRegular.smul_right_injective (hr : IsRegular r) : ((r • ·) : M → M).Injective :=
  hr.isSMulRegular
/-
**IsRegular.smul_right_inj** 是 Mathlib 中的一个定理，位于命名空间 `IsRegular`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M] {r : R}   {m₁ m₂ : M} [Module.IsTorsionFree R 
M], IsRegular r → (r • m₁ = r • m₂ ↔ m₁ = m₂)
参数：r • m₁ = r • m₂ ↔ m₁ = m₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `IsRegular.smul_right_injective`：∀ {R : Type u_1} (M : Type u_3) [inst : 
Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {r : R}   [M
odule.IsTorsionFree …
-/
@[simp] protected lemma IsRegular.smul_right_inj (hr : IsRegular r) : r • m₁ = r • m₂ ↔ m₁ = m₂ :=
  (hr.smul_right_injective _).eq_iff
/-
**IsRegular.smul_eq_zero_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `IsRegular`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M] {r : R}   {m : M} [Module.IsTorsionFree R M], 
IsRegular r → (r • m = 0 ↔ m = 0)
参数：r • m = 0 ↔ m = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsRegular.smul_right_inj`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiri
ng R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {r : R}   {m₁ m₂ :
 M} [Module.Is…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] protected lemma IsRegular.smul_eq_zero_iff_right (hr : IsRegular r) :
    r • m = 0 ↔ m = 0 := by rw [← hr.smul_right_inj (m₁ := m), smul_zero]
/-
**IsRegular.smul_ne_zero_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `IsRegular`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M] {r : R}   {m : M} [Module.IsTorsionFree R M], 
IsRegular r → (r • m ≠ 0 ↔ m ≠ 0)
参数：r • m ≠ 0 ↔ m ≠ 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用定理 `IsRegular.smul_eq_zero_iff_right`：∀ {R : Type u_1} {M : Type u_3} [inst 
: Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {r : R}   
{m : M} [Module.IsTors…
-/
protected lemma IsRegular.smul_ne_zero_iff_right (hr : IsRegular r) : r • m ≠ 0 ↔ m ≠ 0 :=
  hr.smul_eq_zero_iff_right.ne

variable (R) in
/-
**Module.IsTorsionFree.trans** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.IsTorsionFree.trans [Module S R] [IsTorsionFree S R] [IsScalarTower
 S R R] [SMulCommClass S R R] [IsScalarTower S R M] : IsTorsionFree S M where is
SMulRegular s hs x y hxy
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRegular.isSMulRegular`：∀ {R : Type u_1} {M : Type u_3} {inst : Semirin
g R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Is
TorsionFree R…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_one_mul`：smul_one_mul {M N} [MulOneClass N] [SMul M N] [IsScalarTow
er M N N] (x : M) (y : N) : x • (1 : N) * y = x • y
· 使用引理 `mul_smul_one`：mul_smul_one {M N} [MulOneClass N] [SMul M N] [SMulCommCla
ss M N N] (x : M) (y : N) : y * x • (1 : N) = x • y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
lemma Module.IsTorsionFree.trans [Module S R] [IsTorsionFree S R] [IsScalarTower S R R]
    [SMulCommClass S R R] [IsScalarTower S R M] : IsTorsionFree S M where
  isSMulRegular s hs x y hxy := by
    refine (?_ : IsRegular (s • 1 : R)).isSMulRegular (by simpa using hxy)
    exact ⟨fun x y hxy ↦ hs.isSMulRegular <| by simpa using hxy,
      fun x y hxy ↦ hs.isSMulRegular <| by simpa using hxy⟩

variable [IsCancelMulZero R]
/-
**IsSMulRegular.of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSMulRegular.of_ne_zero (hr : r != 0) : IsSMulRegular M r
参数：hr : r != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRegular.isSMulRegular`：∀ {R : Type u_1} {M : Type u_3} {inst : Semirin
g R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Is
TorsionFree R…
· 使用定理 `IsRegular.of_ne_zero`：IsRegular.of_ne_zero (a0 : a != 0) : IsRegular a
-/
lemma IsSMulRegular.of_ne_zero (hr : r ≠ 0) : IsSMulRegular M r :=
  (IsRegular.of_ne_zero hr).isSMulRegular

variable (M) in
/-
**smul_right_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_right_injective (hr : r != 0) : ((r • ·) : M -> M).Injective
参数：hr : r != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRegular.smul_right_injective`：∀ {R : Type u_1} (M : Type u_3) [inst : 
Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {r : R}   [M
odule.IsTorsionFree …
· 使用定理 `IsRegular.of_ne_zero`：IsRegular.of_ne_zero (a0 : a != 0) : IsRegular a
-/
lemma smul_right_injective (hr : r ≠ 0) : ((r • ·) : M → M).Injective :=
  (IsRegular.of_ne_zero hr).smul_right_injective _
/-
**smul_right_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M] {r : R}   {m₁ m₂ : M} [Module.IsTorsionFree R 
M] [IsCancelMulZero R], r ≠ 0 → (r • m₁ = r • m₂ ↔ m₁ = m₂)
参数：r • m₁ = r • m₂ ↔ m₁ = m₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRegular.smul_right_inj`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiri
ng R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {r : R}   {m₁ m₂ :
 M} [Module.Is…
· 使用定理 `IsRegular.of_ne_zero`：IsRegular.of_ne_zero (a0 : a != 0) : IsRegular a
-/
@[simp] lemma smul_right_inj (hr : r ≠ 0) : r • m₁ = r • m₂ ↔ m₁ = m₂ :=
  (IsRegular.of_ne_zero hr).smul_right_inj
/-
**smul_eq_zero_iff_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_eq_zero_iff_right (hr : r != 0) : r • m = 0 ↔ m = 0
参数：hr : r != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRegular.smul_eq_zero_iff_right`：∀ {R : Type u_1} {M : Type u_3} [inst 
: Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {r : R}   
{m : M} [Module.IsTors…
· 使用定理 `IsRegular.of_ne_zero`：IsRegular.of_ne_zero (a0 : a != 0) : IsRegular a
-/
lemma smul_eq_zero_iff_right (hr : r ≠ 0) : r • m = 0 ↔ m = 0 :=
  (IsRegular.of_ne_zero hr).smul_eq_zero_iff_right
/-
**smul_ne_zero_iff_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_ne_zero_iff_right (hr : r != 0) : r • m != 0 ↔ m != 0
参数：hr : r != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用引理 `smul_eq_zero_iff_right`：smul_eq_zero_iff_right (hr : r != 0) : r • m = 0
 ↔ m = 0
-/
lemma smul_ne_zero_iff_right (hr : r ≠ 0) : r • m ≠ 0 ↔ m ≠ 0 := (smul_eq_zero_iff_right hr).ne
/-
**smul_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M] {r : R}   {m : M} [Module.IsTorsionFree R M] [
IsCancelMulZero R], r • m = 0 ↔ r = 0 ∨ m = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
@[simp] lemma smul_eq_zero : r • m = 0 ↔ r = 0 ∨ m = 0 := by
  obtain rfl | hr := eq_or_ne r 0 <;> simp [smul_eq_zero_iff_right, *]
/-
**smul_ne_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_ne_zero_iff : r • m != 0 ↔ r != 0 ∧ m != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma smul_ne_zero_iff : r • m ≠ 0 ↔ r ≠ 0 ∧ m ≠ 0 := by simp
/-
**smul_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_ne_zero (hr : r != 0) (hm : m != 0) : r • m != 0
参数：hr : r != 0；hm : m != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma smul_ne_zero (hr : r ≠ 0) (hm : m ≠ 0) : r • m ≠ 0 := by simp [*]
/-
**smul_eq_zero_iff_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_eq_zero_iff_left (hm : m != 0) : r • m = 0 ↔ r = 0
参数：hm : m != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma smul_eq_zero_iff_left (hm : m ≠ 0) : r • m = 0 ↔ r = 0 := by simp [*]
/-
**smul_ne_zero_iff_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_ne_zero_iff_left (hm : m != 0) : r • m != 0 ↔ r != 0
参数：hm : m != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma smul_ne_zero_iff_left (hm : m ≠ 0) : r • m ≠ 0 ↔ r ≠ 0 := by simp [*]

variable [CharZero R]

variable (R M) in
include R in
/-
**IsAddTorsionFree.of_isTorsionFree** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsAddTorsionFree.of_isTorsionFree : IsAddTorsionFree M where nsmul_right_i
njective n hn
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用引理 `smul_right_injective`：smul_right_injective (hr : r != 0) : ((r • ·) : M 
-> M).Injective
-/
lemma IsAddTorsionFree.of_isTorsionFree : IsAddTorsionFree M where
  nsmul_right_injective n hn := by
    simp_rw [← Nat.cast_smul_eq_nsmul R]; apply smul_right_injective; simpa

/-- A characteristic zero domain is torsion-free. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A characteristic zero domain is torsion-free.
-/
instance (priority := 100) IsAddTorsionFree.of_isDomain_charZero : IsAddTorsionFree R :=
  .of_isTorsionFree R R

@[simp]
/-
**Module.isTorsionFree_nat_iff_isAddTorsionFree** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.isTorsionFree_nat_iff_isAddTorsionFree : IsTorsionFree Nat M ↔ IsAd
dTorsionFree M where mp _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsAddTorsionFree.of_isTorsionFree`：IsAddTorsionFree.of_isTorsionFree : I
sAddTorsionFree M where nsmul_right_injective n hn
-/
lemma Module.isTorsionFree_nat_iff_isAddTorsionFree : IsTorsionFree ℕ M ↔ IsAddTorsionFree M where
  mp _ := .of_isTorsionFree ℕ _
  mpr _ := inferInstance

end AddCommMonoid

section AddCommGroup
variable [CharZero R] [IsDomain R] [AddCommGroup M] [Module R M] {m : M}

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsAddTorsionFree M] : IsTorsionFree ℤ M where
  isSMulRegular n hn := zsmul_right_injective (by simpa [isRegular_iff_ne_zero] using hn)

@[simp]
/-
**Module.isTorsionFree_int_iff_isAddTorsionFree** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.isTorsionFree_int_iff_isAddTorsionFree : IsTorsionFree Int M ↔ IsAd
dTorsionFree M where mp _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsAddTorsionFree.of_isTorsionFree`：IsAddTorsionFree.of_isTorsionFree : I
sAddTorsionFree M where nsmul_right_injective n hn
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
-/
lemma Module.isTorsionFree_int_iff_isAddTorsionFree : IsTorsionFree ℤ M ↔ IsAddTorsionFree M where
  mp _ := .of_isTorsionFree ℤ _
  mpr _ := inferInstance

end AddCommGroup
end Semiring

section Ring
variable [Ring R] [AddCommGroup M] [Module R M] {m : M} {r₁ r₂ : R}

/-
**Module.IsTorsionFree.of_smul_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.IsTorsionFree.of_smul_eq_zero [Nontrivial R] (h : forall (r : R) (m
 : M), r • m = 0 -> r = 0 ∨ m = 0) : IsTorsionFree R M where isSMulRegular r hr 
m₁ m₂ hm
参数：h : forall (r : R) (m : M), r • m = 0 -> r = 0 ∨ m = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `IsRegular.ne_zero`：IsRegular.ne_zero [Nontrivial R] (la : IsRegular a) :
 a != 0
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
-/
lemma Module.IsTorsionFree.of_smul_eq_zero [Nontrivial R]
    (h : ∀ (r : R) (m : M), r • m = 0 → r = 0 ∨ m = 0) :
    IsTorsionFree R M where
  isSMulRegular r hr m₁ m₂ hm := by
    simpa [sub_eq_zero, hr.ne_zero] using h r (m₁ - m₂) (by simpa [smul_sub, sub_eq_zero] using hm)
/-
**Module.isTorsionFree_iff_smul_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.isTorsionFree_iff_smul_eq_zero [IsDomain R] : IsTorsionFree R M ↔ f
orall (r : R) (m : M), r • m = 0 -> r = 0 ∨ m = 0 where mp _ _ _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `smul_eq_zero`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_
1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {r : R}   {m : M} [Module.IsTo
rs…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用引理 `Module.IsTorsionFree.of_smul_eq_zero`：Module.IsTorsionFree.of_smul_eq_ze
ro [Nontrivial R] (h : forall (r : R) (m : M), r • m = 0 -> r = 0 ∨ m = 0) : IsT
orsionFree R M where isSMu…
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
-/
lemma Module.isTorsionFree_iff_smul_eq_zero [IsDomain R] :
    IsTorsionFree R M ↔ ∀ (r : R) (m : M), r • m = 0 → r = 0 ∨ m = 0 where
  mp _ _ _ := smul_eq_zero.1
  mpr := .of_smul_eq_zero

variable [IsCancelMulZero R] [IsTorsionFree R M]

variable (R) in
/-
**smul_left_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_left_injective (hm : m != 0) : ((· • m) : R -> M).Injective
参数：hm : m != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用引理 `smul_eq_zero_iff_left`：smul_eq_zero_iff_left (hm : m != 0) : r • m = 0 ↔
 r = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
-/
lemma smul_left_injective (hm : m ≠ 0) : ((· • m) : R → M).Injective := by
  rintro r₁ r₂ hr
  dsimp at hr
  rwa [← sub_eq_zero, ← sub_smul, smul_eq_zero_iff_left hm, sub_eq_zero] at hr
/-
**smul_left_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} [inst : Ring R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M] {m : M}   {r₁ r₂ : R} [IsCancelMulZero R] [Module.I
sTorsionFree R M], m ≠ 0 → (r₁ • m = r₂ • m ↔ r₁ = r₂)
参数：r₁ • m = r₂ • m ↔ r₁ = r₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `smul_left_injective`：smul_left_injective (hm : m != 0) : ((· • m) : R ->
 M).Injective
-/
@[simp] lemma smul_left_inj (hm : m ≠ 0) : r₁ • m = r₂ • m ↔ r₁ = r₂ :=
  (smul_left_injective _ hm).eq_iff

end Ring

section Semiring
variable (R M) [Semiring R] [AddCommGroup M] [Module R M]

-- TODO: Add a `ℤ`-specific version of `smul_left_injective` and move this lemma to an earlier file.
/-- Only a ring of characteristic zero can have a non-trivial module without additive or
scalar torsion. -/
/-
**CharZero.of_isAddTorsionFree** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CharZero.of_isAddTorsionFree [Nontrivial M] [IsAddTorsionFree M] : CharZer
o R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `smul_left_injective`：smul_left_injective (hm : m != 0) : ((· • m) : R ->
 M).Injective
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M

--- 原说明 ---
Only a ring of characteristic zero can have a non-trivial module without additiv
e or
scalar torsion.
-/
lemma CharZero.of_isAddTorsionFree [Nontrivial M] [IsAddTorsionFree M] : CharZero R := by
  refine ⟨fun {n m h} ↦ ?_⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  replace h : (n : ℤ) • x = (m : ℤ) • x := by simp [← Nat.cast_smul_eq_nsmul R, h]
  simpa using smul_left_injective ℤ hx h

end Semiring

