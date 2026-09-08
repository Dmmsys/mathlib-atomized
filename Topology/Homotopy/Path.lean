/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
module

public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Analysis.Convex.Basic

/-!
# Homotopy between paths

In this file, we define a `Homotopy` between two `Path`s. In addition, we define a relation
`Homotopic` on `Path`s, and prove that it is an equivalence relation.

## Definitions

* `Path.Homotopy p₀ p₁` is the type of homotopies between paths `p₀` and `p₁`
* `Path.Homotopy.refl p` is the constant homotopy between `p` and itself
* `Path.Homotopy.symm F` is the `Path.Homotopy p₁ p₀` defined by reversing the homotopy
* `Path.Homotopy.trans F G`, where `F : Path.Homotopy p₀ p₁`, `G : Path.Homotopy p₁ p₂` is the
  `Path.Homotopy p₀ p₂` defined by putting the first homotopy on `[0, 1/2]` and the second on
  `[1/2, 1]`
* `Path.Homotopy.hcomp F G`, where `F : Path.Homotopy p₀ q₀` and `G : Path.Homotopy p₁ q₁` is
  a `Path.Homotopy (p₀.trans p₁) (q₀.trans q₁)`
* `Path.Homotopic p₀ p₁` is the relation saying that there is a homotopy between `p₀` and `p₁`
* `Path.Homotopic.setoid x₀ x₁` is the setoid on `Path`s from `Path.Homotopic`
* `Path.Homotopic.Quotient x₀ x₁` is the quotient type from `Path x₀ x₀` by `Path.Homotopic.setoid`

-/

@[expose] public section


universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {x₀ x₁ x₂ x₃ : X}

noncomputable section

open unitInterval

namespace Path

/-- The type of homotopies between two paths.
-/
/-
**Path.Homotopy** 是 Mathlib 中的一个缩写定义，位于命名空间 `Path`。
形式化陈述：Homotopy (p₀ p₁ : Path x₀ x₁)
参数：p₀ p₁ : Path x₀ x₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of homotopies between two paths.
-/
abbrev Homotopy (p₀ p₁ : Path x₀ x₁) :=
  ContinuousMap.HomotopyRel p₀.toContinuousMap p₁.toContinuousMap {0, 1}

namespace Homotopy

section

variable {p₀ p₁ : Path x₀ x₁}

/-
**Path.Homotopy.coeFn_injective** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopy`。
形式化陈述：coeFn_injective : @Function.Injective (Homotopy p₀ p₁) (I × I -> X) (⇑)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem coeFn_injective : @Function.Injective (Homotopy p₀ p₁) (I × I → X) (⇑) :=
  DFunLike.coe_injective

@[simp]
/-
**Path.Homotopy.source** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopy`。
形式化陈述：source (F : Homotopy p₀ p₁) (t : I) : F (t, 0) = x₀
参数：F : Homotopy p₀ p₁；t : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.HomotopyRel.eq_fst`：eq_fst (F : HomotopyRel f₀ f₁ S) (t : 
I) {x : X} (hx : x in S) : F (t, x) = f₀ x
· 使用定理 `Path.source`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ :
 Path x y), γ 0 = x
-/
theorem source (F : Homotopy p₀ p₁) (t : I) : F (t, 0) = x₀ :=
  calc F (t, 0) = p₀ 0 := ContinuousMap.HomotopyRel.eq_fst _ _ (.inl rfl)
  _ = x₀ := p₀.source

@[simp]
/-
**Path.Homotopy.target** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopy`。
形式化陈述：target (F : Homotopy p₀ p₁) (t : I) : F (t, 1) = x₁
参数：F : Homotopy p₀ p₁；t : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.HomotopyRel.eq_fst`：eq_fst (F : HomotopyRel f₀ f₁ S) (t : 
I) {x : X} (hx : x in S) : F (t, x) = f₀ x
· 使用定理 `Path.target`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ :
 Path x y), γ 1 = y
-/
theorem target (F : Homotopy p₀ p₁) (t : I) : F (t, 1) = x₁ :=
  calc F (t, 1) = p₀ 1 := ContinuousMap.HomotopyRel.eq_fst _ _ (.inr rfl)
  _ = x₁ := p₀.target

/-- Evaluating a path homotopy at an intermediate point, giving us a `Path`.
-/
@[simps]
/-
**Path.Homotopy.eval** 是 Mathlib 中的一个定义，位于命名空间 `Path.Homotopy`。
形式化陈述：eval (F : Homotopy p₀ p₁) (t : I) : Path x₀ x₁ where toFun
参数：F : Homotopy p₀ p₁；t : I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluating a path homotopy at an intermediate point, giving us a `Path`.
-/
def eval (F : Homotopy p₀ p₁) (t : I) : Path x₀ x₁ where
  toFun := F.toHomotopy.curry t
  source' := by simp
  target' := by simp

@[simp]
/-
**Path.Homotopy.eval_zero** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopy`。
形式化陈述：eval_zero (F : Homotopy p₀ p₁) : F.eval 0 = p₀
参数：F : Homotopy p₀ p₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.ext`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} {γ₁ γ₂ 
: Path x y}, ⇑γ₁ = ⇑γ₂ → γ₁ = γ₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Path.Homotopy.eval_apply`：∀ {X : Type u} [inst : TopologicalSpace X] {x₀
 x₁ : X} {p₀ p₁ : Path x₀ x₁} (F : p₀.Homotopy p₁) (t a : ↑unitInterval),   (F.e
val t) a = (F.…
· 使用定理 `ContinuousMap.Homotopy.curry_zero`：∀ {X : Type u} {Y : Type v} [inst : T
opologicalSpace X] [inst_1 : TopologicalSpace Y] {f₀ f₁ : C(X, Y)}   (F : f₀.Hom
otopy f₁), F.curry 0 = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eval_zero (F : Homotopy p₀ p₁) : F.eval 0 = p₀ := by
  ext t
  simp

@[simp]
/-
**Path.Homotopy.eval_one** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopy`。
形式化陈述：eval_one (F : Homotopy p₀ p₁) : F.eval 1 = p₁
参数：F : Homotopy p₀ p₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.ext`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} {γ₁ γ₂ 
: Path x y}, ⇑γ₁ = ⇑γ₂ → γ₁ = γ₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Path.Homotopy.eval_apply`：∀ {X : Type u} [inst : TopologicalSpace X] {x₀
 x₁ : X} {p₀ p₁ : Path x₀ x₁} (F : p₀.Homotopy p₁) (t a : ↑unitInterval),   (F.e
val t) a = (F.…
· 使用定理 `ContinuousMap.Homotopy.curry_one`：∀ {X : Type u} {Y : Type v} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] {f₀ f₁ : C(X, Y)}   (F : f₀.Homo
topy f₁), F.curry 1 = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eval_one (F : Homotopy p₀ p₁) : F.eval 1 = p₁ := by
  ext t
  simp

end

section

variable {p₀ p₁ p₂ : Path x₀ x₁}

/-- Given a path `p`, we can define a `Homotopy p p` by `F (t, x) = p x`.
-/
@[simps!]
/-
**Path.Homotopy.refl** 是 Mathlib 中的一个定义，位于命名空间 `Path.Homotopy`。
形式化陈述：refl (p : Path x₀ x₁) : Homotopy p p
参数：p : Path x₀ x₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a path `p`, we can define a `Homotopy p p` by `F (t, x) = p x`.
-/
def refl (p : Path x₀ x₁) : Homotopy p p :=
  ContinuousMap.HomotopyRel.refl p.toContinuousMap {0, 1}

/-- Given a `Homotopy p₀ p₁`, we can define a `Homotopy p₁ p₀` by reversing the homotopy.
-/
@[simps!]
/-
**Path.Homotopy.symm** 是 Mathlib 中的一个定义，位于命名空间 `Path.Homotopy`。
形式化陈述：symm (F : Homotopy p₀ p₁) : Homotopy p₁ p₀
参数：F : Homotopy p₀ p₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a `Homotopy p₀ p₁`, we can define a `Homotopy p₁ p₀` by reversing the homo
topy.
-/
def symm (F : Homotopy p₀ p₁) : Homotopy p₁ p₀ :=
  ContinuousMap.HomotopyRel.symm F

@[simp]
/-
**Path.Homotopy.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopy`。
形式化陈述：symm_symm (F : Homotopy p₀ p₁) : F.symm.symm = F
参数：F : Homotopy p₀ p₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.HomotopyRel.symm_symm`：symm_symm (F : HomotopyRel f₀ f₁ S)
 : F.symm.symm = F
-/
theorem symm_symm (F : Homotopy p₀ p₁) : F.symm.symm = F :=
  ContinuousMap.HomotopyRel.symm_symm F
/-
**Path.Homotopy.symm_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopy`。
形式化陈述：symm_bijective : Function.Bijective (Homotopy.symm : Homotopy p₀ p₁ -> Hom
otopy p₁ p₀)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `Path.Homotopy.symm_symm`：symm_symm (F : Homotopy p₀ p₁) : F.symm.symm = 
F
-/
theorem symm_bijective : Function.Bijective (Homotopy.symm : Homotopy p₀ p₁ → Homotopy p₁ p₀) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/--
Given `Homotopy p₀ p₁` and `Homotopy p₁ p₂`, we can define a `Homotopy p₀ p₂` by putting the first
homotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
/-
**Path.Homotopy.trans** 是 Mathlib 中的一个定义，位于命名空间 `Path.Homotopy`。
形式化陈述：trans (F : Homotopy p₀ p₁) (G : Homotopy p₁ p₂) : Homotopy p₀ p₂
参数：F : Homotopy p₀ p₁；G : Homotopy p₁ p₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `Homotopy p₀ p₁` and `Homotopy p₁ p₂`, we can define a `Homotopy p₀ p₂` by
 putting the first
homotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans (F : Homotopy p₀ p₁) (G : Homotopy p₁ p₂) : Homotopy p₀ p₂ :=
  ContinuousMap.HomotopyRel.trans F G
/-
**Path.Homotopy.trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopy`。
形式化陈述：trans_apply (F : Homotopy p₀ p₁) (G : Homotopy p₁ p₂) (x : I × I) : (F.tra
ns G) x = if h : (x.1 : Real) <= 1 / 2 then F (⟨2 * x.1, (unitInterval.mul_pos_m
em_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2) else G (⟨2 * x.1 - 1, unitInterval.two
_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2)
参数：F : Homotopy p₀ p₁；G : Homotopy p₁ p₂；x : I × I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.HomotopyRel.trans_apply`：trans_apply (F : HomotopyRel f₀ f
₁ S) (G : HomotopyRel f₁ f₂ S) (x : I × X) : (F.trans G) x = if h : (x.1 : Real)
 <= 1 / 2 then F (⟨2 * x.1,…
-/
theorem trans_apply (F : Homotopy p₀ p₁) (G : Homotopy p₁ p₂) (x : I × I) :
    (F.trans G) x =
      if h : (x.1 : ℝ) ≤ 1 / 2 then
        F (⟨2 * x.1, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2)
      else
        G (⟨2 * x.1 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
  ContinuousMap.HomotopyRel.trans_apply _ _ _
/-
**Path.Homotopy.symm_trans** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopy`。
形式化陈述：symm_trans (F : Homotopy p₀ p₁) (G : Homotopy p₁ p₂) : (F.trans G).symm = 
G.symm.trans F.symm
参数：F : Homotopy p₀ p₁；G : Homotopy p₁ p₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.HomotopyRel.symm_trans`：symm_trans (F : HomotopyRel f₀ f₁ 
S) (G : HomotopyRel f₁ f₂ S) : (F.trans G).symm = G.symm.trans F.symm
-/
theorem symm_trans (F : Homotopy p₀ p₁) (G : Homotopy p₁ p₂) :
    (F.trans G).symm = G.symm.trans F.symm :=
  ContinuousMap.HomotopyRel.symm_trans _ _

/-- Casting a `Homotopy p₀ p₁` to a `Homotopy q₀ q₁` where `p₀ = q₀` and `p₁ = q₁`. -/
@[simps!]
/-
**Path.Homotopy.cast** 是 Mathlib 中的一个定义，位于命名空间 `Path.Homotopy`。
形式化陈述：cast {p₀ p₁ q₀ q₁ : Path x₀ x₁} (F : Homotopy p₀ p₁) (h₀ : p₀ = q₀) (h₁ : 
p₁ = q₁) : Homotopy q₀ q₁
参数：F : Homotopy p₀ p₁；h₀ : p₀ = q₀；h₁ : p₁ = q₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Casting a `Homotopy p₀ p₁` to a `Homotopy q₀ q₁` where `p₀ = q₀` and `p₁ = q₁`.
-/
def cast {p₀ p₁ q₀ q₁ : Path x₀ x₁} (F : Homotopy p₀ p₁) (h₀ : p₀ = q₀) (h₁ : p₁ = q₁) :
    Homotopy q₀ q₁ :=
  ContinuousMap.HomotopyRel.cast F (congr_arg _ h₀) (congr_arg _ h₁)

/-- If paths `p` and `q` are homotopic as paths `x ⟶ y`,
then they are homotopic as paths `x' ⟶ y'`, where `x' = x` and `y' = y`. -/
@[simp]
/-
**Path.Homotopy.pathCast** 是 Mathlib 中的一个定义，位于命名空间 `Path.Homotopy`。
形式化陈述：pathCast {x x' y y' : X} {p q : Path x y} (F : p.Homotopy q) (hx : x' = x)
 (hy : y' = y) : (p.cast hx hy).Homotopy (q.cast hx hy)
参数：F : p.Homotopy q；hx : x' = x；hy : y' = y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If paths `p` and `q` are homotopic as paths `x ⟶ y`,
then they are homotopic as paths `x' ⟶ y'`, where `x' = x` and `y' = y`.
-/
def pathCast {x x' y y' : X} {p q : Path x y} (F : p.Homotopy q) (hx : x' = x) (hy : y' = y) :
    (p.cast hx hy).Homotopy (q.cast hx hy) :=
  F

end

section

variable {p₀ q₀ : Path x₀ x₁} {p₁ q₁ : Path x₁ x₂}

/-- Suppose `p₀` and `q₀` are paths from `x₀` to `x₁`, `p₁` and `q₁` are paths from `x₁` to `x₂`.
Furthermore, suppose `F : Homotopy p₀ q₀` and `G : Homotopy p₁ q₁`. Then we can define a homotopy
from `p₀.trans p₁` to `q₀.trans q₁`.
-/
/-
**Path.Homotopy.hcomp** 是 Mathlib 中的一个定义，位于命名空间 `Path.Homotopy`。
形式化陈述：hcomp (F : Homotopy p₀ q₀) (G : Homotopy p₁ q₁) : Homotopy (p₀.trans p₁) (
q₀.trans q₁) where toFun x
参数：F : Homotopy p₀ q₀；G : Homotopy p₁ q₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Suppose `p₀` and `q₀` are paths from `x₀` to `x₁`, `p₁` and `q₁` are paths from 
`x₁` to `x₂`.
Furthermore, suppose `F : Homotopy p₀ q₀` and `G : Homotopy p₁ q₁`. Then we can 
define a homotopy
from `p₀.trans p₁` to `q₀.trans q₁`.
-/
def hcomp (F : Homotopy p₀ q₀) (G : Homotopy p₁ q₁) : Homotopy (p₀.trans p₁) (q₀.trans q₁) where
  toFun x :=
    if (x.2 : ℝ) ≤ 1 / 2 then (F.eval x.1).extend (2 * x.2) else (G.eval x.1).extend (2 * x.2 - 1)
  continuous_toFun := continuous_if_le (continuous_induced_dom.comp continuous_snd) continuous_const
    (F.toHomotopy.continuous.comp (by fun_prop)).continuousOn
    (G.toHomotopy.continuous.comp (by fun_prop)).continuousOn fun x hx ↦ by norm_num [hx]
  map_zero_left x := by simp [Path.trans]
  map_one_left x := by simp [Path.trans]
  prop' x t ht := by
    rcases ht with ht | ht
    · norm_num [ht]
    · rw [Set.mem_singleton_iff] at ht
      norm_num [ht]
/-
**Path.Homotopy.hcomp_apply** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopy`。
形式化陈述：hcomp_apply (F : Homotopy p₀ q₀) (G : Homotopy p₁ q₁) (x : I × I) : F.hcom
p G x = if h : (x.2 : Real) <= 1 / 2 then F.eval x.1 ⟨2 * x.2, (unitInterval.mul
_pos_mem_iff zero_lt_two).2 ⟨x.2.2.1, h⟩⟩ else G.eval x.1 ⟨2 * x.2 - 1, unitInte
rval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.2.2.2⟩⟩
参数：F : Homotopy p₀ q₀；G : Homotopy p₁ q₁；x : I × I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `unitInterval.mul_pos_mem_iff`：mul_pos_mem_iff {a t : Real} (ha : 0 < a) 
: a * t in I ↔ t in Set.Icc (0 : Real) (1 / a)
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `unitInterval.two_mul_sub_one_mem_iff`：two_mul_sub_one_mem_iff {t : Real}
 : 2 * t - 1 in I ↔ t in Set.Icc (1 / 2 : Real) 1
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Path.extend_apply`：extend_apply {a b : X} (γ : Path a b) {t : Real} (ht 
: t in (Icc 0 1 : Set Real)) : γ.extend t = γ ⟨t, ht⟩
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem hcomp_apply (F : Homotopy p₀ q₀) (G : Homotopy p₁ q₁) (x : I × I) :
    F.hcomp G x =
      if h : (x.2 : ℝ) ≤ 1 / 2 then
        F.eval x.1 ⟨2 * x.2, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨x.2.2.1, h⟩⟩
      else
        G.eval x.1
          ⟨2 * x.2 - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.2.2.2⟩⟩ :=
  show ite _ _ _ = _ by split_ifs <;> exact Path.extend_apply _ _
/-
**Path.Homotopy.hcomp_half** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopy`。
形式化陈述：hcomp_half (F : Homotopy p₀ q₀) (G : Homotopy p₁ q₁) (t : I) : F.hcomp G (
t, ⟨1 / 2, by norm_num, by norm_num⟩) = x₁
参数：F : Homotopy p₀ q₀；G : Homotopy p₁ q₁；t : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Mathlib.Meta.NormNum.isRat_le_true`：isRat_le_true [Ring α] [LinearOrder 
α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Int} -> {da db : Nat} -> IsRa
t a na da -> IsRat b nb …
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n d → Mathlib.Meta.NormNum.I
sRat a (Int.ofNat n) d
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_eq`：∀ {α : Type u} [inst : AddMonoidWithOn
e α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsNat a n → ↑n = a' → a = a'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Meta.NormNum.isNat_le_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] {a b : α} {a' b' : ℕ},   Mathlib.Me
ta.NormNum.IsNat a a' → …
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isNat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n 1 → Mathlib.Meta.NormNum
.IsNat a n
· 使用定理 `Path.extend_apply`：extend_apply {a b : X} (γ : Path a b) {t : Real} (ht 
: t in (Icc 0 1 : Set Real)) : γ.extend t = γ ⟨t, ht⟩
· 使用定理 `Path.target`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ :
 Path x y), γ 1 = y
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_sub`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HSub.hSub →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Path.source`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ :
 Path x y), γ 0 = x
（共 32 条，此处仅展示前 30 条）
-/
theorem hcomp_half (F : Homotopy p₀ q₀) (G : Homotopy p₁ q₁) (t : I) :
    F.hcomp G (t, ⟨1 / 2, by norm_num, by norm_num⟩) = x₁ :=
  show ite _ _ _ = _ by norm_num

end

/--
Suppose `p` is a path, then we have a homotopy from `p` to `p.reparam f` by the convexity of `I`.
-/
/-
**Path.Homotopy.reparam** 是 Mathlib 中的一个定义，位于命名空间 `Path.Homotopy`。
形式化陈述：reparam (p : Path x₀ x₁) (f : I -> I) (hf : Continuous f) (hf₀ : f 0 = 0) 
(hf₁ : f 1 = 1) : Homotopy p (p.reparam f hf hf₀ hf₁) where toFun x
参数：p : Path x₀ x₁；f : I -> I；hf : Continuous f；hf₀ : f 0 = 0；hf₁ : f 1 = 1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Suppose `p` is a path, then we have a homotopy from `p` to `p.reparam f` by the 
convexity of `I`.
-/
def reparam (p : Path x₀ x₁) (f : I → I) (hf : Continuous f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    Homotopy p (p.reparam f hf hf₀ hf₁) where
  toFun x := p ⟨σ x.1 * x.2 + x.1 * f x.2,
    show (σ x.1 : ℝ) • (x.2 : ℝ) + (x.1 : ℝ) • (f x.2 : ℝ) ∈ I from
      convex_Icc _ _ x.2.2 (f x.2).2 (by unit_interval) (by unit_interval) (by simp)⟩
  map_zero_left x := by norm_num
  map_one_left x := by norm_num
  prop' t x hx := by
    rcases hx with hx | hx
    · rw [hx]
      simp [hf₀]
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      simp [hf₁]
  continuous_toFun := by fun_prop

/-- Suppose `F : Homotopy p q`. Then we have a `Homotopy p.symm q.symm` by reversing the second
argument.
-/
@[simps]
/-
**Path.Homotopy.symm** 是 Mathlib 中的一个定义，位于命名空间 `Path.Homotopy`。
形式化陈述：symm (F : Homotopy p₀ p₁) : Homotopy p₁ p₀
参数：F : Homotopy p₀ p₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Suppose `F : Homotopy p q`. Then we have a `Homotopy p.symm q.symm` by reversing
 the second
argument.
-/
def symm₂ {p q : Path x₀ x₁} (F : p.Homotopy q) : p.symm.Homotopy q.symm where
  toFun x := F ⟨x.1, σ x.2⟩
  map_zero_left := by simp [Path.symm]
  map_one_left := by simp [Path.symm]
  prop' t x hx := by
    rcases hx with hx | hx
    · rw [hx]
      simp
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      simp

/--
Given `F : Homotopy p q`, and `f : C(X, Y)`, we can define a homotopy from `p.map f.continuous` to
`q.map f.continuous`.
-/
@[simps]
/-
**Path.Homotopy.map** 是 Mathlib 中的一个定义，位于命名空间 `Path.Homotopy`。
形式化陈述：map {p q : Path x₀ x₁} (F : p.Homotopy q) (f : C(X, Y)) : Homotopy (p.map 
f.continuous) (q.map f.continuous) where toFun
参数：F : p.Homotopy q；f : C(X, Y)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f

--- 原说明 ---
Given `F : Homotopy p q`, and `f : C(X, Y)`, we can define a homotopy from `p.ma
p f.continuous` to
`q.map f.continuous`.
-/
def map {p q : Path x₀ x₁} (F : p.Homotopy q) (f : C(X, Y)) :
    Homotopy (p.map f.continuous) (q.map f.continuous) where
  toFun := f ∘ F
  map_zero_left := by simp
  map_one_left := by simp
  prop' t x hx := by
    rcases hx with hx | hx
    · simp [hx]
    · rw [Set.mem_singleton_iff] at hx
      simp [hx]

end Homotopy

/-- Two paths `p₀` and `p₁` are `Path.Homotopic` if there exists a `Homotopy` between them.
-/
/-
**Path.Homotopic** 是 Mathlib 中的一个定义，位于命名空间 `Path`。
形式化陈述：Homotopic (p₀ p₁ : Path x₀ x₁) : Prop
参数：p₀ p₁ : Path x₀ x₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two paths `p₀` and `p₁` are `Path.Homotopic` if there exists a `Homotopy` betwee
n them.
-/
def Homotopic (p₀ p₁ : Path x₀ x₁) : Prop :=
  Nonempty (p₀.Homotopy p₁)

namespace Homotopic

@[refl]
/-
**Path.Homotopic.refl** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic`。
形式化陈述：refl (p : Path x₀ x₁) : p.Homotopic p
参数：p : Path x₀ x₁。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl (p : Path x₀ x₁) : p.Homotopic p :=
  ⟨Homotopy.refl p⟩

@[symm]
/-
**Path.Homotopic.symm** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic`。
形式化陈述：symm ⦃p₀ p₁ : Path x₀ x₁⦄ (h : p₀.Homotopic p₁) : p₁.Homotopic p₀
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
-/
theorem symm ⦃p₀ p₁ : Path x₀ x₁⦄ (h : p₀.Homotopic p₁) : p₁.Homotopic p₀ :=
  h.map Homotopy.symm
/-
**Path.Homotopic.symm** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic`。
形式化陈述：symm ⦃p₀ p₁ : Path x₀ x₁⦄ (h : p₀.Homotopic p₁) : p₁.Homotopic p₀
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
-/
theorem symm₂ {p q : Path x₀ x₁} (h : p.Homotopic q) : p.symm.Homotopic q.symm :=
  h.map Homotopy.symm₂

@[trans]
/-
**Path.Homotopic.trans** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic`。
形式化陈述：trans ⦃p₀ p₁ p₂ : Path x₀ x₁⦄ (h₀ : p₀.Homotopic p₁) (h₁ : p₁.Homotopic p₂
) : p₀.Homotopic p₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map2`：∀ {α : Sort u_3} {β : Sort u_4} {γ : Sort u_5} (f : α → β
 → γ), Nonempty α → Nonempty β → Nonempty γ
-/
theorem trans ⦃p₀ p₁ p₂ : Path x₀ x₁⦄ (h₀ : p₀.Homotopic p₁) (h₁ : p₁.Homotopic p₂) :
    p₀.Homotopic p₂ :=
  h₀.map2 Homotopy.trans h₁
/-
**Path.Homotopic.equivalence** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic`。
形式化陈述：equivalence : Equivalence (@Homotopic X _ x₀ x₁)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.Homotopic.refl`：refl (p : Path x₀ x₁) : p.Homotopic p
· 使用定理 `Path.Homotopic.symm`：symm ⦃p₀ p₁ : Path x₀ x₁⦄ (h : p₀.Homotopic p₁) : p
₁.Homotopic p₀
· 使用定理 `Path.Homotopic.trans`：trans ⦃p₀ p₁ p₂ : Path x₀ x₁⦄ (h₀ : p₀.Homotopic p
₁) (h₁ : p₁.Homotopic p₂) : p₀.Homotopic p₂
-/
theorem equivalence : Equivalence (@Homotopic X _ x₀ x₁) :=
  ⟨refl, (symm ·), (trans · ·)⟩
/-
**Path.Homotopic.** 是 Mathlib 中的一个实例，位于命名空间 `Path.Homotopic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsEquiv (Path x₀ x₁) Homotopic where
  refl := refl
  symm := symm
  trans := trans

nonrec theorem map {p q : Path x₀ x₁} (h : p.Homotopic q) (f : C(X, Y)) :
    Homotopic (p.map f.continuous) (q.map f.continuous) :=
  h.map fun F => F.map f
/-
**Path.Homotopic.hcomp** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic`。
形式化陈述：hcomp {p₀ p₁ : Path x₀ x₁} {q₀ q₁ : Path x₁ x₂} (hp : p₀.Homotopic p₁) (hq
 : q₀.Homotopic q₁) : (p₀.trans q₀).Homotopic (p₁.trans q₁)
参数：hp : p₀.Homotopic p₁；hq : q₀.Homotopic q₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map2`：∀ {α : Sort u_3} {β : Sort u_4} {γ : Sort u_5} (f : α → β
 → γ), Nonempty α → Nonempty β → Nonempty γ
-/
theorem hcomp {p₀ p₁ : Path x₀ x₁} {q₀ q₁ : Path x₁ x₂} (hp : p₀.Homotopic p₁)
    (hq : q₀.Homotopic q₁) : (p₀.trans q₀).Homotopic (p₁.trans q₁) :=
  hp.map2 Homotopy.hcomp hq

/-- If paths `p` and `q` are homotopic as paths `x ⟶ y`,
then they are homotopic as paths `x' ⟶ y'`, where `x' = x` and `y' = y`. -/
/-
**Path.Homotopic.pathCast** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic`。
形式化陈述：pathCast {p q : Path x₀ x₁} (hpq : p.Homotopic q) (hsource : x₂ = x₀) (hta
rget : x₃ = x₁) : (p.cast hsource htarget).Homotopic (q.cast hsource htarget)
参数：hpq : p.Homotopic q；hsource : x₂ = x₀；htarget : x₃ = x₁。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If paths `p` and `q` are homotopic as paths `x ⟶ y`,
then they are homotopic as paths `x' ⟶ y'`, where `x' = x` and `y' = y`.
-/
theorem pathCast {p q : Path x₀ x₁} (hpq : p.Homotopic q) (hsource : x₂ = x₀) (htarget : x₃ = x₁) :
    (p.cast hsource htarget).Homotopic (q.cast hsource htarget) :=
  hpq

/--
The setoid on `Path`s defined by the equivalence relation `Path.Homotopic`. That is, two paths are
equivalent if there is a `Homotopy` between them.
-/
@[instance_reducible]
/-
**Path.Homotopic.setoid** 是 Mathlib 中的一个定义，位于命名空间 `Path.Homotopic`。
形式化陈述：{X : Type u} → [inst : TopologicalSpace X] → (x₀ x₁ : X) → Setoid (Path x₀
 x₁)
参数：x₀ x₁ : X；Path x₀ x₁。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Path.Homotopic.equivalence`：equivalence : Equivalence (@Homotopic X _ x₀
 x₁)

--- 原说明 ---
The setoid on `Path`s defined by the equivalence relation `Path.Homotopic`. That
 is, two paths are
equivalent if there is a `Homotopy` between them.
-/
protected def setoid (x₀ x₁ : X) : Setoid (Path x₀ x₁) :=
  ⟨Homotopic, equivalence⟩

/-- The quotient on `Path x₀ x₁` by the equivalence relation `Path.Homotopic`.
-/
/-
**Path.Homotopic.Quotient** 是 Mathlib 中的一个定义，位于命名空间 `Path.Homotopic`。
形式化陈述：{X : Type u} → [TopologicalSpace X] → X → X → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quotient on `Path x₀ x₁` by the equivalence relation `Path.Homotopic`.
-/
protected def Quotient (x₀ x₁ : X) :=
  Quotient (Homotopic.setoid x₀ x₁)

attribute [local instance] Homotopic.setoid
/-
**Path.Homotopic.** 是 Mathlib 中的一个实例，位于命名空间 `Path.Homotopic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Homotopic.Quotient () ()) :=
  ⟨Quotient.mk' <| Path.refl ()⟩

namespace Quotient

/-- The canonical map from `Path x₀ x₁` to `Path.Homotopic.Quotient x₀ x₁`. -/
/-
**Path.Homotopic.Quotient.mk** 是 Mathlib 中的一个定义，位于命名空间 `Path.Homotopic.Quotient`
。
形式化陈述：mk (p : Path x₀ x₁) : Path.Homotopic.Quotient x₀ x₁
参数：p : Path x₀ x₁。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)

--- 原说明 ---
The canonical map from `Path x₀ x₁` to `Path.Homotopic.Quotient x₀ x₁`.
-/
def mk (p : Path x₀ x₁) : Path.Homotopic.Quotient x₀ x₁ :=
  Quotient.mk' p
/-
**Path.Homotopic.Quotient.mk_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopi
c.Quotient`。
形式化陈述：mk_surjective : Function.Surjective (@mk X _ x₀ x₁)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk'_surjective`：∀ {α : Sort u_1} [s : Setoid α], Function.Surje
ctive Quotient.mk'
-/
theorem mk_surjective : Function.Surjective (@mk X _ x₀ x₁) :=
  Quotient.mk'_surjective

/-- `Path.Homotopic.Quotient.mk` is the simp normal form. -/
/-
**Path.Homotopic.Quotient.mk'_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic.Qu
otient`。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] {x₀ x₁ : X} (p : Path x₀ x₁), Q
uotient.mk' p = Path.Homotopic.Quotient.mk p
参数：p : Path x₀ x₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)

--- 原说明 ---
`Path.Homotopic.Quotient.mk` is the simp normal form.
-/
@[simp] theorem mk'_eq_mk (p : Path x₀ x₁) : Quotient.mk' p = mk p := rfl
/-
**Path.Homotopic.Quotient.mk''_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic.Q
uotient`。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] {x₀ x₁ : X} (p : Path x₀ x₁), Q
uotient.mk'' p = Path.Homotopic.Quotient.mk p
参数：p : Path x₀ x₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)

--- 原说明 ---
`Path.Homotopic.Quotient.mk` is the simp normal form.
-/
@[simp] theorem mk''_eq_mk (p : Path x₀ x₁) : Quotient.mk'' p = mk p := rfl
/-
**Path.Homotopic.Quotient.exact** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic.Quotie
nt`。
形式化陈述：exact {p q : Path x₀ x₁} (h : Quotient.mk p = Quotient.mk q) : Homotopic p
 q
参数：h : Quotient.mk p = Quotient.mk q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.exact`：∀ {α : Sort u} {s : Setoid α} {a b : α}, ⟦a⟧ = ⟦b⟧ → a ≈
 b

--- 原说明 ---
`Path.Homotopic.Quotient.mk` is the simp normal form.
-/
theorem exact {p q : Path x₀ x₁} (h : Quotient.mk p = Quotient.mk q) :
    Homotopic p q := by
  exact _root_.Quotient.exact h
/-
**Path.Homotopic.Quotient.eq** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic.Quotient`
。
形式化陈述：eq {p q : Path x₀ x₁} : mk p = mk q ↔ Homotopic p q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y
-/
theorem eq {p q : Path x₀ x₁} : mk p = mk q ↔ Homotopic p q :=
  _root_.Quotient.eq

/--
A reasoning principle for quotients that allows proofs about quotients to assume that all values are
constructed with `Quotient.mk`.
-/
@[induction_eliminator]
/-
**Path.Homotopic.Quotient.ind** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic.Quotient
`。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] {x y : X} {motive : Path.Homoto
pic.Quotient x y → Prop},   (∀ (a : Path x y), motive (Path.Homotopic.Quotient.m
k a)) → ∀ (q : Path.Homotopic.Quotient x y), motive q
参数：∀ (a : Path x y), motive (Path.Homotopic.Quotient.mk a)；q : Path.Homotopic.Qu
otient x y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A reasoning principle for quotients that allows proofs about quotients to assume
 that all values are
constructed with `Quotient.mk`.
-/
protected theorem ind {x y : X} {motive : Homotopic.Quotient x y → Prop} :
    (mk : (a : Path x y) → motive (Quotient.mk a)) → (q : Homotopic.Quotient x y) → motive q :=
  Quot.ind

/--
A reasoning principle for quotients that allows proofs about quotients to assume that all values are
constructed with `Quotient.mk`. This is the two-variable version of `ind`.
-/
@[elab_as_elim]
/-
**Path.Homotopic.Quotient.ind** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic.Quotient
`。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] {x y : X} {motive : Path.Homoto
pic.Quotient x y → Prop},   (∀ (a : Path x y), motive (Path.Homotopic.Quotient.m
k a)) → ∀ (q : Path.Homotopic.Quotient x y), motive q
参数：∀ (a : Path x y), motive (Path.Homotopic.Quotient.mk a)；q : Path.Homotopic.Qu
otient x y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A reasoning principle for quotients that allows proofs about quotients to assume
 that all values are
constructed with `Quotient.mk`. This is the two-variable version of `ind`.
-/
protected theorem ind₂ {Y : Type*} [TopologicalSpace Y] {x₀ y₀ : X} {x₁ y₁ : Y}
    {motive : Homotopic.Quotient x₀ y₀ → Path.Homotopic.Quotient x₁ y₁ → Prop}
    (mk : (a : Path x₀ y₀) → (b : Path x₁ y₁) → motive (Quotient.mk a) (Quotient.mk b))
    (q₀ : Homotopic.Quotient x₀ y₀) (q₁ : Path.Homotopic.Quotient x₁ y₁) : motive q₀ q₁ := by
  induction q₀ using Quot.ind with | mk a =>
  induction q₁ using Quot.ind with | mk b =>
  exact mk a b

/-- The constant path homotopy class at a point. This is `Path.refl` descended to the quotient. -/
/-
**Path.Homotopic.Quotient.refl** 是 Mathlib 中的一个定义，位于命名空间 `Path.Homotopic.Quotien
t`。
形式化陈述：refl (x : X) : Path.Homotopic.Quotient x x
参数：x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant path homotopy class at a point. This is `Path.refl` descended to th
e quotient.
-/
def refl (x : X) : Path.Homotopic.Quotient x x :=
  mk (Path.refl x)

@[simp, grind =]
/-
**Path.Homotopic.Quotient.mk_refl** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic.Quot
ient`。
形式化陈述：mk_refl (x : X) : mk (Path.refl x) = refl x
参数：x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_refl (x : X) : mk (Path.refl x) = refl x :=
  rfl

/-- The reverse of a path homotopy class. This is `Path.symm` descended to the quotient. -/
/-
**Path.Homotopic.Quotient.symm** 是 Mathlib 中的一个定义，位于命名空间 `Path.Homotopic.Quotien
t`。
形式化陈述：symm (P : Path.Homotopic.Quotient x₀ x₁) : Path.Homotopic.Quotient x₁ x₀
参数：P : Path.Homotopic.Quotient x₀ x₁。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Path.Homotopic.symm₂`：symm₂ {p q : Path x₀ x₁} (h : p.Homotopic q) : p.s
ymm.Homotopic q.symm

--- 原说明 ---
The reverse of a path homotopy class. This is `Path.symm` descended to the quoti
ent.
-/
def symm (P : Path.Homotopic.Quotient x₀ x₁) : Path.Homotopic.Quotient x₁ x₀ :=
  _root_.Quotient.map Path.symm (fun _ _ h => Homotopic.symm₂ h) P

@[simp, grind =]
/-
**Path.Homotopic.Quotient.mk_symm** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic.Quot
ient`。
形式化陈述：mk_symm (P : Path x₀ x₁) : mk P.symm = symm (mk P)
参数：P : Path x₀ x₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_symm (P : Path x₀ x₁) : mk P.symm = symm (mk P) :=
  rfl

/-- Cast a path homotopy class using equalities of endpoints. -/
/-
**Path.Homotopic.Quotient.cast** 是 Mathlib 中的一个定义，位于命名空间 `Path.Homotopic.Quotien
t`。
形式化陈述：cast {x y : X} (γ : Homotopic.Quotient x y) {x' y'} (hx : x' = x) (hy : y'
 = y) : Homotopic.Quotient x' y'
参数：γ : Homotopic.Quotient x y；hx : x' = x；hy : y' = y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Cast a path homotopy class using equalities of endpoints.
-/
def cast {x y : X} (γ : Homotopic.Quotient x y) {x' y'} (hx : x' = x) (hy : y' = y) :
    Homotopic.Quotient x' y' :=
  _root_.Quotient.map (fun p => p.cast hx hy) (fun _ _ h => h) γ

@[simp, grind =]
/-
**Path.Homotopic.Quotient.mk_cast** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic.Quot
ient`。
形式化陈述：mk_cast {x y : X} (P : Path x y) {x' y'} (hx : x' = x) (hy : y' = y) : mk 
(P.cast hx hy) = (mk P).cast hx hy
参数：P : Path x y；hx : x' = x；hy : y' = y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_cast {x y : X} (P : Path x y) {x' y'} (hx : x' = x) (hy : y' = y) :
    mk (P.cast hx hy) = (mk P).cast hx hy :=
  rfl

@[simp, grind =]
/-
**Path.Homotopic.Quotient.cast_rfl_rfl** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic
.Quotient`。
形式化陈述：cast_rfl_rfl {x y : X} (γ : Homotopic.Quotient x y) : γ.cast rfl rfl = γ
参数：γ : Homotopic.Quotient x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.Homotopic.Quotient.ind`：∀ {X : Type u} [inst : TopologicalSpace X] 
{x y : X} {motive : Path.Homotopic.Quotient x y → Prop},   (∀ (a : Path x y), mo
tive (Path.Homoto…
-/
theorem cast_rfl_rfl {x y : X} (γ : Homotopic.Quotient x y) : γ.cast rfl rfl = γ := by
  induction γ using Quotient.ind with | mk γ =>
  rfl

@[simp, grind =]
/-
**Path.Homotopic.Quotient.cast_cast** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic.Qu
otient`。
形式化陈述：cast_cast {x y : X} (γ : Homotopic.Quotient x y) {x' y'} (hx : x' = x) (hy
 : y' = y) {x'' y''} (hx' : x'' = x') (hy' : y'' = y') : (γ.cast hx hy).cast hx'
 hy' = γ.cast (hx'.trans hx) (hy'.trans hy)
参数：γ : Homotopic.Quotient x y；hx : x' = x；hy : y' = y；hx' : x'' = x'；hy' : y'' =
 y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.Homotopic.Quotient.ind`：∀ {X : Type u} [inst : TopologicalSpace X] 
{x y : X} {motive : Path.Homotopic.Quotient x y → Prop},   (∀ (a : Path x y), mo
tive (Path.Homoto…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem cast_cast {x y : X} (γ : Homotopic.Quotient x y) {x' y'} (hx : x' = x) (hy : y' = y)
    {x'' y''} (hx' : x'' = x') (hy' : y'' = y') :
    (γ.cast hx hy).cast hx' hy' = γ.cast (hx'.trans hx) (hy'.trans hy) := by
  induction γ using Quotient.ind with | mk γ =>
  rfl
/-
**Path.Homotopic.Quotient.cast_heq** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic.Quo
tient`。
形式化陈述：cast_heq {x y x' y' : X} (hx : x' = x) (hy : y' = y) {γ : Homotopic.Quotie
nt x y} : γ.cast hx hy ≍ γ
参数：hx : x' = x；hy : y' = y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Path.Homotopic.Quotient.cast_rfl_rfl`：cast_rfl_rfl {x y : X} (γ : Homoto
pic.Quotient x y) : γ.cast rfl rfl = γ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem cast_heq {x y x' y' : X} (hx : x' = x) (hy : y' = y) {γ : Homotopic.Quotient x y} :
    γ.cast hx hy ≍ γ := by
  cases hx; cases hy; exact heq_of_eq γ.cast_rfl_rfl

/-- The composition of path homotopy classes. This is `Path.trans` descended to the quotient. -/
/-
**Path.Homotopic.Quotient.trans** 是 Mathlib 中的一个定义，位于命名空间 `Path.Homotopic.Quotie
nt`。
形式化陈述：trans (P₀ : Path.Homotopic.Quotient x₀ x₁) (P₁ : Path.Homotopic.Quotient x
₁ x₂) : Path.Homotopic.Quotient x₀ x₂
参数：P₀ : Path.Homotopic.Quotient x₀ x₁；P₁ : Path.Homotopic.Quotient x₁ x₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Path.Homotopic.hcomp`：hcomp {p₀ p₁ : Path x₀ x₁} {q₀ q₁ : Path x₁ x₂} (h
p : p₀.Homotopic p₁) (hq : q₀.Homotopic q₁) : (p₀.trans q₀).Homotopic (p₁.trans 
q₁)

--- 原说明 ---
The composition of path homotopy classes. This is `Path.trans` descended to the 
quotient.
-/
def trans (P₀ : Path.Homotopic.Quotient x₀ x₁) (P₁ : Path.Homotopic.Quotient x₁ x₂) :
    Path.Homotopic.Quotient x₀ x₂ :=
  Quotient.map₂ Path.trans (fun (_ : Path x₀ x₁) _ hp (_ : Path x₁ x₂) _ hq => hcomp hp hq) P₀ P₁

@[simp, grind =]
/-
**Path.Homotopic.Quotient.mk_trans** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic.Quo
tient`。
形式化陈述：mk_trans (P₀ : Path x₀ x₁) (P₁ : Path x₁ x₂) : mk (P₀.trans P₁) = Quotient
.trans (mk P₀) (mk P₁)
参数：P₀ : Path x₀ x₁；P₁ : Path x₁ x₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_trans (P₀ : Path x₀ x₁) (P₁ : Path x₁ x₂) :
    mk (P₀.trans P₁) = Quotient.trans (mk P₀) (mk P₁) :=
  rfl

/-- The image of a path homotopy class `P₀` under a map `f`.
This is `Path.map` descended to the quotient. -/
/-
**Path.Homotopic.Quotient.map** 是 Mathlib 中的一个定义，位于命名空间 `Path.Homotopic.Quotient
`。
形式化陈述：map (P₀ : Path.Homotopic.Quotient x₀ x₁) (f : C(X, Y)) : Path.Homotopic.Qu
otient (f x₀) (f x₁)
参数：P₀ : Path.Homotopic.Quotient x₀ x₁；f : C(X, Y)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `Path.Homotopic.map`：∀ {X : Type u} {Y : Type v} [inst : TopologicalSpace
 X] [inst_1 : TopologicalSpace Y] {x₀ x₁ : X} {p q : Path x₀ x₁},   p.Homotopic 
q → ∀ (f…

--- 原说明 ---
The image of a path homotopy class `P₀` under a map `f`.
This is `Path.map` descended to the quotient.
-/
def map (P₀ : Path.Homotopic.Quotient x₀ x₁) (f : C(X, Y)) :
    Path.Homotopic.Quotient (f x₀) (f x₁) :=
  _root_.Quotient.map
    (fun q : Path x₀ x₁ => q.map f.continuous) (fun _ _ h => Path.Homotopic.map h f) P₀
/-
**Path.Homotopic.Quotient.mk_map** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic.Quoti
ent`。
形式化陈述：mk_map (P₀ : Path x₀ x₁) (f : C(X, Y)) : mk (P₀.map f.continuous) = map (m
k P₀) f
参数：P₀ : Path x₀ x₁；f : C(X, Y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
-/
theorem mk_map (P₀ : Path x₀ x₁) (f : C(X, Y)) : mk (P₀.map f.continuous) = map (mk P₀) f :=
  rfl
/-
**Path.Homotopic.Quotient.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic.Quo
tient`。
形式化陈述：map_comp {Z} [TopologicalSpace Z] {p : Path.Homotopic.Quotient x₀ x₁} {f :
 C(X, Y)} {g : C(Y, Z)} : p.map (g.comp f) = (p.map f).map g
参数：X, Y；Y, Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_comp {Z} [TopologicalSpace Z] {p : Path.Homotopic.Quotient x₀ x₁}
    {f : C(X, Y)} {g : C(Y, Z)} : p.map (g.comp f) = (p.map f).map g := by
  rcases p; rfl
/-
**Path.Homotopic.Quotient.map_cast** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic.Quo
tient`。
形式化陈述：map_cast {x y : X} (p : Homotopic.Quotient x y) {x' y'} {hx : x' = x} {hy 
: y' = y} {f : C(X, Y)} : (p.cast hx hy).map f = (p.map f).cast congr(f $hx) con
gr(f $hy)
参数：p : Homotopic.Quotient x y；X, Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem map_cast {x y : X} (p : Homotopic.Quotient x y) {x' y'} {hx : x' = x} {hy : y' = y}
    {f : C(X, Y)} : (p.cast hx hy).map f = (p.map f).cast congr(f $hx) congr(f $hy) := by
  rcases p; rfl

end Quotient

set_option backward.isDefEq.respectTransparency false in
-- Porting note: we didn't previously need the `α := ...` and `β := ...` hints.
/-
**Path.Homotopic.hpath_hext** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic`。
形式化陈述：hpath_hext {p₁ : Path x₀ x₁} {p₂ : Path x₂ x₃} (hp : forall t, p₁ t = p₂ t
) : HEq (α
参数：hp : forall t, p₁ t = p₂ t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `heq_iff_eq`：∀ {α : Sort u_1} {a b : α}, a ≍ b ↔ a = b
· 使用定理 `Path.ext`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} {γ₁ γ₂ 
: Path x y}, ⇑γ₁ = ⇑γ₂ → γ₁ = γ₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Path.target`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ :
 Path x y), γ 1 = y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Path.source`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ :
 Path x y), γ 0 = x
-/
theorem hpath_hext {p₁ : Path x₀ x₁} {p₂ : Path x₂ x₃} (hp : ∀ t, p₁ t = p₂ t) :
    HEq (α := Path.Homotopic.Quotient _ _) ⟦p₁⟧ (β := Path.Homotopic.Quotient _ _) ⟦p₂⟧ := by
  obtain rfl : x₀ = x₂ := by convert! hp 0 <;> simp
  obtain rfl : x₁ = x₃ := by convert! hp 1 <;> simp
  rw [heq_iff_eq]; congr; ext t; exact hp t

end Homotopic

/-- A path `Path x₀ x₁` generates a homotopy between constant functions `fun _ ↦ x₀` and
`fun _ ↦ x₁`. -/
@[simps!]
/-
**Path.toHomotopyConst** 是 Mathlib 中的一个定义，位于命名空间 `Path`。
形式化陈述：toHomotopyConst (p : Path x₀ x₁) : (ContinuousMap.const Y x₀).Homotopy (Co
ntinuousMap.const Y x₁) where toContinuousMap
参数：p : Path x₀ x₁。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Path.source`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ :
 Path x y), γ 0 = x
· 使用定理 `Path.target`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} (γ :
 Path x y), γ 1 = y

--- 原说明 ---
A path `Path x₀ x₁` generates a homotopy between constant functions `fun _ ↦ x₀`
 and
`fun _ ↦ x₁`.
-/
def toHomotopyConst (p : Path x₀ x₁) :
    (ContinuousMap.const Y x₀).Homotopy (ContinuousMap.const Y x₁) where
  toContinuousMap := p.toContinuousMap.comp ContinuousMap.fst
  map_zero_left _ := p.source
  map_one_left _ := p.target

end Path

/-- Two constant continuous maps with nonempty domain are homotopic if and only if their values are
joined by a path in the codomain. -/
@[simp]
/-
**ContinuousMap.homotopic_const_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMap.homotopic_const_iff [Nonempty Y] : (ContinuousMap.const Y x₀
).Homotopic (ContinuousMap.const Y x₁) ↔ Joined x₀ x₁
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.prodSwap_apply`：∀ {α : Type u_1} {β : Type u_2} [inst : To
pologicalSpace α] [inst_1 : TopologicalSpace β] (x : α × β),   ContinuousMap.pro
dSwap x = (x.2, x.…
· 使用定理 `ContinuousMap.Homotopy.apply_zero`：apply_zero (F : Homotopy f₀ f₁) (x : 
X) : F (0, x) = f₀ x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContinuousMap.Homotopy.apply_one`：apply_one (F : Homotopy f₀ f₁) (x : X)
 : F (1, x) = f₁ x

--- 原说明 ---
Two constant continuous maps with nonempty domain are homotopic if and only if t
heir values are
joined by a path in the codomain.
-/
theorem ContinuousMap.homotopic_const_iff [Nonempty Y] :
    (ContinuousMap.const Y x₀).Homotopic (ContinuousMap.const Y x₁) ↔ Joined x₀ x₁ := by
  inhabit Y
  refine ⟨fun ⟨H⟩ ↦ ⟨⟨(H.toContinuousMap.comp .prodSwap).curry default, ?_, ?_⟩⟩,
    fun ⟨p⟩ ↦ ⟨p.toHomotopyConst⟩⟩ <;> simp

namespace ContinuousMap.Homotopy

/-- Given a homotopy `H : f ∼ g`, get the path traced by the point `x` as it moves from
`f x` to `g x`.
-/
@[simps]
/-
**ContinuousMap.Homotopy.evalAt** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap.Homotop
y`。
形式化陈述：evalAt {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (x : X) : Path (f 
x) (g x) where toFun t
参数：X, Y；H : ContinuousMap.Homotopy f g；x : X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.Homotopy.apply_zero`：apply_zero (F : Homotopy f₀ f₁) (x : 
X) : F (0, x) = f₀ x
· 使用定理 `ContinuousMap.Homotopy.apply_one`：apply_one (F : Homotopy f₀ f₁) (x : X)
 : F (1, x) = f₁ x

--- 原说明 ---
Given a homotopy `H : f ∼ g`, get the path traced by the point `x` as it moves f
rom
`f x` to `g x`.
-/
def evalAt {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (x : X) : Path (f x) (g x) where
  toFun t := H (t, x)
  source' := H.apply_zero x
  target' := H.apply_one x

@[simp]
/-
**ContinuousMap.Homotopy.pathExtend_evalAt** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
Map.Homotopy`。
形式化陈述：pathExtend_evalAt {f g : C(X, Y)} (H : f.Homotopy g) (x : X) : (H.evalAt x
).extend = (fun t => H.extend t x)
参数：X, Y；H : f.Homotopy g；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pathExtend_evalAt {f g : C(X, Y)} (H : f.Homotopy g) (x : X) :
    (H.evalAt x).extend = (fun t ↦ H.extend t x) := rfl

end ContinuousMap.Homotopy

