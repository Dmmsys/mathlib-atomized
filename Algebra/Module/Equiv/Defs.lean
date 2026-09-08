/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro, Anne Baanen,
  Frédéric Dupuis, Heather Macbeth
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# (Semi)linear equivalences

In this file we define

* `LinearEquiv σ M M₂`, `M ≃ₛₗ[σ] M₂`: an invertible semilinear map. Here, `σ` is a `RingHom`
  from `R` to `R₂` and an `e : M ≃ₛₗ[σ] M₂` satisfies `e (c • x) = (σ c) • (e x)`. The plain
  linear version, with `σ` being `RingHom.id R`, is denoted by `M ≃ₗ[R] M₂`, and the
  star-linear version (with `σ` being `starRingEnd`) is denoted by `M ≃ₗ⋆[R] M₂`.

## Implementation notes

To ensure that composition works smoothly for semilinear equivalences, we use the typeclasses
`RingHomCompTriple`, `RingHomInvPair` and `RingHomSurjective` from
`Algebra/Ring/CompTypeclasses`.

The group structure on automorphisms, `LinearEquiv.automorphismGroup`, is provided elsewhere.

## TODO

* Parts of this file have not yet been generalized to semilinear maps

## Tags

linear equiv, linear equivalences, linear isomorphism, linear isomorphic
-/

@[expose] public section

assert_not_exists Field Pi.module

open Function

variable {R R₁ R₂ R₃ R₄ S M M₁ M₂ M₃ M₄ N₁ N₂ : Type*}

section

/-- A linear equivalence is an invertible linear map. -/
/-
**LinearEquiv** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{R : Type u_14} →   {S : Type u_15} →     [inst : Semiring R] →       [ins
t_1 : Semiring S] →         (σ : R →+* S) →           {σ' : S →+* R} →          
   [RingHomInvPair σ σ'] →               [RingHomInvPair σ' σ] →                
 (M : Type u_16) →                   (M₂ : Type u_17) →                     [ins
t_4 : AddCommMonoid M] →                       [inst_5 : AddCommMonoid M₂] → [_r
oot_.Module R M] → [_root_.Module S M₂] → Type (max u_16 u_17)
参数：σ : R →+* S；M : Type u_16；M₂ : Type u_17；max u_16 u_17。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear equivalence is an invertible linear map.
-/
structure LinearEquiv {R : Type*} {S : Type*} [Semiring R] [Semiring S] (σ : R →+* S)
  {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (M : Type*) (M₂ : Type*)
  [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂] extends LinearMap σ M M₂, M ≃+ M₂

attribute [coe] LinearEquiv.toLinearMap

/-- The linear map underlying a linear equivalence. -/
add_decl_doc LinearEquiv.toLinearMap

/-- The additive equivalence of types underlying a linear equivalence. -/
add_decl_doc LinearEquiv.toAddEquiv

/-- The backwards directed function underlying a linear equivalence. -/
add_decl_doc LinearEquiv.invFun

/-- `LinearEquiv.invFun` is a right inverse to the linear equivalence's underlying function. -/
add_decl_doc LinearEquiv.right_inv

/-- `LinearEquiv.invFun` is a left inverse to the linear equivalence's underlying function. -/
add_decl_doc LinearEquiv.left_inv

/-- `M ≃ₛₗ[σ] M₂` denotes the type of linear equivalences between `M` and `M₂` over a
ring homomorphism `σ`. -/
notation:50 M " ≃ₛₗ[" σ "] " M₂ => LinearEquiv σ M M₂

/-- `M ≃ₗ[R] M₂` denotes the type of linear equivalences between `M` and `M₂` over
a plain linear map `M →ₗ M₂`. -/
notation:50 M " ≃ₗ[" R "] " M₂ => LinearEquiv (RingHom.id R) M M₂

/-- `SemilinearEquivClass F σ M M₂` asserts `F` is a type of bundled `σ`-semilinear equivs
`M → M₂`.

See also `LinearEquivClass F R M M₂` for the case where `σ` is the identity map on `R`.

A map `f` between an `R`-module and an `S`-module over a ring homomorphism `σ : R →+* S`
is semilinear if it satisfies the two properties `f (x + y) = f x + f y` and
`f (c • x) = (σ c) • f x`. -/
/-
**SemilinearEquivClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_14) →   {R : outParam (Type u_15)} →     {S : outParam (Type u
_16)} →       [inst : Semiring R] →         [inst_1 : Semiring S] →           (σ
 : outParam (R →+* S)) →             {σ' : outParam (S →+* R)} →               [
RingHomInvPair σ σ'] →                 [RingHomInvPair σ' σ] →                  
 (M : outParam (Type u_17)) →                     (M₂ : outParam (Type u_18)) → 
                      [inst_4 : AddCommMonoid M] →                         [inst
_5 : AddCommMonoid M₂] →                           [_root_.Module R M] → [_root_
.Module S M₂] → [EquivLike F M M₂] → Prop
参数：R →+* S；Type u_17；Type u_18。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SemilinearEquivClass F σ M M₂` asserts `F` is a type of bundled `σ`-semilinear 
equivs
`M → M₂`.

See also `LinearEquivClass F R M M₂` for the case where `σ` is the identity map 
on `R`.

A map `f` between an `R`-module and an `S`-module over a ring homomorphism `σ : 
R →+* S`
is semilinear if it satisfies the two properties `f (x + y) = f x + f y` and
`f (c • x) = (σ c) • f x`.
-/
class SemilinearEquivClass (F : Type*) {R S : outParam Type*} [Semiring R] [Semiring S]
  (σ : outParam <| R →+* S) {σ' : outParam <| S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  (M M₂ : outParam Type*) [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂]
  [EquivLike F M M₂] : Prop
  extends AddEquivClass F M M₂ where
  /-- Applying a semilinear equivalence `f` over `σ` to `r • x` equals `σ r • f x`. -/
  map_smulₛₗ : ∀ (f : F) (r : R) (x : M), f (r • x) = σ r • f x

-- `R, S, σ, σ'` become metavars, but it's OK since they are outparams.

/-- `LinearEquivClass F R M M₂` asserts `F` is a type of bundled `R`-linear equivs `M → M₂`.
This is an abbreviation for `SemilinearEquivClass F (RingHom.id R) M M₂`.
-/
/-
**LinearEquivClass** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LinearEquivClass (F : Type*) (R M M₂ : outParam Type*) [Semiring R] [AddCo
mmMonoid M] [AddCommMonoid M₂] [Module R M] [Module R M₂] [EquivLike F M M₂]
参数：F : Type*；R M M₂ : outParam Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LinearEquivClass F R M M₂` asserts `F` is a type of bundled `R`-linear equivs `
M → M₂`.
This is an abbreviation for `SemilinearEquivClass F (RingHom.id R) M M₂`.
-/
abbrev LinearEquivClass (F : Type*) (R M M₂ : outParam Type*) [Semiring R] [AddCommMonoid M]
    [AddCommMonoid M₂] [Module R M] [Module R M₂] [EquivLike F M M₂] :=
  SemilinearEquivClass F (RingHom.id R) M M₂

end

namespace SemilinearEquivClass

variable (F : Type*) [Semiring R] [Semiring S]
variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂]
variable [Module R M] [Module S M₂] {σ : R →+* S} {σ' : S →+* R}

/-
**SemilinearEquivClass.** 是 Mathlib 中的一个实例，位于命名空间 `SemilinearEquivClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    [EquivLike F M M₂] [s : SemilinearEquivClass F σ M M₂] : SemilinearMapClass F σ M M₂ :=
  { s with }

variable {F}

/-- Reinterpret an element of a type of semilinear equivalences as a semilinear equivalence. -/
@[coe]
/-
**SemilinearEquivClass.semilinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `SemilinearEqui
vClass`。
形式化陈述：semilinearEquiv [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] [EquivLike F M
 M₂] [SemilinearEquivClass F σ M M₂] (f : F) : M ≃ₛₗ[σ] M₂
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SemilinearEquivClass.toAddEquivClass`：∀ {F : Type u_14} {R : outParam (T
ype u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S} 
  {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearMap.map_smul'`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring 
R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [inst_
2 : AddCo…

--- 原说明 ---
Reinterpret an element of a type of semilinear equivalences as a semilinear equi
valence.
-/
def semilinearEquiv [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    [EquivLike F M M₂] [SemilinearEquivClass F σ M M₂] (f : F) : M ≃ₛₗ[σ] M₂ :=
  { (f : M ≃+ M₂), (f : M →ₛₗ[σ] M₂) with }

end SemilinearEquivClass

namespace LinearEquiv

section AddCommMonoid

variable [Semiring R] [Semiring S]

section

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂]
-- See note [implicit instance arguments]
variable {modM : Module R M} {modM₂ : Module S M₂} {σ : R →+* S} {σ' : S →+* R}
variable [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]

/-
**LinearEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `LinearEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe (M ≃ₛₗ[σ] M₂) (M →ₛₗ[σ] M₂) :=
  ⟨toLinearMap⟩

-- This exists for compatibility, previously `≃ₗ[R]` extended `≃` instead of `≃+`.
/-- The equivalence of types underlying a linear equivalence. -/
@[implicit_reducible]
/-
**LinearEquiv.toEquiv** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：toEquiv (e : M ≃ₛₗ[σ] M₂) : M ≃ M₂
参数：e : M ≃ₛₗ[σ] M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence of types underlying a linear equivalence.
-/
def toEquiv (e : M ≃ₛₗ[σ] M₂) : M ≃ M₂ := e.toAddEquiv.toEquiv
/-
**LinearEquiv.toEquiv_injective** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：toEquiv_injective : (toEquiv (modM
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.mk.injEq`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring
 R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPai
r σ σ'] [i…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Equiv.mk.inj`：∀ {α : Sort u_1} {β : Sort u_2} {toFun : α → β} {invFun : 
β → α}   {left_inv : autoParam (Function.LeftInverse invFun toFun) Equiv.left_in
v.…
· 使用定理 `LinearEquiv.left_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring
 R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPai
r σ σ'] [i…
· 使用定理 `LinearEquiv.right_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semirin
g R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPa
ir σ σ'] [i…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem toEquiv_injective :
    (toEquiv (modM := modM) (modM₂ := modM₂) : (M ≃ₛₗ[σ] M₂) → M ≃ M₂).Injective :=
  fun ⟨⟨⟨_, _⟩, _⟩, _, _, _⟩ ⟨⟨⟨_, _⟩, _⟩, _, _, _⟩ h ↦
    (LinearEquiv.mk.injEq _ _ _ _ _ _ _ _).mpr
      ⟨LinearMap.ext (congr_fun (Equiv.mk.inj h).1), (Equiv.mk.inj h).2⟩

@[simp]
/-
**LinearEquiv.toEquiv_inj** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：toEquiv_inj {e₁ e₂ : M ≃ₛₗ[σ] M₂} : e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `LinearEquiv.toEquiv_injective`：toEquiv_injective : (toEquiv (modM
-/
theorem toEquiv_inj {e₁ e₂ : M ≃ₛₗ[σ] M₂} : e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂ :=
  toEquiv_injective.eq_iff
/-
**LinearEquiv.toLinearMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：toLinearMap_injective : Injective (toLinearMap : (M ≃ₛₗ[σ] M₂) -> M ->ₛₗ[σ
] M₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.toEquiv_injective`：toEquiv_injective : (toEquiv (modM
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
-/
theorem toLinearMap_injective : Injective (toLinearMap : (M ≃ₛₗ[σ] M₂) → M →ₛₗ[σ] M₂) :=
  fun _ _ H ↦ toEquiv_injective <| Equiv.ext <| LinearMap.congr_fun H

@[simp, norm_cast]
/-
**LinearEquiv.toLinearMap_inj** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：toLinearMap_inj {e₁ e₂ : M ≃ₛₗ[σ] M₂} : (↑e₁ : M ->ₛₗ[σ] M₂) = e₂ ↔ e₁ = e
₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `LinearEquiv.toLinearMap_injective`：toLinearMap_injective : Injective (to
LinearMap : (M ≃ₛₗ[σ] M₂) -> M ->ₛₗ[σ] M₂)
-/
theorem toLinearMap_inj {e₁ e₂ : M ≃ₛₗ[σ] M₂} : (↑e₁ : M →ₛₗ[σ] M₂) = e₂ ↔ e₁ = e₂ :=
  toLinearMap_injective.eq_iff
/-
**LinearEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `LinearEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EquivLike (M ≃ₛₗ[σ] M₂) M M₂ where
  coe e := e.toFun
  inv := LinearEquiv.invFun
  coe_injective' _ _ h _ := toLinearMap_injective (DFunLike.coe_injective h)
  left_inv := LinearEquiv.left_inv
  right_inv := LinearEquiv.right_inv
/-
**LinearEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `LinearEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SemilinearEquivClass (M ≃ₛₗ[σ] M₂) σ M M₂ where
  map_add := (·.map_add')
  map_smulₛₗ := (·.map_smul')
/-
**LinearEquiv.toLinearMap_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：toLinearMap_eq_coe {e : M ≃ₛₗ[σ] M₂} : e.toLinearMap = SemilinearMapClass.
semilinearMap e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_eq_coe {e : M ≃ₛₗ[σ] M₂} : e.toLinearMap = SemilinearMapClass.semilinearMap e :=
  rfl

@[simp]
/-
**LinearEquiv.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：coe_mk {f invFun left_inv right_inv} : ((⟨f, invFun, left_inv, right_inv⟩ 
: M ≃ₛₗ[σ] M₂) : M -> M₂) = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk {f invFun left_inv right_inv} :
    ((⟨f, invFun, left_inv, right_inv⟩ : M ≃ₛₗ[σ] M₂) : M → M₂) = f := rfl
/-
**LinearEquiv.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：coe_injective : @Injective (M ≃ₛₗ[σ] M₂) (M -> M₂) DFunLike.coe
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem coe_injective : @Injective (M ≃ₛₗ[σ] M₂) (M → M₂) DFunLike.coe :=
  DFunLike.coe_injective

@[simp]
/-
**LinearEquiv._root_.SemilinearEquivClass.semilinearEquiv_apply** 是 Mathlib 中的一个
引理，位于命名空间 `LinearEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.SemilinearEquivClass.semilinearEquiv_apply {F : Type*} [EquivLike F M M₂]
    [SemilinearEquivClass F σ M M₂] (f : F) (x : M) :
    SemilinearEquivClass.semilinearEquiv (M₂ := M₂) f x = f x := rfl

end

section

variable [Semiring R₁] [Semiring R₂] [Semiring R₃] [Semiring R₄]
variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [AddCommMonoid M₄]
variable [AddCommMonoid N₁] [AddCommMonoid N₂]
variable {module_M : Module R M} {module_S_M₂ : Module S M₂} {σ : R →+* S} {σ' : S →+* R}
variable {re₁ : RingHomInvPair σ σ'} {re₂ : RingHomInvPair σ' σ}
variable (e e' : M ≃ₛₗ[σ] M₂)

@[simp, norm_cast]
/-
**LinearEquiv.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：coe_coe : ⇑(e : M ->ₛₗ[σ] M₂) = e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_coe : ⇑(e : M →ₛₗ[σ] M₂) = e :=
  rfl

@[simp]
/-
**LinearEquiv.coe_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：coe_toEquiv : ⇑(e.toEquiv) = e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toEquiv : ⇑(e.toEquiv) = e :=
  rfl

@[simp]
/-
**LinearEquiv.coe_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：coe_toLinearMap : ⇑e.toLinearMap = e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toLinearMap : ⇑e.toLinearMap = e :=
  rfl
/-
**LinearEquiv.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：toFun_eq_coe : e.toFun = e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe : e.toFun = e := by dsimp

section

variable {e e'}

@[ext]
/-
**LinearEquiv.ext** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：ext (h : forall x, e x = e' x) : e = e'
参数：h : forall x, e x = e' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext (h : ∀ x, e x = e' x) : e = e' :=
  DFunLike.ext _ _ h
/-
**LinearEquiv.congr_arg** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M₂ : Type u_9} [inst : Sem
iring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M] [inst_3 : AddCommMon
oid M₂] {module_M : _root_.Module R M}   {module_S_M₂ : _root_.Module S M₂} {σ :
 R →+* S} {σ' : S →+* R} {re₁ : RingHomInvPair σ σ'}   {re₂ : RingHomInvPair σ' 
σ} {e : M ≃ₛₗ[σ] M₂} {x x' : M}, x = x' → e x = e x'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_arg`：∀ {F : Sort u_1} {α : Sort u_2} {β : Sort u_3} [i : 
FunLike F α β] (f : F) {x y : α}, x = y → f x = f y
-/
protected theorem congr_arg {x x'} : x = x' → e x = e x' :=
  DFunLike.congr_arg e
/-
**LinearEquiv.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M₂ : Type u_9} [inst : Sem
iring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M] [inst_3 : AddCommMon
oid M₂] {module_M : _root_.Module R M}   {module_S_M₂ : _root_.Module S M₂} {σ :
 R →+* S} {σ' : S →+* R} {re₁ : RingHomInvPair σ σ'}   {re₂ : RingHomInvPair σ' 
σ} {e e' : M ≃ₛₗ[σ] M₂}, e = e' → ∀ (x : M), e x = e' x
参数：x : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
protected theorem congr_fun (h : e = e') (x : M) : e x = e' x :=
  DFunLike.congr_fun h x

end

section

variable (M R)

/-- The identity map is a linear equivalence. -/
@[refl]
/-
**LinearEquiv.refl** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：refl [Module R M] : M ≃ₗ[R] M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun

--- 原说明 ---
The identity map is a linear equivalence.
-/
def refl [Module R M] : M ≃ₗ[R] M :=
  { LinearMap.id, Equiv.refl M with }

end

@[simp]
/-
**LinearEquiv.refl_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：refl_apply [Module R M] (x : M) : refl R M x = x
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_apply [Module R M] (x : M) : refl R M x = x :=
  rfl

/-- Linear equivalences are symmetric. -/
@[symm, implicit_reducible]
/-
**LinearEquiv.symm** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：symm (e : M ≃ₛₗ[σ] M₂) : M₂ ≃ₛₗ[σ'] M
参数：e : M ≃ₛₗ[σ] M₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.left_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring
 R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPai
r σ σ'] [i…
· 使用定理 `LinearEquiv.right_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semirin
g R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPa
ir σ σ'] [i…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun

--- 原说明 ---
Linear equivalences are symmetric.
-/
def symm (e : M ≃ₛₗ[σ] M₂) : M₂ ≃ₛₗ[σ'] M :=
  { e.toLinearMap.inverse e.invFun e.left_inv e.right_inv,
    e.toEquiv.symm with
    toFun := e.toLinearMap.inverse e.invFun e.left_inv e.right_inv
    invFun := e.toEquiv.symm.invFun
    map_smul' r x := by rw [map_smulₛₗ] }

/-- See Note [custom simps projection] -/
/-
**LinearEquiv.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv.Simps`。
形式化陈述：{R : Type u_14} →   {S : Type u_15} →     [inst : Semiring R] →       [ins
t_1 : Semiring S] →         {σ : R →+* S} →           {σ' : S →+* R} →          
   [inst_2 : RingHomInvPair σ σ'] →               [inst_3 : RingHomInvPair σ' σ]
 →                 {M : Type u_16} →                   {M₂ : Type u_17} →       
              [inst_4 : AddCommMonoid M] →                       [inst_5 : AddCo
mmMonoid M₂] →                         [inst_6 : _root_.Module R M] → [inst_7 : 
_root_.Module S M₂] → (M ≃ₛₗ[σ] M₂) → M → M₂
参数：M ≃ₛₗ[σ] M₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.apply {R : Type*} {S : Type*} [Semiring R] [Semiring S]
    {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    {M : Type*} {M₂ : Type*} [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂]
    (e : M ≃ₛₗ[σ] M₂) : M → M₂ :=
  e

/-- See Note [custom simps projection] -/
/-
**LinearEquiv.Simps.symm_apply** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv.Simps`。
形式化陈述：{R : Type u_14} →   {S : Type u_15} →     [inst : Semiring R] →       [ins
t_1 : Semiring S] →         {σ : R →+* S} →           {σ' : S →+* R} →          
   [inst_2 : RingHomInvPair σ σ'] →               [inst_3 : RingHomInvPair σ' σ]
 →                 {M : Type u_16} →                   {M₂ : Type u_17} →       
              [inst_4 : AddCommMonoid M] →                       [inst_5 : AddCo
mmMonoid M₂] →                         [inst_6 : _root_.Module R M] → [inst_7 : 
_root_.Module S M₂] → (M ≃ₛₗ[σ] M₂) → M₂ → M
参数：M ≃ₛₗ[σ] M₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.symm_apply {R S : Type*} [Semiring R] [Semiring S]
    {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    {M M₂ : Type*} [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂]
    (e : M ≃ₛₗ[σ] M₂) : M₂ → M :=
  e.symm

initialize_simps_projections LinearEquiv (toFun → apply, invFun → symm_apply)

@[simp]
/-
**LinearEquiv.invFun_eq_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：invFun_eq_symm : e.invFun = e.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invFun_eq_symm : e.invFun = e.symm :=
  rfl
/-
**LinearEquiv.coe_toEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：coe_toEquiv_symm : e.toEquiv.symm = e.symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem coe_toEquiv_symm : e.toEquiv.symm = e.symm := rfl

@[simp]
/-
**LinearEquiv.toEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：toEquiv_symm : e.symm.toEquiv = e.toEquiv.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEquiv_symm : e.symm.toEquiv = e.toEquiv.symm :=
  rfl

@[simp]
/-
**LinearEquiv.coe_symm_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：coe_symm_toEquiv : ⇑e.toEquiv.symm = e.symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem coe_symm_toEquiv : ⇑e.toEquiv.symm = e.symm := rfl

variable {module_M₁ : Module R₁ M₁} {module_M₂ : Module R₂ M₂} {module_M₃ : Module R₃ M₃}
variable {module_M₄ : Module R₄ M₄} {module_N₁ : Module R₁ N₁} {module_N₂ : Module R₁ N₂}
variable {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁}
variable {σ₁₃ : R₁ →+* R₃} {σ₃₁ : R₃ →+* R₁} [RingHomInvPair σ₁₃ σ₃₁] [RingHomInvPair σ₃₁ σ₁₃]
variable {σ₁₄ : R₁ →+* R₄} {σ₄₁ : R₄ →+* R₁} [RingHomInvPair σ₁₄ σ₄₁] [RingHomInvPair σ₄₁ σ₁₄]
variable {σ₂₃ : R₂ →+* R₃} {σ₃₂ : R₃ →+* R₂}
variable {σ₂₄ : R₂ →+* R₄} {σ₄₂ : R₄ →+* R₂} [RingHomInvPair σ₂₄ σ₄₂] [RingHomInvPair σ₄₂ σ₂₄]
variable {σ₃₄ : R₃ →+* R₄} {σ₄₃ : R₄ →+* R₃} [RingHomInvPair σ₃₄ σ₄₃] [RingHomInvPair σ₄₃ σ₃₄]
variable {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}
variable {re₂₃ : RingHomInvPair σ₂₃ σ₃₂} {re₃₂ : RingHomInvPair σ₃₂ σ₂₃}
variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁]
variable [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄] [RingHomCompTriple σ₄₂ σ₂₁ σ₄₁]
variable [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄] [RingHomCompTriple σ₄₃ σ₃₁ σ₄₁]
variable [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄] [RingHomCompTriple σ₄₃ σ₃₂ σ₄₂]
variable (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂₃ : M₂ ≃ₛₗ[σ₂₃] M₃)

set_option linter.overlappingInstances false in
/-- Linear equivalences are transitive. -/
-- Note: the `RingHomCompTriple σ₃₂ σ₂₁ σ₃₁` is unused, but is convenient to carry around
-- implicitly for lemmas like `LinearEquiv.self_trans_symm`.
@[trans, nolint unusedArguments]
/-
**LinearEquiv.trans** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：trans [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁] {re₁
₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₃ : RingHomInvPair σ₂₃ σ₃₂} [RingHomInvPair σ₁₃ 
σ₃₁] {re₂₁ : RingHomInvPair σ₂₁ σ₁₂} {re₃₂ : RingHomInvPair σ₃₂ σ₂₃} [RingHomInv
Pair σ₃₁ σ₁₃] (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂₃ : M₂ ≃ₛₗ[σ₂₃] M₃) : M₁ ≃ₛₗ[σ₁₃] M₃
参数：e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂；e₂₃ : M₂ ≃ₛₗ[σ₂₃] M₃。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
-/
def trans
    [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁]
    {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₃ : RingHomInvPair σ₂₃ σ₃₂}
    [RingHomInvPair σ₁₃ σ₃₁] {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}
    {re₃₂ : RingHomInvPair σ₃₂ σ₂₃} [RingHomInvPair σ₃₁ σ₁₃]
    (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂₃ : M₂ ≃ₛₗ[σ₂₃] M₃) : M₁ ≃ₛₗ[σ₁₃] M₃ :=
  { e₂₃.toLinearMap.comp e₁₂.toLinearMap, e₁₂.toEquiv.trans e₂₃.toEquiv with }

/-- `e₁ ≪≫ₗ e₂` denotes the composition of the linear equivalences `e₁` and `e₂`. -/
notation3:80 (name := transNotation) e₁:80 " ≪≫ₗ " e₂:81 =>
  @LinearEquiv.trans _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (RingHom.id _) (RingHom.id _) (RingHom.id _)
    (RingHom.id _) (RingHom.id _) (RingHom.id _) RingHomCompTriple.ids RingHomCompTriple.ids
    RingHomInvPair.ids RingHomInvPair.ids RingHomInvPair.ids RingHomInvPair.ids RingHomInvPair.ids
    RingHomInvPair.ids e₁ e₂

/-- `LinearEquiv.symm` defines an equivalence between `α ≃ₛₗ[σ] β` and `β ≃ₛₗ[σ] α`. -/
@[simps!]
/-
**LinearEquiv.symmEquiv** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：symmEquiv : (M ≃ₛₗ[σ] M₂) ≃ (M₂ ≃ₛₗ[σ'] M) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LinearEquiv.symm` defines an equivalence between `α ≃ₛₗ[σ] β` and `β ≃ₛₗ[σ] α`.
-/
def symmEquiv : (M ≃ₛₗ[σ] M₂) ≃ (M₂ ≃ₛₗ[σ'] M) where
  toFun := .symm
  invFun := .symm

variable {e₁₂} {e₂₃}
/-
**LinearEquiv.coe_toAddEquiv** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：coe_toAddEquiv : e.toAddEquiv = e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toAddEquiv : e.toAddEquiv = e :=
  rfl

@[simp]
/-
**LinearEquiv.coe_addEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `LinearEquiv`。
形式化陈述：coe_addEquiv_apply (x : M) : (e : M ≃+ M₂) x = e x
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemilinearEquivClass.toAddEquivClass`：∀ {F : Type u_14} {R : outParam (T
ype u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S} 
  {σ : outParam (R →+* S)}…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
-/
lemma coe_addEquiv_apply (x : M) : (e : M ≃+ M₂) x = e x :=
  rfl

/-- The two paths coercion can take to an `AddMonoidHom` are equivalent -/
/-
**LinearEquiv.toAddMonoidHom_commutes** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：toAddMonoidHom_commutes : e.toLinearMap.toAddMonoidHom = e.toAddEquiv.toAd
dMonoidHom
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The two paths coercion can take to an `AddMonoidHom` are equivalent
-/
theorem toAddMonoidHom_commutes : e.toLinearMap.toAddMonoidHom = e.toAddEquiv.toAddMonoidHom :=
  rfl
/-
**LinearEquiv.coe_toAddEquiv_symm** 是 Mathlib 中的一个引理，位于命名空间 `LinearEquiv`。
形式化陈述：coe_toAddEquiv_symm : (e₁₂.symm : M₂ ≃+ M₁) = (e₁₂ : M₁ ≃+ M₂).symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemilinearEquivClass.toAddEquivClass`：∀ {F : Type u_14} {R : outParam (T
ype u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S} 
  {σ : outParam (R →+* S)}…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
-/
lemma coe_toAddEquiv_symm : (e₁₂.symm : M₂ ≃+ M₁) = (e₁₂ : M₁ ≃+ M₂).symm :=
  rfl

@[simp]
/-
**LinearEquiv.trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：trans_apply (c : M₁) : (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[σ₁₃] M₃) c = e₂₃ (e₁₂ c)
参数：c : M₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_apply (c : M₁) : (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[σ₁₃] M₃) c = e₂₃ (e₁₂ c) :=
  rfl
/-
**LinearEquiv.coe_trans** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：coe_trans : (e₁₂.trans e₂₃ : M₁ ->ₛₗ[σ₁₃] M₃) = (e₂₃ : M₂ ->ₛₗ[σ₂₃] M₃).co
mp (e₁₂ : M₁ ->ₛₗ[σ₁₂] M₂)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_trans :
    (e₁₂.trans e₂₃ : M₁ →ₛₗ[σ₁₃] M₃) = (e₂₃ : M₂ →ₛₗ[σ₂₃] M₃).comp (e₁₂ : M₁ →ₛₗ[σ₁₂] M₂) :=
  rfl

@[simp]
/-
**LinearEquiv.apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：apply_symm_apply (c : M₂) : e (e.symm c) = c
参数：c : M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.right_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semirin
g R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPa
ir σ σ'] [i…
-/
theorem apply_symm_apply (c : M₂) : e (e.symm c) = c :=
  e.right_inv c

@[simp]
/-
**LinearEquiv.symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：symm_apply_apply (b : M) : e.symm (e b) = b
参数：b : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.left_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring
 R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPai
r σ σ'] [i…
-/
theorem symm_apply_apply (b : M) : e.symm (e b) = b :=
  e.left_inv b
/-
**LinearEquiv.comp_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：comp_symm : e.toLinearMap ∘ₛₗ e.symm.toLinearMap = LinearMap.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
-/
theorem comp_symm : e.toLinearMap ∘ₛₗ e.symm.toLinearMap = LinearMap.id :=
  LinearMap.ext e.apply_symm_apply
/-
**LinearEquiv.symm_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：symm_comp : e.symm.toLinearMap ∘ₛₗ e.toLinearMap = LinearMap.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
-/
theorem symm_comp : e.symm.toLinearMap ∘ₛₗ e.toLinearMap = LinearMap.id :=
  LinearMap.ext e.symm_apply_apply

@[simp]
/-
**LinearEquiv.comp_symm_assoc** 是 Mathlib 中的一个引理，位于命名空间 `LinearEquiv`。
形式化陈述：comp_symm_assoc (f : M₃ ->ₛₗ[σ₃₂] M₂) [RingHomCompTriple σ₃₁ σ₁₂ σ₃₂] : e₁
₂.toLinearMap ∘ₛₗ e₁₂.symm.toLinearMap ∘ₛₗ f = f
参数：f : M₃ ->ₛₗ[σ₃₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_symm_assoc (f : M₃ →ₛₗ[σ₃₂] M₂) [RingHomCompTriple σ₃₁ σ₁₂ σ₃₂] :
    e₁₂.toLinearMap ∘ₛₗ e₁₂.symm.toLinearMap ∘ₛₗ f = f := by ext; simp

@[simp]
/-
**LinearEquiv.symm_comp_assoc** 是 Mathlib 中的一个引理，位于命名空间 `LinearEquiv`。
形式化陈述：symm_comp_assoc (f : M₃ ->ₛₗ[σ₃₁] M₁) [RingHomCompTriple σ₃₁ σ₁₂ σ₃₂] : e₁
₂.symm.toLinearMap ∘ₛₗ e₁₂.toLinearMap ∘ₛₗ f = f
参数：f : M₃ ->ₛₗ[σ₃₁] M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma symm_comp_assoc (f : M₃ →ₛₗ[σ₃₁] M₁) [RingHomCompTriple σ₃₁ σ₁₂ σ₃₂] :
    e₁₂.symm.toLinearMap ∘ₛₗ e₁₂.toLinearMap ∘ₛₗ f = f := by ext; simp

@[simp]
/-
**LinearEquiv.trans_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：trans_symm : (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[σ₁₃] M₃).symm = e₂₃.symm.trans e₁₂.sy
mm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_symm : (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[σ₁₃] M₃).symm = e₂₃.symm.trans e₁₂.symm :=
  rfl
/-
**LinearEquiv.symm_trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：symm_trans_apply (c : M₃) : (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[σ₁₃] M₃).symm c = e₁₂.
symm (e₂₃.symm c)
参数：c : M₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_trans_apply (c : M₃) :
    (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[σ₁₃] M₃).symm c = e₁₂.symm (e₂₃.symm c) :=
  rfl

@[simp]
/-
**LinearEquiv.trans_refl** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：trans_refl : e.trans (refl S M₂) = e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.toEquiv_injective`：toEquiv_injective : (toEquiv (modM
· 使用定理 `Equiv.trans_refl`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.trans (Equi
v.refl β) = e
-/
theorem trans_refl : e.trans (refl S M₂) = e :=
  toEquiv_injective e.toEquiv.trans_refl

@[simp]
/-
**LinearEquiv.refl_trans** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：refl_trans : (refl R M).trans e = e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.toEquiv_injective`：toEquiv_injective : (toEquiv (modM
· 使用定理 `Equiv.refl_trans`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), (Equiv.refl α
).trans e = e
-/
theorem refl_trans : (refl R M).trans e = e :=
  toEquiv_injective e.toEquiv.refl_trans
/-
**LinearEquiv.symm_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：symm_apply_eq {x y} : e.symm x = y ↔ x = e y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
-/
theorem symm_apply_eq {x y} : e.symm x = y ↔ x = e y :=
  e.toEquiv.symm_apply_eq
/-
**LinearEquiv.eq_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：eq_symm_apply {x y} : y = e.symm x ↔ e y = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
-/
theorem eq_symm_apply {x y} : y = e.symm x ↔ e y = x :=
  e.toEquiv.eq_symm_apply
/-
**LinearEquiv.eq_comp_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：eq_comp_symm {α : Type*} (f : M₂ -> α) (g : M₁ -> α) : f = g ∘ e₁₂.symm ↔ 
f ∘ e₁₂ = g
参数：f : M₂ -> α；g : M₁ -> α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.eq_comp_symm`：eq_comp_symm {α β γ} (e : α ≃ β) (f : β -> γ) (g : α
 -> γ) : f = g ∘ e.symm ↔ f ∘ e = g
-/
theorem eq_comp_symm {α : Type*} (f : M₂ → α) (g : M₁ → α) : f = g ∘ e₁₂.symm ↔ f ∘ e₁₂ = g :=
  e₁₂.toEquiv.eq_comp_symm f g
/-
**LinearEquiv.comp_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：comp_symm_eq {α : Type*} (f : M₂ -> α) (g : M₁ -> α) : g ∘ e₁₂.symm = f ↔ 
g = f ∘ e₁₂
参数：f : M₂ -> α；g : M₁ -> α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.comp_symm_eq`：comp_symm_eq {α β γ} (e : α ≃ β) (f : β -> γ) (g : α
 -> γ) : g ∘ e.symm = f ↔ g = f ∘ e
-/
theorem comp_symm_eq {α : Type*} (f : M₂ → α) (g : M₁ → α) : g ∘ e₁₂.symm = f ↔ g = f ∘ e₁₂ :=
  e₁₂.toEquiv.comp_symm_eq f g
/-
**LinearEquiv.eq_symm_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：eq_symm_comp {α : Type*} (f : α -> M₁) (g : α -> M₂) : f = e₁₂.symm ∘ g ↔ 
e₁₂ ∘ f = g
参数：f : α -> M₁；g : α -> M₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.eq_symm_comp`：eq_symm_comp {α β γ} (e : α ≃ β) (f : γ -> α) (g : γ
 -> β) : f = e.symm ∘ g ↔ e ∘ f = g
-/
theorem eq_symm_comp {α : Type*} (f : α → M₁) (g : α → M₂) : f = e₁₂.symm ∘ g ↔ e₁₂ ∘ f = g :=
  e₁₂.toEquiv.eq_symm_comp f g
/-
**LinearEquiv.symm_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：symm_comp_eq {α : Type*} (f : α -> M₁) (g : α -> M₂) : e₁₂.symm ∘ g = f ↔ 
g = e₁₂ ∘ f
参数：f : α -> M₁；g : α -> M₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_comp_eq`：symm_comp_eq {α β γ} (e : α ≃ β) (f : γ -> α) (g : γ
 -> β) : e.symm ∘ g = f ↔ g = e ∘ f
-/
theorem symm_comp_eq {α : Type*} (f : α → M₁) (g : α → M₂) : e₁₂.symm ∘ g = f ↔ g = e₁₂ ∘ f :=
  e₁₂.toEquiv.symm_comp_eq f g

@[simp]
/-
**LinearEquiv.comp_coe** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：comp_coe (f : M₁ ≃ₛₗ[σ₁₂] M₂) (f' : M₂ ≃ₛₗ[σ₂₃] M₃) : (f' : M₂ ->ₛₗ[σ₂₃] M
₃).comp (f : M₁ ->ₛₗ[σ₁₂] M₂) = (f.trans f' : M₁ ≃ₛₗ[σ₁₃] M₃)
参数：f : M₁ ≃ₛₗ[σ₁₂] M₂；f' : M₂ ≃ₛₗ[σ₂₃] M₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_coe (f : M₁ ≃ₛₗ[σ₁₂] M₂) (f' : M₂ ≃ₛₗ[σ₂₃] M₃) :
    (f' : M₂ →ₛₗ[σ₂₃] M₃).comp (f : M₁ →ₛₗ[σ₁₂] M₂) = (f.trans f' : M₁ ≃ₛₗ[σ₁₃] M₃) :=
  rfl
/-
**LinearEquiv.trans_assoc** 是 Mathlib 中的一个引理，位于命名空间 `LinearEquiv`。
形式化陈述：trans_assoc (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂₃ : M₂ ≃ₛₗ[σ₂₃] M₃) (e₃₄ : M₃ ≃ₛₗ[σ₃
₄] M₄) : (e₁₂.trans e₂₃).trans e₃₄ = e₁₂.trans (e₂₃.trans e₃₄)
参数：e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂；e₂₃ : M₂ ≃ₛₗ[σ₂₃] M₃；e₃₄ : M₃ ≃ₛₗ[σ₃₄] M₄。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma trans_assoc (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂₃ : M₂ ≃ₛₗ[σ₂₃] M₃) (e₃₄ : M₃ ≃ₛₗ[σ₃₄] M₄) :
    (e₁₂.trans e₂₃).trans e₃₄ = e₁₂.trans (e₂₃.trans e₃₄) := rfl

variable [RingHomCompTriple σ₂₁ σ₁₃ σ₂₃] [RingHomCompTriple σ₃₁ σ₁₂ σ₃₂]
/-
**LinearEquiv.eq_comp_toLinearMap_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：eq_comp_toLinearMap_symm (f : M₂ ->ₛₗ[σ₂₃] M₃) (g : M₁ ->ₛₗ[σ₁₃] M₃) : f =
 g.comp e₁₂.symm.toLinearMap ↔ f.comp e₁₂.toLinearMap = g
参数：f : M₂ ->ₛₗ[σ₂₃] M₃；g : M₁ ->ₛₗ[σ₁₃] M₃。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
-/
theorem eq_comp_toLinearMap_symm (f : M₂ →ₛₗ[σ₂₃] M₃) (g : M₁ →ₛₗ[σ₁₃] M₃) :
    f = g.comp e₁₂.symm.toLinearMap ↔ f.comp e₁₂.toLinearMap = g := by
  constructor <;> intro H <;> ext
  · simp [H]
  · simp [← H]
/-
**LinearEquiv.comp_toLinearMap_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：comp_toLinearMap_symm_eq (f : M₂ ->ₛₗ[σ₂₃] M₃) (g : M₁ ->ₛₗ[σ₁₃] M₃) : g.c
omp e₁₂.symm.toLinearMap = f ↔ g = f.comp e₁₂.toLinearMap
参数：f : M₂ ->ₛₗ[σ₂₃] M₃；g : M₁ ->ₛₗ[σ₁₃] M₃。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
-/
theorem comp_toLinearMap_symm_eq (f : M₂ →ₛₗ[σ₂₃] M₃) (g : M₁ →ₛₗ[σ₁₃] M₃) :
    g.comp e₁₂.symm.toLinearMap = f ↔ g = f.comp e₁₂.toLinearMap := by
  constructor <;> intro H <;> ext
  · simp [← H]
  · simp [H]
/-
**LinearEquiv.eq_toLinearMap_symm_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：eq_toLinearMap_symm_comp (f : M₃ ->ₛₗ[σ₃₁] M₁) (g : M₃ ->ₛₗ[σ₃₂] M₂) : f =
 e₁₂.symm.toLinearMap.comp g ↔ e₁₂.toLinearMap.comp f = g
参数：f : M₃ ->ₛₗ[σ₃₁] M₁；g : M₃ ->ₛₗ[σ₃₂] M₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用引理 `LinearEquiv.comp_symm_assoc`：comp_symm_assoc (f : M₃ ->ₛₗ[σ₃₂] M₂) [Ring
HomCompTriple σ₃₁ σ₁₂ σ₃₂] : e₁₂.toLinearMap ∘ₛₗ e₁₂.symm.toLinearMap ∘ₛₗ f = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearEquiv.symm_comp_assoc`：symm_comp_assoc (f : M₃ ->ₛₗ[σ₃₁] M₁) [Ring
HomCompTriple σ₃₁ σ₁₂ σ₃₂] : e₁₂.symm.toLinearMap ∘ₛₗ e₁₂.toLinearMap ∘ₛₗ f = f
-/
theorem eq_toLinearMap_symm_comp (f : M₃ →ₛₗ[σ₃₁] M₁) (g : M₃ →ₛₗ[σ₃₂] M₂) :
    f = e₁₂.symm.toLinearMap.comp g ↔ e₁₂.toLinearMap.comp f = g := by
  constructor <;> intro H <;> ext
  · simp [H]
  · simp [← H]
/-
**LinearEquiv.toLinearMap_symm_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：toLinearMap_symm_comp_eq (f : M₃ ->ₛₗ[σ₃₁] M₁) (g : M₃ ->ₛₗ[σ₃₂] M₂) : e₁₂
.symm.toLinearMap.comp g = f ↔ g = e₁₂.toLinearMap.comp f
参数：f : M₃ ->ₛₗ[σ₃₁] M₁；g : M₃ ->ₛₗ[σ₃₂] M₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearEquiv.comp_symm_assoc`：comp_symm_assoc (f : M₃ ->ₛₗ[σ₃₂] M₂) [Ring
HomCompTriple σ₃₁ σ₁₂ σ₃₂] : e₁₂.toLinearMap ∘ₛₗ e₁₂.symm.toLinearMap ∘ₛₗ f = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `LinearEquiv.symm_comp_assoc`：symm_comp_assoc (f : M₃ ->ₛₗ[σ₃₁] M₁) [Ring
HomCompTriple σ₃₁ σ₁₂ σ₃₂] : e₁₂.symm.toLinearMap ∘ₛₗ e₁₂.toLinearMap ∘ₛₗ f = f
-/
theorem toLinearMap_symm_comp_eq (f : M₃ →ₛₗ[σ₃₁] M₁) (g : M₃ →ₛₗ[σ₃₂] M₂) :
    e₁₂.symm.toLinearMap.comp g = f ↔ g = e₁₂.toLinearMap.comp f := by
  constructor <;> intro H <;> ext
  · simp [← H]
  · simp [H]

@[simp]
/-
**LinearEquiv.comp_toLinearMap_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：comp_toLinearMap_eq_iff (f g : M₃ ->ₛₗ[σ₃₁] M₁) : e₁₂.toLinearMap.comp f =
 e₁₂.toLinearMap.comp g ↔ f = g
参数：f g : M₃ ->ₛₗ[σ₃₁] M₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearEquiv.toLinearMap_symm_comp_eq`：toLinearMap_symm_comp_eq (f : M₃ -
>ₛₗ[σ₃₁] M₁) (g : M₃ ->ₛₗ[σ₃₂] M₂) : e₁₂.symm.toLinearMap.comp g = f ↔ g = e₁₂.t
oLinearMap.comp f
· 使用定理 `LinearEquiv.eq_toLinearMap_symm_comp`：eq_toLinearMap_symm_comp (f : M₃ -
>ₛₗ[σ₃₁] M₁) (g : M₃ ->ₛₗ[σ₃₂] M₂) : f = e₁₂.symm.toLinearMap.comp g ↔ e₁₂.toLin
earMap.comp f = g
-/
theorem comp_toLinearMap_eq_iff (f g : M₃ →ₛₗ[σ₃₁] M₁) :
    e₁₂.toLinearMap.comp f = e₁₂.toLinearMap.comp g ↔ f = g := by
  refine ⟨fun h => ?_, congrArg e₁₂.comp⟩
  rw [← (toLinearMap_symm_comp_eq g (e₁₂.toLinearMap.comp f)).mpr h, eq_toLinearMap_symm_comp]

@[simp]
/-
**LinearEquiv.eq_comp_toLinearMap_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：eq_comp_toLinearMap_iff (f g : M₂ ->ₛₗ[σ₂₃] M₃) : f.comp e₁₂.toLinearMap =
 g.comp e₁₂.toLinearMap ↔ f = g
参数：f g : M₂ ->ₛₗ[σ₂₃] M₃。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearEquiv.eq_comp_toLinearMap_symm`：eq_comp_toLinearMap_symm (f : M₂ -
>ₛₗ[σ₂₃] M₃) (g : M₁ ->ₛₗ[σ₁₃] M₃) : f = g.comp e₁₂.symm.toLinearMap ↔ f.comp e₁
₂.toLinearMap = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
theorem eq_comp_toLinearMap_iff (f g : M₂ →ₛₗ[σ₂₃] M₃) :
    f.comp e₁₂.toLinearMap = g.comp e₁₂.toLinearMap ↔ f = g := by
  refine ⟨fun h => ?_, fun a ↦ congrFun (congrArg LinearMap.comp a) e₁₂.toLinearMap⟩
  rw [(eq_comp_toLinearMap_symm g (f.comp e₁₂.toLinearMap)).mpr h.symm, eq_comp_toLinearMap_symm]
/-
**LinearEquiv.comp_symm_cancel_left** 是 Mathlib 中的一个引理，位于命名空间 `LinearEquiv`。
形式化陈述：comp_symm_cancel_left (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₃ ->ₛₗ[σ₃₂] M₂) : e.toLin
earMap ∘ₛₗ (e.symm.toLinearMap ∘ₛₗ f) = f
参数：e : M₁ ≃ₛₗ[σ₁₂] M₂；f : M₃ ->ₛₗ[σ₃₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearEquiv.comp_symm_assoc`：comp_symm_assoc (f : M₃ ->ₛₗ[σ₃₂] M₂) [Ring
HomCompTriple σ₃₁ σ₁₂ σ₃₂] : e₁₂.toLinearMap ∘ₛₗ e₁₂.symm.toLinearMap ∘ₛₗ f = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_symm_cancel_left (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₃ →ₛₗ[σ₃₂] M₂) :
    e.toLinearMap ∘ₛₗ (e.symm.toLinearMap ∘ₛₗ f) = f := by ext; simp
/-
**LinearEquiv.symm_comp_cancel_left** 是 Mathlib 中的一个引理，位于命名空间 `LinearEquiv`。
形式化陈述：symm_comp_cancel_left (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₃ ->ₛₗ[σ₃₁] M₁) : e.symm.
toLinearMap ∘ₛₗ (e.toLinearMap ∘ₛₗ f) = f
参数：e : M₁ ≃ₛₗ[σ₁₂] M₂；f : M₃ ->ₛₗ[σ₃₁] M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearEquiv.symm_comp_assoc`：symm_comp_assoc (f : M₃ ->ₛₗ[σ₃₁] M₁) [Ring
HomCompTriple σ₃₁ σ₁₂ σ₃₂] : e₁₂.symm.toLinearMap ∘ₛₗ e₁₂.toLinearMap ∘ₛₗ f = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma symm_comp_cancel_left (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₃ →ₛₗ[σ₃₁] M₁) :
    e.symm.toLinearMap ∘ₛₗ (e.toLinearMap ∘ₛₗ f) = f := by ext; simp
/-
**LinearEquiv.comp_symm_cancel_right** 是 Mathlib 中的一个引理，位于命名空间 `LinearEquiv`。
形式化陈述：comp_symm_cancel_right (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₂ ->ₛₗ[σ₂₃] M₃) : (f ∘ₛₗ
 e.toLinearMap) ∘ₛₗ e.symm.toLinearMap = f
参数：e : M₁ ≃ₛₗ[σ₁₂] M₂；f : M₂ ->ₛₗ[σ₂₃] M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_symm_cancel_right (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₂ →ₛₗ[σ₂₃] M₃) :
    (f ∘ₛₗ e.toLinearMap) ∘ₛₗ e.symm.toLinearMap = f := by ext; simp
/-
**LinearEquiv.symm_comp_cancel_right** 是 Mathlib 中的一个引理，位于命名空间 `LinearEquiv`。
形式化陈述：symm_comp_cancel_right (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₁ ->ₛₗ[σ₁₃] M₃) : (f ∘ₛₗ
 e.symm.toLinearMap) ∘ₛₗ e.toLinearMap = f
参数：e : M₁ ≃ₛₗ[σ₁₂] M₂；f : M₁ ->ₛₗ[σ₁₃] M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma symm_comp_cancel_right (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₁ →ₛₗ[σ₁₃] M₃) :
    (f ∘ₛₗ e.symm.toLinearMap) ∘ₛₗ e.toLinearMap = f := by ext; simp
/-
**LinearEquiv.trans_symm_cancel_left** 是 Mathlib 中的一个引理，位于命名空间 `LinearEquiv`。
形式化陈述：trans_symm_cancel_left (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₁ ≃ₛₗ[σ₁₃] M₃) : e.trans
 (e.symm.trans f) = f
参数：e : M₁ ≃ₛₗ[σ₁₂] M₂；f : M₁ ≃ₛₗ[σ₁₃] M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma trans_symm_cancel_left (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₁ ≃ₛₗ[σ₁₃] M₃) :
    e.trans (e.symm.trans f) = f := by ext; simp
/-
**LinearEquiv.symm_trans_cancel_left** 是 Mathlib 中的一个引理，位于命名空间 `LinearEquiv`。
形式化陈述：symm_trans_cancel_left (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₂ ≃ₛₗ[σ₂₃] M₃) : e.symm.
trans (e.trans f) = f
参数：e : M₁ ≃ₛₗ[σ₁₂] M₂；f : M₂ ≃ₛₗ[σ₂₃] M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma symm_trans_cancel_left (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₂ ≃ₛₗ[σ₂₃] M₃) :
    e.symm.trans (e.trans f) = f := by ext; simp
/-
**LinearEquiv.trans_symm_cancel_right** 是 Mathlib 中的一个引理，位于命名空间 `LinearEquiv`。
形式化陈述：trans_symm_cancel_right (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₃ ≃ₛₗ[σ₃₁] M₁) : (f.tra
ns e).trans e.symm = f
参数：e : M₁ ≃ₛₗ[σ₁₂] M₂；f : M₃ ≃ₛₗ[σ₃₁] M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma trans_symm_cancel_right (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₃ ≃ₛₗ[σ₃₁] M₁) :
    (f.trans e).trans e.symm = f := by ext; simp
/-
**LinearEquiv.symm_trans_cancel_right** 是 Mathlib 中的一个引理，位于命名空间 `LinearEquiv`。
形式化陈述：symm_trans_cancel_right (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₃ ≃ₛₗ[σ₃₂] M₂) : (f.tra
ns e.symm).trans e = f
参数：e : M₁ ≃ₛₗ[σ₁₂] M₂；f : M₃ ≃ₛₗ[σ₃₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma symm_trans_cancel_right (e : M₁ ≃ₛₗ[σ₁₂] M₂) (f : M₃ ≃ₛₗ[σ₃₂] M₂) :
    (f.trans e.symm).trans e = f := by ext; simp

@[simp]
/-
**LinearEquiv.refl_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：refl_symm [Module R M] : (refl R M).symm = LinearEquiv.refl R M
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_symm [Module R M] : (refl R M).symm = LinearEquiv.refl R M :=
  rfl

@[simp]
/-
**LinearEquiv.self_trans_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：self_trans_symm (f : M₁ ≃ₛₗ[σ₁₂] M₂) : f.trans f.symm = LinearEquiv.refl R
₁ M₁
参数：f : M₁ ≃ₛₗ[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem self_trans_symm (f : M₁ ≃ₛₗ[σ₁₂] M₂) : f.trans f.symm = LinearEquiv.refl R₁ M₁ := by
  ext x
  simp

@[simp]
/-
**LinearEquiv.symm_trans_self** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：symm_trans_self (f : M₁ ≃ₛₗ[σ₁₂] M₂) : f.symm.trans f = LinearEquiv.refl R
₂ M₂
参数：f : M₁ ≃ₛₗ[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem symm_trans_self (f : M₁ ≃ₛₗ[σ₁₂] M₂) : f.symm.trans f = LinearEquiv.refl R₂ M₂ := by
  ext x
  simp

@[simp]
/-
**LinearEquiv.refl_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：refl_toLinearMap [Module R M] : (LinearEquiv.refl R M : M ->ₗ[R] M) = Line
arMap.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_toLinearMap [Module R M] : (LinearEquiv.refl R M : M →ₗ[R] M) = LinearMap.id :=
  rfl

@[simp]
/-
**LinearEquiv.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：mk_coe (f h₁ h₂) : (LinearEquiv.mk e f h₁ h₂ : M ≃ₛₗ[σ] M₂) = e
参数：f h₁ h₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
-/
theorem mk_coe (f h₁ h₂) : (LinearEquiv.mk e f h₁ h₂ : M ≃ₛₗ[σ] M₂) = e :=
  ext fun _ ↦ rfl
/-
**LinearEquiv.map_add** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M₂ : Type u_9} [inst : Sem
iring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M] [inst_3 : AddCommMon
oid M₂] {module_M : _root_.Module R M}   {module_S_M₂ : _root_.Module S M₂} {σ :
 R →+* S} {σ' : S →+* R} {re₁ : RingHomInvPair σ σ'}   {re₂ : RingHomInvPair σ' 
σ} (e : M ≃ₛₗ[σ] M₂) (a b : M), e (a + b) = e a + e b
参数：e : M ≃ₛₗ[σ] M₂；a b : M；a + b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
-/
protected theorem map_add (a b : M) : e (a + b) = e a + e b :=
  map_add e a b
/-
**LinearEquiv.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M₂ : Type u_9} [inst : Sem
iring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M] [inst_3 : AddCommMon
oid M₂] {module_M : _root_.Module R M}   {module_S_M₂ : _root_.Module S M₂} {σ :
 R →+* S} {σ' : S →+* R} {re₁ : RingHomInvPair σ σ'}   {re₂ : RingHomInvPair σ' 
σ} (e : M ≃ₛₗ[σ] M₂), e 0 = 0
参数：e : M ≃ₛₗ[σ] M₂。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
-/
protected theorem map_zero : e 0 = 0 :=
  map_zero e
/-
**LinearEquiv.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：map_smul (e : N₁ ≃ₗ[R₁] N₂) (c : R₁) (x : N₁) : e (c • x) = c • e x
参数：e : N₁ ≃ₗ[R₁] N₂；c : R₁；x : N₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
-/
protected theorem map_smulₛₗ (c : R) (x : M) : e (c • x) = (σ : R → S) c • e x :=
  e.map_smul' c x
/-
**LinearEquiv.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：map_smul (e : N₁ ≃ₗ[R₁] N₂) (c : R₁) (x : N₁) : e (c • x) = c • e x
参数：e : N₁ ≃ₗ[R₁] N₂；c : R₁；x : N₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
-/
theorem map_smul (e : N₁ ≃ₗ[R₁] N₂) (c : R₁) (x : N₁) : e (c • x) = c • e x :=
  map_smulₛₗ e c x
/-
**LinearEquiv.map_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：map_eq_zero_iff {x : M} : e x = 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.map_eq_zero_iff`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZer
oClass M] [inst_1 : AddZeroClass N] (h : M ≃+ N) {x : M}, h x = 0 ↔ x = 0
-/
theorem map_eq_zero_iff {x : M} : e x = 0 ↔ x = 0 :=
  e.toAddEquiv.map_eq_zero_iff
/-
**LinearEquiv.map_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：map_ne_zero_iff {x : M} : e x != 0 ↔ x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.map_ne_zero_iff`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZer
oClass M] [inst_1 : AddZeroClass N] (h : M ≃+ N) {x : M}, h x ≠ 0 ↔ x ≠ 0
-/
theorem map_ne_zero_iff {x : M} : e x ≠ 0 ↔ x ≠ 0 :=
  e.toAddEquiv.map_ne_zero_iff

@[simp]
/-
**LinearEquiv.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：symm_symm (e : M ≃ₛₗ[σ] M₂) : e.symm.symm = e
参数：e : M ≃ₛₗ[σ] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_symm (e : M ≃ₛₗ[σ] M₂) : e.symm.symm = e := rfl
/-
**LinearEquiv.symm_bijective** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：symm_bijective [Module R M] [Module S M₂] [RingHomInvPair σ' σ] [RingHomIn
vPair σ σ'] : Function.Bijective (symm : (M ≃ₛₗ[σ] M₂) -> M₂ ≃ₛₗ[σ'] M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `LinearEquiv.symm_symm`：symm_symm (e : M ≃ₛₗ[σ] M₂) : e.symm.symm = e
-/
theorem symm_bijective [Module R M] [Module S M₂] [RingHomInvPair σ' σ] [RingHomInvPair σ σ'] :
    Function.Bijective (symm : (M ≃ₛₗ[σ] M₂) → M₂ ≃ₛₗ[σ'] M) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
/-
**LinearEquiv.mk_coe'** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：mk_coe' (f h₁ h₂ h₃ h₄) : (LinearEquiv.mk ⟨⟨f, h₁⟩, h₂⟩ (⇑e) h₃ h₄ : M₂ ≃ₛ
ₗ[σ'] M) = e.symm
参数：f h₁ h₂ h₃ h₄。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `LinearEquiv.symm_bijective`：symm_bijective [Module R M] [Module S M₂] [R
ingHomInvPair σ' σ] [RingHomInvPair σ σ'] : Function.Bijective (symm : (M ≃ₛₗ[σ]
 M₂) -> M₂ ≃ₛₗ[σ…
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
-/
theorem mk_coe' (f h₁ h₂ h₃ h₄) :
    (LinearEquiv.mk ⟨⟨f, h₁⟩, h₂⟩ (⇑e) h₃ h₄ : M₂ ≃ₛₗ[σ'] M) = e.symm :=
  symm_bijective.injective <| ext fun _ ↦ rfl

@[simp]
/-
**LinearEquiv.symm_mk** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：symm_mk (toLinearMap invFun h₁ h₂) : dsimp% (mk toLinearMap invFun h₁ h₂ :
 M ≃ₛₗ[σ] M₂).symm = { (mk toLinearMap invFun h₁ h₂ : M ≃ₛₗ[σ] M₂).symm with toF
un
参数：toLinearMap invFun h₁ h₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_mk (toLinearMap invFun h₁ h₂) : dsimp%
    (mk toLinearMap invFun h₁ h₂ : M ≃ₛₗ[σ] M₂).symm =
      { (mk toLinearMap invFun h₁ h₂ : M ≃ₛₗ[σ] M₂).symm with
        toFun := invFun
        invFun := toLinearMap } :=
  rfl

/-- For a more powerful version, see `coe_symm_mk'`. -/
/-
**LinearEquiv.coe_symm_mk** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：coe_symm_mk [Module R M] [Module R M₂] {to_fun inv_fun map_add map_smul le
ft_inv right_inv} : ⇑(⟨⟨⟨to_fun, map_add⟩, map_smul⟩, inv_fun, left_inv, right_i
nv⟩ : M ≃ₗ[R] M₂).symm = inv_fun
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a more powerful version, see `coe_symm_mk'`.
-/
theorem coe_symm_mk [Module R M] [Module R M₂]
    {to_fun inv_fun map_add map_smul left_inv right_inv} :
    ⇑(⟨⟨⟨to_fun, map_add⟩, map_smul⟩, inv_fun, left_inv, right_inv⟩ : M ≃ₗ[R] M₂).symm = inv_fun :=
  rfl

@[simp]
/-
**LinearEquiv.coe_symm_mk'** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：coe_symm_mk' [Module R M] [Module R M₂] {f inv_fun left_inv right_inv} : ⇑
(⟨f, inv_fun, left_inv, right_inv⟩ : M ≃ₗ[R] M₂).symm = inv_fun
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_symm_mk' [Module R M] [Module R M₂]
    {f inv_fun left_inv right_inv} :
    ⇑(⟨f, inv_fun, left_inv, right_inv⟩ : M ≃ₗ[R] M₂).symm = inv_fun := rfl
/-
**LinearEquiv.bijective** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M₂ : Type u_9} [inst : Sem
iring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M] [inst_3 : AddCommMon
oid M₂] {module_M : _root_.Module R M}   {module_S_M₂ : _root_.Module S M₂} {σ :
 R →+* S} {σ' : S →+* R} {re₁ : RingHomInvPair σ σ'}   {re₂ : RingHomInvPair σ' 
σ} (e : M ≃ₛₗ[σ] M₂), Function.Bijective ⇑e
参数：e : M ≃ₛₗ[σ] M₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
protected theorem bijective : Function.Bijective e :=
  e.toEquiv.bijective
/-
**LinearEquiv.injective** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M₂ : Type u_9} [inst : Sem
iring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M] [inst_3 : AddCommMon
oid M₂] {module_M : _root_.Module R M}   {module_S_M₂ : _root_.Module S M₂} {σ :
 R →+* S} {σ' : S →+* R} {re₁ : RingHomInvPair σ σ'}   {re₂ : RingHomInvPair σ' 
σ} (e : M ≃ₛₗ[σ] M₂), Function.Injective ⇑e
参数：e : M ≃ₛₗ[σ] M₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
protected theorem injective : Function.Injective e :=
  e.toEquiv.injective
/-
**LinearEquiv.surjective** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M₂ : Type u_9} [inst : Sem
iring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M] [inst_3 : AddCommMon
oid M₂] {module_M : _root_.Module R M}   {module_S_M₂ : _root_.Module S M₂} {σ :
 R →+* S} {σ' : S →+* R} {re₁ : RingHomInvPair σ σ'}   {re₂ : RingHomInvPair σ' 
σ} (e : M ≃ₛₗ[σ] M₂), Function.Surjective ⇑e
参数：e : M ≃ₛₗ[σ] M₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
protected theorem surjective : Function.Surjective e :=
  e.toEquiv.surjective
/-
**LinearEquiv.image_eq_preimage_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M₂ : Type u_9} [inst : Sem
iring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M] [inst_3 : AddCommMon
oid M₂] {module_M : _root_.Module R M}   {module_S_M₂ : _root_.Module S M₂} {σ :
 R →+* S} {σ' : S →+* R} {re₁ : RingHomInvPair σ σ'}   {re₂ : RingHomInvPair σ' 
σ} (e : M ≃ₛₗ[σ] M₂) (s : Set M), ⇑e '' s = ⇑e.symm ⁻¹' s
参数：e : M ≃ₛₗ[σ] M₂；s : Set M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
-/
protected theorem image_eq_preimage_symm (s : Set M) : e '' s = e.symm ⁻¹' s :=
  e.toEquiv.image_eq_preimage_symm s
/-
**LinearEquiv.image_symm_eq_preimage** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M₂ : Type u_9} [inst : Sem
iring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M] [inst_3 : AddCommMon
oid M₂] {module_M : _root_.Module R M}   {module_S_M₂ : _root_.Module S M₂} {σ :
 R →+* S} {σ' : S →+* R} {re₁ : RingHomInvPair σ σ'}   {re₂ : RingHomInvPair σ' 
σ} (e : M ≃ₛₗ[σ] M₂) (s : Set M₂), ⇑e.symm '' s = ⇑e ⁻¹' s
参数：e : M ≃ₛₗ[σ] M₂；s : Set M₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
protected theorem image_symm_eq_preimage (s : Set M₂) : e.symm '' s = e ⁻¹' s :=
  e.toEquiv.symm.image_eq_preimage_symm s

end

/-- `Equiv.cast (congrArg _ h)` as a linear equiv.

Note that unlike `Equiv.cast`, this takes an equality of indices rather than an equality of types,
to avoid having to deal with an equality of the algebraic structure itself. -/
@[simps!]
/-
**LinearEquiv.cast** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：{R : Type u_1} →   [inst : Semiring R] →     {ι : Type u_14} →       {M : 
ι → Type u_15} →         [inst_1 : (i : ι) → AddCommMonoid (M i)] →           [i
nst_2 : (i : ι) → _root_.Module R (M i)] → {i j : ι} → i = j → M i ≃ₗ[R] M j
参数：i : ι；M i；i : ι；M i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Equiv.cast (congrArg _ h)` as a linear equiv.

Note that unlike `Equiv.cast`, this takes an equality of indices rather than an 
equality of types,
to avoid having to deal with an equality of the algebraic structure itself.
-/
protected def cast {ι : Type*} {M : ι → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] {i j : ι} (h : i = j) :
    M i ≃ₗ[R] M j where
  toAddEquiv := AddEquiv.cast h
  map_smul' _ _ := by cases h; rfl

/-- Interpret a `RingEquiv` `f` as an `f`-semilinear equiv. -/
@[simps]
/-
**LinearEquiv._root_.RingEquiv.toSemilinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Line
arEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpret a `RingEquiv` `f` as an `f`-semilinear equiv.
-/
def _root_.RingEquiv.toSemilinearEquiv (f : R ≃+* S) :
    haveI := RingHomInvPair.of_ringEquiv f
    haveI := RingHomInvPair.symm (↑f : R →+* S) (f.symm : S →+* R)
    R ≃ₛₗ[(↑f : R →+* S)] S :=
  haveI := RingHomInvPair.of_ringEquiv f
  haveI := RingHomInvPair.symm (↑f : R →+* S) (f.symm : S →+* R)
  { f with
    toFun := f
    map_smul' := f.map_mul }

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**LinearEquiv._root_.RingEquiv.symm_toSemilinearEquiv_symm_apply** 是 Mathlib 中的一
个引理，位于命名空间 `LinearEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.RingEquiv.symm_toSemilinearEquiv_symm_apply (f : R ≃+* S) (x : R) :
  f.symm.toSemilinearEquiv.symm (σ' := RingHomClass.toRingHom f) x = f x := rfl

variable [AddCommMonoid M]

/-- An involutive linear map is a linear equivalence. -/
/-
**LinearEquiv.ofInvolutive** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：ofInvolutive {σ σ' : R ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
 {_ : Module R M} (f : M ->ₛₗ[σ] M) (hf : Involutive f) : M ≃ₛₗ[σ] M
参数：f : M ->ₛₗ[σ] M；hf : Involutive f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun

--- 原说明 ---
An involutive linear map is a linear equivalence.
-/
def ofInvolutive {σ σ' : R →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    {_ : Module R M} (f : M →ₛₗ[σ] M) (hf : Involutive f) : M ≃ₛₗ[σ] M :=
  { f, hf.toPerm f with }

@[simp]
/-
**LinearEquiv.coe_ofInvolutive** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：coe_ofInvolutive {σ σ' : R ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ
' σ] {_ : Module R M} (f : M ->ₛₗ[σ] M) (hf : Involutive f) : ⇑(ofInvolutive f h
f) = f
参数：f : M ->ₛₗ[σ] M；hf : Involutive f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofInvolutive {σ σ' : R →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    {_ : Module R M} (f : M →ₛₗ[σ] M) (hf : Involutive f) : ⇑(ofInvolutive f hf) = f :=
  rfl

end AddCommMonoid

section smul
variable {S R V W G : Type*} [Semiring R] [Semiring S]
  [AddCommMonoid V] [Module R V] [Module S V]
  [AddCommMonoid W] [Module R W] [Module S W]
  [AddCommMonoid G] [Module R G] [Module S G]
  [SMulCommClass R S W] [SMul S R] [IsScalarTower S R V] [IsScalarTower S R W]

/-- Left scalar multiplication of a unit and a linear equivalence, as a linear equivalence. -/
/-
**LinearEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `LinearEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left scalar multiplication of a unit and a linear equivalence, as a linear equiv
alence.
-/
instance : SMul Sˣ (V ≃ₗ[R] W) where smul α e :=
  { __ := (α : S) • e.toLinearMap
    invFun x := (↑α⁻¹ : S) • e.symm x
    left_inv _ := by simp [LinearMapClass.map_smul_of_tower e.symm, smul_smul]
    right_inv _ := by simp [smul_smul] }
/-
**LinearEquiv.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {S : Type u_14} {R : Type u_15} {V : Type u_16} {W : Type u_17} [inst : 
Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid V] [inst_3 : _root_.
Module R V] [inst_4 : _root_.Module S V] [inst_5 : AddCommMonoid W]   [inst_6 : 
_root_.Module R W] [inst_7 : _root_.Module S W] [inst_8 : SMulCommClass R S W] [
inst_9 : SMul S R]   [inst_10 : IsScalarTower S R V] [inst_11 : IsScalarTower S 
R W] (α : Sˣ) (e : V ≃ₗ[R] W) (x : V), (α • e) x = ↑α • e x
参数：α : Sˣ；e : V ≃ₗ[R] W；x : V；α • e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem smul_apply (α : Sˣ) (e : V ≃ₗ[R] W) (x : V) : (α • e) x = (α : S) • e x := rfl
/-
**LinearEquiv.symm_smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：symm_smul_apply (e : V ≃ₗ[R] W) (α : Sˣ) (x : W) : (α • e).symm x = (↑α⁻¹ 
: S) • e.symm x
参数：e : V ≃ₗ[R] W；α : Sˣ；x : W。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_smul_apply (e : V ≃ₗ[R] W) (α : Sˣ) (x : W) :
    (α • e).symm x = (↑α⁻¹ : S) • e.symm x := rfl
/-
**LinearEquiv.symm_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {S : Type u_14} {R : Type u_15} {V : Type u_16} {W : Type u_17} [inst : 
Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid V] [inst_3 : _root_.
Module R V] [inst_4 : _root_.Module S V] [inst_5 : AddCommMonoid W]   [inst_6 : 
_root_.Module R W] [inst_7 : _root_.Module S W] [inst_8 : SMulCommClass R S W] [
inst_9 : SMul S R]   [inst_10 : IsScalarTower S R V] [inst_11 : IsScalarTower S 
R W] [inst_12 : SMulCommClass R S V] (e : V ≃ₗ[R] W)   (α : Sˣ), (α • e).symm = 
α⁻¹ • e.symm
参数：e : V ≃ₗ[R] W；α : Sˣ；α • e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem symm_smul [SMulCommClass R S V] (e : V ≃ₗ[R] W) (α : Sˣ) :
    (α • e).symm = α⁻¹ • e.symm := rfl
/-
**LinearEquiv.toLinearMap_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {S : Type u_14} {R : Type u_15} {V : Type u_16} {W : Type u_17} [inst : 
Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid V] [inst_3 : _root_.
Module R V] [inst_4 : _root_.Module S V] [inst_5 : AddCommMonoid W]   [inst_6 : 
_root_.Module R W] [inst_7 : _root_.Module S W] [inst_8 : SMulCommClass R S W] [
inst_9 : SMul S R]   [inst_10 : IsScalarTower S R V] [inst_11 : IsScalarTower S 
R W] (e : V ≃ₗ[R] W) (α : Sˣ), ↑(α • e) = ↑α • ↑e
参数：e : V ≃ₗ[R] W；α : Sˣ；α • e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toLinearMap_smul (e : V ≃ₗ[R] W) (α : Sˣ) :
    (α • e).toLinearMap = (α : S) • e.toLinearMap := rfl
/-
**LinearEquiv.smul_trans** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：smul_trans [SMulCommClass R S V] [IsScalarTower S R G] (α : Sˣ) (e : G ≃ₗ[
R] V) (f : V ≃ₗ[R] W) : (α • e).trans f = α • (e.trans f)
参数：α : Sˣ；e : G ≃ₗ[R] V；f : V ≃ₗ[R] W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMapClass.map_smul_of_tower`：∀ {M : Type u_8} {M₂ : Type u_10} [ins
t : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type u_15}
   [inst_2 : Semiring …
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_trans [SMulCommClass R S V] [IsScalarTower S R G]
    (α : Sˣ) (e : G ≃ₗ[R] V) (f : V ≃ₗ[R] W) :
    (α • e).trans f = α • (e.trans f) := by ext; simp [LinearMapClass.map_smul_of_tower f]
/-
**LinearEquiv.trans_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：trans_smul [IsScalarTower S R G] (α : Sˣ) (e : G ≃ₗ[R] V) (f : V ≃ₗ[R] W) 
: e.trans (α • f) = α • (e.trans f)
参数：α : Sˣ；e : G ≃ₗ[R] V；f : V ≃ₗ[R] W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trans_smul [IsScalarTower S R G]
    (α : Sˣ) (e : G ≃ₗ[R] V) (f : V ≃ₗ[R] W) :
    e.trans (α • f) = α • (e.trans f) := by ext; simp

end smul
end LinearEquiv

