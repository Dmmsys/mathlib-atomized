/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.Algebra.Module.Equiv

/-!
# Isomorphisms of topological algebras

This file contains an API for `ContinuousAlgEquiv R A B`, the type of
continuous `R`-algebra isomorphisms with continuous inverses. Here `R` is a
commutative (semi)ring, and `A` and `B` are `R`-algebras with topologies.

## Main definitions

Let `R` be a commutative semiring and let `A` and `B` be `R`-algebras which
are also topological spaces.

* `ContinuousAlgEquiv R A B`: the type of continuous `R`-algebra isomorphisms
  from `A` to `B` with continuous inverses.

## Notation

`A ≃A[R] B` : notation for `ContinuousAlgEquiv R A B`.

## Tags

* continuous, isomorphism, algebra
-/

@[expose] public section

open scoped Topology


/--
`ContinuousAlgEquiv R A B`, with notation `A ≃A[R] B`, is the type of bijections
between the topological `R`-algebras `A` and `B` which are both homeomorphisms
and `R`-algebra isomorphisms.
-/
/-
**ContinuousAlgEquiv** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) →   (A : Type u_2) →     (B : Type u_3) →       [inst : Com
mSemiring R] →         [inst_1 : Semiring A] →           [TopologicalSpace A] → 
            [inst_3 : Semiring B] → [TopologicalSpace B] → [Algebra R A] → [Alge
bra R B] → Type (max u_2 u_3)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousAlgEquiv R A B`, with notation `A ≃A[R] B`, is the type of bijections
between the topological `R`-algebras `A` and `B` which are both homeomorphisms
and `R`-algebra isomorphisms.
-/
structure ContinuousAlgEquiv (R A B : Type*) [CommSemiring R]
    [Semiring A] [TopologicalSpace A] [Semiring B] [TopologicalSpace B] [Algebra R A]
    [Algebra R B] extends A ≃ₐ[R] B, A ≃ₜ B

@[inherit_doc]
notation:50 A " ≃A[" R "] " B => ContinuousAlgEquiv R A B

attribute [nolint docBlame] ContinuousAlgEquiv.toHomeomorph

/--
`ContinuousAlgEquivClass F R A B` states that `F` is a type of topological algebra
  structure-preserving equivalences. You should extend this class when you
  extend `ContinuousAlgEquiv`.
-/
/-
**ContinuousAlgEquivClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) →   (R : outParam (Type u_2)) →     (A : outParam (Type u_3
)) →       (B : outParam (Type u_4)) →         [inst : CommSemiring R] →        
   [inst_1 : Semiring A] →             [TopologicalSpace A] →               [ins
t_3 : Semiring B] → [TopologicalSpace B] → [Algebra R A] → [Algebra R B] → [Equi
vLike F A B] → Prop
参数：Type u_2；Type u_3；Type u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousAlgEquivClass F R A B` states that `F` is a type of topological algeb
ra
  structure-preserving equivalences. You should extend this class when you
  extend `ContinuousAlgEquiv`.
-/
class ContinuousAlgEquivClass (F : Type*) (R A B : outParam Type*) [CommSemiring R]
    [Semiring A] [TopologicalSpace A] [Semiring B] [TopologicalSpace B]
    [Algebra R A] [Algebra R B] [EquivLike F A B] : Prop
    extends AlgEquivClass F R A B, HomeomorphClass F A B

namespace ContinuousAlgEquiv

variable {R A B C : Type*}
  [CommSemiring R] [Semiring A] [TopologicalSpace A] [Semiring B]
  [TopologicalSpace B] [Semiring C] [TopologicalSpace C] [Algebra R A] [Algebra R B]
  [Algebra R C]

/-- The natural coercion from a continuous algebra isomorphism to a continuous
algebra morphism. -/
@[coe]
/-
**ContinuousAlgEquiv.toContinuousAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAlg
Equiv`。
形式化陈述：toContinuousAlgHom (e : A ≃A[R] B) : A ->A[R] B where __
参数：e : A ≃A[R] B。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAlgEquiv.continuous_toFun`：∀ {R : Type u_1} {A : Type u_2} {B 
: Type u_3} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Topologica
lSpace A] [inst_3 : Semir…

--- 原说明 ---
The natural coercion from a continuous algebra isomorphism to a continuous
algebra morphism.
-/
def toContinuousAlgHom (e : A ≃A[R] B) : A →A[R] B where
  __ := e.toAlgHom
  cont := e.continuous_toFun
/-
**ContinuousAlgEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAlgEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeOut (A ≃A[R] B) (A →A[R] B) where coe := toContinuousAlgHom
/-
**ContinuousAlgEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAlgEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeOut (A ≃A[R] B) (A ≃ₐ[R] B) where coe := toAlgEquiv
/-
**ContinuousAlgEquiv.equivLike** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAlgEquiv`。
形式化陈述：equivLike : EquivLike (A ≃A[R] B) A B where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance equivLike : EquivLike (A ≃A[R] B) A B where
  coe f := f.toFun
  inv f := f.invFun
  coe_injective' f g h₁ h₂ := by
    obtain ⟨f', _⟩ := f
    obtain ⟨g', _⟩ := g
    rcases f' with ⟨⟨_, _⟩, _⟩
    rcases g' with ⟨⟨_, _⟩, _⟩
    congr
  left_inv f := f.left_inv
  right_inv f := f.right_inv
/-
**ContinuousAlgEquiv.continuousAlgEquivClass** 是 Mathlib 中的一个实例，位于命名空间 `Continuo
usAlgEquiv`。
形式化陈述：continuousAlgEquivClass : ContinuousAlgEquivClass (A ≃A[R] B) R A B where 
map_add f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.map_mul'`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : Comm
Semiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A]
 [inst_…
· 使用定理 `AlgEquiv.map_add'`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : Comm
Semiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A]
 [inst_…
· 使用定理 `AlgEquiv.commutes'`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A
] [inst_…
· 使用定理 `ContinuousAlgEquiv.continuous_toFun`：∀ {R : Type u_1} {A : Type u_2} {B 
: Type u_3} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Topologica
lSpace A] [inst_3 : Semir…
· 使用定理 `ContinuousAlgEquiv.continuous_invFun`：∀ {R : Type u_1} {A : Type u_2} {B
 : Type u_3} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Topologic
alSpace A] [inst_3 : Semir…
-/
instance continuousAlgEquivClass : ContinuousAlgEquivClass (A ≃A[R] B) R A B where
  map_add f := f.map_add'
  map_mul f := f.map_mul'
  commutes f := f.commutes'
  map_continuous := continuous_toFun
  inv_continuous := continuous_invFun
/-
**ContinuousAlgEquiv.coe_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEquiv`。
形式化陈述：coe_apply (e : A ≃A[R] B) (a : A) : (e : A ->A[R] B) a = e a
参数：e : A ≃A[R] B；a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_apply (e : A ≃A[R] B) (a : A) : (e : A →A[R] B) a = e a := rfl
/-
**ContinuousAlgEquiv.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEquiv`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst : CommSemiring R] [in
st_1 : Semiring A]   [inst_2 : TopologicalSpace A] [inst_3 : Semiring B] [inst_4
 : TopologicalSpace B] [inst_5 : Algebra R A]   [inst_6 : Algebra R B] (e : A ≃ₐ
[R] B) (he : Continuous e.toFun) (he' : Continuous e.invFun),   ⇑{ toAlgEquiv :=
 e, continuous_toFun := he, continuous_invFun := he' } = ⇑e
参数：e : A ≃ₐ[R] B；he : Continuous e.toFun；he' : Continuous e.invFun。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_mk (e : A ≃ₐ[R] B) (he he') : ⇑(mk e he he') = e := rfl

@[simp]
/-
**ContinuousAlgEquiv.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEquiv`。
形式化陈述：coe_coe (e : A ≃A[R] B) : ⇑(e : A ->A[R] B) = e
参数：e : A ≃A[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_coe (e : A ≃A[R] B) : ⇑(e : A →A[R] B) = e := rfl
/-
**ContinuousAlgEquiv.toAlgEquiv_injective** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousA
lgEquiv`。
形式化陈述：toAlgEquiv_injective : Function.Injective (toAlgEquiv : (A ≃A[R] B) -> A ≃
ₐ[R] B)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAlgEquiv_injective : Function.Injective (toAlgEquiv : (A ≃A[R] B) → A ≃ₐ[R] B) := by
  rintro ⟨e, _, _⟩ ⟨e', _, _⟩ rfl
  rfl

@[ext]
/-
**ContinuousAlgEquiv.ext** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEquiv`。
形式化陈述：ext {f g : A ≃A[R] B} (h : ⇑f = ⇑g) : f = g
参数：h : ⇑f = ⇑g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAlgEquiv.toAlgEquiv_injective`：toAlgEquiv_injective : Function
.Injective (toAlgEquiv : (A ≃A[R] B) -> A ≃ₐ[R] B)
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
theorem ext {f g : A ≃A[R] B} (h : ⇑f = ⇑g) : f = g :=
  toAlgEquiv_injective <| AlgEquiv.ext <| congr_fun h
/-
**ContinuousAlgEquiv.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEquiv
`。
形式化陈述：coe_injective : Function.Injective ((↑) : (A ≃A[R] B) -> A ->A[R] B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAlgEquiv.ext`：ext {f g : A ≃A[R] B} (h : ⇑f = ⇑g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ContinuousAlgHom.ext_iff`：∀ {R : Type u_1} [inst : CommSemiring R] {A : 
Type u_2} [inst_1 : Semiring A] [inst_2 : TopologicalSpace A]   {B : Type u_3} [
inst_3 : Semir…
-/
theorem coe_injective : Function.Injective ((↑) : (A ≃A[R] B) → A →A[R] B) :=
  fun _ _ h => ext <| funext <| ContinuousAlgHom.ext_iff.1 h

@[simp]
/-
**ContinuousAlgEquiv.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEquiv`。
形式化陈述：coe_inj {f g : A ≃A[R] B} : (f : A ->A[R] B) = g ↔ f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `ContinuousAlgEquiv.coe_injective`：coe_injective : Function.Injective ((↑
) : (A ≃A[R] B) -> A ->A[R] B)
-/
theorem coe_inj {f g : A ≃A[R] B} : (f : A →A[R] B) = g ↔ f = g :=
  coe_injective.eq_iff

@[simp]
/-
**ContinuousAlgEquiv.coe_toAlgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEqui
v`。
形式化陈述：coe_toAlgEquiv (e : A ≃A[R] B) : ⇑e.toAlgEquiv = e
参数：e : A ≃A[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toAlgEquiv (e : A ≃A[R] B) : ⇑e.toAlgEquiv = e := rfl

/-- The natural coercion from a continuous algebra isomorphism
to a continuous linear isomorphism. -/
@[coe]
/-
**ContinuousAlgEquiv.toContinuousLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Continuo
usAlgEquiv`。
形式化陈述：toContinuousLinearEquiv (e : A ≃A[R] B) : A ≃L[R] B
参数：e : A ≃A[R] B。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAlgEquiv.continuous_toFun`：∀ {R : Type u_1} {A : Type u_2} {B 
: Type u_3} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Topologica
lSpace A] [inst_3 : Semir…
· 使用定理 `ContinuousAlgEquiv.continuous_invFun`：∀ {R : Type u_1} {A : Type u_2} {B
 : Type u_3} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Topologic
alSpace A] [inst_3 : Semir…

--- 原说明 ---
The natural coercion from a continuous algebra isomorphism
to a continuous linear isomorphism.
-/
def toContinuousLinearEquiv (e : A ≃A[R] B) : A ≃L[R] B :=
  { e with __ := e.toLinearEquiv }
/-
**ContinuousAlgEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAlgEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe (A ≃A[R] B) (A ≃L[R] B) := ⟨toContinuousLinearEquiv⟩
/-
**ContinuousAlgEquiv.coeCLE_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEquiv`
。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst : CommSemiring R] [in
st_1 : Semiring A]   [inst_2 : TopologicalSpace A] [inst_3 : Semiring B] [inst_4
 : TopologicalSpace B] [inst_5 : Algebra R A]   [inst_6 : Algebra R B] (e : A ≃A
[R] B) (a : A), ↑e a = e a
参数：e : A ≃A[R] B；a : A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coeCLE_apply (e : A ≃A[R] B) (a : A) : (e : A ≃L[R] B) a = e a := rfl
/-
**ContinuousAlgEquiv.coe_coeCLE** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEquiv`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst : CommSemiring R] [in
st_1 : Semiring A]   [inst_2 : TopologicalSpace A] [inst_3 : Semiring B] [inst_4
 : TopologicalSpace B] [inst_5 : Algebra R A]   [inst_6 : Algebra R B] (e : A ≃A
[R] B), ⇑↑e = ⇑e
参数：e : A ≃A[R] B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_coeCLE (e : A ≃A[R] B) : ⇑(e : A ≃L[R] B) = e := rfl

@[simp]
/-
**ContinuousAlgEquiv.toContinuousLinearEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Co
ntinuousAlgEquiv`。
形式化陈述：toContinuousLinearEquiv_apply (e : A ≃A[R] B) (a : A) : e.toContinuousLine
arEquiv a = e a
参数：e : A ≃A[R] B；a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toContinuousLinearEquiv_apply (e : A ≃A[R] B) (a : A) :
    e.toContinuousLinearEquiv a = e a := rfl
/-
**ContinuousAlgEquiv.toContinuousLinearMap_toContinuousLinearEquiv_eq** 是 Mathli
b 中的一个定理，位于命名空间 `ContinuousAlgEquiv`。
形式化陈述：toContinuousLinearMap_toContinuousLinearEquiv_eq (e : A ≃A[R] B) : e.toCon
tinuousLinearEquiv.toContinuousLinearMap = e.toContinuousAlgHom.toContinuousLine
arMap
参数：e : A ≃A[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toContinuousLinearMap_toContinuousLinearEquiv_eq (e : A ≃A[R] B) :
    e.toContinuousLinearEquiv.toContinuousLinearMap
    = e.toContinuousAlgHom.toContinuousLinearMap := rfl
/-
**ContinuousAlgEquiv.toContinuousLinearEquiv_toLinearEquiv_eq** 是 Mathlib 中的一个定理
，位于命名空间 `ContinuousAlgEquiv`。
形式化陈述：toContinuousLinearEquiv_toLinearEquiv_eq (e : A ≃A[R] B) : e.toContinuousL
inearEquiv.toLinearEquiv = e.toAlgEquiv.toLinearEquiv
参数：e : A ≃A[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toContinuousLinearEquiv_toLinearEquiv_eq (e : A ≃A[R] B) :
    e.toContinuousLinearEquiv.toLinearEquiv
    = e.toAlgEquiv.toLinearEquiv := rfl
/-
**ContinuousAlgEquiv.isOpenMap** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEquiv`。
形式化陈述：isOpenMap (e : A ≃A[R] B) : IsOpenMap e
参数：e : A ≃A[R] B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsOpenMap ⇑h
-/
theorem isOpenMap (e : A ≃A[R] B) : IsOpenMap e :=
  e.toHomeomorph.isOpenMap
/-
**ContinuousAlgEquiv.image_closure** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEquiv
`。
形式化陈述：image_closure (e : A ≃A[R] B) (S : Set A) : e '' closure S = closure (e ''
 S)
参数：e : A ≃A[R] B；S : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.image_closure`：image_closure (h : X ≃ₜ Y) (s : Set X) : h '' 
closure s = closure (h '' s)
-/
theorem image_closure (e : A ≃A[R] B) (S : Set A) : e '' closure S = closure (e '' S) :=
  e.toHomeomorph.image_closure S
/-
**ContinuousAlgEquiv.preimage_closure** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEq
uiv`。
形式化陈述：preimage_closure (e : A ≃A[R] B) (S : Set B) : e ⁻¹' closure S = closure (
e ⁻¹' S)
参数：e : A ≃A[R] B；S : Set B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.preimage_closure`：preimage_closure (h : X ≃ₜ Y) (s : Set Y) :
 h ⁻¹' closure s = closure (h ⁻¹' s)
-/
theorem preimage_closure (e : A ≃A[R] B) (S : Set B) : e ⁻¹' closure S = closure (e ⁻¹' S) :=
  e.toHomeomorph.preimage_closure S

@[simp]
/-
**ContinuousAlgEquiv.isClosed_image** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEqui
v`。
形式化陈述：isClosed_image (e : A ≃A[R] B) {S : Set A} : IsClosed (e '' S) ↔ IsClosed 
S
参数：e : A ≃A[R] B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isClosed_image`：isClosed_image (h : X ≃ₜ Y) {s : Set X} : IsC
losed (h '' s) ↔ IsClosed s
-/
theorem isClosed_image (e : A ≃A[R] B) {S : Set A} : IsClosed (e '' S) ↔ IsClosed S :=
  e.toHomeomorph.isClosed_image
/-
**ContinuousAlgEquiv.map_nhds_eq** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEquiv`。
形式化陈述：map_nhds_eq (e : A ≃A[R] B) (a : A) : Filter.map e (𝓝 a) = 𝓝 (e a)
参数：e : A ≃A[R] B；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.map_nhds_eq`：map_nhds_eq (h : X ≃ₜ Y) (x : X) : map h (𝓝 x) =
 𝓝 (h x)
-/
theorem map_nhds_eq (e : A ≃A[R] B) (a : A) : Filter.map e (𝓝 a) = 𝓝 (e a) :=
  e.toHomeomorph.map_nhds_eq a
/-
**ContinuousAlgEquiv.map_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEqu
iv`。
形式化陈述：map_eq_zero_iff (e : A ≃A[R] B) {a : A} : e a = 0 ↔ a = 0
参数：e : A ≃A[R] B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.map_eq_zero_iff`：map_eq_zero_iff {x : M} : e x = 0 ↔ x = 0
-/
theorem map_eq_zero_iff (e : A ≃A[R] B) {a : A} : e a = 0 ↔ a = 0 :=
  e.toAlgEquiv.toLinearEquiv.map_eq_zero_iff

attribute [continuity]
  ContinuousAlgEquiv.continuous_invFun ContinuousAlgEquiv.continuous_toFun

@[fun_prop]
/-
**ContinuousAlgEquiv.continuous** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEquiv`。
形式化陈述：continuous (e : A ≃A[R] B) : Continuous e
参数：e : A ≃A[R] B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAlgEquiv.continuous_toFun`：∀ {R : Type u_1} {A : Type u_2} {B 
: Type u_3} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Topologica
lSpace A] [inst_3 : Semir…
-/
theorem continuous (e : A ≃A[R] B) : Continuous e := e.continuous_toFun
/-
**ContinuousAlgEquiv.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEquiv`
。
形式化陈述：continuousOn (e : A ≃A[R] B) {S : Set A} : ContinuousOn e S
参数：e : A ≃A[R] B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `ContinuousAlgEquiv.continuous`：continuous (e : A ≃A[R] B) : Continuous e
-/
theorem continuousOn (e : A ≃A[R] B) {S : Set A} : ContinuousOn e S :=
  e.continuous.continuousOn
/-
**ContinuousAlgEquiv.continuousAt** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEquiv`
。
形式化陈述：continuousAt (e : A ≃A[R] B) {a : A} : ContinuousAt e a
参数：e : A ≃A[R] B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ContinuousAlgEquiv.continuous`：continuous (e : A ≃A[R] B) : Continuous e
-/
theorem continuousAt (e : A ≃A[R] B) {a : A} : ContinuousAt e a :=
  e.continuous.continuousAt
/-
**ContinuousAlgEquiv.continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlg
Equiv`。
形式化陈述：continuousWithinAt (e : A ≃A[R] B) {S : Set A} {a : A} : ContinuousWithinA
t e S a
参数：e : A ≃A[R] B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
· 使用定理 `ContinuousAlgEquiv.continuous`：continuous (e : A ≃A[R] B) : Continuous e
-/
theorem continuousWithinAt (e : A ≃A[R] B) {S : Set A} {a : A} :
    ContinuousWithinAt e S a :=
  e.continuous.continuousWithinAt
/-
**ContinuousAlgEquiv.comp_continuous_iff** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAl
gEquiv`。
形式化陈述：comp_continuous_iff {α : Type*} [TopologicalSpace α] (e : A ≃A[R] B) {f : 
α -> A} : Continuous (e ∘ f) ↔ Continuous f
参数：e : A ≃A[R] B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.comp_continuous_iff`：comp_continuous_iff (h : X ≃ₜ Y) {f : Z 
-> X} : Continuous (h ∘ f) ↔ Continuous f
-/
theorem comp_continuous_iff {α : Type*} [TopologicalSpace α] (e : A ≃A[R] B) {f : α → A} :
    Continuous (e ∘ f) ↔ Continuous f :=
  e.toHomeomorph.comp_continuous_iff
/-
**ContinuousAlgEquiv.comp_continuous_iff'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousA
lgEquiv`。
形式化陈述：comp_continuous_iff' {β : Type*} [TopologicalSpace β] (e : A ≃A[R] B) {g :
 B -> β} : Continuous (g ∘ e) ↔ Continuous g
参数：e : A ≃A[R] B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.comp_continuous_iff'`：comp_continuous_iff' (h : X ≃ₜ Y) {f : 
Y -> Z} : Continuous (f ∘ h) ↔ Continuous f
-/
theorem comp_continuous_iff' {β : Type*} [TopologicalSpace β] (e : A ≃A[R] B) {g : B → β} :
    Continuous (g ∘ e) ↔ Continuous g :=
  e.toHomeomorph.comp_continuous_iff'

variable (R A)

/-- The identity isomorphism as a continuous `R`-algebra equivalence. -/
@[refl]
/-
**ContinuousAlgEquiv.refl** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAlgEquiv`。
形式化陈述：refl : A ≃A[R] A where __
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)

--- 原说明 ---
The identity isomorphism as a continuous `R`-algebra equivalence.
-/
def refl : A ≃A[R] A where
  __ := AlgEquiv.refl
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

@[simp]
/-
**ContinuousAlgEquiv.refl_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEquiv`。
形式化陈述：refl_apply (a : A) : refl R A a = a
参数：a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_apply (a : A) : refl R A a = a := rfl

@[simp]
/-
**ContinuousAlgEquiv.coe_refl** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEquiv`。
形式化陈述：coe_refl : refl R A = ContinuousAlgHom.id R A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_refl : refl R A = ContinuousAlgHom.id R A := rfl

@[simp]
/-
**ContinuousAlgEquiv.coeCLE_refl** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEquiv`。
形式化陈述：coeCLE_refl : (refl R A).toContinuousLinearEquiv = ContinuousLinearEquiv.r
efl R A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeCLE_refl : (refl R A).toContinuousLinearEquiv = ContinuousLinearEquiv.refl R A := rfl

@[simp]
/-
**ContinuousAlgEquiv.coe_refl'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEquiv`。
形式化陈述：coe_refl' : ⇑(refl R A) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_refl' : ⇑(refl R A) = id := rfl

@[simp]
/-
**ContinuousAlgEquiv.refl_toContinuousLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Con
tinuousAlgEquiv`。
形式化陈述：refl_toContinuousLinearEquiv : (refl R A).toContinuousLinearEquiv = .refl 
R A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_toContinuousLinearEquiv :
    (refl R A).toContinuousLinearEquiv = .refl R A := rfl

variable {R A}

/-- The inverse of a continuous algebra equivalence. -/
@[symm]
/-
**ContinuousAlgEquiv.symm** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAlgEquiv`。
形式化陈述：symm (e : A ≃A[R] B) : B ≃A[R] A where __
参数：e : A ≃A[R] B。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAlgEquiv.continuous_invFun`：∀ {R : Type u_1} {A : Type u_2} {B
 : Type u_3} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Topologic
alSpace A] [inst_3 : Semir…
· 使用定理 `ContinuousAlgEquiv.continuous_toFun`：∀ {R : Type u_1} {A : Type u_2} {B 
: Type u_3} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Topologica
lSpace A] [inst_3 : Semir…

--- 原说明 ---
The inverse of a continuous algebra equivalence.
-/
def symm (e : A ≃A[R] B) : B ≃A[R] A where
  __ := e.toAlgEquiv.symm
  continuous_toFun := e.continuous_invFun
  continuous_invFun := e.continuous_toFun

@[simp]
/-
**ContinuousAlgEquiv.apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEq
uiv`。
形式化陈述：apply_symm_apply (e : A ≃A[R] B) (b : B) : e (e.symm b) = b
参数：e : A ≃A[R] B；b : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
-/
theorem apply_symm_apply (e : A ≃A[R] B) (b : B) : e (e.symm b) = b :=
  e.1.right_inv b

@[simp]
/-
**ContinuousAlgEquiv.symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEq
uiv`。
形式化陈述：symm_apply_apply (e : A ≃A[R] B) (a : A) : e.symm (e a) = a
参数：e : A ≃A[R] B；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
-/
theorem symm_apply_apply (e : A ≃A[R] B) (a : A) : e.symm (e a) = a :=
  e.1.left_inv a

@[simp]
/-
**ContinuousAlgEquiv.symm_image_image** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEq
uiv`。
形式化陈述：symm_image_image (e : A ≃A[R] B) (S : Set A) : e.symm '' e '' S = S
参数：e : A ≃A[R] B；S : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_image_image`：symm_image_image {α β} (e : α ≃ β) (s : Set α) :
 e.symm '' e '' s = s
-/
theorem symm_image_image (e : A ≃A[R] B) (S : Set A) : e.symm '' e '' S = S :=
  e.toEquiv.symm_image_image S

@[simp]
/-
**ContinuousAlgEquiv.image_symm_image** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEq
uiv`。
形式化陈述：image_symm_image (e : A ≃A[R] B) (S : Set B) : e '' e.symm '' S = S
参数：e : A ≃A[R] B；S : Set B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAlgEquiv.symm_image_image`：symm_image_image (e : A ≃A[R] B) (S
 : Set A) : e.symm '' e '' S = S
-/
theorem image_symm_image (e : A ≃A[R] B) (S : Set B) : e '' e.symm '' S = S :=
  e.symm.symm_image_image S

@[simp]
/-
**ContinuousAlgEquiv.symm_toAlgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEqu
iv`。
形式化陈述：symm_toAlgEquiv (e : A ≃A[R] B) : e.symm.toAlgEquiv = e.toAlgEquiv.symm
参数：e : A ≃A[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_toAlgEquiv (e : A ≃A[R] B) : e.symm.toAlgEquiv = e.toAlgEquiv.symm := rfl

@[simp]
/-
**ContinuousAlgEquiv.symm_toHomeomorph** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgE
quiv`。
形式化陈述：symm_toHomeomorph (e : A ≃A[R] B) : e.symm.toHomeomorph = e.toHomeomorph.s
ymm
参数：e : A ≃A[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_toHomeomorph (e : A ≃A[R] B) : e.symm.toHomeomorph = e.toHomeomorph.symm := rfl

@[simp]
/-
**ContinuousAlgEquiv.toContinuousLinearEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Con
tinuousAlgEquiv`。
形式化陈述：toContinuousLinearEquiv_symm (e : A ≃A[R] B) : e.symm.toContinuousLinearEq
uiv = e.toContinuousLinearEquiv.symm
参数：e : A ≃A[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toContinuousLinearEquiv_symm (e : A ≃A[R] B) :
    e.symm.toContinuousLinearEquiv = e.toContinuousLinearEquiv.symm := rfl
/-
**ContinuousAlgEquiv.symm_map_nhds_eq** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEq
uiv`。
形式化陈述：symm_map_nhds_eq (e : A ≃A[R] B) (a : A) : Filter.map e.symm (𝓝 (e a)) = 𝓝
 a
参数：e : A ≃A[R] B；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.symm_map_nhds_eq`：symm_map_nhds_eq (h : X ≃ₜ Y) (x : X) : map
 h.symm (𝓝 (h x)) = 𝓝 x
-/
theorem symm_map_nhds_eq (e : A ≃A[R] B) (a : A) : Filter.map e.symm (𝓝 (e a)) = 𝓝 a :=
  e.toHomeomorph.symm_map_nhds_eq a

/-- The composition of two continuous algebra equivalences. -/
@[trans]
/-
**ContinuousAlgEquiv.trans** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAlgEquiv`。
形式化陈述：trans (e₁ : A ≃A[R] B) (e₂ : B ≃A[R] C) : A ≃A[R] C where __
参数：e₁ : A ≃A[R] B；e₂ : B ≃A[R] C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of two continuous algebra equivalences.
-/
def trans (e₁ : A ≃A[R] B) (e₂ : B ≃A[R] C) : A ≃A[R] C where
  __ := e₁.toAlgEquiv.trans e₂.toAlgEquiv
  continuous_toFun := e₂.continuous_toFun.comp e₁.continuous_toFun
  continuous_invFun := e₁.continuous_invFun.comp e₂.continuous_invFun

@[simp]
/-
**ContinuousAlgEquiv.trans_toAlgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEq
uiv`。
形式化陈述：trans_toAlgEquiv (e₁ : A ≃A[R] B) (e₂ : B ≃A[R] C) : (e₁.trans e₂).toAlgEq
uiv = e₁.toAlgEquiv.trans e₂.toAlgEquiv
参数：e₁ : A ≃A[R] B；e₂ : B ≃A[R] C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_toAlgEquiv (e₁ : A ≃A[R] B) (e₂ : B ≃A[R] C) :
    (e₁.trans e₂).toAlgEquiv = e₁.toAlgEquiv.trans e₂.toAlgEquiv :=
  rfl

@[simp]
/-
**ContinuousAlgEquiv.trans_toContinuousLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Co
ntinuousAlgEquiv`。
形式化陈述：trans_toContinuousLinearEquiv (e₁ : A ≃A[R] B) (e₂ : B ≃A[R] C) : (e₁.tran
s e₂).toContinuousLinearEquiv = e₁.toContinuousLinearEquiv.trans e₂.toContinuous
LinearEquiv
参数：e₁ : A ≃A[R] B；e₂ : B ≃A[R] C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_toContinuousLinearEquiv (e₁ : A ≃A[R] B) (e₂ : B ≃A[R] C) :
    (e₁.trans e₂).toContinuousLinearEquiv
    = e₁.toContinuousLinearEquiv.trans e₂.toContinuousLinearEquiv := rfl

@[simp]
/-
**ContinuousAlgEquiv.trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEquiv`。
形式化陈述：trans_apply (e₁ : A ≃A[R] B) (e₂ : B ≃A[R] C) (a : A) : (e₁.trans e₂) a = 
e₂ (e₁ a)
参数：e₁ : A ≃A[R] B；e₂ : B ≃A[R] C；a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_apply (e₁ : A ≃A[R] B) (e₂ : B ≃A[R] C) (a : A) :
    (e₁.trans e₂) a = e₂ (e₁ a) :=
  rfl

@[simp]
/-
**ContinuousAlgEquiv.symm_trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEq
uiv`。
形式化陈述：symm_trans_apply (e₁ : B ≃A[R] A) (e₂ : C ≃A[R] B) (a : A) : (e₂.trans e₁)
.symm a = e₂.symm (e₁.symm a)
参数：e₁ : B ≃A[R] A；e₂ : C ≃A[R] B；a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_trans_apply (e₁ : B ≃A[R] A) (e₂ : C ≃A[R] B) (a : A) :
    (e₂.trans e₁).symm a = e₂.symm (e₁.symm a) :=
  rfl
/-
**ContinuousAlgEquiv.comp_coe** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEquiv`。
形式化陈述：comp_coe (e₁ : A ≃A[R] B) (e₂ : B ≃A[R] C) : e₂.toAlgHom.comp e₁.toAlgHom 
= e₁.trans e₂
参数：e₁ : A ≃A[R] B；e₂ : B ≃A[R] C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_coe (e₁ : A ≃A[R] B) (e₂ : B ≃A[R] C) :
    e₂.toAlgHom.comp e₁.toAlgHom = e₁.trans e₂ := by
  rfl

@[simp high]
/-
**ContinuousAlgEquiv.coe_comp_coe_symm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgE
quiv`。
形式化陈述：coe_comp_coe_symm (e : A ≃A[R] B) : e.toContinuousAlgHom.comp e.symm = Con
tinuousAlgHom.id R B
参数：e : A ≃A[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAlgHom.ext`：ext {f g : A ->A[R] B} (h : forall x, f x = g x) :
 f = g
· 使用定理 `ContinuousAlgEquiv.apply_symm_apply`：apply_symm_apply (e : A ≃A[R] B) (b
 : B) : e (e.symm b) = b
-/
theorem coe_comp_coe_symm (e : A ≃A[R] B) :
    e.toContinuousAlgHom.comp e.symm = ContinuousAlgHom.id R B :=
  ContinuousAlgHom.ext e.apply_symm_apply

@[simp high]
/-
**ContinuousAlgEquiv.coe_symm_comp_coe** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgE
quiv`。
形式化陈述：coe_symm_comp_coe (e : A ≃A[R] B) : e.symm.toContinuousAlgHom.comp e = Con
tinuousAlgHom.id R A
参数：e : A ≃A[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAlgHom.ext`：ext {f g : A ->A[R] B} (h : forall x, f x = g x) :
 f = g
· 使用定理 `ContinuousAlgEquiv.symm_apply_apply`：symm_apply_apply (e : A ≃A[R] B) (a
 : A) : e.symm (e a) = a
-/
theorem coe_symm_comp_coe (e : A ≃A[R] B) :
    e.symm.toContinuousAlgHom.comp e = ContinuousAlgHom.id R A :=
  ContinuousAlgHom.ext e.symm_apply_apply

@[simp]
/-
**ContinuousAlgEquiv.symm_comp_self** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEqui
v`。
形式化陈述：symm_comp_self (e : A ≃A[R] B) : (e.symm : B -> A) ∘ e = id
参数：e : A ≃A[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousAlgEquiv.symm_apply_apply`：symm_apply_apply (e : A ≃A[R] B) (a
 : A) : e.symm (e a) = a
-/
theorem symm_comp_self (e : A ≃A[R] B) : (e.symm : B → A) ∘ e = id := by
  exact funext <| e.symm_apply_apply

@[simp]
/-
**ContinuousAlgEquiv.self_comp_symm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEqui
v`。
形式化陈述：self_comp_symm (e : A ≃A[R] B) : (e : A -> B) ∘ e.symm = id
参数：e : A ≃A[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousAlgEquiv.apply_symm_apply`：apply_symm_apply (e : A ≃A[R] B) (b
 : B) : e (e.symm b) = b
-/
theorem self_comp_symm (e : A ≃A[R] B) : (e : A → B) ∘ e.symm = id :=
  funext <| e.apply_symm_apply

@[simp]
/-
**ContinuousAlgEquiv.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEquiv`。
形式化陈述：symm_symm (e : A ≃A[R] B) : e.symm.symm = e
参数：e : A ≃A[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_symm (e : A ≃A[R] B) : e.symm.symm = e := rfl
/-
**ContinuousAlgEquiv.symm_bijective** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEqui
v`。
形式化陈述：symm_bijective : Function.Bijective (symm : (A ≃A[R] B) -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `ContinuousAlgEquiv.symm_symm`：symm_symm (e : A ≃A[R] B) : e.symm.symm = 
e
-/
theorem symm_bijective : Function.Bijective (symm : (A ≃A[R] B) → _) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
/-
**ContinuousAlgEquiv.refl_symm** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEquiv`。
形式化陈述：refl_symm : (refl R A).symm = refl R A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_symm : (refl R A).symm = refl R A := rfl
/-
**ContinuousAlgEquiv.symm_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEqu
iv`。
形式化陈述：symm_symm_apply (e : A ≃A[R] B) (a : A) : e.symm.symm a = e a
参数：e : A ≃A[R] B；a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_symm_apply (e : A ≃A[R] B) (a : A) : e.symm.symm a = e a := rfl
/-
**ContinuousAlgEquiv.symm_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEquiv
`。
形式化陈述：symm_apply_eq (e : A ≃A[R] B) {a : A} {b : B} : e.symm b = a ↔ b = e a
参数：e : A ≃A[R] B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
-/
theorem symm_apply_eq (e : A ≃A[R] B) {a : A} {b : B} : e.symm b = a ↔ b = e a :=
  e.toEquiv.symm_apply_eq
/-
**ContinuousAlgEquiv.eq_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEquiv
`。
形式化陈述：eq_symm_apply (e : A ≃A[R] B) {a : A} {b : B} : a = e.symm b ↔ e a = b
参数：e : A ≃A[R] B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
-/
theorem eq_symm_apply (e : A ≃A[R] B) {a : A} {b : B} : a = e.symm b ↔ e a = b :=
  e.toEquiv.eq_symm_apply
/-
**ContinuousAlgEquiv.image_eq_preimage_symm** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sAlgEquiv`。
形式化陈述：image_eq_preimage_symm (e : A ≃A[R] B) (S : Set A) : e '' S = e.symm ⁻¹' S
参数：e : A ≃A[R] B；S : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
-/
theorem image_eq_preimage_symm (e : A ≃A[R] B) (S : Set A) : e '' S = e.symm ⁻¹' S :=
  e.toEquiv.image_eq_preimage_symm S
/-
**ContinuousAlgEquiv.image_symm_eq_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sAlgEquiv`。
形式化陈述：image_symm_eq_preimage (e : A ≃A[R] B) (S : Set B) : e.symm '' S = e ⁻¹' S
参数：e : A ≃A[R] B；S : Set B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAlgEquiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : A
 ≃A[R] B) (S : Set A) : e '' S = e.symm ⁻¹' S
· 使用定理 `ContinuousAlgEquiv.symm_symm`：symm_symm (e : A ≃A[R] B) : e.symm.symm = 
e
-/
theorem image_symm_eq_preimage (e : A ≃A[R] B) (S : Set B) : e.symm '' S = e ⁻¹' S := by
  rw [e.symm.image_eq_preimage_symm, e.symm_symm]

@[simp]
/-
**ContinuousAlgEquiv.symm_preimage_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sAlgEquiv`。
形式化陈述：symm_preimage_preimage (e : A ≃A[R] B) (S : Set B) : e.symm ⁻¹' e ⁻¹' S = 
S
参数：e : A ≃A[R] B；S : Set B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_preimage_preimage`：symm_preimage_preimage {α β} (e : α ≃ β) (
s : Set β) : e.symm ⁻¹' e ⁻¹' s = s
-/
theorem symm_preimage_preimage (e : A ≃A[R] B) (S : Set B) : e.symm ⁻¹' e ⁻¹' S = S :=
  e.toEquiv.symm_preimage_preimage S

@[simp]
/-
**ContinuousAlgEquiv.preimage_symm_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sAlgEquiv`。
形式化陈述：preimage_symm_preimage (e : A ≃A[R] B) (S : Set A) : e ⁻¹' e.symm ⁻¹' S = 
S
参数：e : A ≃A[R] B；S : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAlgEquiv.symm_preimage_preimage`：symm_preimage_preimage (e : A
 ≃A[R] B) (S : Set B) : e.symm ⁻¹' e ⁻¹' S = S
-/
theorem preimage_symm_preimage (e : A ≃A[R] B) (S : Set A) : e ⁻¹' e.symm ⁻¹' S = S :=
  e.symm.symm_preimage_preimage S
/-
**ContinuousAlgEquiv.isUniformEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlg
Equiv`。
形式化陈述：isUniformEmbedding {E₁ E₂ : Type*} [UniformSpace E₁] [UniformSpace E₂] [Ri
ng E₁] [IsUniformAddGroup E₁] [Algebra R E₁] [Ring E₂] [IsUniformAddGroup E₂] [A
lgebra R E₂] (e : E₁ ≃A[R] E₂) : IsUniformEmbedding e
参数：e : E₁ ≃A[R] E₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.isUniformEmbedding`：Equiv.isUniformEmbedding {α β : Type*} [Unifor
mSpace α] [UniformSpace β] (f : α ≃ β) (h₁ : UniformContinuous f) (h₂ : UniformC
ontinuous f.sy…
· 使用定理 `ContinuousAlgHom.uniformContinuous`：∀ {R : Type u_1} [inst : CommSemirin
g R] {E₁ : Type u_4} {E₂ : Type u_5} [inst_1 : UniformSpace E₁]   [inst_2 : Unif
ormSpace E₂] [inst_3 : R…
-/
theorem isUniformEmbedding {E₁ E₂ : Type*} [UniformSpace E₁] [UniformSpace E₂] [Ring E₁]
    [IsUniformAddGroup E₁] [Algebra R E₁] [Ring E₂] [IsUniformAddGroup E₂] [Algebra R E₂]
    (e : E₁ ≃A[R] E₂) : IsUniformEmbedding e :=
  e.toAlgEquiv.isUniformEmbedding e.toContinuousAlgHom.uniformContinuous
    e.symm.toContinuousAlgHom.uniformContinuous
/-
**ContinuousAlgEquiv._root_.AlgEquiv.isUniformEmbedding** 是 Mathlib 中的一个定理，位于命名空
间 `ContinuousAlgEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AlgEquiv.isUniformEmbedding {E₁ E₂ : Type*} [UniformSpace E₁] [UniformSpace E₂]
    [Ring E₁] [IsUniformAddGroup E₁] [Algebra R E₁] [Ring E₂] [IsUniformAddGroup E₂] [Algebra R E₂]
    (e : E₁ ≃ₐ[R] E₂) (h₁ : Continuous e) (h₂ : Continuous e.symm) :
    IsUniformEmbedding e :=
  ContinuousAlgEquiv.isUniformEmbedding { e with
    continuous_toFun := h₁
    continuous_invFun := by dsimp; fun_prop }
/-
**ContinuousAlgEquiv.surjective** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEquiv`。
形式化陈述：surjective (e : A ≃A[R] B) : Function.Surjective e
参数：e : A ≃A[R] B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
-/
theorem surjective (e : A ≃A[R] B) : Function.Surjective e := e.toAlgEquiv.surjective

/-- `Equiv.cast (congrArg _ h)` as a continuous algebra equiv.

Note that unlike `Equiv.cast`, this takes an equality of indices rather than an equality of types,
to avoid having to deal with an equality of the algebraic structure itself. -/
/-
**ContinuousAlgEquiv.cast** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousAlgEquiv`。
形式化陈述：cast {ι : Type*} {A : ι -> Type*} [(i : ι) -> Semiring (A i)] [(i : ι) -> 
Algebra R (A i)] [(i : ι) -> TopologicalSpace (A i)] {i j : ι} (h : i = j) : A i
 ≃A[R] A j where __
参数：i : ι；A i；i : ι；A i；i : ι；A i；h : i = j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Equiv.cast (congrArg _ h)` as a continuous algebra equiv.

Note that unlike `Equiv.cast`, this takes an equality of indices rather than an 
equality of types,
to avoid having to deal with an equality of the algebraic structure itself.
-/
def cast {ι : Type*} {A : ι → Type*} [(i : ι) → Semiring (A i)] [(i : ι) → Algebra R (A i)]
    [(i : ι) → TopologicalSpace (A i)] {i j : ι} (h : i = j) :
    A i ≃A[R] A j where
  __ := AlgEquiv.cast h
  continuous_toFun := by cases h; exact continuous_id
  continuous_invFun := by cases h; exact continuous_id

@[simp]
/-
**ContinuousAlgEquiv.cast_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEquiv`。
形式化陈述：cast_apply {ι : Type*} {A : ι -> Type*} [(i : ι) -> Semiring (A i)] [(i : 
ι) -> Algebra R (A i)] [(i : ι) -> TopologicalSpace (A i)] {i j : ι} (h : i = j)
 (x : A i) : cast (R
参数：i : ι；A i；i : ι；A i；i : ι；A i；h : i = j；x : A i。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cast_apply {ι : Type*} {A : ι → Type*} [(i : ι) → Semiring (A i)]
    [(i : ι) → Algebra R (A i)] [(i : ι) → TopologicalSpace (A i)] {i j : ι} (h : i = j) (x : A i) :
    cast (R := R) h x = Equiv.cast (congrArg A h) x := rfl

@[simp]
/-
**ContinuousAlgEquiv.cast_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAlgEqu
iv`。
形式化陈述：cast_symm_apply {ι : Type*} {A : ι -> Type*} [(i : ι) -> Semiring (A i)] [
(i : ι) -> Algebra R (A i)] [(i : ι) -> TopologicalSpace (A i)] {i j : ι} (h : i
 = j) (x : A j) : (cast (R
参数：i : ι；A i；i : ι；A i；i : ι；A i；h : i = j；x : A j。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cast_symm_apply {ι : Type*} {A : ι → Type*} [(i : ι) → Semiring (A i)]
    [(i : ι) → Algebra R (A i)] [(i : ι) → TopologicalSpace (A i)] {i j : ι} (h : i = j)
    (x : A j) : (cast (R := R) h).symm x = Equiv.cast (congrArg A h.symm) x := rfl

end ContinuousAlgEquiv

