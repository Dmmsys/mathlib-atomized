/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Restrictions of continuous linear maps to submodules

In this file, we collect the various operations of restrictions of `ContinuousLinearMap`s
to subspaces of the domain/codomain.

## Main definitions

* `Submodule.subtypeL S` is the inclusion map `S →L[R] M` when `S : Submodule R M`.
  In other words, it is `Submodule.subtype S` bundled as a `ContinuousLinearMap`.
* `ContinuousLinearMap.domRestrict f S` is the map `S →SL[σ] N` obtained by restricting
  `f : M →SL[σ] N` to a subspace `S` of the *domain*.
  This is the continuous version of `LinearMap.domRestrict`.
* `ContinuousLinearMap.codRestrict f S h` is the map `M →SL[σ] S` obtained by co-restricting
  `f : M →SL[σ] N` to a subspace `S` of the *codomain*; this requires a proof `h` that all values
  of `f` indeed belong to `S`.
  This is the continuous version of `LinearMap.codRestrict`.
* `ContinuousLinearMap.rangeRestrict f` is an abbreviation for
  `f.codRestrict f.range ⋯ : M →SL[σ] f.range`.
  This is the continuous version of `LinearMap.rangeRestrict`.
* `ContinuousLinearMap.restrict f h` is the map `S →SL[σ] T` obtained by restricting from
  `f : M →SL[σ] N` and a proof `h` that `f` maps `S` inside `T`.
  This is the continuous version of `LinearMap.restrict`.
-/

@[expose] public section

open LinearMap (ker range)

namespace Submodule

section Semiring

variable {R : Type*} [Semiring R] {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [Module R M]

/-- `Submodule.subtype` as a `ContinuousLinearMap`. -/
/-
**Submodule.subtypeL** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：subtypeL (p : Submodule R M) : p ->L[R] M where toLinearMap
参数：p : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Submodule.subtype` as a `ContinuousLinearMap`.
-/
def subtypeL (p : Submodule R M) : p →L[R] M where
  toLinearMap := p.subtype

@[simp, norm_cast]
/-
**Submodule.toLinearMap_subtypeL** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：toLinearMap_subtypeL (p : Submodule R M) : (p.subtypeL : p ->ₗ[R] M) = p.s
ubtype
参数：p : Submodule R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_subtypeL (p : Submodule R M) : (p.subtypeL : p →ₗ[R] M) = p.subtype := rfl

@[simp]
/-
**Submodule.coe_subtypeL** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_subtypeL (p : Submodule R M) : ⇑p.subtypeL = p.subtype
参数：p : Submodule R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_subtypeL (p : Submodule R M) : ⇑p.subtypeL = p.subtype := rfl

@[deprecated (since := "2026-05-06")]
alias coe_subtypeL' := coe_subtypeL
/-
**Submodule.subtypeL_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：subtypeL_apply (p : Submodule R M) (x : p) : p.subtypeL x = x
参数：p : Submodule R M；x : p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem subtypeL_apply (p : Submodule R M) (x : p) : p.subtypeL x = x := by simp
/-
**Submodule.isEmbedding_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isEmbedding_subtype (p : Submodule R M) : Topology.IsEmbedding p.subtype
参数：p : Submodule R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)
-/
theorem isEmbedding_subtype (p : Submodule R M) : Topology.IsEmbedding p.subtype := .subtypeVal
/-
**Submodule.isEmbedding_subtypeL** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isEmbedding_subtypeL (p : Submodule R M) : Topology.IsEmbedding p.subtypeL
参数：p : Submodule R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)
-/
theorem isEmbedding_subtypeL (p : Submodule R M) : Topology.IsEmbedding p.subtypeL := .subtypeVal
/-
**Submodule.isClosedEmbedding_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isClosedEmbedding_subtype (p : Submodule R M) (hp : IsClosed (p : Set M)) 
: Topology.IsClosedEmbedding p.subtype
参数：p : Submodule R M；hp : IsClosed (p : Set M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.subtypeVal`：Topology.IsClosedEmbedding.subtyp
eVal (h : IsClosed {a | p a}) : IsClosedEmbedding ((↑) : Subtype p -> X)
-/
theorem isClosedEmbedding_subtype (p : Submodule R M) (hp : IsClosed (p : Set M)) :
    Topology.IsClosedEmbedding p.subtype := .subtypeVal hp
/-
**Submodule.isClosedEmbedding_subtypeL** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：isClosedEmbedding_subtypeL (p : Submodule R M) (hp : IsClosed (p : Set M))
 : Topology.IsClosedEmbedding p.subtypeL
参数：p : Submodule R M；hp : IsClosed (p : Set M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.subtypeVal`：Topology.IsClosedEmbedding.subtyp
eVal (h : IsClosed {a | p a}) : IsClosedEmbedding ((↑) : Subtype p -> X)
-/
theorem isClosedEmbedding_subtypeL (p : Submodule R M) (hp : IsClosed (p : Set M)) :
    Topology.IsClosedEmbedding p.subtypeL := .subtypeVal hp

@[deprecated range_subtype (since := "2026-05-06")]
/-
**Submodule.range_subtypeL** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：range_subtypeL (p : Submodule R M) : (p.subtypeL : p ->ₗ[R] M).range = p
参数：p : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
-/
theorem range_subtypeL (p : Submodule R M) : (p.subtypeL : p →ₗ[R] M).range = p :=
  Submodule.range_subtype _

@[deprecated ker_subtype (since := "2026-05-06")]
/-
**Submodule.ker_subtypeL** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：ker_subtypeL (p : Submodule R M) : (p.subtypeL : p ->ₗ[R] M).ker = ⊥
参数：p : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ker_subtype`：ker_subtype : ker p.subtype = ⊥
-/
theorem ker_subtypeL (p : Submodule R M) : (p.subtypeL : p →ₗ[R] M).ker = ⊥ :=
  Submodule.ker_subtype _

end Semiring

end Submodule

namespace ContinuousLinearMap

section Restrict

variable {R₁ R₂ R₃ : Type*} [Semiring R₁] [Semiring R₂] [Semiring R₃]
  {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
  {M₁ M₂ M₃ : Type*}
  [TopologicalSpace M₁] [AddCommMonoid M₁] [Module R₁ M₁]
  [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R₂ M₂]
  [TopologicalSpace M₃] [AddCommMonoid M₃] [Module R₃ M₃]

/-- The restriction of a linear map `f : M → M₂` to a submodule `p ⊆ M` gives a linear map
`p → M₂`. -/
@[simps!]
/-
**ContinuousLinearMap.domRestrict** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：domRestrict (f : M₁ ->SL[σ₁₂] M₂) (p : Submodule R₁ M₁) : p ->SL[σ₁₂] M₂
参数：f : M₁ ->SL[σ₁₂] M₂；p : Submodule R₁ M₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a linear map `f : M → M₂` to a submodule `p ⊆ M` gives a line
ar map
`p → M₂`.
-/
def domRestrict (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₁ M₁) : p →SL[σ₁₂] M₂ :=
  f ∘SL p.subtypeL

@[simp]
/-
**ContinuousLinearMap.toLinearMap_domRestrict** 是 Mathlib 中的一个定理，位于命名空间 `Continu
ousLinearMap`。
形式化陈述：toLinearMap_domRestrict (f : M₁ ->SL[σ₁₂] M₂) (p : Submodule R₁ M₁) : (f.d
omRestrict p).toLinearMap = f.toLinearMap.domRestrict p
参数：f : M₁ ->SL[σ₁₂] M₂；p : Submodule R₁ M₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_domRestrict (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₁ M₁) :
    (f.domRestrict p).toLinearMap = f.toLinearMap.domRestrict p :=
  rfl
/-
**ContinuousLinearMap.coe_domRestrict** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：coe_domRestrict (f : M₁ ->SL[σ₁₂] M₂) (p : Submodule R₁ M₁) : ⇑(f.domRestr
ict p) = Set.domRestrict p f
参数：f : M₁ ->SL[σ₁₂] M₂；p : Submodule R₁ M₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_domRestrict (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₁ M₁) :
    ⇑(f.domRestrict p) = Set.domRestrict p f :=
  rfl

/-- Restrict codomain of a continuous linear map. -/
/-
**ContinuousLinearMap.codRestrict** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap
`。
形式化陈述：codRestrict (f : M₁ ->SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : forall x, f x
 in p) : M₁ ->SL[σ₁₂] p where cont
参数：f : M₁ ->SL[σ₁₂] M₂；p : Submodule R₂ M₂；h : forall x, f x in p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict codomain of a continuous linear map.
-/
def codRestrict (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : ∀ x, f x ∈ p) :
    M₁ →SL[σ₁₂] p where
  cont := f.continuous.subtype_mk _
  toLinearMap := (f : M₁ →ₛₗ[σ₁₂] M₂).codRestrict p h

@[simp, norm_cast]
/-
**ContinuousLinearMap.toLinearMap_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `Continu
ousLinearMap`。
形式化陈述：toLinearMap_codRestrict (f : M₁ ->SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : f
orall x, f x in p) : (f.codRestrict p h).toLinearMap = f.toLinearMap.codRestrict
 p h
参数：f : M₁ ->SL[σ₁₂] M₂；p : Submodule R₂ M₂；h : forall x, f x in p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_codRestrict (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : ∀ x, f x ∈ p) :
    (f.codRestrict p h).toLinearMap = f.toLinearMap.codRestrict p h :=
  rfl
/-
**ContinuousLinearMap.coe_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：coe_codRestrict (f : M₁ ->SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : forall x,
 f x in p) : (f.codRestrict p h : M₁ -> p) = Set.codRestrict (f : M₁ -> M₂) p h
参数：f : M₁ ->SL[σ₁₂] M₂；p : Submodule R₂ M₂；h : forall x, f x in p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_codRestrict (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : ∀ x, f x ∈ p) :
    (f.codRestrict p h : M₁ → p) = Set.codRestrict (f : M₁ → M₂) p h :=
  rfl

@[simp]
/-
**ContinuousLinearMap.coe_codRestrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `Continuou
sLinearMap`。
形式化陈述：coe_codRestrict_apply (f : M₁ ->SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : for
all x, f x in p) (x) : (f.codRestrict p h x : M₂) = f x
参数：f : M₁ ->SL[σ₁₂] M₂；p : Submodule R₂ M₂；h : forall x, f x in p；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_codRestrict_apply (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : ∀ x, f x ∈ p) (x) :
    (f.codRestrict p h x : M₂) = f x :=
  rfl
/-
**ContinuousLinearMap.ker_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：ker_codRestrict (f : M₁ ->SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : forall x,
 f x in p) : ker (f.codRestrict p h : M₁ ->ₛₗ[σ₁₂] p) = ker (f : M₁ ->ₛₗ[σ₁₂] M₂
)
参数：f : M₁ ->SL[σ₁₂] M₂；p : Submodule R₂ M₂；h : forall x, f x in p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ker_codRestrict`：ker_codRestrict (p : Submodule R₂ M₂) (f : M 
->ₛₗ[τ₁₂] M₂) (hf) : ker (codRestrict p f hf) = ker f
-/
theorem ker_codRestrict (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : ∀ x, f x ∈ p) :
    ker (f.codRestrict p h : M₁ →ₛₗ[σ₁₂] p) = ker (f : M₁ →ₛₗ[σ₁₂] M₂) :=
  f.toLinearMap.ker_codRestrict p h

@[simp]
/-
**ContinuousLinearMap.subtypeL_comp_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `Conti
nuousLinearMap`。
形式化陈述：subtypeL_comp_codRestrict (f : M₁ ->SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h :
 forall x, f x in p) : p.subtypeL ∘SL f.codRestrict p h = f
参数：f : M₁ ->SL[σ₁₂] M₂；p : Submodule R₂ M₂；h : forall x, f x in p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtypeL_comp_codRestrict (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₂ M₂) (h : ∀ x, f x ∈ p) :
    p.subtypeL ∘SL f.codRestrict p h = f :=
  rfl

@[simp]
/-
**ContinuousLinearMap.domRestrict_comp_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `Co
ntinuousLinearMap`。
形式化陈述：domRestrict_comp_codRestrict (g : M₂ ->SL[σ₂₃] M₃) (f : M₁ ->SL[σ₁₂] M₂) (
p : Submodule R₂ M₂) (h : forall x, f x in p) : g.domRestrict p ∘SL f.codRestric
t p h = g ∘SL f
参数：g : M₂ ->SL[σ₂₃] M₃；f : M₁ ->SL[σ₁₂] M₂；p : Submodule R₂ M₂；h : forall x, f x
 in p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domRestrict_comp_codRestrict (g : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂)
    (p : Submodule R₂ M₂) (h : ∀ x, f x ∈ p) :
    g.domRestrict p ∘SL f.codRestrict p h = g ∘SL f :=
  rfl

/-- Restrict the codomain of a continuous linear map `f` to `f.range`. -/
/-
**ContinuousLinearMap.rangeRestrict** 是 Mathlib 中的一个缩写定义，位于命名空间 `ContinuousLinea
rMap`。
形式化陈述：rangeRestrict [RingHomSurjective σ₁₂] (f : M₁ ->SL[σ₁₂] M₂)
参数：f : M₁ ->SL[σ₁₂] M₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict the codomain of a continuous linear map `f` to `f.range`.
-/
abbrev rangeRestrict [RingHomSurjective σ₁₂] (f : M₁ →SL[σ₁₂] M₂) :=
  f.codRestrict (LinearMap.range (f : M₁ →ₛₗ[σ₁₂] M₂)) (LinearMap.mem_range_self _)
/-
**ContinuousLinearMap.toLinearMap_rangeRestrict** 是 Mathlib 中的一个定理，位于命名空间 `Conti
nuousLinearMap`。
形式化陈述：toLinearMap_rangeRestrict [RingHomSurjective σ₁₂] (f : M₁ ->SL[σ₁₂] M₂) : 
f.rangeRestrict.toLinearMap = f.toLinearMap.rangeRestrict
参数：f : M₁ ->SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toLinearMap_rangeRestrict [RingHomSurjective σ₁₂] (f : M₁ →SL[σ₁₂] M₂) :
    f.rangeRestrict.toLinearMap = f.toLinearMap.rangeRestrict := by simp

@[simp]
/-
**ContinuousLinearMap.coe_rangeRestrict** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLin
earMap`。
形式化陈述：coe_rangeRestrict [RingHomSurjective σ₁₂] (f : M₁ ->SL[σ₁₂] M₂) : (f.range
Restrict : M₁ -> f.range) = Set.rangeFactorization f
参数：f : M₁ ->SL[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_rangeRestrict [RingHomSurjective σ₁₂] (f : M₁ →SL[σ₁₂] M₂) :
    (f.rangeRestrict : M₁ → f.range) = Set.rangeFactorization f := rfl

/-- Restrict codomain of a continuous linear map. -/
/-
**ContinuousLinearMap.restrict** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousLinearMap`。
形式化陈述：restrict (f : M₁ ->SL[σ₁₂] M₂) {p : Submodule R₁ M₁} {q : Submodule R₂ M₂}
 (h : forall x in p, f x in q) : p ->SL[σ₁₂] q
参数：f : M₁ ->SL[σ₁₂] M₂；h : forall x in p, f x in q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict codomain of a continuous linear map.
-/
def restrict (f : M₁ →SL[σ₁₂] M₂) {p : Submodule R₁ M₁} {q : Submodule R₂ M₂}
    (h : ∀ x ∈ p, f x ∈ q) : p →SL[σ₁₂] q :=
  (f.domRestrict p).codRestrict q <| SetLike.forall.2 h

@[simp, norm_cast]
/-
**ContinuousLinearMap.toLinearMap_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
LinearMap`。
形式化陈述：toLinearMap_restrict {f : M₁ ->SL[σ₁₂] M₂} {p : Submodule R₁ M₁} {q : Subm
odule R₂ M₂} (h : forall x in p, f x in q) : (f.restrict h).toLinearMap = f.toLi
nearMap.restrict h
参数：h : forall x in p, f x in q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_restrict {f : M₁ →SL[σ₁₂] M₂} {p : Submodule R₁ M₁} {q : Submodule R₂ M₂}
    (h : ∀ x ∈ p, f x ∈ q) :
    (f.restrict h).toLinearMap = f.toLinearMap.restrict h :=
  rfl

@[simp]
/-
**ContinuousLinearMap.coe_restrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearMap`。
形式化陈述：coe_restrict_apply {f : M₁ ->SL[σ₁₂] M₂} {p : Submodule R₁ M₁} {q : Submod
ule R₂ M₂} (hf : forall x in p, f x in q) (x : p) : ↑(f.restrict hf x) = f x
参数：hf : forall x in p, f x in q；x : p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_restrict_apply {f : M₁ →SL[σ₁₂] M₂} {p : Submodule R₁ M₁} {q : Submodule R₂ M₂}
    (hf : ∀ x ∈ p, f x ∈ q) (x : p) : ↑(f.restrict hf x) = f x :=
  rfl
/-
**ContinuousLinearMap.restrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinear
Map`。
形式化陈述：restrict_apply {f : M₁ ->SL[σ₁₂] M₂} {p : Submodule R₁ M₁} {q : Submodule 
R₂ M₂} (hf : forall x in p, f x in q) (x : p) : f.restrict hf x = ⟨f x, hf x.1 x
.2⟩
参数：hf : forall x in p, f x in q；x : p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrict_apply {f : M₁ →SL[σ₁₂] M₂} {p : Submodule R₁ M₁} {q : Submodule R₂ M₂}
    (hf : ∀ x ∈ p, f x ∈ q) (x : p) : f.restrict hf x = ⟨f x, hf x.1 x.2⟩ :=
  rfl

open Set in
/-
**ContinuousLinearMap.restrict_comp** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLinearM
ap`。
形式化陈述：restrict_comp {p : Submodule R₁ M₁} {p₂ : Submodule R₂ M₂} {p₃ : Submodule
 R₃ M₃} {f : M₁ ->SL[σ₁₂] M₂} {g : M₂ ->SL[σ₂₃] M₃} (hf : MapsTo f p p₂) (hg : M
apsTo g p₂ p₃) (hfg : MapsTo (g ∘SL f) p p₃
参数：hf : MapsTo f p p₂；hg : MapsTo g p₂ p₃。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrict_comp {p : Submodule R₁ M₁} {p₂ : Submodule R₂ M₂} {p₃ : Submodule R₃ M₃}
    {f : M₁ →SL[σ₁₂] M₂} {g : M₂ →SL[σ₂₃] M₃}
    (hf : MapsTo f p p₂) (hg : MapsTo g p₂ p₃) (hfg : MapsTo (g ∘SL f) p p₃ := hg.comp hf) :
    (g ∘SL f).restrict hfg = (g.restrict hg) ∘SL (f.restrict hf) :=
  rfl
/-
**ContinuousLinearMap.subtypeL_comp_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usLinearMap`。
形式化陈述：subtypeL_comp_restrict {f : M₁ ->SL[σ₁₂] M₂} {p : Submodule R₁ M₁} {q : Su
bmodule R₂ M₂} (hf : forall x in p, f x in q) : q.subtypeL ∘SL (f.restrict hf) =
 f.domRestrict p
参数：hf : forall x in p, f x in q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtypeL_comp_restrict {f : M₁ →SL[σ₁₂] M₂} {p : Submodule R₁ M₁} {q : Submodule R₂ M₂}
    (hf : ∀ x ∈ p, f x ∈ q) : q.subtypeL ∘SL (f.restrict hf) = f.domRestrict p :=
  rfl
/-
**ContinuousLinearMap.restrict_eq_codRestrict_domRestrict** 是 Mathlib 中的一个定理，位于命
名空间 `ContinuousLinearMap`。
形式化陈述：restrict_eq_codRestrict_domRestrict {f : M₁ ->SL[σ₁₂] M₂} {p : Submodule R
₁ M₁} {q : Submodule R₂ M₂} (hf : forall x in p, f x in q) : f.restrict hf = (f.
domRestrict p).codRestrict q fun x => hf x.1 x.2
参数：hf : forall x in p, f x in q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrict_eq_codRestrict_domRestrict {f : M₁ →SL[σ₁₂] M₂} {p : Submodule R₁ M₁}
    {q : Submodule R₂ M₂} (hf : ∀ x ∈ p, f x ∈ q) :
    f.restrict hf = (f.domRestrict p).codRestrict q fun x => hf x.1 x.2 :=
  rfl
/-
**ContinuousLinearMap.restrict_eq_domRestrict_codRestrict** 是 Mathlib 中的一个定理，位于命
名空间 `ContinuousLinearMap`。
形式化陈述：restrict_eq_domRestrict_codRestrict {f : M₁ ->SL[σ₁₂] M₂} {p : Submodule R
₁ M₁} {q : Submodule R₂ M₂} (hf : forall x, f x in q) : (f.restrict fun x _ => h
f x) = (f.codRestrict q hf).domRestrict p
参数：hf : forall x, f x in q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrict_eq_domRestrict_codRestrict {f : M₁ →SL[σ₁₂] M₂} {p : Submodule R₁ M₁}
    {q : Submodule R₂ M₂} (hf : ∀ x, f x ∈ q) :
    (f.restrict fun x _ => hf x) = (f.codRestrict q hf).domRestrict p :=
  rfl

end Restrict

section

variable {R₁ R₂ R₃ : Type*} [Ring R₁] [Ring R₂]
  {σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁} [RingHomInvPair σ₁₂ σ₂₁]
  {M₁ M₂ : Type*}
  [TopologicalSpace M₁] [AddCommGroup M₁] [Module R₁ M₁]
  [TopologicalSpace M₂] [AddCommGroup M₂] [Module R₂ M₂]

/-- Given a right inverse `f₂ : M₂ →L[R] M₁` to `f₁ : M₁ →L[R] M₂`,
`projKerOfRightInverse f₁ f₂ h` is the projection `M₁ →L[R] LinearMap.ker f₁` along
`LinearMap.range f₂`. -/
/-
**ContinuousLinearMap.projKerOfRightInverse** 是 Mathlib 中的一个定义，位于命名空间 `Continuou
sLinearMap`。
形式化陈述：projKerOfRightInverse [IsTopologicalAddGroup M₁] (f₁ : M₁ ->SL[σ₁₂] M₂) (f
₂ : M₂ ->SL[σ₂₁] M₁) (h : Function.RightInverse f₂ f₁) : M₁ ->L[R₁] LinearMap.ke
r (f₁ : M₁ ->ₛₗ[σ₁₂] M₂)
参数：f₁ : M₁ ->SL[σ₁₂] M₂；f₂ : M₂ ->SL[σ₂₁] M₁；h : Function.RightInverse f₂ f₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a right inverse `f₂ : M₂ →L[R] M₁` to `f₁ : M₁ →L[R] M₂`,
`projKerOfRightInverse f₁ f₂ h` is the projection `M₁ →L[R] LinearMap.ker f₁` al
ong
`LinearMap.range f₂`.
-/
def projKerOfRightInverse [IsTopologicalAddGroup M₁] (f₁ : M₁ →SL[σ₁₂] M₂) (f₂ : M₂ →SL[σ₂₁] M₁)
    (h : Function.RightInverse f₂ f₁) : M₁ →L[R₁] LinearMap.ker (f₁ : M₁ →ₛₗ[σ₁₂] M₂) :=
  (.id R₁ M₁ - f₂ ∘SL f₁).codRestrict (LinearMap.ker f₁.toLinearMap) fun x => by simp [h (f₁ x)]

@[simp]
/-
**ContinuousLinearMap.coe_projKerOfRightInverse_apply** 是 Mathlib 中的一个定理，位于命名空间 
`ContinuousLinearMap`。
形式化陈述：coe_projKerOfRightInverse_apply [IsTopologicalAddGroup M₁] (f₁ : M₁ ->SL[σ
₁₂] M₂) (f₂ : M₂ ->SL[σ₂₁] M₁) (h : Function.RightInverse f₂ f₁) (x : M₁) : (f₁.
projKerOfRightInverse f₂ h x : M₁) = x - f₂ (f₁ x)
参数：f₁ : M₁ ->SL[σ₁₂] M₂；f₂ : M₂ ->SL[σ₂₁] M₁；h : Function.RightInverse f₂ f₁；x :
 M₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_projKerOfRightInverse_apply [IsTopologicalAddGroup M₁] (f₁ : M₁ →SL[σ₁₂] M₂)
    (f₂ : M₂ →SL[σ₂₁] M₁) (h : Function.RightInverse f₂ f₁) (x : M₁) :
    (f₁.projKerOfRightInverse f₂ h x : M₁) = x - f₂ (f₁ x) :=
  rfl

@[simp]
/-
**ContinuousLinearMap.projKerOfRightInverse_apply_idem** 是 Mathlib 中的一个定理，位于命名空间
 `ContinuousLinearMap`。
形式化陈述：projKerOfRightInverse_apply_idem [IsTopologicalAddGroup M₁] (f₁ : M₁ ->SL[
σ₁₂] M₂) (f₂ : M₂ ->SL[σ₂₁] M₁) (h : Function.RightInverse f₂ f₁) (x : f₁.ker) :
 f₁.projKerOfRightInverse f₂ h x = x
参数：f₁ : M₁ ->SL[σ₁₂] M₂；f₂ : M₂ ->SL[σ₂₁] M₁；h : Function.RightInverse f₂ f₁；x :
 f₁.ker。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.apply_val_ker`：apply_val_ker (f : M₁ ->SL[σ₁₂] M₂) (
x : f.ker) : f x = 0
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
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem projKerOfRightInverse_apply_idem [IsTopologicalAddGroup M₁] (f₁ : M₁ →SL[σ₁₂] M₂)
    (f₂ : M₂ →SL[σ₂₁] M₁) (h : Function.RightInverse f₂ f₁) (x : f₁.ker) :
    f₁.projKerOfRightInverse f₂ h x = x := by
  ext1
  simp

@[simp]
/-
**ContinuousLinearMap.projKerOfRightInverse_comp_inv** 是 Mathlib 中的一个定理，位于命名空间 `
ContinuousLinearMap`。
形式化陈述：projKerOfRightInverse_comp_inv [IsTopologicalAddGroup M₁] (f₁ : M₁ ->SL[σ₁
₂] M₂) (f₂ : M₂ ->SL[σ₂₁] M₁) (h : Function.RightInverse f₂ f₁) (y : M₂) : f₁.pr
ojKerOfRightInverse f₂ h (f₂ y) = 0
参数：f₁ : M₁ ->SL[σ₁₂] M₂；f₂ : M₂ ->SL[σ₂₁] M₁；h : Function.RightInverse f₂ f₁；y :
 M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem projKerOfRightInverse_comp_inv [IsTopologicalAddGroup M₁] (f₁ : M₁ →SL[σ₁₂] M₂)
    (f₂ : M₂ →SL[σ₂₁] M₁) (h : Function.RightInverse f₂ f₁) (y : M₂) :
    f₁.projKerOfRightInverse f₂ h (f₂ y) = 0 :=
  Subtype.ext_iff.2 <| by simp [h y]

end

end ContinuousLinearMap

