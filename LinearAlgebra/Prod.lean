/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Eric Wieser
-/
module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Group.Graph
public import Mathlib.LinearAlgebra.Span.Basic

/-! ### Products of modules

This file defines constructors for linear maps whose domains or codomains are products.

It contains theorems relating these to each other, as well as to `Submodule.prod`, `Submodule.map`,
`Submodule.comap`, `LinearMap.range`, and `LinearMap.ker`.

## Main definitions

- products in the domain:
  - `LinearMap.fst`
  - `LinearMap.snd`
  - `LinearMap.coprod`
  - `LinearMap.prod_ext`
- products in the codomain:
  - `LinearMap.inl`
  - `LinearMap.inr`
  - `LinearMap.prod`
- products in both domain and codomain:
  - `LinearMap.prodMap`
  - `LinearEquiv.prodMap`
  - `LinearEquiv.skewProd`
- product with the trivial module:
  - `LinearEquiv.prodUnique`
  - `LinearEquiv.uniqueProd`
-/

@[expose] public section


universe u v w x y z u' v' w' y'

variable {R : Type u} {K : Type u'} {M : Type v} {V : Type v'} {M₂ : Type w} {V₂ : Type w'}
variable {M₃ : Type y} {V₃ : Type y'} {M₄ : Type z} {ι : Type x}
variable {M₅ M₆ : Type*}

section Prod

namespace LinearMap

variable (S : Type*) [Semiring R] [Semiring S]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]
variable [AddCommMonoid M₅] [AddCommMonoid M₆]
variable [Module R M] [Module R M₂] [Module R M₃] [Module R M₄]
variable [Module R M₅] [Module R M₆]
variable (f : M →ₗ[R] M₂)

section

variable (R M M₂)

/-- The first projection of a product is a linear map. -/
/-
**LinearMap.fst** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：fst : M × M₂ ->ₗ[R] M where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first projection of a product is a linear map.
-/
def fst : M × M₂ →ₗ[R] M where
  toFun := Prod.fst
  map_add' _x _y := rfl
  map_smul' _x _y := rfl

/-- The second projection of a product is a linear map. -/
/-
**LinearMap.snd** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：snd : M × M₂ ->ₗ[R] M₂ where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second projection of a product is a linear map.
-/
def snd : M × M₂ →ₗ[R] M₂ where
  toFun := Prod.snd
  map_add' _x _y := rfl
  map_smul' _x _y := rfl

end

@[simp]
/-
**LinearMap.fst_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：fst_apply (x : M × M₂) : fst R M M₂ x = x.1
参数：x : M × M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_apply (x : M × M₂) : fst R M M₂ x = x.1 :=
  rfl

@[simp]
/-
**LinearMap.snd_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：snd_apply (x : M × M₂) : snd R M M₂ x = x.2
参数：x : M × M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_apply (x : M × M₂) : snd R M M₂ x = x.2 :=
  rfl
/-
**LinearMap.coe_fst** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u} {M : Type v} {M₂ : Type w} [inst : Semiring R] [inst_1 : Ad
dCommMonoid M] [inst_2 : AddCommMonoid M₂]   [inst_3 : _root_.Module R M] [inst_
4 : _root_.Module R M₂], ⇑(LinearMap.fst R M M₂) = Prod.fst
参数：LinearMap.fst R M M₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_fst : ⇑(fst R M M₂) = Prod.fst := rfl
/-
**LinearMap.coe_snd** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u} {M : Type v} {M₂ : Type w} [inst : Semiring R] [inst_1 : Ad
dCommMonoid M] [inst_2 : AddCommMonoid M₂]   [inst_3 : _root_.Module R M] [inst_
4 : _root_.Module R M₂], ⇑(LinearMap.snd R M M₂) = Prod.snd
参数：LinearMap.snd R M M₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_snd : ⇑(snd R M M₂) = Prod.snd := rfl
/-
**LinearMap.fst_surjective** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：fst_surjective : Function.Surjective (fst R M M₂)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_surjective : Function.Surjective (fst R M M₂) := fun x => ⟨(x, 0), rfl⟩
/-
**LinearMap.snd_surjective** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：snd_surjective : Function.Surjective (snd R M M₂)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_surjective : Function.Surjective (snd R M M₂) := fun x => ⟨(0, x), rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- The prod of two linear maps is a linear map. -/
@[simps]
/-
**LinearMap.prod** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：prod (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] M₃) : M ->ₗ[R] M₂ × M₃ where toFun
参数：f : M ->ₗ[R] M₂；g : M ->ₗ[R] M₃。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The prod of two linear maps is a linear map.
-/
def prod (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) : M →ₗ[R] M₂ × M₃ where
  toFun := Function.prod f g
  map_add' x y := by simp only [Function.prod_apply, Prod.mk_add_mk, map_add]
  map_smul' c x := by simp only [Function.prod_apply, Prod.smul_mk, map_smul, RingHom.id_apply]
/-
**LinearMap.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coe_prod (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] M₃) : ⇑(f.prod g) = Function.prod
 f g
参数：f : M ->ₗ[R] M₂；g : M ->ₗ[R] M₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prod (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) : ⇑(f.prod g) = Function.prod f g :=
  rfl

@[simp]
/-
**LinearMap.fst_prod** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：fst_prod (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] M₃) : (fst R M₂ M₃).comp (prod f 
g) = f
参数：f : M ->ₗ[R] M₂；g : M ->ₗ[R] M₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_prod (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) : (fst R M₂ M₃).comp (prod f g) = f := rfl

@[simp]
/-
**LinearMap.snd_prod** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：snd_prod (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] M₃) : (snd R M₂ M₃).comp (prod f 
g) = g
参数：f : M ->ₗ[R] M₂；g : M ->ₗ[R] M₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_prod (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) : (snd R M₂ M₃).comp (prod f g) = g := rfl

@[simp]
/-
**LinearMap.pair_fst_snd** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：pair_fst_snd : prod (fst R M M₂) (snd R M M₂) = LinearMap.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pair_fst_snd : prod (fst R M M₂) (snd R M M₂) = LinearMap.id := rfl
/-
**LinearMap.prod_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：prod_comp (f : M₂ ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₄) (h : M ->ₗ[R] M₂) : (f.pro
d g).comp h = (f.comp h).prod (g.comp h)
参数：f : M₂ ->ₗ[R] M₃；g : M₂ ->ₗ[R] M₄；h : M ->ₗ[R] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_comp (f : M₂ →ₗ[R] M₃) (g : M₂ →ₗ[R] M₄)
    (h : M →ₗ[R] M₂) : (f.prod g).comp h = (f.comp h).prod (g.comp h) :=
  rfl

/-- Taking the product of two maps with the same domain is equivalent to taking the product of
their codomains.

See note [bundled maps over different rings] for why separate `R` and `S` semirings are used. -/
@[simps]
/-
**LinearMap.prodEquiv** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：prodEquiv [Module S M₂] [Module S M₃] [SMulCommClass R S M₂] [SMulCommClas
s R S M₃] : ((M ->ₗ[R] M₂) × (M ->ₗ[R] M₃)) ≃ₗ[S] M ->ₗ[R] M₂ × M₃ where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taking the product of two maps with the same domain is equivalent to taking the 
product of
their codomains.

See note [bundled maps over different rings] for why separate `R` and `S` semiri
ngs are used.
-/
def prodEquiv [Module S M₂] [Module S M₃] [SMulCommClass R S M₂] [SMulCommClass R S M₃] :
    ((M →ₗ[R] M₂) × (M →ₗ[R] M₃)) ≃ₗ[S] M →ₗ[R] M₂ × M₃ where
  toFun f := f.1.prod f.2
  invFun f := ((fst _ _ _).comp f, (snd _ _ _).comp f)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

section

variable (R M M₂)

/-- The left injection into a product is a linear map. -/
/-
**LinearMap.inl** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：inl : M ->ₗ[R] M × M₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left injection into a product is a linear map.
-/
def inl : M →ₗ[R] M × M₂ :=
  prod LinearMap.id 0

/-- The right injection into a product is a linear map. -/
/-
**LinearMap.inr** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：inr : M₂ ->ₗ[R] M × M₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right injection into a product is a linear map.
-/
def inr : M₂ →ₗ[R] M × M₂ :=
  prod 0 LinearMap.id
/-
**LinearMap.range_inl** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：range_inl : range (inl R M M₂) = ker (snd R M M₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem range_inl : range (inl R M M₂) = ker (snd R M M₂) := by
  ext x
  simp only [mem_ker, mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    rfl
  · intro h
    exact ⟨x.fst, Prod.ext rfl h.symm⟩
/-
**LinearMap.ker_snd** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ker_snd : ker (snd R M M₂) = range (inl R M M₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_inl`：range_inl : range (inl R M M₂) = ker (snd R M M₂)
-/
theorem ker_snd : ker (snd R M M₂) = range (inl R M M₂) :=
  Eq.symm <| range_inl R M M₂
/-
**LinearMap.range_inr** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：range_inr : range (inr R M M₂) = ker (fst R M M₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem range_inr : range (inr R M M₂) = ker (fst R M M₂) := by
  ext x
  simp only [mem_ker, mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    rfl
  · intro h
    exact ⟨x.snd, Prod.ext h.symm rfl⟩
/-
**LinearMap.ker_fst** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ker_fst : ker (fst R M M₂) = range (inr R M M₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_inr`：range_inr : range (inr R M M₂) = ker (fst R M M₂)
-/
theorem ker_fst : ker (fst R M M₂) = range (inr R M M₂) :=
  Eq.symm <| range_inr R M M₂
/-
**LinearMap.fst_comp_inl** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ (R : Type u) (M : Type v) (M₂ : Type w) [inst : Semiring R] [inst_1 : Ad
dCommMonoid M] [inst_2 : AddCommMonoid M₂]   [inst_3 : _root_.Module R M] [inst_
4 : _root_.Module R M₂],   LinearMap.fst R M M₂ ∘ₗ LinearMap.inl R M M₂ = Linear
Map.id
参数：R : Type u；M : Type v；M₂ : Type w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem fst_comp_inl : fst R M M₂ ∘ₗ inl R M M₂ = id := rfl
/-
**LinearMap.snd_comp_inl** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ (R : Type u) (M : Type v) (M₂ : Type w) [inst : Semiring R] [inst_1 : Ad
dCommMonoid M] [inst_2 : AddCommMonoid M₂]   [inst_3 : _root_.Module R M] [inst_
4 : _root_.Module R M₂], LinearMap.snd R M M₂ ∘ₗ LinearMap.inl R M M₂ = 0
参数：R : Type u；M : Type v；M₂ : Type w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem snd_comp_inl : snd R M M₂ ∘ₗ inl R M M₂ = 0 := rfl
/-
**LinearMap.fst_comp_inr** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ (R : Type u) (M : Type v) (M₂ : Type w) [inst : Semiring R] [inst_1 : Ad
dCommMonoid M] [inst_2 : AddCommMonoid M₂]   [inst_3 : _root_.Module R M] [inst_
4 : _root_.Module R M₂], LinearMap.fst R M M₂ ∘ₗ LinearMap.inr R M M₂ = 0
参数：R : Type u；M : Type v；M₂ : Type w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem fst_comp_inr : fst R M M₂ ∘ₗ inr R M M₂ = 0 := rfl
/-
**LinearMap.snd_comp_inr** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ (R : Type u) (M : Type v) (M₂ : Type w) [inst : Semiring R] [inst_1 : Ad
dCommMonoid M] [inst_2 : AddCommMonoid M₂]   [inst_3 : _root_.Module R M] [inst_
4 : _root_.Module R M₂],   LinearMap.snd R M M₂ ∘ₗ LinearMap.inr R M M₂ = Linear
Map.id
参数：R : Type u；M : Type v；M₂ : Type w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem snd_comp_inr : snd R M M₂ ∘ₗ inr R M M₂ = id := rfl

end

@[simp]
/-
**LinearMap.coe_inl** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coe_inl : (inl R M M₂ : M -> M × M₂) = fun x => (x, 0)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inl : (inl R M M₂ : M → M × M₂) = fun x => (x, 0) :=
  rfl
/-
**LinearMap.inl_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：inl_apply (x : M) : inl R M M₂ x = (x, 0)
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inl_apply (x : M) : inl R M M₂ x = (x, 0) :=
  rfl

@[simp]
/-
**LinearMap.coe_inr** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coe_inr : (inr R M M₂ : M₂ -> M × M₂) = Prod.mk 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inr : (inr R M M₂ : M₂ → M × M₂) = Prod.mk 0 :=
  rfl
/-
**LinearMap.inr_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：inr_apply (x : M₂) : inr R M M₂ x = (0, x)
参数：x : M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inr_apply (x : M₂) : inr R M M₂ x = (0, x) :=
  rfl
/-
**LinearMap.inl_eq_prod** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：inl_eq_prod : inl R M M₂ = prod LinearMap.id 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inl_eq_prod : inl R M M₂ = prod LinearMap.id 0 :=
  rfl
/-
**LinearMap.inr_eq_prod** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：inr_eq_prod : inr R M M₂ = prod 0 LinearMap.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inr_eq_prod : inr R M M₂ = prod 0 LinearMap.id :=
  rfl
/-
**LinearMap.inl_injective** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：inl_injective : Function.Injective (inl R M M₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem inl_injective : Function.Injective (inl R M M₂) := fun _ => by simp
/-
**LinearMap.inr_injective** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：inr_injective : Function.Injective (inr R M M₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem inr_injective : Function.Injective (inr R M M₂) := fun _ => by simp

/-- The coprod function `x : M × M₂ ↦ f x.1 + g x.2` is a linear map. -/
/-
**LinearMap.coprod** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：coprod (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃) : M × M₂ ->ₗ[R] M₃
参数：f : M ->ₗ[R] M₃；g : M₂ ->ₗ[R] M₃。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coprod function `x : M × M₂ ↦ f x.1 + g x.2` is a linear map.
-/
def coprod (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) : M × M₂ →ₗ[R] M₃ :=
  f.comp (fst _ _ _) + g.comp (snd _ _ _)

@[simp]
/-
**LinearMap.coprod_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coprod_apply (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃) (x : M × M₂) : coprod f 
g x = f x.1 + g x.2
参数：f : M ->ₗ[R] M₃；g : M₂ ->ₗ[R] M₃；x : M × M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coprod_apply (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) (x : M × M₂) :
    coprod f g x = f x.1 + g x.2 :=
  rfl

@[simp]
/-
**LinearMap.coprod_inl** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coprod_inl (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃) : (coprod f g).comp (inl R
 M M₂) = f
参数：f : M ->ₗ[R] M₃；g : M₂ ->ₗ[R] M₃。
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
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coprod_inl (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) : (coprod f g).comp (inl R M M₂) = f := by
  ext; simp only [map_zero, add_zero, coprod_apply, inl_apply, comp_apply]

@[simp]
/-
**LinearMap.coprod_inr** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coprod_inr (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃) : (coprod f g).comp (inr R
 M M₂) = g
参数：f : M ->ₗ[R] M₃；g : M₂ ->ₗ[R] M₃。
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
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coprod_inr (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) : (coprod f g).comp (inr R M M₂) = g := by
  ext; simp only [map_zero, coprod_apply, inr_apply, zero_add, comp_apply]

@[simp]
/-
**LinearMap.coprod_inl_inr** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coprod_inl_inr : coprod (inl R M M₂) (inr R M M₂) = LinearMap.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coprod_inl_inr : coprod (inl R M M₂) (inr R M M₂) = LinearMap.id := by
  ext <;>
    simp only [Prod.mk_add_mk, add_zero, id_apply, coprod_apply, inl_apply, inr_apply, zero_add]
/-
**LinearMap.coprod_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coprod_zero_left (g : M₂ ->ₗ[R] M₃) : (0 : M ->ₗ[R] M₃).coprod g = g.comp 
(snd R M M₂)
参数：g : M₂ ->ₗ[R] M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem coprod_zero_left (g : M₂ →ₗ[R] M₃) : (0 : M →ₗ[R] M₃).coprod g = g.comp (snd R M M₂) :=
  zero_add _
/-
**LinearMap.coprod_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coprod_zero_right (f : M ->ₗ[R] M₃) : f.coprod (0 : M₂ ->ₗ[R] M₃) = f.comp
 (fst R M M₂)
参数：f : M ->ₗ[R] M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem coprod_zero_right (f : M →ₗ[R] M₃) : f.coprod (0 : M₂ →ₗ[R] M₃) = f.comp (fst R M M₂) :=
  add_zero _
/-
**LinearMap.comp_coprod** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：comp_coprod (f : M₃ ->ₗ[R] M₄) (g₁ : M ->ₗ[R] M₃) (g₂ : M₂ ->ₗ[R] M₃) : f.
comp (g₁.coprod g₂) = (f.comp g₁).coprod (f.comp g₂)
参数：f : M₃ ->ₗ[R] M₄；g₁ : M ->ₗ[R] M₃；g₂ : M₂ ->ₗ[R] M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearMap.map_add`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
-/
theorem comp_coprod (f : M₃ →ₗ[R] M₄) (g₁ : M →ₗ[R] M₃) (g₂ : M₂ →ₗ[R] M₃) :
    f.comp (g₁.coprod g₂) = (f.comp g₁).coprod (f.comp g₂) :=
  ext fun x => f.map_add (g₁ x.1) (g₂ x.2)
/-
**LinearMap.fst_eq_coprod** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：fst_eq_coprod : fst R M M₂ = coprod LinearMap.id 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fst_eq_coprod : fst R M M₂ = coprod LinearMap.id 0 := by ext; simp
/-
**LinearMap.snd_eq_coprod** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：snd_eq_coprod : snd R M M₂ = coprod 0 LinearMap.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem snd_eq_coprod : snd R M M₂ = coprod 0 LinearMap.id := by ext; simp

@[simp]
/-
**LinearMap.coprod_comp_prod** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coprod_comp_prod (f : M₂ ->ₗ[R] M₄) (g : M₃ ->ₗ[R] M₄) (f' : M ->ₗ[R] M₂) 
(g' : M ->ₗ[R] M₃) : (f.coprod g).comp (f'.prod g') = f.comp f' + g.comp g'
参数：f : M₂ ->ₗ[R] M₄；g : M₃ ->ₗ[R] M₄；f' : M ->ₗ[R] M₂；g' : M ->ₗ[R] M₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coprod_comp_prod (f : M₂ →ₗ[R] M₄) (g : M₃ →ₗ[R] M₄) (f' : M →ₗ[R] M₂) (g' : M →ₗ[R] M₃) :
    (f.coprod g).comp (f'.prod g') = f.comp f' + g.comp g' :=
  rfl

@[simp]
/-
**LinearMap.coprod_map_prod** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coprod_map_prod (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃) (S : Submodule R M) (
S' : Submodule R M₂) : (Submodule.prod S S').map (LinearMap.coprod f g) = S.map 
f ⊔ S'.map g
参数：f : M ->ₗ[R] M₃；g : M₂ ->ₗ[R] M₃；S : Submodule R M；S' : Submodule R M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.coe_sup`：coe_sup : ↑(p ⊔ p') = (p + p' : Set M)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image2_add`：∀ {α : Type u_2} [inst : Add α] {s t : Set α}, Set.image
2 (fun x1 x2 => x1 + x2) s t = s + t
· 使用定理 `Set.image2_image_left`：image2_image_left (f : γ -> β -> δ) (g : α -> γ) 
: image2 f (g '' s) t = image2 (fun a b => f (g a) b) s t
· 使用定理 `Set.image2_image_right`：image2_image_right (f : α -> γ -> δ) (g : β -> γ
) : image2 f s (g '' t) = image2 (fun a b => f a (g b)) s t
· 使用引理 `Set.image_prod`：image_prod : (fun x : α × β => f x.1 x.2) '' s ×ˢ t = im
age2 f s t
-/
theorem coprod_map_prod (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) (S : Submodule R M)
    (S' : Submodule R M₂) : (Submodule.prod S S').map (LinearMap.coprod f g) = S.map f ⊔ S'.map g :=
  SetLike.coe_injective <| by
    simp only [LinearMap.coprod_apply, Submodule.coe_sup, Submodule.map_coe]
    rw [← Set.image2_add, Set.image2_image_left, Set.image2_image_right]
    exact Set.image_prod fun m m₂ => f m + g m₂

@[simp]
/-
**LinearMap.coprod_comp_inl_inr** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coprod_comp_inl_inr (f : M × M₂ ->ₗ[R] M₃) : (f.comp (inl R M M₂)).coprod 
(f.comp (inr R M M₂)) = f
参数：f : M × M₂ ->ₗ[R] M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_coprod`：comp_coprod (f : M₃ ->ₗ[R] M₄) (g₁ : M ->ₗ[R] M₃)
 (g₂ : M₂ ->ₗ[R] M₃) : f.comp (g₁.coprod g₂) = (f.comp g₁).coprod (f.comp g₂)
· 使用定理 `LinearMap.coprod_inl_inr`：coprod_inl_inr : coprod (inl R M M₂) (inr R M 
M₂) = LinearMap.id
· 使用定理 `LinearMap.comp_id`：comp_id : f.comp id = f
-/
theorem coprod_comp_inl_inr (f : M × M₂ →ₗ[R] M₃) :
    (f.comp (inl R M M₂)).coprod (f.comp (inr R M M₂)) = f := by
  rw [← comp_coprod, coprod_inl_inr, comp_id]

/-- Taking the product of two maps with the same codomain is equivalent to taking the product of
their domains.

See note [bundled maps over different rings] for why separate `R` and `S` semirings are used. -/
@[simps]
/-
**LinearMap.coprodEquiv** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：coprodEquiv [Module S M₃] [SMulCommClass R S M₃] : ((M ->ₗ[R] M₃) × (M₂ ->
ₗ[R] M₃)) ≃ₗ[S] M × M₂ ->ₗ[R] M₃ where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taking the product of two maps with the same codomain is equivalent to taking th
e product of
their domains.

See note [bundled maps over different rings] for why separate `R` and `S` semiri
ngs are used.
-/
def coprodEquiv [Module S M₃] [SMulCommClass R S M₃] :
    ((M →ₗ[R] M₃) × (M₂ →ₗ[R] M₃)) ≃ₗ[S] M × M₂ →ₗ[R] M₃ where
  toFun f := f.1.coprod f.2
  invFun f := (f.comp (inl _ _ _), f.comp (inr _ _ _))
  left_inv f := by simp only [coprod_inl, coprod_inr]
  right_inv f := by simp only [← comp_coprod, comp_id, coprod_inl_inr]
  map_add' a b := by
    ext
    simp only [Prod.snd_add, add_apply, coprod_apply, Prod.fst_add, add_add_add_comm]
  map_smul' r a := by
    dsimp
    ext
    simp only [smul_add, smul_apply, coprod_apply]
/-
**LinearMap.prod_ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：prod_ext_iff {f g : M × M₂ ->ₗ[R] M₃} : f = g ↔ f.comp (inl _ _ _) = g.com
p (inl _ _ _) ∧ f.comp (inr _ _ _) = g.comp (inr _ _ _)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Prod.ext_iff`：∀ {α : Type u} {β : Type v} {x y : α × β}, x = y ↔ x.1 = y
.1 ∧ x.2 = y.2
-/
theorem prod_ext_iff {f g : M × M₂ →ₗ[R] M₃} :
    f = g ↔ f.comp (inl _ _ _) = g.comp (inl _ _ _) ∧ f.comp (inr _ _ _) = g.comp (inr _ _ _) :=
  (coprodEquiv ℕ).symm.injective.eq_iff.symm.trans Prod.ext_iff

/--
Split equality of linear maps from a product into linear maps over each component, to allow `ext`
to apply lemmas specific to `M →ₗ M₃` and `M₂ →ₗ M₃`.

See note [partially-applied ext lemmas]. -/
@[ext 1100]
/-
**LinearMap.prod_ext** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：prod_ext {f g : M × M₂ ->ₗ[R] M₃} (hl : f.comp (inl _ _ _) = g.comp (inl _
 _ _)) (hr : f.comp (inr _ _ _) = g.comp (inr _ _ _)) : f = g
参数：hl : f.comp (inl _ _ _) = g.comp (inl _ _ _)；hr : f.comp (inr _ _ _) = g.comp
 (inr _ _ _)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.prod_ext_iff`：prod_ext_iff {f g : M × M₂ ->ₗ[R] M₃} : f = g ↔ 
f.comp (inl _ _ _) = g.comp (inl _ _ _) ∧ f.comp (inr _ _ _) = g.comp (inr _ _ _
)

--- 原说明 ---
Split equality of linear maps from a product into linear maps over each componen
t, to allow `ext`
to apply lemmas specific to `M →ₗ M₃` and `M₂ →ₗ M₃`.

See note [partially-applied ext lemmas].
-/
theorem prod_ext {f g : M × M₂ →ₗ[R] M₃} (hl : f.comp (inl _ _ _) = g.comp (inl _ _ _))
    (hr : f.comp (inr _ _ _) = g.comp (inr _ _ _)) : f = g :=
  prod_ext_iff.2 ⟨hl, hr⟩

/-- `Prod.map` of two linear maps. -/
/-
**LinearMap.prodMap** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：prodMap (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₄) : M × M₂ ->ₗ[R] M₃ × M₄
参数：f : M ->ₗ[R] M₃；g : M₂ ->ₗ[R] M₄。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Prod.map` of two linear maps.
-/
def prodMap (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₄) : M × M₂ →ₗ[R] M₃ × M₄ :=
  (f.comp (fst R M M₂)).prod (g.comp (snd R M M₂))
/-
**LinearMap.coe_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coe_prodMap (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₄) : ⇑(f.prodMap g) = Prod.m
ap f g
参数：f : M ->ₗ[R] M₃；g : M₂ ->ₗ[R] M₄。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodMap (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₄) : ⇑(f.prodMap g) = Prod.map f g :=
  rfl

@[simp]
/-
**LinearMap.prodMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：prodMap_apply (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₄) (x) : f.prodMap g x = (
f x.1, g x.2)
参数：f : M ->ₗ[R] M₃；g : M₂ ->ₗ[R] M₄；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodMap_apply (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₄) (x) : f.prodMap g x = (f x.1, g x.2) :=
  rfl
/-
**LinearMap.prodMap_comap_prod** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：prodMap_comap_prod (f : M ->ₗ[R] M₂) (g : M₃ ->ₗ[R] M₄) (S : Submodule R M
₂) (S' : Submodule R M₄) : (Submodule.prod S S').comap (LinearMap.prodMap f g) =
 (S.comap f).prod (S'.comap g)
参数：f : M ->ₗ[R] M₂；g : M₃ ->ₗ[R] M₄；S : Submodule R M₂；S' : Submodule R M₄。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.preimage_prod_map_prod`：preimage_prod_map_prod (f : α -> β) (g : γ -
> δ) (s : Set β) (t : Set δ) : Prod.map f g ⁻¹' s ×ˢ t = (f ⁻¹' s) ×ˢ (g ⁻¹' t)
-/
theorem prodMap_comap_prod (f : M →ₗ[R] M₂) (g : M₃ →ₗ[R] M₄) (S : Submodule R M₂)
    (S' : Submodule R M₄) :
    (Submodule.prod S S').comap (LinearMap.prodMap f g) = (S.comap f).prod (S'.comap g) :=
  SetLike.coe_injective <| Set.preimage_prod_map_prod f g _ _
/-
**LinearMap.prodMap_map_prod** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：prodMap_map_prod (f : M ->ₗ[R] M₂) (g : M₃ ->ₗ[R] M₄) (S : Submodule R M) 
(S' : Submodule R M₃) : (Submodule.prod S S').map (LinearMap.prodMap f g) = (S.m
ap f).prod (S'.map g)
参数：f : M ->ₗ[R] M₂；g : M₃ ->ₗ[R] M₄；S : Submodule R M；S' : Submodule R M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.prodMap_image_prod`：prodMap_image_prod (f : α -> β) (g : γ -> δ) (s 
: Set α) (t : Set γ) : (Prod.map f g) '' (s ×ˢ t) = (f '' s) ×ˢ (g '' t)
-/
theorem prodMap_map_prod (f : M →ₗ[R] M₂) (g : M₃ →ₗ[R] M₄) (S : Submodule R M)
    (S' : Submodule R M₃) :
    (Submodule.prod S S').map (LinearMap.prodMap f g) = (S.map f).prod (S'.map g) :=
  SetLike.coe_injective <| Set.prodMap_image_prod f g _ _

@[simp]
/-
**LinearMap.ker_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ker_prodMap (f : M ->ₗ[R] M₂) (g : M₃ ->ₗ[R] M₄) : ker (LinearMap.prodMap 
f g) = Submodule.prod (ker f) (ker g)
参数：f : M ->ₗ[R] M₂；g : M₃ ->ₗ[R] M₄。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.prodMap_comap_prod`：prodMap_comap_prod (f : M ->ₗ[R] M₂) (g : 
M₃ ->ₗ[R] M₄) (S : Submodule R M₂) (S' : Submodule R M₄) : (Submodule.prod S S')
.comap (LinearMap.…
· 使用定理 `Submodule.prod_bot`：prod_bot : (prod ⊥ ⊥ : Submodule R (M × M')) = ⊥
-/
theorem ker_prodMap (f : M →ₗ[R] M₂) (g : M₃ →ₗ[R] M₄) :
    ker (LinearMap.prodMap f g) = Submodule.prod (ker f) (ker g) := by
  dsimp only [ker]
  rw [← prodMap_comap_prod, Submodule.prod_bot]

@[simp]
/-
**LinearMap.range_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：range_prodMap (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₄) : (f.prodMap g).range =
 f.range.prod g.range
参数：f : M ->ₗ[R] M₃；g : M₂ ->ₗ[R] M₄。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem range_prodMap (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₄) :
    (f.prodMap g).range = f.range.prod g.range := by
  ext ⟨_, _⟩; simp

@[simp]
/-
**LinearMap.prodMap_id** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：prodMap_id : (id : M ->ₗ[R] M).prodMap (id : M₂ ->ₗ[R] M₂) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodMap_id : (id : M →ₗ[R] M).prodMap (id : M₂ →ₗ[R] M₂) = id :=
  rfl

@[simp]
/-
**LinearMap.prodMap_one** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：prodMap_one : (1 : M ->ₗ[R] M).prodMap (1 : M₂ ->ₗ[R] M₂) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodMap_one : (1 : M →ₗ[R] M).prodMap (1 : M₂ →ₗ[R] M₂) = 1 :=
  rfl
/-
**LinearMap.prodMap_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：prodMap_comp (f₁₂ : M ->ₗ[R] M₂) (f₂₃ : M₂ ->ₗ[R] M₃) (g₁₂ : M₄ ->ₗ[R] M₅)
 (g₂₃ : M₅ ->ₗ[R] M₆) : f₂₃.prodMap g₂₃ ∘ₗ f₁₂.prodMap g₁₂ = (f₂₃ ∘ₗ f₁₂).prodMa
p (g₂₃ ∘ₗ g₁₂)
参数：f₁₂ : M ->ₗ[R] M₂；f₂₃ : M₂ ->ₗ[R] M₃；g₁₂ : M₄ ->ₗ[R] M₅；g₂₃ : M₅ ->ₗ[R] M₆。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodMap_comp (f₁₂ : M →ₗ[R] M₂) (f₂₃ : M₂ →ₗ[R] M₃) (g₁₂ : M₄ →ₗ[R] M₅)
    (g₂₃ : M₅ →ₗ[R] M₆) :
    f₂₃.prodMap g₂₃ ∘ₗ f₁₂.prodMap g₁₂ = (f₂₃ ∘ₗ f₁₂).prodMap (g₂₃ ∘ₗ g₁₂) :=
  rfl
/-
**LinearMap.prodMap_mul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：prodMap_mul (f₁₂ : M ->ₗ[R] M) (f₂₃ : M ->ₗ[R] M) (g₁₂ : M₂ ->ₗ[R] M₂) (g₂
₃ : M₂ ->ₗ[R] M₂) : f₂₃.prodMap g₂₃ * f₁₂.prodMap g₁₂ = (f₂₃ * f₁₂).prodMap (g₂₃
 * g₁₂)
参数：f₁₂ : M ->ₗ[R] M；f₂₃ : M ->ₗ[R] M；g₁₂ : M₂ ->ₗ[R] M₂；g₂₃ : M₂ ->ₗ[R] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodMap_mul (f₁₂ : M →ₗ[R] M) (f₂₃ : M →ₗ[R] M) (g₁₂ : M₂ →ₗ[R] M₂) (g₂₃ : M₂ →ₗ[R] M₂) :
    f₂₃.prodMap g₂₃ * f₁₂.prodMap g₁₂ = (f₂₃ * f₁₂).prodMap (g₂₃ * g₁₂) :=
  rfl
/-
**LinearMap.prodMap_add** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：prodMap_add (f₁ : M ->ₗ[R] M₃) (f₂ : M ->ₗ[R] M₃) (g₁ : M₂ ->ₗ[R] M₄) (g₂ 
: M₂ ->ₗ[R] M₄) : (f₁ + f₂).prodMap (g₁ + g₂) = f₁.prodMap g₁ + f₂.prodMap g₂
参数：f₁ : M ->ₗ[R] M₃；f₂ : M ->ₗ[R] M₃；g₁ : M₂ ->ₗ[R] M₄；g₂ : M₂ ->ₗ[R] M₄。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodMap_add (f₁ : M →ₗ[R] M₃) (f₂ : M →ₗ[R] M₃) (g₁ : M₂ →ₗ[R] M₄) (g₂ : M₂ →ₗ[R] M₄) :
    (f₁ + f₂).prodMap (g₁ + g₂) = f₁.prodMap g₁ + f₂.prodMap g₂ :=
  rfl

@[simp]
/-
**LinearMap.prodMap_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：prodMap_zero : (0 : M ->ₗ[R] M₂).prodMap (0 : M₃ ->ₗ[R] M₄) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodMap_zero : (0 : M →ₗ[R] M₂).prodMap (0 : M₃ →ₗ[R] M₄) = 0 :=
  rfl

@[simp]
/-
**LinearMap.prodMap_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：prodMap_smul [DistribMulAction S M₃] [DistribMulAction S M₄] [SMulCommClas
s R S M₃] [SMulCommClass R S M₄] (s : S) (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₄) : 
prodMap (s • f) (s • g) = s • prodMap f g
参数：s : S；f : M ->ₗ[R] M₃；g : M₂ ->ₗ[R] M₄。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodMap_smul [DistribMulAction S M₃] [DistribMulAction S M₄] [SMulCommClass R S M₃]
    [SMulCommClass R S M₄] (s : S) (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₄) :
    prodMap (s • f) (s • g) = s • prodMap f g :=
  rfl

variable (R M M₂ M₃ M₄)

/-- `LinearMap.prodMap` as a `LinearMap` -/
@[simps]
/-
**LinearMap.prodMapLinear** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：prodMapLinear [Module S M₃] [Module S M₄] [SMulCommClass R S M₃] [SMulComm
Class R S M₄] : (M ->ₗ[R] M₃) × (M₂ ->ₗ[R] M₄) ->ₗ[S] M × M₂ ->ₗ[R] M₃ × M₄ wher
e toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LinearMap.prodMap` as a `LinearMap`
-/
def prodMapLinear [Module S M₃] [Module S M₄] [SMulCommClass R S M₃] [SMulCommClass R S M₄] :
    (M →ₗ[R] M₃) × (M₂ →ₗ[R] M₄) →ₗ[S] M × M₂ →ₗ[R] M₃ × M₄ where
  toFun f := prodMap f.1 f.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `LinearMap.prodMap` as a `RingHom` -/
@[simps]
/-
**LinearMap.prodMapRingHom** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：prodMapRingHom : (M ->ₗ[R] M) × (M₂ ->ₗ[R] M₂) ->+* M × M₂ ->ₗ[R] M × M₂ w
here toFun f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.prodMap_one`：prodMap_one : (1 : M ->ₗ[R] M).prodMap (1 : M₂ ->
ₗ[R] M₂) = 1

--- 原说明 ---
`LinearMap.prodMap` as a `RingHom`
-/
def prodMapRingHom : (M →ₗ[R] M) × (M₂ →ₗ[R] M₂) →+* M × M₂ →ₗ[R] M × M₂ where
  toFun f := prodMap f.1 f.2
  map_one' := prodMap_one
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

variable {R M M₂ M₃ M₄}

section map_mul

variable {A : Type*} [NonUnitalNonAssocSemiring A] [Module R A]
variable {B : Type*} [NonUnitalNonAssocSemiring B] [Module R B]

/-
**LinearMap.inl_map_mul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：inl_map_mul (a₁ a₂ : A) : LinearMap.inl R A B (a₁ * a₂) = LinearMap.inl R 
A B a₁ * LinearMap.inl R A B a₂
参数：a₁ a₂ : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inl_map_mul (a₁ a₂ : A) :
    LinearMap.inl R A B (a₁ * a₂) = LinearMap.inl R A B a₁ * LinearMap.inl R A B a₂ :=
  Prod.ext rfl (by simp)
/-
**LinearMap.inr_map_mul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：inr_map_mul (b₁ b₂ : B) : LinearMap.inr R A B (b₁ * b₂) = LinearMap.inr R 
A B b₁ * LinearMap.inr R A B b₂
参数：b₁ b₂ : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inr_map_mul (b₁ b₂ : B) :
    LinearMap.inr R A B (b₁ * b₂) = LinearMap.inr R A B b₁ * LinearMap.inr R A B b₂ :=
  Prod.ext (by simp) rfl

end map_mul

end LinearMap

end Prod

namespace LinearMap

variable (R M M₂)
variable [CommSemiring R]
variable [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R M₂]

/-- `LinearMap.prodMap` as an `AlgHom` -/
@[simps!]
/-
**LinearMap.prodMapAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：prodMapAlgHom : Module.End R M × Module.End R M₂ ->ₐ[R] Module.End R (M × 
M₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LinearMap.prodMap` as an `AlgHom`
-/
def prodMapAlgHom : Module.End R M × Module.End R M₂ →ₐ[R] Module.End R (M × M₂) :=
  { prodMapRingHom R M M₂ with commutes' := fun _ => rfl }

end LinearMap

namespace LinearMap

open Submodule

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]
  [Module R M] [Module R M₂] [Module R M₃] [Module R M₄]

/-
**LinearMap.range_coprod** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：range_coprod (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃) : range (f.coprod g) = r
ange f ⊔ range g
参数：f : M ->ₗ[R] M₃；g : M₂ ->ₗ[R] M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem range_coprod (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) : range (f.coprod g) = range f ⊔ range g :=
  Submodule.ext fun x => by simp [mem_sup]
/-
**LinearMap.isCompl_range_inl_inr** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isCompl_range_inl_inr : IsCompl (range <| inl R M M₂) (range <| inr R M M₂
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.disjoint_def`：disjoint_def {p p' : Submodule R M} : Disjoint p
 p' ↔ forall x in p, x in p' -> x = (0 : M)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `codisjoint_iff_le_sup`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_
1 : OrderTop α] {a b : α}, Codisjoint a b ↔ ⊤ ≤ a ⊔ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isCompl_range_inl_inr : IsCompl (range <| inl R M M₂) (range <| inr R M M₂) := by
  constructor
  · rw [disjoint_def]
    rintro ⟨_, _⟩ ⟨x, hx⟩ ⟨y, hy⟩
    simp only [Prod.ext_iff, inl_apply, inr_apply] at hx hy ⊢
    exact ⟨hy.1.symm, hx.2.symm⟩
  · rw [codisjoint_iff_le_sup]
    rintro ⟨x, y⟩ -
    simp only [mem_sup, mem_range]
    refine ⟨(x, 0), ⟨x, rfl⟩, (0, y), ⟨y, rfl⟩, ?_⟩
    simp
/-
**LinearMap.sup_range_inl_inr** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：sup_range_inl_inr : (range <| inl R M M₂) ⊔ (range <| inr R M M₂) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.sup_eq_top`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Bounde
dOrder α] {x y : α}, IsCompl x y → x ⊔ y = ⊤
· 使用定理 `LinearMap.isCompl_range_inl_inr`：isCompl_range_inl_inr : IsCompl (range 
<| inl R M M₂) (range <| inr R M M₂)
-/
theorem sup_range_inl_inr : (range <| inl R M M₂) ⊔ (range <| inr R M M₂) = ⊤ :=
  IsCompl.sup_eq_top isCompl_range_inl_inr
/-
**LinearMap.disjoint_inl_inr** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：disjoint_inl_inr : Disjoint (range <| inl R M M₂) (range <| inr R M M₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem disjoint_inl_inr : Disjoint (range <| inl R M M₂) (range <| inr R M M₂) := by
  simp +contextual [disjoint_def, @eq_comm M 0]
/-
**LinearMap.map_coprod_prod** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：map_coprod_prod (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃) (p : Submodule R M) (
q : Submodule R M₂) : map (coprod f g) (p.prod q) = map f p ⊔ map g q
参数：f : M ->ₗ[R] M₃；g : M₂ ->ₗ[R] M₃；p : Submodule R M；q : Submodule R M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.coprod_map_prod`：coprod_map_prod (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ
[R] M₃) (S : Submodule R M) (S' : Submodule R M₂) : (Submodule.prod S S').map (L
inearMap.coprod…
-/
theorem map_coprod_prod (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) (p : Submodule R M)
    (q : Submodule R M₂) : map (coprod f g) (p.prod q) = map f p ⊔ map g q :=
  coprod_map_prod f g p q
/-
**LinearMap.comap_prod_prod** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：comap_prod_prod (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] M₃) (p : Submodule R M₂) (
q : Submodule R M₃) : comap (prod f g) (p.prod q) = comap f p ⊓ comap g q
参数：f : M ->ₗ[R] M₂；g : M ->ₗ[R] M₃；p : Submodule R M₂；q : Submodule R M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem comap_prod_prod (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) (p : Submodule R M₂)
    (q : Submodule R M₃) : comap (prod f g) (p.prod q) = comap f p ⊓ comap g q :=
  Submodule.ext fun _x => Iff.rfl
/-
**LinearMap.prod_eq_inf_comap** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：prod_eq_inf_comap (p : Submodule R M) (q : Submodule R M₂) : p.prod q = p.
comap (LinearMap.fst R M M₂) ⊓ q.comap (LinearMap.snd R M M₂)
参数：p : Submodule R M；q : Submodule R M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem prod_eq_inf_comap (p : Submodule R M) (q : Submodule R M₂) :
    p.prod q = p.comap (LinearMap.fst R M M₂) ⊓ q.comap (LinearMap.snd R M M₂) :=
  Submodule.ext fun _x => Iff.rfl
/-
**LinearMap.prod_eq_sup_map** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：prod_eq_sup_map (p : Submodule R M) (q : Submodule R M₂) : p.prod q = p.ma
p (LinearMap.inl R M M₂) ⊔ q.map (LinearMap.inr R M M₂)
参数：p : Submodule R M；q : Submodule R M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.map_coprod_prod`：map_coprod_prod (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ
[R] M₃) (p : Submodule R M) (q : Submodule R M₂) : map (coprod f g) (p.prod q) =
 map f p ⊔ map …
· 使用定理 `LinearMap.coprod_inl_inr`：coprod_inl_inr : coprod (inl R M M₂) (inr R M 
M₂) = LinearMap.id
· 使用定理 `Submodule.map_id`：map_id : map (LinearMap.id : M ->ₗ[R] M) p = p
-/
theorem prod_eq_sup_map (p : Submodule R M) (q : Submodule R M₂) :
    p.prod q = p.map (LinearMap.inl R M M₂) ⊔ q.map (LinearMap.inr R M M₂) := by
  rw [← map_coprod_prod, coprod_inl_inr, map_id]
/-
**LinearMap.span_inl_union_inr** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：span_inl_union_inr {s : Set M} {t : Set M₂} : span R (inl R M M₂ '' s unio
n inr R M M₂ '' t) = (span R s).prod (span R t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_union`：span_union (s t : Set M) : span R (s union t) = sp
an R s ⊔ span R t
· 使用定理 `LinearMap.prod_eq_sup_map`：prod_eq_sup_map (p : Submodule R M) (q : Subm
odule R M₂) : p.prod q = p.map (LinearMap.inl R M M₂) ⊔ q.map (LinearMap.inr R M
 M₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_image`：span_image [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂
] M₂) : span R₂ (f '' s) = map f (span R s)
-/
theorem span_inl_union_inr {s : Set M} {t : Set M₂} :
    span R (inl R M M₂ '' s ∪ inr R M M₂ '' t) = (span R s).prod (span R t) := by
  rw [span_union, prod_eq_sup_map, ← span_image, ← span_image]

@[simp]
/-
**LinearMap.ker_prod** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ker_prod (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] M₃) : ker (prod f g) = ker f ⊓ ke
r g
参数：f : M ->ₗ[R] M₂；g : M ->ₗ[R] M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.ker.eq_1`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} {M₂ 
: Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid
 M] [ins…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.prod_bot`：prod_bot : (prod ⊥ ⊥ : Submodule R (M × M')) = ⊥
· 使用定理 `LinearMap.comap_prod_prod`：comap_prod_prod (f : M ->ₗ[R] M₂) (g : M ->ₗ[
R] M₃) (p : Submodule R M₂) (q : Submodule R M₃) : comap (prod f g) (p.prod q) =
 comap f p ⊓ co…
-/
theorem ker_prod (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) : ker (prod f g) = ker f ⊓ ker g := by
  rw [ker, ← prod_bot, comap_prod_prod]; rfl
/-
**LinearMap.range_prod_le** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：range_prod_le (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] M₃) : range (prod f g) <= (r
ange f).prod (range g)
参数：f : M ->ₗ[R] M₂；g : M ->ₗ[R] M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.prod_apply`：∀ {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Ty
pe y} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M
₂] [inst_3…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem range_prod_le (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) :
    range (prod f g) ≤ (range f).prod (range g) := by
  simp only [SetLike.le_def, prod_apply, mem_range, mem_prod, exists_imp]
  rintro _ x rfl
  exact ⟨⟨x, rfl⟩, ⟨x, rfl⟩⟩
/-
**LinearMap.ker_prod_ker_le_ker_coprod** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ker_prod_ker_le_ker_coprod {M₂ : Type*} [AddCommMonoid M₂] [Module R M₂] {
M₃ : Type*} [AddCommMonoid M₃] [Module R M₃] (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃
) : (ker f).prod (ker g) <= ker (f.coprod g)
参数：f : M ->ₗ[R] M₃；g : M₂ ->ₗ[R] M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem ker_prod_ker_le_ker_coprod {M₂ : Type*} [AddCommMonoid M₂] [Module R M₂] {M₃ : Type*}
    [AddCommMonoid M₃] [Module R M₃] (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) :
    (ker f).prod (ker g) ≤ ker (f.coprod g) := by
  rintro ⟨y, z⟩
  simp +contextual
/-
**LinearMap.ker_coprod_of_disjoint_range** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ker_coprod_of_disjoint_range {M₂ : Type*} [AddCommGroup M₂] [Module R M₂] 
{M₃ : Type*} [AddCommGroup M₃] [Module R M₃] (f : M ->ₗ[R] M₃) (g : M₂ ->ₗ[R] M₃
) (hd : Disjoint (range f) (range g)) : ker (f.coprod g) = (ker f).prod (ker g)
参数：f : M ->ₗ[R] M₃；g : M₂ ->ₗ[R] M₃；hd : Disjoint (range f) (range g)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `LinearMap.ker_prod_ker_le_ker_coprod`：ker_prod_ker_le_ker_coprod {M₂ : T
ype*} [AddCommMonoid M₂] [Module R M₂] {M₃ : Type*} [AddCommMonoid M₃] [Module R
 M₃] (f : M ->ₗ[R] M₃) (g …
-/
theorem ker_coprod_of_disjoint_range {M₂ : Type*} [AddCommGroup M₂] [Module R M₂] {M₃ : Type*}
    [AddCommGroup M₃] [Module R M₃] (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃)
    (hd : Disjoint (range f) (range g)) : ker (f.coprod g) = (ker f).prod (ker g) := by
  apply le_antisymm _ (ker_prod_ker_le_ker_coprod f g)
  rintro ⟨y, z⟩ h
  simp only [mem_ker, mem_prod, coprod_apply] at h ⊢
  have : f y ∈ (range f) ⊓ (range g) := by
    simp only [true_and, mem_range, mem_inf, exists_apply_eq_apply]
    use -z
    rwa [eq_comm, map_neg, ← sub_eq_zero, sub_neg_eq_add]
  rw [hd.eq_bot, mem_bot] at this
  rw [this] at h
  simpa [this] using h

set_option backward.isDefEq.respectTransparency false in
/-- Given a linear map `f : E →ₗ[R] F` and a complement `C` of its kernel, we get a linear
equivalence between `C` and `range f`. -/
@[simps!]
/-
**LinearMap.kerComplementEquivRange** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：kerComplementEquivRange {R M M₂ : Type*} [Ring R] [AddCommGroup M] [AddCom
mGroup M₂] [Module R M] [Module R M₂] (f : M ->ₗ[R] M₂) {C : Submodule R M} (h :
 IsCompl C (LinearMap.ker f)) : C ≃ₗ[R] range f
参数：f : M ->ₗ[R] M₂；h : IsCompl C (LinearMap.ker f)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a linear map `f : E →ₗ[R] F` and a complement `C` of its kernel, we get a 
linear
equivalence between `C` and `range f`.
-/
noncomputable def kerComplementEquivRange {R M M₂ : Type*} [Ring R] [AddCommGroup M]
    [AddCommGroup M₂] [Module R M] [Module R M₂] (f : M →ₗ[R] M₂) {C : Submodule R M}
    (h : IsCompl C (LinearMap.ker f)) : C ≃ₗ[R] range f :=
  .ofBijective (codRestrict (range f) f (mem_range_self f) ∘ₗ C.subtype)
  ⟨by simpa [← ker_eq_bot, ker_codRestrict, ker_comp, ← disjoint_iff_comap_eq_bot] using h.disjoint,
   by
    rintro ⟨-, x, rfl⟩
    obtain ⟨y, z, hy, hz, rfl⟩ := codisjoint_iff_exists_add_eq.mp h.codisjoint x
    use ⟨y, hy⟩
    simpa [Subtype.ext_iff]⟩

end LinearMap

namespace Submodule

open LinearMap

variable [Semiring R]
variable [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R M₂]

/-
**Submodule.sup_eq_range** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：sup_eq_range (p q : Submodule R M) : p ⊔ q = range (p.subtype.coprod q.sub
type)
参数：p q : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sup_eq_range (p q : Submodule R M) : p ⊔ q = range (p.subtype.coprod q.subtype) :=
  Submodule.ext fun x => by simp [Submodule.mem_sup]

variable (p : Submodule R M) (q : Submodule R M₂)

@[simp]
/-
**Submodule.map_inl** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_inl : p.map (inl R M M₂) = prod p ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_inl : p.map (inl R M M₂) = prod p ⊥ := by
  ext ⟨x, y⟩
  simp only [and_left_comm, eq_comm, mem_map, Prod.mk_inj, inl_apply, mem_bot, exists_eq_left',
    mem_prod]

@[simp]
/-
**Submodule.map_inr** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：map_inr : q.map (inr R M M₂) = prod ⊥ q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_inr : q.map (inr R M M₂) = prod ⊥ q := by
  ext ⟨x, y⟩; simp [and_left_comm, eq_comm, and_comm]

@[simp]
/-
**Submodule.comap_fst** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comap_fst : p.comap (fst R M M₂) = prod p ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem comap_fst : p.comap (fst R M M₂) = prod p ⊤ := by ext ⟨x, y⟩; simp

@[simp]
/-
**Submodule.comap_snd** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comap_snd : q.comap (snd R M M₂) = prod ⊤ q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem comap_snd : q.comap (snd R M M₂) = prod ⊤ q := by ext ⟨x, y⟩; simp

@[simp]
/-
**Submodule.prod_comap_inl** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：prod_comap_inl : (prod p q).comap (inl R M M₂) = p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_comap_inl : (prod p q).comap (inl R M M₂) = p := by ext; simp

@[simp]
/-
**Submodule.prod_comap_inr** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：prod_comap_inr : (prod p q).comap (inr R M M₂) = q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_comap_inr : (prod p q).comap (inr R M M₂) = q := by ext; simp

@[simp]
/-
**Submodule.prod_map_fst** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：prod_map_fst : (prod p q).map (fst R M M₂) = p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_map_fst : (prod p q).map (fst R M M₂) = p := by
  ext x; simp [(⟨0, zero_mem _⟩ : ∃ x, x ∈ q)]

@[simp]
/-
**Submodule.prod_map_snd** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：prod_map_snd : (prod p q).map (snd R M M₂) = q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_map_snd : (prod p q).map (snd R M M₂) = q := by
  ext x; simp [(⟨0, zero_mem _⟩ : ∃ x, x ∈ p)]

@[simp]
/-
**Submodule.ker_inl** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：ker_inl : ker (inl R M M₂) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.ker.eq_1`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} {M₂ 
: Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid
 M] [ins…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.prod_bot`：prod_bot : (prod ⊥ ⊥ : Submodule R (M × M')) = ⊥
· 使用定理 `Submodule.prod_comap_inl`：prod_comap_inl : (prod p q).comap (inl R M M₂)
 = p
-/
theorem ker_inl : ker (inl R M M₂) = ⊥ := by rw [ker, ← prod_bot, prod_comap_inl]

@[simp]
/-
**Submodule.ker_inr** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：ker_inr : ker (inr R M M₂) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.ker.eq_1`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} {M₂ 
: Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid
 M] [ins…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.prod_bot`：prod_bot : (prod ⊥ ⊥ : Submodule R (M × M')) = ⊥
· 使用定理 `Submodule.prod_comap_inr`：prod_comap_inr : (prod p q).comap (inr R M M₂)
 = q
-/
theorem ker_inr : ker (inr R M M₂) = ⊥ := by rw [ker, ← prod_bot, prod_comap_inr]

@[simp]
/-
**Submodule.range_fst** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：range_fst : range (fst R M M₂) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.range_eq_map`：range_eq_map [RingHomSurjective τ₁₂] (f : M ->ₛₗ
[τ₁₂] M₂) : range f = map f ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.prod_top`：prod_top : (prod ⊤ ⊤ : Submodule R (M × M')) = ⊤
· 使用定理 `Submodule.prod_map_fst`：prod_map_fst : (prod p q).map (fst R M M₂) = p
-/
theorem range_fst : range (fst R M M₂) = ⊤ := by rw [range_eq_map, ← prod_top, prod_map_fst]

@[simp]
/-
**Submodule.range_snd** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：range_snd : range (snd R M M₂) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.range_eq_map`：range_eq_map [RingHomSurjective τ₁₂] (f : M ->ₛₗ
[τ₁₂] M₂) : range f = map f ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.prod_top`：prod_top : (prod ⊤ ⊤ : Submodule R (M × M')) = ⊤
· 使用定理 `Submodule.prod_map_snd`：prod_map_snd : (prod p q).map (snd R M M₂) = q
-/
theorem range_snd : range (snd R M M₂) = ⊤ := by rw [range_eq_map, ← prod_top, prod_map_snd]

variable (R M M₂)

/-- `M` as a submodule of `M × N`. -/
/-
**Submodule.fst** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：fst : Submodule R (M × M₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M` as a submodule of `M × N`.
-/
def fst : Submodule R (M × M₂) :=
  (⊥ : Submodule R M₂).comap (LinearMap.snd R M M₂)

/-- `M` as a submodule of `M × N` is isomorphic to `M`. -/
@[simps]
/-
**Submodule.fstEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：fstEquiv : Submodule.fst R M M₂ ≃ₗ[R] M where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M` as a submodule of `M × N` is isomorphic to `M`.
-/
def fstEquiv : Submodule.fst R M M₂ ≃ₗ[R] M where
  toFun x := x.1.1
  invFun m := ⟨⟨m, 0⟩, by aesop⟩
  map_add' := by simp
  map_smul' := by simp
  left_inv x := by aesop (add norm simp Submodule.fst)
  right_inv x := by simp
/-
**Submodule.fst_map_fst** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：fst_map_fst : (Submodule.fst R M M₂).map (LinearMap.fst R M M₂) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
-/
theorem fst_map_fst : (Submodule.fst R M M₂).map (LinearMap.fst R M M₂) = ⊤ := by
  aesop
/-
**Submodule.fst_map_snd** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：fst_map_snd : (Submodule.fst R M M₂).map (LinearMap.snd R M M₂) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem fst_map_snd : (Submodule.fst R M M₂).map (LinearMap.snd R M M₂) = ⊥ := by
  aesop (add simp fst)

/-- `N` as a submodule of `M × N`. -/
/-
**Submodule.snd** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：snd : Submodule R (M × M₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`N` as a submodule of `M × N`.
-/
def snd : Submodule R (M × M₂) :=
  (⊥ : Submodule R M).comap (LinearMap.fst R M M₂)

/-- `N` as a submodule of `M × N` is isomorphic to `N`. -/
@[simps]
/-
**Submodule.sndEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：sndEquiv : Submodule.snd R M M₂ ≃ₗ[R] M₂ where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`N` as a submodule of `M × N` is isomorphic to `N`.
-/
def sndEquiv : Submodule.snd R M M₂ ≃ₗ[R] M₂ where
  toFun x := x.1.2
  invFun n := ⟨⟨0, n⟩, by aesop⟩
  map_add' := by simp
  map_smul' := by simp
  left_inv x := by aesop (add norm simp Submodule.snd)
/-
**Submodule.snd_map_fst** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：snd_map_fst : (Submodule.snd R M M₂).map (LinearMap.fst R M M₂) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem snd_map_fst : (Submodule.snd R M M₂).map (LinearMap.fst R M M₂) = ⊥ := by
  aesop (add simp snd)
/-
**Submodule.snd_map_snd** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：snd_map_snd : (Submodule.snd R M M₂).map (LinearMap.snd R M M₂) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
-/
theorem snd_map_snd : (Submodule.snd R M M₂).map (LinearMap.snd R M M₂) = ⊤ := by
  aesop
/-
**Submodule.fst_sup_snd** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：fst_sup_snd : Submodule.fst R M M₂ ⊔ Submodule.snd R M M₂ = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
· 使用定理 `Submodule.mem_sup_left`：mem_sup_left {S T : Submodule R M} : forall {x :
 M}, x in S -> x in S ⊔ T
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.mem_comap`：mem_comap {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R₂ M₂
} : x in comap f p ↔ f x in p
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Submodule.mem_sup_right`：mem_sup_right {S T : Submodule R M} : forall {x
 : M}, x in T -> x in S ⊔ T
-/
theorem fst_sup_snd : Submodule.fst R M M₂ ⊔ Submodule.snd R M M₂ = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨m, n⟩ -
  rw [show (m, n) = (m, 0) + (0, n) by simp]
  apply Submodule.add_mem (Submodule.fst R M M₂ ⊔ Submodule.snd R M M₂)
  · exact Submodule.mem_sup_left (Submodule.mem_comap.mpr (by simp))
  · exact Submodule.mem_sup_right (Submodule.mem_comap.mpr (by simp))
/-
**Submodule.fst_inf_snd** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：fst_inf_snd : Submodule.fst R M M₂ ⊓ Submodule.snd R M M₂ = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem fst_inf_snd : Submodule.fst R M M₂ ⊓ Submodule.snd R M M₂ = ⊥ := by
  aesop
/-
**Submodule.le_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：le_prod_iff {p₁ : Submodule R M} {p₂ : Submodule R M₂} {q : Submodule R (M
 × M₂)} : q <= p₁.prod p₂ ↔ map (LinearMap.fst R M M₂) q <= p₁ ∧ map (LinearMap.
snd R M M₂) q <= p₂
参数：M × M₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem le_prod_iff {p₁ : Submodule R M} {p₂ : Submodule R M₂} {q : Submodule R (M × M₂)} :
    q ≤ p₁.prod p₂ ↔ map (LinearMap.fst R M M₂) q ≤ p₁ ∧ map (LinearMap.snd R M M₂) q ≤ p₂ := by
  constructor
  · intro h
    constructor
    · rintro x ⟨⟨y1, y2⟩, ⟨hy1, rfl⟩⟩
      exact (h hy1).1
    · rintro x ⟨⟨y1, y2⟩, ⟨hy1, rfl⟩⟩
      exact (h hy1).2
  · rintro ⟨hH, hK⟩ ⟨x1, x2⟩ h
    exact ⟨hH ⟨_, h, rfl⟩, hK ⟨_, h, rfl⟩⟩
/-
**Submodule.prod_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：prod_le_iff {p₁ : Submodule R M} {p₂ : Submodule R M₂} {q : Submodule R (M
 × M₂)} : p₁.prod p₂ <= q ↔ map (LinearMap.inl R M M₂) p₁ <= q ∧ map (LinearMap.
inr R M M₂) p₂ <= q
参数：M × M₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_inl`：map_inl : p.map (inl R M M₂) = prod p ⊥
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Submodule.map_inr`：map_inr : q.map (inr R M M₂) = prod ⊥ q
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
-/
theorem prod_le_iff {p₁ : Submodule R M} {p₂ : Submodule R M₂} {q : Submodule R (M × M₂)} :
    p₁.prod p₂ ≤ q ↔ map (LinearMap.inl R M M₂) p₁ ≤ q ∧ map (LinearMap.inr R M M₂) p₂ ≤ q := by
  constructor
  · intro h
    constructor
    · rintro _ ⟨x, hx, rfl⟩
      apply h
      exact ⟨hx, zero_mem p₂⟩
    · rintro _ ⟨x, hx, rfl⟩
      apply h
      exact ⟨zero_mem p₁, hx⟩
  · rintro ⟨hH, hK⟩ ⟨x1, x2⟩ ⟨h1, h2⟩
    have h1' : (LinearMap.inl R _ _) x1 ∈ q := by
      apply hH
      simpa using h1
    have h2' : (LinearMap.inr R _ _) x2 ∈ q := by
      apply hK
      simpa using h2
    simpa using add_mem h1' h2'
/-
**Submodule.prod_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：prod_eq_bot_iff {p₁ : Submodule R M} {p₂ : Submodule R M₂} : p₁.prod p₂ = 
⊥ ↔ p₁ = ⊥ ∧ p₂ = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GaloisConnection.le_iff_le`：le_iff_le {a : α} {b : β} : l a <= b ↔ a <= 
u b
· 使用定理 `Submodule.gc_map_comap`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} 
{M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMo
noid M] [ins…
· 使用定理 `Submodule.ker_inl`：ker_inl : ker (inl R M M₂) = ⊥
· 使用定理 `Submodule.ker_inr`：ker_inr : ker (inr R M M₂) = ⊥
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_eq_bot_iff {p₁ : Submodule R M} {p₂ : Submodule R M₂} :
    p₁.prod p₂ = ⊥ ↔ p₁ = ⊥ ∧ p₂ = ⊥ := by
  simp only [eq_bot_iff, prod_le_iff, (gc_map_comap _).le_iff_le, comap_bot, ker_inl, ker_inr]
/-
**Submodule.prod_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：prod_eq_top_iff {p₁ : Submodule R M} {p₂ : Submodule R M₂} : p₁.prod p₂ = 
⊤ ↔ p₁ = ⊤ ∧ p₂ = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Submodule.range_fst`：range_fst : range (fst R M M₂) = ⊤
· 使用定理 `Submodule.range_snd`：range_snd : range (snd R M M₂) = ⊤
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_eq_top_iff {p₁ : Submodule R M} {p₂ : Submodule R M₂} :
    p₁.prod p₂ = ⊤ ↔ p₁ = ⊤ ∧ p₂ = ⊤ := by
  simp only [eq_top_iff, le_prod_iff, map_top, range_fst, range_snd]

variable {M M₂} in
/-
**Submodule.span_prod_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：span_prod_eq {s : Set M} {t : Set M₂} (hs : 0 in s) (ht : 0 in t) : span R
 (s ×ˢ t) = (span R s).prod (span R t)
参数：hs : 0 in s；ht : 0 in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Submodule.span_prod_le`：span_prod_le (s : Set M) (t : Set M') : span R (
s ×ˢ t) <= prod (span R s) (span R t)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
-/
theorem span_prod_eq {s : Set M} {t : Set M₂} (hs : 0 ∈ s) (ht : 0 ∈ t) :
    span R (s ×ˢ t) = (span R s).prod (span R t) := by
  refine le_antisymm (span_prod_le s t) ?_
  simp [Submodule.prod_le_iff, map_span]
  grind [span_mono]

end Submodule

namespace LinearEquiv

/-- Product of modules is commutative up to linear isomorphism. -/
@[simps apply]
/-
**LinearEquiv.prodComm** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：prodComm (R M N : Type*) [Semiring R] [AddCommMonoid M] [AddCommMonoid N] 
[Module R M] [Module R N] : (M × N) ≃ₗ[R] N × M
参数：R M N : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Product of modules is commutative up to linear isomorphism.
-/
def prodComm (R M N : Type*) [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M]
    [Module R N] : (M × N) ≃ₗ[R] N × M :=
  { AddEquiv.prodComm with
    toFun := Prod.swap
    map_smul' := fun _r ⟨_m, _n⟩ => rfl }

section prodComm

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R M₂]

/-
**LinearEquiv.fst_comp_prodComm** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：fst_comp_prodComm : (LinearMap.fst R M₂ M).comp (prodComm R M M₂).toLinear
Map = (LinearMap.snd R M M₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.prod_ext`：prod_ext {f g : M × M₂ ->ₗ[R] M₃} (hl : f.comp (inl 
_ _ _) = g.comp (inl _ _ _)) (hr : f.comp (inr _ _ _) = g.comp (inr _ _ _)) : f 
= g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.prodComm_apply`：∀ (R : Type u_3) (M : Type u_4) (N : Type u_
5) [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : AddCommMonoid N]   [
inst_3 : _root_.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fst_comp_prodComm :
    (LinearMap.fst R M₂ M).comp (prodComm R M M₂).toLinearMap = (LinearMap.snd R M M₂) := by
  ext <;> simp
/-
**LinearEquiv.snd_comp_prodComm** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：snd_comp_prodComm : (LinearMap.snd R M₂ M).comp (prodComm R M M₂).toLinear
Map = (LinearMap.fst R M M₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.prod_ext`：prod_ext {f g : M × M₂ ->ₗ[R] M₃} (hl : f.comp (inl 
_ _ _) = g.comp (inl _ _ _)) (hr : f.comp (inr _ _ _) = g.comp (inr _ _ _)) : f 
= g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.prodComm_apply`：∀ (R : Type u_3) (M : Type u_4) (N : Type u_
5) [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : AddCommMonoid N]   [
inst_3 : _root_.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem snd_comp_prodComm :
    (LinearMap.snd R M₂ M).comp (prodComm R M M₂).toLinearMap = (LinearMap.fst R M M₂) := by
  ext <;> simp

@[simp]
/-
**LinearEquiv.symm_prodComm** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：symm_prodComm : (prodComm R M M₂).symm = prodComm R M₂ M
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_prodComm : (prodComm R M M₂).symm = prodComm R M₂ M := rfl

end prodComm

/-- Product of modules is associative up to linear isomorphism. -/
@[simps apply]
/-
**LinearEquiv.prodAssoc** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：prodAssoc (R M₁ M₂ M₃ : Type*) [Semiring R] [AddCommMonoid M₁] [AddCommMon
oid M₂] [AddCommMonoid M₃] [Module R M₁] [Module R M₂] [Module R M₃] : ((M₁ × M₂
) × M₃) ≃ₗ[R] (M₁ × (M₂ × M₃))
参数：R M₁ M₂ M₃ : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Product of modules is associative up to linear isomorphism.
-/
def prodAssoc (R M₁ M₂ M₃ : Type*) [Semiring R]
    [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
    [Module R M₁] [Module R M₂] [Module R M₃] : ((M₁ × M₂) × M₃) ≃ₗ[R] (M₁ × (M₂ × M₃)) :=
  { AddEquiv.prodAssoc with
    map_smul' := fun _r ⟨_m, _n⟩ => rfl }

section prodAssoc

variable {M₁ : Type*}
variable [Semiring R] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M₁] [Module R M₂] [Module R M₃]

/-
**LinearEquiv.fst_comp_prodAssoc** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：fst_comp_prodAssoc : (LinearMap.fst R M₁ (M₂ × M₃)).comp (prodAssoc R M₁ M
₂ M₃).toLinearMap = (LinearMap.fst R M₁ M₂).comp (LinearMap.fst R (M₁ × M₂) M₃)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.prod_ext`：prod_ext {f g : M × M₂ ->ₗ[R] M₃} (hl : f.comp (inl 
_ _ _) = g.comp (inl _ _ _)) (hr : f.comp (inr _ _ _) = g.comp (inr _ _ _)) : f 
= g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.prodAssoc_apply`：∀ (R : Type u_3) (M₁ : Type u_4) (M₂ : Type
 u_5) (M₃ : Type u_6) [inst : Semiring R] [inst_1 : AddCommMonoid M₁]   [inst_2 
: AddCommMonoid M…
· 使用定理 `Equiv.prodAssoc_apply`：∀ (α : Type u_9) (β : Type u_10) (γ : Type u_11) 
(p : (α × β) × γ), (Equiv.prodAssoc α β γ) p = (p.1.1, p.1.2, p.2)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fst_comp_prodAssoc :
    (LinearMap.fst R M₁ (M₂ × M₃)).comp (prodAssoc R M₁ M₂ M₃).toLinearMap =
    (LinearMap.fst R M₁ M₂).comp (LinearMap.fst R (M₁ × M₂) M₃) := by
  ext <;> simp
/-
**LinearEquiv.snd_comp_prodAssoc** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：snd_comp_prodAssoc : (LinearMap.snd R M₁ (M₂ × M₃)).comp (prodAssoc R M₁ M
₂ M₃).toLinearMap = (LinearMap.snd R M₁ M₂).prodMap (LinearMap.id : M₃ ->ₗ[R] M₃
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.prod_ext`：prod_ext {f g : M × M₂ ->ₗ[R] M₃} (hl : f.comp (inl 
_ _ _) = g.comp (inl _ _ _)) (hr : f.comp (inr _ _ _) = g.comp (inr _ _ _)) : f 
= g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.prodAssoc_apply`：∀ (R : Type u_3) (M₁ : Type u_4) (M₂ : Type
 u_5) (M₃ : Type u_6) [inst : Semiring R] [inst_1 : AddCommMonoid M₁]   [inst_2 
: AddCommMonoid M…
· 使用定理 `Equiv.prodAssoc_apply`：∀ (α : Type u_9) (β : Type u_10) (γ : Type u_11) 
(p : (α × β) × γ), (Equiv.prodAssoc α β γ) p = (p.1.1, p.1.2, p.2)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem snd_comp_prodAssoc :
    (LinearMap.snd R M₁ (M₂ × M₃)).comp (prodAssoc R M₁ M₂ M₃).toLinearMap =
    (LinearMap.snd R M₁ M₂).prodMap (LinearMap.id : M₃ →ₗ[R] M₃) := by
  ext <;> simp

end prodAssoc

section SkewSwap

variable (R M N)
variable [Semiring R]
variable [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N]

/-- The map `(x, y) ↦ (-y, x)` as a linear equivalence. -/
/-
**LinearEquiv.skewSwap** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：(R : Type u) →   (M : Type v) →     (N : Type u_3) →       [inst : Semirin
g R] →         [inst_1 : AddCommGroup M] →           [inst_2 : AddCommGroup N] →
 [inst_3 : _root_.Module R M] → [inst_4 : _root_.Module R N] → (M × N) ≃ₗ[R] N ×
 M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `(x, y) ↦ (-y, x)` as a linear equivalence.
-/
protected def skewSwap : (M × N) ≃ₗ[R] (N × M) where
  toFun x := (-x.2, x.1)
  invFun x := (x.2, -x.1)
  map_add' _ _ := by
    simp [add_comm]
  map_smul' _ _ := by
    simp
  left_inv _ := by
    simp
  right_inv _ := by
    simp

variable {R M N}

@[simp]
/-
**LinearEquiv.skewSwap_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：skewSwap_apply (x : M × N) : LinearEquiv.skewSwap R M N x = (-x.2, x.1)
参数：x : M × N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem skewSwap_apply (x : M × N) : LinearEquiv.skewSwap R M N x = (-x.2, x.1) := rfl

@[simp]
/-
**LinearEquiv.skewSwap_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：skewSwap_symm_apply (x : N × M) : (LinearEquiv.skewSwap R M N).symm x = (x
.2, -x.1)
参数：x : N × M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem skewSwap_symm_apply (x : N × M) : (LinearEquiv.skewSwap R M N).symm x = (x.2, -x.1) := rfl

end SkewSwap

section

variable (R M M₂ M₃ M₄)
variable [Semiring R]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]
variable [Module R M] [Module R M₂] [Module R M₃] [Module R M₄]

/-- Four-way commutativity of `prod`. The name matches `mul_mul_mul_comm`. -/
@[simps apply]
/-
**LinearEquiv.prodProdProdComm** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：prodProdProdComm : ((M × M₂) × M₃ × M₄) ≃ₗ[R] (M × M₃) × M₂ × M₄
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Four-way commutativity of `prod`. The name matches `mul_mul_mul_comm`.
-/
def prodProdProdComm : ((M × M₂) × M₃ × M₄) ≃ₗ[R] (M × M₃) × M₂ × M₄ :=
  { AddEquiv.prodProdProdComm M M₂ M₃ M₄ with
    toFun := fun mnmn => ((mnmn.1.1, mnmn.2.1), (mnmn.1.2, mnmn.2.2))
    invFun := fun mmnn => ((mmnn.1.1, mmnn.2.1), (mmnn.1.2, mmnn.2.2))
    map_smul' := fun _c _mnmn => rfl }

@[simp]
/-
**LinearEquiv.prodProdProdComm_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：prodProdProdComm_symm : (prodProdProdComm R M M₂ M₃ M₄).symm = prodProdPro
dComm R M M₃ M₂ M₄
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodProdProdComm_symm :
    (prodProdProdComm R M M₂ M₃ M₄).symm = prodProdProdComm R M M₃ M₂ M₄ :=
  rfl

@[simp]
/-
**LinearEquiv.prodProdProdComm_toAddEquiv** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv
`。
形式化陈述：prodProdProdComm_toAddEquiv : (prodProdProdComm R M M₂ M₃ M₄ : _ ≃+ _) = A
ddEquiv.prodProdProdComm M M₂ M₃ M₄
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemilinearEquivClass.toAddEquivClass`：∀ {F : Type u_14} {R : outParam (T
ype u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S} 
  {σ : outParam (R →+* S)}…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
-/
theorem prodProdProdComm_toAddEquiv :
    (prodProdProdComm R M M₂ M₃ M₄ : _ ≃+ _) = AddEquiv.prodProdProdComm M M₂ M₃ M₄ :=
  rfl

end

section

variable [Semiring R]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]
variable {module_M : Module R M} {module_M₂ : Module R M₂}
variable {module_M₃ : Module R M₃} {module_M₄ : Module R M₄}
variable (e₁ : M ≃ₗ[R] M₂) (e₂ : M₃ ≃ₗ[R] M₄)

/-- Product of linear equivalences; the maps come from `Equiv.prodCongr`. -/
/-
**LinearEquiv.prodCongr** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：{R : Type u} →   {M : Type v} →     {M₂ : Type w} →       {M₃ : Type y} → 
        {M₄ : Type z} →           [inst : Semiring R] →             [inst_1 : Ad
dCommMonoid M] →               [inst_2 : AddCommMonoid M₂] →                 [in
st_3 : AddCommMonoid M₃] →                   [inst_4 : AddCommMonoid M₄] →      
               {module_M : _root_.Module R M} →                       {module_M₂
 : _root_.Module R M₂} →                         {module_M₃ : _root_.Module R M₃
} →                           {module_M₄ : _root_.Module R M₄} → (M ≃ₗ[R] M₂) → 
(M₃ ≃ₗ[R] M₄) → (M × M₃) ≃ₗ[R] M₂ × M₄
参数：M ≃ₗ[R] M₂；M₃ ≃ₗ[R] M₄；M × M₃。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Product of linear equivalences; the maps come from `Equiv.prodCongr`.
-/
protected def prodCongr : (M × M₃) ≃ₗ[R] M₂ × M₄ :=
  { e₁.toAddEquiv.prodCongr e₂.toAddEquiv with
    map_smul' := fun c _x => Prod.ext (e₁.map_smulₛₗ c _) (e₂.map_smulₛₗ c _) }

@[simp]
/-
**LinearEquiv.prodCongr_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：prodCongr_symm : (e₁.prodCongr e₂).symm = e₁.symm.prodCongr e₂.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodCongr_symm : (e₁.prodCongr e₂).symm = e₁.symm.prodCongr e₂.symm :=
  rfl

@[simp]
/-
**LinearEquiv.prodCongr_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：prodCongr_apply (p) : e₁.prodCongr e₂ p = (e₁ p.1, e₂ p.2)
参数：p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodCongr_apply (p) : e₁.prodCongr e₂ p = (e₁ p.1, e₂ p.2) :=
  rfl

@[simp, norm_cast]
/-
**LinearEquiv.coe_prodCongr** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：coe_prodCongr : (e₁.prodCongr e₂ : M × M₃ ->ₗ[R] M₂ × M₄) = (e₁ : M ->ₗ[R]
 M₂).prodMap (e₂ : M₃ ->ₗ[R] M₄)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodCongr :
    (e₁.prodCongr e₂ : M × M₃ →ₗ[R] M₂ × M₄) = (e₁ : M →ₗ[R] M₂).prodMap (e₂ : M₃ →ₗ[R] M₄) :=
  rfl

end

section

variable [Semiring R]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommGroup M₄]
variable {module_M : Module R M} {module_M₂ : Module R M₂}
variable {module_M₃ : Module R M₃} {module_M₄ : Module R M₄}
variable (e₁ : M ≃ₗ[R] M₂) (e₂ : M₃ ≃ₗ[R] M₄)

/-- Equivalence given by a block lower diagonal matrix. `e₁` and `e₂` are diagonal square blocks,
  and `f` is a rectangular block below the diagonal. -/
/-
**LinearEquiv.skewProd** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：{R : Type u} →   {M : Type v} →     {M₂ : Type w} →       {M₃ : Type y} → 
        {M₄ : Type z} →           [inst : Semiring R] →             [inst_1 : Ad
dCommMonoid M] →               [inst_2 : AddCommMonoid M₂] →                 [in
st_3 : AddCommMonoid M₃] →                   [inst_4 : AddCommGroup M₄] →       
              {module_M : _root_.Module R M} →                       {module_M₂ 
: _root_.Module R M₂} →                         {module_M₃ : _root_.Module R M₃}
 →                           {module_M₄ : _root_.Module R M₄} →                 
            (M ≃ₗ[R] M₂) → (M₃ ≃ₗ[R] M₄) → (M →ₗ[R] M₄) → (M × M₃) ≃ₗ[R] M₂ × M₄
参数：M ≃ₗ[R] M₂；M₃ ≃ₗ[R] M₄；M →ₗ[R] M₄；M × M₃。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence given by a block lower diagonal matrix. `e₁` and `e₂` are diagonal s
quare blocks,
  and `f` is a rectangular block below the diagonal.
-/
protected def skewProd (f : M →ₗ[R] M₄) : (M × M₃) ≃ₗ[R] M₂ × M₄ :=
  { ((e₁ : M →ₗ[R] M₂).comp (LinearMap.fst R M M₃)).prod
      ((e₂ : M₃ →ₗ[R] M₄).comp (LinearMap.snd R M M₃) +
        f.comp (LinearMap.fst R M M₃)) with
    invFun := fun p : M₂ × M₄ => (e₁.symm p.1, e₂.symm (p.2 - f (e₁.symm p.1)))
    left_inv := fun p => by simp
    right_inv := fun p => by simp }

@[simp]
/-
**LinearEquiv.skewProd_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：skewProd_apply (f : M ->ₗ[R] M₄) (x) : e₁.skewProd e₂ f x = (e₁ x.1, e₂ x.
2 + f x.1)
参数：f : M ->ₗ[R] M₄；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem skewProd_apply (f : M →ₗ[R] M₄) (x) : e₁.skewProd e₂ f x = (e₁ x.1, e₂ x.2 + f x.1) :=
  rfl

@[simp]
/-
**LinearEquiv.skewProd_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：skewProd_symm_apply (f : M ->ₗ[R] M₄) (x) : (e₁.skewProd e₂ f).symm x = (e
₁.symm x.1, e₂.symm (x.2 - f (e₁.symm x.1)))
参数：f : M ->ₗ[R] M₄；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem skewProd_symm_apply (f : M →ₗ[R] M₄) (x) :
    (e₁.skewProd e₂ f).symm x = (e₁.symm x.1, e₂.symm (x.2 - f (e₁.symm x.1))) :=
  rfl

end

section Unique

variable [Semiring R]
variable [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R M₂] [Unique M₂]

set_option backward.isDefEq.respectTransparency false in
/-- Multiplying by the trivial module from the left does not change the structure.
This is the `LinearEquiv` version of `AddEquiv.uniqueProd`. -/
@[simps!]
/-
**LinearEquiv.uniqueProd** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：uniqueProd : (M₂ × M) ≃ₗ[R] M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplying by the trivial module from the left does not change the structure.
This is the `LinearEquiv` version of `AddEquiv.uniqueProd`.
-/
def uniqueProd : (M₂ × M) ≃ₗ[R] M :=
  AddEquiv.uniqueProd.toLinearEquiv (by simp [AddEquiv.uniqueProd])
/-
**LinearEquiv.coe_uniqueProd** 是 Mathlib 中的一个引理，位于命名空间 `LinearEquiv`。
形式化陈述：coe_uniqueProd : (uniqueProd (R
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_uniqueProd :
    (uniqueProd (R := R) (M := M) (M₂ := M₂) : (M₂ × M) ≃ M) = Equiv.uniqueProd M M₂ := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Multiplying by the trivial module from the right does not change the structure.
This is the `LinearEquiv` version of `AddEquiv.prodUnique`. -/
@[simps!]
/-
**LinearEquiv.prodUnique** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：prodUnique : (M × M₂) ≃ₗ[R] M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplying by the trivial module from the right does not change the structure.
This is the `LinearEquiv` version of `AddEquiv.prodUnique`.
-/
def prodUnique : (M × M₂) ≃ₗ[R] M :=
  AddEquiv.prodUnique.toLinearEquiv (by simp [AddEquiv.prodUnique])
/-
**LinearEquiv.coe_prodUnique** 是 Mathlib 中的一个引理，位于命名空间 `LinearEquiv`。
形式化陈述：coe_prodUnique : (prodUnique (R
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_prodUnique :
    (prodUnique (R := R) (M := M) (M₂ := M₂) : (M × M₂) ≃ M) = Equiv.prodUnique M M₂ := rfl

end Unique

end LinearEquiv

namespace LinearMap

open Submodule

variable [Ring R]
variable [AddCommGroup M] [AddCommGroup M₂] [AddCommGroup M₃]
variable [Module R M] [Module R M₂] [Module R M₃]

/-- If the union of the kernels `ker f` and `ker g` spans the domain, then the range of
`Prod f g` is equal to the product of `range f` and `range g`. -/
/-
**LinearMap.range_prod_eq** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：range_prod_eq {f : M ->ₗ[R] M₂} {g : M ->ₗ[R] M₃} (h : ker f ⊔ ker g = ⊤) 
: range (prod f g) = (range f).prod (range g)
参数：h : ker f ⊔ ker g = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LinearMap.range_prod_le`：range_prod_le (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] M
₃) : range (prod f g) <= (range f).prod (range g)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.prod_apply`：∀ {R : Type u} {M : Type v} {M₂ : Type w} {M₃ : Ty
pe y} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M
₂] [inst_3…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.sub_mem_ker_iff`：sub_mem_ker_iff {x y} : x - y in ker f ↔ f x 
= f y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `eq_sub_iff_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a =
 b - c ↔ a + c = b
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If the union of the kernels `ker f` and `ker g` spans the domain, then the range
 of
`Prod f g` is equal to the product of `range f` and `range g`.
-/
theorem range_prod_eq {f : M →ₗ[R] M₂} {g : M →ₗ[R] M₃} (h : ker f ⊔ ker g = ⊤) :
    range (prod f g) = (range f).prod (range g) := by
  refine le_antisymm (f.range_prod_le g) ?_
  simp only [SetLike.le_def, prod_apply, mem_range, mem_prod, exists_imp, and_imp,
    Prod.forall, Function.prod_apply]
  rintro _ _ x rfl y rfl
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specify `(f := f)`
  simp only [Prod.mk_inj, ← sub_mem_ker_iff (f := f)]
  have : y - x ∈ ker f ⊔ ker g := by simp only [h, mem_top]
  rcases mem_sup.1 this with ⟨x', hx', y', hy', H⟩
  refine ⟨x' + x, ?_, ?_⟩
  · rwa [add_sub_cancel_right]
  · simp [← eq_sub_iff_add_eq.1 H, map_add, mem_ker.mp hy']

end LinearMap

namespace LinearMap

section Graph

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommGroup M₃] [AddCommGroup M₄]
  [Module R M] [Module R M₂] [Module R M₃] [Module R M₄] (f : M →ₗ[R] M₂) (g : M₃ →ₗ[R] M₄)

/-- Graph of a linear map. -/
/-
**LinearMap.graph** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：graph : Submodule R (M × M₂) where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Graph of a linear map.
-/
def graph : Submodule R (M × M₂) where
  carrier := { p | p.2 = f p.1 }
  add_mem' (ha : _ = _) (hb : _ = _) := by
    change _ + _ = f (_ + _)
    rw [map_add, ha, hb]
  zero_mem' := Eq.symm (map_zero f)
  smul_mem' c x (hx : _ = _) := by
    change _ • _ = f (_ • _)
    rw [map_smul, hx]

@[simp]
/-
**LinearMap.mem_graph_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：mem_graph_iff (x : M × M₂) : x in f.graph ↔ x.2 = f x.1
参数：x : M × M₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_graph_iff (x : M × M₂) : x ∈ f.graph ↔ x.2 = f x.1 :=
  Iff.rfl
/-
**LinearMap.graph_eq_ker_coprod** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：graph_eq_ker_coprod : g.graph = ker ((-g).coprod LinearMap.id)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_neg_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a + -b 
= 0 ↔ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem graph_eq_ker_coprod : g.graph = ker ((-g).coprod LinearMap.id) := by
  ext x
  change _ = _ ↔ -g x.1 + x.2 = _
  rw [add_comm, add_neg_eq_zero]
/-
**LinearMap.graph_eq_range_prod** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：graph_eq_range_prod : f.graph = range (LinearMap.id.prod f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem graph_eq_range_prod : f.graph = range (LinearMap.id.prod f) := by
  ext x
  exact ⟨fun hx => ⟨x.1, Prod.ext rfl hx.symm⟩, fun ⟨u, hu⟩ => hu ▸ rfl⟩

end Graph

end LinearMap

section LineTest

open Set Function

variable {R S G H I : Type*}
  [Semiring R] [Semiring S] {σ : R →+* S} [RingHomSurjective σ]
  [AddCommMonoid G] [Module R G]
  [AddCommMonoid H] [Module S H]
  [AddCommMonoid I] [Module S I]

/-- **Vertical line test** for linear maps.

Let `f : G → H × I` be a linear (or semilinear) map to a product. Assume that `f` is surjective on
the first factor and that the image of `f` intersects every "vertical line" `{(h, i) | i : I}` at
most once. Then the image of `f` is the graph of some linear map `f' : H → I`. -/
/-
**LinearMap.exists_range_eq_graph** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearMap.exists_range_eq_graph {f : G ->ₛₗ[σ] H × I} (hf₁ : Surjective (P
rod.fst ∘ f)) (hf : forall g₁ g₂, (f g₁).1 = (f g₂).1 -> (f g₁).2 = (f g₂).2) : 
exists f' : H ->ₗ[S] I, LinearMap.range f = LinearMap.graph f'
参数：hf₁ : Surjective (Prod.fst ∘ f)；hf : forall g₁ g₂, (f g₁).1 = (f g₂).1 -> (f 
g₁).2 = (f g₂).2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `AddMonoidHom.exists_mrange_eq_mgraph`：∀ {G : Type u_1} {H : Type u_2} {I
 : Type u_3} [inst : AddMonoid G] [inst_1 : AddMonoid H] [inst_2 : AddMonoid I] 
  {f : G →+ H × I},   Func…
· 使用定理 `AddMonoidHom.map_add'`：∀ {M : Type u_10} {N : Type u_11} [inst : AddZero
 M] [inst_1 : AddZero N] (self : M →+ N) (x y : M),   (↑self).toFun (x + y) = (↑
self).toFun…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Prod.smul_mk`：∀ {E : Type u_8} {α : Type u_9} {β : Type u_10} [inst : SM
ul E α] [inst_1 : SMul E β] (c : E) (a : α) (b : β),   c • (a, b) = (c • a, c • 
b)
· 使用定理 `LinearMap.mem_range`：mem_range [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] 
M₂} {x} : x in range f ↔ exists y, f y = x
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
**Vertical line test** for linear maps.

Let `f : G → H × I` be a linear (or semilinear) map to a product. Assume that `f
` is surjective on
the first factor and that the image of `f` intersects every "vertical line" `{(h
, i) | i : I}` at
most once. Then the image of `f` is the graph of some linear map `f' : H → I`.
-/
lemma LinearMap.exists_range_eq_graph {f : G →ₛₗ[σ] H × I} (hf₁ : Surjective (Prod.fst ∘ f))
    (hf : ∀ g₁ g₂, (f g₁).1 = (f g₂).1 → (f g₁).2 = (f g₂).2) :
    ∃ f' : H →ₗ[S] I, LinearMap.range f = LinearMap.graph f' := by
  obtain ⟨f', hf'⟩ :=
    AddMonoidHom.exists_mrange_eq_mgraph (G := G) (H := H) (I := I) (f := f) hf₁ hf
  simp only [SetLike.ext_iff, AddMonoidHom.mem_mrange, AddMonoidHom.coe_coe,
    AddMonoidHom.mem_mgraph] at hf'
  use
  { toFun := f'.toFun
    map_add' := f'.map_add'
    map_smul' := by
      intro s h
      simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, RingHom.id_apply]
      refine (hf' (s • h, _)).mp ?_
      rw [← Prod.smul_mk, ← LinearMap.mem_range]
      apply Submodule.smul_mem
      rw [LinearMap.mem_range, hf'] }
  ext x
  simpa only [mem_range, Eq.comm, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, mem_graph_iff,
    coe_mk, AddHom.coe_mk, AddMonoidHom.coe_coe, Set.mem_range] using hf' x

/-- **Vertical line test** for linear maps.

Let `G ≤ H × I` be a submodule of a product of modules. Assume that `G` maps bijectively to the
first factor. Then `G` is the graph of some linear map `f : H →ₗ[R] I`. -/
/-
**Submodule.exists_eq_graph** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submodule.exists_eq_graph {G : Submodule S (H × I)} (hf₁ : Bijective (Prod
.fst ∘ G.subtype)) : exists f : H ->ₗ[S] I, G = LinearMap.graph f
参数：H × I；hf₁ : Bijective (Prod.fst ∘ G.subtype)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用引理 `LinearMap.exists_range_eq_graph`：LinearMap.exists_range_eq_graph {f : G 
->ₛₗ[σ] H × I} (hf₁ : Surjective (Prod.fst ∘ f)) (hf : forall g₁ g₂, (f g₁).1 = 
(f g₂).1 -> (f g₁).2 …
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f

--- 原说明 ---
**Vertical line test** for linear maps.

Let `G ≤ H × I` be a submodule of a product of modules. Assume that `G` maps bij
ectively to the
first factor. Then `G` is the graph of some linear map `f : H →ₗ[R] I`.
-/
lemma Submodule.exists_eq_graph {G : Submodule S (H × I)} (hf₁ : Bijective (Prod.fst ∘ G.subtype)) :
    ∃ f : H →ₗ[S] I, G = LinearMap.graph f := by
  simpa only [range_subtype] using LinearMap.exists_range_eq_graph hf₁.surjective
      (fun a b h ↦ congr_arg (Prod.snd ∘ G.subtype) (hf₁.injective h))

/-- **Line test** for module isomorphisms.

Let `f : G → H × I` be a linear (or semilinear) map to a product of modules. Assume that `f` is
surjective onto both factors and that the image of `f` intersects every "vertical line"
`{(h, i) | i : I}` and every "horizontal line" `{(h, i) | h : H}` at most once. Then the image of
`f` is the graph of some module isomorphism `f' : H ≃ I`. -/
/-
**LinearMap.exists_linearEquiv_eq_graph** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearMap.exists_linearEquiv_eq_graph {f : G ->ₛₗ[σ] H × I} (hf₁ : Surject
ive (Prod.fst ∘ f)) (hf₂ : Surjective (Prod.snd ∘ f)) (hf : forall g₁ g₂, (f g₁)
.1 = (f g₂).1 ↔ (f g₁).2 = (f g₂).2) : exists e : H ≃ₗ[S] I, range f = e.toLinea
rMap.graph
参数：hf₁ : Surjective (Prod.fst ∘ f)；hf₂ : Surjective (Prod.snd ∘ f)；hf : forall g
₁ g₂, (f g₁).1 = (f g₂).1 ↔ (f g₁).2 = (f g₂).2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.exists_range_eq_graph`：LinearMap.exists_range_eq_graph {f : G 
->ₛₗ[σ] H × I} (hf₁ : Surjective (Prod.fst ∘ f)) (hf : forall g₁ g₂, (f g₁).1 = 
(f g₂).1 -> (f g₁).2 …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.prodComm_apply`：∀ (R : Type u_3) (M : Type u_4) (N : Type u_
5) [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : AddCommMonoid N]   [
inst_3 : _root_.…
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `AddHom.map_add'`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [inst_
1 : Add N] (self : M →ₙ+ N) (x y : M),   self.toFun (x + y) = self.toFun x + sel
f.toF…
· 使用定理 `LinearMap.map_smul'`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring 
R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [inst_
2 : AddCo…

--- 原说明 ---
**Line test** for module isomorphisms.

Let `f : G → H × I` be a linear (or semilinear) map to a product of modules. Ass
ume that `f` is
surjective onto both factors and that the image of `f` intersects every "vertica
l line"
`{(h, i) | i : I}` and every "horizontal line" `{(h, i) | h : H}` at most once. 
Then the image of
`f` is the graph of some module isomorphism `f' : H ≃ I`.
-/
lemma LinearMap.exists_linearEquiv_eq_graph {f : G →ₛₗ[σ] H × I} (hf₁ : Surjective (Prod.fst ∘ f))
    (hf₂ : Surjective (Prod.snd ∘ f)) (hf : ∀ g₁ g₂, (f g₁).1 = (f g₂).1 ↔ (f g₁).2 = (f g₂).2) :
    ∃ e : H ≃ₗ[S] I, range f = e.toLinearMap.graph := by
  obtain ⟨e₁, he₁⟩ := f.exists_range_eq_graph hf₁ fun _ _ ↦ (hf _ _).1
  obtain ⟨e₂, he₂⟩ := ((LinearEquiv.prodComm _ _ _).toLinearMap.comp f).exists_range_eq_graph
    (by simpa) <| by simp [hf]
  have he₁₂ h i : e₁ h = i ↔ e₂ i = h := by
    simp only [SetLike.ext_iff, LinearMap.mem_graph_iff] at he₁ he₂
    rw [Eq.comm, ← he₁ (h, i), Eq.comm, ← he₂ (i, h)]
    simp only [mem_range, coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.prodComm_apply, Prod.swap_eq_iff_eq_swap, Prod.swap_prod_mk]
  exact ⟨
  { toFun := e₁
    map_smul' := e₁.map_smul'
    map_add' := e₁.map_add'
    invFun := e₂
    left_inv := fun h ↦ by rw [← he₁₂]
    right_inv := fun i ↦ by rw [he₁₂] }, he₁⟩

/-- **Goursat's lemma** for module isomorphisms.

Let `G ≤ H × I` be a submodule of a product of modules. Assume that the natural maps from `G` to
both factors are bijective. Then `G` is the graph of some module isomorphism `f : H ≃ I`. -/
/-
**Submodule.exists_equiv_eq_graph** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submodule.exists_equiv_eq_graph {G : Submodule S (H × I)} (hG₁ : Bijective
 (Prod.fst ∘ G.subtype)) (hG₂ : Bijective (Prod.snd ∘ G.subtype)) : exists e : H
 ≃ₗ[S] I, G = e.toLinearMap.graph
参数：H × I；hG₁ : Bijective (Prod.fst ∘ G.subtype)；hG₂ : Bijective (Prod.snd ∘ G.su
btype)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用引理 `LinearMap.exists_linearEquiv_eq_graph`：LinearMap.exists_linearEquiv_eq_g
raph {f : G ->ₛₗ[σ] H × I} (hf₁ : Surjective (Prod.fst ∘ f)) (hf₂ : Surjective (
Prod.snd ∘ f)) (hf : forall…
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)

--- 原说明 ---
**Goursat's lemma** for module isomorphisms.

Let `G ≤ H × I` be a submodule of a product of modules. Assume that the natural 
maps from `G` to
both factors are bijective. Then `G` is the graph of some module isomorphism `f 
: H ≃ I`.
-/
lemma Submodule.exists_equiv_eq_graph {G : Submodule S (H × I)}
    (hG₁ : Bijective (Prod.fst ∘ G.subtype)) (hG₂ : Bijective (Prod.snd ∘ G.subtype)) :
    ∃ e : H ≃ₗ[S] I, G = e.toLinearMap.graph := by
  simpa only [range_subtype] using LinearMap.exists_linearEquiv_eq_graph
    hG₁.surjective hG₂.surjective fun _ _ ↦ hG₁.injective.eq_iff.trans hG₂.injective.eq_iff.symm

end LineTest

