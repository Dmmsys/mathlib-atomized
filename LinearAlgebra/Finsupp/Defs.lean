/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Data.Finsupp.SMul

/-!
# Properties of the module `α →₀ M`

Given an `R`-module `M`, the `R`-module structure on `α →₀ M` is defined in
`Mathlib/Data/Finsupp/SMul.lean`.

In this file we define `LinearMap` versions of various maps:

* `Finsupp.lsingle a : M →ₗ[R] ι →₀ M`: `Finsupp.single a` as a linear map;
* `Finsupp.lapply a : (ι →₀ M) →ₗ[R] M`: the map `fun f ↦ f a` as a linear map;
* `Finsupp.lsubtypeDomain (s : Set α) : (α →₀ M) →ₗ[R] (s →₀ M)`: restriction to a subtype as a
  linear map;
* `Finsupp.restrictDom`: `Finsupp.filter` as a linear map to `Finsupp.supported s`;
* `Finsupp.lmapDomain`: a linear map version of `Finsupp.mapDomain`;

## Tags

function with finite support, module, linear algebra
-/

@[expose] public section

assert_not_exists Submodule

noncomputable section

open Set LinearMap

namespace Finsupp

variable {α : Type*} {M : Type*} {N : Type*} {P : Type*} {R R₂ R₃ : Type*} {S : Type*}
variable [Semiring R] [Semiring R₂] [Semiring R₃] [Semiring S]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R₂ N]
variable [AddCommMonoid P] [Module R₃ P]
variable {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}
variable {σ₂₃ : R₂ →+* R₃} {σ₃₂ : R₃ →+* R₂}
variable {σ₁₃ : R →+* R₃} {σ₃₁ : R₃ →+* R}
variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁]

section LinearEquivFunOnFinite

variable (R : Type*) {S : Type*} (M : Type*) (α : Type*)
variable [Finite α] [AddCommMonoid M] [Semiring R] [Module R M]

/-- Given `Finite α`, `linearEquivFunOnFinite R` is the natural `R`-linear equivalence between
`α →₀ β` and `α → β`. -/
@[simps apply]
/-
**Finsupp.linearEquivFunOnFinite** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：linearEquivFunOnFinite : (α ->₀ M) ≃ₗ[R] α -> M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `Finite α`, `linearEquivFunOnFinite R` is the natural `R`-linear equivalen
ce between
`α →₀ β` and `α → β`.
-/
noncomputable def linearEquivFunOnFinite : (α →₀ M) ≃ₗ[R] α → M :=
  { equivFunOnFinite with
    toFun := (⇑)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

@[simp]
/-
**Finsupp.linearEquivFunOnFinite_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：linearEquivFunOnFinite_single [DecidableEq α] (x : α) (m : M) : (linearEqu
ivFunOnFinite R M α) (single x m) = Pi.single x m
参数：x : α；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.equivFunOnFinite_single`：equivFunOnFinite_single [DecidableEq α]
 [Finite α] (x : α) (m : M) : Finsupp.equivFunOnFinite (Finsupp.single x m) = Pi
.single x m
-/
theorem linearEquivFunOnFinite_single [DecidableEq α] (x : α) (m : M) :
    (linearEquivFunOnFinite R M α) (single x m) = Pi.single x m :=
  equivFunOnFinite_single x m

@[simp]
/-
**Finsupp.linearEquivFunOnFinite_symm_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`
。
形式化陈述：linearEquivFunOnFinite_symm_single [DecidableEq α] (x : α) (m : M) : (line
arEquivFunOnFinite R M α).symm (Pi.single x m) = single x m
参数：x : α；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.equivFunOnFinite_symm_single`：equivFunOnFinite_symm_single [Deci
dableEq α] [Finite α] (x : α) (m : M) : Finsupp.equivFunOnFinite.symm (Pi.single
 x m) = Finsupp.single x m
-/
theorem linearEquivFunOnFinite_symm_single [DecidableEq α] (x : α) (m : M) :
    (linearEquivFunOnFinite R M α).symm (Pi.single x m) = single x m :=
  equivFunOnFinite_symm_single x m

@[simp]
/-
**Finsupp.linearEquivFunOnFinite_symm_coe** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：linearEquivFunOnFinite_symm_coe (f : α ->₀ M) : (linearEquivFunOnFinite R 
M α).symm f = f
参数：f : α ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
-/
theorem linearEquivFunOnFinite_symm_coe (f : α →₀ M) : (linearEquivFunOnFinite R M α).symm f = f :=
  (linearEquivFunOnFinite R M α).symm_apply_apply f

@[simp]
/-
**Finsupp.linearEquivFunOnFinite_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：linearEquivFunOnFinite_symm_apply (f : α -> M) : (linearEquivFunOnFinite R
 M α).symm f = f
参数：f : α -> M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem linearEquivFunOnFinite_symm_apply (f : α → M) : (linearEquivFunOnFinite R M α).symm f = f :=
  rfl

end LinearEquivFunOnFinite

/-- Interpret `Finsupp.single a` as a linear map. -/
/-
**Finsupp.lsingle** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：lsingle (a : α) : M ->ₗ[R] α ->₀ M
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpret `Finsupp.single a` as a linear map.
-/
def lsingle (a : α) : M →ₗ[R] α →₀ M :=
  { Finsupp.singleAddHom a with map_smul' := fun _ _ => (smul_single _ _ _).symm }

/-- Two `R`-linear maps from `Finsupp X M` which agree on each `single x y` agree everywhere. -/
/-
**Finsupp.lhom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：lhom_ext ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a b, φ (single a b) = ψ
 (single a b)) : φ = ψ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.toAddMonoidHom_injective`：toAddMonoidHom_injective : Function.
Injective (toAddMonoidHom : (M ->ₛₗ[σ] M₃) -> M ->+ M₃)
· 使用定理 `Finsupp.addHom_ext`：addHom_ext [AddZeroClass N] ⦃f g : (α ->₀ M) ->+ N⦄ 
(H : forall x y, f (single x y) = g (single x y)) : f = g

--- 原说明 ---
Two `R`-linear maps from `Finsupp X M` which agree on each `single x y` agree ev
erywhere.
-/
theorem lhom_ext ⦃φ ψ : (α →₀ M) →ₛₗ[σ₁₂] N⦄ (h : ∀ a b, φ (single a b) = ψ (single a b)) : φ = ψ :=
  LinearMap.toAddMonoidHom_injective <| addHom_ext h

/-- Two `R`-linear maps from `Finsupp X M` which agree on each `single x y` agree everywhere.

We formulate this fact using equality of linear maps `φ.comp (lsingle a)` and `ψ.comp (lsingle a)`
so that the `ext` tactic can apply a type-specific extensionality lemma to prove equality of these
maps. E.g., if `M = R`, then it suffices to verify `φ (single a 1) = ψ (single a 1)`. -/
-- The priority should be higher than `LinearMap.ext`.
@[ext high]
/-
**Finsupp.lhom_ext'** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a, φ.comp (lsingle a) 
= ψ.comp (lsingle a)) : φ = ψ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.lhom_ext`：lhom_ext ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a b
, φ (single a b) = ψ (single a b)) : φ = ψ
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
-/
theorem lhom_ext' ⦃φ ψ : (α →₀ M) →ₛₗ[σ₁₂] N⦄ (h : ∀ a, φ.comp (lsingle a) = ψ.comp (lsingle a)) :
    φ = ψ :=
  lhom_ext fun a => LinearMap.congr_fun (h a)

/-- Interpret `fun f : α →₀ M ↦ f a` as a linear map. -/
/-
**Finsupp.lapply** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：lapply (a : α) : (α ->₀ M) ->ₗ[R] M
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpret `fun f : α →₀ M ↦ f a` as a linear map.
-/
def lapply (a : α) : (α →₀ M) →ₗ[R] M :=
  { Finsupp.applyAddHom a with map_smul' := fun _ _ => rfl }
/-
**Finsupp.** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty α] [FaithfulSMul R M] : FaithfulSMul R (α →₀ M) :=
  .of_injective (Finsupp.lsingle <| Classical.arbitrary _) (Finsupp.single_injective _)

section LSubtypeDomain

variable (s : Set α)

/-- Interpret `Finsupp.subtypeDomain s` as a linear map. -/
/-
**Finsupp.lsubtypeDomain** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：lsubtypeDomain : (α ->₀ M) ->ₗ[R] s ->₀ M where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpret `Finsupp.subtypeDomain s` as a linear map.
-/
def lsubtypeDomain : (α →₀ M) →ₗ[R] s →₀ M where
  toFun := subtypeDomain fun x => x ∈ s
  map_add' _ _ := subtypeDomain_add
  map_smul' _ _ := ext fun _ => rfl
/-
**Finsupp.lsubtypeDomain_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：lsubtypeDomain_apply (f : α ->₀ M) : (lsubtypeDomain s : (α ->₀ M) ->ₗ[R] 
s ->₀ M) f = subtypeDomain (fun x => x in s) f
参数：f : α ->₀ M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lsubtypeDomain_apply (f : α →₀ M) :
    (lsubtypeDomain s : (α →₀ M) →ₗ[R] s →₀ M) f = subtypeDomain (fun x => x ∈ s) f :=
  rfl

end LSubtypeDomain

@[simp]
/-
**Finsupp.lsingle_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：lsingle_apply (a : α) (b : M) : (lsingle a : M ->ₗ[R] α ->₀ M) b = single 
a b
参数：a : α；b : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lsingle_apply (a : α) (b : M) : (lsingle a : M →ₗ[R] α →₀ M) b = single a b :=
  rfl

@[simp]
/-
**Finsupp.lapply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：lapply_apply (a : α) (f : α ->₀ M) : (lapply a : (α ->₀ M) ->ₗ[R] M) f = f
 a
参数：a : α；f : α ->₀ M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lapply_apply (a : α) (f : α →₀ M) : (lapply a : (α →₀ M) →ₗ[R] M) f = f a :=
  rfl

@[simp]
/-
**Finsupp.lapply_comp_lsingle_same** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：lapply_comp_lsingle_same (a : α) : lapply a ∘ₗ lsingle a = (.id : M ->ₗ[R]
 M)
参数：a : α。
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
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lapply_comp_lsingle_same (a : α) : lapply a ∘ₗ lsingle a = (.id : M →ₗ[R] M) := by ext; simp

@[simp]
/-
**Finsupp.lapply_comp_lsingle_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：lapply_comp_lsingle_of_ne (a a' : α) (h : a != a') : lapply a ∘ₗ lsingle a
' = (0 : M ->ₗ[R] M)
参数：a a' : α；h : a != a'。
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
· 使用定理 `Finsupp.single_eq_of_ne'`：single_eq_of_ne' (h : a != a') : (single a b :
 α ->₀ M) a' = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lapply_comp_lsingle_of_ne (a a' : α) (h : a ≠ a') :
    lapply a ∘ₗ lsingle a' = (0 : M →ₗ[R] M) := by ext; simp [h.symm]

section LMapDomain

variable {α' : Type*} {α'' : Type*} (M R)

/-- Interpret `Finsupp.mapDomain` as a linear map. -/
/-
**Finsupp.lmapDomain** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：lmapDomain (f : α -> α') : (α ->₀ M) ->ₗ[R] α' ->₀ M where toFun
参数：f : α -> α'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.mapDomain_add`：mapDomain_add {f : α -> β} : mapDomain f (v₁ + v₂
) = mapDomain f v₁ + mapDomain f v₂

--- 原说明 ---
Interpret `Finsupp.mapDomain` as a linear map.
-/
def lmapDomain (f : α → α') : (α →₀ M) →ₗ[R] α' →₀ M where
  toFun := mapDomain f
  map_add' _ _ := mapDomain_add
  map_smul' := mapDomain_smul

@[simp]
/-
**Finsupp.lmapDomain_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：lmapDomain_apply (f : α -> α') (l : α ->₀ M) : (lmapDomain M R f : (α ->₀ 
M) ->ₗ[R] α' ->₀ M) l = mapDomain f l
参数：f : α -> α'；l : α ->₀ M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lmapDomain_apply (f : α → α') (l : α →₀ M) :
    (lmapDomain M R f : (α →₀ M) →ₗ[R] α' →₀ M) l = mapDomain f l :=
  rfl
/-
**Finsupp.coe_lmapDomain** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：coe_lmapDomain (f : α -> α') : ⇑(lmapDomain M R f) = Finsupp.mapDomain f
参数：f : α -> α'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_lmapDomain (f : α → α') : ⇑(lmapDomain M R f) = Finsupp.mapDomain f :=
  rfl

@[simp]
/-
**Finsupp.lmapDomain_id** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：lmapDomain_id : (lmapDomain M R _root_.id : (α ->₀ M) ->ₗ[R] α ->₀ M) = Li
nearMap.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Finsupp.mapDomain_id`：mapDomain_id : mapDomain id v = v
-/
theorem lmapDomain_id : (lmapDomain M R _root_.id : (α →₀ M) →ₗ[R] α →₀ M) = LinearMap.id :=
  LinearMap.ext fun _ => mapDomain_id
/-
**Finsupp.lmapDomain_comp** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：lmapDomain_comp (f : α -> α') (g : α' -> α'') : lmapDomain M R (g ∘ f) = (
lmapDomain M R g).comp (lmapDomain M R f)
参数：f : α -> α'；g : α' -> α''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Finsupp.mapDomain_comp`：mapDomain_comp {f : α -> β} {g : β -> γ} : mapDo
main (g ∘ f) v = mapDomain g (mapDomain f v)
-/
theorem lmapDomain_comp (f : α → α') (g : α' → α'') :
    lmapDomain M R (g ∘ f) = (lmapDomain M R g).comp (lmapDomain M R f) :=
  LinearMap.ext fun _ => mapDomain_comp

/-- `Finsupp.mapDomain` as a `LinearEquiv`. -/
/-
**Finsupp.mapDomain.linearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp.mapDomain`。
形式化陈述：{α : Type u_1} →   (M : Type u_2) →     (R : Type u_5) →       [inst : Sem
iring R] →         [inst_1 : AddCommMonoid M] → [inst_2 : _root_.Module R M] → {
α' : Type u_9} → α ≃ α' → (α →₀ M) ≃ₗ[R] α' →₀ M
参数：M : Type u_2；R : Type u_5；α →₀ M。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`Finsupp.mapDomain` as a `LinearEquiv`.
-/
def mapDomain.linearEquiv (f : α ≃ α') : (α →₀ M) ≃ₗ[R] (α' →₀ M) where
  __ := lmapDomain M R f.toFun
  invFun := mapDomain f.symm
  left_inv _ := by
    simp [← mapDomain_comp]
  right_inv _ := by
    simp [← mapDomain_comp]
/-
**Finsupp.mapDomain.coe_linearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.mapDomain
`。
形式化陈述：∀ {α : Type u_1} (M : Type u_2) (R : Type u_5) [inst : Semiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : _root_.Module R M] {α' : Type u_9} (f : α ≃ α'),
   ⇑(Finsupp.mapDomain.linearEquiv M R f) = Finsupp.mapDomain ⇑f
参数：M : Type u_2；R : Type u_5；f : α ≃ α'；Finsupp.mapDomain.linearEquiv M R f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem mapDomain.coe_linearEquiv (f : α ≃ α') :
    ⇑(linearEquiv M R f) = mapDomain f := rfl
/-
**Finsupp.mapDomain.toLinearMap_linearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.m
apDomain`。
形式化陈述：∀ {α : Type u_1} (M : Type u_2) (R : Type u_5) [inst : Semiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : _root_.Module R M] {α' : Type u_9} (f : α ≃ α'),
   ↑(Finsupp.mapDomain.linearEquiv M R f) = Finsupp.lmapDomain M R ⇑f
参数：M : Type u_2；R : Type u_5；f : α ≃ α'；Finsupp.mapDomain.linearEquiv M R f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem mapDomain.toLinearMap_linearEquiv (f : α ≃ α') :
    (linearEquiv M R f : _ →ₗ[R] _) = lmapDomain M R f := rfl
/-
**Finsupp.mapDomain.linearEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.mapDomai
n`。
形式化陈述：∀ {α : Type u_1} (M : Type u_2) (R : Type u_5) [inst : Semiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : _root_.Module R M] {α' : Type u_9} (f : α ≃ α'),
   (Finsupp.mapDomain.linearEquiv M R f).symm = Finsupp.mapDomain.linearEquiv M 
R f.symm
参数：M : Type u_2；R : Type u_5；f : α ≃ α'；Finsupp.mapDomain.linearEquiv M R f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem mapDomain.linearEquiv_symm (f : α ≃ α') :
    (linearEquiv M R f).symm = linearEquiv M R f.symm := rfl

end LMapDomain

section LComapDomain

variable {β : Type*}

/-- Given `f : α → β` and a proof `hf` that `f` is injective, `lcomapDomain f hf` is the linear map
sending `l : β →₀ M` to the finitely supported function from `α` to `M` given by composing
`l` with `f`.

This is the linear version of `Finsupp.comapDomain`. -/
@[simps]
/-
**Finsupp.lcomapDomain** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：lcomapDomain (f : α -> β) (hf : Function.Injective f) : (β ->₀ M) ->ₗ[R] α
 ->₀ M where toFun l
参数：f : α -> β；hf : Function.Injective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `f : α → β` and a proof `hf` that `f` is injective, `lcomapDomain f hf` is
 the linear map
sending `l : β →₀ M` to the finitely supported function from `α` to `M` given by
 composing
`l` with `f`.

This is the linear version of `Finsupp.comapDomain`.
-/
def lcomapDomain (f : α → β) (hf : Function.Injective f) : (β →₀ M) →ₗ[R] α →₀ M where
  toFun l := Finsupp.comapDomain f l hf.injOn
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp
/-
**Finsupp.leftInverse_lcomapDomain_mapDomain** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`
。
形式化陈述：leftInverse_lcomapDomain_mapDomain (f : α -> β) (hf : Function.Injective f
) : Function.LeftInverse (lcomapDomain (R
参数：f : α -> β；hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.comapDomain_mapDomain`：comapDomain_mapDomain (hf : Function.Inje
ctive f) (l : α ->₀ M) : comapDomain f (mapDomain f l) hf.injOn = l
-/
theorem leftInverse_lcomapDomain_mapDomain (f : α → β) (hf : Function.Injective f) :
    Function.LeftInverse (lcomapDomain (R := R) (M := M) f hf) (mapDomain f) :=
  comapDomain_mapDomain f hf

end LComapDomain

/-- `Finsupp.mapRange` as a `LinearMap`. -/
@[simps apply]
/-
**Finsupp.mapRange.linearMap** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp.mapRange`。
形式化陈述：{α : Type u_1} →   {M : Type u_2} →     {N : Type u_3} →       {R : Type u
_5} →         {R₂ : Type u_6} →           [inst : Semiring R] →             [ins
t_1 : Semiring R₂] →               [inst_2 : AddCommMonoid M] →                 
[inst_3 : _root_.Module R M] →                   [inst_4 : AddCommMonoid N] →   
                  [inst_5 : _root_.Module R₂ N] → {σ₁₂ : R →+* R₂} → (M →ₛₗ[σ₁₂]
 N) → (α →₀ M) →ₛₗ[σ₁₂] α →₀ N
参数：M →ₛₗ[σ₁₂] N；α →₀ M。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…

--- 原说明 ---
`Finsupp.mapRange` as a `LinearMap`.
-/
def mapRange.linearMap (f : M →ₛₗ[σ₁₂] N) : (α →₀ M) →ₛₗ[σ₁₂] α →₀ N :=
  { mapRange.addMonoidHom f.toAddMonoidHom with
    toFun := (mapRange f f.map_zero : (α →₀ M) → α →₀ N)
    map_smul' := fun c v => mapRange_smul' c (σ₁₂ c) v (f.map_smulₛₗ c) }

@[simp]
/-
**Finsupp.mapRange.linearMap_id** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.mapRange`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} {R : Type u_5} [inst : Semiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : _root_.Module R M], Finsupp.mapRange.linearMap L
inearMap.id = LinearMap.id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Finsupp.mapRange_id`：mapRange_id (g : α ->₀ M) : mapRange id rfl g = g
-/
theorem mapRange.linearMap_id :
    mapRange.linearMap LinearMap.id = (LinearMap.id : (α →₀ M) →ₗ[R] _) :=
  LinearMap.ext mapRange_id
/-
**Finsupp.mapRange.linearMap_comp** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.mapRange`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} {N : Type u_3} {P : Type u_4} {R : Type u_
5} {R₂ : Type u_6} {R₃ : Type u_7}   [inst : Semiring R] [inst_1 : Semiring R₂] 
[inst_2 : Semiring R₃] [inst_3 : AddCommMonoid M]   [inst_4 : _root_.Module R M]
 [inst_5 : AddCommMonoid N] [inst_6 : _root_.Module R₂ N] [inst_7 : AddCommMonoi
d P]   [inst_8 : _root_.Module R₃ P] {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R
 →+* R₃}   [inst_9 : RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] (f : N →ₛₗ[σ₂₃] P) (f₂ : M →
ₛₗ[σ₁₂] N),   Finsupp.mapRange.linearMap (f ∘ₛₗ f₂) = Finsupp.mapRange.linearMap
 f ∘ₛₗ Finsupp.mapRange.linearMap f₂
参数：f : N →ₛₗ[σ₂₃] P；f₂ : M →ₛₗ[σ₁₂] N；f ∘ₛₗ f₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Finsupp.mapRange_comp`：mapRange_comp (f : N -> O) (hf : f 0 = 0) (f₂ : M
 -> N) (hf₂ : f₂ 0 = 0) (h : (f ∘ f₂) 0 = 0) (g : α ->₀ M) : mapRange (f ∘ f₂) h
 g = mapRan…
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
-/
theorem mapRange.linearMap_comp (f : N →ₛₗ[σ₂₃] P) (f₂ : M →ₛₗ[σ₁₂] N) :
    (mapRange.linearMap (f.comp f₂) : (α →₀ _) →ₛₗ[σ₁₃] _) =
      (mapRange.linearMap f).comp (mapRange.linearMap f₂) :=
  LinearMap.ext <| mapRange_comp f f.map_zero f₂ f₂.map_zero (comp f f₂).map_zero

@[simp]
/-
**Finsupp.mapRange.linearMap_toAddMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.m
apRange`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} {N : Type u_3} {R : Type u_5} {R₂ : Type u
_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M] [ins
t_3 : _root_.Module R M] [inst_4 : AddCommMonoid N] [inst_5 : _root_.Module R₂ N
]   {σ₁₂ : R →+* R₂} (f : M →ₛₗ[σ₁₂] N),   (Finsupp.mapRange.linearMap f).toAddM
onoidHom = Finsupp.mapRange.addMonoidHom f.toAddMonoidHom
参数：f : M →ₛₗ[σ₁₂] N；Finsupp.mapRange.linearMap f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
-/
theorem mapRange.linearMap_toAddMonoidHom (f : M →ₛₗ[σ₁₂] N) :
    (mapRange.linearMap f).toAddMonoidHom =
      (mapRange.addMonoidHom f.toAddMonoidHom : (α →₀ M) →+ _) :=
  AddMonoidHom.ext fun _ => rfl

section Equiv

variable [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
variable [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₃₂ σ₂₃]
variable [RingHomInvPair σ₁₃ σ₃₁] [RingHomInvPair σ₃₁ σ₁₃]

/-- `Finsupp.mapRange` as a `LinearEquiv`. -/
@[simps apply]
/-
**Finsupp.mapRange.linearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp.mapRange`。
形式化陈述：{α : Type u_1} →   {M : Type u_2} →     {N : Type u_3} →       {R : Type u
_5} →         {R₂ : Type u_6} →           [inst : Semiring R] →             [ins
t_1 : Semiring R₂] →               [inst_2 : AddCommMonoid M] →                 
[inst_3 : _root_.Module R M] →                   [inst_4 : AddCommMonoid N] →   
                  [inst_5 : _root_.Module R₂ N] →                       {σ₁₂ : R
 →+* R₂} →                         {σ₂₁ : R₂ →+* R} →                           
[inst_6 : RingHomInvPair σ₁₂ σ₂₁] →                             [inst_7 : RingHo
mInvPair σ₂₁ σ₁₂] → (M ≃ₛₗ[σ₁₂] N) → (α →₀ M) ≃ₛₗ[σ₁₂] α →₀ N
参数：M ≃ₛₗ[σ₁₂] N；α →₀ M。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.map_zero`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M₂
 : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst_…

--- 原说明 ---
`Finsupp.mapRange` as a `LinearEquiv`.
-/
def mapRange.linearEquiv (e : M ≃ₛₗ[σ₁₂] N) : (α →₀ M) ≃ₛₗ[σ₁₂] α →₀ N :=
  { mapRange.linearMap e.toLinearMap,
    mapRange.addEquiv e.toAddEquiv with
    toFun := mapRange e e.map_zero
    invFun := mapRange e.symm e.symm.map_zero }

@[simp]
/-
**Finsupp.mapRange.linearEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.mapRange`
。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} {R : Type u_5} [inst : Semiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : _root_.Module R M], Finsupp.mapRange.linearEquiv
 (LinearEquiv.refl R M) = LinearEquiv.refl R (α →₀ M)
参数：LinearEquiv.refl R M；α →₀ M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `Finsupp.mapRange_id`：mapRange_id (g : α ->₀ M) : mapRange id rfl g = g
-/
theorem mapRange.linearEquiv_refl :
    mapRange.linearEquiv (LinearEquiv.refl R M) = LinearEquiv.refl R (α →₀ M) :=
  LinearEquiv.ext mapRange_id
/-
**Finsupp.mapRange.linearEquiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.mapRange
`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} {N : Type u_3} {P : Type u_4} {R : Type u_
5} {R₂ : Type u_6} {R₃ : Type u_7}   [inst : Semiring R] [inst_1 : Semiring R₂] 
[inst_2 : Semiring R₃] [inst_3 : AddCommMonoid M]   [inst_4 : _root_.Module R M]
 [inst_5 : AddCommMonoid N] [inst_6 : _root_.Module R₂ N] [inst_7 : AddCommMonoi
d P]   [inst_8 : _root_.Module R₃ P] {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} {σ₂₃ : R₂
 →+* R₃} {σ₃₂ : R₃ →+* R₂} {σ₁₃ : R →+* R₃}   {σ₃₁ : R₃ →+* R} [inst_9 : RingHom
CompTriple σ₁₂ σ₂₃ σ₁₃] [inst_10 : RingHomCompTriple σ₃₂ σ₂₁ σ₃₁]   [inst_11 : R
ingHomInvPair σ₁₂ σ₂₁] [inst_12 : RingHomInvPair σ₂₁ σ₁₂] [inst_13 : RingHomInvP
air σ₂₃ σ₃₂]   [inst_14 : RingHomInvPair σ₃₂ σ₂₃] [inst_15 : RingHomInvPair σ₁₃ 
σ₃₁] [inst_16 : RingHomInvPair σ₃₁ σ₁₃]   (f : M ≃ₛₗ[σ₁₂] N) (f₂ : N ≃ₛₗ[σ₂₃] P)
,   Finsupp.mapRange.linearEquiv (f.trans f₂) = (Finsupp.mapRange.linearEquiv f)
.trans (Finsupp.mapRange.linearEquiv f₂)
参数：f : M ≃ₛₗ[σ₁₂] N；f₂ : N ≃ₛₗ[σ₂₃] P；f.trans f₂；Finsupp.mapRange.linearEquiv f；
Finsupp.mapRange.linearEquiv f₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `Finsupp.mapRange_comp`：mapRange_comp (f : N -> O) (hf : f 0 = 0) (f₂ : M
 -> N) (hf₂ : f₂ 0 = 0) (h : (f ∘ f₂) 0 = 0) (g : α ->₀ M) : mapRange (f ∘ f₂) h
 g = mapRan…
· 使用定理 `LinearEquiv.map_zero`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M₂
 : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst_…
-/
theorem mapRange.linearEquiv_trans (f : M ≃ₛₗ[σ₁₂] N) (f₂ : N ≃ₛₗ[σ₂₃] P) :
    (mapRange.linearEquiv (f.trans f₂) : (α →₀ _) ≃ₛₗ[σ₁₃] _) =
      (mapRange.linearEquiv f).trans (mapRange.linearEquiv f₂) :=
  LinearEquiv.ext <| mapRange_comp f₂ f₂.map_zero f f.map_zero (f.trans f₂).map_zero

@[simp]
/-
**Finsupp.mapRange.linearEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.mapRange`
。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} {N : Type u_3} {R : Type u_5} {R₂ : Type u
_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M] [ins
t_3 : _root_.Module R M] [inst_4 : AddCommMonoid N] [inst_5 : _root_.Module R₂ N
]   {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} [inst_6 : RingHomInvPair σ₁₂ σ₂₁] [inst_7 
: RingHomInvPair σ₂₁ σ₁₂]   (f : M ≃ₛₗ[σ₁₂] N), (Finsupp.mapRange.linearEquiv f)
.symm = Finsupp.mapRange.linearEquiv f.symm
参数：f : M ≃ₛₗ[σ₁₂] N；Finsupp.mapRange.linearEquiv f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
-/
theorem mapRange.linearEquiv_symm (f : M ≃ₛₗ[σ₁₂] N) :
    ((mapRange.linearEquiv f).symm : (α →₀ _) ≃ₛₗ[σ₂₁] _) = mapRange.linearEquiv f.symm :=
  LinearEquiv.ext fun _x => rfl

@[simp]
/-
**Finsupp.mapRange.linearEquiv_toAddEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.map
Range`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} {N : Type u_3} {R : Type u_5} {R₂ : Type u
_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M] [ins
t_3 : _root_.Module R M] [inst_4 : AddCommMonoid N] [inst_5 : _root_.Module R₂ N
]   {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} [inst_6 : RingHomInvPair σ₁₂ σ₂₁] [inst_7 
: RingHomInvPair σ₂₁ σ₁₂]   (f : M ≃ₛₗ[σ₁₂] N), (Finsupp.mapRange.linearEquiv f)
.toAddEquiv = Finsupp.mapRange.addEquiv f.toAddEquiv
参数：f : M ≃ₛₗ[σ₁₂] N；Finsupp.mapRange.linearEquiv f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst_1 : A
dd N] {f g : M ≃+ N}, (∀ (x : M), f x = g x) → f = g
-/
theorem mapRange.linearEquiv_toAddEquiv (f : M ≃ₛₗ[σ₁₂] N) :
    (mapRange.linearEquiv f).toAddEquiv = (mapRange.addEquiv f.toAddEquiv : (α →₀ M) ≃+ _) :=
  AddEquiv.ext fun _ => rfl

@[simp]
/-
**Finsupp.mapRange.linearEquiv_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.ma
pRange`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} {N : Type u_3} {R : Type u_5} {R₂ : Type u
_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M] [ins
t_3 : _root_.Module R M] [inst_4 : AddCommMonoid N] [inst_5 : _root_.Module R₂ N
]   {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} [inst_6 : RingHomInvPair σ₁₂ σ₂₁] [inst_7 
: RingHomInvPair σ₂₁ σ₁₂]   (f : M ≃ₛₗ[σ₁₂] N), ↑(Finsupp.mapRange.linearEquiv f
) = Finsupp.mapRange.linearMap ↑f
参数：f : M ≃ₛₗ[σ₁₂] N；Finsupp.mapRange.linearEquiv f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
theorem mapRange.linearEquiv_toLinearMap (f : M ≃ₛₗ[σ₁₂] N) :
    (mapRange.linearEquiv f).toLinearMap =
    (mapRange.linearMap f.toLinearMap : (α →₀ M) →ₛₗ[σ₁₂] _) :=
  LinearMap.ext fun _ => rfl

end Equiv

section Prod

variable {α β R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

variable (R) in
/-- The linear equivalence between `α × β →₀ M` and `α →₀ β →₀ M`.

This is the `LinearEquiv` version of `Finsupp.curryEquiv`. -/
@[simps +simpRhs]
/-
**Finsupp.curryLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：curryLinearEquiv : (α × β ->₀ M) ≃ₗ[R] α ->₀ β ->₀ M where toAddEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear equivalence between `α × β →₀ M` and `α →₀ β →₀ M`.

This is the `LinearEquiv` version of `Finsupp.curryEquiv`.
-/
noncomputable def curryLinearEquiv : (α × β →₀ M) ≃ₗ[R] α →₀ β →₀ M where
  toAddEquiv := curryAddEquiv
  map_smul' c f := by ext; simp

@[deprecated (since := "2026-01-03")] alias finsuppProdLEquiv := curryLinearEquiv
/-
**Finsupp.curryLinearEquiv_symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：curryLinearEquiv_symm_apply_apply (f : α ->₀ β ->₀ M) (xy) : (curryLinearE
quiv R).symm f xy = f xy.1 xy.2
参数：f : α ->₀ β ->₀ M；xy。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem curryLinearEquiv_symm_apply_apply (f : α →₀ β →₀ M) (xy) :
    (curryLinearEquiv R).symm f xy = f xy.1 xy.2 :=
  rfl

@[deprecated (since := "2026-01-03")]
alias finsuppProdLEquiv_symm_apply_apply := curryLinearEquiv_symm_apply_apply

end Prod

end Finsupp

variable {R : Type*} {M : Type*} {N : Type*}
variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

open Finsupp

section

variable (R)

/-- If `Subsingleton R`, then `M ≃ₗ[R] ι →₀ R` for any type `ι`. -/
@[simps]
/-
**Module.subsingletonEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Module.subsingletonEquiv (R M ι : Type*) [Semiring R] [Subsingleton R] [Ad
dCommMonoid M] [Module R M] : M ≃ₗ[R] ι ->₀ R where toFun _
参数：R M ι : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `Subsingleton R`, then `M ≃ₗ[R] ι →₀ R` for any type `ι`.
-/
def Module.subsingletonEquiv (R M ι : Type*) [Semiring R] [Subsingleton R] [AddCommMonoid M]
    [Module R M] : M ≃ₗ[R] ι →₀ R where
  toFun _ := 0
  invFun _ := 0
  left_inv m :=
    have := Module.subsingleton R M
    Subsingleton.elim _ _
  right_inv f := by simp only [eq_iff_true_of_subsingleton]
  map_add' _ _ := (add_zero 0).symm
  map_smul' r _ := (smul_zero r).symm

end

namespace Module.End

variable (ι : Type*) {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- If `M` is an `R`-module and `ι` is a type, then an additive endomorphism of `M` that
commutes with all `R`-endomorphisms of `M` gives rise to an additive endomorphism of `ι →₀ M`
that commutes with all `R`-endomorphisms of `ι →₀ M`. -/
/-
**Module.End.ringHomEndFinsupp** 是 Mathlib 中的一个定义，位于命名空间 `Module.End`。
形式化陈述：(ι : Type u_4) →   {R : Type u_5} →     {M : Type u_6} →       [inst : Sem
iring R] →         [inst_1 : AddCommMonoid M] →           [inst_2 : _root_.Modul
e R M] → Module.End (Module.End R M) M →+* Module.End (Module.End R (ι →₀ M)) (ι
 →₀ M)
参数：ι →₀ M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M` is an `R`-module and `ι` is a type, then an additive endomorphism of `M` 
that
commutes with all `R`-endomorphisms of `M` gives rise to an additive endomorphis
m of `ι →₀ M`
that commutes with all `R`-endomorphisms of `ι →₀ M`.
-/
@[simps] noncomputable def ringHomEndFinsupp :
    End (End R M) M →+* End (End R (ι →₀ M)) (ι →₀ M) where
  toFun f :=
  { toFun := Finsupp.mapRange.addMonoidHom f
    map_add' := map_add _
    map_smul' g x := x.induction_linear (by simp)
      (fun _ _ h h' ↦ by rw [smul_add, map_add, h, h', map_add, smul_add]) fun i m ↦ by
        ext j
        change f (Finsupp.lapply j ∘ₗ g ∘ₗ Finsupp.lsingle i • m) = _
        rw [map_smul]
        simp }
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

variable {ι}

/-- If `M` is an `R`-module and `ι` is a nonempty type, then every additive endomorphism
of `ι →₀ M` that commutes with all `R`-endomorphisms of `ι →₀ M` comes from an additive
endomorphism of `M` that commutes with all `R`-endomorphisms of `M`.
See (15) in F4 of §28 on p.131 of [Lorenz2008]. -/
/-
**Module.End.ringEquivEndFinsupp** 是 Mathlib 中的一个定义，位于命名空间 `Module.End`。
形式化陈述：{ι : Type u_4} →   {R : Type u_5} →     {M : Type u_6} →       [inst : Sem
iring R] →         [inst_1 : AddCommMonoid M] →           [inst_2 : _root_.Modul
e R M] →             ι → Module.End (Module.End R M) M ≃+* Module.End (Module.En
d R (ι →₀ M)) (ι →₀ M)
参数：Module.End R M；Module.End R (ι →₀ M)；ι →₀ M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M` is an `R`-module and `ι` is a nonempty type, then every additive endomorp
hism
of `ι →₀ M` that commutes with all `R`-endomorphisms of `ι →₀ M` comes from an a
dditive
endomorphism of `M` that commutes with all `R`-endomorphisms of `M`.
See (15) in F4 of §28 on p.131 of [Lorenz2008].
-/
@[simps!] noncomputable def ringEquivEndFinsupp (i : ι) :
    End (End R M) M ≃+* End (End R (ι →₀ M)) (ι →₀ M) where
  __ := ringHomEndFinsupp ι
  invFun f :=
  { toFun m := f (Finsupp.single i m) i
    map_add' _ _ := by simp
    map_smul' g m := let g := Finsupp.mapRange.linearMap g
      show _ = g _ i by rw [← End.smul_def g, ← map_smul]; simp [g] }
  left_inv _ := by ext; simp
  right_inv f := by
    ext x j
    change f (Finsupp.lsingle (R := R) (M := M) i ∘ₗ Finsupp.lapply j • x) i = _
    rw [map_smul]
    simp

variable (R M ι)
/-
**Module.End.ringHomEndFinsupp_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`
。
形式化陈述：ringHomEndFinsupp_surjective : Function.Surjective (ringHomEndFinsupp (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
-/
theorem ringHomEndFinsupp_surjective :
    Function.Surjective (ringHomEndFinsupp (R := R) (M := M) ι) := by
  intro f
  obtain _ | ⟨⟨i⟩⟩ := isEmpty_or_nonempty ι
  · exact ⟨0, Subsingleton.elim ..⟩
  · exact ⟨_, (ringEquivEndFinsupp i).right_inv f⟩

end Module.End

