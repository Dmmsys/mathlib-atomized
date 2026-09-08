/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!

# Linear maps involving submodules of a module

In this file we define a number of linear maps involving submodules of a module.

## Main declarations

* `Submodule.subtype`: Embedding of a submodule `p` to the ambient space `M` as a `Submodule`.
* `LinearMap.domRestrict`: The restriction of a semilinear map `f : M → M₂` to a submodule `p ⊆ M`
  as a semilinear map `p → M₂`.
* `LinearMap.restrict`: The restriction of a linear map `f : M → M₁` to a submodule `p ⊆ M` and
  `q ⊆ M₁` (if `q` contains the codomain).
* `Submodule.inclusion`: the inclusion `p ⊆ p'` of submodules `p` and `p'` as a linear map.

## Tags

submodule, subspace, linear map
-/

@[expose] public section

open Function Set

universe u'' u' u v w

section

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

namespace SMulMemClass

variable [Semiring R] [AddCommMonoid M] [Module R M] {A : Type*} [SetLike A M]
  [AddSubmonoidClass A M] [SMulMemClass A R M] (S' : A)

/-- The natural `R`-linear map from a submodule of an `R`-module `M` to `M`. -/
/-
**SMulMemClass.subtype** 是 Mathlib 中的一个定义，位于命名空间 `SMulMemClass`。
形式化陈述：{R : Type u} →   {M : Type v} →     [inst : Semiring R] →       [inst_1 : 
AddCommMonoid M] →         [inst_2 : _root_.Module R M] →           {A : Type u_
1} →             [inst_3 : SetLike A M] →               [inst_4 : AddSubmonoidCl
ass A M] → [inst_5 : SMulMemClass A R M] → (S' : A) → ↥S' →ₗ[R] M
参数：S' : A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural `R`-linear map from a submodule of an `R`-module `M` to `M`.
-/
protected def subtype : S' →ₗ[R] M where
  toFun := Subtype.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {S'} in
@[simp]
/-
**SMulMemClass.subtype_apply** 是 Mathlib 中的一个引理，位于命名空间 `SMulMemClass`。
形式化陈述：subtype_apply (x : S') : SMulMemClass.subtype S' x = x
参数：x : S'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subtype_apply (x : S') :
    SMulMemClass.subtype S' x = x := rfl
/-
**SMulMemClass.subtype_injective** 是 Mathlib 中的一个引理，位于命名空间 `SMulMemClass`。
形式化陈述：subtype_injective : Function.Injective (SMulMemClass.subtype S')
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
lemma subtype_injective :
    Function.Injective (SMulMemClass.subtype S') :=
  Subtype.coe_injective

@[simp]
/-
**SMulMemClass.coe_subtype** 是 Mathlib 中的一个定理，位于命名空间 `SMulMemClass`。
形式化陈述：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst_1 : AddCommMonoid M]
 [inst_2 : _root_.Module R M] {A : Type u_1}   [inst_3 : SetLike A M] [inst_4 : 
AddSubmonoidClass A M] [inst_5 : SMulMemClass A R M] (S' : A),   ⇑(SMulMemClass.
subtype S') = Subtype.val
参数：S' : A；SMulMemClass.subtype S'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coe_subtype : (SMulMemClass.subtype S' : S' → M) = Subtype.val :=
  rfl

end SMulMemClass

namespace Submodule

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M]

-- We can infer the module structure implicitly from the bundled submodule,
-- rather than via typeclass resolution.
variable {module_M : Module R M}
variable {p q : Submodule R M}
variable {r : R} {x y : M}
variable (p)

/-- Embedding of a submodule `p` to the ambient space `M`. -/
/-
**Submodule.subtype** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：{R : Type u} →   {M : Type v} →     [inst : Semiring R] → [inst_1 : AddCom
mMonoid M] → {module_M : _root_.Module R M} → (p : Submodule R M) → ↥p →ₗ[R] M
参数：p : Submodule R M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Embedding of a submodule `p` to the ambient space `M`.
-/
protected def subtype : p →ₗ[R] M where
  toFun := Subtype.val
  map_add' := by simp
  map_smul' := by simp

variable {p} in
@[simp]
/-
**Submodule.subtype_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：subtype_apply (x : p) : p.subtype x = x
参数：x : p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtype_apply (x : p) : p.subtype x = x :=
  rfl
/-
**Submodule.subtype_injective** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：subtype_injective : Function.Injective p.subtype
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
lemma subtype_injective :
    Function.Injective p.subtype :=
  Subtype.coe_injective

@[simp]
/-
**Submodule.coe_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_subtype : (Submodule.subtype p : p -> M) = Subtype.val
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_subtype : (Submodule.subtype p : p → M) = Subtype.val :=
  rfl
/-
**Submodule.injective_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：injective_subtype : Injective p.subtype
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem injective_subtype : Injective p.subtype :=
  Subtype.coe_injective

/-- Note the `AddSubmonoid` version of this lemma is called `AddSubmonoid.coe_finsetSum`. -/
/-
**Submodule.coe_sum** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_sum (x : ι -> p) (s : Finset ι) : ↑(∑ i in s, x i) = ∑ i in s, (x i : 
M)
参数：x : ι -> p；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…

--- 原说明 ---
Note the `AddSubmonoid` version of this lemma is called `AddSubmonoid.coe_finset
Sum`.
-/
theorem coe_sum (x : ι → p) (s : Finset ι) : ↑(∑ i ∈ s, x i) = ∑ i ∈ s, (x i : M) :=
  map_sum p.subtype _ _

section AddAction

variable {α β : Type*}

/-- The action by a submodule is the action by the underlying module. -/
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by a submodule is the action by the underlying module.
-/
instance [AddAction M α] : AddAction p α :=
  AddSubmonoid.instAddActionSubtypeMem p

end AddAction

end AddCommMonoid

end Submodule

end

section

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}
variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}
variable {ι : Type*}

namespace LinearMap

section AddCommMonoid

variable [Semiring R] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R M₁] [Module R₂ M₂] [Module R₃ M₃]
variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
variable (f : M →ₛₗ[σ₁₂] M₂) (g : M₂ →ₛₗ[σ₂₃] M₃)


/-- The restriction of a linear map `f : M → M₂` to a submodule `p ⊆ M` gives a linear map
`p → M₂`. -/
/-
**LinearMap.domRestrict** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：domRestrict (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M) : p ->ₛₗ[σ₁₂] M₂
参数：f : M ->ₛₗ[σ₁₂] M₂；p : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a linear map `f : M → M₂` to a submodule `p ⊆ M` gives a line
ar map
`p → M₂`.
-/
def domRestrict (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) : p →ₛₗ[σ₁₂] M₂ :=
  f.comp p.subtype

@[simp]
/-
**LinearMap.domRestrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：domRestrict_apply (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M) (x : p) : f.dom
Restrict p x = f x
参数：f : M ->ₛₗ[σ₁₂] M₂；p : Submodule R M；x : p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domRestrict_apply (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) (x : p) :
    f.domRestrict p x = f x :=
  rfl
/-
**LinearMap.coe_domRestrict** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：coe_domRestrict (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M) : ⇑(f.domRestrict
 p) = Set.domRestrict p f
参数：f : M ->ₛₗ[σ₁₂] M₂；p : Submodule R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_domRestrict (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) :
    ⇑(f.domRestrict p) = Set.domRestrict p f := rfl

/-- A linear map `f : M₂ → M` whose values lie in a submodule `p ⊆ M` can be restricted to a
linear map M₂ → p.

See also `LinearMap.codLift`. -/
/-
**LinearMap.codRestrict** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：codRestrict (p : Submodule R₂ M₂) (f : M ->ₛₗ[σ₁₂] M₂) (h : forall c, f c 
in p) : M ->ₛₗ[σ₁₂] p where toFun c
参数：p : Submodule R₂ M₂；f : M ->ₛₗ[σ₁₂] M₂；h : forall c, f c in p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear map `f : M₂ → M` whose values lie in a submodule `p ⊆ M` can be restric
ted to a
linear map M₂ → p.

See also `LinearMap.codLift`.
-/
def codRestrict (p : Submodule R₂ M₂) (f : M →ₛₗ[σ₁₂] M₂) (h : ∀ c, f c ∈ p) : M →ₛₗ[σ₁₂] p where
  toFun c := ⟨f c, h c⟩
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

@[simp]
/-
**LinearMap.codRestrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：codRestrict_apply (p : Submodule R₂ M₂) (f : M ->ₛₗ[σ₁₂] M₂) {h} (x : M) :
 (codRestrict p f h x : M₂) = f x
参数：p : Submodule R₂ M₂；f : M ->ₛₗ[σ₁₂] M₂；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem codRestrict_apply (p : Submodule R₂ M₂) (f : M →ₛₗ[σ₁₂] M₂) {h} (x : M) :
    (codRestrict p f h x : M₂) = f x :=
  rfl

@[simp]
/-
**LinearMap.comp_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：comp_codRestrict (p : Submodule R₃ M₃) (h : forall b, g b in p) : ((codRes
trict p g h).comp f : M ->ₛₗ[σ₁₃] p) = codRestrict p (g.comp f) fun _ => h _
参数：p : Submodule R₃ M₃；h : forall b, g b in p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_codRestrict (p : Submodule R₃ M₃) (h : ∀ b, g b ∈ p) :
    ((codRestrict p g h).comp f : M →ₛₗ[σ₁₃] p) = codRestrict p (g.comp f) fun _ => h _ :=
  rfl

@[simp]
/-
**LinearMap.subtype_comp_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：subtype_comp_codRestrict (p : Submodule R₂ M₂) (h : forall b, f b in p) : 
p.subtype.comp (codRestrict p f h) = f
参数：p : Submodule R₂ M₂；h : forall b, f b in p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtype_comp_codRestrict (p : Submodule R₂ M₂) (h : ∀ b, f b ∈ p) :
    p.subtype.comp (codRestrict p f h) = f :=
  rfl

@[simp]
/-
**LinearMap.domRestrict_comp_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：domRestrict_comp_codRestrict (g : M₂ ->ₛₗ[σ₂₃] M₃) (f : M ->ₛₗ[σ₁₂] M₂) (p
 : Submodule R₂ M₂) (h : forall c, f c in p) : g.domRestrict p ∘ₛₗ f.codRestrict
 p h = g ∘ₛₗ f
参数：g : M₂ ->ₛₗ[σ₂₃] M₃；f : M ->ₛₗ[σ₁₂] M₂；p : Submodule R₂ M₂；h : forall c, f c 
in p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domRestrict_comp_codRestrict (g : M₂ →ₛₗ[σ₂₃] M₃) (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R₂ M₂)
    (h : ∀ c, f c ∈ p) :
    g.domRestrict p ∘ₛₗ f.codRestrict p h = g ∘ₛₗ f :=
  rfl

section

variable {M₂' : Type*} [AddCommMonoid M₂'] [Module R₂ M₂']
  (p : M₂' →ₗ[R₂] M₂) (hp : Injective p) (h : ∀ c, f c ∈ range p)

set_option backward.isDefEq.respectTransparency false in
/-- A linear map `f : M → M₂` whose values lie in the image of an injective linear map
`p : M₂' → M₂` admits a unique lift to a linear map `M → M₂'`. -/
/-
**LinearMap.codLift** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：codLift : M ->ₛₗ[σ₁₂] M₂' where toFun c
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear map `f : M → M₂` whose values lie in the image of an injective linear m
ap
`p : M₂' → M₂` admits a unique lift to a linear map `M → M₂'`.
-/
noncomputable def codLift :
    M →ₛₗ[σ₁₂] M₂' where
  toFun c := (h c).choose
  map_add' b c := by apply hp; simp_rw [map_add, (h _).choose_spec, ← map_add, (h _).choose_spec]
  map_smul' r c := by apply hp; simp_rw [map_smul, (h _).choose_spec, map_smulₛₗ]
/-
**LinearMap.codLift_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ : Type u_7} [inst : Se
miring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M] [inst_3 : AddCommM
onoid M₂] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R₂ M₂]   {σ₁₂ : R
 →+* R₂} (f : M →ₛₗ[σ₁₂] M₂) {M₂' : Type u_10} [inst_6 : AddCommMonoid M₂'] [ins
t_7 : _root_.Module R₂ M₂']   (p : M₂' →ₗ[R₂] M₂) (hp : Function.Injective ⇑p) (
h : ∀ (c : M), f c ∈ Set.range ⇑p) (x : M),   (f.codLift p hp h) x = Exists.choo
se ⋯
参数：f : M →ₛₗ[σ₁₂] M₂；p : M₂' →ₗ[R₂] M₂；hp : Function.Injective ⇑p；h : ∀ (c : M),
 f c ∈ Set.range ⇑p；x : M；f.codLift p hp h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem codLift_apply (x : M) :
    (f.codLift p hp h x) = (h x).choose :=
  rfl

@[simp]
/-
**LinearMap.comp_codLift** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：comp_codLift : p.comp (f.codLift p hp h) = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `LinearMap.codLift_apply`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5}
 {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommM
onoid M] [ins…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem comp_codLift :
    p.comp (f.codLift p hp h) = f := by
  ext x
  rw [comp_apply, codLift_apply, (h x).choose_spec]

end

/-- Restrict domain and codomain of a linear map. -/
/-
**LinearMap.restrict** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：restrict (f : M ->ₛₗ[σ₁₂] M₂) {p : Submodule R M} {q : Submodule R₂ M₂} (h
f : forall x in p, f x in q) : p ->ₛₗ[σ₁₂] q
参数：f : M ->ₛₗ[σ₁₂] M₂；hf : forall x in p, f x in q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict domain and codomain of a linear map.
-/
def restrict (f : M →ₛₗ[σ₁₂] M₂) {p : Submodule R M} {q : Submodule R₂ M₂} (hf : ∀ x ∈ p, f x ∈ q) :
    p →ₛₗ[σ₁₂] q :=
  (f.domRestrict p).codRestrict q <| SetLike.forall.2 hf

@[simp]
/-
**LinearMap.coe_restrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coe_restrict_apply {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {q : Submodule
 R₂ M₂} (hf : forall x in p, f x in q) (x : p) : ↑(f.restrict hf x) = f x
参数：hf : forall x in p, f x in q；x : p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_restrict_apply {f : M →ₛₗ[σ₁₂] M₂} {p : Submodule R M} {q : Submodule R₂ M₂}
    (hf : ∀ x ∈ p, f x ∈ q) (x : p) : ↑(f.restrict hf x) = f x :=
  rfl

@[deprecated coe_restrict_apply (since := "2026-05-13")]
/-
**LinearMap.restrict_coe_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：restrict_coe_apply (f : M ->ₛₗ[σ₁₂] M₂) {p : Submodule R M} {q : Submodule
 R₂ M₂} (hf : forall x in p, f x in q) (x : p) : ↑(f.restrict hf x) = f x
参数：f : M ->ₛₗ[σ₁₂] M₂；hf : forall x in p, f x in q；x : p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrict_coe_apply (f : M →ₛₗ[σ₁₂] M₂) {p : Submodule R M} {q : Submodule R₂ M₂}
    (hf : ∀ x ∈ p, f x ∈ q) (x : p) : ↑(f.restrict hf x) = f x :=
  rfl
/-
**LinearMap.restrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：restrict_apply {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {q : Submodule R₂ 
M₂} (hf : forall x in p, f x in q) (x : p) : f.restrict hf x = ⟨f x, hf x.1 x.2⟩
参数：hf : forall x in p, f x in q；x : p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrict_apply {f : M →ₛₗ[σ₁₂] M₂} {p : Submodule R M} {q : Submodule R₂ M₂}
    (hf : ∀ x ∈ p, f x ∈ q) (x : p) : f.restrict hf x = ⟨f x, hf x.1 x.2⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**LinearMap.restrict_sub** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：restrict_sub {R R₂ M M₂ : Type*} [Ring R] [Ring R₂] {σ₁₂ : R ->+* R₂} [Add
CommGroup M] [AddCommGroup M₂] [Module R M] [Module R₂ M₂] {p : Submodule R M} {
q : Submodule R₂ M₂} {f g : M ->ₛₗ[σ₁₂] M₂} (hf : MapsTo f p q) (hg : MapsTo g p
 q) (hfg : MapsTo (f - g) p q
参数：hf : MapsTo f p q；hg : MapsTo g p q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma restrict_sub {R R₂ M M₂ : Type*}
    [Ring R] [Ring R₂] {σ₁₂ : R →+* R₂} [AddCommGroup M] [AddCommGroup M₂]
    [Module R M] [Module R₂ M₂] {p : Submodule R M} {q : Submodule R₂ M₂} {f g : M →ₛₗ[σ₁₂] M₂}
    (hf : MapsTo f p q) (hg : MapsTo g p q)
    (hfg : MapsTo (f - g) p q := fun _ hx ↦ q.sub_mem (hf hx) (hg hx)) :
    f.restrict hf - g.restrict hg = (f - g).restrict hfg := by
  ext; simp
/-
**LinearMap.restrict_comp** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：restrict_comp {p : Submodule R M} {p₂ : Submodule R₂ M₂} {p₃ : Submodule R
₃ M₃} {f : M ->ₛₗ[σ₁₂] M₂} {g : M₂ ->ₛₗ[σ₂₃] M₃} (hf : MapsTo f p p₂) (hg : Maps
To g p₂ p₃) (hfg : MapsTo (g ∘ₛₗ f) p p₃
参数：hf : MapsTo f p p₂；hg : MapsTo g p₂ p₃。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrict_comp {p : Submodule R M} {p₂ : Submodule R₂ M₂} {p₃ : Submodule R₃ M₃}
    {f : M →ₛₗ[σ₁₂] M₂} {g : M₂ →ₛₗ[σ₂₃] M₃}
    (hf : MapsTo f p p₂) (hg : MapsTo g p₂ p₃) (hfg : MapsTo (g ∘ₛₗ f) p p₃ := hg.comp hf) :
    (g ∘ₛₗ f).restrict hfg = (g.restrict hg) ∘ₛₗ (f.restrict hf) :=
  rfl

-- TODO Consider defining `Algebra R (p.compatibleMaps p)`, `AlgHom` version of `LinearMap.restrict`
/-
**LinearMap.restrict_smul_one** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：restrict_smul_one {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module
 R M] {p : Submodule R M} (μ : R) (h : forall x in p, (μ • (1 : Module.End R M))
 x in p
参数：μ : R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrict_smul_one
    {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] {p : Submodule R M}
    (μ : R) (h : ∀ x ∈ p, (μ • (1 : Module.End R M)) x ∈ p := fun _ ↦ p.smul_mem μ) :
    (μ • 1 : Module.End R M).restrict h = μ • (1 : Module.End R p) :=
  rfl
/-
**LinearMap.restrict_commute** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：restrict_commute {f g : M ->ₗ[R] M} (h : Commute f g) {p : Submodule R M} 
(hf : MapsTo f p p) (hg : MapsTo g p p) : Commute (f.restrict hf) (g.restrict hg
)
参数：h : Commute f g；hf : MapsTo f p p；hg : MapsTo g p p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set
 α} {t : Set β} {p : Set γ} {f : α → β} {g : β → γ},   Set.MapsTo g t p → Set.Ma
psTo …
-/
lemma restrict_commute {f g : M →ₗ[R] M} (h : Commute f g) {p : Submodule R M}
    (hf : MapsTo f p p) (hg : MapsTo g p p) :
    Commute (f.restrict hf) (g.restrict hg) := by
  change (f ∘ₗ g).restrict (hf.comp hg) = (g ∘ₗ f).restrict (hg.comp hf)
  congr 1
/-
**LinearMap.subtype_comp_restrict** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：subtype_comp_restrict {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {q : Submod
ule R₂ M₂} (hf : forall x in p, f x in q) : q.subtype.comp (f.restrict hf) = f.d
omRestrict p
参数：hf : forall x in p, f x in q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtype_comp_restrict {f : M →ₛₗ[σ₁₂] M₂} {p : Submodule R M} {q : Submodule R₂ M₂}
    (hf : ∀ x ∈ p, f x ∈ q) : q.subtype.comp (f.restrict hf) = f.domRestrict p :=
  rfl
/-
**LinearMap.restrict_eq_codRestrict_domRestrict** 是 Mathlib 中的一个定理，位于命名空间 `Linea
rMap`。
形式化陈述：restrict_eq_codRestrict_domRestrict {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R 
M} {q : Submodule R₂ M₂} (hf : forall x in p, f x in q) : f.restrict hf = (f.dom
Restrict p).codRestrict q fun x => hf x.1 x.2
参数：hf : forall x in p, f x in q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrict_eq_codRestrict_domRestrict {f : M →ₛₗ[σ₁₂] M₂} {p : Submodule R M}
    {q : Submodule R₂ M₂} (hf : ∀ x ∈ p, f x ∈ q) :
    f.restrict hf = (f.domRestrict p).codRestrict q fun x => hf x.1 x.2 :=
  rfl
/-
**LinearMap.restrict_eq_domRestrict_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `Linea
rMap`。
形式化陈述：restrict_eq_domRestrict_codRestrict {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R 
M} {q : Submodule R₂ M₂} (hf : forall x, f x in q) : (f.restrict fun x _ => hf x
) = (f.codRestrict q hf).domRestrict p
参数：hf : forall x, f x in q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrict_eq_domRestrict_codRestrict {f : M →ₛₗ[σ₁₂] M₂} {p : Submodule R M}
    {q : Submodule R₂ M₂} (hf : ∀ x, f x ∈ q) :
    (f.restrict fun x _ => hf x) = (f.codRestrict q hf).domRestrict p :=
  rfl
/-
**LinearMap.sum_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：sum_apply (t : Finset ι) (f : ι -> M ->ₛₗ[σ₁₂] M₂) (b : M) : (∑ d in t, f 
d) b = ∑ d in t, f d b
参数：t : Finset ι；f : ι -> M ->ₛₗ[σ₁₂] M₂；b : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem sum_apply (t : Finset ι) (f : ι → M →ₛₗ[σ₁₂] M₂) (b : M) :
    (∑ d ∈ t, f d) b = ∑ d ∈ t, f d b :=
  _root_.map_sum ((AddMonoidHom.eval b).comp toAddMonoidHom') f _

@[simp, norm_cast]
/-
**LinearMap.coe_sum** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ₁₂] M₂) : ⇑(∑ i in t,
 f i) = ∑ i in t, (f i : M -> M₂)
参数：t : Finset ι；f : ι -> M ->ₛₗ[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem coe_sum {ι : Type*} (t : Finset ι) (f : ι → M →ₛₗ[σ₁₂] M₂) :
    ⇑(∑ i ∈ t, f i) = ∑ i ∈ t, (f i : M → M₂) :=
  _root_.map_sum
    (show AddMonoidHom (M →ₛₗ[σ₁₂] M₂) (M → M₂)
      from { toFun := DFunLike.coe,
             map_zero' := rfl
             map_add' := fun _ _ => rfl }) _ _
/-
**LinearMap._root_.Module.End.submodule_pow_eq_zero_of_pow_eq_zero** 是 Mathlib 中
的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Module.End.submodule_pow_eq_zero_of_pow_eq_zero {N : Submodule R M}
    {g : Module.End R N} {G : Module.End R M} (h : G.comp N.subtype = N.subtype.comp g) {k : ℕ}
    (hG : G ^ k = 0) : g ^ k = 0 := by
  ext m
  have hg : N.subtype.comp (g ^ k) m = 0 := by
    rw [← Module.End.commute_pow_left_of_commute h, hG, zero_comp, zero_apply]
  simpa using hg

section

variable {f' : M →ₗ[R] M}

/-
**LinearMap._root_.Module.End.pow_apply_mem_of_forall_mem** 是 Mathlib 中的一个定理，位于命
名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Module.End.pow_apply_mem_of_forall_mem {p : Submodule R M} (n : ℕ)
    (h : ∀ x ∈ p, f' x ∈ p) (x : M) (hx : x ∈ p) : (f' ^ n) x ∈ p := by
  induction n generalizing x with
  | zero => simpa
  | succ n ih =>
    simpa only [iterate_succ, coe_comp, Function.comp_apply, restrict_apply] using! ih _ (h _ hx)
/-
**LinearMap._root_.Module.End.pow_restrict** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Module.End.pow_restrict {p : Submodule R M} (n : ℕ) (h : ∀ x ∈ p, f' x ∈ p)
    (h' := Module.End.pow_apply_mem_of_forall_mem n h) :
    (f'.restrict h) ^ n = (f' ^ n).restrict h' := by
  ext x
  have : Semiconj (↑) (f'.restrict h) f' := fun _ ↦ coe_restrict_apply _ _
  simp [Module.End.coe_pow, this.iterate_right _ _]

end

end AddCommMonoid

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R M₂]
variable (f g : M →ₗ[R] M₂)

/-- Alternative version of `domRestrict` as a linear map. -/
/-
**LinearMap.domRestrict'** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：domRestrict' (p : Submodule R M) : (M ->ₗ[R] M₂) ->ₗ[R] p ->ₗ[R] M₂ where 
toFun φ
参数：p : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Alternative version of `domRestrict` as a linear map.
-/
def domRestrict' (p : Submodule R M) : (M →ₗ[R] M₂) →ₗ[R] p →ₗ[R] M₂ where
  toFun φ := φ.domRestrict p
  map_add' := by simp [LinearMap.ext_iff]
  map_smul' := by simp [LinearMap.ext_iff]

@[simp]
/-
**LinearMap.domRestrict'_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {M : Type u_5} {M₂ : Type u_7} [inst : CommSemiring R] [i
nst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_3 : _root_.Module R
 M] [inst_4 : _root_.Module R M₂] (f : M →ₗ[R] M₂)   (p : Submodule R M) (x : ↥p
), ((LinearMap.domRestrict' p) f) x = f ↑x
参数：f : M →ₗ[R] M₂；p : Submodule R M；x : ↥p；(LinearMap.domRestrict' p) f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domRestrict'_apply (f : M →ₗ[R] M₂) (p : Submodule R M) (x : p) :
    domRestrict' p f x = f x :=
  rfl

end CommSemiring

end LinearMap

end

namespace Submodule

section AddCommMonoid

variable {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {p p' : Submodule R M}

/-- If two submodules `p` and `p'` satisfy `p ⊆ p'`, then `inclusion p p'` is the linear map version
of this inclusion. -/
/-
**Submodule.inclusion** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：inclusion (h : p <= p') : p ->ₗ[R] p'
参数：h : p <= p'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If two submodules `p` and `p'` satisfy `p ⊆ p'`, then `inclusion p p'` is the li
near map version
of this inclusion.
-/
def inclusion (h : p ≤ p') : p →ₗ[R] p' :=
  p.subtype.codRestrict p' fun ⟨_, hx⟩ => h hx

@[simp]
/-
**Submodule.coe_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_inclusion (h : p <= p') (x : p) : (inclusion h x : M) = x
参数：h : p <= p'；x : p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inclusion (h : p ≤ p') (x : p) : (inclusion h x : M) = x :=
  rfl
/-
**Submodule.inclusion_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：inclusion_apply (h : p <= p') (x : p) : inclusion h x = ⟨x, h x.2⟩
参数：h : p <= p'；x : p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inclusion_apply (h : p ≤ p') (x : p) : inclusion h x = ⟨x, h x.2⟩ :=
  rfl
/-
**Submodule.inclusion_injective** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：inclusion_injective (h : p <= p') : Function.Injective (inclusion h)
参数：h : p <= p'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Subtype.mk.inj`：∀ {α : Sort u} {p : α → Prop} {val : α} {property : p va
l} {val_1 : α} {property_1 : p val_1},   ⟨val, property⟩ = ⟨val_1, property_1⟩ →
 val…
-/
theorem inclusion_injective (h : p ≤ p') : Function.Injective (inclusion h) := fun _ _ h =>
  Subtype.val_injective (Subtype.mk.inj h)

variable (p p')
/-
**Submodule.subtype_comp_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：subtype_comp_inclusion (p q : Submodule R M) (h : p <= q) : q.subtype.comp
 (inclusion h) = p.subtype
参数：p q : Submodule R M；h : p <= q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtype_comp_inclusion (p q : Submodule R M) (h : p ≤ q) :
    q.subtype.comp (inclusion h) = p.subtype := rfl

end AddCommMonoid

end Submodule

