/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
module

public import Mathlib.Algebra.Module.Submodule.Range

/-! ### Linear equivalences involving submodules -/

@[expose] public section

open Function

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}
variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}
variable {N : Type*}

namespace LinearEquiv

section AddCommMonoid

section

variable [Semiring R] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable {module_M : Module R M} {module_M₂ : Module R₂ M₂} {module_M₃ : Module R₃ M₃}
variable {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}
variable {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
variable {σ₃₂ : R₃ →+* R₂}
variable {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}
variable {re₂₃ : RingHomInvPair σ₂₃ σ₃₂} {re₃₂ : RingHomInvPair σ₃₂ σ₂₃}
variable (f : M →ₛₗ[σ₁₂] M₂) (g : M₂ →ₛₗ[σ₂₁] M) (e : M ≃ₛₗ[σ₁₂] M₂) (h : M₂ →ₛₗ[σ₂₃] M₃)
variable (p q : Submodule R M)

/-- Linear equivalence between two equal submodules. -/
/-
**LinearEquiv.ofEq** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：ofEq (h : p = q) : p ≃ₗ[R] q
参数：h : p = q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Linear equivalence between two equal submodules.
-/
def ofEq (h : p = q) : p ≃ₗ[R] q :=
  { Equiv.setCongr (congr_arg _ h) with
    map_smul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

variable {p q}

@[simp]
/-
**LinearEquiv.coe_ofEq_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：coe_ofEq_apply (h : p = q) (x : p) : (ofEq p q h x : M) = x
参数：h : p = q；x : p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofEq_apply (h : p = q) (x : p) : (ofEq p q h x : M) = x :=
  rfl

@[simp]
/-
**LinearEquiv.ofEq_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：ofEq_symm (h : p = q) : (ofEq p q h).symm = ofEq q p h.symm
参数：h : p = q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofEq_symm (h : p = q) : (ofEq p q h).symm = ofEq q p h.symm :=
  rfl

@[simp]
/-
**LinearEquiv.ofEq_rfl** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：ofEq_rfl : ofEq p p rfl = LinearEquiv.refl R p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem ofEq_rfl : ofEq p p rfl = LinearEquiv.refl R p := by ext; rfl

/-- A linear equivalence which maps a submodule of one module onto another, restricts to a linear
equivalence of the two submodules. -/
/-
**LinearEquiv.ofSubmodules** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：ofSubmodules (p : Submodule R M) (q : Submodule R₂ M₂) (h : p.map (e : M -
>ₛₗ[σ₁₂] M₂) = q) : p ≃ₛₗ[σ₁₂] q
参数：p : Submodule R M；q : Submodule R₂ M₂；h : p.map (e : M ->ₛₗ[σ₁₂] M₂) = q。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…

--- 原说明 ---
A linear equivalence which maps a submodule of one module onto another, restrict
s to a linear
equivalence of the two submodules.
-/
def ofSubmodules (p : Submodule R M) (q : Submodule R₂ M₂) (h : p.map (e : M →ₛₗ[σ₁₂] M₂) = q) :
    p ≃ₛₗ[σ₁₂] q :=
  (e.submoduleMap p).trans (LinearEquiv.ofEq _ _ h)

@[simp]
/-
**LinearEquiv.ofSubmodules_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：ofSubmodules_apply {p : Submodule R M} {q : Submodule R₂ M₂} (h : p.map (e
 : M ->ₛₗ[σ₁₂] M₂) = q) (x : p) : ↑(e.ofSubmodules p q h x) = e x
参数：h : p.map (e : M ->ₛₗ[σ₁₂] M₂) = q；x : p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
-/
theorem ofSubmodules_apply {p : Submodule R M} {q : Submodule R₂ M₂}
    (h : p.map (e : M →ₛₗ[σ₁₂] M₂) = q) (x : p) :
    ↑(e.ofSubmodules p q h x) = e x :=
  rfl

@[simp]
/-
**LinearEquiv.ofSubmodules_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：ofSubmodules_symm_apply {p : Submodule R M} {q : Submodule R₂ M₂} (h : p.m
ap (e : M ->ₛₗ[σ₁₂] M₂) = q) (x : q) : ↑((e.ofSubmodules p q h).symm x) = e.symm
 x
参数：h : p.map (e : M ->ₛₗ[σ₁₂] M₂) = q；x : q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
-/
theorem ofSubmodules_symm_apply {p : Submodule R M} {q : Submodule R₂ M₂}
    (h : p.map (e : M →ₛₗ[σ₁₂] M₂) = q)
    (x : q) : ↑((e.ofSubmodules p q h).symm x) = e.symm x :=
  rfl

/-- A linear equivalence of two modules restricts to a linear equivalence from the preimage of any
submodule to that submodule.

This is `LinearEquiv.ofSubmodule` but with `comap` on the left instead of `map` on the right. -/
/-
**LinearEquiv.ofSubmodule'** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：ofSubmodule' [Module R M] [Module R₂ M₂] (f : M ≃ₛₗ[σ₁₂] M₂) (U : Submodul
e R₂ M₂) : U.comap (f : M ->ₛₗ[σ₁₂] M₂) ≃ₛₗ[σ₁₂] U
参数：f : M ≃ₛₗ[σ₁₂] M₂；U : Submodule R₂ M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear equivalence of two modules restricts to a linear equivalence from the p
reimage of any
submodule to that submodule.

This is `LinearEquiv.ofSubmodule` but with `comap` on the left instead of `map` 
on the right.
-/
def ofSubmodule' [Module R M] [Module R₂ M₂] (f : M ≃ₛₗ[σ₁₂] M₂) (U : Submodule R₂ M₂) :
    U.comap (f : M →ₛₗ[σ₁₂] M₂) ≃ₛₗ[σ₁₂] U :=
  (f.symm.ofSubmodules _ _ (U.map_equiv_eq_comap_symm f.symm)).symm
/-
**LinearEquiv.ofSubmodule'_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ : Type u_7} [inst : Se
miring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M] [inst_3 : AddCommM
onoid M₂] {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}   {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {r
e₂₁ : RingHomInvPair σ₂₁ σ₁₂} [inst_4 : _root_.Module R M]   [inst_5 : _root_.Mo
dule R₂ M₂] (f : M ≃ₛₗ[σ₁₂] M₂) (U : Submodule R₂ M₂),   ↑(f.ofSubmodule' U) = L
inearMap.codRestrict U ((↑f).domRestrict (Submodule.comap (↑f) U)) ⋯
参数：f : M ≃ₛₗ[σ₁₂] M₂；U : Submodule R₂ M₂；f.ofSubmodule' U；(↑f).domRestrict (Subm
odule.comap (↑f) U)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem ofSubmodule'_toLinearMap [Module R M] [Module R₂ M₂] (f : M ≃ₛₗ[σ₁₂] M₂)
    (U : Submodule R₂ M₂) :
    (f.ofSubmodule' U).toLinearMap = (f.toLinearMap.domRestrict _).codRestrict _ Subtype.prop := by
  ext
  rfl

@[simp]
/-
**LinearEquiv.ofSubmodule'_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ : Type u_7} [inst : Se
miring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M] [inst_3 : AddCommM
onoid M₂] {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}   {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {r
e₂₁ : RingHomInvPair σ₂₁ σ₁₂} [inst_4 : _root_.Module R M]   [inst_5 : _root_.Mo
dule R₂ M₂] (f : M ≃ₛₗ[σ₁₂] M₂) (U : Submodule R₂ M₂) (x : ↥(Submodule.comap (↑f
) U)),   ↑((f.ofSubmodule' U) x) = f ↑x
参数：f : M ≃ₛₗ[σ₁₂] M₂；U : Submodule R₂ M₂；x : ↥(Submodule.comap (↑f) U)；(f.ofSubm
odule' U) x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofSubmodule'_apply [Module R M] [Module R₂ M₂] (f : M ≃ₛₗ[σ₁₂] M₂) (U : Submodule R₂ M₂)
    (x : U.comap (f : M →ₛₗ[σ₁₂] M₂)) : (f.ofSubmodule' U x : M₂) = f (x : M) :=
  rfl

@[simp]
/-
**LinearEquiv.ofSubmodule'_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ : Type u_7} [inst : Se
miring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M] [inst_3 : AddCommM
onoid M₂] {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}   {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {r
e₂₁ : RingHomInvPair σ₂₁ σ₁₂} [inst_4 : _root_.Module R M]   [inst_5 : _root_.Mo
dule R₂ M₂] (f : M ≃ₛₗ[σ₁₂] M₂) (U : Submodule R₂ M₂) (x : ↥U),   ↑((f.ofSubmodu
le' U).symm x) = f.symm ↑x
参数：f : M ≃ₛₗ[σ₁₂] M₂；U : Submodule R₂ M₂；x : ↥U；(f.ofSubmodule' U).symm x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofSubmodule'_symm_apply [Module R M] [Module R₂ M₂] (f : M ≃ₛₗ[σ₁₂] M₂)
    (U : Submodule R₂ M₂) (x : U) : ((f.ofSubmodule' U).symm x : M) = f.symm (x : M₂) :=
  rfl

variable (p)

/-- The top submodule of `M` is linearly equivalent to `M`. -/
/-
**LinearEquiv.ofTop** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：ofTop (h : p = ⊤) : p ≃ₗ[R] M
参数：h : p = ⊤。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The top submodule of `M` is linearly equivalent to `M`.
-/
def ofTop (h : p = ⊤) : p ≃ₗ[R] M :=
  { p.subtype with
    invFun := fun x => ⟨x, h.symm ▸ trivial⟩ }

@[simp]
/-
**LinearEquiv.ofTop_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：ofTop_apply {h} (x : p) : ofTop p h x = x
参数：x : p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofTop_apply {h} (x : p) : ofTop p h x = x :=
  rfl

@[simp]
/-
**LinearEquiv.coe_ofTop_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：coe_ofTop_symm_apply {h} (x : M) : ((ofTop p h).symm x : M) = x
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofTop_symm_apply {h} (x : M) : ((ofTop p h).symm x : M) = x :=
  rfl
/-
**LinearEquiv.ofTop_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：ofTop_symm_apply {h} (x : M) : (ofTop p h).symm x = ⟨x, h.symm ▸ trivial⟩
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofTop_symm_apply {h} (x : M) : (ofTop p h).symm x = ⟨x, h.symm ▸ trivial⟩ :=
  rfl

@[simp]
/-
**LinearEquiv.toLinearMap_ofTop** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：toLinearMap_ofTop {h} : (ofTop p h).toLinearMap = p.subtype
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_ofTop {h} : (ofTop p h).toLinearMap = p.subtype :=
  rfl

@[simp]
/-
**LinearEquiv.range** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ : Type u_7} [inst : Se
miring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M] [inst_3 : AddCommM
onoid M₂] {module_M : _root_.Module R M}   {module_M₂ : _root_.Module R₂ M₂} {σ₁
₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} {re₁₂ : RingHomInvPair σ₁₂ σ₂₁}   {re₂₁ : RingHom
InvPair σ₂₁ σ₁₂} (e : M ≃ₛₗ[σ₁₂] M₂), (↑e).range = ⊤
参数：e : M ≃ₛₗ[σ₁₂] M₂；↑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
protected theorem range : LinearMap.range (e : M →ₛₗ[σ₁₂] M₂) = ⊤ :=
  LinearMap.range_eq_top.2 e.toEquiv.surjective
/-
**LinearEquiv.eq_bot_of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：eq_bot_of_equiv [Module R₂ M₂] (e : p ≃ₛₗ[σ₁₂] (⊥ : Submodule R₂ M₂)) : p 
= ⊥
参数：e : p ≃ₛₗ[σ₁₂] (⊥ : Submodule R₂ M₂)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.mk_eq_zero`：mk_eq_zero {x} (h : x in p) : (⟨x, h⟩ : p) = 0 ↔ x
 = 0
· 使用定理 `LinearEquiv.map_eq_zero_iff`：map_eq_zero_iff {x : M} : e x = 0 ↔ x = 0
· 使用定理 `Submodule.eq_zero_of_bot_submodule`：∀ {R : Type u_1} {M : Type u_5} [ins
t : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (b : ↥⊥)
,   b = 0
-/
theorem eq_bot_of_equiv [Module R₂ M₂] (e : p ≃ₛₗ[σ₁₂] (⊥ : Submodule R₂ M₂)) : p = ⊥ := by
  refine bot_unique (SetLike.le_def.2 fun b hb => (Submodule.mem_bot R).2 ?_)
  rw [← p.mk_eq_zero hb, ← e.map_eq_zero_iff]
  apply Submodule.eq_zero_of_bot_submodule

@[simp]
/-
**LinearEquiv.range_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：range_comp [RingHomSurjective σ₂₃] [RingHomSurjective σ₁₃] : LinearMap.ran
ge (h.comp (e : M ->ₛₗ[σ₁₂] M₂) : M ->ₛₗ[σ₁₃] M₃) = LinearMap.range h
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.range_comp_of_range_eq_top`：range_comp_of_range_eq_top [RingHo
mSurjective τ₁₂] [RingHomSurjective τ₂₃] [RingHomSurjective τ₁₃] {f : M ->ₛₗ[τ₁₂
] M₂} (g : M₂ ->ₛₗ[τ₂₃] M₃…
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `LinearEquiv.range`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ :
 Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid 
M] [ins…
-/
theorem range_comp [RingHomSurjective σ₂₃] [RingHomSurjective σ₁₃] :
    LinearMap.range (h.comp (e : M →ₛₗ[σ₁₂] M₂) : M →ₛₗ[σ₁₃] M₃) = LinearMap.range h :=
  LinearMap.range_comp_of_range_eq_top _ e.range

variable {f g}

/-- A linear map `f : M →ₗ[R] M₂` with a left-inverse `g : M₂ →ₗ[R] M` defines a linear
equivalence between `M` and `f.range`.

This is a computable alternative to `LinearEquiv.ofInjective`, and a bidirectional version of
`LinearMap.rangeRestrict`. -/
/-
**LinearEquiv.ofLeftInverse** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：ofLeftInverse [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {g : M₂ ->
 M} (h : Function.LeftInverse g f) : M ≃ₛₗ[σ₁₂] (LinearMap.range f)
参数：h : Function.LeftInverse g f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…

--- 原说明 ---
A linear map `f : M →ₗ[R] M₂` with a left-inverse `g : M₂ →ₗ[R] M` defines a lin
ear
equivalence between `M` and `f.range`.

This is a computable alternative to `LinearEquiv.ofInjective`, and a bidirection
al version of
`LinearMap.rangeRestrict`.
-/
def ofLeftInverse [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {g : M₂ → M}
    (h : Function.LeftInverse g f) : M ≃ₛₗ[σ₁₂] (LinearMap.range f) :=
  { LinearMap.rangeRestrict f with
    toFun := LinearMap.rangeRestrict f
    invFun := g ∘ (LinearMap.range f).subtype
    left_inv := h
    right_inv := fun x =>
      Subtype.ext <|
        let ⟨x', hx'⟩ := LinearMap.mem_range.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }

@[simp]
/-
**LinearEquiv.ofLeftInverse_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：ofLeftInverse_apply [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] (h :
 Function.LeftInverse g f) (x : M) : ↑(ofLeftInverse h x) = f x
参数：h : Function.LeftInverse g f；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
-/
theorem ofLeftInverse_apply [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
    (h : Function.LeftInverse g f) (x : M) : ↑(ofLeftInverse h x) = f x :=
  rfl

@[simp]
/-
**LinearEquiv.ofLeftInverse_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：ofLeftInverse_symm_apply [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
 (h : Function.LeftInverse g f) (x : LinearMap.range f) : (ofLeftInverse h).symm
 x = g x
参数：h : Function.LeftInverse g f；x : LinearMap.range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
-/
theorem ofLeftInverse_symm_apply [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
    (h : Function.LeftInverse g f) (x : LinearMap.range f) : (ofLeftInverse h).symm x = g x :=
  rfl

variable (f)

/-- An `Injective` linear map `f : M →ₗ[R] M₂` defines a linear equivalence
between `M` and `f.range`. See also `LinearMap.ofLeftInverse`. -/
/-
**LinearEquiv.ofInjective** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：ofInjective [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] (h : Injecti
ve f) : M ≃ₛₗ[σ₁₂] LinearMap.range f
参数：h : Injective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `Injective` linear map `f : M →ₗ[R] M₂` defines a linear equivalence
between `M` and `f.range`. See also `LinearMap.ofLeftInverse`.
-/
noncomputable def ofInjective [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] (h : Injective f) :
    M ≃ₛₗ[σ₁₂] LinearMap.range f :=
  ofLeftInverse <| Classical.choose_spec h.hasLeftInverse

@[simp]
/-
**LinearEquiv.ofInjective_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：ofInjective_apply [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {h : I
njective f} (x : M) : ↑(ofInjective f h x) = f x
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
-/
theorem ofInjective_apply [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {h : Injective f}
    (x : M) : ↑(ofInjective f h x) = f x :=
  rfl

@[simp]
/-
**LinearEquiv.ofInjective_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `LinearEquiv`。
形式化陈述：ofInjective_symm_apply [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {
h : Injective f} (x : LinearMap.range f) : f ((ofInjective f h).symm x) = x
参数：x : LinearMap.range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `LinearMap.mem_range_self`：mem_range_self [RingHomSurjective τ₁₂] (f : M 
->ₛₗ[τ₁₂] M₂) (x : M) : f x in range f
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
lemma ofInjective_symm_apply [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {h : Injective f}
    (x : LinearMap.range f) :
    f ((ofInjective f h).symm x) = x := by
  obtain ⟨-, ⟨y, rfl⟩⟩ := x
  have : ⟨f y, LinearMap.mem_range_self f y⟩ = LinearEquiv.ofInjective f h y := rfl
  simp [this]

/-- A bijective linear map is a linear equivalence. -/
/-
**LinearEquiv.ofBijective** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：ofBijective [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] (hf : Biject
ive f) : M ≃ₛₗ[σ₁₂] M₂
参数：hf : Bijective f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…

--- 原说明 ---
A bijective linear map is a linear equivalence.
-/
noncomputable def ofBijective [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] (hf : Bijective f) :
    M ≃ₛₗ[σ₁₂] M₂ :=
  (ofInjective f hf.injective).trans <| ofTop _ <|
    LinearMap.range_eq_top.2 hf.surjective

@[simp]
/-
**LinearEquiv.ofBijective_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：ofBijective_apply [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {hf} (
x : M) : ofBijective f hf x = f x
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofBijective_apply [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {hf} (x : M) :
    ofBijective f hf x = f x :=
  rfl

@[simp]
/-
**LinearEquiv.ofBijective_symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEqui
v`。
形式化陈述：ofBijective_symm_apply_apply [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ 
σ₁₂] {h} (x : M) : (ofBijective f h).symm (f x) = x
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofBijective_symm_apply_apply [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {h} (x : M) :
    (ofBijective f h).symm (f x) = x := by
  simp [LinearEquiv.symm_apply_eq]

@[simp]
/-
**LinearEquiv.apply_ofBijective_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEqui
v`。
形式化陈述：apply_ofBijective_symm_apply [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ 
σ₁₂] {h} (x : M₂) : f ((ofBijective f h).symm x) = x
参数：x : M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.ofBijective_apply`：ofBijective_apply [RingHomInvPair σ₁₂ σ₂₁
] [RingHomInvPair σ₂₁ σ₁₂] {hf} (x : M) : ofBijective f hf x = f x
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
-/
theorem apply_ofBijective_symm_apply [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {h}
    (x : M₂) : f ((ofBijective f h).symm x) = x := by
  rw [← ofBijective_apply f (hf := h) ((ofBijective f h).symm x), apply_symm_apply]

end

end AddCommMonoid

end LinearEquiv

namespace Submodule

section Module

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- Given `p` a submodule of the module `M` and `q` a submodule of `p`, `p.equivSubtypeMap q`
is the natural `LinearEquiv` between `q` and `q.map p.subtype`. -/
/-
**Submodule.equivSubtypeMap** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：equivSubtypeMap (p : Submodule R M) (q : Submodule R p) : q ≃ₗ[R] q.map p.
subtype
参数：p : Submodule R M；q : Submodule R p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `p` a submodule of the module `M` and `q` a submodule of `p`, `p.equivSubt
ypeMap q`
is the natural `LinearEquiv` between `q` and `q.map p.subtype`.
-/
def equivSubtypeMap (p : Submodule R M) (q : Submodule R p) : q ≃ₗ[R] q.map p.subtype :=
  { (p.subtype.domRestrict q).codRestrict _ (by rintro ⟨x, hx⟩; exact ⟨x, hx, rfl⟩) with
    invFun := by
      rintro ⟨x, hx⟩
      refine ⟨⟨x, ?_⟩, ?_⟩ <;> rcases hx with ⟨⟨_, h⟩, _, rfl⟩ <;> assumption }

@[simp]
/-
**Submodule.equivSubtypeMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：equivSubtypeMap_apply {p : Submodule R M} {q : Submodule R p} (x : q) : (p
.equivSubtypeMap q x : M) = p.subtype.domRestrict q x
参数：x : q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equivSubtypeMap_apply {p : Submodule R M} {q : Submodule R p} (x : q) :
    (p.equivSubtypeMap q x : M) = p.subtype.domRestrict q x :=
  rfl

@[simp]
/-
**Submodule.equivSubtypeMap_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：equivSubtypeMap_symm_apply {p : Submodule R M} {q : Submodule R p} (x : q.
map p.subtype) : ((p.equivSubtypeMap q).symm x : M) = x
参数：x : q.map p.subtype。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equivSubtypeMap_symm_apply {p : Submodule R M} {q : Submodule R p} (x : q.map p.subtype) :
    ((p.equivSubtypeMap q).symm x : M) = x := rfl

/-- A linear injection `M ↪ N` restricts to an equivalence `f⁻¹ p ≃ p` for any submodule `p`
contained in its range. -/
@[simps! apply]
/-
**Submodule.comap_equiv_self_of_inj_of_le** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：comap_equiv_self_of_inj_of_le {f : M ->ₗ[R] N} {p : Submodule R N} (hf : I
njective f) (h : p <= LinearMap.range f) : p.comap f ≃ₗ[R] p
参数：hf : Injective f；h : p <= LinearMap.range f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear injection `M ↪ N` restricts to an equivalence `f⁻¹ p ≃ p` for any submo
dule `p`
contained in its range.
-/
noncomputable def comap_equiv_self_of_inj_of_le {f : M →ₗ[R] N} {p : Submodule R N}
    (hf : Injective f) (h : p ≤ LinearMap.range f) :
    p.comap f ≃ₗ[R] p :=
  LinearEquiv.ofBijective
  ((f ∘ₗ (p.comap f).subtype).codRestrict p <| fun ⟨_, hx⟩ ↦ mem_comap.mp hx)
  (⟨fun x y hxy ↦ by simpa using hf (Subtype.ext_iff.mp hxy),
    fun ⟨x, hx⟩ ↦ by obtain ⟨y, rfl⟩ := h hx; exact ⟨⟨y, hx⟩, by simp [Subtype.ext_iff]⟩⟩)

end Module

end Submodule

namespace LinearMap

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
  [Module R M] [Module R M₁] [Module R M₂] [Module R M₃]

section

variable (f : M₁ →ₗ[R] M₂) (i : M₃ →ₗ[R] M₂) (hi : Injective i)
  (hf : ∀ x, f x ∈ LinearMap.range i)

/-- The restriction of a linear map on the target to a submodule of the target given by
an inclusion. -/
/-
**LinearMap.codRestrictOfInjective** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：codRestrictOfInjective : M₁ ->ₗ[R] M₃
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a linear map on the target to a submodule of the target given
 by
an inclusion.
-/
noncomputable def codRestrictOfInjective : M₁ →ₗ[R] M₃ :=
  (LinearEquiv.ofInjective i hi).symm ∘ₗ f.codRestrict (LinearMap.range i) hf

@[simp]
/-
**LinearMap.codRestrictOfInjective_comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `LinearM
ap`。
形式化陈述：codRestrictOfInjective_comp_apply (x : M₁) : i (LinearMap.codRestrictOfInj
ective f i hi hf x) = f x
参数：x : M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearEquiv.ofInjective_symm_apply`：ofInjective_symm_apply [RingHomInvPa
ir σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {h : Injective f} (x : LinearMap.range f) :
 f ((ofInjective f h).sy…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma codRestrictOfInjective_comp_apply (x : M₁) :
    i (LinearMap.codRestrictOfInjective f i hi hf x) = f x := by
  simp [LinearMap.codRestrictOfInjective]

@[simp]
/-
**LinearMap.codRestrictOfInjective_comp** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：codRestrictOfInjective_comp : i ∘ₗ LinearMap.codRestrictOfInjective f i hi
 hf = f
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
· 使用引理 `LinearMap.codRestrictOfInjective_comp_apply`：codRestrictOfInjective_comp
_apply (x : M₁) : i (LinearMap.codRestrictOfInjective f i hi hf x) = f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma codRestrictOfInjective_comp :
    i ∘ₗ LinearMap.codRestrictOfInjective f i hi hf = f := by
  ext
  simp

end

variable (f : M₁ →ₗ[R] M₂ →ₗ[R] M) (i : M₃ →ₗ[R] M) (hi : Injective i)
  (hf : ∀ x y, f x y ∈ LinearMap.range i)

/-- The restriction of a bilinear map to a submodule in which it takes values. -/
/-
**LinearMap.codRestrict** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：codRestrict (p : Submodule R₂ M₂) (f : M ->ₛₗ[σ₁₂] M₂) (h : forall c, f c 
in p) : M ->ₛₗ[σ₁₂] p where toFun c
参数：p : Submodule R₂ M₂；f : M ->ₛₗ[σ₁₂] M₂；h : forall c, f c in p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a bilinear map to a submodule in which it takes values.
-/
noncomputable def codRestrict₂ :
    M₁ →ₗ[R] M₂ →ₗ[R] M₃ :=
  let e : LinearMap.range i ≃ₗ[R] M₃ := (LinearEquiv.ofInjective i hi).symm
  { toFun := fun x ↦ e.comp <| (f x).codRestrict (p := LinearMap.range i) (hf x)
    map_add' := by intro x₁ x₂; ext y; simp [f.map_add, ← e.map_add, codRestrict]
    map_smul' := by intro t x; ext y; simp [f.map_smul, ← e.map_smul, codRestrict] }

@[simp]
/-
**LinearMap.codRestrict** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：codRestrict (p : Submodule R₂ M₂) (f : M ->ₛₗ[σ₁₂] M₂) (h : forall c, f c 
in p) : M ->ₛₗ[σ₁₂] p where toFun c
参数：p : Submodule R₂ M₂；f : M ->ₛₗ[σ₁₂] M₂；h : forall c, f c in p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma codRestrict₂_apply (x : M₁) (y : M₂) :
    i (codRestrict₂ f i hi hf x y) = f x y := by
  simp [codRestrict₂]

end LinearMap

