/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Submonoid.Membership
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.PUnit
public import Mathlib.Data.Set.Subsingleton
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# The lattice structure on `Submodule`s

This file defines the lattice structure on submodules, `Submodule.CompleteLattice`, with `⊥`
defined as `{0}` and `⊓` defined as intersection of the underlying carrier.
If `p` and `q` are submodules of a module, `p ≤ q` means that `p ⊆ q`.


## Implementation notes

This structure should match the `AddSubmonoid.CompleteLattice` structure, and we should try
to unify the APIs where possible.

-/

@[expose] public section

universe v

variable {R S M : Type*}

section AddCommMonoid

variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]
variable [SMul S R] [IsScalarTower S R M]
variable {p q : Submodule R M}

namespace Submodule

/-!
## Bottom element of a submodule
-/

/-- The set `{0}` is the bottom element of the lattice of submodules. -/
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set `{0}` is the bottom element of the lattice of submodules.
-/
instance : Bot (Submodule R M) :=
  ⟨{ (⊥ : AddSubmonoid M) with
      carrier := {0}
      smul_mem' := by simp }⟩
/-
**Submodule.inhabited'** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：inhabited' : Inhabited (Submodule R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabited' : Inhabited (Submodule R M) :=
  ⟨⊥⟩

@[simp]
/-
**Submodule.bot_coe** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：bot_coe : ((⊥ : Submodule R M) : Set M) = {0}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_coe : ((⊥ : Submodule R M) : Set M) = {0} :=
  rfl

@[simp]
/-
**Submodule.bot_toAddSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：bot_toAddSubmonoid : (⊥ : Submodule R M).toAddSubmonoid = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_toAddSubmonoid : (⊥ : Submodule R M).toAddSubmonoid = ⊥ :=
  rfl

@[simp]
/-
**Submodule.bot_toAddSubgroup** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：bot_toAddSubgroup {R M} [Ring R] [AddCommGroup M] [Module R M] : (⊥ : Subm
odule R M).toAddSubgroup = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma bot_toAddSubgroup {R M} [Ring R] [AddCommGroup M] [Module R M] :
    (⊥ : Submodule R M).toAddSubgroup = ⊥ := rfl

variable (R) in
@[simp]
/-
**Submodule.mem_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
-/
theorem mem_bot {x : M} : x ∈ (⊥ : Submodule R M) ↔ x = 0 :=
  Set.mem_singleton_iff
/-
**Submodule.mk_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   (carrier : AddSubmonoid M) (smul_mem' : ∀ (c
 : R) {x : M}, x ∈ carrier.carrier → c • x ∈ carrier.carrier),   { toAddSubmonoi
d := carrier, smul_mem' := smul_mem' } = ⊥ ↔ carrier = ⊥
参数：carrier : AddSubmonoid M；smul_mem' : ∀ (c : R) {x : M}, x ∈ carrier.carrier →
 c • x ∈ carrier.carrier。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma mk_eq_bot (carrier : AddSubmonoid M) (smul_mem') :
    mk carrier smul_mem' = (⊥ : Submodule R M) ↔ carrier = ⊥ := by simp [← toAddSubmonoid_inj]
/-
**Submodule.uniqueBot** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：uniqueBot : Unique (⊥ : Submodule R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance uniqueBot : Unique (⊥ : Submodule R M) :=
  ⟨inferInstance, fun x ↦ Subtype.ext <| (mem_bot R).1 x.mem⟩
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderBot (Submodule R M) where
  bot_le p x := by simp +contextual [zero_mem]
/-
**Submodule.eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   (p : Submodule R M), p = ⊥ ↔ ∀ x ∈ p, x = 0
参数：p : Submodule R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
-/
protected theorem eq_bot_iff (p : Submodule R M) : p = ⊥ ↔ ∀ x ∈ p, x = (0 : M) :=
  ⟨fun h ↦ h.symm ▸ fun _ hx ↦ (mem_bot R).mp hx,
    fun h ↦ eq_bot_iff.mpr fun x hx ↦ (mem_bot R).mpr (h x hx)⟩

@[ext high]
/-
**Submodule.bot_ext** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M] (x y : ↥⊥),   x = y
参数：x y : ↥⊥。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
protected theorem bot_ext (x y : (⊥ : Submodule R M)) : x = y := by
  subsingleton
/-
**Submodule.ne_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   (p : Submodule R M), p ≠ ⊥ ↔ ∃ x ∈ p, x ≠ 0
参数：p : Submodule R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.eq_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p = ⊥ ↔ ∀…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem ne_bot_iff (p : Submodule R M) : p ≠ ⊥ ↔ ∃ x ∈ p, x ≠ (0 : M) := by
  simp only [ne_eq, p.eq_bot_iff, not_forall, exists_prop]
/-
**Submodule.nonzero_mem_of_bot_lt** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：nonzero_mem_of_bot_lt {p : Submodule R M} (bot_lt : ⊥ < p) : exists a : p,
 a != 0
参数：bot_lt : ⊥ < p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.ne_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p ≠ ⊥ ↔ ∃…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem nonzero_mem_of_bot_lt {p : Submodule R M} (bot_lt : ⊥ < p) : ∃ a : p, a ≠ 0 :=
  let ⟨b, hb₁, hb₂⟩ := p.ne_bot_iff.mp bot_lt.ne'
  ⟨⟨b, hb₁⟩, hb₂ ∘ congr_arg Subtype.val⟩
/-
**Submodule.exists_mem_ne_zero_of_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：exists_mem_ne_zero_of_ne_bot {p : Submodule R M} (h : p != ⊥) : exists b :
 M, b in p ∧ b != 0
参数：h : p != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.ne_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p ≠ ⊥ ↔ ∃…
-/
theorem exists_mem_ne_zero_of_ne_bot {p : Submodule R M} (h : p ≠ ⊥) : ∃ b : M, b ∈ p ∧ b ≠ 0 :=
  let ⟨b, hb₁, hb₂⟩ := p.ne_bot_iff.mp h
  ⟨b, hb₁, hb₂⟩

-- FIXME: we default PUnit to PUnit.{1} here without the explicit universe annotation
/-- The bottom submodule is linearly equivalent to punit as an `R`-module. -/
@[simps]
/-
**Submodule.botEquivPUnit** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：botEquivPUnit : (⊥ : Submodule R M) ≃ₗ[R] PUnit.{v + 1} where toFun _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bottom submodule is linearly equivalent to punit as an `R`-module.
-/
def botEquivPUnit : (⊥ : Submodule R M) ≃ₗ[R] PUnit.{v + 1} where
  toFun _ := PUnit.unit
  invFun _ := 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-
**Submodule.subsingleton_iff_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：subsingleton_iff_eq_bot : Subsingleton p ↔ p = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `subsingleton_iff`：subsingleton_iff : Subsingleton α ↔ forall x y : α, x 
= y
· 使用定理 `Submodule.eq_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p = ⊥ ↔ ∀…
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem subsingleton_iff_eq_bot : Subsingleton p ↔ p = ⊥ := by
  rw [subsingleton_iff, Submodule.eq_bot_iff]
  refine ⟨fun h x hx ↦ by simpa using h ⟨x, hx⟩ ⟨0, p.zero_mem⟩,
    fun h ⟨x, hx⟩ ⟨y, hy⟩ ↦ by simp [h x hx, h y hy]⟩
/-
**Submodule.eq_bot_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：eq_bot_of_subsingleton [Subsingleton p] : p = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.subsingleton_iff_eq_bot`：subsingleton_iff_eq_bot : Subsingleto
n p ↔ p = ⊥
-/
theorem eq_bot_of_subsingleton [Subsingleton p] : p = ⊥ :=
  subsingleton_iff_eq_bot.mp inferInstance
/-
**Submodule.nontrivial_iff_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：nontrivial_iff_ne_bot : Nontrivial p ↔ p != ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_not_comm`：iff_not_comm : (a ↔ ¬b) ↔ (b ↔ ¬a)
· 使用定理 `not_nontrivial_iff_subsingleton`：not_nontrivial_iff_subsingleton : ¬Nont
rivial α ↔ Subsingleton α
· 使用定理 `Submodule.subsingleton_iff_eq_bot`：subsingleton_iff_eq_bot : Subsingleto
n p ↔ p = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nontrivial_iff_ne_bot : Nontrivial p ↔ p ≠ ⊥ := by
  rw [iff_not_comm, not_nontrivial_iff_subsingleton, subsingleton_iff_eq_bot]

/-!
## Top element of a submodule
-/

/-- The universal set is the top element of the lattice of submodules. -/
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The universal set is the top element of the lattice of submodules.
-/
instance : Top (Submodule R M) :=
  ⟨{ (⊤ : AddSubmonoid M) with
      carrier := Set.univ
      smul_mem' := fun _ _ _ ↦ trivial }⟩

@[simp]
/-
**Submodule.top_coe** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：top_coe : ((⊤ : Submodule R M) : Set M) = Set.univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_coe : ((⊤ : Submodule R M) : Set M) = Set.univ :=
  rfl

@[simp]
/-
**Submodule.coe_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_eq_univ : (p : Set M) = Set.univ ↔ p = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_comm`：∀ {a b : Prop}, (a ↔ b) ↔ (b ↔ a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.coe_set_eq`：coe_set_eq : (p : Set B) = q ↔ p = q
· 使用定理 `Submodule.top_coe`：top_coe : ((⊤ : Submodule R M) : Set M) = Set.univ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_eq_univ : (p : Set M) = Set.univ ↔ p = ⊤ := by
  rw [iff_comm, ← SetLike.coe_set_eq, top_coe]
/-
**Submodule.mem_top** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
@[simp] lemma mem_top {x : M} : x ∈ (⊤ : Submodule R M) := trivial

@[simp]
/-
**Submodule.top_toAddSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：top_toAddSubmonoid : (⊤ : Submodule R M).toAddSubmonoid = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_toAddSubmonoid : (⊤ : Submodule R M).toAddSubmonoid = ⊤ :=
  rfl

@[simp]
/-
**Submodule.top_toAddSubgroup** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：top_toAddSubgroup {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] : (
⊤ : Submodule R M).toAddSubgroup = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma top_toAddSubgroup {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] :
    (⊤ : Submodule R M).toAddSubgroup = ⊤ := rfl

@[simp]
/-
**Submodule.toAddSubgroup_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：toAddSubgroup_eq_top {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] 
{p : Submodule R M} : p.toAddSubgroup = ⊤ ↔ p = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toAddSubgroup_eq_top {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {p : Submodule R M} : p.toAddSubgroup = ⊤ ↔ p = ⊤ := by simp [← toAddSubgroup_inj]
/-
**Submodule.mk_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   (carrier : AddSubmonoid M) (smul_mem' : ∀ (c
 : R) {x : M}, x ∈ carrier.carrier → c • x ∈ carrier.carrier),   { toAddSubmonoi
d := carrier, smul_mem' := smul_mem' } = ⊤ ↔ carrier = ⊤
参数：carrier : AddSubmonoid M；smul_mem' : ∀ (c : R) {x : M}, x ∈ carrier.carrier →
 c • x ∈ carrier.carrier。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma mk_eq_top (carrier : AddSubmonoid M) (smul_mem') :
    mk carrier smul_mem' = (⊤ : Submodule R M) ↔ carrier = ⊤ := by simp [← toAddSubmonoid_inj]
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderTop (Submodule R M) where
  le_top _ _ _ := trivial
/-
**Submodule.eq_top_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：eq_top_iff' {p : Submodule R M} : p = ⊤ ↔ forall x, x in p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `trivial`：True
-/
theorem eq_top_iff' {p : Submodule R M} : p = ⊤ ↔ ∀ x, x ∈ p :=
  eq_top_iff.trans ⟨fun h _ ↦ h trivial, fun h x _ ↦ h x⟩

/-- The top submodule is linearly equivalent to the module.

This is the module version of `AddSubmonoid.topEquiv`. -/
@[simps]
/-
**Submodule.topEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：topEquiv : (⊤ : Submodule R M) ≃ₗ[R] M where toFun x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤

--- 原说明 ---
The top submodule is linearly equivalent to the module.

This is the module version of `AddSubmonoid.topEquiv`.
-/
def topEquiv : (⊤ : Submodule R M) ≃ₗ[R] M where
  toFun x := x
  invFun x := ⟨x, mem_top⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-!
## Infima & suprema in a submodule
-/

/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
## Infima & suprema in a submodule
-/
instance : InfSet (Submodule R M) :=
  ⟨fun S ↦
    { carrier := ⋂ s ∈ S, (s : Set M)
      zero_mem' := by simp [zero_mem]
      add_mem' := by simp +contextual [add_mem]
      smul_mem' := by simp +contextual [smul_mem] }⟩
/-
**Submodule.isGLB_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   {S : Set (Submodule R M)}, IsGLB S (sInf S)
参数：Submodule R M；sInf S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGLB.of_image`：IsGLB.of_image [Preorder α] [Preorder β] {f : α -> β} (h
f : forall {x y}, f x <= f y ↔ x <= y) {s : Set α} {x : α} (hx : IsGLB (f '' s) 
(f x…
· 使用定理 `SetLike.coe_subset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike 
A B] [inst_1 : LE A] [IsConcreteLE A B] {S T : A}, ↑S ⊆ ↑T ↔ S ≤ T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `isGLB_biInf`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] 
{s : Set β} {f : β → α}, IsGLB (f '' s) (⨅ x ∈ s, f x)
-/
protected theorem isGLB_sInf {S : Set (Submodule R M)} : IsGLB S (sInf S) :=
  .of_image SetLike.coe_subset_coe isGLB_biInf
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Min (Submodule R M) :=
  ⟨fun p q ↦
    { carrier := p ∩ q
      zero_mem' := by simp [zero_mem]
      add_mem' := by simp +contextual [add_mem]
      smul_mem' := by simp +contextual [smul_mem] }⟩
/-
**Submodule.completeLattice** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：completeLattice : CompleteLattice (Submodule R M) where sup a b
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.isGLB_sInf`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {S : Set (Submodule 
R M)}, IsG…
-/
instance completeLattice : CompleteLattice (Submodule R M) where
  sup a b := sInf { x | a ≤ x ∧ b ≤ x }
  le_sup_left _ _ := Set.subset_iInter₂ fun _ ⟨h, _⟩ ↦ h
  le_sup_right _ _ := Set.subset_iInter₂ fun _ ⟨_, h⟩ ↦ h
  sup_le _ _ _ h₁ h₂ := Set.biInter_subset_of_mem ⟨h₁, h₂⟩
  inf := (· ⊓ ·)
  le_inf _ _ _ := Set.subset_inter
  inf_le_left _ _ := Set.inter_subset_left
  inf_le_right _ _ := Set.inter_subset_right
  sSup S := sInf {sm | ∀ s ∈ S, s ≤ sm}
  isLUB_sSup _ := isGLB_upperBounds.mp Submodule.isGLB_sInf
  isGLB_sInf _ := Submodule.isGLB_sInf

@[simp]
/-
**Submodule.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_inf : ↑(p ⊓ q) = (p inter q : Set M)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inf : ↑(p ⊓ q) = (p ∩ q : Set M) :=
  rfl

@[simp]
/-
**Submodule.mem_inf** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_inf {p q : Submodule R M} {x : M} : x in p ⊓ q ↔ x in p ∧ x in q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_inf {p q : Submodule R M} {x : M} : x ∈ p ⊓ q ↔ x ∈ p ∧ x ∈ q :=
  Iff.rfl

@[simp, norm_cast]
/-
**Submodule.coe_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_sInf (P : Set (Submodule R M)) : (↑(sInf P) : Set M) = ⋂ p in P, ↑p
参数：P : Set (Submodule R M)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sInf (P : Set (Submodule R M)) : (↑(sInf P) : Set M) = ⋂ p ∈ P, ↑p :=
  rfl

@[simp]
/-
**Submodule.coe_finsetInf** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_finsetInf {ι} (s : Finset ι) (p : ι -> Submodule R M) : (↑(s.inf p) : 
Set M) = ⋂ i in s, ↑(p i)
参数：s : Finset ι；p : ι -> Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.inf_empty`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeInf
 α] [inst_1 : OrderTop α] {f : β → α}, ∅.inf f = ⊤
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_of_empty`：iInter_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋂ i,
 s i = univ
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iInter_univ`：iInter_univ : (⋂ _ : ι, univ : Set α) = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.inf_insert`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeIn
f α] [inst_1 : OrderTop α] {s : Finset β} {f : β → α}   [inst_2 : DecidableEq β]
 {b : β…
· 使用定理 `Submodule.coe_inf`：coe_inf : ↑(p ⊓ q) = (p inter q : Set M)
· 使用定理 `Set.iInter_iInter_eq_or_left`：iInter_iInter_eq_or_left {b : β} {p : β ->
 Prop} {s : forall x : β, x = b ∨ p x -> Set α} : ⋂ (x) (h), s x h = s b (Or.inl
 rfl) inter ⋂ (x) …
-/
theorem coe_finsetInf {ι} (s : Finset ι) (p : ι → Submodule R M) :
    (↑(s.inf p) : Set M) = ⋂ i ∈ s, ↑(p i) := by
  let := Classical.decEq ι
  refine s.induction_on ?_ fun i s _ ih ↦ ?_
  · simp
  · rw [Finset.inf_insert, coe_inf, ih]
    simp

@[simp, norm_cast]
/-
**Submodule.coe_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_iInf {ι} (p : ι -> Submodule R M) : (↑(⨅ i, p i) : Set M) = ⋂ i, ↑(p i
)
参数：p : ι -> Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : InfSet α] (s : ι → α), iI
nf s = sInf (Set.range s)
· 使用定理 `Submodule.coe_sInf`：coe_sInf (P : Set (Submodule R M)) : (↑(sInf P) : Se
t M) = ⋂ p in P, ↑p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_exists`：iInter_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.iInter_iInter_eq'`：iInter_iInter_eq' {f : ι -> α} {g : α -> Set β} :
 ⋂ (x) (y) (_ : f y = x), g x = ⋂ y, g (f y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_iInf {ι} (p : ι → Submodule R M) : (↑(⨅ i, p i) : Set M) = ⋂ i, ↑(p i) := by
  rw [iInf, coe_sInf]; simp only [Set.mem_range, Set.iInter_exists, Set.iInter_iInter_eq']

@[simp]
/-
**Submodule.mem_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_sInf {S : Set (Submodule R M)} {x : M} : x in sInf S ↔ forall p in S, 
x in p
参数：Submodule R M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_iInter₂`：mem_iInter₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋂ (i) (j), s i j) ↔ forall i j, x in s i j
-/
theorem mem_sInf {S : Set (Submodule R M)} {x : M} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p :=
  Set.mem_iInter₂

@[simp]
/-
**Submodule.mem_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_iInf {ι} (p : ι -> Submodule R M) {x} : x in ⨅ i, p i ↔ forall i, x in
 p i
参数：p : ι -> Submodule R M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Submodule.coe_iInf`：coe_iInf {ι} (p : ι -> Submodule R M) : (↑(⨅ i, p i)
 : Set M) = ⋂ i, ↑(p i)
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_iInf {ι} (p : ι → Submodule R M) {x} : x ∈ ⨅ i, p i ↔ ∀ i, x ∈ p i := by
  rw [← SetLike.mem_coe, coe_iInf, Set.mem_iInter]; rfl

@[simp]
/-
**Submodule.mem_finsetInf** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_finsetInf {ι} {s : Finset ι} {p : ι -> Submodule R M} {x : M} : x in s
.inf p ↔ forall i in s, x in p i
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
· 使用定理 `Submodule.coe_finsetInf`：coe_finsetInf {ι} (s : Finset ι) (p : ι -> Subm
odule R M) : (↑(s.inf p) : Set M) = ⋂ i in s, ↑(p i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_finsetInf {ι} {s : Finset ι} {p : ι → Submodule R M} {x : M} :
    x ∈ s.inf p ↔ ∀ i ∈ s, x ∈ p i := by
  simp only [← SetLike.mem_coe, coe_finsetInf, Set.mem_iInter]
/-
**Submodule.inf_iInf** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：inf_iInf {ι : Sort*} [Nonempty ι] {p : ι -> Submodule R M} (q : Submodule 
R M) : q ⊓ ⨅ i, p i = ⨅ i, q ⊓ p i
参数：q : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.coe_iInf`：coe_iInf {ι} (p : ι -> Submodule R M) : (↑(⨅ i, p i)
 : Set M) = ⋂ i, ↑(p i)
· 使用定理 `Set.inter_iInter`：inter_iInter [Nonempty ι] (s : Set β) (t : ι -> Set β)
 : (s inter ⋂ i, t i) = ⋂ i, s inter t i
-/
lemma inf_iInf {ι : Sort*} [Nonempty ι] {p : ι → Submodule R M} (q : Submodule R M) :
    q ⊓ ⨅ i, p i = ⨅ i, q ⊓ p i :=
  SetLike.coe_injective <| by simpa only [coe_inf, coe_iInf] using Set.inter_iInter _ _
/-
**Submodule.mem_sup_left** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_sup_left {S T : Submodule R M} : forall {x : M}, x in S -> x in S ⊔ T
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LE.le.eq_1`：∀ (α : Type u) [self : LE α], LE.le = self.1
-/
theorem mem_sup_left {S T : Submodule R M} : ∀ {x : M}, x ∈ S → x ∈ S ⊔ T := by
  have : S ≤ S ⊔ T := le_sup_left
  rw [LE.le] at this
  exact this
/-
**Submodule.mem_sup_right** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_sup_right {S T : Submodule R M} : forall {x : M}, x in T -> x in S ⊔ T
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LE.le.eq_1`：∀ (α : Type u) [self : LE α], LE.le = self.1
-/
theorem mem_sup_right {S T : Submodule R M} : ∀ {x : M}, x ∈ T → x ∈ S ⊔ T := by
  have : T ≤ S ⊔ T := le_sup_right
  rw [LE.le] at this
  exact this
/-
**Submodule.add_mem_sup** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：add_mem_sup {S T : Submodule R M} {s t : M} (hs : s in S) (ht : t in T) : 
s + t in S ⊔ T
参数：hs : s in S；ht : t in T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `Submodule.mem_sup_left`：mem_sup_left {S T : Submodule R M} : forall {x :
 M}, x in S -> x in S ⊔ T
· 使用定理 `Submodule.mem_sup_right`：mem_sup_right {S T : Submodule R M} : forall {x
 : M}, x in T -> x in S ⊔ T
-/
theorem add_mem_sup {S T : Submodule R M} {s t : M} (hs : s ∈ S) (ht : t ∈ T) : s + t ∈ S ⊔ T :=
  add_mem (mem_sup_left hs) (mem_sup_right ht)
/-
**Submodule.sub_mem_sup** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：sub_mem_sup {R' M' : Type*} [Ring R'] [AddCommGroup M'] [Module R' M'] {S 
T : Submodule R' M'} {s t : M'} (hs : s in S) (ht : t in T) : s - t in S ⊔ T
参数：hs : s in S；ht : t in T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Submodule.add_mem_sup`：add_mem_sup {S T : Submodule R M} {s t : M} (hs :
 s in S) (ht : t in T) : s + t in S ⊔ T
· 使用定理 `NegMemClass.neg_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Neg G} {inst_1 : SetLike S G} [self : NegMemClass S G] {s : S}   {x : G}, x ∈ s 
→ -x ∈ s
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
-/
theorem sub_mem_sup {R' M' : Type*} [Ring R'] [AddCommGroup M'] [Module R' M']
    {S T : Submodule R' M'} {s t : M'} (hs : s ∈ S) (ht : t ∈ T) : s - t ∈ S ⊔ T := by
  rw [sub_eq_add_neg]
  exact add_mem_sup hs (neg_mem ht)
/-
**Submodule.mem_iSup_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_iSup_of_mem {ι : Sort*} {b : M} {p : ι -> Submodule R M} (i : ι) (h : 
b in p i) : b in ⨆ i, p i
参数：i : ι；h : b in p i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
theorem mem_iSup_of_mem {ι : Sort*} {b : M} {p : ι → Submodule R M} (i : ι) (h : b ∈ p i) :
    b ∈ ⨆ i, p i :=
  (le_iSup p i) h
/-
**Submodule.sum_mem_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：sum_mem_iSup {ι : Type*} [Fintype ι] {f : ι -> M} {p : ι -> Submodule R M}
 (h : forall i, f i in p i) : (∑ i, f i) in ⨆ i, p i
参数：h : forall i, f i in p i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `Submodule.mem_iSup_of_mem`：mem_iSup_of_mem {ι : Sort*} {b : M} {p : ι ->
 Submodule R M} (i : ι) (h : b in p i) : b in ⨆ i, p i
-/
theorem sum_mem_iSup {ι : Type*} [Fintype ι] {f : ι → M} {p : ι → Submodule R M}
    (h : ∀ i, f i ∈ p i) : (∑ i, f i) ∈ ⨆ i, p i :=
  sum_mem fun i _ ↦ mem_iSup_of_mem i (h i)
/-
**Submodule.sum_mem_biSup** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：sum_mem_biSup {ι : Type*} {s : Finset ι} {f : ι -> M} {p : ι -> Submodule 
R M} (h : forall i in s, f i in p i) : (∑ i in s, f i) in ⨆ i in s, p i
参数：h : forall i in s, f i in p i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `Submodule.mem_iSup_of_mem`：mem_iSup_of_mem {ι : Sort*} {b : M} {p : ι ->
 Submodule R M} (i : ι) (h : b in p i) : b in ⨆ i, p i
-/
theorem sum_mem_biSup {ι : Type*} {s : Finset ι} {f : ι → M} {p : ι → Submodule R M}
    (h : ∀ i ∈ s, f i ∈ p i) : (∑ i ∈ s, f i) ∈ ⨆ i ∈ s, p i :=
  sum_mem fun i hi ↦ mem_iSup_of_mem i <| mem_iSup_of_mem hi (h i hi)

/-! Note that `Submodule.mem_iSup` is provided in `Mathlib/LinearAlgebra/Span/Defs.lean`. -/


/-
**Submodule.mem_sSup_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_sSup_of_mem {S : Set (Submodule R M)} {s : Submodule R M} (hs : s in S
) : forall {x : M}, x in s -> x in sSup S
参数：Submodule R M；hs : s in S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LE.le.eq_1`：∀ (α : Type u) [self : LE α], LE.le = self.1

--- 原说明 ---
Note that `Submodule.mem_iSup` is provided in `Mathlib/LinearAlgebra/Span/Defs.l
ean`.
-/
theorem mem_sSup_of_mem {S : Set (Submodule R M)} {s : Submodule R M} (hs : s ∈ S) :
    ∀ {x : M}, x ∈ s → x ∈ sSup S := by
  have := le_sSup hs
  rw [LE.le] at this
  exact this

@[simp]
/-
**Submodule.toAddSubmonoid_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：toAddSubmonoid_sSup (s : Set (Submodule R M)) : (sSup s).toAddSubmonoid = 
sSup (toAddSubmonoid '' s)
参数：s : Set (Submodule R M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_eq_iSup'`：sSup_eq_iSup' (s : Set α) : sSup s = ⨆ a : s, (a : α)
· 使用定理 `AddSubmonoid.iSup_induction'`：∀ {M : Type u_1} [inst : AddZeroClass M] {
ι : Sort u_4} (S : ι → AddSubmonoid M)   {motive : (x : M) → x ∈ ⨆ i, S i → Prop
},   (∀ (i : ι) (x…
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubmonoid.instAddSubmonoidClass`：∀ {M : Type u_1} [inst : AddZeroClas
s M], AddSubmonoidClass (AddSubmonoid M) M
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `sSup_le`：sSup_le (h : forall b in s, b <= a) : sSup s <= a
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem toAddSubmonoid_sSup (s : Set (Submodule R M)) :
    (sSup s).toAddSubmonoid = sSup (toAddSubmonoid '' s) := by
  let p : Submodule R M :=
    { toAddSubmonoid := sSup (toAddSubmonoid '' s)
      smul_mem' := fun t {m} h ↦ by
        simp_rw [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup, sSup_eq_iSup'] at h ⊢
        induction h using AddSubmonoid.iSup_induction' with
        | mem p x hx =>
          obtain ⟨-, ⟨p : Submodule R M, hp : p ∈ s, rfl⟩⟩ := p
          suffices p.toAddSubmonoid ≤ ⨆ q : toAddSubmonoid '' s, (q : AddSubmonoid M) by
            exact this (smul_mem p t hx)
          apply le_sSup
          rw [Subtype.range_coe_subtype]
          exact ⟨p, hp, rfl⟩
        | zero => simpa only [smul_zero] using zero_mem _
        | add _ _ _ _ mx my => revert mx my; simp_rw [smul_add]; exact add_mem }
  refine le_antisymm (?_ : sSup s ≤ p) ?_
  · exact sSup_le fun q hq ↦ le_sSup <| Set.mem_image_of_mem toAddSubmonoid hq
  · exact sSup_le fun _ ⟨q, hq, hq'⟩ ↦ hq'.symm ▸ le_sSup hq

variable (R)

@[simp]
/-
**Submodule.subsingleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：subsingleton_iff : Subsingleton (Submodule R M) ↔ Subsingleton M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `subsingleton_iff_bot_eq_top`：subsingleton_iff_bot_eq_top : (⊥ : α) = (⊤ 
: α) ↔ Subsingleton α
· 使用定理 `Submodule.toAddSubmonoid_inj`：toAddSubmonoid_inj : p.toAddSubmonoid = q.
toAddSubmonoid ↔ p = q
· 使用定理 `Submodule.bot_toAddSubmonoid`：bot_toAddSubmonoid : (⊥ : Submodule R M).t
oAddSubmonoid = ⊥
· 使用定理 `Submodule.top_toAddSubmonoid`：top_toAddSubmonoid : (⊤ : Submodule R M).t
oAddSubmonoid = ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `AddSubmonoid.subsingleton_iff`：∀ {M : Type u_1} [inst : AddZeroClass M],
 Subsingleton (AddSubmonoid M) ↔ Subsingleton M
-/
theorem subsingleton_iff : Subsingleton (Submodule R M) ↔ Subsingleton M :=
  have h : Subsingleton (Submodule R M) ↔ Subsingleton (AddSubmonoid M) := by
    rw [← subsingleton_iff_bot_eq_top, ← subsingleton_iff_bot_eq_top, ← toAddSubmonoid_inj,
      bot_toAddSubmonoid, top_toAddSubmonoid]
  h.trans AddSubmonoid.subsingleton_iff

@[simp]
/-
**Submodule.nontrivial_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：nontrivial_iff : Nontrivial (Submodule R M) ↔ Nontrivial M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `not_nontrivial_iff_subsingleton`：not_nontrivial_iff_subsingleton : ¬Nont
rivial α ↔ Subsingleton α
· 使用定理 `Submodule.subsingleton_iff`：subsingleton_iff : Subsingleton (Submodule R
 M) ↔ Subsingleton M
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
-/
theorem nontrivial_iff : Nontrivial (Submodule R M) ↔ Nontrivial M :=
  not_iff_not.mp
    ((not_nontrivial_iff_subsingleton.trans <| subsingleton_iff R).trans
      not_nontrivial_iff_subsingleton.symm)

variable {R}
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton M] : Unique (Submodule R M) :=
  ⟨⟨⊥⟩, fun a => @Subsingleton.elim _ ((subsingleton_iff R).mpr ‹_›) a _⟩
/-
**Submodule.unique'** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：unique' [Subsingleton R] : Unique (Submodule R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance unique' [Subsingleton R] : Unique (Submodule R M) := by
  haveI := Module.subsingleton R M; infer_instance
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial M] : Nontrivial (Submodule R M) :=
  (nontrivial_iff R).mpr ‹_›

/-!
## Disjointness of submodules
-/

/-
**Submodule.disjoint_def** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：disjoint_def {p p' : Submodule R M} : Disjoint p p' ↔ forall x in p, x in 
p' -> x = (0 : M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
## Disjointness of submodules
-/
theorem disjoint_def {p p' : Submodule R M} : Disjoint p p' ↔ ∀ x ∈ p, x ∈ p' → x = (0 : M) :=
  disjoint_iff_inf_le.trans <| show (∀ x, x ∈ p ∧ x ∈ p' → x ∈ ({0} : Set M)) ↔ _ by simp
/-
**Submodule.disjoint_def'** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：disjoint_def' {p p' : Submodule R M} : Disjoint p p' ↔ forall x in p, fora
ll y in p', x = y -> x = (0 : M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Submodule.disjoint_def`：disjoint_def {p p' : Submodule R M} : Disjoint p
 p' ↔ forall x in p, x in p' -> x = (0 : M)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem disjoint_def' {p p' : Submodule R M} :
    Disjoint p p' ↔ ∀ x ∈ p, ∀ y ∈ p', x = y → x = (0 : M) :=
  disjoint_def.trans
    ⟨fun h x hx _ hy hxy ↦ h x hx <| hxy.symm ▸ hy, fun h x hx hx' ↦ h _ hx x hx' rfl⟩
/-
**Submodule.eq_zero_of_coe_mem_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`
。
形式化陈述：eq_zero_of_coe_mem_of_disjoint (hpq : Disjoint p q) {a : p} (ha : (a : M) 
in q) : a = 0
参数：hpq : Disjoint p q；ha : (a : M) in q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.disjoint_def`：disjoint_def {p p' : Submodule R M} : Disjoint p
 p' ↔ forall x in p, x in p' -> x = (0 : M)
· 使用定理 `Submodule.coe_mem`：coe_mem (x : p) : (x : M) in p
-/
theorem eq_zero_of_coe_mem_of_disjoint (hpq : Disjoint p q) {a : p} (ha : (a : M) ∈ q) : a = 0 :=
  mod_cast disjoint_def.mp hpq a (coe_mem a) ha
/-
**Submodule.mem_right_iff_eq_zero_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Submodu
le`。
形式化陈述：mem_right_iff_eq_zero_of_disjoint {p p' : Submodule R M} (h : Disjoint p p
') {x : p} : (x : M) in p' ↔ x = 0
参数：h : Disjoint p p'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.coe_eq_zero`：coe_eq_zero {x : p} : (x : M) = 0 ↔ x = 0
· 使用定理 `Submodule.disjoint_def`：disjoint_def {p p' : Submodule R M} : Disjoint p
 p' ↔ forall x in p, x in p' -> x = (0 : M)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mem_right_iff_eq_zero_of_disjoint {p p' : Submodule R M} (h : Disjoint p p') {x : p} :
    (x : M) ∈ p' ↔ x = 0 :=
  ⟨fun hx => coe_eq_zero.1 <| disjoint_def.1 h x x.2 hx, fun h => h.symm ▸ p'.zero_mem⟩
/-
**Submodule.mem_left_iff_eq_zero_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Submodul
e`。
形式化陈述：mem_left_iff_eq_zero_of_disjoint {p p' : Submodule R M} (h : Disjoint p p'
) {x : p'} : (x : M) in p ↔ x = 0
参数：h : Disjoint p p'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.coe_eq_zero`：coe_eq_zero {x : p} : (x : M) = 0 ↔ x = 0
· 使用定理 `Submodule.disjoint_def`：disjoint_def {p p' : Submodule R M} : Disjoint p
 p' ↔ forall x in p, x in p' -> x = (0 : M)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mem_left_iff_eq_zero_of_disjoint {p p' : Submodule R M} (h : Disjoint p p') {x : p'} :
    (x : M) ∈ p ↔ x = 0 :=
  ⟨fun hx => coe_eq_zero.1 <| disjoint_def.1 h x hx x.2, fun h => h.symm ▸ p.zero_mem⟩

/-- Version of `AddSubgroup.disjoint_iff_add_eq_zero` for submodules. -/
/-
**Submodule.disjoint_iff_add_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：disjoint_iff_add_eq_zero {M R : Type*} [Ring R] [AddCommGroup M] [Module R
 M] {N₁ N₂ : Submodule R M} : Disjoint N₁ N₂ ↔ forall {x y : M}, x in N₁ -> y in
 N₂ -> x + y = 0 -> x = 0 ∧ y = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.neg_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M}, x
 ∈ p → …

--- 原说明 ---
Version of `AddSubgroup.disjoint_iff_add_eq_zero` for submodules.
-/
theorem disjoint_iff_add_eq_zero {M R : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {N₁ N₂ : Submodule R M} :
    Disjoint N₁ N₂ ↔ ∀ {x y : M}, x ∈ N₁ → y ∈ N₂ → x + y = 0 → x = 0 ∧ y = 0 := by
  simp only [← Submodule.mem_toAddSubgroup, ← AddSubgroup.disjoint_iff_add_eq_zero]
  aesop (add norm [disjoint_def', AddSubgroup.disjoint_def'])

end Submodule

section NatSubmodule

/-!
## ℕ-submodules
-/

/-- An additive submonoid is equivalent to a ℕ-submodule. -/
/-
**AddSubmonoid.toNatSubmodule** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddSubmonoid.toNatSubmodule : AddSubmonoid M ≃o Submodule Nat M where toFu
n S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive submonoid is equivalent to a ℕ-submodule.
-/
def AddSubmonoid.toNatSubmodule : AddSubmonoid M ≃o Submodule ℕ M where
  toFun S := { S with smul_mem' := fun r s hs ↦ show r • s ∈ S from nsmul_mem hs _ }
  invFun := Submodule.toAddSubmonoid
  map_rel_iff' := Iff.rfl

@[simp]
/-
**AddSubmonoid.toNatSubmodule_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddSubmonoid.toNatSubmodule_symm : ⇑(AddSubmonoid.toNatSubmodule.symm : _ 
≃o AddSubmonoid M) = Submodule.toAddSubmonoid
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AddSubmonoid.toNatSubmodule_symm :
    ⇑(AddSubmonoid.toNatSubmodule.symm : _ ≃o AddSubmonoid M) = Submodule.toAddSubmonoid :=
  rfl

@[simp]
/-
**AddSubmonoid.coe_toNatSubmodule** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddSubmonoid.coe_toNatSubmodule (S : AddSubmonoid M) : (S.toNatSubmodule :
 Set M) = S
参数：S : AddSubmonoid M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AddSubmonoid.coe_toNatSubmodule (S : AddSubmonoid M) :
    (S.toNatSubmodule : Set M) = S :=
  rfl

@[simp]
/-
**AddSubmonoid.toNatSubmodule_toAddSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddSubmonoid.toNatSubmodule_toAddSubmonoid (S : AddSubmonoid M) : S.toNatS
ubmodule.toAddSubmonoid = S
参数：S : AddSubmonoid M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.symm_apply_apply`：symm_apply_apply (e : α ≃o β) (x : α) : e.sym
m (e x) = x
-/
theorem AddSubmonoid.toNatSubmodule_toAddSubmonoid (S : AddSubmonoid M) :
    S.toNatSubmodule.toAddSubmonoid = S :=
  AddSubmonoid.toNatSubmodule.symm_apply_apply S

@[simp]
/-
**Submodule.toAddSubmonoid_toNatSubmodule** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.toAddSubmonoid_toNatSubmodule (S : Submodule Nat M) : S.toAddSub
monoid.toNatSubmodule = S
参数：S : Submodule Nat M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.apply_symm_apply`：apply_symm_apply (e : α ≃o β) (x : β) : e (e.
symm x) = x
-/
theorem Submodule.toAddSubmonoid_toNatSubmodule (S : Submodule ℕ M) :
    S.toAddSubmonoid.toNatSubmodule = S :=
  AddSubmonoid.toNatSubmodule.apply_symm_apply S

end NatSubmodule

end AddCommMonoid

section IntSubmodule

/-!
## ℤ-submodules
-/

variable [AddCommGroup M]

/-- An additive subgroup is equivalent to a ℤ-submodule. -/
/-
**AddSubgroup.toIntSubmodule** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddSubgroup.toIntSubmodule : AddSubgroup M ≃o Submodule Int M where toFun 
S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive subgroup is equivalent to a ℤ-submodule.
-/
def AddSubgroup.toIntSubmodule : AddSubgroup M ≃o Submodule ℤ M where
  toFun S := { S with smul_mem' := fun _ _ hs ↦ S.zsmul_mem hs _ }
  invFun := Submodule.toAddSubgroup
  map_rel_iff' := Iff.rfl

@[simp]
/-
**AddSubgroup.toIntSubmodule_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddSubgroup.toIntSubmodule_symm : ⇑(AddSubgroup.toIntSubmodule.symm : _ ≃o
 AddSubgroup M) = Submodule.toAddSubgroup
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AddSubgroup.toIntSubmodule_symm :
    ⇑(AddSubgroup.toIntSubmodule.symm : _ ≃o AddSubgroup M) = Submodule.toAddSubgroup :=
  rfl

@[simp]
/-
**AddSubgroup.coe_toIntSubmodule** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddSubgroup.coe_toIntSubmodule (S : AddSubgroup M) : (S.toIntSubmodule : S
et M) = S
参数：S : AddSubgroup M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AddSubgroup.coe_toIntSubmodule (S : AddSubgroup M) :
    (S.toIntSubmodule : Set M) = S :=
  rfl

@[simp]
/-
**AddSubgroup.toIntSubmodule_toAddSubgroup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddSubgroup.toIntSubmodule_toAddSubgroup (S : AddSubgroup M) : S.toIntSubm
odule.toAddSubgroup = S
参数：S : AddSubgroup M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.symm_apply_apply`：symm_apply_apply (e : α ≃o β) (x : α) : e.sym
m (e x) = x
-/
theorem AddSubgroup.toIntSubmodule_toAddSubgroup (S : AddSubgroup M) :
    S.toIntSubmodule.toAddSubgroup = S :=
  AddSubgroup.toIntSubmodule.symm_apply_apply S
/-
**Submodule.toAddSubgroup_toIntSubmodule** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.toAddSubgroup_toIntSubmodule (S : Submodule Int M) : S.toAddSubg
roup.toIntSubmodule = S
参数：S : Submodule Int M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.apply_symm_apply`：apply_symm_apply (e : α ≃o β) (x : β) : e (e.
symm x) = x
-/
theorem Submodule.toAddSubgroup_toIntSubmodule (S : Submodule ℤ M) :
    S.toAddSubgroup.toIntSubmodule = S :=
  AddSubgroup.toIntSubmodule.apply_symm_apply S

end IntSubmodule

