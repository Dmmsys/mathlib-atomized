/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Torsion.Free

/-!
# Submodules of a module

This file contains basic results on submodules that require further theory to be defined.
As such it is a good target for organizing and splitting further.

## Tags

submodule, subspace, linear map
-/

@[expose] public section

open Function

universe u'' u' u v w

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

namespace Submodule

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable {p q : Submodule R M}

@[gcongr, mono]
/-
**Submodule.toAddSubmonoid_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：toAddSubmonoid_strictMono : StrictMono (toAddSubmonoid : Submodule R M -> 
AddSubmonoid M)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAddSubmonoid_strictMono : StrictMono (toAddSubmonoid : Submodule R M → AddSubmonoid M) :=
  fun _ _ => id
/-
**Submodule.toAddSubmonoid_le** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：toAddSubmonoid_le : p.toAddSubmonoid <= q.toAddSubmonoid ↔ p <= q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toAddSubmonoid_le : p.toAddSubmonoid ≤ q.toAddSubmonoid ↔ p ≤ q :=
  Iff.rfl

@[gcongr, mono]
/-
**Submodule.toAddSubmonoid_mono** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：toAddSubmonoid_mono : Monotone (toAddSubmonoid : Submodule R M -> AddSubmo
noid M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Submodule.toAddSubmonoid_strictMono`：toAddSubmonoid_strictMono : StrictM
ono (toAddSubmonoid : Submodule R M -> AddSubmonoid M)
-/
theorem toAddSubmonoid_mono : Monotone (toAddSubmonoid : Submodule R M → AddSubmonoid M) :=
  toAddSubmonoid_strictMono.monotone

@[gcongr, mono]
/-
**Submodule.toSubMulAction_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：toSubMulAction_strictMono : StrictMono (toSubMulAction : Submodule R M -> 
SubMulAction R M)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSubMulAction_strictMono :
    StrictMono (toSubMulAction : Submodule R M → SubMulAction R M) := fun _ _ => id

@[gcongr, mono]
/-
**Submodule.toSubMulAction_mono** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：toSubMulAction_mono : Monotone (toSubMulAction : Submodule R M -> SubMulAc
tion R M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Submodule.toSubMulAction_strictMono`：toSubMulAction_strictMono : StrictM
ono (toSubMulAction : Submodule R M -> SubMulAction R M)
-/
theorem toSubMulAction_mono : Monotone (toSubMulAction : Submodule R M → SubMulAction R M) :=
  toSubMulAction_strictMono.monotone

end Submodule

namespace Submodule

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M]

-- We can infer the module structure implicitly from the bundled submodule,
-- rather than via typeclass resolution.
variable {module_M : Module R M}
variable {p q : Submodule R M}
variable {r : R} {x y : M}
variable (p)

/-
**Submodule.sum_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u} {M : Type v} {ι : Type w} [inst : Semiring R] [inst_1 : Add
CommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {t : Finset ι
} {f : ι → M}, (∀ c ∈ t, f c ∈ p) → ∑ i ∈ t, f i ∈ p
参数：p : Submodule R M；∀ c ∈ t, f c ∈ p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
-/
protected theorem sum_mem {t : Finset ι} {f : ι → M} : (∀ c ∈ t, f c ∈ p) → (∑ i ∈ t, f i) ∈ p :=
  sum_mem
/-
**Submodule.sum_smul_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：sum_smul_mem {t : Finset ι} {f : ι -> M} (r : ι -> R) (hyp : forall c in t
, f c in p) : (∑ i in t, r i • f i) in p
参数：r : ι -> R；hyp : forall c in t, f c in p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
-/
theorem sum_smul_mem {t : Finset ι} {f : ι → M} (r : ι → R) (hyp : ∀ c ∈ t, f c ∈ p) :
    (∑ i ∈ t, r i • f i) ∈ p :=
  sum_mem fun i hi => smul_mem _ _ (hyp i hi)
/-
**Submodule.isCentralScalar** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：isCentralScalar [SMul S R] [SMul S M] [IsScalarTower S R M] [SMul Sᵐᵒᵖ R] 
[SMul Sᵐᵒᵖ M] [IsScalarTower Sᵐᵒᵖ R M] [IsCentralScalar S M] : IsCentralScalar S
 p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isCentralScalar [SMul S R] [SMul S M] [IsScalarTower S R M] [SMul Sᵐᵒᵖ R] [SMul Sᵐᵒᵖ M]
    [IsScalarTower Sᵐᵒᵖ R M] [IsCentralScalar S M] : IsCentralScalar S p :=
  p.toSubMulAction.isCentralScalar
/-
**Submodule.instIsTorsionFree** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：instIsTorsionFree [Module.IsTorsionFree R M] : Module.IsTorsionFree R p
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.Injective.moduleIsTorsionFree`：Function.Injective.moduleIsTorsi
onFree [IsTorsionFree R N] (f : M -> N) (hf : f.Injective) (smul : forall (r : R
) (m : M), f (r • m) = r • f…
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
instance instIsTorsionFree [Module.IsTorsionFree R M] : Module.IsTorsionFree R p :=
  Subtype.coe_injective.moduleIsTorsionFree _ (by simp)

section AddAction

/-! ### Additive actions by `Submodule`s
These instances transfer the action by an element `m : M` of an `R`-module `M` written as `m +ᵥ a`
onto the action by an element `s : S` of a submodule `S : Submodule R M` such that
`s +ᵥ a = (s : M) +ᵥ a`.
These instances work particularly well in conjunction with `AddGroup.toAddAction`, enabling
`s +ᵥ m` as an alias for `↑s + m`.
-/


variable {α β : Type*}

/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [VAdd M α] : VAdd p α :=
  AddSubmonoid.instVAddSubtypeMem p
/-
**Submodule.vaddCommClass** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：vaddCommClass [VAdd M β] [VAdd α β] [VAddCommClass M α β] : VAddCommClass 
p α β
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `VAddCommClass.vadd_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : VAdd M α} {inst_1 : VAdd N α} [self : VAddCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance vaddCommClass [VAdd M β] [VAdd α β] [VAddCommClass M α β] : VAddCommClass p α β :=
  ⟨fun a => vadd_comm (a : M)⟩
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [VAdd M α] [FaithfulVAdd M α] : FaithfulVAdd p α :=
  ⟨fun h => Subtype.ext <| eq_of_vadd_eq_vadd h⟩

variable {p}
/-
**Submodule.vadd_def** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：vadd_def [VAdd M α] (g : p) (m : α) : g +ᵥ m = (g : M) +ᵥ m
参数：g : p；m : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem vadd_def [VAdd M α] (g : p) (m : α) : g +ᵥ m = (g : M) +ᵥ m :=
  rfl

end AddAction

end AddCommMonoid

section AddCommGroup

variable [Ring R] [AddCommGroup M]
variable {module_M : Module R M}
variable (p p' : Submodule R M)
variable {r : R} {x y : M}


@[gcongr, mono]
/-
**Submodule.toAddSubgroup_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：toAddSubgroup_strictMono : StrictMono (toAddSubgroup : Submodule R M -> Ad
dSubgroup M)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAddSubgroup_strictMono : StrictMono (toAddSubgroup : Submodule R M → AddSubgroup M) :=
  fun _ _ => id

@[gcongr]
/-
**Submodule.toAddSubgroup_le** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：toAddSubgroup_le : p.toAddSubgroup <= p'.toAddSubgroup ↔ p <= p'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toAddSubgroup_le : p.toAddSubgroup ≤ p'.toAddSubgroup ↔ p ≤ p' :=
  Iff.rfl

@[mono]
/-
**Submodule.toAddSubgroup_mono** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：toAddSubgroup_mono : Monotone (toAddSubgroup : Submodule R M -> AddSubgrou
p M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Submodule.toAddSubgroup_strictMono`：toAddSubgroup_strictMono : StrictMon
o (toAddSubgroup : Submodule R M -> AddSubgroup M)
-/
theorem toAddSubgroup_mono : Monotone (toAddSubgroup : Submodule R M → AddSubgroup M) :=
  toAddSubgroup_strictMono.monotone

@[simp]
/-
**Submodule.toAddSubgroup_toAddSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：toAddSubgroup_toAddSubmonoid (p : Submodule R M) : p.toAddSubgroup.toAddSu
bmonoid = p.toAddSubmonoid
参数：p : Submodule R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAddSubgroup_toAddSubmonoid (p : Submodule R M) :
    p.toAddSubgroup.toAddSubmonoid = p.toAddSubmonoid :=
  rfl

-- See `neg_coe_set`
/-
**Submodule.neg_coe** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：neg_coe : -(p : Set M) = p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Submodule.neg_mem_iff`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst
_1 : AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M
}, -x ∈ p ↔…
-/
theorem neg_coe : -(p : Set M) = p :=
  Set.ext fun _ => p.neg_mem_iff

end AddCommGroup

section IsDomain

variable [Ring R] [IsDomain R]
variable [AddCommGroup M] [Module R M] {b : ι → M}

/-
**Submodule.notMem_of_ortho** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：notMem_of_ortho {x : M} {N : Submodule R M} (ortho : forall (c : R), foral
l y in N, c • x + y = (0 : M) -> c = 0) : x ∉ N
参数：ortho : forall (c : R), forall y in N, c • x + y = (0 : M) -> c = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
theorem notMem_of_ortho {x : M} {N : Submodule R M}
    (ortho : ∀ (c : R), ∀ y ∈ N, c • x + y = (0 : M) → c = 0) : x ∉ N := by
  intro hx
  simpa using ortho (-1) x hx
/-
**Submodule.ne_zero_of_ortho** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：ne_zero_of_ortho {x : M} {N : Submodule R M} (ortho : forall (c : R), fora
ll y in N, c • x + y = (0 : M) -> c = 0) : x != 0
参数：ortho : forall (c : R), forall y in N, c • x + y = (0 : M) -> c = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.notMem_of_ortho`：notMem_of_ortho {x : M} {N : Submodule R M} (
ortho : forall (c : R), forall y in N, c • x + y = (0 : M) -> c = 0) : x ∉ N
-/
theorem ne_zero_of_ortho {x : M} {N : Submodule R M}
    (ortho : ∀ (c : R), ∀ y ∈ N, c • x + y = (0 : M) → c = 0) : x ≠ 0 :=
  mt (fun h => show x ∈ N from h.symm ▸ N.zero_mem) (notMem_of_ortho ortho)

end IsDomain

end Submodule

namespace Submodule

variable [DivisionSemiring S] [Semiring R] [AddCommMonoid M] [Module R M]
variable [SMul S R] [Module S M] [IsScalarTower S R M]
variable (p : Submodule R M) {s : S} {x y : M}

/-
**Submodule.smul_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：smul_mem_iff (s0 : s != 0) : s • x in p ↔ x in p
参数：s0 : s != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubMulAction.smul_mem_iff`：smul_mem_iff (s0 : s != 0) : s • x in p ↔ x i
n p
-/
theorem smul_mem_iff (s0 : s ≠ 0) : s • x ∈ p ↔ x ∈ p :=
  p.toSubMulAction.smul_mem_iff s0

end Submodule

/-- Subspace of a vector space. Defined to equal `Submodule`. -/
/-
**Subspace** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Subspace (R : Type u) (M : Type v) [DivisionRing R] [AddCommGroup M] [Modu
le R M]
参数：R : Type u；M : Type v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Subspace of a vector space. Defined to equal `Submodule`.
-/
abbrev Subspace (R : Type u) (M : Type v) [DivisionRing R] [AddCommGroup M] [Module R M] :=
  Submodule R M
