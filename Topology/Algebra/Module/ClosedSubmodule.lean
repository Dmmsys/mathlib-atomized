/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Sets.Closeds

/-!
# Closed submodules of a topological module

This file builds the frame of closed `R`-submodules of a topological module `M`.

One can turn `s : Submodule R E` + `hs : IsClosed s` into `s : ClosedSubmodule R E` in a tactic
block by doing `lift s to ClosedSubmodule R E using hs`.

## TODO

Actually provide the `Order.Frame (ClosedSubmodule R M)` instance.
-/

@[expose] public section

open Function Order TopologicalSpace

variable {ι : Sort*} {R M N O : Type*} [Semiring R]
  [AddCommMonoid M] [TopologicalSpace M] [Module R M]
  [AddCommMonoid N] [TopologicalSpace N] [Module R N]
  [AddCommMonoid O] [TopologicalSpace O] [Module R O]

variable (R M) in
/-- The type of closed submodules of a topological module. -/
@[ext]
/-
**ClosedSubmodule** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_2) →   (M : Type u_3) →     [inst : Semiring R] → [inst_1 : Ad
dCommMonoid M] → [TopologicalSpace M] → [_root_.Module R M] → Type u_3
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of closed submodules of a topological module.
-/
structure ClosedSubmodule extends Submodule R M, Closeds M where

namespace ClosedSubmodule
variable {s t : ClosedSubmodule R M} {x : M}

attribute [coe] toSubmodule toCloseds

/-- Reinterpret a closed submodule as a submodule. -/
add_decl_doc toSubmodule

/-- Reinterpret a closed submodule as a closed set. -/
add_decl_doc toCloseds

/-
**ClosedSubmodule.toSubmodule_injective** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodu
le`。
形式化陈述：toSubmodule_injective : Injective (toSubmodule : ClosedSubmodule R M -> Su
bmodule R M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `ClosedSubmodule.isClosed'`：∀ {R : Type u_2} {M : Type u_3} [inst : Semir
ing R] [inst_1 : AddCommMonoid M] [inst_2 : TopologicalSpace M]   [inst_3 : _roo
t_.Module R M] …
-/
lemma toSubmodule_injective : Injective (toSubmodule : ClosedSubmodule R M → Submodule R M) :=
  fun s t h ↦ by cases s; congr!
/-
**ClosedSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `ClosedSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (ClosedSubmodule R M) M where
  coe s := s.1
  coe_injective _ _ h := toSubmodule_injective <| SetLike.coe_injective h
/-
**ClosedSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `ClosedSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (ClosedSubmodule R M) := .ofSetLike (ClosedSubmodule R M) M
/-
**ClosedSubmodule.toCloseds_injective** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule
`。
形式化陈述：toCloseds_injective : Injective (toCloseds : ClosedSubmodule R M -> Closed
s M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma toCloseds_injective : Injective (toCloseds : ClosedSubmodule R M → Closeds M) :=
  fun _s _t h ↦ SetLike.coe_injective congr(($h : Set M))
/-
**ClosedSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `ClosedSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddSubmonoidClass (ClosedSubmodule R M) M where
  zero_mem s := s.zero_mem
  add_mem {s} := s.add_mem
/-
**ClosedSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `ClosedSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMulMemClass (ClosedSubmodule R M) R M where
  smul_mem {s} r := s.smul_mem r
/-
**ClosedSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `ClosedSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe (ClosedSubmodule R M) (Submodule R M) where
  coe := toSubmodule
/-
**ClosedSubmodule.carrier_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `ClosedSubmodule`。
形式化陈述：∀ {R : Type u_2} {M : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : TopologicalSpace M]   [inst_3 : _root_.Module R M] (s : ClosedSub
module R M), (↑s).carrier = ↑s
参数：s : ClosedSubmodule R M；↑s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma carrier_eq_coe (s : ClosedSubmodule R M) : s.carrier = s := rfl
/-
**ClosedSubmodule.mem_mk** 是 Mathlib 中的一个定理，位于命名空间 `ClosedSubmodule`。
形式化陈述：∀ {R : Type u_2} {M : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : TopologicalSpace M]   [inst_3 : _root_.Module R M] {x : M} {s : S
ubmodule R M} {hs : IsClosed s.carrier},   x ∈ { toSubmodule := s, isClosed' := 
hs } ↔ x ∈ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_mk {s : Submodule R M} {hs} : x ∈ mk s hs ↔ x ∈ s := .rfl

@[simp, norm_cast]
/-
**ClosedSubmodule.coe_toSubmodule** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule`。
形式化陈述：coe_toSubmodule (s : ClosedSubmodule R M) : (s.toSubmodule : Set M) = s
参数：s : ClosedSubmodule R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_toSubmodule (s : ClosedSubmodule R M) : (s.toSubmodule : Set M) = s := rfl

@[simp]
/-
**ClosedSubmodule.mem_toSubmodule_iff** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule
`。
形式化陈述：mem_toSubmodule_iff (x : M) (s : ClosedSubmodule R M) : x in s.toSubmodule
 ↔ x in s
参数：x : M；s : ClosedSubmodule R M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_toSubmodule_iff (x : M) (s : ClosedSubmodule R M) : x ∈ s.toSubmodule ↔ x ∈ s := by
  rfl

@[simp]
/-
**ClosedSubmodule.coe_toCloseds** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule`。
形式化陈述：coe_toCloseds (s : ClosedSubmodule R M) : (s.toCloseds : Set M) = s
参数：s : ClosedSubmodule R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_toCloseds (s : ClosedSubmodule R M) : (s.toCloseds : Set M) = s := rfl
/-
**ClosedSubmodule.isClosed** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule`。
形式化陈述：isClosed (s : ClosedSubmodule R M) : IsClosed (s : Set M)
参数：s : ClosedSubmodule R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosedSubmodule.isClosed'`：∀ {R : Type u_2} {M : Type u_3} [inst : Semir
ing R] [inst_1 : AddCommMonoid M] [inst_2 : TopologicalSpace M]   [inst_3 : _roo
t_.Module R M] …
-/
lemma isClosed (s : ClosedSubmodule R M) : IsClosed (s : Set M) := s.isClosed'

initialize_simps_projections ClosedSubmodule (carrier → coe, as_prefix coe)
/-
**ClosedSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `ClosedSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CanLift (Submodule R M) (ClosedSubmodule R M) toSubmodule (IsClosed (X := M) ·) where
  prf s hs := ⟨⟨s, hs⟩, rfl⟩
/-
**ClosedSubmodule.toSubmodule_le_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `ClosedSu
bmodule`。
形式化陈述：∀ {R : Type u_2} {M : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : TopologicalSpace M]   [inst_3 : _root_.Module R M] {s t : ClosedS
ubmodule R M}, ↑s ≤ ↑t ↔ s ≤ t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, norm_cast] lemma toSubmodule_le_toSubmodule {s t : ClosedSubmodule R M} :
    s.toSubmodule ≤ t.toSubmodule ↔ s ≤ t := .rfl

/-- The preimage of a closed submodule under a continuous linear map as a closed submodule. -/
@[simps!]
/-
**ClosedSubmodule.comap** 是 Mathlib 中的一个定义，位于命名空间 `ClosedSubmodule`。
形式化陈述：comap (f : M ->L[R] N) (s : ClosedSubmodule R N) : ClosedSubmodule R M whe
re toSubmodule
参数：f : M ->L[R] N；s : ClosedSubmodule R N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The preimage of a closed submodule under a continuous linear map as a closed sub
module.
-/
def comap (f : M →L[R] N) (s : ClosedSubmodule R N) : ClosedSubmodule R M where
  toSubmodule := .comap (f : M →ₗ[R] N) s
  isClosed' := by simpa using s.isClosed.preimage f.continuous

@[simp]
/-
**ClosedSubmodule.mem_comap** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule`。
形式化陈述：mem_comap {f : M ->L[R] N} {s : ClosedSubmodule R N} {x : M} : x in s.coma
p f ↔ f x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_comap {f : M →L[R] N} {s : ClosedSubmodule R N} {x : M} : x ∈ s.comap f ↔ f x ∈ s := .rfl
/-
**ClosedSubmodule.toSubmodule_comap** 是 Mathlib 中的一个定理，位于命名空间 `ClosedSubmodule`。
形式化陈述：∀ {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Semiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : TopologicalSpace M] [inst_3 : _root_.Module R M]
 [inst_4 : AddCommMonoid N] [inst_5 : TopologicalSpace N]   [inst_6 : _root_.Mod
ule R N] (f : M →L[R] N) (s : ClosedSubmodule R N),   ↑(ClosedSubmodule.comap f 
s) = Submodule.comap ↑f ↑s
参数：f : M →L[R] N；s : ClosedSubmodule R N；ClosedSubmodule.comap f s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toSubmodule_comap (f : M →L[R] N) (s : ClosedSubmodule R N) :
    (s.comap f).toSubmodule = s.toSubmodule.comap (f : M →ₗ[R] N) := rfl
/-
**ClosedSubmodule.comap_id** 是 Mathlib 中的一个定理，位于命名空间 `ClosedSubmodule`。
形式化陈述：∀ {R : Type u_2} {M : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : TopologicalSpace M]   [inst_3 : _root_.Module R M] (s : ClosedSub
module R M), ClosedSubmodule.comap (ContinuousLinearMap.id R M) s = s
参数：s : ClosedSubmodule R M；ContinuousLinearMap.id R M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma comap_id (s : ClosedSubmodule R M) : s.comap (.id _ _) = s := rfl
/-
**ClosedSubmodule.comap_comap** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule`。
形式化陈述：comap_comap (g : N ->L[R] O) (f : M ->L[R] N) (s : ClosedSubmodule R O) : 
(s.comap g).comap f = s.comap (g.comp f)
参数：g : N ->L[R] O；f : M ->L[R] N；s : ClosedSubmodule R O。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comap_comap (g : N →L[R] O) (f : M →L[R] N) (s : ClosedSubmodule R O) :
    (s.comap g).comap f = s.comap (g.comp f) := rfl
/-
**ClosedSubmodule.instInf** 是 Mathlib 中的一个实例，位于命名空间 `ClosedSubmodule`。
形式化陈述：instInf : Min (ClosedSubmodule R M) where min s t
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInf : Min (ClosedSubmodule R M) where
  min s t := ⟨s ⊓ t, s.isClosed.inter t.isClosed⟩
/-
**ClosedSubmodule.instInfSet** 是 Mathlib 中的一个实例，位于命名空间 `ClosedSubmodule`。
形式化陈述：instInfSet : InfSet (ClosedSubmodule R M) where sInf S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInfSet : InfSet (ClosedSubmodule R M) where
  sInf S := ⟨⨅ s ∈ S, s, by simpa using isClosed_biInter fun x hx ↦ x.isClosed⟩

@[simp, norm_cast]
/-
**ClosedSubmodule.toSubmodule_sInf** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule`。
形式化陈述：toSubmodule_sInf (S : Set (ClosedSubmodule R M)) : toSubmodule (sInf S) = 
⨅ s in S, s.toSubmodule
参数：S : Set (ClosedSubmodule R M)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toSubmodule_sInf (S : Set (ClosedSubmodule R M)) :
    toSubmodule (sInf S) = ⨅ s ∈ S, s.toSubmodule := rfl

@[simp, norm_cast]
/-
**ClosedSubmodule.toSubmodule_iInf** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule`。
形式化陈述：toSubmodule_iInf (f : ι -> ClosedSubmodule R M) : toSubmodule (⨅ i, f i) =
 ⨅ i, (f i).toSubmodule
参数：f : ι -> ClosedSubmodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : InfSet α] (s : ι → α), iI
nf s = sInf (Set.range s)
· 使用引理 `ClosedSubmodule.toSubmodule_sInf`：toSubmodule_sInf (S : Set (ClosedSubmo
dule R M)) : toSubmodule (sInf S) = ⨅ s in S, s.toSubmodule
· 使用定理 `iInf_range`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst : Compl
eteLattice α] {g : β → α} {f : ι → β},   ⨅ b ∈ Set.range f, g b = ⨅ i, g (f i)
-/
lemma toSubmodule_iInf (f : ι → ClosedSubmodule R M) :
    toSubmodule (⨅ i, f i) = ⨅ i, (f i).toSubmodule := by rw [iInf, toSubmodule_sInf, iInf_range]

@[simp, norm_cast]
/-
**ClosedSubmodule.coe_sInf** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule`。
形式化陈述：coe_sInf (S : Set (ClosedSubmodule R M)) : ↑(sInf S) = ⨅ s in S, (s : Set 
M)
参数：S : Set (ClosedSubmodule R M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.coe_iInf`：coe_iInf {ι} (p : ι -> Submodule R M) : (↑(⨅ i, p i)
 : Set M) = ⋂ i, ↑(p i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coe_sInf (S : Set (ClosedSubmodule R M)) : ↑(sInf S) = ⨅ s ∈ S, (s : Set M) := by
  simp [← coe_toSubmodule]

@[simp, norm_cast]
/-
**ClosedSubmodule.coe_iInf** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule`。
形式化陈述：coe_iInf (f : ι -> ClosedSubmodule R M) : ↑(⨅ i, f i) = ⨅ i, (f i : Set M)
参数：f : ι -> ClosedSubmodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ClosedSubmodule.toSubmodule_iInf`：toSubmodule_iInf (f : ι -> ClosedSubmo
dule R M) : toSubmodule (⨅ i, f i) = ⨅ i, (f i).toSubmodule
· 使用定理 `Submodule.coe_iInf`：coe_iInf {ι} (p : ι -> Submodule R M) : (↑(⨅ i, p i)
 : Set M) = ⋂ i, ↑(p i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coe_iInf (f : ι → ClosedSubmodule R M) : ↑(⨅ i, f i) = ⨅ i, (f i : Set M) := by
  simp [← coe_toSubmodule]
/-
**ClosedSubmodule.mem_sInf** 是 Mathlib 中的一个定理，位于命名空间 `ClosedSubmodule`。
形式化陈述：∀ {R : Type u_2} {M : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : TopologicalSpace M]   [inst_3 : _root_.Module R M] {x : M} {S : S
et (ClosedSubmodule R M)}, x ∈ sInf S ↔ ∀ s ∈ S, x ∈ s
参数：ClosedSubmodule R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ClosedSubmodule.coe_sInf`：coe_sInf (S : Set (ClosedSubmodule R M)) : ↑(s
Inf S) = ⨅ s in S, (s : Set M)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma mem_sInf {S : Set (ClosedSubmodule R M)} : x ∈ sInf S ↔ ∀ s ∈ S, x ∈ s := by
  simp [← SetLike.mem_coe]
/-
**ClosedSubmodule.mem_iInf** 是 Mathlib 中的一个定理，位于命名空间 `ClosedSubmodule`。
形式化陈述：∀ {ι : Sort u_1} {R : Type u_2} {M : Type u_3} [inst : Semiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : TopologicalSpace M] [inst_3 : _root_.Module R M]
 {x : M} {f : ι → ClosedSubmodule R M},   x ∈ ⨅ i, f i ↔ ∀ (i : ι), x ∈ f i
参数：i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ClosedSubmodule.coe_iInf`：coe_iInf (f : ι -> ClosedSubmodule R M) : ↑(⨅ 
i, f i) = ⨅ i, (f i : Set M)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma mem_iInf {f : ι → ClosedSubmodule R M} : x ∈ ⨅ i, f i ↔ ∀ i, x ∈ f i := by
  simp [← SetLike.mem_coe]
/-
**ClosedSubmodule.instSemilatticeInf** 是 Mathlib 中的一个实例，位于命名空间 `ClosedSubmodule`
。
形式化陈述：instSemilatticeInf : SemilatticeInf (ClosedSubmodule R M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `ClosedSubmodule.toSubmodule_injective`：toSubmodule_injective : Injective
 (toSubmodule : ClosedSubmodule R M -> Submodule R M)
-/
instance instSemilatticeInf : SemilatticeInf (ClosedSubmodule R M) :=
  toSubmodule_injective.semilatticeInf _ .rfl .rfl fun _ _ ↦ rfl

@[simp, norm_cast]
/-
**ClosedSubmodule.toSubmodule_inf** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule`。
形式化陈述：toSubmodule_inf (s t : ClosedSubmodule R M) : toSubmodule (s ⊓ t) = s.toSu
bmodule ⊓ t.toSubmodule
参数：s t : ClosedSubmodule R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toSubmodule_inf (s t : ClosedSubmodule R M) :
    toSubmodule (s ⊓ t) = s.toSubmodule ⊓ t.toSubmodule := rfl
/-
**ClosedSubmodule.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `ClosedSubmodule`。
形式化陈述：∀ {R : Type u_2} {M : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : TopologicalSpace M]   [inst_3 : _root_.Module R M] (s t : ClosedS
ubmodule R M), ↑(s ⊓ t) = ↑s ⊓ ↑t
参数：s t : ClosedSubmodule R M；s ⊓ t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_inf (s t : ClosedSubmodule R M) : ↑(s ⊓ t) = (s ⊓ t : Set M) := rfl
/-
**ClosedSubmodule.mem_inf** 是 Mathlib 中的一个定理，位于命名空间 `ClosedSubmodule`。
形式化陈述：∀ {R : Type u_2} {M : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : TopologicalSpace M]   [inst_3 : _root_.Module R M] {s t : ClosedS
ubmodule R M} {x : M}, x ∈ s ⊓ t ↔ x ∈ s ∧ x ∈ t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_inf : x ∈ s ⊓ t ↔ x ∈ s ∧ x ∈ t := .rfl
/-
**ClosedSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `ClosedSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteSemilatticeInf (ClosedSubmodule R M) where
  isGLB_sInf _ := .of_image toSubmodule_le_toSubmodule isGLB_biInf
/-
**ClosedSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `ClosedSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderTop (ClosedSubmodule R M) where
  top := ⟨⊤, isClosed_univ⟩
  le_top s := le_top (a := s.toSubmodule)
/-
**ClosedSubmodule.toSubmodule_top** 是 Mathlib 中的一个定理，位于命名空间 `ClosedSubmodule`。
形式化陈述：∀ {R : Type u_2} {M : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : TopologicalSpace M]   [inst_3 : _root_.Module R M], ↑⊤ = ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma toSubmodule_top : toSubmodule (⊤ : ClosedSubmodule R M) = ⊤ := rfl
/-
**ClosedSubmodule.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `ClosedSubmodule`。
形式化陈述：∀ {R : Type u_2} {M : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : TopologicalSpace M]   [inst_3 : _root_.Module R M], ↑⊤ = Set.univ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_top : ((⊤ : ClosedSubmodule R M) : Set M) = .univ := rfl
/-
**ClosedSubmodule.mem_top** 是 Mathlib 中的一个定理，位于命名空间 `ClosedSubmodule`。
形式化陈述：∀ {R : Type u_2} {M : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : TopologicalSpace M]   [inst_3 : _root_.Module R M] {x : M}, x ∈ ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
@[simp] lemma mem_top : x ∈ (⊤ : ClosedSubmodule R M) := trivial

section T1Space
variable [T1Space M]

/-
**ClosedSubmodule.instOrderBot** 是 Mathlib 中的一个实例，位于命名空间 `ClosedSubmodule`。
形式化陈述：instOrderBot : OrderBot (ClosedSubmodule R M) where bot
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instOrderBot : OrderBot (ClosedSubmodule R M) where
  bot := ⟨⊥, isClosed_singleton⟩
  bot_le s := bot_le (a := s.toSubmodule)
/-
**ClosedSubmodule.toSubmodule_bot** 是 Mathlib 中的一个定理，位于命名空间 `ClosedSubmodule`。
形式化陈述：∀ {R : Type u_2} {M : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : TopologicalSpace M]   [inst_3 : _root_.Module R M] [inst_4 : T1Sp
ace M], ↑⊥ = ⊥
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma toSubmodule_bot : toSubmodule (⊥ : ClosedSubmodule R M) = ⊥ := rfl
/-
**ClosedSubmodule.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `ClosedSubmodule`。
形式化陈述：∀ {R : Type u_2} {M : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : TopologicalSpace M]   [inst_3 : _root_.Module R M] [inst_4 : T1Sp
ace M], ↑⊥ = {0}
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_bot : ((⊥ : ClosedSubmodule R M) : Set M) = {0} := rfl
/-
**ClosedSubmodule.mem_bot** 是 Mathlib 中的一个定理，位于命名空间 `ClosedSubmodule`。
形式化陈述：∀ {R : Type u_2} {M : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : TopologicalSpace M]   [inst_3 : _root_.Module R M] {x : M} [inst_
4 : T1Space M], x ∈ ⊥ ↔ x = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_bot : x ∈ (⊥ : ClosedSubmodule R M) ↔ x = 0 := .rfl

end T1Space
end ClosedSubmodule

namespace Submodule
variable [ContinuousAdd M] [ContinuousConstSMul R M]

/-- The closure of a submodule as a closed submodule. -/
@[simps!]
/-
**Submodule.closure** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：{R : Type u_2} →   {M : Type u_3} →     [inst : Semiring R] →       [inst_
1 : AddCommMonoid M] →         [inst_2 : TopologicalSpace M] →           [inst_3
 : _root_.Module R M] →             [ContinuousAdd M] → [ContinuousConstSMul R M
] → Submodule R M → ClosedSubmodule R M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The closure of a submodule as a closed submodule.
-/
protected def closure (s : Submodule R M) : ClosedSubmodule R M where
  toSubmodule := s.topologicalClosure
  isClosed' := isClosed_closure
/-
**Submodule.closure_le** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_2} {M : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : TopologicalSpace M]   [inst_3 : _root_.Module R M] [inst_4 : Cont
inuousAdd M] [inst_5 : ContinuousConstSMul R M] {s : Submodule R M}   {t : Close
dSubmodule R M}, s.closure ≤ t ↔ s ≤ ↑t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用引理 `ClosedSubmodule.isClosed`：isClosed (s : ClosedSubmodule R M) : IsClosed 
(s : Set M)
-/
@[simp] lemma closure_le {s : Submodule R M} {t : ClosedSubmodule R M} : s.closure ≤ t ↔ s ≤ t :=
  t.isClosed.closure_subset_iff

@[simp]
/-
**Submodule.mem_closure_iff** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：mem_closure_iff {x : M} {s : Submodule R M} : x in s.closure ↔ x in s.topo
logicalClosure
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_closure_iff {x : M} {s : Submodule R M} : x ∈ s.closure ↔ x ∈ s.topologicalClosure :=
  Iff.rfl

@[simp]
/-
**Submodule.closure_eq** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：closure_eq {s : ClosedSubmodule R M} : s.closure = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosedSubmodule.ext`：∀ {R : Type u_2} {M : Type u_3} {inst : Semiring R}
 {inst_1 : AddCommMonoid M} {inst_2 : TopologicalSpace M}   {inst_3 : _root_.Mod
ule R M} …
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.coe_closure`：∀ {R : Type u_2} {M : Type u_3} [inst : Semiring 
R] [inst_1 : AddCommMonoid M] [inst_2 : TopologicalSpace M]   [inst_3 : _root_.M
odule R M] …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `closure_eq_iff_isClosed`：closure_eq_iff_isClosed : closure s = s ↔ IsClo
sed s
· 使用定理 `ClosedSubmodule.isClosed'`：∀ {R : Type u_2} {M : Type u_3} [inst : Semir
ing R] [inst_1 : AddCommMonoid M] [inst_2 : TopologicalSpace M]   [inst_3 : _roo
t_.Module R M] …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma closure_eq {s : ClosedSubmodule R M} : s.closure = s := by
  ext
  simp only [carrier_eq_coe, ClosedSubmodule.coe_toSubmodule, coe_closure, SetLike.mem_coe]
  rw [closure_eq_iff_isClosed.mpr]
  · rfl
  · exact s.isClosed'
/-
**Submodule.closure_eq'** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：closure_eq' {s : Submodule R M} (hs : IsClosed s.carrier) : s.closure = ⟨s
, hs⟩
参数：hs : IsClosed s.carrier。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosedSubmodule.ext`：∀ {R : Type u_2} {M : Type u_3} {inst : Semiring R}
 {inst_1 : AddCommMonoid M} {inst_2 : TopologicalSpace M}   {inst_3 : _root_.Mod
ule R M} …
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.coe_closure`：∀ {R : Type u_2} {M : Type u_3} [inst : Semiring 
R] [inst_1 : AddCommMonoid M] [inst_2 : TopologicalSpace M]   [inst_3 : _root_.M
odule R M] …
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma closure_eq' {s : Submodule R M} (hs : IsClosed s.carrier) : s.closure = ⟨s, hs⟩ := by
  ext; simp

end Submodule

namespace ClosedSubmodule

variable [ContinuousAdd N] [ContinuousConstSMul R N] {f : M →L[R] N}

/-
**ClosedSubmodule.closure_toSubmodule_eq** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmod
ule`。
形式化陈述：closure_toSubmodule_eq {s : ClosedSubmodule R N} : s.toSubmodule.closure =
 s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosedSubmodule.ext`：∀ {R : Type u_2} {M : Type u_3} {inst : Semiring R}
 {inst_1 : AddCommMonoid M} {inst_2 : TopologicalSpace M}   {inst_3 : _root_.Mod
ule R M} …
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Submodule.closure_eq`：closure_eq {s : ClosedSubmodule R M} : s.closure =
 s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma closure_toSubmodule_eq {s : ClosedSubmodule R N} : s.toSubmodule.closure = s := by
  ext x; simp

/-- The closure of the image of a closed submodule under a continuous linear map is a closed
submodule.

`ClosedSubmodule.map f` is left-adjoint to `ClosedSubmodule.comap f`.
See `ClosedSubmodule.gc_map_comap`. -/
/-
**ClosedSubmodule.map** 是 Mathlib 中的一个定义，位于命名空间 `ClosedSubmodule`。
形式化陈述：map (f : M ->L[R] N) (s : ClosedSubmodule R M) : ClosedSubmodule R N
参数：f : M ->L[R] N；s : ClosedSubmodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The closure of the image of a closed submodule under a continuous linear map is 
a closed
submodule.

`ClosedSubmodule.map f` is left-adjoint to `ClosedSubmodule.comap f`.
See `ClosedSubmodule.gc_map_comap`.
-/
def map (f : M →L[R] N) (s : ClosedSubmodule R M) : ClosedSubmodule R N :=
  (s.toSubmodule.map (f : M →ₗ[R] N)).closure

@[simp]
/-
**ClosedSubmodule.map_id** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule`。
形式化陈述：map_id [ContinuousAdd M] [ContinuousConstSMul R M] (s : ClosedSubmodule R 
M) : s.map (.id _ _) = s
参数：s : ClosedSubmodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.closure.congr_simp`：∀ {R : Type u_2} {M : Type u_3} [inst : Se
miring R] [inst_1 : AddCommMonoid M] [inst_2 : TopologicalSpace M]   [inst_3 : _
root_.Module R M] …
· 使用定理 `Submodule.map_id`：map_id : map (LinearMap.id : M ->ₗ[R] M) p = p
· 使用引理 `Submodule.closure_eq`：closure_eq {s : ClosedSubmodule R M} : s.closure =
 s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_id [ContinuousAdd M] [ContinuousConstSMul R M] (s : ClosedSubmodule R M) :
    s.map (.id _ _) = s := SetLike.coe_injective <| by simp [map]
/-
**ClosedSubmodule.map_le_iff_le_comap** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule
`。
形式化陈述：map_le_iff_le_comap {s : ClosedSubmodule R M} {t : ClosedSubmodule R N} : 
map f s <= t ↔ s <= comap f t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma map_le_iff_le_comap {s : ClosedSubmodule R M} {t : ClosedSubmodule R N} :
    map f s ≤ t ↔ s ≤ comap f t := by
  simp [map, Submodule.map_le_iff_le_comap]; simp [← toSubmodule_le_toSubmodule]
/-
**ClosedSubmodule.gc_map_comap** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule`。
形式化陈述：gc_map_comap : GaloisConnection (map f) (comap f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ClosedSubmodule.map_le_iff_le_comap`：map_le_iff_le_comap {s : ClosedSubm
odule R M} {t : ClosedSubmodule R N} : map f s <= t ↔ s <= comap f t
-/
lemma gc_map_comap : GaloisConnection (map f) (comap f) := fun _ _ ↦ map_le_iff_le_comap

variable {s t : ClosedSubmodule R N} {x : N}
/-
**ClosedSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `ClosedSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Max (ClosedSubmodule R N) where
  max s t := (s.toSubmodule ⊔ t.toSubmodule).closure

@[simp]
/-
**ClosedSubmodule.toSubmodule_sup** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule`。
形式化陈述：toSubmodule_sup : toSubmodule (s ⊔ t) = (s.toSubmodule ⊔ t.toSubmodule).cl
osure
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toSubmodule_sup :
  toSubmodule (s ⊔ t) = (s.toSubmodule ⊔ t.toSubmodule).closure := rfl

@[simp, norm_cast]
/-
**ClosedSubmodule.coe_sup** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule`。
形式化陈述：coe_sup : ↑(s ⊔ t) = closure (s.toSubmodule ⊔ t.toSubmodule).carrier
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.coe_closure`：∀ {R : Type u_2} {M : Type u_3} [inst : Semiring 
R] [inst_1 : AddCommMonoid M] [inst_2 : TopologicalSpace M]   [inst_3 : _root_.M
odule R M] …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coe_sup :
    ↑(s ⊔ t) = closure (s.toSubmodule ⊔ t.toSubmodule).carrier := by
  simp only [← coe_toSubmodule, toSubmodule_sup]
  simp only [coe_toSubmodule, Submodule.coe_closure, Submodule.carrier_eq_coe]
/-
**ClosedSubmodule.mem_sup** 是 Mathlib 中的一个定理，位于命名空间 `ClosedSubmodule`。
形式化陈述：∀ {R : Type u_2} {N : Type u_4} [inst : Semiring R] [inst_1 : AddCommMonoi
d N] [inst_2 : TopologicalSpace N]   [inst_3 : _root_.Module R N] [inst_4 : Cont
inuousAdd N] [inst_5 : ContinuousConstSMul R N] {s t : ClosedSubmodule R N}   {x
 : N}, x ∈ s ⊔ t ↔ x ∈ closure (↑s ⊔ ↑t).carrier
参数：↑s ⊔ ↑t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_sup :
    x ∈ s ⊔ t ↔ x ∈ closure (s.toSubmodule ⊔ t.toSubmodule).carrier := Iff.rfl
/-
**ClosedSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `ClosedSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SupSet (ClosedSubmodule R N) where
  sSup S := ⟨(⨆ s ∈ S, s.toSubmodule).closure, isClosed_closure⟩

@[simp]
/-
**ClosedSubmodule.toSubmodule_sSup** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule`。
形式化陈述：toSubmodule_sSup (S : Set (ClosedSubmodule R N)) : toSubmodule (sSup S) = 
(⨆ s in S, s.toSubmodule).closure
参数：S : Set (ClosedSubmodule R N)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toSubmodule_sSup (S : Set (ClosedSubmodule R N)) :
    toSubmodule (sSup S) = (⨆ s ∈ S, s.toSubmodule).closure := rfl

@[simp]
/-
**ClosedSubmodule.toSubmodule_iSup** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule`。
形式化陈述：toSubmodule_iSup (f : ι -> ClosedSubmodule R N) : toSubmodule (⨆ i, f i) =
 (⨆ i, (f i).toSubmodule).closure
参数：f : ι -> ClosedSubmodule R N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用引理 `ClosedSubmodule.toSubmodule_sSup`：toSubmodule_sSup (S : Set (ClosedSubmo
dule R N)) : toSubmodule (sSup S) = (⨆ s in S, s.toSubmodule).closure
· 使用定理 `iSup_range`：iSup_range {g : β -> α} {f : ι -> β} : ⨆ b in range f, g b =
 ⨆ i, g (f i)
-/
lemma toSubmodule_iSup (f : ι → ClosedSubmodule R N) :
    toSubmodule (⨆ i, f i) = (⨆ i, (f i).toSubmodule).closure := by
  rw [iSup, toSubmodule_sSup, iSup_range]

@[simp, norm_cast]
/-
**ClosedSubmodule.coe_sSup** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule`。
形式化陈述：coe_sSup (S : Set (ClosedSubmodule R N)) : ↑(sSup S) = closure (⨆ s in S, 
s.toSubmodule).carrier
参数：S : Set (ClosedSubmodule R N)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.coe_closure`：∀ {R : Type u_2} {M : Type u_3} [inst : Semiring 
R] [inst_1 : AddCommMonoid M] [inst_2 : TopologicalSpace M]   [inst_3 : _root_.M
odule R M] …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coe_sSup (S : Set (ClosedSubmodule R N)) :
    ↑(sSup S) = closure (⨆ s ∈ S, s.toSubmodule).carrier := by
  simp only [← coe_toSubmodule, toSubmodule_sSup]
  simp only [coe_toSubmodule, Submodule.coe_closure, Submodule.carrier_eq_coe]

@[simp, norm_cast]
/-
**ClosedSubmodule.coe_iSup** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule`。
形式化陈述：coe_iSup (f : ι -> ClosedSubmodule R N) : ↑(⨆ i, f i) = closure (⨆ i, (f i
).toSubmodule).carrier
参数：f : ι -> ClosedSubmodule R N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ClosedSubmodule.toSubmodule_iSup`：toSubmodule_iSup (f : ι -> ClosedSubmo
dule R N) : toSubmodule (⨆ i, f i) = (⨆ i, (f i).toSubmodule).closure
-/
lemma coe_iSup (f : ι → ClosedSubmodule R N) :
    ↑(⨆ i, f i) = closure (⨆ i, (f i).toSubmodule).carrier := by
  simp only [← coe_toSubmodule, toSubmodule_iSup, Submodule.carrier_eq_coe]
  rfl
/-
**ClosedSubmodule.mem_sSup** 是 Mathlib 中的一个定理，位于命名空间 `ClosedSubmodule`。
形式化陈述：∀ {R : Type u_2} {N : Type u_4} [inst : Semiring R] [inst_1 : AddCommMonoi
d N] [inst_2 : TopologicalSpace N]   [inst_3 : _root_.Module R N] [inst_4 : Cont
inuousAdd N] [inst_5 : ContinuousConstSMul R N] {x : N}   {S : Set (ClosedSubmod
ule R N)}, x ∈ sSup S ↔ x ∈ closure (⨆ s ∈ S, ↑s).carrier
参数：ClosedSubmodule R N；⨆ s ∈ S, ↑s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_sSup {S : Set (ClosedSubmodule R N)} :
    x ∈ sSup S ↔ x ∈ closure (⨆ s ∈ S, s.toSubmodule).carrier := Iff.rfl
/-
**ClosedSubmodule.mem_iSup** 是 Mathlib 中的一个定理，位于命名空间 `ClosedSubmodule`。
形式化陈述：∀ {ι : Sort u_1} {R : Type u_2} {N : Type u_4} [inst : Semiring R] [inst_1
 : AddCommMonoid N]   [inst_2 : TopologicalSpace N] [inst_3 : _root_.Module R N]
 [inst_4 : ContinuousAdd N]   [inst_5 : ContinuousConstSMul R N] {x : N} {f : ι 
→ ClosedSubmodule R N},   x ∈ ⨆ i, f i ↔ x ∈ closure (⨆ i, ↑(f i)).carrier
参数：⨆ i, ↑(f i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ClosedSubmodule.coe_iSup`：coe_iSup (f : ι -> ClosedSubmodule R N) : ↑(⨆ 
i, f i) = closure (⨆ i, (f i).toSubmodule).carrier
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma mem_iSup {f : ι → ClosedSubmodule R N} :
    x ∈ ⨆ i, f i ↔ x ∈ closure (⨆ i, (f i).toSubmodule).carrier := by
  simp [← SetLike.mem_coe]
/-
**ClosedSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `ClosedSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SemilatticeSup (ClosedSubmodule R N) where
  sup s t := s ⊔ t
  le_sup_left _ _ _ hx := subset_closure <| Submodule.mem_sup_left hx
  le_sup_right _ _ _ hx := subset_closure <| Submodule.mem_sup_right hx
  sup_le _ _ _ ha hb := Submodule.closure_le.mpr <| sup_le_iff.mpr ⟨ha, hb⟩
/-
**ClosedSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `ClosedSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteSemilatticeSup (ClosedSubmodule R N) where
  isLUB_sSup _ := by
    refine ⟨fun a ha x hx ↦ ?_, fun a h x ↦ ?_⟩
    · exact subset_closure <| Submodule.mem_iSup_of_mem _ <| Submodule.mem_iSup_of_mem ha hx
    · rw [← ClosedSubmodule.closure_toSubmodule_eq (s := a)]
      apply closure_mono
      simp only [Submodule.coe_toAddSubmonoid, coe_toSubmodule]
      intro y hy
      simp only [SetLike.mem_coe, Submodule.mem_iSup] at hy
      exact hy a fun b _ hz ↦ Submodule.mem_iSup _ |>.mp hz _ <| fun hb ↦ h hb
/-
**ClosedSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `ClosedSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Lattice (ClosedSubmodule R N) where
/-
**ClosedSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `ClosedSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [T1Space N] : CompleteLattice (ClosedSubmodule R N) where

end ClosedSubmodule

namespace ClosedSubmodule

variable (f : M ≃L[R] N)

/-- A continuous equivalence `f` between modules `M` and `N` on `R` induces an equivalence between
closed submodules in `M` and those in `N` through `map f`.
The definition does not use `ClosedSubmodule.map` because that has additional `ContinuousAdd` and
`ContinuousConstSMul` type-class assumptions. -/
/-
**ClosedSubmodule.mapEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ClosedSubmodule`。
形式化陈述：mapEquiv : ClosedSubmodule R M ≃ ClosedSubmodule R N where toFun s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous equivalence `f` between modules `M` and `N` on `R` induces an equiv
alence between
closed submodules in `M` and those in `N` through `map f`.
The definition does not use `ClosedSubmodule.map` because that has additional `C
ontinuousAdd` and
`ContinuousConstSMul` type-class assumptions.
-/
def mapEquiv : ClosedSubmodule R M ≃ ClosedSubmodule R N where
  toFun s := ⟨s.toSubmodule.map f.toLinearMap, by simpa using s.isClosed⟩
  invFun t := ⟨t.toSubmodule.map f.symm.toLinearMap, by simpa using t.isClosed⟩
  left_inv := by intro _; ext _; simp
  right_inv := by intro _; ext _; simp

variable (s : ClosedSubmodule R M)

@[simp]
/-
**ClosedSubmodule.mapEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule`。
形式化陈述：mapEquiv_apply : (s.mapEquiv f).toSubmodule = s.toSubmodule.map f.toLinear
Map
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapEquiv_apply : (s.mapEquiv f).toSubmodule = s.toSubmodule.map f.toLinearMap := rfl

@[simp]
/-
**ClosedSubmodule.mapEquiv_symm** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule`。
形式化陈述：mapEquiv_symm : mapEquiv f.symm = (mapEquiv f).symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapEquiv_symm : mapEquiv f.symm = (mapEquiv f).symm := rfl

@[simp]
/-
**ClosedSubmodule.mem_mapEquiv_iff** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule`。
形式化陈述：mem_mapEquiv_iff (x : N) : x in (s.mapEquiv f) ↔ f.symm x in s
参数：x : N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.mem_map_equiv`：mem_map_equiv {e : M ≃ₛₗ[τ₁₂] M₂} {x : M₂} : x 
in p.map (e : M ->ₛₗ[τ₁₂] M₂) ↔ e.symm x in p
-/
lemma mem_mapEquiv_iff (x : N) : x ∈ (s.mapEquiv f) ↔ f.symm x ∈ s :=
  Submodule.mem_map_equiv (e := f.toLinearEquiv) s.toSubmodule
/-
**ClosedSubmodule.mem_mapEquiv_iff'** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule`。
形式化陈述：mem_mapEquiv_iff' (x : M) : f x in (s.mapEquiv f) ↔ x in s
参数：x : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearEquiv.symm_apply_apply`：symm_apply_apply (e : M₁ ≃SL[σ₁₂
] M₂) (b : M₁) : e.symm (e b) = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_mapEquiv_iff' (x : M) : f x ∈ (s.mapEquiv f) ↔ x ∈ s := by
  simp

@[simp]
/-
**ClosedSubmodule.mapEquiv_bot_eq_bot** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule
`。
形式化陈述：mapEquiv_bot_eq_bot [T1Space M] [T1Space N] : ((⊥ : ClosedSubmodule R M).m
apEquiv f) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosedSubmodule.ext`：∀ {R : Type u_2} {M : Type u_3} {inst : Semiring R}
 {inst_1 : AddCommMonoid M} {inst_2 : TopologicalSpace M}   {inst_3 : _root_.Mod
ule R M} …
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.map_bot`：map_bot (f : M ->ₛₗ[σ₁₂] M₂) : map f ⊥ = ⊥
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mapEquiv_bot_eq_bot [T1Space M] [T1Space N] : ((⊥ : ClosedSubmodule R M).mapEquiv f) = ⊥ := by
  ext x; simp

@[simp]
/-
**ClosedSubmodule.mapEquiv_top_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule
`。
形式化陈述：mapEquiv_top_eq_top : ((⊤ : ClosedSubmodule R M).mapEquiv f) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosedSubmodule.ext`：∀ {R : Type u_2} {M : Type u_3} {inst : Semiring R}
 {inst_1 : AddCommMonoid M} {inst_2 : TopologicalSpace M}   {inst_3 : _root_.Mod
ule R M} …
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
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
· 使用定理 `LinearEquiv.range`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ :
 Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid 
M] [ins…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mapEquiv_top_eq_top : ((⊤ : ClosedSubmodule R M).mapEquiv f) = ⊤ := by
  ext x; simp

@[simp]
/-
**ClosedSubmodule.mapEquiv_inf_eq** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule`。
形式化陈述：mapEquiv_inf_eq (f : M ≃L[R] N) {s t : ClosedSubmodule R M} : (s ⊓ t).mapE
quiv f = s.mapEquiv f ⊓ t.mapEquiv f
参数：f : M ≃L[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosedSubmodule.ext`：∀ {R : Type u_2} {M : Type u_3} {inst : Semiring R}
 {inst_1 : AddCommMonoid M} {inst_2 : TopologicalSpace M}   {inst_3 : _root_.Mod
ule R M} …
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mapEquiv_inf_eq (f : M ≃L[R] N) {s t : ClosedSubmodule R M} :
    (s ⊓ t).mapEquiv f = s.mapEquiv f ⊓ t.mapEquiv f := by
  ext x
  simp only [Submodule.carrier_eq_coe, coe_toSubmodule, SetLike.mem_coe, toSubmodule_inf,
    Submodule.coe_inf, Set.mem_inter_iff, mem_mapEquiv_iff, mem_inf]

variable [ContinuousAdd N] [ContinuousConstSMul R N] [ContinuousAdd M] [ContinuousConstSMul R M]

@[simp]
/-
**ClosedSubmodule.closure_map_eq_mapEquiv_closure** 是 Mathlib 中的一个引理，位于命名空间 `Clo
sedSubmodule`。
形式化陈述：closure_map_eq_mapEquiv_closure (s : Submodule R M) : (s.map f.toLinearMap
).closure = s.closure.mapEquiv f
参数：s : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosedSubmodule.ext`：∀ {R : Type u_2} {M : Type u_3} {inst : Semiring R}
 {inst_1 : AddCommMonoid M} {inst_2 : TopologicalSpace M}   {inst_3 : _root_.Mod
ule R M} …
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.coe_closure`：∀ {R : Type u_2} {M : Type u_3} [inst : Semiring 
R] [inst_1 : AddCommMonoid M] [inst_2 : TopologicalSpace M]   [inst_3 : _root_.M
odule R M] …
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearEquiv.image_closure`：image_closure (e : M₁ ≃SL[σ₁₂] M₂) 
(s : Set M₁) : e '' closure s = closure (e '' s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma closure_map_eq_mapEquiv_closure (s : Submodule R M) :
    (s.map f.toLinearMap).closure = s.closure.mapEquiv f := by
  ext x
  simp only [Submodule.carrier_eq_coe, coe_toSubmodule, Submodule.coe_closure, Submodule.map_coe,
    LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv, mapEquiv_apply, Set.mem_image]
  rw [← ContinuousLinearEquiv.image_closure]
  simp

@[simp]
/-
**ClosedSubmodule.mapEquiv_sup_eq** 是 Mathlib 中的一个引理，位于命名空间 `ClosedSubmodule`。
形式化陈述：mapEquiv_sup_eq (f : M ≃L[R] N) {s t : ClosedSubmodule R M} : (s ⊔ t).mapE
quiv f = s.mapEquiv f ⊔ t.mapEquiv f
参数：f : M ≃L[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosedSubmodule.ext`：∀ {R : Type u_2} {M : Type u_3} {inst : Semiring R}
 {inst_1 : AddCommMonoid M} {inst_2 : TopologicalSpace M}   {inst_3 : _root_.Mod
ule R M} …
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Submodule.coe_closure`：∀ {R : Type u_2} {M : Type u_3} [inst : Semiring 
R] [inst_1 : AddCommMonoid M] [inst_2 : TopologicalSpace M]   [inst_3 : _root_.M
odule R M] …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.map_sup`：map_sup (f : M ->ₛₗ[σ₁₂] M₂) : map f (p ⊔ p') = map f
 p ⊔ map f p'
· 使用定理 `Submodule.map_coe`：map_coe (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M) : (m
ap f p : Set M₂) = f '' p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mapEquiv_sup_eq (f : M ≃L[R] N) {s t : ClosedSubmodule R M} :
    (s ⊔ t).mapEquiv f = s.mapEquiv f ⊔ t.mapEquiv f := by
  ext x
  simp only [mapEquiv_apply, toSubmodule_sup, Submodule.carrier_eq_coe, Submodule.map_coe,
    LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv, coe_toSubmodule,
    Submodule.coe_closure, Set.mem_image]
  have : f = f.toLinearEquiv.toLinearMap := by
    exact LinearMap.ext (congrFun rfl)
  rw [← this, ← Submodule.coe_closure, ← Submodule.map_sup, Submodule.map_coe]
  simp [← ContinuousLinearEquiv.image_closure]

end ClosedSubmodule

section CompleteSpace

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {𝕜 H : Type*} [Semiring 𝕜] [AddCommMonoid H] [UniformSpace H] [Module 𝕜 H]
    [CompleteSpace H] (K : ClosedSubmodule 𝕜 H) : CompleteSpace K := by
  apply IsComplete.completeSpace_coe
  rw [← ClosedSubmodule.carrier_eq_coe]
  exact K.isClosed'.isComplete

end CompleteSpace

