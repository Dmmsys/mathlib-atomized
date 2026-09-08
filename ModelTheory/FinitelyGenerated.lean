/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.ModelTheory.Substructures

/-!
# Finitely Generated First-Order Structures

This file defines what it means for a first-order (sub)structure to be finitely or countably
generated, similarly to other finitely-generated objects in the algebra library.

## Main Definitions

- `FirstOrder.Language.Substructure.FG` indicates that a substructure is finitely generated.
- `FirstOrder.Language.Structure.FG` indicates that a structure is finitely generated.
- `FirstOrder.Language.Substructure.CG` indicates that a substructure is countably generated.
- `FirstOrder.Language.Structure.CG` indicates that a structure is countably generated.


## TODO

Develop a more unified definition of finite generation using the theory of closure operators, or use
this definition of finite generation to define the others.

-/

@[expose] public section

open FirstOrder Set

namespace FirstOrder

namespace Language

open Structure

variable {L : Language} {M : Type*} [L.Structure M]

namespace Substructure

/-- A substructure of `M` is finitely generated if it is the closure of a finite subset of `M`. -/
/-
**FirstOrder.Language.Substructure.FG** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Lang
uage.Substructure`。
形式化陈述：FG (N : L.Substructure M) : Prop
参数：N : L.Substructure M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A substructure of `M` is finitely generated if it is the closure of a finite sub
set of `M`.
-/
def FG (N : L.Substructure M) : Prop :=
  ∃ S : Finset M, closure L S = N
/-
**FirstOrder.Language.Substructure.fg_def** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.Substructure`。
形式化陈述：fg_def {N : L.Substructure M} : N.FG ↔ exists S : Set M, S.Finite ∧ closur
e L S = N
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Set.Finite.exists_finset_coe`：∀ {α : Type u} {s : Set α}, s.Finite → ∃ s
', ↑s' = s
-/
theorem fg_def {N : L.Substructure M} : N.FG ↔ ∃ S : Set M, S.Finite ∧ closure L S = N :=
  ⟨fun ⟨t, h⟩ => ⟨_, Finset.finite_toSet t, h⟩, by
    rintro ⟨t', h, rfl⟩
    rcases Finite.exists_finset_coe h with ⟨t, rfl⟩
    exact ⟨t, rfl⟩⟩
/-
**FirstOrder.Language.Substructure.fg_iff_exists_fin_generating_family** 是 Mathl
ib 中的一个定理，位于命名空间 `FirstOrder.Language.Substructure`。
形式化陈述：fg_iff_exists_fin_generating_family {N : L.Substructure M} : N.FG ↔ exists
 (n : Nat) (s : Fin n -> M), closure L (range s) = N
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Substructure.fg_def`：fg_def {N : L.Substructure M} :
 N.FG ↔ exists S : Set M, S.Finite ∧ closure L S = N
· 使用定理 `Set.Finite.fin_embedding`：∀ {α : Type u} {s : Set α}, s.Finite → ∃ n f, 
Set.range ⇑f = s
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem fg_iff_exists_fin_generating_family {N : L.Substructure M} :
    N.FG ↔ ∃ (n : ℕ) (s : Fin n → M), closure L (range s) = N := by
  rw [fg_def]
  constructor
  · rintro ⟨S, Sfin, hS⟩
    obtain ⟨n, f, rfl⟩ := Sfin.fin_embedding
    exact ⟨n, f, hS⟩
  · rintro ⟨n, s, hs⟩
    exact ⟨range s, finite_range s, hs⟩
/-
**FirstOrder.Language.Substructure.fg_bot** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.Substructure`。
形式化陈述：fg_bot : (⊥ : L.Substructure M).FG
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `FirstOrder.Language.Substructure.closure_empty`：closure_empty : closure 
L (∅ : Set M) = ⊥
-/
theorem fg_bot : (⊥ : L.Substructure M).FG :=
  ⟨∅, by rw [Finset.coe_empty, closure_empty]⟩
/-
**FirstOrder.Language.Substructure.instInhabited_fg** 是 Mathlib 中的一个实例，位于命名空间 `F
irstOrder.Language.Substructure`。
形式化陈述：instInhabited_fg : Inhabited { S : L.Substructure M // S.FG }
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Substructure.fg_bot`：fg_bot : (⊥ : L.Substructure M)
.FG
-/
instance instInhabited_fg : Inhabited { S : L.Substructure M // S.FG } := ⟨⊥, fg_bot⟩
/-
**FirstOrder.Language.Substructure.fg_closure** 是 Mathlib 中的一个定理，位于命名空间 `FirstOr
der.Language.Substructure`。
形式化陈述：fg_closure {s : Set M} (hs : s.Finite) : FG (closure L s)
参数：hs : s.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
-/
theorem fg_closure {s : Set M} (hs : s.Finite) : FG (closure L s) :=
  ⟨hs.toFinset, by rw [hs.coe_toFinset]⟩
/-
**FirstOrder.Language.Substructure.fg_closure_singleton** 是 Mathlib 中的一个定理，位于命名空
间 `FirstOrder.Language.Substructure`。
形式化陈述：fg_closure_singleton (x : M) : FG (closure L ({x} : Set M))
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Substructure.fg_closure`：fg_closure {s : Set M} (hs 
: s.Finite) : FG (closure L s)
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
-/
theorem fg_closure_singleton (x : M) : FG (closure L ({x} : Set M)) :=
  fg_closure (finite_singleton x)
/-
**FirstOrder.Language.Substructure.FG.sup** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.Substructure.FG`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type u_1} [inst : L.Structure M] {N₁ N₂ :
 L.Substructure M},   N₁.FG → N₂.FG → (N₁ ⊔ N₂).FG
参数：N₁ ⊔ N₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.Substructure.fg_def`：fg_def {N : L.Substructure M} :
 N.FG ↔ exists S : Set M, S.Finite ∧ closure L S = N
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Substructure.closure_union`：closure_union (s t : Set
 M) : closure L (s union t) = closure L s ⊔ closure L t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem FG.sup {N₁ N₂ : L.Substructure M} (hN₁ : N₁.FG) (hN₂ : N₂.FG) : (N₁ ⊔ N₂).FG :=
  let ⟨t₁, ht₁⟩ := fg_def.1 hN₁
  let ⟨t₂, ht₂⟩ := fg_def.1 hN₂
  fg_def.2 ⟨t₁ ∪ t₂, ht₁.1.union ht₂.1, by rw [closure_union, ht₁.2, ht₂.2]⟩
/-
**FirstOrder.Language.Substructure.FG.map** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.Substructure.FG`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type u_1} [inst : L.Structure M] {N : Typ
e u_2} [inst_1 : L.Structure N]   (f : L.Hom M N) {s : L.Substructure M}, s.FG →
 (FirstOrder.Language.Substructure.map f s).FG
参数：f : L.Hom M N；FirstOrder.Language.Substructure.map f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.Substructure.fg_def`：fg_def {N : L.Substructure M} :
 N.FG ↔ exists S : Set M, S.Finite ∧ closure L S = N
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Substructure.closure_image`：closure_image (f : M ->[
L] N) : closure L (f '' s) = map f (closure L s)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem FG.map {N : Type*} [L.Structure N] (f : M →[L] N) {s : L.Substructure M} (hs : s.FG) :
    (s.map f).FG :=
  let ⟨t, ht⟩ := fg_def.1 hs
  fg_def.2 ⟨f '' t, ht.1.image _, by rw [closure_image, ht.2]⟩
/-
**FirstOrder.Language.Substructure.FG.of_map_embedding** 是 Mathlib 中的一个定理，位于命名空间
 `FirstOrder.Language.Substructure.FG`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type u_1} [inst : L.Structure M] {N : Typ
e u_2} [inst_1 : L.Structure N]   (f : L.Embedding M N) {s : L.Substructure M}, 
(FirstOrder.Language.Substructure.map f.toHom s).FG → s.FG
参数：f : L.Embedding M N；FirstOrder.Language.Substructure.map f.toHom s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Substructure.fg_def`：fg_def {N : L.Substructure M} :
 N.FG ↔ exists S : Set M, S.Finite ∧ closure L S = N
· 使用定理 `Set.Finite.preimage`：∀ {α : Type u} {β : Type v} {f : α → β} {s : Set β}
, Set.InjOn f (f ⁻¹' s) → s.Finite → (f ⁻¹' s).Finite
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `FirstOrder.Language.Embedding.injective`：injective (f : M ↪[L] N) : Func
tion.Injective f
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `FirstOrder.Language.Substructure.map_injective_of_injective`：map_injecti
ve_of_injective : Function.Injective (map f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Substructure.map_closure`：map_closure (f : M ->[L] N
) (s : Set M) : (closure L s).map f = closure L (f '' s)
· 使用定理 `FirstOrder.Language.Embedding.coe_toHom`：coe_toHom {f : M ↪[L] N} : (f.t
oHom : M -> N) = f
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
· 使用定理 `FirstOrder.Language.Substructure.subset_closure`：subset_closure : s subs
eteq closure L s
· 使用定理 `FirstOrder.Language.Hom.map_le_range`：map_le_range {f : M ->[L] N} {p : 
L.Substructure M} : map f p <= range f
-/
theorem FG.of_map_embedding {N : Type*} [L.Structure N] (f : M ↪[L] N) {s : L.Substructure M}
    (hs : (s.map f.toHom).FG) : s.FG := by
  rcases hs with ⟨t, h⟩
  rw [fg_def]
  refine ⟨f ⁻¹' t, t.finite_toSet.preimage f.injective.injOn, ?_⟩
  have hf : Function.Injective f.toHom := f.injective
  refine map_injective_of_injective hf ?_
  rw [← h, map_closure, Embedding.coe_toHom, image_preimage_eq_of_subset]
  intro x hx
  have h' := subset_closure (L := L) hx
  rw [h] at h'
  exact Hom.map_le_range h'

set_option backward.isDefEq.respectTransparency false in
/-
**FirstOrder.Language.Substructure.FG.of_finite** 是 Mathlib 中的一个定理，位于命名空间 `First
Order.Language.Substructure.FG`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type u_1} [inst : L.Structure M] {s : L.S
ubstructure M} [h : Finite ↥s], s.FG
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `FirstOrder.Language.Substructure.closure_eq`：closure_eq : closure L (S :
 Set M) = S
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem FG.of_finite {s : L.Substructure M} [h : Finite s] : s.FG :=
  ⟨Set.Finite.toFinset h, by simp only [Finite.coe_toFinset, closure_eq]⟩
/-
**FirstOrder.Language.Substructure.FG.finite** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrd
er.Language.Substructure.FG`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type u_1} [inst : L.Structure M] [L.IsRel
ational] {S : L.Substructure M},   S.FG → Finite ↥S
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `FirstOrder.Language.Substructure.closure_eq_of_isRelational`：closure_eq_
of_isRelational [L.IsRelational] (s : Set M) : closure L s = s
-/
theorem FG.finite [L.IsRelational] {S : L.Substructure M} (h : S.FG) : Finite S := by
  obtain ⟨s, rfl⟩ := h
  have hs := s.finite_toSet
  rw [← closure_eq_of_isRelational L (s : Set M)] at hs
  exact hs
/-
**FirstOrder.Language.Substructure.fg_iff_finite** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.Substructure`。
形式化陈述：fg_iff_finite [L.IsRelational] {S : L.Substructure M} : S.FG ↔ Finite S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Substructure.FG.finite`：∀ {L : FirstOrder.Language} 
{M : Type u_1} [inst : L.Structure M] [L.IsRelational] {S : L.Substructure M},  
 S.FG → Finite ↥S
· 使用定理 `FirstOrder.Language.Substructure.FG.of_finite`：∀ {L : FirstOrder.Languag
e} {M : Type u_1} [inst : L.Structure M] {s : L.Substructure M} [h : Finite ↥s],
 s.FG
-/
theorem fg_iff_finite [L.IsRelational] {S : L.Substructure M} : S.FG ↔ Finite S :=
  ⟨FG.finite, fun _ => FG.of_finite⟩

/-- A substructure of `M` is countably generated if it is the closure of a countable subset of `M`.
-/
/-
**FirstOrder.Language.Substructure.CG** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Lang
uage.Substructure`。
形式化陈述：CG (N : L.Substructure M) : Prop
参数：N : L.Substructure M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A substructure of `M` is countably generated if it is the closure of a countable
 subset of `M`.
-/
def CG (N : L.Substructure M) : Prop :=
  ∃ S : Set M, S.Countable ∧ closure L S = N
/-
**FirstOrder.Language.Substructure.cg_def** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.Substructure`。
形式化陈述：cg_def {N : L.Substructure M} : N.CG ↔ exists S : Set M, S.Countable ∧ clo
sure L S = N
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.refl`：∀ (a : Prop), a ↔ a
-/
theorem cg_def {N : L.Substructure M} : N.CG ↔ ∃ S : Set M, S.Countable ∧ closure L S = N :=
  Iff.refl _
/-
**FirstOrder.Language.Substructure.FG.cg** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.L
anguage.Substructure.FG`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type u_1} [inst : L.Structure M] {N : L.S
ubstructure M}, N.FG → N.CG
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.Substructure.fg_def`：fg_def {N : L.Substructure M} :
 N.FG ↔ exists S : Set M, S.Finite ∧ closure L S = N
· 使用定理 `Set.Finite.countable`：∀ {α : Type u} {s : Set α}, s.Finite → s.Countable
-/
theorem FG.cg {N : L.Substructure M} (h : N.FG) : N.CG := by
  obtain ⟨s, hf, rfl⟩ := fg_def.1 h
  exact ⟨s, hf.countable, rfl⟩
/-
**FirstOrder.Language.Substructure.cg_iff_empty_or_exists_nat_generating_family*
* 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Language.Substructure`。
形式化陈述：cg_iff_empty_or_exists_nat_generating_family {N : L.Substructure M} : N.CG
 ↔ N = (∅ : Set M) ∨ exists s : Nat -> M, closure L (range s) = N
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Substructure.cg_def`：cg_def {N : L.Substructure M} :
 N.CG ↔ exists S : Set M, S.Countable ∧ closure L S = N
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Or.intro_left`：∀ {a : Prop} (b : Prop), a → a ∨ b
· 使用定理 `Set.Countable.exists_eq_range`：∀ {α : Type u} {s : Set α}, s.Countable →
 s.Nonempty → ∃ f, s = Set.range f
· 使用定理 `Set.Countable.union`：∀ {α : Type u} {s t : Set α}, s.Countable → t.Count
able → (s ∪ t).Countable
· 使用定理 `Set.countable_singleton`：∀ {α : Type u} (a : α), {a}.Countable
· 使用定理 `Set.Nonempty.inr`：∀ {α : Type u} {s t : Set α}, t.Nonempty → (s ∪ t).Non
empty
· 使用定理 `Set.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Set α).Nonem
pty
· 使用定理 `Or.intro_right`：∀ {b : Prop} (a : Prop), b → a ∨ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Substructure.closure_union`：closure_union (s t : Set
 M) : closure L (s union t) = closure L s ⊔ closure L t
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
· 使用定理 `FirstOrder.Language.Substructure.closure_le`：closure_le : closure L s <=
 S ↔ s subseteq S
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Set.Nonempty.some_mem`：∀ {α : Type u} {s : Set α} (h : s.Nonempty), h.so
me ∈ s
· 使用定理 `Set.countable_empty`：∀ {α : Type u}, ∅.Countable
· 使用定理 `FirstOrder.Language.Substructure.closure_eq_of_le`：closure_eq_of_le (h₁ 
: s subseteq S) (h₂ : S <= closure L s) : closure L s = S
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
· 使用定理 `SetLike.coe_subset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike 
A B] [inst_1 : LE A] [IsConcreteLE A B] {S T : A}, ↑S ⊆ ↑T ↔ S ≤ T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Set.countable_range`：countable_range [Countable ι] (f : ι -> β) : (range
 f).Countable
· 使用定理 `instCountableNat`：Countable ℕ
-/
theorem cg_iff_empty_or_exists_nat_generating_family {N : L.Substructure M} :
    N.CG ↔ N = (∅ : Set M) ∨ ∃ s : ℕ → M, closure L (range s) = N := by
  rw [cg_def]
  constructor
  · rintro ⟨S, Scount, hS⟩
    rcases eq_empty_or_nonempty (N : Set M) with h | h
    · exact Or.intro_left _ h
    obtain ⟨f, h'⟩ :=
      (Scount.union (Set.countable_singleton h.some)).exists_eq_range
        (singleton_nonempty h.some).inr
    refine Or.intro_right _ ⟨f, ?_⟩
    rw [← h', closure_union, hS, sup_eq_left, closure_le]
    exact singleton_subset_iff.2 h.some_mem
  · intro h
    rcases h with h | h
    · refine ⟨∅, countable_empty, closure_eq_of_le (empty_subset _) ?_⟩
      rw [← SetLike.coe_subset_coe, h]
      exact empty_subset _
    · obtain ⟨f, rfl⟩ := h
      exact ⟨range f, countable_range _, rfl⟩
/-
**FirstOrder.Language.Substructure.cg_bot** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.Substructure`。
形式化陈述：cg_bot : (⊥ : L.Substructure M).CG
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Substructure.FG.cg`：∀ {L : FirstOrder.Language} {M :
 Type u_1} [inst : L.Structure M] {N : L.Substructure M}, N.FG → N.CG
· 使用定理 `FirstOrder.Language.Substructure.fg_bot`：fg_bot : (⊥ : L.Substructure M)
.FG
-/
theorem cg_bot : (⊥ : L.Substructure M).CG :=
  fg_bot.cg
/-
**FirstOrder.Language.Substructure.cg_closure** 是 Mathlib 中的一个定理，位于命名空间 `FirstOr
der.Language.Substructure`。
形式化陈述：cg_closure {s : Set M} (hs : s.Countable) : CG (closure L s)
参数：hs : s.Countable。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cg_closure {s : Set M} (hs : s.Countable) : CG (closure L s) :=
  ⟨s, hs, rfl⟩
/-
**FirstOrder.Language.Substructure.cg_closure_singleton** 是 Mathlib 中的一个定理，位于命名空
间 `FirstOrder.Language.Substructure`。
形式化陈述：cg_closure_singleton (x : M) : CG (closure L ({x} : Set M))
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Substructure.FG.cg`：∀ {L : FirstOrder.Language} {M :
 Type u_1} [inst : L.Structure M] {N : L.Substructure M}, N.FG → N.CG
· 使用定理 `FirstOrder.Language.Substructure.fg_closure_singleton`：fg_closure_single
ton (x : M) : FG (closure L ({x} : Set M))
-/
theorem cg_closure_singleton (x : M) : CG (closure L ({x} : Set M)) :=
  (fg_closure_singleton x).cg
/-
**FirstOrder.Language.Substructure.CG.sup** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.Substructure.CG`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type u_1} [inst : L.Structure M] {N₁ N₂ :
 L.Substructure M},   N₁.CG → N₂.CG → (N₁ ⊔ N₂).CG
参数：N₁ ⊔ N₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.Substructure.cg_def`：cg_def {N : L.Substructure M} :
 N.CG ↔ exists S : Set M, S.Countable ∧ closure L S = N
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Countable.union`：∀ {α : Type u} {s t : Set α}, s.Countable → t.Count
able → (s ∪ t).Countable
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Substructure.closure_union`：closure_union (s t : Set
 M) : closure L (s union t) = closure L s ⊔ closure L t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem CG.sup {N₁ N₂ : L.Substructure M} (hN₁ : N₁.CG) (hN₂ : N₂.CG) : (N₁ ⊔ N₂).CG :=
  let ⟨t₁, ht₁⟩ := cg_def.1 hN₁
  let ⟨t₂, ht₂⟩ := cg_def.1 hN₂
  cg_def.2 ⟨t₁ ∪ t₂, ht₁.1.union ht₂.1, by rw [closure_union, ht₁.2, ht₂.2]⟩
/-
**FirstOrder.Language.Substructure.CG.map** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.Substructure.CG`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type u_1} [inst : L.Structure M] {N : Typ
e u_2} [inst_1 : L.Structure N]   (f : L.Hom M N) {s : L.Substructure M}, s.CG →
 (FirstOrder.Language.Substructure.map f s).CG
参数：f : L.Hom M N；FirstOrder.Language.Substructure.map f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.Substructure.cg_def`：cg_def {N : L.Substructure M} :
 N.CG ↔ exists S : Set M, S.Countable ∧ closure L S = N
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Countable.image`：∀ {α : Type u} {β : Type v} {s : Set α}, s.Countabl
e → ∀ (f : α → β), (f '' s).Countable
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Substructure.closure_image`：closure_image (f : M ->[
L] N) : closure L (f '' s) = map f (closure L s)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem CG.map {N : Type*} [L.Structure N] (f : M →[L] N) {s : L.Substructure M} (hs : s.CG) :
    (s.map f).CG :=
  let ⟨t, ht⟩ := cg_def.1 hs
  cg_def.2 ⟨f '' t, ht.1.image _, by rw [closure_image, ht.2]⟩
/-
**FirstOrder.Language.Substructure.CG.of_map_embedding** 是 Mathlib 中的一个定理，位于命名空间
 `FirstOrder.Language.Substructure.CG`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type u_1} [inst : L.Structure M] {N : Typ
e u_2} [inst_1 : L.Structure N]   (f : L.Embedding M N) {s : L.Substructure M}, 
(FirstOrder.Language.Substructure.map f.toHom s).CG → s.CG
参数：f : L.Embedding M N；FirstOrder.Language.Substructure.map f.toHom s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Substructure.cg_def`：cg_def {N : L.Substructure M} :
 N.CG ↔ exists S : Set M, S.Countable ∧ closure L S = N
· 使用定理 `Set.Countable.preimage`：∀ {α : Type u} {β : Type v} {s : Set β}, s.Count
able → ∀ {f : α → β}, Function.Injective f → (f ⁻¹' s).Countable
· 使用定理 `FirstOrder.Language.Embedding.injective`：injective (f : M ↪[L] N) : Func
tion.Injective f
· 使用定理 `FirstOrder.Language.Substructure.map_injective_of_injective`：map_injecti
ve_of_injective : Function.Injective (map f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Substructure.map_closure`：map_closure (f : M ->[L] N
) (s : Set M) : (closure L s).map f = closure L (f '' s)
· 使用定理 `FirstOrder.Language.Embedding.coe_toHom`：coe_toHom {f : M ↪[L] N} : (f.t
oHom : M -> N) = f
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
· 使用定理 `FirstOrder.Language.Substructure.subset_closure`：subset_closure : s subs
eteq closure L s
· 使用定理 `FirstOrder.Language.Hom.map_le_range`：map_le_range {f : M ->[L] N} {p : 
L.Substructure M} : map f p <= range f
-/
theorem CG.of_map_embedding {N : Type*} [L.Structure N] (f : M ↪[L] N) {s : L.Substructure M}
    (hs : (s.map f.toHom).CG) : s.CG := by
  rcases hs with ⟨t, h1, h2⟩
  rw [cg_def]
  refine ⟨f ⁻¹' t, h1.preimage f.injective, ?_⟩
  have hf : Function.Injective f.toHom := f.injective
  refine map_injective_of_injective hf ?_
  rw [← h2, map_closure, Embedding.coe_toHom, image_preimage_eq_of_subset]
  intro x hx
  have h' := subset_closure (L := L) hx
  rw [h2] at h'
  exact Hom.map_le_range h'
/-
**FirstOrder.Language.Substructure.cg_iff_countable** 是 Mathlib 中的一个定理，位于命名空间 `F
irstOrder.Language.Substructure`。
形式化陈述：cg_iff_countable [Countable (Σ l, L.Functions l)] {s : L.Substructure M} :
 s.CG ↔ Countable s
参数：Σ l, L.Functions l。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Countable.substructure_closure`：∀ (L : FirstOrder.Language) {M : Typ
e w} [inst : L.Structure M] {s : Set M} [Countable ((l : ℕ) × L.Functions l)],  
 s.Countable → Countable…
· 使用定理 `Countable.to_set`：∀ {α : Type u} {s : Set α}, Countable ↑s → s.Countable
· 使用定理 `FirstOrder.Language.Substructure.closure_eq`：closure_eq : closure L (S :
 Set M) = S
-/
theorem cg_iff_countable [Countable (Σ l, L.Functions l)] {s : L.Substructure M} :
    s.CG ↔ Countable s := by
  refine ⟨?_, fun h => ⟨s, h.to_set, s.closure_eq⟩⟩
  rintro ⟨s, h, rfl⟩
  exact h.substructure_closure L
/-
**FirstOrder.Language.Substructure.cg_of_countable** 是 Mathlib 中的一个定理，位于命名空间 `Fi
rstOrder.Language.Substructure`。
形式化陈述：cg_of_countable {s : L.Substructure M} [h : Countable s] : s.CG
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Countable.to_set`：∀ {α : Type u} {s : Set α}, Countable ↑s → s.Countable
· 使用定理 `FirstOrder.Language.Substructure.closure_eq`：closure_eq : closure L (S :
 Set M) = S
-/
theorem cg_of_countable {s : L.Substructure M} [h : Countable s] : s.CG :=
  ⟨s, h.to_set, s.closure_eq⟩

end Substructure

open Substructure

namespace Structure

variable (L) (M)

/-- A structure is finitely generated if it is the closure of a finite subset. -/
/-
**FirstOrder.Language.Structure.FG** 是 Mathlib 中的一个归纳类型，位于命名空间 `FirstOrder.Langu
age.Structure`。
形式化陈述：(L : FirstOrder.Language) → (M : Type u_1) → [L.Structure M] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A structure is finitely generated if it is the closure of a finite subset.
-/
class FG : Prop where
  out : (⊤ : L.Substructure M).FG

/-- A structure is countably generated if it is the closure of a countable subset. -/
/-
**FirstOrder.Language.Structure.CG** 是 Mathlib 中的一个归纳类型，位于命名空间 `FirstOrder.Langu
age.Structure`。
形式化陈述：(L : FirstOrder.Language) → (M : Type u_1) → [L.Structure M] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A structure is countably generated if it is the closure of a countable subset.
-/
class CG : Prop where
  out : (⊤ : L.Substructure M).CG

variable {L M}
/-
**FirstOrder.Language.Structure.fg_def** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lan
guage.Structure`。
形式化陈述：fg_def : FG L M ↔ (⊤ : L.Substructure M).FG
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Structure.FG.out`：∀ {L : FirstOrder.Language} {M : T
ype u_1} {inst : L.Structure M} [self : FirstOrder.Language.Structure.FG L M], ⊤
.FG
-/
theorem fg_def : FG L M ↔ (⊤ : L.Substructure M).FG :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

/-- An equivalent expression of `Structure.FG` in terms of `Set.Finite` instead of `Finset`. -/
/-
**FirstOrder.Language.Structure.fg_iff** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lan
guage.Structure`。
形式化陈述：fg_iff : FG L M ↔ exists S : Set M, S.Finite ∧ closure L S = (⊤ : L.Substr
ucture M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Structure.fg_def`：fg_def : FG L M ↔ (⊤ : L.Substruct
ure M).FG
· 使用定理 `FirstOrder.Language.Substructure.fg_def`：fg_def {N : L.Substructure M} :
 N.FG ↔ exists S : Set M, S.Finite ∧ closure L S = N
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
An equivalent expression of `Structure.FG` in terms of `Set.Finite` instead of `
Finset`.
-/
theorem fg_iff : FG L M ↔ ∃ S : Set M, S.Finite ∧ closure L S = (⊤ : L.Substructure M) := by
  rw [fg_def, Substructure.fg_def]
/-
**FirstOrder.Language.Structure.FG.range** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.L
anguage.Structure.FG`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type u_1} [inst : L.Structure M] {N : Typ
e u_2} [inst_1 : L.Structure N],   FirstOrder.Language.Structure.FG L M → ∀ (f :
 L.Hom M N), f.range.FG
参数：f : L.Hom M N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Hom.range_eq_map`：range_eq_map (f : M ->[L] N) : f.r
ange = map f ⊤
· 使用定理 `FirstOrder.Language.Substructure.FG.map`：∀ {L : FirstOrder.Language} {M 
: Type u_1} [inst : L.Structure M] {N : Type u_2} [inst_1 : L.Structure N]   (f 
: L.Hom M N) {s : L.Substruct…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.Structure.fg_def`：fg_def : FG L M ↔ (⊤ : L.Substruct
ure M).FG
-/
theorem FG.range {N : Type*} [L.Structure N] (h : FG L M) (f : M →[L] N) : f.range.FG := by
  rw [Hom.range_eq_map]
  exact (fg_def.1 h).map f
/-
**FirstOrder.Language.Structure.FG.map_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.Structure.FG`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type u_1} [inst : L.Structure M] {N : Typ
e u_2} [inst_1 : L.Structure N],   FirstOrder.Language.Structure.FG L M →     ∀ 
(f : L.Hom M N), Function.Surjective ⇑f → FirstOrder.Language.Structure.FG L N
参数：f : L.Hom M N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Structure.fg_def`：fg_def : FG L M ↔ (⊤ : L.Substruct
ure M).FG
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Hom.range_eq_top`：range_eq_top {f : M ->[L] N} : ran
ge f = ⊤ ↔ Function.Surjective f
· 使用定理 `FirstOrder.Language.Structure.FG.range`：∀ {L : FirstOrder.Language} {M :
 Type u_1} [inst : L.Structure M] {N : Type u_2} [inst_1 : L.Structure N],   Fir
stOrder.Language.Structure.F…
-/
theorem FG.map_of_surjective {N : Type*} [L.Structure N] (h : FG L M) (f : M →[L] N)
    (hs : Function.Surjective f) : FG L N := by
  rw [← Hom.range_eq_top] at hs
  rw [fg_def, ← hs]
  exact h.range f
/-
**FirstOrder.Language.Structure.FG.countable_hom** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.Structure.FG`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type u_1} [inst : L.Structure M] (N : Typ
e u_2) [inst_1 : L.Structure N] [Countable N],   FirstOrder.Language.Structure.F
G L M → Countable (L.Hom M N)
参数：N : Type u_2；L.Hom M N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.Structure.fg_iff`：fg_iff : FG L M ↔ exists S : Set M
, S.Finite ∧ closure L S = (⊤ : L.Substructure M)
· 使用定理 `FirstOrder.Language.Hom.eq_of_eqOn_dense`：eq_of_eqOn_dense (hs : closure
 L s = ⊤) {f g : M ->[L] N} (h : s.EqOn f g) : f = g
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.finite_coe_iff`：finite_coe_iff {s : Set α} : Finite s ↔ s.Finite
· 使用定理 `Function.Embedding.countable`：∀ {α : Sort u} {β : Sort v} [Countable β] 
(f : α ↪ β), Countable α
· 使用定理 `instCountableForallOfFinite`：∀ {α : Sort u} {π : α → Sort w} [Finite α] 
[∀ (a : α), Countable (π a)], Countable ((a : α) → π a)
-/
theorem FG.countable_hom (N : Type*) [L.Structure N] [Countable N] (h : FG L M) :
    Countable (M →[L] N) := by
  let ⟨S, finite_S, closure_S⟩ := fg_iff.1 h
  let g : (M →[L] N) → (S → N) :=
    fun f ↦ f ∘ (↑)
  have g_inj : Function.Injective g := by
    intro f f' h
    apply Hom.eq_of_eqOn_dense closure_S
    intro x x_in_S
    exact congr_fun h ⟨x, x_in_S⟩
  have : Finite ↑S := (S.finite_coe_iff).2 finite_S
  exact Function.Embedding.countable ⟨g, g_inj⟩
/-
**FirstOrder.Language.Structure.FG.instCountable_hom** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.Structure.FG`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type u_1} [inst : L.Structure M] (N : Typ
e u_2) [inst_1 : L.Structure N] [Countable N]   [h : FirstOrder.Language.Structu
re.FG L M], Countable (L.Hom M N)
参数：N : Type u_2；L.Hom M N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Structure.FG.countable_hom`：∀ {L : FirstOrder.Langua
ge} {M : Type u_1} [inst : L.Structure M] (N : Type u_2) [inst_1 : L.Structure N
] [Countable N],   FirstOrder.Langua…
-/
instance FG.instCountable_hom (N : Type*) [L.Structure N] [Countable N] [h : FG L M] :
    Countable (M →[L] N) :=
  FG.countable_hom N h
/-
**FirstOrder.Language.Structure.FG.countable_embedding** 是 Mathlib 中的一个定理，位于命名空间
 `FirstOrder.Language.Structure.FG`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type u_1} [inst : L.Structure M] (N : Typ
e u_2) [inst_1 : L.Structure N] [Countable N],   FirstOrder.Language.Structure.F
G L M → Countable (L.Embedding M N)
参数：N : Type u_2；L.Embedding M N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Embedding.countable`：∀ {α : Sort u} {β : Sort v} [Countable β] 
(f : α ↪ β), Countable α
· 使用定理 `FirstOrder.Language.Structure.FG.instCountable_hom`：∀ {L : FirstOrder.La
nguage} {M : Type u_1} [inst : L.Structure M] (N : Type u_2) [inst_1 : L.Structu
re N] [Countable N]   [h : FirstOrder.La…
· 使用定理 `FirstOrder.Language.Embedding.toHom_injective`：toHom_injective : @Functi
on.Injective (M ↪[L] N) (M ->[L] N) (·.toHom)
-/
theorem FG.countable_embedding (N : Type*) [L.Structure N] [Countable N] (_ : FG L M) :
    Countable (M ↪[L] N) :=
  Function.Embedding.countable ⟨Embedding.toHom, Embedding.toHom_injective⟩
/-
**FirstOrder.Language.Structure.Fg.instCountable_embedding** 是 Mathlib 中的一个定理，位于
命名空间 `FirstOrder.Language.Structure.Fg`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type u_1} [inst : L.Structure M] (N : Typ
e u_2) [inst_1 : L.Structure N] [Countable N]   [h : FirstOrder.Language.Structu
re.FG L M], Countable (L.Embedding M N)
参数：N : Type u_2；L.Embedding M N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Structure.FG.countable_embedding`：∀ {L : FirstOrder.
Language} {M : Type u_1} [inst : L.Structure M] (N : Type u_2) [inst_1 : L.Struc
ture N] [Countable N],   FirstOrder.Langua…
-/
instance Fg.instCountable_embedding (N : Type*) [L.Structure N]
    [Countable N] [h : FG L M] : Countable (M ↪[L] N) :=
  FG.countable_embedding N h
/-
**FirstOrder.Language.Structure.FG.of_finite** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrd
er.Language.Structure.FG`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type u_1} [inst : L.Structure M] [Finite 
M], FirstOrder.Language.Structure.FG L M
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem FG.of_finite [Finite M] : FG L M := by
  simp only [fg_def, Substructure.FG.of_finite]
/-
**FirstOrder.Language.Structure.FG.finite** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.Structure.FG`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type u_1} [inst : L.Structure M] [L.IsRel
ational],   FirstOrder.Language.Structure.FG L M → Finite M
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_finite_univ`：∀ {α : Type u}, Set.univ.Finite → Finite α
· 使用定理 `FirstOrder.Language.Substructure.FG.finite`：∀ {L : FirstOrder.Language} 
{M : Type u_1} [inst : L.Structure M] [L.IsRelational] {S : L.Substructure M},  
 S.FG → Finite ↥S
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.Structure.fg_def`：fg_def : FG L M ↔ (⊤ : L.Substruct
ure M).FG
-/
theorem FG.finite [L.IsRelational] (h : FG L M) : Finite M :=
  Finite.of_finite_univ (Substructure.FG.finite (fg_def.1 h))
/-
**FirstOrder.Language.Structure.fg_iff_finite** 是 Mathlib 中的一个定理，位于命名空间 `FirstOr
der.Language.Structure`。
形式化陈述：fg_iff_finite [L.IsRelational] : FG L M ↔ Finite M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Structure.FG.finite`：∀ {L : FirstOrder.Language} {M 
: Type u_1} [inst : L.Structure M] [L.IsRelational],   FirstOrder.Language.Struc
ture.FG L M → Finite M
· 使用定理 `FirstOrder.Language.Structure.FG.of_finite`：∀ {L : FirstOrder.Language} 
{M : Type u_1} [inst : L.Structure M] [Finite M], FirstOrder.Language.Structure.
FG L M
-/
theorem fg_iff_finite [L.IsRelational] : FG L M ↔ Finite M :=
  ⟨FG.finite, fun _ => FG.of_finite⟩
/-
**FirstOrder.Language.Structure.cg_def** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lan
guage.Structure`。
形式化陈述：cg_def : CG L M ↔ (⊤ : L.Substructure M).CG
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Structure.CG.out`：∀ {L : FirstOrder.Language} {M : T
ype u_1} {inst : L.Structure M} [self : FirstOrder.Language.Structure.CG L M], ⊤
.CG
-/
theorem cg_def : CG L M ↔ (⊤ : L.Substructure M).CG :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

/-- An equivalent expression of `Structure.cg`. -/
/-
**FirstOrder.Language.Structure.cg_iff** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lan
guage.Structure`。
形式化陈述：cg_iff : CG L M ↔ exists S : Set M, S.Countable ∧ closure L S = (⊤ : L.Sub
structure M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Structure.cg_def`：cg_def : CG L M ↔ (⊤ : L.Substruct
ure M).CG
· 使用定理 `FirstOrder.Language.Substructure.cg_def`：cg_def {N : L.Substructure M} :
 N.CG ↔ exists S : Set M, S.Countable ∧ closure L S = N
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
An equivalent expression of `Structure.cg`.
-/
theorem cg_iff : CG L M ↔ ∃ S : Set M, S.Countable ∧ closure L S = (⊤ : L.Substructure M) := by
  rw [cg_def, Substructure.cg_def]
/-
**FirstOrder.Language.Structure.CG.range** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.L
anguage.Structure.CG`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type u_1} [inst : L.Structure M] {N : Typ
e u_2} [inst_1 : L.Structure N],   FirstOrder.Language.Structure.CG L M → ∀ (f :
 L.Hom M N), f.range.CG
参数：f : L.Hom M N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Hom.range_eq_map`：range_eq_map (f : M ->[L] N) : f.r
ange = map f ⊤
· 使用定理 `FirstOrder.Language.Substructure.CG.map`：∀ {L : FirstOrder.Language} {M 
: Type u_1} [inst : L.Structure M] {N : Type u_2} [inst_1 : L.Structure N]   (f 
: L.Hom M N) {s : L.Substruct…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.Structure.cg_def`：cg_def : CG L M ↔ (⊤ : L.Substruct
ure M).CG
-/
theorem CG.range {N : Type*} [L.Structure N] (h : CG L M) (f : M →[L] N) : f.range.CG := by
  rw [Hom.range_eq_map]
  exact (cg_def.1 h).map f
/-
**FirstOrder.Language.Structure.CG.map_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `
FirstOrder.Language.Structure.CG`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type u_1} [inst : L.Structure M] {N : Typ
e u_2} [inst_1 : L.Structure N],   FirstOrder.Language.Structure.CG L M →     ∀ 
(f : L.Hom M N), Function.Surjective ⇑f → FirstOrder.Language.Structure.CG L N
参数：f : L.Hom M N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Structure.cg_def`：cg_def : CG L M ↔ (⊤ : L.Substruct
ure M).CG
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Hom.range_eq_top`：range_eq_top {f : M ->[L] N} : ran
ge f = ⊤ ↔ Function.Surjective f
· 使用定理 `FirstOrder.Language.Structure.CG.range`：∀ {L : FirstOrder.Language} {M :
 Type u_1} [inst : L.Structure M] {N : Type u_2} [inst_1 : L.Structure N],   Fir
stOrder.Language.Structure.C…
-/
theorem CG.map_of_surjective {N : Type*} [L.Structure N] (h : CG L M) (f : M →[L] N)
    (hs : Function.Surjective f) : CG L N := by
  rw [← Hom.range_eq_top] at hs
  rw [cg_def, ← hs]
  exact h.range f
/-
**FirstOrder.Language.Structure.cg_iff_countable** 是 Mathlib 中的一个定理，位于命名空间 `Firs
tOrder.Language.Structure`。
形式化陈述：cg_iff_countable [Countable (Σ l, L.Functions l)] : CG L M ↔ Countable M
参数：Σ l, L.Functions l。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Structure.cg_def`：cg_def : CG L M ↔ (⊤ : L.Substruct
ure M).CG
· 使用定理 `FirstOrder.Language.Substructure.cg_iff_countable`：cg_iff_countable [Cou
ntable (Σ l, L.Functions l)] {s : L.Substructure M} : s.CG ↔ Countable s
· 使用定理 `Equiv.countable_iff`：Equiv.countable_iff (e : α ≃ β) : Countable α ↔ Cou
ntable β
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cg_iff_countable [Countable (Σ l, L.Functions l)] : CG L M ↔ Countable M := by
  rw [cg_def, Substructure.cg_iff_countable, topEquiv.toEquiv.countable_iff]
/-
**FirstOrder.Language.Structure.cg_of_countable** 是 Mathlib 中的一个定理，位于命名空间 `First
Order.Language.Structure`。
形式化陈述：cg_of_countable [Countable M] : CG L M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
-/
theorem cg_of_countable [Countable M] : CG L M := by
  simp only [cg_def, Substructure.cg_of_countable]
/-
**FirstOrder.Language.Structure.FG.cg** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Lang
uage.Structure.FG`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type u_1} [inst : L.Structure M],   First
Order.Language.Structure.FG L M → FirstOrder.Language.Structure.CG L M
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FirstOrder.Language.Structure.cg_def`：cg_def : CG L M ↔ (⊤ : L.Substruct
ure M).CG
· 使用定理 `FirstOrder.Language.Substructure.FG.cg`：∀ {L : FirstOrder.Language} {M :
 Type u_1} [inst : L.Structure M] {N : L.Substructure M}, N.FG → N.CG
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FirstOrder.Language.Structure.fg_def`：fg_def : FG L M ↔ (⊤ : L.Substruct
ure M).FG
-/
theorem FG.cg (h : FG L M) : CG L M :=
  cg_def.2 (fg_def.1 h).cg
/-
**FirstOrder.Language.Structure.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Language.
Structure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) cg_of_fg [h : FG L M] : CG L M :=
  h.cg

end Structure

/-
**FirstOrder.Language.Equiv.fg_iff** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Languag
e.Equiv`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type u_1} [inst : L.Structure M] {N : Typ
e u_2} [inst_1 : L.Structure N]   (f : L.Equiv M N), FirstOrder.Language.Structu
re.FG L M ↔ FirstOrder.Language.Structure.FG L N
参数：f : L.Equiv M N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Structure.FG.map_of_surjective`：∀ {L : FirstOrder.La
nguage} {M : Type u_1} [inst : L.Structure M] {N : Type u_2} [inst_1 : L.Structu
re N],   FirstOrder.Language.Structure.F…
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem Equiv.fg_iff {N : Type*} [L.Structure N] (f : M ≃[L] N) :
    Structure.FG L M ↔ Structure.FG L N :=
  ⟨fun h => h.map_of_surjective f.toHom f.toEquiv.surjective, fun h =>
    h.map_of_surjective f.symm.toHom f.toEquiv.symm.surjective⟩
/-
**FirstOrder.Language.Substructure.fg_iff_structure_fg** 是 Mathlib 中的一个定理，位于命名空间
 `FirstOrder.Language.Substructure`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type u_1} [inst : L.Structure M] (S : L.S
ubstructure M),   S.FG ↔ FirstOrder.Language.Structure.FG L ↥S
参数：S : L.Substructure M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Structure.fg_def`：fg_def : FG L M ↔ (⊤ : L.Substruct
ure M).FG
· 使用定理 `FirstOrder.Language.Substructure.FG.of_map_embedding`：∀ {L : FirstOrder.
Language} {M : Type u_1} [inst : L.Structure M] {N : Type u_2} [inst_1 : L.Struc
ture N]   (f : L.Embedding M N) {s : L.Sub…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Hom.range_eq_map`：range_eq_map (f : M ->[L] N) : f.r
ange = map f ⊤
· 使用定理 `FirstOrder.Language.Substructure.range_subtype`：range_subtype (S : L.Sub
structure M) : S.subtype.toHom.range = S
· 使用定理 `FirstOrder.Language.Substructure.FG.map`：∀ {L : FirstOrder.Language} {M 
: Type u_1} [inst : L.Structure M] {N : Type u_2} [inst_1 : L.Structure N]   (f 
: L.Hom M N) {s : L.Substruct…
-/
theorem Substructure.fg_iff_structure_fg (S : L.Substructure M) : S.FG ↔ Structure.FG L S := by
  rw [Structure.fg_def]
  refine ⟨fun h => FG.of_map_embedding S.subtype ?_, fun h => ?_⟩
  · rw [← Hom.range_eq_map, range_subtype]
    exact h
  · have h := h.map S.subtype.toHom
    rw [← Hom.range_eq_map, range_subtype] at h
    exact h
/-
**FirstOrder.Language.Equiv.cg_iff** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Languag
e.Equiv`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type u_1} [inst : L.Structure M] {N : Typ
e u_2} [inst_1 : L.Structure N]   (f : L.Equiv M N), FirstOrder.Language.Structu
re.CG L M ↔ FirstOrder.Language.Structure.CG L N
参数：f : L.Equiv M N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Structure.CG.map_of_surjective`：∀ {L : FirstOrder.La
nguage} {M : Type u_1} [inst : L.Structure M] {N : Type u_2} [inst_1 : L.Structu
re N],   FirstOrder.Language.Structure.C…
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem Equiv.cg_iff {N : Type*} [L.Structure N] (f : M ≃[L] N) :
    Structure.CG L M ↔ Structure.CG L N :=
  ⟨fun h => h.map_of_surjective f.toHom f.toEquiv.surjective, fun h =>
    h.map_of_surjective f.symm.toHom f.toEquiv.symm.surjective⟩
/-
**FirstOrder.Language.Substructure.cg_iff_structure_cg** 是 Mathlib 中的一个定理，位于命名空间
 `FirstOrder.Language.Substructure`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type u_1} [inst : L.Structure M] (S : L.S
ubstructure M),   S.CG ↔ FirstOrder.Language.Structure.CG L ↥S
参数：S : L.Substructure M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Structure.cg_def`：cg_def : CG L M ↔ (⊤ : L.Substruct
ure M).CG
· 使用定理 `FirstOrder.Language.Substructure.CG.of_map_embedding`：∀ {L : FirstOrder.
Language} {M : Type u_1} [inst : L.Structure M] {N : Type u_2} [inst_1 : L.Struc
ture N]   (f : L.Embedding M N) {s : L.Sub…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FirstOrder.Language.Hom.range_eq_map`：range_eq_map (f : M ->[L] N) : f.r
ange = map f ⊤
· 使用定理 `FirstOrder.Language.Substructure.range_subtype`：range_subtype (S : L.Sub
structure M) : S.subtype.toHom.range = S
· 使用定理 `FirstOrder.Language.Substructure.CG.map`：∀ {L : FirstOrder.Language} {M 
: Type u_1} [inst : L.Structure M] {N : Type u_2} [inst_1 : L.Structure N]   (f 
: L.Hom M N) {s : L.Substruct…
-/
theorem Substructure.cg_iff_structure_cg (S : L.Substructure M) : S.CG ↔ Structure.CG L S := by
  rw [Structure.cg_def]
  refine ⟨fun h => CG.of_map_embedding S.subtype ?_, fun h => ?_⟩
  · rw [← Hom.range_eq_map, range_subtype]
    exact h
  · have h := h.map S.subtype.toHom
    rw [← Hom.range_eq_map, range_subtype] at h
    exact h
/-
**FirstOrder.Language.Substructure.countable_fg_substructures_of_countable** 是 M
athlib 中的一个定理，位于命名空间 `FirstOrder.Language.Substructure`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type u_1} [inst : L.Structure M] [Countab
le M], Countable { S // S.FG }
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Function.Embedding.countable`：∀ {α : Sort u} {β : Sort v} [Countable β] 
(f : α ↪ β), Countable α
· 使用定理 `Finset.countable`：∀ {α : Type u_1} [Countable α], Countable (Finset α)
-/
theorem Substructure.countable_fg_substructures_of_countable [Countable M] :
    Countable { S : L.Substructure M // S.FG } := by
  let g : { S : L.Substructure M // S.FG } → Finset M :=
    fun S ↦ Exists.choose S.prop
  have g_inj : Function.Injective g := by
    intro S S' h
    apply Subtype.ext
    rw [(Exists.choose_spec S.prop).symm, (Exists.choose_spec S'.prop).symm]
    exact congr_arg (closure L ∘ SetLike.coe) h
  exact Function.Embedding.countable ⟨g, g_inj⟩
/-
**FirstOrder.Language.Substructure.instCountable_fg_substructures_of_countable**
 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Language.Substructure`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type u_1} [inst : L.Structure M] [Countab
le M], Countable { S // S.FG }
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Substructure.countable_fg_substructures_of_countable
`：∀ {L : FirstOrder.Language} {M : Type u_1} [inst : L.Structure M] [Countable M
], Countable { S // S.FG }
-/
instance Substructure.instCountable_fg_substructures_of_countable [Countable M] :
    Countable { S : L.Substructure M // S.FG } :=
  countable_fg_substructures_of_countable

end Language

end FirstOrder

