/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Sara Rousta
-/
module

public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Order.UpperLower.Basic

/-!
# The complete lattice structure on `UpperSet`/`LowerSet`

This file defines a completely distributive lattice structure on `UpperSet` and `LowerSet`,
pulled back across the canonical injection (`UpperSet.carrier`, `LowerSet.carrier`) into `Set α`.

## Notes

Upper sets are ordered by **reverse** inclusion. This convention is motivated by the fact that this
makes them order-isomorphic to lower sets and antichains, and matches the convention on `Filter`.
-/

@[expose] public section

open OrderDual Set

variable {α β γ : Type*} {ι : Sort*} {κ : ι → Sort*}

namespace UpperSet

section LE

variable [LE α]

@[to_dual]
/-
**UpperSet.** 是 Mathlib 中的一个实例，位于命名空间 `UpperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (UpperSet α) α where
  coe := UpperSet.carrier
  coe_injective s t h := by cases s; cases t; congr

/-- See Note [custom simps projection]. -/
@[to_dual /-- See Note [custom simps projection]. -/]
/-
**UpperSet.Simps.coe** 是 Mathlib 中的一个定义，位于命名空间 `UpperSet.Simps`。
形式化陈述：{α : Type u_1} → [inst : LE α] → UpperSet α → Set α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection].
-/
def Simps.coe (s : UpperSet α) : Set α := s

initialize_simps_projections UpperSet (carrier → coe, as_prefix coe)
initialize_simps_projections LowerSet (carrier → coe, as_prefix coe)

@[to_dual (attr := ext)]
/-
**UpperSet.ext** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：ext {s t : UpperSet α} : (s : Set α) = t -> s = t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
-/
theorem ext {s t : UpperSet α} : (s : Set α) = t → s = t :=
  SetLike.ext'

@[to_dual (attr := simp)]
/-
**UpperSet.carrier_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：carrier_eq_coe (s : UpperSet α) : s.carrier = s
参数：s : UpperSet α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem carrier_eq_coe (s : UpperSet α) : s.carrier = s :=
  rfl

@[to_dual (attr := simp)]
/-
**UpperSet.upper** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] (s : UpperSet α), IsUpperSet ↑s
参数：s : UpperSet α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperSet.upper'`：∀ {α : Type u_1} [inst : LE α] (self : UpperSet α), IsU
pperSet self.carrier
-/
protected lemma upper (s : UpperSet α) : IsUpperSet (s : Set α) := s.upper'

@[to_dual (attr := simp, norm_cast)]
/-
**UpperSet.coe_mk** 是 Mathlib 中的一个引理，位于命名空间 `UpperSet`。
形式化陈述：coe_mk (s : Set α) (hs) : mk s hs = s
参数：s : Set α；hs。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_mk (s : Set α) (hs) : mk s hs = s := rfl

@[to_dual (attr := simp)]
/-
**UpperSet.mem_mk** 是 Mathlib 中的一个引理，位于命名空间 `UpperSet`。
形式化陈述：mem_mk {s : Set α} (hs) {a : α} : a in mk s hs ↔ a in s
参数：hs。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_mk {s : Set α} (hs) {a : α} : a ∈ mk s hs ↔ a ∈ s := Iff.rfl

variable {S : Set (UpperSet α)} {s t : UpperSet α} {a : α}

@[to_dual]
/-
**UpperSet.** 是 Mathlib 中的一个实例，位于命名空间 `UpperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Max (UpperSet α) :=
  ⟨fun s t => ⟨s ∩ t, s.upper.inter t.upper⟩⟩

@[to_dual]
/-
**UpperSet.** 是 Mathlib 中的一个实例，位于命名空间 `UpperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Min (UpperSet α) :=
  ⟨fun s t => ⟨s ∪ t, s.upper.union t.upper⟩⟩

@[to_dual]
/-
**UpperSet.** 是 Mathlib 中的一个实例，位于命名空间 `UpperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Top (UpperSet α) :=
  ⟨⟨∅, isUpperSet_empty⟩⟩

@[to_dual]
/-
**UpperSet.** 是 Mathlib 中的一个实例，位于命名空间 `UpperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bot (UpperSet α) :=
  ⟨⟨univ, isUpperSet_univ⟩⟩

@[to_dual]
/-
**UpperSet.** 是 Mathlib 中的一个实例，位于命名空间 `UpperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SupSet (UpperSet α) :=
  ⟨fun S => ⟨⋂ s ∈ S, ↑s, isUpperSet_iInter₂ fun s _ => s.upper⟩⟩

@[to_dual]
/-
**UpperSet.** 是 Mathlib 中的一个实例，位于命名空间 `UpperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InfSet (UpperSet α) :=
  ⟨fun S => ⟨⋃ s ∈ S, ↑s, isUpperSet_iUnion₂ fun s _ => s.upper⟩⟩
/-
**UpperSet.** 是 Mathlib 中的一个实例，位于命名空间 `UpperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (UpperSet α) :=
  PartialOrder.lift _ (toDual.injective.comp SetLike.coe_injective)
/-
**UpperSet.completeLattice** 是 Mathlib 中的一个实例，位于命名空间 `UpperSet`。
形式化陈述：completeLattice : CompleteLattice (UpperSet α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance completeLattice : CompleteLattice (UpperSet α) :=
  (toDual.injective.comp SetLike.coe_injective).completeLattice _
    .rfl .rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) rfl rfl
/-
**UpperSet.completelyDistribLattice** 是 Mathlib 中的一个实例，位于命名空间 `UpperSet`。
形式化陈述：completelyDistribLattice : CompletelyDistribLattice (UpperSet α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance completelyDistribLattice : CompletelyDistribLattice (UpperSet α) :=
  .ofMinimalAxioms <|
    (toDual.injective.comp SetLike.coe_injective).completelyDistribLatticeMinimalAxioms .of _
      (fun _ ↦ rfl) (fun _ ↦ rfl)

@[to_dual existing]
/-
**UpperSet._root_.LowerSet.instPartialOrder** 是 Mathlib 中的一个实例，位于命名空间 `UpperSet`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.LowerSet.instPartialOrder : PartialOrder (LowerSet α) :=
  PartialOrder.lift _ SetLike.coe_injective

@[to_dual existing]
/-
**UpperSet._root_.LowerSet.completeLattice** 是 Mathlib 中的一个实例，位于命名空间 `UpperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.LowerSet.completeLattice : CompleteLattice (LowerSet α) :=
  SetLike.coe_injective.completeLattice _
    .rfl .rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) rfl rfl

@[to_dual existing]
/-
**UpperSet._root_.LowerSet.completelyDistribLattice** 是 Mathlib 中的一个实例，位于命名空间 `U
pperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.LowerSet.completelyDistribLattice : CompletelyDistribLattice (LowerSet α) :=
  .ofMinimalAxioms <| SetLike.coe_injective.completelyDistribLatticeMinimalAxioms .of _
    (fun _ ↦ rfl) (fun _ ↦ rfl)

@[to_dual]
/-
**UpperSet.** 是 Mathlib 中的一个实例，位于命名空间 `UpperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (UpperSet α) :=
  ⟨⊥⟩

@[to_dual (attr := simp 1100, norm_cast)]
/-
**UpperSet.coe_subset_coe** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：coe_subset_coe : (s : Set α) subseteq t ↔ t <= s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_subset_coe : (s : Set α) ⊆ t ↔ t ≤ s :=
  Iff.rfl

@[to_dual (attr := simp 1100, norm_cast)]
/-
**UpperSet.coe_ssubset_coe** 是 Mathlib 中的一个引理，位于命名空间 `UpperSet`。
形式化陈述：coe_ssubset_coe : (s : Set α) ⊂ t ↔ t < s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma coe_ssubset_coe : (s : Set α) ⊂ t ↔ t < s := Iff.rfl

@[to_dual (attr := simp, norm_cast)]
/-
**UpperSet.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：coe_top : ((⊤ : UpperSet α) : Set α) = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_top : ((⊤ : UpperSet α) : Set α) = ∅ :=
  rfl

@[to_dual (attr := simp, norm_cast)]
/-
**UpperSet.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：coe_bot : ((⊥ : UpperSet α) : Set α) = univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_bot : ((⊥ : UpperSet α) : Set α) = univ :=
  rfl

@[to_dual (attr := simp, norm_cast)]
/-
**UpperSet.coe_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：coe_eq_univ : (s : Set α) = univ ↔ s = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coe_eq_univ : (s : Set α) = univ ↔ s = ⊥ := by simp [SetLike.ext'_iff]

@[to_dual (attr := simp, norm_cast)]
/-
**UpperSet.coe_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：coe_eq_empty : (s : Set α) = ∅ ↔ s = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coe_eq_empty : (s : Set α) = ∅ ↔ s = ⊤ := by simp [SetLike.ext'_iff]

@[to_dual (attr := simp, norm_cast)]
/-
**UpperSet.coe_nonempty** 是 Mathlib 中的一个引理，位于命名空间 `UpperSet`。
形式化陈述：coe_nonempty : (s : Set α).Nonempty ↔ s != ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `UpperSet.coe_eq_empty`：coe_eq_empty : (s : Set α) = ∅ ↔ s = ⊤
-/
lemma coe_nonempty : (s : Set α).Nonempty ↔ s ≠ ⊤ :=
  nonempty_iff_ne_empty.trans coe_eq_empty.not

@[to_dual (attr := simp, norm_cast)]
/-
**UpperSet.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：coe_sup (s t : UpperSet α) : (↑(s ⊔ t) : Set α) = (s : Set α) inter t
参数：s t : UpperSet α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sup (s t : UpperSet α) : (↑(s ⊔ t) : Set α) = (s : Set α) ∩ t :=
  rfl

@[to_dual (attr := simp, norm_cast)]
/-
**UpperSet.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：coe_inf (s t : UpperSet α) : (↑(s ⊓ t) : Set α) = (s : Set α) union t
参数：s t : UpperSet α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inf (s t : UpperSet α) : (↑(s ⊓ t) : Set α) = (s : Set α) ∪ t :=
  rfl

@[to_dual (attr := simp, norm_cast)]
/-
**UpperSet.coe_sSup** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：coe_sSup (S : Set (UpperSet α)) : (↑(sSup S) : Set α) = ⋂ s in S, ↑s
参数：S : Set (UpperSet α)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sSup (S : Set (UpperSet α)) : (↑(sSup S) : Set α) = ⋂ s ∈ S, ↑s :=
  rfl

@[to_dual (attr := simp, norm_cast)]
/-
**UpperSet.coe_sInf** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：coe_sInf (S : Set (UpperSet α)) : (↑(sInf S) : Set α) = ⋃ s in S, ↑s
参数：S : Set (UpperSet α)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sInf (S : Set (UpperSet α)) : (↑(sInf S) : Set α) = ⋃ s ∈ S, ↑s :=
  rfl

@[to_dual (attr := simp, norm_cast)]
/-
**UpperSet.coe_iSup** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：coe_iSup (f : ι -> UpperSet α) : (↑(⨆ i, f i) : Set α) = ⋂ i, f i
参数：f : ι -> UpperSet α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
theorem coe_iSup (f : ι → UpperSet α) : (↑(⨆ i, f i) : Set α) = ⋂ i, f i := by simp [iSup]

@[to_dual (attr := simp, norm_cast)]
/-
**UpperSet.coe_iInf** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：coe_iInf (f : ι -> UpperSet α) : (↑(⨅ i, f i) : Set α) = ⋃ i, f i
参数：f : ι -> UpperSet α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_exists`：iUnion_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋃ x, f x = ⋃ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.iUnion_iUnion_eq'`：iUnion_iUnion_eq' {f : ι -> α} {g : α -> Set β} :
 ⋃ (x) (y) (_ : f y = x), g x = ⋃ y, g (f y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_iInf (f : ι → UpperSet α) : (↑(⨅ i, f i) : Set α) = ⋃ i, f i := by simp [iInf]

@[to_dual (attr := norm_cast)]
/-
**UpperSet.coe_iSup** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：coe_iSup (f : ι -> UpperSet α) : (↑(⨆ i, f i) : Set α) = ⋂ i, f i
参数：f : ι -> UpperSet α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
theorem coe_iSup₂ (f : ∀ i, κ i → UpperSet α) :
    (↑(⨆ (i) (j), f i j) : Set α) = ⋂ (i) (j), f i j := by simp

@[to_dual (attr := norm_cast)]
/-
**UpperSet.coe_iInf** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：coe_iInf (f : ι -> UpperSet α) : (↑(⨅ i, f i) : Set α) = ⋃ i, f i
参数：f : ι -> UpperSet α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_exists`：iUnion_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋃ x, f x = ⋃ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.iUnion_iUnion_eq'`：iUnion_iUnion_eq' {f : ι -> α} {g : α -> Set β} :
 ⋃ (x) (y) (_ : f y = x), g x = ⋃ y, g (f y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_iInf₂ (f : ∀ i, κ i → UpperSet α) :
    (↑(⨅ (i) (j), f i j) : Set α) = ⋃ (i) (j), f i j := by simp

@[to_dual (attr := simp)]
/-
**UpperSet.notMem_top** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：notMem_top : a ∉ (⊤ : UpperSet α)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem notMem_top : a ∉ (⊤ : UpperSet α) :=
  id

@[to_dual (attr := simp)]
/-
**UpperSet.mem_bot** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：mem_bot : a in (⊥ : UpperSet α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
theorem mem_bot : a ∈ (⊥ : UpperSet α) :=
  trivial

@[to_dual (attr := simp)]
/-
**UpperSet.mem_sup_iff** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：mem_sup_iff : a in s ⊔ t ↔ a in s ∧ a in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_sup_iff : a ∈ s ⊔ t ↔ a ∈ s ∧ a ∈ t :=
  Iff.rfl

@[to_dual (attr := simp)]
/-
**UpperSet.mem_inf_iff** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：mem_inf_iff : a in s ⊓ t ↔ a in s ∨ a in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_inf_iff : a ∈ s ⊓ t ↔ a ∈ s ∨ a ∈ t :=
  Iff.rfl

@[to_dual (attr := simp)]
/-
**UpperSet.mem_sSup_iff** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：mem_sSup_iff : a in sSup S ↔ forall s in S, a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_iInter₂`：mem_iInter₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋂ (i) (j), s i j) ↔ forall i j, x in s i j
-/
theorem mem_sSup_iff : a ∈ sSup S ↔ ∀ s ∈ S, a ∈ s :=
  mem_iInter₂

@[to_dual (attr := simp)]
/-
**UpperSet.mem_sInf_iff** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：mem_sInf_iff : a in sInf S ↔ exists s in S, a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_sInf_iff : a ∈ sInf S ↔ ∃ s ∈ S, a ∈ s :=
  mem_iUnion₂.trans <| by simp only [exists_prop, SetLike.mem_coe]

@[to_dual (attr := simp)]
/-
**UpperSet.mem_iSup_iff** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：mem_iSup_iff {f : ι -> UpperSet α} : (a in ⨆ i, f i) ↔ forall i, a in f i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `UpperSet.coe_iSup`：coe_iSup (f : ι -> UpperSet α) : (↑(⨆ i, f i) : Set α
) = ⋂ i, f i
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
-/
theorem mem_iSup_iff {f : ι → UpperSet α} : (a ∈ ⨆ i, f i) ↔ ∀ i, a ∈ f i := by
  rw [← SetLike.mem_coe, coe_iSup]
  exact mem_iInter

@[to_dual (attr := simp)]
/-
**UpperSet.mem_iInf_iff** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：mem_iInf_iff {f : ι -> UpperSet α} : (a in ⨅ i, f i) ↔ exists i, a in f i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `UpperSet.coe_iInf`：coe_iInf (f : ι -> UpperSet α) : (↑(⨅ i, f i) : Set α
) = ⋃ i, f i
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
-/
theorem mem_iInf_iff {f : ι → UpperSet α} : (a ∈ ⨅ i, f i) ↔ ∃ i, a ∈ f i := by
  rw [← SetLike.mem_coe, coe_iInf]
  exact mem_iUnion

@[to_dual]
/-
**UpperSet.mem_iSup** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_iSup₂_iff {f : ∀ i, κ i → UpperSet α} : (a ∈ ⨆ (i) (j), f i j) ↔ ∀ i j, a ∈ f i j := by
  simp

@[to_dual]
/-
**UpperSet.mem_iInf** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_iInf₂_iff {f : ∀ i, κ i → UpperSet α} : (a ∈ ⨅ (i) (j), f i j) ↔ ∃ i j, a ∈ f i j := by
  simp

@[to_dual (attr := simp, norm_cast)]
/-
**UpperSet.codisjoint_coe** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：codisjoint_coe : Codisjoint (s : Set α) t ↔ Disjoint s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem codisjoint_coe : Codisjoint (s : Set α) t ↔ Disjoint s t := by
  simp [disjoint_iff, codisjoint_iff, SetLike.ext'_iff]

/-! ### Complement -/

/-- The complement of an upper set as a lower set. -/
@[to_dual /-- The complement of a lower set as an upper set. -/]
/-
**UpperSet.compl** 是 Mathlib 中的一个定义，位于命名空间 `UpperSet`。
形式化陈述：compl (s : UpperSet α) : LowerSet α
参数：s : UpperSet α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The complement of an upper set as a lower set.
-/
def compl (s : UpperSet α) : LowerSet α :=
  ⟨sᶜ, s.upper.compl⟩

@[to_dual (attr := simp)]
/-
**UpperSet.coe_compl** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：coe_compl (s : UpperSet α) : (s.compl : Set α) = (↑s)ᶜ
参数：s : UpperSet α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_compl (s : UpperSet α) : (s.compl : Set α) = (↑s)ᶜ :=
  rfl

@[to_dual (attr := simp)]
/-
**UpperSet.mem_compl_iff** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：mem_compl_iff : a in s.compl ↔ a ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_compl_iff : a ∈ s.compl ↔ a ∉ s :=
  Iff.rfl

@[to_dual (attr := simp)]
nonrec theorem compl_compl (s : UpperSet α) : s.compl.compl = s :=
  UpperSet.ext <| compl_compl _

@[to_dual (attr := simp)]
/-
**UpperSet.compl_le_compl** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：compl_le_compl : s.compl <= t.compl ↔ s <= t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s
-/
theorem compl_le_compl : s.compl ≤ t.compl ↔ s ≤ t :=
  compl_subset_compl

@[to_dual (attr := simp)]
/-
**UpperSet.compl_sup** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] (s t : UpperSet α), (s ⊔ t).compl = s.compl
 ⊔ t.compl
参数：s t : UpperSet α；s ⊔ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSet.ext`：∀ {α : Type u_1} [inst : LE α] {s t : LowerSet α}, ↑s = ↑t
 → s = t
· 使用定理 `compl_inf`：compl_inf : (x ⊓ y)ᶜ = xᶜ ⊔ yᶜ
-/
protected theorem compl_sup (s t : UpperSet α) : (s ⊔ t).compl = s.compl ⊔ t.compl :=
  LowerSet.ext compl_inf

@[to_dual (attr := simp)]
/-
**UpperSet.compl_inf** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] (s t : UpperSet α), (s ⊓ t).compl = s.compl
 ⊓ t.compl
参数：s t : UpperSet α；s ⊓ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSet.ext`：∀ {α : Type u_1} [inst : LE α] {s t : LowerSet α}, ↑s = ↑t
 → s = t
· 使用定理 `compl_sup`：compl_sup : (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ
-/
protected theorem compl_inf (s t : UpperSet α) : (s ⊓ t).compl = s.compl ⊓ t.compl :=
  LowerSet.ext compl_sup

@[to_dual (attr := simp)]
/-
**UpperSet.compl_top** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：∀ {α : Type u_1} [inst : LE α], ⊤.compl = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSet.ext`：∀ {α : Type u_1} [inst : LE α] {s t : LowerSet α}, ↑s = ↑t
 → s = t
· 使用定理 `Set.compl_empty`：compl_empty : (∅ : Set α)ᶜ = univ
-/
protected theorem compl_top : (⊤ : UpperSet α).compl = ⊤ :=
  LowerSet.ext compl_empty

@[to_dual (attr := simp)]
/-
**UpperSet.compl_bot** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：∀ {α : Type u_1} [inst : LE α], ⊥.compl = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSet.ext`：∀ {α : Type u_1} [inst : LE α] {s t : LowerSet α}, ↑s = ↑t
 → s = t
· 使用定理 `Set.compl_univ`：compl_univ : (univ : Set α)ᶜ = ∅
-/
protected theorem compl_bot : (⊥ : UpperSet α).compl = ⊥ :=
  LowerSet.ext compl_univ

@[to_dual (attr := simp)]
/-
**UpperSet.compl_sSup** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] (S : Set (UpperSet α)), (sSup S).compl = ⨆ 
s ∈ S, s.compl
参数：S : Set (UpperSet α)；sSup S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSet.ext`：∀ {α : Type u_1} [inst : LE α] {s t : LowerSet α}, ↑s = ↑t
 → s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_iInter₂`：compl_iInter₂ (s : forall i, κ i -> Set α) : (⋂ (i) (
j), s i j)ᶜ = ⋃ (i) (j), (s i j)ᶜ
· 使用定理 `LowerSet.coe_iSup₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_5} [
inst : LE α] (f : (i : ι) → κ i → LowerSet α),   ↑(⨆ i, ⨆ j, f i j) = ⋃ i, ⋃ j, 
↑(f i j)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem compl_sSup (S : Set (UpperSet α)) : (sSup S).compl = ⨆ s ∈ S, UpperSet.compl s :=
  LowerSet.ext <| by simp only [coe_compl, coe_sSup, compl_iInter₂, LowerSet.coe_iSup₂]

@[to_dual (attr := simp)]
/-
**UpperSet.compl_sInf** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] (S : Set (UpperSet α)), (sInf S).compl = ⨅ 
s ∈ S, s.compl
参数：S : Set (UpperSet α)；sInf S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSet.ext`：∀ {α : Type u_1} [inst : LE α] {s t : LowerSet α}, ↑s = ↑t
 → s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_iUnion₂`：compl_iUnion₂ (s : forall i, κ i -> Set α) : (⋃ (i) (
j), s i j)ᶜ = ⋂ (i) (j), (s i j)ᶜ
· 使用定理 `LowerSet.coe_iInf₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_5} [
inst : LE α] (f : (i : ι) → κ i → LowerSet α),   ↑(⨅ i, ⨅ j, f i j) = ⋂ i, ⋂ j, 
↑(f i j)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem compl_sInf (S : Set (UpperSet α)) : (sInf S).compl = ⨅ s ∈ S, UpperSet.compl s :=
  LowerSet.ext <| by simp only [coe_compl, coe_sInf, compl_iUnion₂, LowerSet.coe_iInf₂]

@[to_dual (attr := simp)]
/-
**UpperSet.compl_iSup** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} [inst : LE α] (f : ι → UpperSet α), (⨆ i, 
f i).compl = ⨆ i, (f i).compl
参数：f : ι → UpperSet α；⨆ i, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSet.ext`：∀ {α : Type u_1} [inst : LE α] {s t : LowerSet α}, ↑s = ↑t
 → s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UpperSet.coe_iSup`：coe_iSup (f : ι -> UpperSet α) : (↑(⨆ i, f i) : Set α
) = ⋂ i, f i
· 使用定理 `Set.compl_iInter`：compl_iInter (s : ι -> Set β) : (⋂ i, s i)ᶜ = ⋃ i, (s 
i)ᶜ
· 使用定理 `LowerSet.coe_iSup`：∀ {α : Type u_1} {ι : Sort u_4} [inst : LE α] (f : ι 
→ LowerSet α), ↑(⨆ i, f i) = ⋃ i, ↑(f i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem compl_iSup (f : ι → UpperSet α) : (⨆ i, f i).compl = ⨆ i, (f i).compl :=
  LowerSet.ext <| by simp only [coe_compl, coe_iSup, compl_iInter, LowerSet.coe_iSup]

@[to_dual (attr := simp)]
/-
**UpperSet.compl_iInf** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} [inst : LE α] (f : ι → UpperSet α), (⨅ i, 
f i).compl = ⨅ i, (f i).compl
参数：f : ι → UpperSet α；⨅ i, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSet.ext`：∀ {α : Type u_1} [inst : LE α] {s t : LowerSet α}, ↑s = ↑t
 → s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UpperSet.coe_iInf`：coe_iInf (f : ι -> UpperSet α) : (↑(⨅ i, f i) : Set α
) = ⋃ i, f i
· 使用定理 `Set.compl_iUnion`：compl_iUnion (s : ι -> Set β) : (⋃ i, s i)ᶜ = ⋂ i, (s 
i)ᶜ
· 使用定理 `LowerSet.coe_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : LE α] (f : ι 
→ LowerSet α), ↑(⨅ i, f i) = ⋂ i, ↑(f i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem compl_iInf (f : ι → UpperSet α) : (⨅ i, f i).compl = ⨅ i, (f i).compl :=
  LowerSet.ext <| by simp only [coe_compl, coe_iInf, compl_iUnion, LowerSet.coe_iInf]

@[to_dual]
/-
**UpperSet.compl_iSup** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} [inst : LE α] (f : ι → UpperSet α), (⨆ i, 
f i).compl = ⨆ i, (f i).compl
参数：f : ι → UpperSet α；⨆ i, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSet.ext`：∀ {α : Type u_1} [inst : LE α] {s t : LowerSet α}, ↑s = ↑t
 → s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UpperSet.coe_iSup`：coe_iSup (f : ι -> UpperSet α) : (↑(⨆ i, f i) : Set α
) = ⋂ i, f i
· 使用定理 `Set.compl_iInter`：compl_iInter (s : ι -> Set β) : (⋂ i, s i)ᶜ = ⋃ i, (s 
i)ᶜ
· 使用定理 `LowerSet.coe_iSup`：∀ {α : Type u_1} {ι : Sort u_4} [inst : LE α] (f : ι 
→ LowerSet α), ↑(⨆ i, f i) = ⋃ i, ↑(f i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem compl_iSup₂ (f : ∀ i, κ i → UpperSet α) :
    (⨆ (i) (j), f i j).compl = ⨆ (i) (j), (f i j).compl := by simp

@[to_dual]
/-
**UpperSet.compl_iInf** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} [inst : LE α] (f : ι → UpperSet α), (⨅ i, 
f i).compl = ⨅ i, (f i).compl
参数：f : ι → UpperSet α；⨅ i, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSet.ext`：∀ {α : Type u_1} [inst : LE α] {s t : LowerSet α}, ↑s = ↑t
 → s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UpperSet.coe_iInf`：coe_iInf (f : ι -> UpperSet α) : (↑(⨅ i, f i) : Set α
) = ⋃ i, f i
· 使用定理 `Set.compl_iUnion`：compl_iUnion (s : ι -> Set β) : (⋃ i, s i)ᶜ = ⋂ i, (s 
i)ᶜ
· 使用定理 `LowerSet.coe_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : LE α] (f : ι 
→ LowerSet α), ↑(⨅ i, f i) = ⋂ i, ↑(f i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem compl_iInf₂ (f : ∀ i, κ i → UpperSet α) :
    (⨅ (i) (j), f i j).compl = ⨅ (i) (j), (f i j).compl := by simp

/-- Upper sets are order-isomorphic to lower sets under complementation. -/
@[simps]
/-
**UpperSet._root_.upperSetIsoLowerSet** 是 Mathlib 中的一个定义，位于命名空间 `UpperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Upper sets are order-isomorphic to lower sets under complementation.
-/
def _root_.upperSetIsoLowerSet : UpperSet α ≃o LowerSet α where
  toFun := UpperSet.compl
  invFun := LowerSet.compl
  left_inv := UpperSet.compl_compl
  right_inv := LowerSet.compl_compl
  map_rel_iff' := UpperSet.compl_le_compl

end LE

section LinearOrder
variable [LinearOrder α]

@[to_dual none]
/-
**UpperSet.total_le** 是 Mathlib 中的一个实例，位于命名空间 `UpperSet`。
形式化陈述：total_le : @Std.Total (UpperSet α) (· <= ·)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUpperSet.total`：IsUpperSet.total (hs : IsUpperSet s) (ht : IsUpperSet 
t) : s subseteq t ∨ t subseteq s
· 使用定理 `UpperSet.upper`：∀ {α : Type u_1} [inst : LE α] (s : UpperSet α), IsUpper
Set ↑s
-/
instance total_le : @Std.Total (UpperSet α) (· ≤ ·) := ⟨fun s t => t.upper.total s.upper⟩
/-
**UpperSet.instLinearOrder** 是 Mathlib 中的一个实例，位于命名空间 `UpperSet`。
形式化陈述：instLinearOrder : LinearOrder (UpperSet α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance instLinearOrder : LinearOrder (UpperSet α) := by
  classical exact Lattice.toLinearOrder _
/-
**UpperSet.instCompleteLinearOrder** 是 Mathlib 中的一个实例，位于命名空间 `UpperSet`。
形式化陈述：instCompleteLinearOrder : CompleteLinearOrder (UpperSet α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance instCompleteLinearOrder : CompleteLinearOrder (UpperSet α) :=
  { completelyDistribLattice, instLinearOrder with }

@[to_dual none]
/-
**UpperSet._root_.LowerSet.total_le** 是 Mathlib 中的一个实例，位于命名空间 `UpperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.LowerSet.total_le : @Std.Total (LowerSet α) (· ≤ ·) :=
  ⟨fun s t => s.lower.total t.lower⟩

@[to_dual existing]
/-
**UpperSet._root_.LowerSet.instLinearOrder** 是 Mathlib 中的一个实例，位于命名空间 `UpperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance _root_.LowerSet.instLinearOrder : LinearOrder (LowerSet α) := by
  classical exact Lattice.toLinearOrder _

@[to_dual existing]
/-
**UpperSet._root_.LowerSet.instCompleteLinearOrder** 是 Mathlib 中的一个实例，位于命名空间 `Up
perSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance _root_.LowerSet.instCompleteLinearOrder : CompleteLinearOrder (LowerSet α) :=
  { LowerSet.completelyDistribLattice, LowerSet.instLinearOrder with }

end LinearOrder

section Map

variable [Preorder α] [Preorder β] [Preorder γ]

variable {f : α ≃o β} {s t : UpperSet α} {a : α} {b : β}

/-- An order isomorphism of Preorders induces an order isomorphism of their upper sets. -/
@[to_dual
/-- An order isomorphism of Preorders induces an order isomorphism of their lower sets. -/]
/-
**UpperSet.map** 是 Mathlib 中的一个定义，位于命名空间 `UpperSet`。
形式化陈述：map (f : α ≃o β) : UpperSet α ≃o UpperSet β where toFun s
参数：f : α ≃o β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def map (f : α ≃o β) : UpperSet α ≃o UpperSet β where
  toFun s := ⟨f '' s, s.upper.image f⟩
  invFun t := ⟨f ⁻¹' t, t.upper.preimage f.monotone⟩
  left_inv _ := ext <| f.preimage_image _
  right_inv _ := ext <| f.image_preimage _
  map_rel_iff' := image_subset_image_iff f.injective

-- `simps` could generate these theorems, but `to_dual` is not happy with those versions.
@[to_dual (attr := simp)]
/-
**UpperSet.coe_map_apply** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：coe_map_apply (f : α ≃o β) (s : UpperSet α) : map f s = f '' s
参数：f : α ≃o β；s : UpperSet α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_map_apply (f : α ≃o β) (s : UpperSet α) : map f s = f '' s := rfl
@[to_dual (attr := simp)]
/-
**UpperSet.coe_map_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：coe_map_symm_apply (f : α ≃o β) (s : UpperSet β) : (map f).symm s = f ⁻¹' 
s
参数：f : α ≃o β；s : UpperSet β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_map_symm_apply (f : α ≃o β) (s : UpperSet β) : (map f).symm s = f ⁻¹' s := rfl

set_option backward.isDefEq.respectTransparency false in
@[to_dual (attr := simp)]
/-
**UpperSet.symm_map** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：symm_map (f : α ≃o β) : (map f).symm = map f.symm
参数：f : α ≃o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.ext`：ext {f g : α ≃o β} (h : (f : α -> β) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `UpperSet.ext`：ext {s t : UpperSet α} : (s : Set α) = t -> s = t
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem symm_map (f : α ≃o β) : (map f).symm = map f.symm := by
  ext; simp [map, OrderIso.symm_apply_eq]

@[to_dual (attr := simp)]
/-
**UpperSet.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：mem_map : b in map f s ↔ f.symm b in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.symm_symm`：symm_symm (e : α ≃o β) : e.symm.symm = e
· 使用定理 `UpperSet.symm_map`：symm_map (f : α ≃o β) : (map f).symm = map f.symm
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_map : b ∈ map f s ↔ f.symm b ∈ s := by
  rw [← f.symm_symm, ← symm_map, f.symm_symm]
  rfl

@[to_dual (attr := simp)]
/-
**UpperSet.map_refl** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：map_refl : map (OrderIso.refl α) = OrderIso.refl _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.ext`：ext {f g : α ≃o β} (h : (f : α -> β) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `UpperSet.ext`：ext {s t : UpperSet α} : (s : Set α) = t -> s = t
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Set.image_id_eq`：image_id_eq : image (id : α -> α) = id
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_refl : map (OrderIso.refl α) = OrderIso.refl _ := by
  ext
  simp

@[to_dual (attr := simp)]
/-
**UpperSet.map_map** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：map_map (g : β ≃o γ) (f : α ≃o β) : map g (map f s) = map (f.trans g) s
参数：g : β ≃o γ；f : α ≃o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperSet.ext`：ext {s t : UpperSet α} : (s : Set α) = t -> s = t
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
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
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_map (g : β ≃o γ) (f : α ≃o β) : map g (map f s) = map (f.trans g) s := by
  ext
  simp

variable (f s t)

@[to_dual (attr := norm_cast)]
/-
**UpperSet.coe_map** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：coe_map : (map f s : Set β) = f '' s
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_map : (map f s : Set β) = f '' s :=
  rfl

@[to_dual (attr := simp)]
/-
**UpperSet.compl_map** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：compl_map : (map f s).compl = LowerSet.map f s.compl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_compl_eq`：image_compl_eq {f : α -> β} {s : Set α} (H : Bijecti
ve f) : f '' sᶜ = (f '' s)ᶜ
· 使用定理 `OrderIso.bijective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_
1 : LE β] (e : α ≃o β), Function.Bijective ⇑e
-/
theorem compl_map : (map f s).compl = LowerSet.map f s.compl :=
  SetLike.coe_injective (Set.image_compl_eq f.bijective).symm


end Map

end UpperSet

