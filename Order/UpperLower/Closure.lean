/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Sara Rousta
-/
module

public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Order.Minimal
public import Mathlib.Order.UpperLower.Principal

/-!
# Upper and lower closures

Upper (lower) closures generalise principal upper (lower) sets to arbitrary included sets. Indeed,
they are equivalent to a union over principal upper (lower) sets, as shown in `coe_upperClosure`
(`coe_lowerClosure`).

## Main declarations

* `upperClosure`: The greatest upper set containing a set.
* `lowerClosure`: The least lower set containing a set.
-/

@[expose] public section

open OrderDual Set

variable {α β : Type*} {ι : Sort*}

section Preorder
variable [Preorder α] [Preorder β] {s t : Set α} {x : α}

/-- The greatest upper set containing a given set. -/
@[to_dual /-- The least lower set containing a given set. -/]
/-
**upperClosure** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：upperClosure (s : Set α) : UpperSet α
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The greatest upper set containing a given set.
-/
def upperClosure (s : Set α) : UpperSet α :=
  ⟨{ x | ∃ a ∈ s, a ≤ x }, fun _ _ hle h => h.imp fun _x hx => ⟨hx.1, hx.2.trans hle⟩⟩

@[to_dual (attr := simp)]
/-
**mem_upperClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_upperClosure : x in upperClosure s ↔ exists a in s, a <= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_upperClosure : x ∈ upperClosure s ↔ ∃ a ∈ s, a ≤ x :=
  Iff.rfl

-- We do not tag this as `simp` to respect the abstraction.
@[to_dual (attr := norm_cast)]
/-
**coe_upperClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_upperClosure (s : Set α) : ↑(upperClosure s) = ⋃ a in s, Ici a
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
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
theorem coe_upperClosure (s : Set α) : ↑(upperClosure s) = ⋃ a ∈ s, Ici a := by
  ext
  simp

@[to_dual]
/-
**instDecidablePredMemUpperClosure** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instDecidablePredMemUpperClosure [DecidablePred (exists a in s, a <= ·)] :
 DecidablePred (· in upperClosure s)
参数：exists a in s, a <= ·。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDecidablePredMemUpperClosure [DecidablePred (∃ a ∈ s, a ≤ ·)] :
    DecidablePred (· ∈ upperClosure s) := ‹DecidablePred _›

@[to_dual]
/-
**subset_upperClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_upperClosure : s subseteq upperClosure s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem subset_upperClosure : s ⊆ upperClosure s := fun x hx => ⟨x, hx, le_rfl⟩

@[to_dual lowerClosure_min]
/-
**upperClosure_min** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperClosure_min (h : s subseteq t) (ht : IsUpperSet t) : ↑(upperClosure s
) subseteq t
参数：h : s subseteq t；ht : IsUpperSet t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem upperClosure_min (h : s ⊆ t) (ht : IsUpperSet t) : ↑(upperClosure s) ⊆ t :=
  fun _a ⟨_b, hb, hba⟩ => ht hba <| h hb

@[to_dual]
/-
**IsUpperSet.upperClosure** 是 Mathlib 中的一个定理，位于命名空间 `IsUpperSet`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, IsUpperSet s → ↑(upperCl
osure s) = s
参数：upperClosure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `upperClosure_min`：upperClosure_min (h : s subseteq t) (ht : IsUpperSet t
) : ↑(upperClosure s) subseteq t
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `subset_upperClosure`：subset_upperClosure : s subseteq upperClosure s
-/
protected theorem IsUpperSet.upperClosure (hs : IsUpperSet s) : ↑(upperClosure s) = s :=
  (upperClosure_min Subset.rfl hs).antisymm subset_upperClosure

@[to_dual (attr := simp)]
/-
**UpperSet.upperClosure** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] (s : UpperSet α), upperClosure ↑s = s
参数：s : UpperSet α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `IsUpperSet.upperClosure`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α
}, IsUpperSet s → ↑(upperClosure s) = s
· 使用定理 `UpperSet.upper'`：∀ {α : Type u_1} [inst : LE α] (self : UpperSet α), IsU
pperSet self.carrier
-/
protected theorem UpperSet.upperClosure (s : UpperSet α) : upperClosure (s : Set α) = s :=
  SetLike.coe_injective s.2.upperClosure

@[to_dual (attr := simp)]
/-
**upperClosure_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperClosure_image (f : α ≃o β) : upperClosure (f '' s) = UpperSet.map f (
upperClosure s)
参数：f : α ≃o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.symm_symm`：symm_symm (e : α ≃o β) : e.symm.symm = e
· 使用定理 `UpperSet.symm_map`：symm_map (f : α ≃o β) : (map f).symm = map f.symm
· 使用定理 `UpperSet.ext`：ext {s t : UpperSet α} : (s : Set α) = t -> s = t
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `OrderIso.le_symm_apply`：le_symm_apply (e : α ≃o β) {x : α} {y : β} : x <
= e.symm y ↔ e x <= y
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem upperClosure_image (f : α ≃o β) :
    upperClosure (f '' s) = UpperSet.map f (upperClosure s) := by
  rw [← f.symm_symm, ← UpperSet.symm_map, f.symm_symm]
  ext
  simp only [SetLike.mem_coe]
  simp [f.le_symm_apply]

@[to_dual (attr := simp)]
/-
**UpperSet.iInf_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperSet.iInf_Ici (s : Set α) : ⨅ a in s, UpperSet.Ici a = upperClosure s
参数：s : Set α。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `UpperSet.coe_iInf`：coe_iInf (f : ι -> UpperSet α) : (↑(⨅ i, f i) : Set α
) = ⋃ i, f i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem UpperSet.iInf_Ici (s : Set α) : ⨅ a ∈ s, UpperSet.Ici a = upperClosure s := by
  ext
  simp

@[to_dual (attr := simp) le_upperClosure]
/-
**lowerClosure_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lowerClosure_le {t : LowerSet α} : lowerClosure s <= t ↔ s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `subset_lowerClosure`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, s
 ⊆ ↑(lowerClosure s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LowerSet.coe_subset_coe`：∀ {α : Type u_1} [inst : LE α] {s t : LowerSet 
α}, ↑s ⊆ ↑t ↔ s ≤ t
· 使用定理 `lowerClosure_min`：∀ {α : Type u_1} [inst : Preorder α] {s t : Set α}, s 
⊆ t → IsLowerSet t → ↑(lowerClosure s) ⊆ t
· 使用定理 `LowerSet.lower`：∀ {α : Type u_1} [inst : LE α] (s : LowerSet α), IsLower
Set ↑s
-/
lemma lowerClosure_le {t : LowerSet α} : lowerClosure s ≤ t ↔ s ⊆ t :=
  ⟨fun h ↦ subset_lowerClosure.trans <| LowerSet.coe_subset_coe.2 h,
    fun h ↦ lowerClosure_min h t.lower⟩
/-
**gc_upperClosure_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gc_upperClosure_coe : GaloisConnection (toDual ∘ upperClosure : Set α -> (
UpperSet α)ᵒᵈ) ((↑) ∘ ofDual)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_upperClosure`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {t : U
pperSet α}, t ≤ upperClosure s ↔ s ⊆ ↑t
-/
theorem gc_upperClosure_coe :
    GaloisConnection (toDual ∘ upperClosure : Set α → (UpperSet α)ᵒᵈ) ((↑) ∘ ofDual) :=
  fun _s _t ↦ le_upperClosure
/-
**gc_lowerClosure_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gc_lowerClosure_coe : GaloisConnection (lowerClosure : Set α -> LowerSet α
) (↑)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lowerClosure_le`：lowerClosure_le {t : LowerSet α} : lowerClosure s <= t 
↔ s subseteq t
-/
theorem gc_lowerClosure_coe :
    GaloisConnection (lowerClosure : Set α → LowerSet α) (↑) := fun _s _t ↦ lowerClosure_le

/-- `upperClosure` forms a reversed Galois insertion with the coercion from upper sets to sets. -/
/-
**giUpperClosureCoe** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：giUpperClosureCoe : GaloisInsertion (toDual ∘ upperClosure : Set α -> (Upp
erSet α)ᵒᵈ) ((↑) ∘ ofDual) where choice s hs
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `gc_upperClosure_coe`：gc_upperClosure_coe : GaloisConnection (toDual ∘ up
perClosure : Set α -> (UpperSet α)ᵒᵈ) ((↑) ∘ ofDual)

--- 原说明 ---
`upperClosure` forms a reversed Galois insertion with the coercion from upper se
ts to sets.
-/
def giUpperClosureCoe :
    GaloisInsertion (toDual ∘ upperClosure : Set α → (UpperSet α)ᵒᵈ) ((↑) ∘ ofDual) where
  choice s hs := toDual (⟨s, fun a _b hab ha => hs ⟨a, ha, hab⟩⟩ : UpperSet α)
  gc := gc_upperClosure_coe
  le_l_u _ := subset_upperClosure
  choice_eq _s hs := ofDual.injective <| SetLike.coe_injective <| subset_upperClosure.antisymm hs

/-- `lowerClosure` forms a Galois insertion with the coercion from lower sets to sets. -/
/-
**giLowerClosureCoe** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：giLowerClosureCoe : GaloisInsertion (lowerClosure : Set α -> LowerSet α) (
↑) where choice s hs
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `gc_lowerClosure_coe`：gc_lowerClosure_coe : GaloisConnection (lowerClosur
e : Set α -> LowerSet α) (↑)

--- 原说明 ---
`lowerClosure` forms a Galois insertion with the coercion from lower sets to set
s.
-/
def giLowerClosureCoe : GaloisInsertion (lowerClosure : Set α → LowerSet α) (↑) where
  choice s hs := ⟨s, fun a _b hba ha => hs ⟨a, ha, hba⟩⟩
  gc := gc_lowerClosure_coe
  le_l_u _ := subset_lowerClosure
  choice_eq _s hs := SetLike.coe_injective <| subset_lowerClosure.antisymm hs
/-
**upperClosure_anti** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperClosure_anti : Antitone (upperClosure : Set α -> UpperSet α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `gc_upperClosure_coe`：gc_upperClosure_coe : GaloisConnection (toDual ∘ up
perClosure : Set α -> (UpperSet α)ᵒᵈ) ((↑) ∘ ofDual)
-/
theorem upperClosure_anti : Antitone (upperClosure : Set α → UpperSet α) :=
  gc_upperClosure_coe.monotone_l
/-
**lowerClosure_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerClosure_mono : Monotone (lowerClosure : Set α -> LowerSet α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `gc_lowerClosure_coe`：gc_lowerClosure_coe : GaloisConnection (lowerClosur
e : Set α -> LowerSet α) (↑)
-/
theorem lowerClosure_mono : Monotone (lowerClosure : Set α → LowerSet α) :=
  gc_lowerClosure_coe.monotone_l

@[to_dual (attr := simp)]
/-
**upperClosure_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperClosure_eq_top_iff : upperClosure s = ⊤ ↔ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `le_upperClosure`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {t : U
pperSet α}, t ≤ upperClosure s ↔ s ⊆ ↑t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem upperClosure_eq_top_iff : upperClosure s = ⊤ ↔ s = ∅ := by
  rw [eq_top_iff, le_upperClosure]; simp

@[to_dual (attr := simp)]
/-
**upperClosure_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperClosure_empty : upperClosure (∅ : Set α) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `upperClosure_eq_top_iff`：upperClosure_eq_top_iff : upperClosure s = ⊤ ↔ 
s = ∅
-/
theorem upperClosure_empty : upperClosure (∅ : Set α) = ⊤ :=
  upperClosure_eq_top_iff.mpr rfl

@[to_dual (attr := simp)]
/-
**upperClosure_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperClosure_singleton (a : α) : upperClosure ({a} : Set α) = UpperSet.Ici
 a
参数：a : α。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem upperClosure_singleton (a : α) : upperClosure ({a} : Set α) = UpperSet.Ici a := by
  ext
  simp

@[to_dual (attr := simp)]
/-
**upperClosure_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperClosure_univ : upperClosure (univ : Set α) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `subset_upperClosure`：subset_upperClosure : s subseteq upperClosure s
-/
theorem upperClosure_univ : upperClosure (univ : Set α) = ⊥ :=
  bot_unique subset_upperClosure
/-
**upperClosure_union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperClosure_union (s t : Set α) : upperClosure (s union t) = upperClosure
 s ⊓ upperClosure t
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `gc_upperClosure_coe`：gc_upperClosure_coe : GaloisConnection (toDual ∘ up
perClosure : Set α -> (UpperSet α)ᵒᵈ) ((↑) ∘ ofDual)
-/
theorem upperClosure_union (s t : Set α) : upperClosure (s ∪ t) = upperClosure s ⊓ upperClosure t :=
  (@gc_upperClosure_coe α _).l_sup

@[to_dual existing (attr := simp)]
/-
**lowerClosure_union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerClosure_union (s t : Set α) : lowerClosure (s union t) = lowerClosure
 s ⊔ lowerClosure t
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `gc_lowerClosure_coe`：gc_lowerClosure_coe : GaloisConnection (lowerClosur
e : Set α -> LowerSet α) (↑)
-/
theorem lowerClosure_union (s t : Set α) : lowerClosure (s ∪ t) = lowerClosure s ⊔ lowerClosure t :=
  (@gc_lowerClosure_coe α _).l_sup
/-
**upperClosure_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperClosure_iUnion (f : ι -> Set α) : upperClosure (⋃ i, f i) = ⨅ i, uppe
rClosure (f i)
参数：f : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `gc_upperClosure_coe`：gc_upperClosure_coe : GaloisConnection (toDual ∘ up
perClosure : Set α -> (UpperSet α)ᵒᵈ) ((↑) ∘ ofDual)
-/
theorem upperClosure_iUnion (f : ι → Set α) : upperClosure (⋃ i, f i) = ⨅ i, upperClosure (f i) :=
  (@gc_upperClosure_coe α _).l_iSup

@[to_dual existing (attr := simp)]
/-
**lowerClosure_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerClosure_iUnion (f : ι -> Set α) : lowerClosure (⋃ i, f i) = ⨆ i, lowe
rClosure (f i)
参数：f : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `gc_lowerClosure_coe`：gc_lowerClosure_coe : GaloisConnection (lowerClosur
e : Set α -> LowerSet α) (↑)
-/
theorem lowerClosure_iUnion (f : ι → Set α) : lowerClosure (⋃ i, f i) = ⨆ i, lowerClosure (f i) :=
  (@gc_lowerClosure_coe α _).l_iSup

@[to_dual (attr := simp)]
/-
**upperClosure_sUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperClosure_sUnion (S : Set (Set α)) : upperClosure (⋃₀ S) = ⨅ s in S, up
perClosure s
参数：S : Set (Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `upperClosure_iUnion`：upperClosure_iUnion (f : ι -> Set α) : upperClosure
 (⋃ i, f i) = ⨅ i, upperClosure (f i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem upperClosure_sUnion (S : Set (Set α)) : upperClosure (⋃₀ S) = ⨅ s ∈ S, upperClosure s := by
  simp_rw [sUnion_eq_biUnion, upperClosure_iUnion]
/-
**Set.OrdConnected.upperClosure_inter_lowerClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.OrdConnected.upperClosure_inter_lowerClosure (h : s.OrdConnected) : ↑(
upperClosure s) inter ↑(lowerClosure s) = s
参数：h : s.OrdConnected。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `subset_upperClosure`：subset_upperClosure : s subseteq upperClosure s
· 使用定理 `subset_lowerClosure`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, s
 ⊆ ↑(lowerClosure s)
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
-/
theorem Set.OrdConnected.upperClosure_inter_lowerClosure (h : s.OrdConnected) :
    ↑(upperClosure s) ∩ ↑(lowerClosure s) = s :=
  (subset_inter subset_upperClosure subset_lowerClosure).antisymm'
    fun _a ⟨⟨_b, hb, hba⟩, _c, hc, hac⟩ => h.out hb hc ⟨hba, hac⟩
/-
**ordConnected_iff_upperClosure_inter_lowerClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ordConnected_iff_upperClosure_inter_lowerClosure : s.OrdConnected ↔ ↑(uppe
rClosure s) inter ↑(lowerClosure s) = s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.upperClosure_inter_lowerClosure`：Set.OrdConnected.upper
Closure_inter_lowerClosure (h : s.OrdConnected) : ↑(upperClosure s) inter ↑(lowe
rClosure s) = s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.OrdConnected.inter`：∀ {α : Type u_1} [inst : Preorder α] {s t : Set 
α}, s.OrdConnected → t.OrdConnected → (s ∩ t).OrdConnected
· 使用定理 `IsUpperSet.ordConnected`：IsUpperSet.ordConnected (h : IsUpperSet s) : s.
OrdConnected
· 使用定理 `UpperSet.upper`：∀ {α : Type u_1} [inst : LE α] (s : UpperSet α), IsUpper
Set ↑s
· 使用定理 `IsLowerSet.ordConnected`：IsLowerSet.ordConnected (h : IsLowerSet s) : s.
OrdConnected
· 使用定理 `LowerSet.lower`：∀ {α : Type u_1} [inst : LE α] (s : LowerSet α), IsLower
Set ↑s
-/
theorem ordConnected_iff_upperClosure_inter_lowerClosure :
    s.OrdConnected ↔ ↑(upperClosure s) ∩ ↑(lowerClosure s) = s := by
  refine ⟨Set.OrdConnected.upperClosure_inter_lowerClosure, fun h => ?_⟩
  rw [← h]
  exact (UpperSet.upper _).ordConnected.inter (LowerSet.lower _).ordConnected

@[to_dual (attr := simp)]
/-
**lowerBounds_upperClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerBounds_upperClosure : lowerBounds (upperClosure s : Set α) = lowerBou
nds s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `lowerBounds_mono_set`：∀ {α : Type u_1} [inst : Preorder α] ⦃s t : Set α⦄
, s ⊆ t → lowerBounds t ⊆ lowerBounds s
· 使用定理 `subset_upperClosure`：subset_upperClosure : s subseteq upperClosure s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem lowerBounds_upperClosure : lowerBounds (upperClosure s : Set α) = lowerBounds s :=
  (lowerBounds_mono_set subset_upperClosure).antisymm
    fun _a ha _b ⟨_c, hc, hcb⟩ ↦ (ha hc).trans hcb

@[to_dual (attr := simp)]
/-
**bddBelow_upperClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bddBelow_upperClosure : BddBelow (upperClosure s : Set α) ↔ BddBelow s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lowerBounds_upperClosure`：lowerBounds_upperClosure : lowerBounds (upperC
losure s : Set α) = lowerBounds s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem bddBelow_upperClosure : BddBelow (upperClosure s : Set α) ↔ BddBelow s := by
  simp_rw [BddBelow, lowerBounds_upperClosure]

@[to_dual]
protected alias ⟨BddBelow.of_upperClosure, BddBelow.upperClosure⟩ := bddBelow_upperClosure

@[to_dual (attr := simp) disjoint_lowerClosure_left]
/-
**IsLowerSet.disjoint_upperClosure_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLowerSet.disjoint_upperClosure_left (ht : IsLowerSet t) : Disjoint ↑(upp
erClosure s) t ↔ Disjoint s t
参数：ht : IsLowerSet t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用定理 `subset_upperClosure`：subset_upperClosure : s subseteq upperClosure s
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma IsLowerSet.disjoint_upperClosure_left (ht : IsLowerSet t) :
    Disjoint ↑(upperClosure s) t ↔ Disjoint s t := by
  refine ⟨Disjoint.mono_left subset_upperClosure, ?_⟩
  simp only [disjoint_left, SetLike.mem_coe, mem_upperClosure, forall_exists_index, and_imp]
  exact fun h a b hb hba ha ↦ h hb <| ht hba ha

@[to_dual (attr := simp) disjoint_lowerClosure_right]
/-
**IsLowerSet.disjoint_upperClosure_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLowerSet.disjoint_upperClosure_right (hs : IsLowerSet s) : Disjoint s (u
pperClosure t) ↔ Disjoint s t
参数：hs : IsLowerSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsLowerSet.disjoint_upperClosure_left`：IsLowerSet.disjoint_upperClosure_
left (ht : IsLowerSet t) : Disjoint ↑(upperClosure s) t ↔ Disjoint s t
-/
lemma IsLowerSet.disjoint_upperClosure_right (hs : IsLowerSet s) :
    Disjoint s (upperClosure t) ↔ Disjoint s t := by
  simpa only [disjoint_comm] using hs.disjoint_upperClosure_left

@[to_dual (attr := simp)]
/-
**upperClosure_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperClosure_eq : ↑(upperClosure s) = s ↔ IsUpperSet s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperSet.upper`：∀ {α : Type u_1} [inst : LE α] (s : UpperSet α), IsUpper
Set ↑s
· 使用定理 `IsUpperSet.upperClosure`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α
}, IsUpperSet s → ↑(upperClosure s) = s
-/
lemma upperClosure_eq :
    ↑(upperClosure s) = s ↔ IsUpperSet s :=
  ⟨(· ▸ UpperSet.upper _), IsUpperSet.upperClosure⟩

end Preorder

section PartialOrder
variable [PartialOrder α] {s : Set α} {x : α}

/-
**IsAntichain.minimal_mem_upperClosure_iff_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsAntichain.minimal_mem_upperClosure_iff_mem (hs : IsAntichain (· <= ·) s)
 : Minimal (· in upperClosure s) x ↔ x in s
参数：hs : IsAntichain (· <= ·) s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Minimal.prop`：Minimal.prop (h : Minimal P x) : P x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Minimal.eq_of_ge`：Minimal.eq_of_ge (hx : Minimal P x) (hy : P y) (hge : 
y <= x) : x = y
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsAntichain.eq`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}, IsAntic
hain r s → ∀ {a b : α}, a ∈ s → b ∈ s → r a b → a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma IsAntichain.minimal_mem_upperClosure_iff_mem (hs : IsAntichain (· ≤ ·) s) :
    Minimal (· ∈ upperClosure s) x ↔ x ∈ s := by
  simp only [upperClosure]
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨⟨x, h, rfl.le⟩, fun b ⟨a, has, hab⟩ hbx ↦ ?_⟩⟩
  · obtain ⟨a, has, hax⟩ := h.prop
    rwa [h.eq_of_ge ⟨a, has, rfl.le⟩ hax]
  rwa [← hs.eq has h (hab.trans hbx)]
/-
**IsAntichain.maximal_mem_lowerClosure_iff_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsAntichain.maximal_mem_lowerClosure_iff_mem (hs : IsAntichain (· <= ·) s)
 : Maximal (· in lowerClosure s) x ↔ x in s
参数：hs : IsAntichain (· <= ·) s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsAntichain.minimal_mem_upperClosure_iff_mem`：IsAntichain.minimal_mem_up
perClosure_iff_mem (hs : IsAntichain (· <= ·) s) : Minimal (· in upperClosure s)
 x ↔ x in s
· 使用定理 `IsAntichain.to_dual`：to_dual [LE α] (hs : IsAntichain (· <= ·) s) : @IsA
ntichain αᵒᵈ (· <= ·) s
-/
lemma IsAntichain.maximal_mem_lowerClosure_iff_mem (hs : IsAntichain (· ≤ ·) s) :
    Maximal (· ∈ lowerClosure s) x ↔ x ∈ s :=
  hs.to_dual.minimal_mem_upperClosure_iff_mem

end PartialOrder

section LinearOrder

variable [LinearOrder α]

@[to_dual]
/-
**upperClosure_eq_bot** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperClosure_eq_bot {s : Set α} (hs : ¬ BddBelow s) : upperClosure s = ⊥
参数：hs : ¬ BddBelow s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `not_bddBelow_iff`：∀ {α : Type u_4} [inst : LinearOrder α] {s : Set α}, ¬
BddBelow s ↔ ∀ (x : α), ∃ y ∈ s, y < x
· 使用定理 `And.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∧ b → c ∧ d
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma upperClosure_eq_bot {s : Set α} (hs : ¬ BddBelow s) : upperClosure s = ⊥ :=
  le_bot_iff.mp fun x _ ↦ ⟨_, (not_bddBelow_iff.mp hs x).choose_spec.imp id le_of_lt⟩

@[to_dual]
/-
**upperClosure_eq_bot_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperClosure_eq_bot_iff [NoMinOrder α] {s : Set α} : upperClosure s = ⊥ ↔ 
¬ BddBelow s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNoBotOrderOfNoMinOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMinO
rder α], NoBotOrder α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `bddBelow_upperClosure`：bddBelow_upperClosure : BddBelow (upperClosure s 
: Set α) ↔ BddBelow s
· 使用引理 `upperClosure_eq_bot`：upperClosure_eq_bot {s : Set α} (hs : ¬ BddBelow s)
 : upperClosure s = ⊥
-/
lemma upperClosure_eq_bot_iff [NoMinOrder α] {s : Set α} : upperClosure s = ⊥ ↔ ¬ BddBelow s :=
  ⟨fun h₁ h₂ ↦ by simpa [h₁] using bddBelow_upperClosure.mpr h₂, upperClosure_eq_bot⟩

end LinearOrder

/-! ### Set Difference -/

namespace UpperSet
variable [Preorder α] {s : UpperSet α} {t : Set α} {a : α}

/-- The biggest upper subset of an upper set `s` disjoint from a set `t`. -/
@[to_dual /-- The biggest lower subset of a lower set `s` disjoint from a set `t`. -/]
/-
**UpperSet.sdiff** 是 Mathlib 中的一个定义，位于命名空间 `UpperSet`。
形式化陈述：sdiff (s : UpperSet α) (t : Set α) : UpperSet α where carrier
参数：s : UpperSet α；t : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The biggest upper subset of an upper set `s` disjoint from a set `t`.
-/
def sdiff (s : UpperSet α) (t : Set α) : UpperSet α where
  carrier := s \ lowerClosure t
  upper' := s.upper.sdiff_of_isLowerSet (lowerClosure t).lower

/-- The biggest upper subset of an upper set `s` not containing an element `a`. -/
@[to_dual /-- The biggest lower subset of a lower set `s` not containing an element `a`. -/]
/-
**UpperSet.erase** 是 Mathlib 中的一个定义，位于命名空间 `UpperSet`。
形式化陈述：erase (s : UpperSet α) (a : α) : UpperSet α where carrier
参数：s : UpperSet α；a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The biggest upper subset of an upper set `s` not containing an element `a`.
-/
def erase (s : UpperSet α) (a : α) : UpperSet α where
  carrier := s \ LowerSet.Iic a
  upper' := s.upper.sdiff_of_isLowerSet (LowerSet.Iic a).lower

@[to_dual (attr := simp, norm_cast)]
/-
**UpperSet.coe_sdiff** 是 Mathlib 中的一个引理，位于命名空间 `UpperSet`。
形式化陈述：coe_sdiff (s : UpperSet α) (t : Set α) : s.sdiff t = (s : Set α) \ lowerCl
osure t
参数：s : UpperSet α；t : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_sdiff (s : UpperSet α) (t : Set α) : s.sdiff t = (s : Set α) \ lowerClosure t := rfl

@[to_dual (attr := simp, norm_cast)]
/-
**UpperSet.coe_erase** 是 Mathlib 中的一个引理，位于命名空间 `UpperSet`。
形式化陈述：coe_erase (s : UpperSet α) (a : α) : s.erase a = (s : Set α) \ LowerSet.Ii
c a
参数：s : UpperSet α；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_erase (s : UpperSet α) (a : α) : s.erase a = (s : Set α) \ LowerSet.Iic a := rfl

@[to_dual (attr := simp)]
/-
**UpperSet.sdiff_singleton** 是 Mathlib 中的一个引理，位于命名空间 `UpperSet`。
形式化陈述：sdiff_singleton (s : UpperSet α) (a : α) : s.sdiff {a} = s.erase a
参数：s : UpperSet α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lowerClosure_singleton`：∀ {α : Type u_1} [inst : Preorder α] (a : α), lo
werClosure {a} = LowerSet.Iic a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `UpperSet.mk.congr_simp`：∀ {α : Type u_1} [inst : LE α] (carrier carrier_
1 : Set α) (e_carrier : carrier = carrier_1)   (upper' : IsUpperSet carrier), { 
carrier := c…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sdiff_singleton (s : UpperSet α) (a : α) : s.sdiff {a} = s.erase a := by
  simp [sdiff, erase]
/-
**UpperSet.le_sdiff_left** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {s : UpperSet α} {t : Set α}, s ≤ s.s
diff t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
-/
@[to_dual sdiff_le_left] lemma le_sdiff_left : s ≤ s.sdiff t := sdiff_subset
/-
**UpperSet.le_erase** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {s : UpperSet α} {a : α}, s ≤ s.erase
 a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
-/
@[to_dual erase_le] lemma le_erase : s ≤ s.erase a := sdiff_subset

@[to_dual (attr := simp)]
/-
**UpperSet.sdiff_eq_left** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {s : UpperSet α} {t : Set α}, s.sdiff
 t = s ↔ Disjoint (↑s) t
参数：↑s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma sdiff_eq_left : s.sdiff t = s ↔ Disjoint ↑s t := by
  simp [← SetLike.coe_set_eq]

@[to_dual (attr := simp)]
/-
**UpperSet.erase_eq** 是 Mathlib 中的一个引理，位于命名空间 `UpperSet`。
形式化陈述：erase_eq : s.erase a = s ↔ a ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `UpperSet.sdiff_singleton`：sdiff_singleton (s : UpperSet α) (a : α) : s.s
diff {a} = s.erase a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma erase_eq : s.erase a = s ↔ a ∉ s := by rw [← sdiff_singleton]; simp [-sdiff_singleton]

@[to_dual (attr := simp) sdiff_lt_left]
/-
**UpperSet.lt_sdiff_left** 是 Mathlib 中的一个引理，位于命名空间 `UpperSet`。
形式化陈述：lt_sdiff_left : s < s.sdiff t ↔ ¬ Disjoint ↑s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `LE.le.lt_iff_ne'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (b < a ↔ a ≠ b)
· 使用定理 `UpperSet.le_sdiff_left`：∀ {α : Type u_1} [inst : Preorder α] {s : UpperS
et α} {t : Set α}, s ≤ s.sdiff t
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `UpperSet.sdiff_eq_left`：∀ {α : Type u_1} [inst : Preorder α] {s : UpperS
et α} {t : Set α}, s.sdiff t = s ↔ Disjoint (↑s) t
-/
lemma lt_sdiff_left : s < s.sdiff t ↔ ¬ Disjoint ↑s t :=
  le_sdiff_left.lt_iff_ne'.trans UpperSet.sdiff_eq_left.not

@[to_dual (attr := simp) erase_lt]
/-
**UpperSet.lt_erase** 是 Mathlib 中的一个引理，位于命名空间 `UpperSet`。
形式化陈述：lt_erase : s < s.erase a ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `LE.le.lt_iff_ne'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (b < a ↔ a ≠ b)
· 使用定理 `UpperSet.le_erase`：∀ {α : Type u_1} [inst : Preorder α] {s : UpperSet α}
 {a : α}, s ≤ s.erase a
· 使用定理 `Iff.not_left`：Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b
· 使用引理 `UpperSet.erase_eq`：erase_eq : s.erase a = s ↔ a ∉ s
-/
lemma lt_erase : s < s.erase a ↔ a ∈ s := le_erase.lt_iff_ne'.trans erase_eq.not_left

@[to_dual (attr := simp)]
/-
**UpperSet.sdiff_idem** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] (s : UpperSet α) (t : Set α), (s.sdif
f t).sdiff t = s.sdiff t
参数：s : UpperSet α；t : Set α；s.sdiff t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `sdiff_idem`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b
 : α}, (a \ b) \ b = a \ b
-/
protected lemma sdiff_idem (s : UpperSet α) (t : Set α) : (s.sdiff t).sdiff t = s.sdiff t :=
  SetLike.coe_injective sdiff_idem

@[to_dual (attr := simp)]
/-
**UpperSet.erase_idem** 是 Mathlib 中的一个引理，位于命名空间 `UpperSet`。
形式化陈述：erase_idem (s : UpperSet α) (a : α) : (s.erase a).erase a = s.erase a
参数：s : UpperSet α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `sdiff_idem`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b
 : α}, (a \ b) \ b = a \ b
-/
lemma erase_idem (s : UpperSet α) (a : α) : (s.erase a).erase a = s.erase a :=
  SetLike.coe_injective sdiff_idem

@[to_dual]
/-
**UpperSet.sdiff_inf_upperClosure** 是 Mathlib 中的一个引理，位于命名空间 `UpperSet`。
形式化陈述：sdiff_inf_upperClosure (hts : t subseteq s) (hst : forall b in s, forall c
 in t, b <= c -> b in t) : s.sdiff t ⊓ upperClosure t = s
参数：hts : t subseteq s；hst : forall b in s, forall c in t, b <= c -> b in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ge_antisymm`：ge_antisymm : b <= a -> a <= b -> a = b
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `UpperSet.le_sdiff_left`：∀ {α : Type u_1} [inst : Preorder α] {s : UpperS
et α} {t : Set α}, s ≤ s.sdiff t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_upperClosure`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {t : U
pperSet α}, t ≤ upperClosure s ↔ s ⊆ ↑t
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `subset_upperClosure`：subset_upperClosure : s subseteq upperClosure s
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
-/
lemma sdiff_inf_upperClosure (hts : t ⊆ s) (hst : ∀ b ∈ s, ∀ c ∈ t, b ≤ c → b ∈ t) :
    s.sdiff t ⊓ upperClosure t = s := by
  refine ge_antisymm (le_inf le_sdiff_left <| le_upperClosure.2 hts) fun a ha ↦ ?_
  obtain hat | hat := em (a ∈ t)
  · exact subset_union_right (subset_upperClosure hat)
  · refine subset_union_left ⟨ha, ?_⟩
    rintro ⟨b, hb, hab⟩
    exact hat <| hst _ ha _ hb hab

@[to_dual]
/-
**UpperSet.upperClosure_inf_sdiff** 是 Mathlib 中的一个引理，位于命名空间 `UpperSet`。
形式化陈述：upperClosure_inf_sdiff (hts : t subseteq s) (hst : forall b in s, forall c
 in t, b <= c -> b in t) : upperClosure t ⊓ s.sdiff t = s
参数：hts : t subseteq s；hst : forall b in s, forall c in t, b <= c -> b in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用引理 `UpperSet.sdiff_inf_upperClosure`：sdiff_inf_upperClosure (hts : t subsete
q s) (hst : forall b in s, forall c in t, b <= c -> b in t) : s.sdiff t ⊓ upperC
losure t = s
-/
lemma upperClosure_inf_sdiff (hts : t ⊆ s) (hst : ∀ b ∈ s, ∀ c ∈ t, b ≤ c → b ∈ t) :
    upperClosure t ⊓ s.sdiff t = s := by rw [inf_comm, sdiff_inf_upperClosure hts hst]

@[to_dual]
/-
**UpperSet.erase_inf_Ici** 是 Mathlib 中的一个引理，位于命名空间 `UpperSet`。
形式化陈述：erase_inf_Ici (ha : a in s) (has : forall b in s, b <= a -> b = a) : s.era
se a ⊓ Ici a = s
参数：ha : a in s；has : forall b in s, b <= a -> b = a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `upperClosure_singleton`：upperClosure_singleton (a : α) : upperClosure ({
a} : Set α) = UpperSet.Ici a
· 使用引理 `UpperSet.sdiff_singleton`：sdiff_singleton (s : UpperSet α) (a : α) : s.s
diff {a} = s.erase a
· 使用引理 `UpperSet.sdiff_inf_upperClosure`：sdiff_inf_upperClosure (hts : t subsete
q s) (hst : forall b in s, forall c in t, b <= c -> b in t) : s.sdiff t ⊓ upperC
losure t = s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma erase_inf_Ici (ha : a ∈ s) (has : ∀ b ∈ s, b ≤ a → b = a) : s.erase a ⊓ Ici a = s := by
  rw [← upperClosure_singleton, ← sdiff_singleton, sdiff_inf_upperClosure] <;> simpa

@[to_dual]
/-
**UpperSet.Ici_inf_erase** 是 Mathlib 中的一个引理，位于命名空间 `UpperSet`。
形式化陈述：Ici_inf_erase (ha : a in s) (has : forall b in s, b <= a -> b = a) : Ici a
 ⊓ s.erase a = s
参数：ha : a in s；has : forall b in s, b <= a -> b = a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用引理 `UpperSet.erase_inf_Ici`：erase_inf_Ici (ha : a in s) (has : forall b in s
, b <= a -> b = a) : s.erase a ⊓ Ici a = s
-/
lemma Ici_inf_erase (ha : a ∈ s) (has : ∀ b ∈ s, b ≤ a → b = a) : Ici a ⊓ s.erase a = s := by
  rw [inf_comm, erase_inf_Ici ha has]

end UpperSet

