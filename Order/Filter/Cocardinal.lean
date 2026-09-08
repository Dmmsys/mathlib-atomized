/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
module

public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.CountableInter
public import Mathlib.Order.Filter.CardinalInter
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal

/-!
# The cocardinal filter

In this file we define `Filter.cocardinal hc`: the filter of sets with cardinality less than
  a regular cardinal `c` that satisfies `Cardinal.aleph0 < c`.
  Such filters are `CardinalInterFilter` with cardinality `c`.

-/

@[expose] public section

open Set Filter Cardinal

universe u
variable {α : Type u} {c : Cardinal.{u}} {hreg : c.IsRegular}

namespace Filter

variable (α) in
/-- The filter defined by all sets that have a complement with at most cardinality `c`. For a union
of `c` sets of `c` elements to have `c` elements, we need that `c` is a regular cardinal. -/
/-
**Filter.cocardinal** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：cocardinal (hreg : c.IsRegular) : Filter α
参数：hreg : c.IsRegular。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The filter defined by all sets that have a complement with at most cardinality `
c`. For a union
of `c` sets of `c` elements to have `c` elements, we need that `c` is a regular 
cardinal.
-/
def cocardinal (hreg : c.IsRegular) : Filter α := by
  apply ofCardinalUnion {s | Cardinal.mk s < c} (natCast_lt_aleph0.trans_le hreg.aleph0_le)
  · refine fun s hS hSc ↦ lt_of_le_of_lt (mk_sUnion_le _) <| mul_lt_of_lt hreg.aleph0_le hS ?_
    apply iSup_lt_of_lt_cof_ord _ fun i ↦ hSc i.1 i.2
    rwa [hreg.cof_ord]
  · exact fun _ hSc _ ht ↦ lt_of_le_of_lt (mk_le_mk_of_subset ht) hSc

@[simp]
/-
**Filter.mem_cocardinal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_cocardinal {s : Set α} : s in cocardinal α hreg ↔ Cardinal.mk (sᶜ : Se
t α) < c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_cocardinal {s : Set α} :
    s ∈ cocardinal α hreg ↔ Cardinal.mk (sᶜ : Set α) < c := Iff.rfl
/-
**Filter.cocardinal_aleph0_eq_cofinite** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u}, Filter.cocardinal α Cardinal.isRegular_aleph0 = Filter.cof
inite
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `Cardinal.isRegular_aleph0`：isRegular_aleph0 : IsRegular ℵ₀
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma cocardinal_aleph0_eq_cofinite :
    cocardinal (α := α) isRegular_aleph0 = cofinite := by
  aesop
/-
**Filter.instCardinalInterFilter_cocardinal** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：instCardinalInterFilter_cocardinal : CardinalInterFilter (cocardinal (α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_cocardinal`：mem_cocardinal {s : Set α} : s in cocardinal α hr
eg ↔ Cardinal.mk (sᶜ : Set α) < c
· 使用定理 `Set.compl_sInter`：compl_sInter (S : Set (Set α)) : (⋂₀ S)ᶜ = ⋃₀ (compl '
' S)
· 使用定理 `lt_imp_lt_of_le_of_le`：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a < b -> c < d
· 使用定理 `Cardinal.mk_sUnion_le`：mk_sUnion_le {α : Type u} (A : Set (Set α)) : #(⋃
₀ A) <= #A * ⨆ s : A, #s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Cardinal.mul_lt_of_lt`：mul_lt_of_lt {a b c : Cardinal} (hc : ℵ₀ <= c) (h
a : a < c) (hb : b < c) : a * b < c
· 使用定理 `Cardinal.IsRegular.aleph0_le`：∀ {c : Cardinal.{u_1}}, c.IsRegular → Card
inal.aleph0 ≤ c
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Cardinal.mk_image_le`：mk_image_le {α β : Type u} {f : α -> β} {s : Set α
} : #(f '' s) <= #s
· 使用定理 `Cardinal.iSup_lt_of_lt_cof_ord`：∀ {α : Type u} {f : α → Cardinal.{u}} {a
 : Cardinal.{u}},   Cardinal.mk α < a.ord.cof → (∀ (i : α), f i < a) → ⨆ i, f i 
< a
· 使用定理 `Cardinal.IsRegular.cof_ord`：∀ {c : Cardinal.{u_1}}, c.IsRegular → c.ord.
cof = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
-/
instance instCardinalInterFilter_cocardinal : CardinalInterFilter (cocardinal (α := α) hreg) c where
  cardinal_sInter_mem S hS hSs := by
    grw [mem_cocardinal, Set.compl_sInter, mk_sUnion_le]
    apply mul_lt_of_lt hreg.aleph0_le (mk_image_le.trans_lt hS) (iSup_lt_of_lt_cof_ord ..)
    · rw [hreg.cof_ord]
      exact mk_image_le.trans_lt hS
    · aesop

@[simp]
/-
**Filter.eventually_cocardinal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_cocardinal {p : α -> Prop} : (forallᶠ x in cocardinal α hreg, p
 x) ↔ #{ x | ¬p x } < c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eventually_cocardinal {p : α → Prop} :
    (∀ᶠ x in cocardinal α hreg, p x) ↔ #{ x | ¬p x } < c := Iff.rfl
/-
**Filter.hasBasis_cocardinal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：hasBasis_cocardinal : HasBasis (cocardinal α hreg) (fun s : Set α => #s < 
c) compl
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Cardinal.mk_le_mk_of_subset`：mk_le_mk_of_subset {α} {s t : Set α} (h : s
 subseteq t) : #s <= #t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_subset_comm`：compl_subset_comm : sᶜ subseteq t ↔ tᶜ subseteq s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem hasBasis_cocardinal : HasBasis (cocardinal α hreg) (fun s : Set α ↦ #s < c) compl :=
  ⟨fun s =>
    ⟨fun h => ⟨sᶜ, h, (compl_compl s).subset⟩, fun ⟨_t, htf, hts⟩ => by
      have : #↑sᶜ < c := by
        apply lt_of_le_of_lt _ htf
        rw [compl_subset_comm] at hts
        apply Cardinal.mk_le_mk_of_subset hts
      simp_all only [mem_cocardinal] ⟩⟩
/-
**Filter.frequently_cocardinal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_cocardinal {p : α -> Prop} : (existsᶠ x in cocardinal α hreg, p
 x) ↔ c <= #{ x | p x }
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem frequently_cocardinal {p : α → Prop} :
    (∃ᶠ x in cocardinal α hreg, p x) ↔ c ≤ #{ x | p x } := by
  simp only [Filter.Frequently, eventually_cocardinal, not_not, coe_ofPred, not_lt]
/-
**Filter.frequently_cocardinal_mem** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：frequently_cocardinal_mem {s : Set α} : (existsᶠ x in cocardinal α hreg, x
 in s) ↔ c <= #s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.frequently_cocardinal`：frequently_cocardinal {p : α -> Prop} : (e
xistsᶠ x in cocardinal α hreg, p x) ↔ c <= #{ x | p x }
-/
lemma frequently_cocardinal_mem {s : Set α} :
    (∃ᶠ x in cocardinal α hreg, x ∈ s) ↔ c ≤ #s := frequently_cocardinal

@[simp]
/-
**Filter.cocardinal_inf_principal_neBot_iff** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：cocardinal_inf_principal_neBot_iff {s : Set α} : (cocardinal α hreg ⊓ 𝓟 s)
.NeBot ↔ c <= #s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `Filter.frequently_mem_iff_neBot`：frequently_mem_iff_neBot {l : Filter α}
 {s : Set α} : (existsᶠ x in l, x in s) ↔ NeBot (l ⊓ 𝓟 s)
· 使用定理 `Filter.frequently_cocardinal`：frequently_cocardinal {p : α -> Prop} : (e
xistsᶠ x in cocardinal α hreg, p x) ↔ c <= #{ x | p x }
-/
lemma cocardinal_inf_principal_neBot_iff {s : Set α} :
    (cocardinal α hreg ⊓ 𝓟 s).NeBot ↔ c ≤ #s :=
  frequently_mem_iff_neBot.symm.trans frequently_cocardinal
/-
**Filter.compl_mem_cocardinal_of_card_lt** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：compl_mem_cocardinal_of_card_lt {s : Set α} (hs : #s < c) : sᶜ in cocardin
al α hreg
参数：hs : #s < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.mem_cocardinal`：mem_cocardinal {s : Set α} : s in cocardinal α hr
eg ↔ Cardinal.mk (sᶜ : Set α) < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
-/
theorem compl_mem_cocardinal_of_card_lt {s : Set α} (hs : #s < c) :
    sᶜ ∈ cocardinal α hreg :=
  mem_cocardinal.2 <| (compl_compl s).symm ▸ hs
/-
**Filter._root_.Set.Finite.compl_mem_cocardinal** 是 Mathlib 中的一个定理，位于命名空间 `Filte
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.Finite.compl_mem_cocardinal {s : Set α} (hs : s.Finite) :
    sᶜ ∈ cocardinal α hreg :=
  compl_mem_cocardinal_of_card_lt <| lt_of_lt_of_le (Finite.lt_aleph0 hs) (hreg.aleph0_le)
/-
**Filter.eventually_cocardinal_notMem_of_card_lt** 是 Mathlib 中的一个定理，位于命名空间 `Filt
er`。
形式化陈述：eventually_cocardinal_notMem_of_card_lt {s : Set α} (hs : #s < c) : forall
ᶠ x in cocardinal α hreg, x ∉ s
参数：hs : #s < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.compl_mem_cocardinal_of_card_lt`：compl_mem_cocardinal_of_card_lt 
{s : Set α} (hs : #s < c) : sᶜ in cocardinal α hreg
-/
theorem eventually_cocardinal_notMem_of_card_lt {s : Set α} (hs : #s < c) :
    ∀ᶠ x in cocardinal α hreg, x ∉ s :=
  compl_mem_cocardinal_of_card_lt hs
/-
**Filter._root_.Finset.eventually_cocardinal_notMem** 是 Mathlib 中的一个定理，位于命名空间 `F
ilter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Finset.eventually_cocardinal_notMem (s : Finset α) :
    ∀ᶠ x in cocardinal α hreg, x ∉ s :=
  eventually_cocardinal_notMem_of_card_lt <| (finset_card_lt_aleph0 s).trans_le (hreg.aleph0_le)
/-
**Filter.eventually_cocardinal_ne** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_cocardinal_ne (x : α) : forallᶠ a in cocardinal α hreg, a != x
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Cardinal.IsRegular.nat_lt`：∀ {c : Cardinal.{u_1}}, c.IsRegular → ∀ (n : 
ℕ), ↑n < c
-/
theorem eventually_cocardinal_ne (x : α) : ∀ᶠ a in cocardinal α hreg, a ≠ x := by
  simpa [Set.finite_singleton x] using hreg.nat_lt 1

/-- The filter defined by all sets that have countable complements. -/
/-
**Filter.cocountable** 是 Mathlib 中的一个缩写定义，位于命名空间 `Filter`。
形式化陈述：cocountable : Filter α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.isRegular_aleph_one`：isRegular_aleph_one : IsRegular ℵ₁

--- 原说明 ---
The filter defined by all sets that have countable complements.
-/
noncomputable abbrev cocountable : Filter α := cocardinal α Cardinal.isRegular_aleph_one
/-
**Filter.mem_cocountable** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_cocountable {s : Set α} : s in cocountable ↔ (sᶜ : Set α).Countable
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.le_aleph0_iff_set_countable`：le_aleph0_iff_set_countable {s : S
et α} : #s <= ℵ₀ ↔ s.Countable
· 使用定理 `Cardinal.isRegular_aleph_one`：isRegular_aleph_one : IsRegular ℵ₁
· 使用定理 `Filter.mem_cocardinal`：mem_cocardinal {s : Set α} : s in cocardinal α hr
eg ↔ Cardinal.mk (sᶜ : Set α) < c
· 使用定理 `Cardinal.lt_aleph_one_iff`：lt_aleph_one_iff {c : Cardinal} : c < ℵ₁ ↔ c 
<= ℵ₀
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_cocountable {s : Set α} : s ∈ cocountable ↔ (sᶜ : Set α).Countable := by
  rw [← Cardinal.le_aleph0_iff_set_countable, mem_cocardinal, lt_aleph_one_iff]

end Filter

