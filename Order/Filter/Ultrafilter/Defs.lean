/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov
-/
module

public import Mathlib.Order.Filter.Map
public import Mathlib.Order.ZornAtoms

/-!
# Ultrafilters

An ultrafilter is a minimal (maximal in the set order) proper filter.
In this file we define

* `Ultrafilter.of`: an ultrafilter that is less than or equal to a given filter;
* `Ultrafilter`: subtype of ultrafilters;
* `pure x : Ultrafilter α`: `pure x` as an `Ultrafilter`;
* `Ultrafilter.map`, `Ultrafilter.bind`, `Ultrafilter.comap` : operations on ultrafilters;
-/

@[expose] public section

assert_not_exists Set.Finite

universe u v

variable {α : Type u} {β : Type v} {γ : Type*}

open Set Filter Function

/-- `Filter α` is an atomic type: for every filter there exists an ultrafilter that is less than or
equal to this filter. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Filter α` is an atomic type: for every filter there exists an ultrafilter that 
is less than or
equal to this filter.
-/
instance : IsAtomic (Filter α) :=
  IsAtomic.of_isChain_bounded fun c hc hne hb =>
    ⟨sInf c, (sInf_neBot_of_directed' hne (show IsChain (· ≥ ·) c from hc.symm).directedOn hb).ne,
      fun _ hx => sInf_le hx⟩

/-- An ultrafilter is a minimal (maximal in the set order) proper filter. -/
/-
**Ultrafilter** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_2 → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An ultrafilter is a minimal (maximal in the set order) proper filter.
-/
structure Ultrafilter (α : Type*) extends Filter α where
  /-- An ultrafilter is nontrivial. -/
  protected neBot' : NeBot toFilter
  /-- If `g` is a nontrivial filter that is less than or equal to an ultrafilter, then it is greater
  than or equal to the ultrafilter. -/
  protected le_of_le : ∀ g, Filter.NeBot g → g ≤ toFilter → toFilter ≤ g

namespace Ultrafilter

variable {f g : Ultrafilter α} {s t : Set α} {p q : α → Prop}

attribute [coe] Ultrafilter.toFilter

/-
**Ultrafilter.** 是 Mathlib 中的一个实例，位于命名空间 `Ultrafilter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeTC (Ultrafilter α) (Filter α) :=
  ⟨Ultrafilter.toFilter⟩
/-
**Ultrafilter.** 是 Mathlib 中的一个实例，位于命名空间 `Ultrafilter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Membership (Set α) (Ultrafilter α) :=
  ⟨fun f s => s ∈ (f : Filter α)⟩
/-
**Ultrafilter.unique** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：unique (f : Ultrafilter α) {g : Filter α} (h : g <= f) (hne : NeBot g
参数：f : Ultrafilter α；h : g <= f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Ultrafilter.le_of_le`：∀ {α : Type u_2} (self : Ultrafilter α) (g : Filte
r α), g.NeBot → g ≤ ↑self → ↑self ≤ g
-/
theorem unique (f : Ultrafilter α) {g : Filter α} (h : g ≤ f) (hne : NeBot g := by infer_instance) :
    g = f :=
  le_antisymm h <| f.le_of_le g hne h
/-
**Ultrafilter.neBot** 是 Mathlib 中的一个实例，位于命名空间 `Ultrafilter`。
形式化陈述：neBot (f : Ultrafilter α) : NeBot (f : Filter α)
参数：f : Ultrafilter α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Ultrafilter.neBot'`：∀ {α : Type u_2} (self : Ultrafilter α), (↑self).NeB
ot
-/
instance neBot (f : Ultrafilter α) : NeBot (f : Filter α) :=
  f.neBot'
/-
**Ultrafilter.isAtom** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：∀ {α : Type u} (f : Ultrafilter α), IsAtom ↑f
参数：f : Ultrafilter α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.NeBot.ne`：∀ {α : Type u} {f : Filter α}, f.NeBot → f ≠ ⊥
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Ultrafilter.unique`：unique (f : Ultrafilter α) {g : Filter α} (h : g <= 
f) (hne : NeBot g
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
protected theorem isAtom (f : Ultrafilter α) : IsAtom (f : Filter α) :=
  ⟨f.neBot.ne, fun _ hgf => by_contra fun hg => hgf.ne <| f.unique hgf.le ⟨hg⟩⟩

@[simp, norm_cast]
/-
**Ultrafilter.mem_coe** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：mem_coe : s in (f : Filter α) ↔ s in f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_coe : s ∈ (f : Filter α) ↔ s ∈ f :=
  Iff.rfl
/-
**Ultrafilter.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：∀ {α : Type u}, Function.Injective Ultrafilter.toFilter
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_injective : Injective ((↑) : Ultrafilter α → Filter α)
  | ⟨f, h₁, h₂⟩, ⟨g, _, _⟩, _ => by congr
/-
**Ultrafilter.eq_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：eq_of_le {f g : Ultrafilter α} (h : (f : Filter α) <= g) : f = g
参数：h : (f : Filter α) <= g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ultrafilter.coe_injective`：∀ {α : Type u}, Function.Injective Ultrafilte
r.toFilter
· 使用定理 `Ultrafilter.unique`：unique (f : Ultrafilter α) {g : Filter α} (h : g <= 
f) (hne : NeBot g
-/
theorem eq_of_le {f g : Ultrafilter α} (h : (f : Filter α) ≤ g) : f = g :=
  coe_injective (g.unique h)

@[simp, norm_cast]
/-
**Ultrafilter.coe_le_coe** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：coe_le_coe {f g : Ultrafilter α} : (f : Filter α) <= g ↔ f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ultrafilter.eq_of_le`：eq_of_le {f g : Ultrafilter α} (h : (f : Filter α)
 <= g) : f = g
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem coe_le_coe {f g : Ultrafilter α} : (f : Filter α) ≤ g ↔ f = g :=
  ⟨fun h => eq_of_le h, fun h => h ▸ le_rfl⟩

@[simp, norm_cast]
/-
**Ultrafilter.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：coe_inj : (f : Filter α) = g ↔ f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Ultrafilter.coe_injective`：∀ {α : Type u}, Function.Injective Ultrafilte
r.toFilter
-/
theorem coe_inj : (f : Filter α) = g ↔ f = g :=
  coe_injective.eq_iff

@[ext]
/-
**Ultrafilter.ext** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：ext ⦃f g : Ultrafilter α⦄ (h : forall s, s in f ↔ s in g) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ultrafilter.coe_injective`：∀ {α : Type u}, Function.Injective Ultrafilte
r.toFilter
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
-/
theorem ext ⦃f g : Ultrafilter α⦄ (h : ∀ s, s ∈ f ↔ s ∈ g) : f = g :=
  coe_injective <| Filter.ext h
/-
**Ultrafilter.le_of_inf_neBot** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：le_of_inf_neBot (f : Ultrafilter α) {g : Filter α} (hg : NeBot (↑f ⊓ g)) :
 ↑f <= g
参数：f : Ultrafilter α；hg : NeBot (↑f ⊓ g)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_inf_eq`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= a → a ≤ b
· 使用定理 `Ultrafilter.unique`：unique (f : Ultrafilter α) {g : Filter α} (h : g <= 
f) (hne : NeBot g
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem le_of_inf_neBot (f : Ultrafilter α) {g : Filter α} (hg : NeBot (↑f ⊓ g)) : ↑f ≤ g :=
  le_of_inf_eq (f.unique inf_le_left hg)
/-
**Ultrafilter.le_of_inf_neBot'** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：le_of_inf_neBot' (f : Ultrafilter α) {g : Filter α} (hg : NeBot (g ⊓ f)) :
 ↑f <= g
参数：f : Ultrafilter α；hg : NeBot (g ⊓ f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ultrafilter.le_of_inf_neBot`：le_of_inf_neBot (f : Ultrafilter α) {g : Fi
lter α} (hg : NeBot (↑f ⊓ g)) : ↑f <= g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
-/
theorem le_of_inf_neBot' (f : Ultrafilter α) {g : Filter α} (hg : NeBot (g ⊓ f)) : ↑f ≤ g :=
  f.le_of_inf_neBot <| by rwa [inf_comm]
/-
**Ultrafilter.inf_neBot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：inf_neBot_iff {f : Ultrafilter α} {g : Filter α} : NeBot (↑f ⊓ g) ↔ ↑f <= 
g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ultrafilter.le_of_inf_neBot`：le_of_inf_neBot (f : Ultrafilter α) {g : Fi
lter α} (hg : NeBot (↑f ⊓ g)) : ↑f <= g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
-/
theorem inf_neBot_iff {f : Ultrafilter α} {g : Filter α} : NeBot (↑f ⊓ g) ↔ ↑f ≤ g :=
  ⟨le_of_inf_neBot f, fun h => (inf_of_le_left h).symm ▸ f.neBot⟩
/-
**Ultrafilter.disjoint_iff_not_le** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：disjoint_iff_not_le {f : Ultrafilter α} {g : Filter α} : Disjoint (↑f) g ↔
 ¬↑f <= g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ultrafilter.inf_neBot_iff`：inf_neBot_iff {f : Ultrafilter α} {g : Filter
 α} : NeBot (↑f ⊓ g) ↔ ↑f <= g
· 使用定理 `Filter.neBot_iff`：neBot_iff {f : Filter α} : NeBot f ↔ f != ⊥
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem disjoint_iff_not_le {f : Ultrafilter α} {g : Filter α} : Disjoint (↑f) g ↔ ¬↑f ≤ g := by
  rw [← inf_neBot_iff, neBot_iff, Ne, not_not, disjoint_iff]

@[simp]
/-
**Ultrafilter.compl_notMem_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：compl_notMem_iff : sᶜ ∉ f ↔ s in f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `Ultrafilter.le_of_inf_neBot`：le_of_inf_neBot (f : Ultrafilter α) {g : Fi
lter α} (hg : NeBot (↑f ⊓ g)) : ↑f <= g
· 使用定理 `Filter.mem_of_eq_bot`：mem_of_eq_bot {f : Filter α} {s : Set α} (h : f ⊓ 
𝓟 sᶜ = ⊥) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Filter.compl_notMem`：compl_notMem {f : Filter α} {s : Set α} [NeBot f] (
h : s in f) : sᶜ ∉ f
-/
theorem compl_notMem_iff : sᶜ ∉ f ↔ s ∈ f :=
  ⟨fun hsc =>
    le_principal_iff.1 <|
      f.le_of_inf_neBot ⟨fun h => hsc <| mem_of_eq_bot <| by rwa [compl_compl]⟩,
    compl_notMem⟩

@[simp]
/-
**Ultrafilter.frequently_iff_eventually** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：frequently_iff_eventually : (existsᶠ x in f, p x) ↔ forallᶠ x in f, p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ultrafilter.compl_notMem_iff`：compl_notMem_iff : sᶜ ∉ f ↔ s in f
-/
theorem frequently_iff_eventually : (∃ᶠ x in f, p x) ↔ ∀ᶠ x in f, p x :=
  compl_notMem_iff

alias ⟨_root_.Filter.Frequently.eventually, _⟩ := frequently_iff_eventually
/-
**Ultrafilter.compl_mem_iff_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：compl_mem_iff_notMem : sᶜ in f ↔ s ∉ f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ultrafilter.compl_notMem_iff`：compl_notMem_iff : sᶜ ∉ f ↔ s in f
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem compl_mem_iff_notMem : sᶜ ∈ f ↔ s ∉ f := by rw [← compl_notMem_iff, compl_compl]
/-
**Ultrafilter.sdiff_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：sdiff_mem_iff (f : Ultrafilter α) : s \ t in f ↔ s in f ∧ t ∉ f
参数：f : Ultrafilter α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.inter_mem_iff`：inter_mem_iff {s t : Set α} : s inter t in f ↔ s i
n f ∧ t in f
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Ultrafilter.compl_mem_iff_notMem`：compl_mem_iff_notMem : sᶜ in f ↔ s ∉ f
-/
theorem sdiff_mem_iff (f : Ultrafilter α) : s \ t ∈ f ↔ s ∈ f ∧ t ∉ f :=
  inter_mem_iff.trans <| and_congr Iff.rfl compl_mem_iff_notMem

@[deprecated (since := "2026-06-03")] alias diff_mem_iff := sdiff_mem_iff

/-- If `sᶜ ∉ f ↔ s ∈ f`, then `f` is an ultrafilter. The other implication is given by
`Ultrafilter.compl_notMem_iff`. -/
/-
**Ultrafilter.ofComplNotMemIff** 是 Mathlib 中的一个定义，位于命名空间 `Ultrafilter`。
形式化陈述：ofComplNotMemIff (f : Filter α) (h : forall s, sᶜ ∉ f ↔ s in f) : Ultrafil
ter α where toFilter
参数：f : Filter α；h : forall s, sᶜ ∉ f ↔ s in f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `sᶜ ∉ f ↔ s ∈ f`, then `f` is an ultrafilter. The other implication is given 
by
`Ultrafilter.compl_notMem_iff`.
-/
def ofComplNotMemIff (f : Filter α) (h : ∀ s, sᶜ ∉ f ↔ s ∈ f) : Ultrafilter α where
  toFilter := f
  neBot' := ⟨fun hf => by simp [hf] at h⟩
  le_of_le _ _ hgf s hs := (h s).1 fun hsc => compl_notMem hs (hgf hsc)

/-- If `f : Filter α` is an atom, then it is an ultrafilter. -/
/-
**Ultrafilter.ofAtom** 是 Mathlib 中的一个定义，位于命名空间 `Ultrafilter`。
形式化陈述：ofAtom (f : Filter α) (hf : IsAtom f) : Ultrafilter α where toFilter
参数：f : Filter α；hf : IsAtom f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : Filter α` is an atom, then it is an ultrafilter.
-/
def ofAtom (f : Filter α) (hf : IsAtom f) : Ultrafilter α where
  toFilter := f
  neBot' := ⟨hf.1⟩
  le_of_le g hg := (isAtom_iff_le_of_ge.1 hf).2 g hg.ne
/-
**Ultrafilter.nonempty_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：nonempty_of_mem (hs : s in f) : s.Nonempty
参数：hs : s in f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.nonempty_of_mem`：nonempty_of_mem {f : Filter α} [hf : NeBot f] {s
 : Set α} (hs : s in f) : s.Nonempty
-/
theorem nonempty_of_mem (hs : s ∈ f) : s.Nonempty :=
  Filter.nonempty_of_mem hs
/-
**Ultrafilter.ne_empty_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：ne_empty_of_mem (hs : s in f) : s != ∅
参数：hs : s in f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `Ultrafilter.nonempty_of_mem`：nonempty_of_mem (hs : s in f) : s.Nonempty
-/
theorem ne_empty_of_mem (hs : s ∈ f) : s ≠ ∅ :=
  (nonempty_of_mem hs).ne_empty

@[simp]
/-
**Ultrafilter.empty_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：empty_notMem : ∅ ∉ f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.empty_notMem`：empty_notMem (f : Filter α) [NeBot f] : ∅ ∉ f
-/
theorem empty_notMem : ∅ ∉ f :=
  Filter.empty_notMem (f : Filter α)

@[simp]
/-
**Ultrafilter.le_sup_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：le_sup_iff {u : Ultrafilter α} {f g : Filter α} : ↑u <= f ⊔ g ↔ ↑u <= f ∨ 
↑u <= g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem le_sup_iff {u : Ultrafilter α} {f g : Filter α} : ↑u ≤ f ⊔ g ↔ ↑u ≤ f ∨ ↑u ≤ g :=
  not_iff_not.1 <| by simp only [← disjoint_iff_not_le, not_or, disjoint_sup_right]

@[simp]
/-
**Ultrafilter.union_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：union_mem_iff : s union t in f ↔ s in f ∨ t in f
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
theorem union_mem_iff : s ∪ t ∈ f ↔ s ∈ f ∨ t ∈ f := by
  simp only [← mem_coe, ← le_principal_iff, ← sup_principal, le_sup_iff]
/-
**Ultrafilter.mem_or_compl_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：mem_or_compl_mem (f : Ultrafilter α) (s : Set α) : s in f ∨ sᶜ in f
参数：f : Ultrafilter α；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Ultrafilter.compl_mem_iff_notMem`：compl_mem_iff_notMem : sᶜ in f ↔ s ∉ f
-/
theorem mem_or_compl_mem (f : Ultrafilter α) (s : Set α) : s ∈ f ∨ sᶜ ∈ f :=
  or_iff_not_imp_left.2 compl_mem_iff_notMem.2
/-
**Ultrafilter.em** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：∀ {α : Type u} (f : Ultrafilter α) (p : α → Prop), (∀ᶠ (x : α) in ↑f, p x)
 ∨ ∀ᶠ (x : α) in ↑f, ¬p x
参数：f : Ultrafilter α；p : α → Prop；∀ᶠ (x : α) in ↑f, p x；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ultrafilter.mem_or_compl_mem`：mem_or_compl_mem (f : Ultrafilter α) (s : 
Set α) : s in f ∨ sᶜ in f
-/
protected theorem em (f : Ultrafilter α) (p : α → Prop) : (∀ᶠ x in f, p x) ∨ ∀ᶠ x in f, ¬p x :=
  f.mem_or_compl_mem { x | p x }
/-
**Ultrafilter.eventually_or** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：eventually_or : (forallᶠ x in f, p x ∨ q x) ↔ (forallᶠ x in f, p x) ∨ fora
llᶠ x in f, q x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ultrafilter.union_mem_iff`：union_mem_iff : s union t in f ↔ s in f ∨ t i
n f
-/
theorem eventually_or : (∀ᶠ x in f, p x ∨ q x) ↔ (∀ᶠ x in f, p x) ∨ ∀ᶠ x in f, q x :=
  union_mem_iff

@[push ← high] -- higher priority than `Filter.not_eventually`
/-
**Ultrafilter.eventually_not** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：eventually_not : (forallᶠ x in f, ¬p x) ↔ ¬forallᶠ x in f, p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ultrafilter.compl_mem_iff_notMem`：compl_mem_iff_notMem : sᶜ in f ↔ s ∉ f
-/
theorem eventually_not : (∀ᶠ x in f, ¬p x) ↔ ¬∀ᶠ x in f, p x :=
  compl_mem_iff_notMem
/-
**Ultrafilter.eventually_imp** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：eventually_imp : (forallᶠ x in f, p x -> q x) ↔ (forallᶠ x in f, p x) -> f
orallᶠ x in f, q x
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eventually_imp : (∀ᶠ x in f, p x → q x) ↔ (∀ᶠ x in f, p x) → ∀ᶠ x in f, q x := by
  simp only [imp_iff_not_or, eventually_or, eventually_not]

/-- Pushforward for ultrafilters. -/
nonrec def map (m : α → β) (f : Ultrafilter α) : Ultrafilter β :=
  ofComplNotMemIff (map m f) fun s => @compl_notMem_iff _ f (m ⁻¹' s)

@[simp, norm_cast]
/-
**Ultrafilter.coe_map** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：coe_map (m : α -> β) (f : Ultrafilter α) : (map m f : Filter β) = Filter.m
ap m ↑f
参数：m : α -> β；f : Ultrafilter α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_map (m : α → β) (f : Ultrafilter α) : (map m f : Filter β) = Filter.map m ↑f :=
  rfl

@[simp]
/-
**Ultrafilter.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：mem_map {m : α -> β} {f : Ultrafilter α} {s : Set β} : s in map m f ↔ m ⁻¹
' s in f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_map {m : α → β} {f : Ultrafilter α} {s : Set β} : s ∈ map m f ↔ m ⁻¹' s ∈ f :=
  Iff.rfl

@[simp]
nonrec theorem map_id (f : Ultrafilter α) : f.map id = f :=
  coe_injective map_id

@[simp]
/-
**Ultrafilter.map_id'** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：map_id' (f : Ultrafilter α) : (f.map fun x => x) = f
参数：f : Ultrafilter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ultrafilter.map_id`：∀ {α : Type u} (f : Ultrafilter α), Ultrafilter.map 
id f = f
-/
theorem map_id' (f : Ultrafilter α) : (f.map fun x => x) = f :=
  map_id _

@[simp]
nonrec theorem map_map (f : Ultrafilter α) (m : α → β) (n : β → γ) :
    (f.map m).map n = f.map (n ∘ m) :=
  coe_injective map_map

/-- The pullback of an ultrafilter along an injection whose range is large with respect to the given
ultrafilter. -/
nonrec def comap {m : α → β} (u : Ultrafilter β) (inj : Injective m) (large : Set.range m ∈ u) :
    Ultrafilter α where
  toFilter := comap m u
  neBot' := u.neBot'.comap_of_range_mem large
  le_of_le g hg hgu := by
    simp only [← u.unique (map_le_iff_le_comap.2 hgu), comap_map inj, le_rfl]

@[simp]
/-
**Ultrafilter.mem_comap** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：mem_comap {m : α -> β} (u : Ultrafilter β) (inj : Injective m) (large : Se
t.range m in u) {s : Set α} : s in u.comap inj large ↔ m '' s in u
参数：u : Ultrafilter β；inj : Injective m；large : Set.range m in u。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_comap_iff`：mem_comap_iff {f : Filter β} {m : α -> β} (inj : I
njective m) (large : Set.range m in f) {S : Set α} : S in comap m f ↔ m '' S in 
f
-/
theorem mem_comap {m : α → β} (u : Ultrafilter β) (inj : Injective m) (large : Set.range m ∈ u)
    {s : Set α} : s ∈ u.comap inj large ↔ m '' s ∈ u :=
  mem_comap_iff inj large

@[simp, norm_cast]
/-
**Ultrafilter.coe_comap** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：coe_comap {m : α -> β} (u : Ultrafilter β) (inj : Injective m) (large : Se
t.range m in u) : (u.comap inj large : Filter α) = Filter.comap m u
参数：u : Ultrafilter β；inj : Injective m；large : Set.range m in u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comap {m : α → β} (u : Ultrafilter β) (inj : Injective m) (large : Set.range m ∈ u) :
    (u.comap inj large : Filter α) = Filter.comap m u :=
  rfl

@[simp]
nonrec theorem comap_id (f : Ultrafilter α) (h₀ : Injective (id : α → α) := injective_id)
    (h₁ : range id ∈ f := (by rw [range_id]; exact univ_mem)) :
    f.comap h₀ h₁ = f :=
  coe_injective comap_id

@[simp]
nonrec theorem comap_comap (f : Ultrafilter γ) {m : α → β} {n : β → γ} (inj₀ : Injective n)
    (large₀ : range n ∈ f) (inj₁ : Injective m) (large₁ : range m ∈ f.comap inj₀ large₀)
    (inj₂ : Injective (n ∘ m) := inj₀.comp inj₁)
    (large₂ : range (n ∘ m) ∈ f :=
      (by rw [range_comp]; exact image_mem_of_mem_comap large₀ large₁)) :
    (f.comap inj₀ large₀).comap inj₁ large₁ = f.comap inj₂ large₂ :=
  coe_injective comap_comap

/-- The principal ultrafilter associated to a point `x`. -/
/-
**Ultrafilter.** 是 Mathlib 中的一个实例，位于命名空间 `Ultrafilter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The principal ultrafilter associated to a point `x`.
-/
instance : Pure Ultrafilter :=
  ⟨fun a => ofComplNotMemIff (pure a) fun s => by simp⟩

@[simp]
/-
**Ultrafilter.mem_pure** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：mem_pure {a : α} {s : Set α} : s in (pure a : Ultrafilter α) ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_pure {a : α} {s : Set α} : s ∈ (pure a : Ultrafilter α) ↔ a ∈ s :=
  Iff.rfl

@[simp]
/-
**Ultrafilter.coe_pure** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：coe_pure (a : α) : ↑(pure a : Ultrafilter α) = (pure a : Filter α)
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pure (a : α) : ↑(pure a : Ultrafilter α) = (pure a : Filter α) :=
  rfl

@[simp]
/-
**Ultrafilter.map_pure** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：map_pure (m : α -> β) (a : α) : map m (pure a) = pure (m a)
参数：m : α -> β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_pure (m : α → β) (a : α) : map m (pure a) = pure (m a) :=
  rfl

@[simp]
/-
**Ultrafilter.comap_pure** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：comap_pure {m : α -> β} (a : α) (inj : Injective m) (large) : comap (pure 
<| m a) inj large = pure a
参数：a : α；inj : Injective m；large。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ultrafilter.coe_injective`：∀ {α : Type u}, Function.Injective Ultrafilte
r.toFilter
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.comap_pure`：comap_pure {b : β} : comap m (pure b) = 𝓟 (m ⁻¹' {b})
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ultrafilter.coe_pure`：coe_pure (a : α) : ↑(pure a : Ultrafilter α) = (pu
re a : Filter α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.principal_singleton`：principal_singleton (a : α) : 𝓟 {a} = pure a
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
-/
theorem comap_pure {m : α → β} (a : α) (inj : Injective m) (large) :
    comap (pure <| m a) inj large = pure a :=
  coe_injective <|
    Filter.comap_pure.trans <| by
      rw [coe_pure, ← principal_singleton, ← image_singleton, preimage_image_eq _ inj]
/-
**Ultrafilter.pure_injective** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：pure_injective : Injective (pure : α -> Ultrafilter α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.pure_injective`：pure_injective : Injective (pure : α -> Filter α)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem pure_injective : Injective (pure : α → Ultrafilter α) := fun _ _ h =>
  Filter.pure_injective (congr_arg Ultrafilter.toFilter h :)
/-
**Ultrafilter.** 是 Mathlib 中的一个实例，位于命名空间 `Ultrafilter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited α] : Inhabited (Ultrafilter α) :=
  ⟨pure default⟩
/-
**Ultrafilter.** 是 Mathlib 中的一个实例，位于命名空间 `Ultrafilter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty α] : Nonempty (Ultrafilter α) :=
  Nonempty.map pure inferInstance

/-- Monadic bind for ultrafilters, coming from the one on filters
defined in terms of map and join. -/
/-
**Ultrafilter.bind** 是 Mathlib 中的一个定义，位于命名空间 `Ultrafilter`。
形式化陈述：bind (f : Ultrafilter α) (m : α -> Ultrafilter β) : Ultrafilter β
参数：f : Ultrafilter α；m : α -> Ultrafilter β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Monadic bind for ultrafilters, coming from the one on filters
defined in terms of map and join.
-/
def bind (f : Ultrafilter α) (m : α → Ultrafilter β) : Ultrafilter β :=
  ofComplNotMemIff (Filter.bind ↑f fun x => ↑(m x)) fun s => by
    simp only [mem_bind', mem_coe, ← compl_mem_iff_notMem, compl_ofPred, compl_compl]
/-
**Ultrafilter.instBind** 是 Mathlib 中的一个实例，位于命名空间 `Ultrafilter`。
形式化陈述：instBind : Bind Ultrafilter
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instBind : Bind Ultrafilter :=
  ⟨@Ultrafilter.bind⟩
/-
**Ultrafilter.functor** 是 Mathlib 中的一个实例，位于命名空间 `Ultrafilter`。
形式化陈述：functor : Functor Ultrafilter where map
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance functor : Functor Ultrafilter where map := @Ultrafilter.map
/-
**Ultrafilter.monad** 是 Mathlib 中的一个实例，位于命名空间 `Ultrafilter`。
形式化陈述：monad : Monad Ultrafilter where map
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance monad : Monad Ultrafilter where map := @Ultrafilter.map

section

attribute [local instance] Filter.monad Filter.lawfulMonad

/-
**Ultrafilter.lawfulMonad** 是 Mathlib 中的一个实例，位于命名空间 `Ultrafilter`。
形式化陈述：lawfulMonad : LawfulMonad Ultrafilter where id_map f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Ultrafilter.coe_injective`：∀ {α : Type u}, Function.Injective Ultrafilte
r.toFilter
· 使用定理 `LawfulFunctor.id_map`：∀ {f : Type u → Type v} {inst : Functor f} [self :
 LawfulFunctor f] {α : Type u} (x : f α), id <$> x = x
· 使用定理 `Filter.instLawfulFunctor`：LawfulFunctor Filter
· 使用定理 `LawfulMonad.bind_pure_comp`：∀ {m : Type u → Type v} {inst : Monad m} [se
lf : LawfulMonad m] {α β : Type u} (f : α → β) (x : m α),   (do       let a ← x 
      pure (f a)…
· 使用定理 `Filter.lawfulMonad`：LawfulMonad Filter
· 使用定理 `Filter.pure_bind`：pure_bind (a : α) (m : α -> Filter β) : bind (pure a) 
m = m a
· 使用定理 `Filter.filter_eq`：∀ {α : Type u_1} {f g : Filter α}, f.sets = g.sets → f
 = g
-/
instance lawfulMonad : LawfulMonad Ultrafilter where
  id_map f := coe_injective (id_map f.toFilter)
  pure_bind a f := coe_injective (Filter.pure_bind a ((Ultrafilter.toFilter) ∘ f))
  bind_assoc _ _ _ := coe_injective (filter_eq rfl)
  bind_pure_comp f x := coe_injective (bind_pure_comp f x.1)
  map_const := rfl
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  pure_seq _ _ := rfl
  bind_map _ _ := rfl

end

/-- The ultrafilter lemma: Any proper filter is contained in an ultrafilter. -/
/-
**Ultrafilter.exists_le** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：exists_le (f : Filter α) [h : NeBot f] : exists u : Ultrafilter α, ↑u <= f
参数：f : Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `IsAtomic.eq_bot_or_exists_atom_le`：∀ {α : Type u_2} {inst : PartialOrder
 α} {inst_1 : OrderBot α} [self : IsAtomic α] (b : α),   b = ⊥ ∨ ∃ a, IsAtom a ∧
 a ≤ b
· 使用定理 `instIsAtomicFilter`：∀ {α : Type u}, IsAtomic (Filter α)
· 使用定理 `Filter.NeBot.ne`：∀ {α : Type u} {f : Filter α}, f.NeBot → f ≠ ⊥

--- 原说明 ---
The ultrafilter lemma: Any proper filter is contained in an ultrafilter.
-/
theorem exists_le (f : Filter α) [h : NeBot f] : ∃ u : Ultrafilter α, ↑u ≤ f :=
  let ⟨u, hu, huf⟩ := (eq_bot_or_exists_atom_le f).resolve_left h.ne
  ⟨ofAtom u hu, huf⟩

alias _root_.Filter.exists_ultrafilter_le := exists_le

/-- Construct an ultrafilter extending a given filter.
  The ultrafilter lemma is the assertion that such a filter exists;
  we use the axiom of choice to pick one. -/
/-
**Ultrafilter.of** 是 Mathlib 中的一个定义，位于命名空间 `Ultrafilter`。
形式化陈述：of (f : Filter α) [NeBot f] : Ultrafilter α
参数：f : Filter α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ultrafilter.exists_le`：exists_le (f : Filter α) [h : NeBot f] : exists u
 : Ultrafilter α, ↑u <= f

--- 原说明 ---
Construct an ultrafilter extending a given filter.
  The ultrafilter lemma is the assertion that such a filter exists;
  we use the axiom of choice to pick one.
-/
noncomputable def of (f : Filter α) [NeBot f] : Ultrafilter α :=
  Classical.choose (exists_le f)
/-
**Ultrafilter.of_le** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：of_le (f : Filter α) [NeBot f] : ↑(of f) <= f
参数：f : Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Ultrafilter.exists_le`：exists_le (f : Filter α) [h : NeBot f] : exists u
 : Ultrafilter α, ↑u <= f
-/
theorem of_le (f : Filter α) [NeBot f] : ↑(of f) ≤ f :=
  Classical.choose_spec (exists_le f)
/-
**Ultrafilter.of_coe** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：of_coe (f : Ultrafilter α) : of ↑f = f
参数：f : Ultrafilter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ultrafilter.coe_inj`：coe_inj : (f : Filter α) = g ↔ f = g
· 使用定理 `Ultrafilter.unique`：unique (f : Ultrafilter α) {g : Filter α} (h : g <= 
f) (hne : NeBot g
· 使用定理 `Ultrafilter.of_le`：of_le (f : Filter α) [NeBot f] : ↑(of f) <= f
-/
theorem of_coe (f : Ultrafilter α) : of ↑f = f :=
  coe_inj.1 <| f.unique (of_le f.toFilter)

end Ultrafilter

namespace Filter

variable {f : Filter α} {s : Set α} {a : α}

open Ultrafilter

/-
**Filter.isAtom_pure** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：isAtom_pure : IsAtom (pure a : Filter α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ultrafilter.isAtom`：∀ {α : Type u} (f : Ultrafilter α), IsAtom ↑f
-/
theorem isAtom_pure : IsAtom (pure a : Filter α) :=
  (pure a : Ultrafilter α).isAtom
/-
**Filter.NeBot.le_pure_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter.NeBot`。
形式化陈述：∀ {α : Type u} {f : Filter α} {a : α}, f.NeBot → (f ≤ pure a ↔ f = pure a)
参数：f ≤ pure a ↔ f = pure a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ultrafilter.unique`：unique (f : Ultrafilter α) {g : Filter α} (h : g <= 
f) (hne : NeBot g
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
protected theorem NeBot.le_pure_iff (hf : f.NeBot) : f ≤ pure a ↔ f = pure a :=
  ⟨Ultrafilter.unique (pure a), le_of_eq⟩
/-
**Filter.NeBot.eq_pure_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter.NeBot`。
形式化陈述：∀ {α : Type u} {f : Filter α}, f.NeBot → ∀ {x : α}, f = pure x ↔ {x} ∈ f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.NeBot.le_pure_iff`：∀ {α : Type u} {f : Filter α} {a : α}, f.NeBot
 → (f ≤ pure a ↔ f = pure a)
· 使用定理 `Filter.le_pure_iff`：le_pure_iff {f : Filter α} {a : α} : f <= pure a ↔ {
a} in f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem NeBot.eq_pure_iff (hf : f.NeBot) {x : α} :
    f = pure x ↔ {x} ∈ f := by
  rw [← hf.le_pure_iff, le_pure_iff]

@[simp]
/-
**Filter.lt_pure_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：lt_pure_iff : f < pure a ↔ f = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAtom.lt_iff`：IsAtom.lt_iff (h : IsAtom a) : x < a ↔ x = ⊥
· 使用定理 `Filter.isAtom_pure`：isAtom_pure : IsAtom (pure a : Filter α)
-/
theorem lt_pure_iff : f < pure a ↔ f = ⊥ :=
  isAtom_pure.lt_iff
/-
**Filter.le_pure_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：le_pure_iff' : f <= pure a ↔ f = ⊥ ∨ f = pure a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAtom.le_iff`：IsAtom.le_iff (h : IsAtom a) : x <= a ↔ x = ⊥ ∨ x = a
· 使用定理 `Filter.isAtom_pure`：isAtom_pure : IsAtom (pure a : Filter α)
-/
theorem le_pure_iff' : f ≤ pure a ↔ f = ⊥ ∨ f = pure a :=
  isAtom_pure.le_iff

@[simp]
/-
**Filter.Iic_pure** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：Iic_pure (a : α) : Iic (pure a : Filter α) = {⊥, pure a}
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAtom.Iic_eq`：IsAtom.Iic_eq (h : IsAtom a) : Set.Iic a = {⊥, a}
· 使用定理 `Filter.isAtom_pure`：isAtom_pure : IsAtom (pure a : Filter α)
-/
theorem Iic_pure (a : α) : Iic (pure a : Filter α) = {⊥, pure a} :=
  isAtom_pure.Iic_eq
/-
**Filter.mem_iff_ultrafilter** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_iff_ultrafilter : s in f ↔ forall g : Ultrafilter α, ↑g <= f -> s in g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.comap_neBot_iff_compl_range`：comap_neBot_iff_compl_range {f : Fil
ter β} {m : α -> β} : NeBot (comap m f) ↔ (range m)ᶜ ∉ f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.preimage_coe_compl'`：preimage_coe_compl' (s : Set α) : (fun x : 
(sᶜ : Set α) => (x : α)) ⁻¹' s = ∅
· 使用定理 `Filter.map_le_iff_le_comap`：map_le_iff_le_comap : map m f <= g ↔ f <= co
map m g
· 使用定理 `Ultrafilter.of_le`：of_le (f : Filter α) [NeBot f] : ↑(of f) <= f
-/
theorem mem_iff_ultrafilter : s ∈ f ↔ ∀ g : Ultrafilter α, ↑g ≤ f → s ∈ g := by
  refine ⟨fun hf g hg => hg hf, fun H => by_contra fun hf => ?_⟩
  set g : Filter (sᶜ : Set α) := comap (↑) f
  have : NeBot g := comap_neBot_iff_compl_range.2 (by simpa [compl_ofPred])
  simpa using H ((of g).map (↑)) (map_le_iff_le_comap.mpr (of_le g))
/-
**Filter.le_iff_ultrafilter** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：le_iff_ultrafilter {f₁ f₂ : Filter α} : f₁ <= f₂ ↔ forall g : Ultrafilter 
α, ↑g <= f₁ -> ↑g <= f₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.mem_iff_ultrafilter`：mem_iff_ultrafilter : s in f ↔ forall g : Ul
trafilter α, ↑g <= f -> s in g
-/
theorem le_iff_ultrafilter {f₁ f₂ : Filter α} : f₁ ≤ f₂ ↔ ∀ g : Ultrafilter α, ↑g ≤ f₁ → ↑g ≤ f₂ :=
  ⟨fun h _ h₁ => h₁.trans h, fun h _ hs => mem_iff_ultrafilter.2 fun g hg => h g hg hs⟩

/-- A filter equals the intersection of all the ultrafilters which contain it. -/
/-
**Filter.iSup_ultrafilter_le_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：iSup_ultrafilter_le_eq (f : Filter α) : ⨆ (g : Ultrafilter α) (_ : g <= f)
, (g : Filter α) = f
参数：f : Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A filter equals the intersection of all the ultrafilters which contain it.
-/
theorem iSup_ultrafilter_le_eq (f : Filter α) :
    ⨆ (g : Ultrafilter α) (_ : g ≤ f), (g : Filter α) = f :=
  eq_of_forall_ge_iff fun f' => by simp only [iSup_le_iff, ← le_iff_ultrafilter]
/-
**Filter.exists_ultrafilter_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：exists_ultrafilter_iff {f : Filter α} : (exists u : Ultrafilter α, ↑u <= f
) ↔ NeBot f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.neBot_of_le`：neBot_of_le {f g : Filter α} [hf : NeBot f] (hg : f 
<= g) : NeBot g
· 使用定理 `Filter.exists_ultrafilter_le`：∀ {α : Type u} (f : Filter α) [h : f.NeBot
], ∃ u, ↑u ≤ f
-/
theorem exists_ultrafilter_iff {f : Filter α} : (∃ u : Ultrafilter α, ↑u ≤ f) ↔ NeBot f :=
  ⟨fun ⟨_, uf⟩ => neBot_of_le uf, fun h => @exists_ultrafilter_le _ _ h⟩
/-
**Filter.forall_neBot_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：forall_neBot_le_iff {g : Filter α} {p : Filter α -> Prop} (hp : Monotone p
) : (forall f : Filter α, NeBot f -> f <= g -> p f) ↔ forall f : Ultrafilter α, 
↑f <= g -> p f
参数：hp : Monotone p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ultrafilter.of_le`：of_le (f : Filter α) [NeBot f] : ↑(of f) <= f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem forall_neBot_le_iff {g : Filter α} {p : Filter α → Prop} (hp : Monotone p) :
    (∀ f : Filter α, NeBot f → f ≤ g → p f) ↔ ∀ f : Ultrafilter α, ↑f ≤ g → p f := by
  refine ⟨fun H f hf => H f f.neBot hf, ?_⟩
  intro H f hf hfg
  exact hp (of_le f) (H _ ((of_le f).trans hfg))

end Filter

namespace Ultrafilter

variable {m : α → β} {s : Set α} {g : Ultrafilter β}

/-
**Ultrafilter.comap_inf_principal_neBot_of_image_mem** 是 Mathlib 中的一个定理，位于命名空间 `
Ultrafilter`。
形式化陈述：comap_inf_principal_neBot_of_image_mem (h : m '' s in g) : (Filter.comap m
 g ⊓ 𝓟 s).NeBot
参数：h : m '' s in g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.comap_inf_principal_neBot_of_image_mem`：comap_inf_principal_neBot
_of_image_mem {f : Filter β} {m : α -> β} (hf : NeBot f) {s : Set α} (hs : m '' 
s in f) : NeBot (comap m f ⊓ 𝓟 s)
-/
theorem comap_inf_principal_neBot_of_image_mem (h : m '' s ∈ g) : (Filter.comap m g ⊓ 𝓟 s).NeBot :=
  Filter.comap_inf_principal_neBot_of_image_mem g.neBot h

/-- Ultrafilter extending the inf of a comapped ultrafilter and a principal ultrafilter. -/
/-
**Ultrafilter.ofComapInfPrincipal** 是 Mathlib 中的一个定义，位于命名空间 `Ultrafilter`。
形式化陈述：ofComapInfPrincipal (h : m '' s in g) : Ultrafilter α
参数：h : m '' s in g。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ultrafilter.comap_inf_principal_neBot_of_image_mem`：comap_inf_principal_
neBot_of_image_mem (h : m '' s in g) : (Filter.comap m g ⊓ 𝓟 s).NeBot

--- 原说明 ---
Ultrafilter extending the inf of a comapped ultrafilter and a principal ultrafil
ter.
-/
noncomputable def ofComapInfPrincipal (h : m '' s ∈ g) : Ultrafilter α :=
  @of _ (Filter.comap m g ⊓ 𝓟 s) (comap_inf_principal_neBot_of_image_mem h)
/-
**Ultrafilter.ofComapInfPrincipal_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：ofComapInfPrincipal_mem (h : m '' s in g) : s in ofComapInfPrincipal h
参数：h : m '' s in g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ultrafilter.comap_inf_principal_neBot_of_image_mem`：comap_inf_principal_
neBot_of_image_mem (h : m '' s in g) : (Filter.comap m g ⊓ 𝓟 s).NeBot
· 使用定理 `Filter.mem_inf_of_right`：mem_inf_of_right {f g : Filter α} {s : Set α} (
h : s in g) : s in f ⊓ g
· 使用定理 `Filter.mem_principal_self`：mem_principal_self (s : Set α) : s in 𝓟 s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.le_def`：le_def : f <= g ↔ forall x in g, x in f
· 使用定理 `Ultrafilter.of_le`：of_le (f : Filter α) [NeBot f] : ↑(of f) <= f
-/
theorem ofComapInfPrincipal_mem (h : m '' s ∈ g) : s ∈ ofComapInfPrincipal h := by
  let f := Filter.comap m g ⊓ 𝓟 s
  have : f.NeBot := comap_inf_principal_neBot_of_image_mem h
  have : s ∈ f := mem_inf_of_right (mem_principal_self s)
  exact le_def.mp (of_le _) s this
/-
**Ultrafilter.ofComapInfPrincipal_eq_of_map** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilt
er`。
形式化陈述：ofComapInfPrincipal_eq_of_map (h : m '' s in g) : (ofComapInfPrincipal h).
map m = g
参数：h : m '' s in g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ultrafilter.comap_inf_principal_neBot_of_image_mem`：comap_inf_principal_
neBot_of_image_mem (h : m '' s in g) : (Filter.comap m g ⊓ 𝓟 s).NeBot
· 使用定理 `Ultrafilter.eq_of_le`：eq_of_le {f g : Ultrafilter α} (h : (f : Filter α)
 <= g) : f = g
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
· 使用定理 `Ultrafilter.of_le`：of_le (f : Filter α) [NeBot f] : ↑(of f) <= f
· 使用定理 `Filter.map_inf_le`：map_inf_le {f g : Filter α} {m : α -> β} : map m (f ⊓
 g) <= map m f ⊓ map m g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_principal`：map_principal {s : Set α} {f : α -> β} : map f (𝓟 
s) = 𝓟 (Set.image f s)
· 使用定理 `inf_le_inf_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α} (c 
: α), b ≤ a → b ⊓ c ≤ a ⊓ c
· 使用定理 `Filter.map_comap_le`：map_comap_le : map m (comap m g) <= g
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
-/
theorem ofComapInfPrincipal_eq_of_map (h : m '' s ∈ g) : (ofComapInfPrincipal h).map m = g := by
  let f := Filter.comap m g ⊓ 𝓟 s
  have : f.NeBot := comap_inf_principal_neBot_of_image_mem h
  apply eq_of_le
  calc
    Filter.map m (of f) ≤ Filter.map m f := map_mono (of_le _)
    _ ≤ (Filter.map m <| Filter.comap m g) ⊓ Filter.map m (𝓟 s) := map_inf_le
    _ = (Filter.map m <| Filter.comap m g) ⊓ (𝓟 <| m '' s) := by rw [map_principal]
    _ ≤ ↑g ⊓ (𝓟 <| m '' s) := inf_le_inf_right _ map_comap_le
    _ = ↑g := inf_of_le_left (le_principal_iff.mpr h)
/-
**Ultrafilter.eq_of_le_pure** 是 Mathlib 中的一个定理，位于命名空间 `Ultrafilter`。
形式化陈述：eq_of_le_pure {X : Type _} {α : Filter X} (hα : α.NeBot) {x y : X} (hx : α
 <= pure x) (hy : α <= pure y) : x = y
参数：hα : α.NeBot；hx : α <= pure x；hy : α <= pure y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.pure_injective`：pure_injective : Injective (pure : α -> Filter α)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.NeBot.le_pure_iff`：∀ {α : Type u} {f : Filter α} {a : α}, f.NeBot
 → (f ≤ pure a ↔ f = pure a)
-/
theorem eq_of_le_pure {X : Type _} {α : Filter X} (hα : α.NeBot) {x y : X}
    (hx : α ≤ pure x) (hy : α ≤ pure y) : x = y :=
  Filter.pure_injective (hα.le_pure_iff.mp hx ▸ hα.le_pure_iff.mp hy)

end Ultrafilter

