/-
Copyright (c) 2018 Rohan Mitta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Mitta, Kevin Buzzard, Alistair Tucker, Johannes Hölzl, Yury Kudryashov, Winston Yin
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Tactic.Finiteness
public import Mathlib.Topology.EMetricSpace.Diam

/-!
# Lipschitz continuous functions

A map `f : α → β` between two (extended) metric spaces is called *Lipschitz continuous*
with constant `K ≥ 0` if for all `x, y` we have `edist (f x) (f y) ≤ K * edist x y`.
For a metric space, the latter inequality is equivalent to `dist (f x) (f y) ≤ K * dist x y`.
There is also a version asserting this inequality only for `x` and `y` in some set `s`.
Finally, `f : α → β` is called *locally Lipschitz continuous* if each `x : α` has a neighbourhood
on which `f` is Lipschitz continuous (with some constant).

In this file we provide various ways to prove that various combinations of Lipschitz continuous
functions are Lipschitz continuous. We also prove that Lipschitz continuous functions are
uniformly continuous, and that locally Lipschitz functions are continuous.

## Main definitions and lemmas

* `LipschitzWith K f`: states that `f` is Lipschitz with constant `K : ℝ≥0`
* `LipschitzOnWith K f s`: states that `f` is Lipschitz with constant `K : ℝ≥0` on a set `s`
* `LipschitzWith.uniformContinuous`: a Lipschitz function is uniformly continuous
* `LipschitzOnWith.uniformContinuousOn`: a function which is Lipschitz on a set `s` is uniformly
  continuous on `s`.
* `LocallyLipschitz f`: states that `f` is locally Lipschitz
* `LocallyLipschitzOn f s`: states that `f` is locally Lipschitz on `s`.
* `LocallyLipschitz.continuous`: a locally Lipschitz function is continuous.


## Implementation notes

The parameter `K` has type `ℝ≥0`. This way we avoid conjunction in the definition and have
coercions both to `ℝ` and `ℝ≥0∞`. Constructors whose names end with `'` take `K : ℝ` as an
argument, and return `LipschitzWith (Real.toNNReal K) f`.
-/

@[expose] public section

universe u v w x

open Filter Function Set Topology NNReal ENNReal Bornology

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Type x}

section PseudoEMetricSpace
variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] {K : ℝ≥0} {s t : Set α} {f : α → β}

/-- A function `f` is **Lipschitz continuous** with constant `K ≥ 0` if for all `x, y`
we have `dist (f x) (f y) ≤ K * dist x y`. -/
/-
**LipschitzWith** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LipschitzWith (K : Real>=0) (f : α -> β)
参数：K : Real>=0；f : α -> β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` is **Lipschitz continuous** with constant `K ≥ 0` if for all `x, 
y`
we have `dist (f x) (f y) ≤ K * dist x y`.
-/
def LipschitzWith (K : ℝ≥0) (f : α → β) := ∀ x y, edist (f x) (f y) ≤ K * edist x y

/-- A function `f` is **Lipschitz continuous** with constant `K ≥ 0` **on `s`** if
for all `x, y` in `s` we have `dist (f x) (f y) ≤ K * dist x y`. -/
/-
**LipschitzOnWith** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LipschitzOnWith (K : Real>=0) (f : α -> β) (s : Set α)
参数：K : Real>=0；f : α -> β；s : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` is **Lipschitz continuous** with constant `K ≥ 0` **on `s`** if
for all `x, y` in `s` we have `dist (f x) (f y) ≤ K * dist x y`.
-/
def LipschitzOnWith (K : ℝ≥0) (f : α → β) (s : Set α) :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → edist (f x) (f y) ≤ K * edist x y

/-- `f : α → β` is called **locally Lipschitz continuous** iff every point `x`
has a neighbourhood on which `f` is Lipschitz. -/
/-
**LocallyLipschitz** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LocallyLipschitz (f : α -> β) : Prop
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f : α → β` is called **locally Lipschitz continuous** iff every point `x`
has a neighbourhood on which `f` is Lipschitz.
-/
def LocallyLipschitz (f : α → β) : Prop := ∀ x, ∃ K, ∃ t ∈ 𝓝 x, LipschitzOnWith K f t

/-- `f : α → β` is called **locally Lipschitz continuous** on `s` iff every point `x` of `s`
has a neighbourhood within `s` on which `f` is Lipschitz. -/
/-
**LocallyLipschitzOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LocallyLipschitzOn (s : Set α) (f : α -> β) : Prop
参数：s : Set α；f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f : α → β` is called **locally Lipschitz continuous** on `s` iff every point `x
` of `s`
has a neighbourhood within `s` on which `f` is Lipschitz.
-/
def LocallyLipschitzOn (s : Set α) (f : α → β) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∃ K, ∃ t ∈ 𝓝[s] x, LipschitzOnWith K f t

/-- Every function is Lipschitz on the empty set (with any Lipschitz constant). -/
@[simp]
/-
**lipschitzOnWith_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lipschitzOnWith_empty (K : Real>=0) (f : α -> β) : LipschitzOnWith K f ∅
参数：K : Real>=0；f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every function is Lipschitz on the empty set (with any Lipschitz constant).
-/
theorem lipschitzOnWith_empty (K : ℝ≥0) (f : α → β) : LipschitzOnWith K f ∅ := fun _ => False.elim
/-
**locallyLipschitzOn_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [inst_1 : Pseudo
EMetricSpace β] (f : α → β),   LocallyLipschitzOn ∅ f
参数：f : α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma locallyLipschitzOn_empty (f : α → β) : LocallyLipschitzOn ∅ f := fun _ ↦ False.elim

/-- Being Lipschitz on a set is monotone w.r.t. that set. -/
/-
**LipschitzOnWith.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LipschitzOnWith.mono (hf : LipschitzOnWith K f t) (h : s subseteq t) : Lip
schitzOnWith K f s
参数：hf : LipschitzOnWith K f t；h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Being Lipschitz on a set is monotone w.r.t. that set.
-/
theorem LipschitzOnWith.mono (hf : LipschitzOnWith K f t) (h : s ⊆ t) : LipschitzOnWith K f s :=
  fun _x x_in _y y_in => hf (h x_in) (h y_in)
/-
**LocallyLipschitzOn.mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LocallyLipschitzOn.mono (hf : LocallyLipschitzOn t f) (h : s subseteq t) :
 LocallyLipschitzOn s f
参数：hf : LocallyLipschitzOn t f；h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
-/
lemma LocallyLipschitzOn.mono (hf : LocallyLipschitzOn t f) (h : s ⊆ t) : LocallyLipschitzOn s f :=
  fun x hx ↦ by obtain ⟨K, u, hu, hfu⟩ := hf (h hx); exact ⟨K, u, nhdsWithin_mono _ h hu, hfu⟩

/-- `f` is Lipschitz iff it is Lipschitz on the entire space. -/
/-
**lipschitzOnWith_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [inst_1 : Pseudo
EMetricSpace β] {K : NNReal} {f : α → β},   LipschitzOnWith K f Set.univ ↔ Lipsc
hitzWith K f
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`f` is Lipschitz iff it is Lipschitz on the entire space.
-/
@[simp] lemma lipschitzOnWith_univ : LipschitzOnWith K f univ ↔ LipschitzWith K f := by
  simp [LipschitzOnWith, LipschitzWith]
/-
**locallyLipschitzOn_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [inst_1 : Pseudo
EMetricSpace β] {f : α → β},   LocallyLipschitzOn Set.univ f ↔ LocallyLipschitz 
f
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma locallyLipschitzOn_univ : LocallyLipschitzOn univ f ↔ LocallyLipschitz f := by
  simp [LocallyLipschitzOn, LocallyLipschitz]
/-
**LocallyLipschitz.locallyLipschitzOn** 是 Mathlib 中的一个定理，位于命名空间 `LocallyLipschit
z`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [inst_1 : Pseudo
EMetricSpace β] {s : Set α} {f : α → β},   LocallyLipschitz f → LocallyLipschitz
On s f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LocallyLipschitzOn.mono`：LocallyLipschitzOn.mono (hf : LocallyLipschitzO
n t f) (h : s subseteq t) : LocallyLipschitzOn s f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `locallyLipschitzOn_univ`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetr
icSpace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   LocallyLipschitzOn Set
.univ f ↔ Loc…
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
protected lemma LocallyLipschitz.locallyLipschitzOn (h : LocallyLipschitz f) :
    LocallyLipschitzOn s f := (locallyLipschitzOn_univ.2 h).mono s.subset_univ
/-
**lipschitzOnWith_iff_restrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lipschitzOnWith_iff_restrict : LipschitzOnWith K f s ↔ LipschitzWith K (s.
domRestrict f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lipschitzOnWith_iff_restrict :
    LipschitzOnWith K f s ↔ LipschitzWith K (s.domRestrict f) := by
  simp [LipschitzOnWith, LipschitzWith]
/-
**lipschitzOnWith_restrict** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lipschitzOnWith_restrict {t : Set s} : LipschitzOnWith K (s.domRestrict f)
 t ↔ LipschitzOnWith K f (s inter Subtype.val '' t)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Set.image_val_inter_self_right_eq_coe`：image_val_inter_self_right_eq_coe
 : A inter ↑D = ↑D
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma lipschitzOnWith_restrict {t : Set s} :
    LipschitzOnWith K (s.domRestrict f) t ↔ LipschitzOnWith K f (s ∩ Subtype.val '' t) := by
  simp [LipschitzOnWith]
/-
**locallyLipschitzOn_iff_restrict** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：locallyLipschitzOn_iff_restrict : LocallyLipschitzOn s f ↔ LocallyLipschit
z (s.domRestrict f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `nhds_subtype_eq_comap_nhdsWithin`：nhds_subtype_eq_comap_nhdsWithin (s : 
Set X) (x : { x // x in s }) : 𝓝 x = comap (↑) (𝓝[s] (x : X))
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `LipschitzOnWith.mono`：LipschitzOnWith.mono (hf : LipschitzOnWith K f t) 
(h : s subseteq t) : LipschitzOnWith K f s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma locallyLipschitzOn_iff_restrict :
    LocallyLipschitzOn s f ↔ LocallyLipschitz (s.domRestrict f) := by
  simp only [LocallyLipschitzOn, LocallyLipschitz, SetCoe.forall',
    lipschitzOnWith_restrict,
    nhds_subtype_eq_comap_nhdsWithin, mem_comap]
  congr! with x K
  constructor
  · rintro ⟨t, ht, hft⟩
    exact ⟨_, ⟨t, ht, Subset.rfl⟩, hft.mono <| inter_subset_right.trans <| image_preimage_subset ..⟩
  · rintro ⟨t, ⟨u, hu, hut⟩, hft⟩
    exact ⟨s ∩ u, Filter.inter_mem self_mem_nhdsWithin hu,
      hft.mono fun x hx ↦ ⟨hx.1, ⟨x, hx.1⟩, hut hx.2, rfl⟩⟩

alias ⟨LipschitzOnWith.to_restrict, _⟩ := lipschitzOnWith_iff_restrict
alias ⟨LocallyLipschitzOn.restrict, _⟩ := locallyLipschitzOn_iff_restrict
/-
**Set.MapsTo.lipschitzOnWith_iff_restrict** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.MapsTo.lipschitzOnWith_iff_restrict {t : Set β} (h : MapsTo f s t) : L
ipschitzOnWith K f s ↔ LipschitzWith K (h.restrict f s t)
参数：h : MapsTo f s t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lipschitzOnWith_iff_restrict`：lipschitzOnWith_iff_restrict : LipschitzOn
With K f s ↔ LipschitzWith K (s.domRestrict f)
-/
lemma Set.MapsTo.lipschitzOnWith_iff_restrict {t : Set β} (h : MapsTo f s t) :
    LipschitzOnWith K f s ↔ LipschitzWith K (h.restrict f s t) :=
  _root_.lipschitzOnWith_iff_restrict

alias ⟨LipschitzOnWith.mapsToRestrict, _⟩ := Set.MapsTo.lipschitzOnWith_iff_restrict

end PseudoEMetricSpace

namespace LipschitzWith

open Metric

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] [PseudoEMetricSpace γ]
variable {K : ℝ≥0} {f : α → β} {x y : α} {r : ℝ≥0∞} {s : Set α}

/-
**LipschitzWith.lipschitzOnWith** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [inst_1 : Pseudo
EMetricSpace β] {K : NNReal} {f : α → β}   {s : Set α}, LipschitzWith K f → Lips
chitzOnWith K f s
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem lipschitzOnWith (h : LipschitzWith K f) : LipschitzOnWith K f s :=
  fun x _ y _ => h x y
/-
**LipschitzWith.edist_le_mul** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：edist_le_mul (h : LipschitzWith K f) (x y : α) : edist (f x) (f y) <= K * 
edist x y
参数：h : LipschitzWith K f；x y : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem edist_le_mul (h : LipschitzWith K f) (x y : α) : edist (f x) (f y) ≤ K * edist x y :=
  h x y
/-
**LipschitzWith.edist_le_mul_of_le** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：edist_le_mul_of_le (h : LipschitzWith K f) (hr : edist x y <= r) : edist (
f x) (f y) <= K * r
参数：h : LipschitzWith K f；hr : edist x y <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `mul_right_mono`：mul_right_mono [MulLeftMono α] {a : α} : Monotone (a * ·
)
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
-/
theorem edist_le_mul_of_le (h : LipschitzWith K f) (hr : edist x y ≤ r) :
    edist (f x) (f y) ≤ K * r :=
  (h x y).trans <| mul_right_mono hr
/-
**LipschitzWith.edist_lt_mul_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：edist_lt_mul_of_lt (h : LipschitzWith K f) (hK : K != 0) (hr : edist x y <
 r) : edist (f x) (f y) < K * r
参数：h : LipschitzWith K f；hK : K != 0；hr : edist x y < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_imp_lt_of_le_of_le`：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a < b -> c < d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `ENNReal.mul_lt_mul_right`：∀ {a b c : ENNReal}, a ≠ 0 → a ≠ ⊤ → b < c → a
 * b < a * c
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem edist_lt_mul_of_lt (h : LipschitzWith K f) (hK : K ≠ 0) (hr : edist x y < r) :
    edist (f x) (f y) < K * r := by grw [h x y]; gcongr; simp
/-
**LipschitzWith.mapsTo_closedEBall** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：mapsTo_closedEBall (h : LipschitzWith K f) (x : α) (r : Real>=0∞) : MapsTo
 f (closedEBall x r) (closedEBall (f x) (K * r))
参数：h : LipschitzWith K f；x : α；r : Real>=0∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.edist_le_mul_of_le`：edist_le_mul_of_le (h : LipschitzWith 
K f) (hr : edist x y <= r) : edist (f x) (f y) <= K * r
-/
theorem mapsTo_closedEBall (h : LipschitzWith K f) (x : α) (r : ℝ≥0∞) :
    MapsTo f (closedEBall x r) (closedEBall (f x) (K * r)) := fun _y hy => h.edist_le_mul_of_le hy

@[deprecated (since := "2026-01-24")]
alias mapsTo_emetric_closedBall := mapsTo_closedEBall
/-
**LipschitzWith.mapsTo_eball** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：mapsTo_eball (h : LipschitzWith K f) (hK : K != 0) (x : α) (r : Real>=0∞) 
: MapsTo f (eball x r) (eball (f x) (K * r))
参数：h : LipschitzWith K f；hK : K != 0；x : α；r : Real>=0∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.edist_lt_mul_of_lt`：edist_lt_mul_of_lt (h : LipschitzWith 
K f) (hK : K != 0) (hr : edist x y < r) : edist (f x) (f y) < K * r
-/
theorem mapsTo_eball (h : LipschitzWith K f) (hK : K ≠ 0) (x : α) (r : ℝ≥0∞) :
    MapsTo f (eball x r) (eball (f x) (K * r)) := fun _y hy => h.edist_lt_mul_of_lt hK hy

@[deprecated (since := "2026-01-24")]
alias mapsTo_emetric_ball := mapsTo_eball
/-
**LipschitzWith.edist_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：edist_lt_top (hf : LipschitzWith K f) {x y : α} (h : edist x y != ⊤) : edi
st (f x) (f y) < ⊤
参数：hf : LipschitzWith K f；h : edist x y != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `ENNReal.mul_ne_top`：mul_ne_top : a != ∞ -> b != ∞ -> a * b != ∞
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
-/
theorem edist_lt_top (hf : LipschitzWith K f) {x y : α} (h : edist x y ≠ ⊤) :
    edist (f x) (f y) < ⊤ :=
  (hf x y).trans_lt (by finiteness)
/-
**LipschitzWith.mul_edist_le** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：mul_edist_le (h : LipschitzWith K f) (x y : α) : (K⁻¹ : Real>=0∞) * edist 
(f x) (f y) <= edist x y
参数：h : LipschitzWith K f；x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `ENNReal.div_le_of_le_mul'`：div_le_of_le_mul' (h : a <= b * c) : a / b <=
 c
-/
theorem mul_edist_le (h : LipschitzWith K f) (x y : α) :
    (K⁻¹ : ℝ≥0∞) * edist (f x) (f y) ≤ edist x y := by
  rw [mul_comm, ← div_eq_mul_inv]
  exact ENNReal.div_le_of_le_mul' (h x y)
/-
**LipschitzWith.of_edist_le** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [inst_1 : Pseudo
EMetricSpace β] {f : α → β},   (∀ (x y : α), edist (f x) (f y) ≤ edist x y) → Li
pschitzWith 1 f
参数：∀ (x y : α), edist (f x) (f y) ≤ edist x y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
protected theorem of_edist_le (h : ∀ x y, edist (f x) (f y) ≤ edist x y) : LipschitzWith 1 f :=
  fun x y => by simp only [ENNReal.coe_one, one_mul, h]
/-
**LipschitzWith.weaken** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [inst_1 : Pseudo
EMetricSpace β] {K : NNReal} {f : α → β},   LipschitzWith K f → ∀ {K' : NNReal},
 K ≤ K' → LipschitzWith K' f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `mul_left_mono`：mul_left_mono [MulRightMono α] {a : α} : Monotone (· * a)
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
-/
protected theorem weaken (hf : LipschitzWith K f) {K' : ℝ≥0} (h : K ≤ K') : LipschitzWith K' f :=
  fun x y => le_trans (hf x y) <| mul_left_mono (ENNReal.coe_le_coe.2 h)
/-
**LipschitzWith.ediam_image_le** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：ediam_image_le (hf : LipschitzWith K f) (s : Set α) : Metric.ediam (f '' s
) <= K * Metric.ediam s
参数：hf : LipschitzWith K f；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.ediam_le`：ediam_le {d : Real>=0∞} (h : forall x in s, forall y in
 s, edist x y <= d) : ediam s <= d
· 使用定理 `LipschitzWith.edist_le_mul_of_le`：edist_le_mul_of_le (h : LipschitzWith 
K f) (hr : edist x y <= r) : edist (f x) (f y) <= K * r
· 使用定理 `Metric.edist_le_ediam_of_mem`：edist_le_ediam_of_mem (hx : x in s) (hy : 
y in s) : edist x y <= ediam s
-/
theorem ediam_image_le (hf : LipschitzWith K f) (s : Set α) :
    Metric.ediam (f '' s) ≤ K * Metric.ediam s := by
  apply Metric.ediam_le
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact hf.edist_le_mul_of_le (Metric.edist_le_ediam_of_mem hx hy)
/-
**LipschitzWith.edist_lt_of_edist_lt_div** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWit
h`。
形式化陈述：edist_lt_of_edist_lt_div (hf : LipschitzWith K f) {x y : α} {d : Real>=0∞}
 (h : edist x y < d / K) : edist (f x) (f y) < d
参数：hf : LipschitzWith K f；h : edist x y < d / K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.mul_lt_of_lt_div'`：mul_lt_of_lt_div' (h : a < b / c) : c * a < b
-/
theorem edist_lt_of_edist_lt_div (hf : LipschitzWith K f) {x y : α} {d : ℝ≥0∞}
    (h : edist x y < d / K) : edist (f x) (f y) < d :=
  calc
    edist (f x) (f y) ≤ K * edist x y := hf x y
    _ < d := ENNReal.mul_lt_of_lt_div' h

/-- A Lipschitz function is uniformly continuous. -/
/-
**LipschitzWith.uniformContinuous** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [inst_1 : Pseudo
EMetricSpace β] {K : NNReal} {f : α → β},   LipschitzWith K f → UniformContinuou
s f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EMetric.uniformContinuous_iff`：uniformContinuous_iff [PseudoEMetricSpace
 β] {f : α -> β} : UniformContinuous f ↔ forall ε > 0, exists δ > 0, forall {a b
 : α}, edist a b < …
· 使用定理 `ENNReal.div_pos_iff`：∀ {a b : ENNReal}, 0 < a / b ↔ a ≠ 0 ∧ b ≠ ⊤
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `LipschitzWith.edist_lt_of_edist_lt_div`：edist_lt_of_edist_lt_div (hf : L
ipschitzWith K f) {x y : α} {d : Real>=0∞} (h : edist x y < d / K) : edist (f x)
 (f y) < d

--- 原说明 ---
A Lipschitz function is uniformly continuous.
-/
protected theorem uniformContinuous (hf : LipschitzWith K f) : UniformContinuous f :=
  EMetric.uniformContinuous_iff.2 fun ε εpos =>
    ⟨ε / K, ENNReal.div_pos_iff.2 ⟨ne_of_gt εpos, ENNReal.coe_ne_top⟩, hf.edist_lt_of_edist_lt_div⟩

/-- A Lipschitz function is continuous. -/
/-
**LipschitzWith.continuous** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [inst_1 : Pseudo
EMetricSpace β] {K : NNReal} {f : α → β},   LipschitzWith K f → Continuous f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `LipschitzWith.uniformContinuous`：∀ {α : Type u} {β : Type v} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   L
ipschitzWith K f → Un…

--- 原说明 ---
A Lipschitz function is continuous.
-/
protected theorem continuous (hf : LipschitzWith K f) : Continuous f :=
  hf.uniformContinuous.continuous

/-- Constant functions are Lipschitz (with any constant). -/
/-
**LipschitzWith.const** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [inst_1 : Pseudo
EMetricSpace β] (b : β),   LipschitzWith 0 fun x => b
参数：b : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal

--- 原说明 ---
Constant functions are Lipschitz (with any constant).
-/
protected theorem const (b : β) : LipschitzWith 0 fun _ : α => b := fun x y => by
  simp only [edist_self, zero_le]
/-
**LipschitzWith.const'** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [inst_1 : Pseudo
EMetricSpace β] (b : β) {K : NNReal},   LipschitzWith K fun x => b
参数：b : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
protected theorem const' (b : β) {K : ℝ≥0} : LipschitzWith K fun _ : α => b := fun x y => by
  simp only [edist_self, zero_le]

@[simp]
/-
**LipschitzWith.zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `LipschitzWith`。
形式化陈述：zero_iff {β : Type*} [EMetricSpace β] (f : α -> β) : LipschitzWith 0 f ↔ f
orall x y, f x = f y
参数：f : α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma zero_iff {β : Type*} [EMetricSpace β] (f : α → β) : LipschitzWith 0 f ↔ ∀ x y, f x = f y := by
  simp [LipschitzWith]

/-- The identity is 1-Lipschitz. -/
/-
**LipschitzWith.id** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：∀ {α : Type u} [inst : PseudoEMetricSpace α], LipschitzWith 1 id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.of_edist_le`：∀ {α : Type u} {β : Type v} [inst : PseudoEMe
tricSpace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   (∀ (x y : α), edist 
(f x) (f y) ≤ e…
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
The identity is 1-Lipschitz.
-/
protected theorem id : LipschitzWith 1 (@id α) :=
  LipschitzWith.of_edist_le fun _ _ => le_rfl

/-- The inclusion of a subset is 1-Lipschitz. -/
/-
**LipschitzWith.subtype_val** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：∀ {α : Type u} [inst : PseudoEMetricSpace α] (s : Set α), LipschitzWith 1 
Subtype.val
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.of_edist_le`：∀ {α : Type u} {β : Type v} [inst : PseudoEMe
tricSpace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   (∀ (x y : α), edist 
(f x) (f y) ≤ e…
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
The inclusion of a subset is 1-Lipschitz.
-/
protected theorem subtype_val (s : Set α) : LipschitzWith 1 (Subtype.val : s → α) :=
  LipschitzWith.of_edist_le fun _ _ => le_rfl
/-
**LipschitzWith.subtype_mk** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：subtype_mk (hf : LipschitzWith K f) {p : β -> Prop} (hp : forall x, p (f x
)) : LipschitzWith K (fun x => ⟨f x, hp x⟩ : α -> { y // p y })
参数：hf : LipschitzWith K f；hp : forall x, p (f x)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtype_mk (hf : LipschitzWith K f) {p : β → Prop} (hp : ∀ x, p (f x)) :
    LipschitzWith K (fun x => ⟨f x, hp x⟩ : α → { y // p y }) :=
  hf
/-
**LipschitzWith.eval** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：∀ {ι : Type x} {α : ι → Type u} [inst : (i : ι) → PseudoEMetricSpace (α i)
] [inst_1 : Fintype ι] (i : ι),   LipschitzWith 1 (Function.eval i)
参数：i : ι；α i；i : ι；Function.eval i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.of_edist_le`：∀ {α : Type u} {β : Type v} [inst : PseudoEMe
tricSpace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   (∀ (x y : α), edist 
(f x) (f y) ≤ e…
· 使用定理 `edist_le_pi_edist`：edist_le_pi_edist [forall b, EDist (X b)] (f g : fora
ll b, X b) (b : β) : edist (f b) (g b) <= edist f g
-/
protected theorem eval {α : ι → Type u} [∀ i, PseudoEMetricSpace (α i)] [Fintype ι] (i : ι) :
    LipschitzWith 1 (Function.eval i : (∀ i, α i) → α i) :=
  LipschitzWith.of_edist_le fun f g => by convert! edist_le_pi_edist f g i

/-- The restriction of a `K`-Lipschitz function is `K`-Lipschitz. -/
/-
**LipschitzWith.restrict** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [inst_1 : Pseudo
EMetricSpace β] {K : NNReal} {f : α → β},   LipschitzWith K f → ∀ (s : Set α), L
ipschitzWith K (s.domRestrict f)
参数：s : Set α；s.domRestrict f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a `K`-Lipschitz function is `K`-Lipschitz.
-/
protected theorem restrict (hf : LipschitzWith K f) (s : Set α) :
    LipschitzWith K (s.domRestrict f) := fun x y => hf x y

/-- The composition of Lipschitz functions is Lipschitz. -/
/-
**LipschitzWith.comp** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : PseudoEMetricSpace α] [in
st_1 : PseudoEMetricSpace β]   [inst_2 : PseudoEMetricSpace γ] {Kf Kg : NNReal} 
{f : β → γ} {g : α → β},   LipschitzWith Kf f → LipschitzWith Kg g → LipschitzWi
th (Kf * Kg) (f ∘ g)
参数：Kf * Kg；f ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `mul_right_mono`：mul_right_mono [MulLeftMono α] {a : α} : Monotone (a * ·
)
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `ENNReal.coe_mul`：∀ (x y : NNReal), ↑(x * y) = ↑x * ↑y

--- 原说明 ---
The composition of Lipschitz functions is Lipschitz.
-/
protected theorem comp {Kf Kg : ℝ≥0} {f : β → γ} {g : α → β} (hf : LipschitzWith Kf f)
    (hg : LipschitzWith Kg g) : LipschitzWith (Kf * Kg) (f ∘ g) := fun x y =>
  calc
    edist (f (g x)) (f (g y)) ≤ Kf * edist (g x) (g y) := hf _ _
    _ ≤ Kf * (Kg * edist x y) := mul_right_mono (hg _ _)
    _ = (Kf * Kg : ℝ≥0) * edist x y := by rw [← mul_assoc, ENNReal.coe_mul]
/-
**LipschitzWith.comp_lipschitzOnWith** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：comp_lipschitzOnWith {Kf Kg : Real>=0} {f : β -> γ} {g : α -> β} {s : Set 
α} (hf : LipschitzWith Kf f) (hg : LipschitzOnWith Kg g s) : LipschitzOnWith (Kf
 * Kg) (f ∘ g) s
参数：hf : LipschitzWith Kf f；hg : LipschitzOnWith Kg g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lipschitzOnWith_iff_restrict`：lipschitzOnWith_iff_restrict : LipschitzOn
With K f s ↔ LipschitzWith K (s.domRestrict f)
· 使用定理 `LipschitzWith.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β]   [inst_2 : PseudoEMetricSpac
e γ] {Kf…
· 使用定理 `LipschitzOnWith.to_restrict`：∀ {α : Type u} {β : Type v} [inst : PseudoE
MetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {s : Set α}   {f : α
 → β}, LipschitzO…
-/
theorem comp_lipschitzOnWith {Kf Kg : ℝ≥0} {f : β → γ} {g : α → β} {s : Set α}
    (hf : LipschitzWith Kf f) (hg : LipschitzOnWith Kg g s) : LipschitzOnWith (Kf * Kg) (f ∘ g) s :=
  lipschitzOnWith_iff_restrict.mpr <| hf.comp hg.to_restrict
/-
**LipschitzWith.prod_fst** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [inst_1 : Pseudo
EMetricSpace β], LipschitzWith 1 Prod.fst
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.of_edist_le`：∀ {α : Type u} {β : Type v} [inst : PseudoEMe
tricSpace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   (∀ (x y : α), edist 
(f x) (f y) ≤ e…
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
-/
protected theorem prod_fst : LipschitzWith 1 (@Prod.fst α β) :=
  LipschitzWith.of_edist_le fun _ _ => le_max_left _ _
/-
**LipschitzWith.prod_snd** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [inst_1 : Pseudo
EMetricSpace β], LipschitzWith 1 Prod.snd
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.of_edist_le`：∀ {α : Type u} {β : Type v} [inst : PseudoEMe
tricSpace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   (∀ (x y : α), edist 
(f x) (f y) ≤ e…
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
protected theorem prod_snd : LipschitzWith 1 (@Prod.snd α β) :=
  LipschitzWith.of_edist_le fun _ _ => le_max_right _ _

/-- If `f` and `g` are Lipschitz functions, so is the induced map `f × g` to the product type. -/
/-
**LipschitzWith.prodMk** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : PseudoEMetricSpace α] [in
st_1 : PseudoEMetricSpace β]   [inst_2 : PseudoEMetricSpace γ] {f : α → β} {Kf :
 NNReal},   LipschitzWith Kf f → ∀ {g : α → γ} {Kg : NNReal}, LipschitzWith Kg g
 → LipschitzWith (max Kf Kg) fun x => (f x, g x)
参数：max Kf Kg；f x, g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用定理 `ENNReal.coe_mono`：coe_mono : Monotone ofNNReal
· 使用定理 `Prod.edist_eq`：Prod.edist_eq [PseudoEMetricSpace β] (x y : α × β) : edis
t x y = max (edist x.1 y.1) (edist x.2 y.2)
· 使用引理 `max_mul`：max_mul [MulRightMono α] (a b c : α) : max a b * c = max (a * c
) (b * c)
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `max_le_max`：max_le_max : a <= c -> b <= d -> max a b <= max c d

--- 原说明 ---
If `f` and `g` are Lipschitz functions, so is the induced map `f × g` to the pro
duct type.
-/
protected theorem prodMk {f : α → β} {Kf : ℝ≥0} (hf : LipschitzWith Kf f) {g : α → γ} {Kg : ℝ≥0}
    (hg : LipschitzWith Kg g) : LipschitzWith (max Kf Kg) fun x => (f x, g x) := by
  intro x y
  rw [ENNReal.coe_mono.map_max, Prod.edist_eq, max_mul]
  exact max_le_max (hf x y) (hg x y)
/-
**LipschitzWith.prodMk_left** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [inst_1 : Pseudo
EMetricSpace β] (a : α),   LipschitzWith 1 (Prod.mk a)
参数：a : α；Prod.mk a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `LipschitzWith.prodMk`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : P
seudoEMetricSpace α] [inst_1 : PseudoEMetricSpace β]   [inst_2 : PseudoEMetricSp
ace γ] {f …
· 使用定理 `LipschitzWith.const`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSp
ace α] [inst_1 : PseudoEMetricSpace β] (b : β),   LipschitzWith 0 fun x => b
· 使用定理 `LipschitzWith.id`：∀ {α : Type u} [inst : PseudoEMetricSpace α], Lipschit
zWith 1 id
-/
protected theorem prodMk_left (a : α) : LipschitzWith 1 (Prod.mk a : β → α × β) := by
  simpa only [max_eq_right zero_le_one] using! (LipschitzWith.const a).prodMk LipschitzWith.id
/-
**LipschitzWith.prodMk_right** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [inst_1 : Pseudo
EMetricSpace β] (b : β),   LipschitzWith 1 fun a => (a, b)
参数：b : β；a, b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `LipschitzWith.prodMk`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : P
seudoEMetricSpace α] [inst_1 : PseudoEMetricSpace β]   [inst_2 : PseudoEMetricSp
ace γ] {f …
· 使用定理 `LipschitzWith.id`：∀ {α : Type u} [inst : PseudoEMetricSpace α], Lipschit
zWith 1 id
· 使用定理 `LipschitzWith.const`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSp
ace α] [inst_1 : PseudoEMetricSpace β] (b : β),   LipschitzWith 0 fun x => b
-/
protected theorem prodMk_right (b : β) : LipschitzWith 1 fun a : α => (a, b) := by
  simpa only [max_eq_left zero_le_one] using! LipschitzWith.id.prodMk (LipschitzWith.const b)
/-
**LipschitzWith.uncurry** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : PseudoEMetricSpace α] [in
st_1 : PseudoEMetricSpace β]   [inst_2 : PseudoEMetricSpace γ] {f : α → β → γ} {
Kα Kβ : NNReal},   (∀ (b : β), LipschitzWith Kα fun a => f a b) →     (∀ (a : α)
, LipschitzWith Kβ (f a)) → LipschitzWith (Kα + Kβ) (Function.uncurry f)
参数：∀ (b : β), LipschitzWith Kα fun a => f a b；∀ (a : α), LipschitzWith Kβ (f a)；
Kα + Kβ；Function.uncurry f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `PseudoEMetricSpace.edist_triangle`：∀ {α : Type u} [self : PseudoEMetricS
pace α] (x y z : α), edist x z ≤ edist x y + edist y z
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `mul_right_mono`：mul_right_mono [MulLeftMono α] {a : α} : Monotone (a * ·
)
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
protected theorem uncurry {f : α → β → γ} {Kα Kβ : ℝ≥0} (hα : ∀ b, LipschitzWith Kα fun a => f a b)
    (hβ : ∀ a, LipschitzWith Kβ (f a)) : LipschitzWith (Kα + Kβ) (Function.uncurry f) := by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
  simp only [Function.uncurry, ENNReal.coe_add, add_mul]
  apply le_trans (edist_triangle _ (f a₂ b₁) _)
  exact
    add_le_add (le_trans (hα _ _ _) <| mul_right_mono <| le_max_left _ _)
      (le_trans (hβ _ _ _) <| mul_right_mono <| le_max_right _ _)

/-- Iterates of a Lipschitz function are Lipschitz. -/
/-
**LipschitzWith.iterate** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：∀ {α : Type u} [inst : PseudoEMetricSpace α] {K : NNReal} {f : α → α},   L
ipschitzWith K f → ∀ (n : ℕ), LipschitzWith (K ^ n) f^[n]
参数：n : ℕ；K ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Iterates of a Lipschitz function are Lipschitz.
-/
protected theorem iterate {f : α → α} (hf : LipschitzWith K f) : ∀ n, LipschitzWith (K ^ n) f^[n]
  | 0 => by simpa only [pow_zero] using! LipschitzWith.id
  | n + 1 => by rw [pow_succ]; exact (LipschitzWith.iterate hf n).comp hf
/-
**LipschitzWith.edist_iterate_succ_le_geometric** 是 Mathlib 中的一个定理，位于命名空间 `Lipsc
hitzWith`。
形式化陈述：edist_iterate_succ_le_geometric {f : α -> α} (hf : LipschitzWith K f) (x n
) : edist (f^[n] x) (f^[n + 1] x) <= edist x (f x) * (K : Real>=0∞) ^ n
参数：hf : LipschitzWith K f；x n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_succ`：iterate_succ (n : Nat) : f^[n.succ] = f^[n] ∘ f
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `LipschitzWith.iterate`：∀ {α : Type u} [inst : PseudoEMetricSpace α] {K :
 NNReal} {f : α → α},   LipschitzWith K f → ∀ (n : ℕ), LipschitzWith (K ^ n) f^[
n]
-/
theorem edist_iterate_succ_le_geometric {f : α → α} (hf : LipschitzWith K f) (x n) :
    edist (f^[n] x) (f^[n + 1] x) ≤ edist x (f x) * (K : ℝ≥0∞) ^ n := by
  rw [iterate_succ, mul_comm]
  simpa only [ENNReal.coe_pow] using! (hf.iterate n) x (f x)
/-
**LipschitzWith.mul_end** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：∀ {α : Type u} [inst : PseudoEMetricSpace α] {f g : Function.End α} {Kf Kg
 : NNReal},   LipschitzWith Kf f → LipschitzWith Kg g → LipschitzWith (Kf * Kg) 
(f * g)
参数：Kf * Kg；f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β]   [inst_2 : PseudoEMetricSpac
e γ] {Kf…
-/
protected theorem mul_end {f g : Function.End α} {Kf Kg} (hf : LipschitzWith Kf f)
    (hg : LipschitzWith Kg g) : LipschitzWith (Kf * Kg) (f * g : Function.End α) :=
  hf.comp hg

/-- The product of a list of Lipschitz continuous endomorphisms is a Lipschitz continuous
endomorphism. -/
/-
**LipschitzWith.list_prod** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：∀ {α : Type u} {ι : Type x} [inst : PseudoEMetricSpace α] (f : ι → Functio
n.End α) (K : ι → NNReal),   (∀ (i : ι), LipschitzWith (K i) (f i)) → ∀ (l : Lis
t ι), LipschitzWith (List.map K l).prod (List.map f l).prod
参数：f : ι → Function.End α；K : ι → NNReal；∀ (i : ι), LipschitzWith (K i) (f i)；l 
: List ι；List.map K l；List.map f l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of a list of Lipschitz continuous endomorphisms is a Lipschitz conti
nuous
endomorphism.
-/
protected theorem list_prod (f : ι → Function.End α) (K : ι → ℝ≥0)
    (h : ∀ i, LipschitzWith (K i) (f i)) : ∀ l : List ι, LipschitzWith (l.map K).prod (l.map f).prod
  | [] => by simpa using! LipschitzWith.id
  | i::l => by
    simp only [List.map_cons, List.prod_cons]
    exact (h i).mul_end (LipschitzWith.list_prod f K h l)
/-
**LipschitzWith.pow_end** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：∀ {α : Type u} [inst : PseudoEMetricSpace α] {f : Function.End α} {K : NNR
eal},   LipschitzWith K f → ∀ (n : ℕ), LipschitzWith (K ^ n) (f ^ n)
参数：n : ℕ；K ^ n；f ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem pow_end {f : Function.End α} {K} (h : LipschitzWith K f) :
    ∀ n : ℕ, LipschitzWith (K ^ n) (f ^ n : Function.End α)
  | 0 => by simpa only [pow_zero] using! LipschitzWith.id
  | n + 1 => by
    rw [pow_succ, pow_succ]
    exact (LipschitzWith.pow_end h n).mul_end h

end LipschitzWith

namespace LipschitzOnWith

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] [PseudoEMetricSpace γ]
variable {K : ℝ≥0} {s : Set α} {f : α → β}

@[simp]
/-
**LipschitzOnWith.zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `LipschitzOnWith`。
形式化陈述：zero_iff {β : Type*} [EMetricSpace β] (f : α -> β) : LipschitzOnWith 0 f s
 ↔ forall x in s, forall y in s, f x = f y
参数：f : α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma zero_iff {β : Type*} [EMetricSpace β] (f : α → β) :
    LipschitzOnWith 0 f s ↔ ∀ x ∈ s, ∀ y ∈ s, f x = f y := by
  simp [LipschitzOnWith]
/-
**LipschitzOnWith.uniformContinuousOn** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzOnWith
`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [inst_1 : Pseudo
EMetricSpace β] {K : NNReal} {s : Set α}   {f : α → β}, LipschitzOnWith K f s → 
UniformContinuousOn f s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `uniformContinuousOn_iff_restrict`：uniformContinuousOn_iff_restrict [Unif
ormSpace α] [UniformSpace β] {f : α -> β} {s : Set α} : UniformContinuousOn f s 
↔ UniformContinuous (s…
· 使用定理 `LipschitzWith.uniformContinuous`：∀ {α : Type u} {β : Type v} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   L
ipschitzWith K f → Un…
· 使用定理 `LipschitzOnWith.to_restrict`：∀ {α : Type u} {β : Type v} [inst : PseudoE
MetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {s : Set α}   {f : α
 → β}, LipschitzO…
-/
protected theorem uniformContinuousOn (hf : LipschitzOnWith K f s) : UniformContinuousOn f s :=
  uniformContinuousOn_iff_restrict.mpr hf.to_restrict.uniformContinuous
/-
**LipschitzOnWith.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzOnWith`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [inst_1 : Pseudo
EMetricSpace β] {K : NNReal} {s : Set α}   {f : α → β}, LipschitzOnWith K f s → 
ContinuousOn f s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousOn.continuousOn`：UniformContinuousOn.continuousOn [Unif
ormSpace α] [UniformSpace β] {f : α -> β} {s : Set α} (h : UniformContinuousOn f
 s) : ContinuousOn f s
· 使用定理 `LipschitzOnWith.uniformContinuousOn`：∀ {α : Type u} {β : Type v} [inst :
 PseudoEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {s : Set α} 
  {f : α → β}, LipschitzO…
-/
protected theorem continuousOn (hf : LipschitzOnWith K f s) : ContinuousOn f s :=
  hf.uniformContinuousOn.continuousOn
/-
**LipschitzOnWith.weaken** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzOnWith`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [inst_1 : Pseudo
EMetricSpace β] {K : NNReal} {s : Set α}   {f : α → β}, LipschitzOnWith K f s → 
∀ {K' : NNReal}, K ≤ K' → LipschitzOnWith K' f s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `mul_left_mono`：mul_left_mono [MulRightMono α] {a : α} : Monotone (· * a)
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
-/
protected theorem weaken (hf : LipschitzOnWith K f s) {K' : ℝ≥0} (h : K ≤ K') :
    LipschitzOnWith K' f s :=
  fun _ hx _ hy => (hf hx hy).trans <| mul_left_mono (ENNReal.coe_le_coe.2 h)
/-
**LipschitzOnWith.edist_le_mul_of_le** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzOnWith`
。
形式化陈述：edist_le_mul_of_le (h : LipschitzOnWith K f s) {x y : α} (hx : x in s) (hy
 : y in s) {r : Real>=0∞} (hr : edist x y <= r) : edist (f x) (f y) <= K * r
参数：h : LipschitzOnWith K f s；hx : x in s；hy : y in s；hr : edist x y <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `mul_right_mono`：mul_right_mono [MulLeftMono α] {a : α} : Monotone (a * ·
)
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
-/
theorem edist_le_mul_of_le (h : LipschitzOnWith K f s) {x y : α} (hx : x ∈ s) (hy : y ∈ s)
    {r : ℝ≥0∞} (hr : edist x y ≤ r) :
    edist (f x) (f y) ≤ K * r :=
  (h hx hy).trans <| mul_right_mono hr
/-
**LipschitzOnWith.edist_lt_of_edist_lt_div** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzO
nWith`。
形式化陈述：edist_lt_of_edist_lt_div (hf : LipschitzOnWith K f s) {x y : α} (hx : x in
 s) (hy : y in s) {d : Real>=0∞} (hd : edist x y < d / K) : edist (f x) (f y) < 
d
参数：hf : LipschitzOnWith K f s；hx : x in s；hy : y in s；hd : edist x y < d / K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.edist_lt_of_edist_lt_div`：edist_lt_of_edist_lt_div (hf : L
ipschitzWith K f) {x y : α} {d : Real>=0∞} (h : edist x y < d / K) : edist (f x)
 (f y) < d
· 使用定理 `LipschitzOnWith.to_restrict`：∀ {α : Type u} {β : Type v} [inst : PseudoE
MetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {s : Set α}   {f : α
 → β}, LipschitzO…
-/
theorem edist_lt_of_edist_lt_div (hf : LipschitzOnWith K f s) {x y : α} (hx : x ∈ s) (hy : y ∈ s)
    {d : ℝ≥0∞} (hd : edist x y < d / K) : edist (f x) (f y) < d :=
  hf.to_restrict.edist_lt_of_edist_lt_div <| show edist (⟨x, hx⟩ : s) ⟨y, hy⟩ < d / K from hd
/-
**LipschitzOnWith.comp** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzOnWith`。
形式化陈述：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : PseudoEMetricSpace α] [in
st_1 : PseudoEMetricSpace β]   [inst_2 : PseudoEMetricSpace γ] {K : NNReal} {s :
 Set α} {f : α → β} {g : β → γ} {t : Set β} {Kg : NNReal},   LipschitzOnWith Kg 
g t → LipschitzOnWith K f s → Set.MapsTo f s t → LipschitzOnWith (Kg * K) (g ∘ f
) s
参数：Kg * K；g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lipschitzOnWith_iff_restrict`：lipschitzOnWith_iff_restrict : LipschitzOn
With K f s ↔ LipschitzWith K (s.domRestrict f)
· 使用定理 `LipschitzWith.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β]   [inst_2 : PseudoEMetricSpac
e γ] {Kf…
· 使用定理 `LipschitzOnWith.to_restrict`：∀ {α : Type u} {β : Type v} [inst : PseudoE
MetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {s : Set α}   {f : α
 → β}, LipschitzO…
· 使用定理 `LipschitzOnWith.mapsToRestrict`：∀ {α : Type u} {β : Type v} [inst : Pseu
doEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {s : Set α}   {f 
: α → β} {t : Set β}…
-/
protected theorem comp {g : β → γ} {t : Set β} {Kg : ℝ≥0} (hg : LipschitzOnWith Kg g t)
    (hf : LipschitzOnWith K f s) (hmaps : MapsTo f s t) : LipschitzOnWith (Kg * K) (g ∘ f) s :=
  lipschitzOnWith_iff_restrict.mpr <| hg.to_restrict.comp (hf.mapsToRestrict hmaps)

/-- If `f` and `g` are Lipschitz on `s`, so is the induced map `f × g` to the product type. -/
/-
**LipschitzOnWith.prodMk** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzOnWith`。
形式化陈述：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : PseudoEMetricSpace α] [in
st_1 : PseudoEMetricSpace β]   [inst_2 : PseudoEMetricSpace γ] {s : Set α} {f : 
α → β} {g : α → γ} {Kf Kg : NNReal},   LipschitzOnWith Kf f s → LipschitzOnWith 
Kg g s → LipschitzOnWith (max Kf Kg) (fun x => (f x, g x)) s
参数：max Kf Kg；fun x => (f x, g x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用定理 `ENNReal.coe_mono`：coe_mono : Monotone ofNNReal
· 使用定理 `Prod.edist_eq`：Prod.edist_eq [PseudoEMetricSpace β] (x y : α × β) : edis
t x y = max (edist x.1 y.1) (edist x.2 y.2)
· 使用引理 `max_mul`：max_mul [MulRightMono α] (a b c : α) : max a b * c = max (a * c
) (b * c)
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `max_le_max`：max_le_max : a <= c -> b <= d -> max a b <= max c d

--- 原说明 ---
If `f` and `g` are Lipschitz on `s`, so is the induced map `f × g` to the produc
t type.
-/
protected theorem prodMk {g : α → γ} {Kf Kg : ℝ≥0} (hf : LipschitzOnWith Kf f s)
    (hg : LipschitzOnWith Kg g s) : LipschitzOnWith (max Kf Kg) (fun x => (f x, g x)) s := by
  intro _ hx _ hy
  rw [ENNReal.coe_mono.map_max, Prod.edist_eq, max_mul]
  exact max_le_max (hf hx hy) (hg hx hy)
/-
**LipschitzOnWith.ediam_image2_le** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzOnWith`。
形式化陈述：ediam_image2_le (f : α -> β -> γ) {K₁ K₂ : Real>=0} (s : Set α) (t : Set β
) (hf₁ : forall b in t, LipschitzOnWith K₁ (f · b) s) (hf₂ : forall a in s, Lips
chitzOnWith K₂ (f a) t) : Metric.ediam (Set.image2 f s t) <= ↑K₁ * Metric.ediam 
s + ↑K₂ * Metric.ediam t
参数：f : α -> β -> γ；s : Set α；t : Set β；hf₁ : forall b in t, LipschitzOnWith K₁ (
f · b) s；hf₂ : forall a in s, LipschitzOnWith K₂ (f a) t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `PseudoEMetricSpace.edist_triangle`：∀ {α : Type u} [self : PseudoEMetricS
pace α] (x y z : α), edist x z ≤ edist x y + edist y z
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `mul_right_mono`：mul_right_mono [MulLeftMono α] {a : α} : Monotone (a * ·
)
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `Metric.edist_le_ediam_of_mem`：edist_le_ediam_of_mem (hx : x in s) (hy : 
y in s) : edist x y <= ediam s
-/
theorem ediam_image2_le (f : α → β → γ) {K₁ K₂ : ℝ≥0} (s : Set α) (t : Set β)
    (hf₁ : ∀ b ∈ t, LipschitzOnWith K₁ (f · b) s) (hf₂ : ∀ a ∈ s, LipschitzOnWith K₂ (f a) t) :
    Metric.ediam (Set.image2 f s t) ≤ ↑K₁ * Metric.ediam s + ↑K₂ * Metric.ediam t := by
  simp only [Metric.ediam_le_iff, forall_mem_image2]
  intro a₁ ha₁ b₁ hb₁ a₂ ha₂ b₂ hb₂
  refine (edist_triangle _ (f a₂ b₁) _).trans ?_
  exact
    add_le_add
      ((hf₁ b₁ hb₁ ha₁ ha₂).trans <| mul_right_mono <| Metric.edist_le_ediam_of_mem ha₁ ha₂)
      ((hf₂ a₂ ha₂ hb₁ hb₂).trans <| mul_right_mono <| Metric.edist_le_ediam_of_mem hb₁ hb₂)

end LipschitzOnWith

namespace LocallyLipschitz
variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] [PseudoEMetricSpace γ] {f : α → β}

/-- A Lipschitz function is locally Lipschitz. -/
/-
**LocallyLipschitz._root_.LipschitzWith.locallyLipschitz** 是 Mathlib 中的一个引理，位于命名
空间 `LocallyLipschitz`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Lipschitz function is locally Lipschitz.
-/
protected lemma _root_.LipschitzWith.locallyLipschitz {K : ℝ≥0} (hf : LipschitzWith K f) :
    LocallyLipschitz f :=
  fun _ ↦ ⟨K, univ, Filter.univ_mem, lipschitzOnWith_univ.mpr hf⟩

/-- The identity function is locally Lipschitz. -/
/-
**LocallyLipschitz.id** 是 Mathlib 中的一个定理，位于命名空间 `LocallyLipschitz`。
形式化陈述：∀ {α : Type u} [inst : PseudoEMetricSpace α], LocallyLipschitz id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.locallyLipschitz`：∀ {α : Type u} {β : Type v} [inst : Pseu
doEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {f : α → β} {K : NNReal},   Li
pschitzWith K f → Lo…
· 使用定理 `LipschitzWith.id`：∀ {α : Type u} [inst : PseudoEMetricSpace α], Lipschit
zWith 1 id

--- 原说明 ---
The identity function is locally Lipschitz.
-/
protected lemma id : LocallyLipschitz (@id α) := LipschitzWith.id.locallyLipschitz

/-- Constant functions are locally Lipschitz. -/
/-
**LocallyLipschitz.const** 是 Mathlib 中的一个定理，位于命名空间 `LocallyLipschitz`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [inst_1 : Pseudo
EMetricSpace β] (b : β),   LocallyLipschitz fun x => b
参数：b : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.locallyLipschitz`：∀ {α : Type u} {β : Type v} [inst : Pseu
doEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {f : α → β} {K : NNReal},   Li
pschitzWith K f → Lo…
· 使用定理 `LipschitzWith.const`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSp
ace α] [inst_1 : PseudoEMetricSpace β] (b : β),   LipschitzWith 0 fun x => b

--- 原说明 ---
Constant functions are locally Lipschitz.
-/
protected lemma const (b : β) : LocallyLipschitz (fun _ : α ↦ b) :=
  (LipschitzWith.const b).locallyLipschitz

/-- A locally Lipschitz function is continuous. (The converse is false: for example,
$x ↦ \sqrt{x}$ is continuous, but not locally Lipschitz at 0.) -/
/-
**LocallyLipschitz.continuous** 是 Mathlib 中的一个定理，位于命名空间 `LocallyLipschitz`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [inst_1 : Pseudo
EMetricSpace β] {f : α → β},   LocallyLipschitz f → Continuous f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `ContinuousOn.continuousAt`：ContinuousOn.continuousAt (h : ContinuousOn f
 s) (hx : s in 𝓝 x) : ContinuousAt f x
· 使用定理 `LipschitzOnWith.continuousOn`：∀ {α : Type u} {β : Type v} [inst : Pseudo
EMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {s : Set α}   {f : 
α → β}, LipschitzO…

--- 原说明 ---
A locally Lipschitz function is continuous. (The converse is false: for example,
$x ↦ \sqrt{x}$ is continuous, but not locally Lipschitz at 0.)
-/
protected theorem continuous {f : α → β} (hf : LocallyLipschitz f) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases (hf x) with ⟨K, t, ht, hK⟩
  exact (hK.continuousOn).continuousAt ht

/-- The composition of locally Lipschitz functions is locally Lipschitz. -/
/-
**LocallyLipschitz.comp** 是 Mathlib 中的一个定理，位于命名空间 `LocallyLipschitz`。
形式化陈述：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : PseudoEMetricSpace α] [in
st_1 : PseudoEMetricSpace β]   [inst_2 : PseudoEMetricSpace γ] {f : β → γ} {g : 
α → β},   LocallyLipschitz f → LocallyLipschitz g → LocallyLipschitz (f ∘ g)
参数：f ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `LocallyLipschitz.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoE
MetricSpace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   LocallyLipschitz f
 → Continuous f
· 使用定理 `LipschitzOnWith.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : P
seudoEMetricSpace α] [inst_1 : PseudoEMetricSpace β]   [inst_2 : PseudoEMetricSp
ace γ] {K …
· 使用定理 `LipschitzOnWith.mono`：LipschitzOnWith.mono (hf : LipschitzOnWith K f t) 
(h : s subseteq t) : LipschitzOnWith K f s
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.MapsTo.mono_left`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t
 : Set β} {f : α → β}, Set.MapsTo f s₁ t → s₂ ⊆ s₁ → Set.MapsTo f s₂ t
· 使用定理 `Set.mapsTo_preimage`：mapsTo_preimage (f : α -> β) (t : Set β) : MapsTo f
 (f ⁻¹' t) t
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t

--- 原说明 ---
The composition of locally Lipschitz functions is locally Lipschitz.
-/
protected lemma comp {f : β → γ} {g : α → β}
    (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) : LocallyLipschitz (f ∘ g) := by
  intro x
  -- g is Lipschitz on t ∋ x, f is Lipschitz on u ∋ g(x)
  rcases hg x with ⟨Kg, t, ht, hgL⟩
  rcases hf (g x) with ⟨Kf, u, hu, hfL⟩
  refine ⟨Kf * Kg, t ∩ g⁻¹' u, inter_mem ht (hg.continuous.continuousAt hu), ?_⟩
  exact hfL.comp (hgL.mono inter_subset_left)
    ((mapsTo_preimage g u).mono_left inter_subset_right)

/-- If `f` and `g` are locally Lipschitz, so is the induced map `f × g` to the product type. -/
/-
**LocallyLipschitz.prodMk** 是 Mathlib 中的一个定理，位于命名空间 `LocallyLipschitz`。
形式化陈述：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : PseudoEMetricSpace α] [in
st_1 : PseudoEMetricSpace β]   [inst_2 : PseudoEMetricSpace γ] {f : α → β},   Lo
callyLipschitz f → ∀ {g : α → γ}, LocallyLipschitz g → LocallyLipschitz fun x =>
 (f x, g x)
参数：f x, g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `LipschitzOnWith.prodMk`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst :
 PseudoEMetricSpace α] [inst_1 : PseudoEMetricSpace β]   [inst_2 : PseudoEMetric
Space γ] {s …
· 使用定理 `LipschitzOnWith.mono`：LipschitzOnWith.mono (hf : LipschitzOnWith K f t) 
(h : s subseteq t) : LipschitzOnWith K f s
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t

--- 原说明 ---
If `f` and `g` are locally Lipschitz, so is the induced map `f × g` to the produ
ct type.
-/
protected lemma prodMk {f : α → β} (hf : LocallyLipschitz f) {g : α → γ} (hg : LocallyLipschitz g) :
    LocallyLipschitz fun x => (f x, g x) := by
  intro x
  rcases hf x with ⟨Kf, t₁, h₁t, hfL⟩
  rcases hg x with ⟨Kg, t₂, h₂t, hgL⟩
  refine ⟨max Kf Kg, t₁ ∩ t₂, Filter.inter_mem h₁t h₂t, ?_⟩
  exact (hfL.mono inter_subset_left).prodMk (hgL.mono inter_subset_right)
/-
**LocallyLipschitz.prodMk_left** 是 Mathlib 中的一个定理，位于命名空间 `LocallyLipschitz`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [inst_1 : Pseudo
EMetricSpace β] (a : α),   LocallyLipschitz (Prod.mk a)
参数：a : α；Prod.mk a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.locallyLipschitz`：∀ {α : Type u} {β : Type v} [inst : Pseu
doEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {f : α → β} {K : NNReal},   Li
pschitzWith K f → Lo…
· 使用定理 `LipschitzWith.prodMk_left`：∀ {α : Type u} {β : Type v} [inst : PseudoEMe
tricSpace α] [inst_1 : PseudoEMetricSpace β] (a : α),   LipschitzWith 1 (Prod.mk
 a)
-/
protected theorem prodMk_left (a : α) : LocallyLipschitz (Prod.mk a : β → α × β) :=
  (LipschitzWith.prodMk_left a).locallyLipschitz
/-
**LocallyLipschitz.prodMk_right** 是 Mathlib 中的一个定理，位于命名空间 `LocallyLipschitz`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [inst_1 : Pseudo
EMetricSpace β] (b : β),   LocallyLipschitz fun a => (a, b)
参数：b : β；a, b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.locallyLipschitz`：∀ {α : Type u} {β : Type v} [inst : Pseu
doEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {f : α → β} {K : NNReal},   Li
pschitzWith K f → Lo…
· 使用定理 `LipschitzWith.prodMk_right`：∀ {α : Type u} {β : Type v} [inst : PseudoEM
etricSpace α] [inst_1 : PseudoEMetricSpace β] (b : β),   LipschitzWith 1 fun a =
> (a, b)
-/
protected theorem prodMk_right (b : β) : LocallyLipschitz (fun a : α => (a, b)) :=
  (LipschitzWith.prodMk_right b).locallyLipschitz
/-
**LocallyLipschitz.iterate** 是 Mathlib 中的一个定理，位于命名空间 `LocallyLipschitz`。
形式化陈述：∀ {α : Type u} [inst : PseudoEMetricSpace α] {f : α → α}, LocallyLipschitz
 f → ∀ (n : ℕ), LocallyLipschitz f^[n]
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem iterate {f : α → α} (hf : LocallyLipschitz f) : ∀ n, LocallyLipschitz f^[n]
  | 0 => by simpa only [pow_zero] using! LocallyLipschitz.id
  | n + 1 => by rw [iterate_add, iterate_one]; exact (hf.iterate n).comp hf
/-
**LocallyLipschitz.mul_end** 是 Mathlib 中的一个定理，位于命名空间 `LocallyLipschitz`。
形式化陈述：∀ {α : Type u} [inst : PseudoEMetricSpace α] {f g : Function.End α},   Loc
allyLipschitz f → LocallyLipschitz g → LocallyLipschitz (f * g)
参数：f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyLipschitz.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : 
PseudoEMetricSpace α] [inst_1 : PseudoEMetricSpace β]   [inst_2 : PseudoEMetricS
pace γ] {f …
-/
protected theorem mul_end {f g : Function.End α} (hf : LocallyLipschitz f)
    (hg : LocallyLipschitz g) : LocallyLipschitz (f * g : Function.End α) := hf.comp hg
/-
**LocallyLipschitz.pow_end** 是 Mathlib 中的一个定理，位于命名空间 `LocallyLipschitz`。
形式化陈述：∀ {α : Type u} [inst : PseudoEMetricSpace α] {f : Function.End α},   Local
lyLipschitz f → ∀ (n : ℕ), LocallyLipschitz (f ^ n)
参数：n : ℕ；f ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem pow_end {f : Function.End α} (h : LocallyLipschitz f) :
    ∀ n : ℕ, LocallyLipschitz (f ^ n : Function.End α)
  | 0 => by simpa only [pow_zero] using! LocallyLipschitz.id
  | n + 1 => by
    rw [pow_succ]
    exact (h.pow_end n).mul_end h

end LocallyLipschitz

namespace LocallyLipschitzOn
variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] {f : α → β} {s : Set α}

/-
**LocallyLipschitzOn.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `LocallyLipschitzOn`
。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [inst_1 : Pseudo
EMetricSpace β] {f : α → β} {s : Set α},   LocallyLipschitzOn s f → ContinuousOn
 f s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
· 使用定理 `LocallyLipschitz.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoE
MetricSpace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   LocallyLipschitz f
 → Continuous f
· 使用定理 `LocallyLipschitzOn.restrict`：∀ {α : Type u} {β : Type v} [inst : PseudoE
MetricSpace α] [inst_1 : PseudoEMetricSpace β] {s : Set α} {f : α → β},   Locall
yLipschitzOn s f …
-/
protected lemma continuousOn (hf : LocallyLipschitzOn s f) : ContinuousOn f s :=
  continuousOn_iff_continuous_domRestrict.2 hf.restrict.continuous

end LocallyLipschitzOn

/-- Consider a function `f : α × β → γ`. Suppose that it is continuous on each “vertical fiber”
`{a} × t`, `a ∈ s`, and is Lipschitz continuous on each “horizontal fiber” `s × {b}`, `b ∈ t`
with the same Lipschitz constant `K`. Then it is continuous on `s × t`. Moreover, it suffices
to require continuity on vertical fibers for `a` from a subset `s' ⊆ s` that is dense in `s`.

The actual statement uses (Lipschitz) continuity of `fun y ↦ f (a, y)` and `fun x ↦ f (x, b)`
instead of continuity of `f` on subsets of the product space. -/
/-
**continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith** 是 Mathlib 中
的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith [PseudoEM
etricSpace α] [TopologicalSpace β] [PseudoEMetricSpace γ] (f : α × β -> γ) {s s'
 : Set α} {t : Set β} (hs' : s' subseteq s) (hss' : s subseteq closure s') (K : 
Real>=0) (ha : forall a in s', ContinuousOn (fun y => f (a, y)) t) (hb : forall 
b in t, LipschitzOnWith K (fun x => f (x, b)) s) : ContinuousOn f (s ×ˢ t)
参数：f : α × β -> γ；hs' : s' subseteq s；hss' : s subseteq closure s'；K : Real>=0；h
a : forall a in s', ContinuousOn (fun y => f (a, y)) t；hb : forall b in t, Lipsc
hitzOnWith K (fun x => f (x, b)) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `Metric.nhds_basis_closedEBall`：nhds_basis_closedEBall : (𝓝 x).HasBasis (
fun ε : Real>=0∞ => 0 < ε) (closedEBall x)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ENNReal.half_pos`：∀ {a : ENNReal}, a ≠ 0 → 0 < a / 2
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `ENNReal.exists_nnreal_pos_mul_lt`：exists_nnreal_pos_mul_lt (ha : a != ∞)
 (hb : b != 0) : exists n > 0, ↑(n : Real>=0) * a < b
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EMetric.mem_closure_iff`：mem_closure_iff : x in closure s ↔ forall ε > 0
, exists y in s, edist x y < ε
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用定理 `inter_mem_nhdsWithin`：inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : 
α} (h : t in 𝓝 a) : s inter t in 𝓝[s] a
· 使用定理 `Metric.eball_mem_nhds`：eball_mem_nhds (x : α) {ε : Real>=0∞} (ε0 : 0 < ε
) : eball x ε in 𝓝 x
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Metric.closedEBall_mem_nhds`：closedEBall_mem_nhds (x : α) {ε : Real>=0∞}
 (ε0 : 0 < ε) : closedEBall x ε in 𝓝 x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `nhdsWithin_prod`：nhdsWithin_prod [TopologicalSpace β] {s u : Set α} {t v
 : Set β} {a : α} {b : β} (hu : u in 𝓝[s] a) (hv : v in 𝓝[t] b) : u ×ˢ v in 𝓝[s 
×ˢ t]…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `edist_triangle4`：edist_triangle4 (x y z t : α) : edist x t <= edist x y 
+ edist y z + edist z t
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `LipschitzOnWith.edist_le_mul_of_le`：edist_le_mul_of_le (h : LipschitzOnW
ith K f s) {x y : α} (hx : x in s) (hy : y in s) {r : Real>=0∞} (hr : edist x y 
<= r) : edist (f x) (f y…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `PseudoEMetricSpace.edist_triangle`：∀ {α : Type u} [self : PseudoEMetricS
pace α] (x y z : α), edist x z ≤ edist x y + edist y z
（共 58 条，此处仅展示前 30 条）

--- 原说明 ---
Consider a function `f : α × β → γ`. Suppose that it is continuous on each “vert
ical fiber”
`{a} × t`, `a ∈ s`, and is Lipschitz continuous on each “horizontal fiber” `s × 
{b}`, `b ∈ t`
with the same Lipschitz constant `K`. Then it is continuous on `s × t`. Moreover
, it suffices
to require continuity on vertical fibers for `a` from a subset `s' ⊆ s` that is 
dense in `s`.

The actual statement uses (Lipschitz) continuity of `fun y ↦ f (a, y)` and `fun 
x ↦ f (x, b)`
instead of continuity of `f` on subsets of the product space.
-/
theorem continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith [PseudoEMetricSpace α]
    [TopologicalSpace β] [PseudoEMetricSpace γ] (f : α × β → γ) {s s' : Set α} {t : Set β}
    (hs' : s' ⊆ s) (hss' : s ⊆ closure s') (K : ℝ≥0)
    (ha : ∀ a ∈ s', ContinuousOn (fun y => f (a, y)) t)
    (hb : ∀ b ∈ t, LipschitzOnWith K (fun x => f (x, b)) s) : ContinuousOn f (s ×ˢ t) := by
  rintro ⟨x, y⟩ ⟨hx : x ∈ s, hy : y ∈ t⟩
  refine Metric.nhds_basis_closedEBall.tendsto_right_iff.2 fun ε (ε0 : 0 < ε) => ?_
  replace ε0 : 0 < ε / 2 := ENNReal.half_pos ε0.ne'
  obtain ⟨δ, δpos, hδ⟩ : ∃ δ : ℝ≥0, 0 < δ ∧ (δ : ℝ≥0∞) * ↑(3 * K) < ε / 2 :=
    ENNReal.exists_nnreal_pos_mul_lt ENNReal.coe_ne_top ε0.ne'
  rw [← ENNReal.coe_pos] at δpos
  rcases EMetric.mem_closure_iff.1 (hss' hx) δ δpos with ⟨x', hx', hxx'⟩
  have A : s ∩ Metric.eball x δ ∈ 𝓝[s] x :=
    inter_mem_nhdsWithin _ (Metric.eball_mem_nhds _ δpos)
  have B : t ∩ { b | edist (f (x', b)) (f (x', y)) ≤ ε / 2 } ∈ 𝓝[t] y :=
    inter_mem self_mem_nhdsWithin (ha x' hx' y hy (Metric.closedEBall_mem_nhds (f (x', y)) ε0))
  filter_upwards [nhdsWithin_prod A B] with ⟨a, b⟩ ⟨⟨has, hax⟩, ⟨hbt, hby⟩⟩
  calc
    edist (f (a, b)) (f (x, y)) ≤ edist (f (a, b)) (f (x', b)) + edist (f (x', b)) (f (x', y)) +
        edist (f (x', y)) (f (x, y)) := edist_triangle4 _ _ _ _
    _ ≤ K * (δ + δ) + ε / 2 + K * δ := by
      gcongr
      · refine (hb b hbt).edist_le_mul_of_le has (hs' hx') ?_
        exact (edist_triangle _ _ _).trans (add_le_add (le_of_lt hax) hxx'.le)
      · exact hby
      · exact (hb y hy).edist_le_mul_of_le (hs' hx') hx ((edist_comm _ _).trans_le hxx'.le)
    _ = δ * ↑(3 * K) + ε / 2 := by push_cast; ring
    _ ≤ ε / 2 + ε / 2 := by gcongr
    _ = ε := ENNReal.add_halves _

/-- Consider a function `f : α × β → γ`. Suppose that it is continuous on each “vertical fiber”
`{a} × t`, `a ∈ s`, and is Lipschitz continuous on each “horizontal fiber” `s × {b}`, `b ∈ t`
with the same Lipschitz constant `K`. Then it is continuous on `s × t`.

The actual statement uses (Lipschitz) continuity of `fun y ↦ f (a, y)` and `fun x ↦ f (x, b)`
instead of continuity of `f` on subsets of the product space. -/
/-
**continuousOn_prod_of_continuousOn_lipschitzOnWith** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：continuousOn_prod_of_continuousOn_lipschitzOnWith [PseudoEMetricSpace α] [
TopologicalSpace β] [PseudoEMetricSpace γ] (f : α × β -> γ) {s : Set α} {t : Set
 β} (K : Real>=0) (ha : forall a in s, ContinuousOn (fun y => f (a, y)) t) (hb :
 forall b in t, LipschitzOnWith K (fun x => f (x, b)) s) : ContinuousOn f (s ×ˢ 
t)
参数：f : α × β -> γ；K : Real>=0；ha : forall a in s, ContinuousOn (fun y => f (a, y
)) t；hb : forall b in t, LipschitzOnWith K (fun x => f (x, b)) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith`：contin
uousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith [PseudoEMetricSpace α
] [TopologicalSpace β] [PseudoEMetricSpace γ] (f : α ×…
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s

--- 原说明 ---
Consider a function `f : α × β → γ`. Suppose that it is continuous on each “vert
ical fiber”
`{a} × t`, `a ∈ s`, and is Lipschitz continuous on each “horizontal fiber” `s × 
{b}`, `b ∈ t`
with the same Lipschitz constant `K`. Then it is continuous on `s × t`.

The actual statement uses (Lipschitz) continuity of `fun y ↦ f (a, y)` and `fun 
x ↦ f (x, b)`
instead of continuity of `f` on subsets of the product space.
-/
theorem continuousOn_prod_of_continuousOn_lipschitzOnWith [PseudoEMetricSpace α]
    [TopologicalSpace β] [PseudoEMetricSpace γ] (f : α × β → γ) {s : Set α} {t : Set β} (K : ℝ≥0)
    (ha : ∀ a ∈ s, ContinuousOn (fun y => f (a, y)) t)
    (hb : ∀ b ∈ t, LipschitzOnWith K (fun x => f (x, b)) s) : ContinuousOn f (s ×ˢ t) :=
  continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith
    f Subset.rfl subset_closure K ha hb

/-- Consider a function `f : α × β → γ`. Suppose that it is continuous on each “vertical section”
`{a} × univ` for `a : α` from a dense set. Suppose that it is Lipschitz continuous on each
“horizontal section” `univ × {b}`, `b : β` with the same Lipschitz constant `K`. Then it is
continuous.

The actual statement uses (Lipschitz) continuity of `fun y ↦ f (a, y)` and `fun x ↦ f (x, b)`
instead of continuity of `f` on subsets of the product space. -/
/-
**continuous_prod_of_dense_continuous_lipschitzWith** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：continuous_prod_of_dense_continuous_lipschitzWith [PseudoEMetricSpace α] [
TopologicalSpace β] [PseudoEMetricSpace γ] (f : α × β -> γ) (K : Real>=0) {s : S
et α} (hs : Dense s) (ha : forall a in s, Continuous fun y => f (a, y)) (hb : fo
rall b, LipschitzWith K fun x => f (x, b)) : Continuous f
参数：f : α × β -> γ；K : Real>=0；hs : Dense s；ha : forall a in s, Continuous fun y 
=> f (a, y)；hb : forall b, LipschitzWith K fun x => f (x, b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith`：contin
uousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith [PseudoEMetricSpace α
] [TopologicalSpace β] [PseudoEMetricSpace γ] (f : α ×…
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Dense.closure_eq`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}
, Dense s → closure s = Set.univ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
Consider a function `f : α × β → γ`. Suppose that it is continuous on each “vert
ical section”
`{a} × univ` for `a : α` from a dense set. Suppose that it is Lipschitz continuo
us on each
“horizontal section” `univ × {b}`, `b : β` with the same Lipschitz constant `K`.
 Then it is
continuous.

The actual statement uses (Lipschitz) continuity of `fun y ↦ f (a, y)` and `fun 
x ↦ f (x, b)`
instead of continuity of `f` on subsets of the product space.
-/
theorem continuous_prod_of_dense_continuous_lipschitzWith [PseudoEMetricSpace α]
    [TopologicalSpace β] [PseudoEMetricSpace γ] (f : α × β → γ) (K : ℝ≥0) {s : Set α}
    (hs : Dense s) (ha : ∀ a ∈ s, Continuous fun y => f (a, y))
    (hb : ∀ b, LipschitzWith K fun x => f (x, b)) : Continuous f := by
  simp only [← continuousOn_univ, ← univ_prod_univ, ← lipschitzOnWith_univ] at *
  exact continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith f (subset_univ _)
    hs.closure_eq.ge K ha fun b _ => hb b

/-- Consider a function `f : α × β → γ`. Suppose that it is continuous on each “vertical section”
`{a} × univ`, `a : α`, and is Lipschitz continuous on each “horizontal section”
`univ × {b}`, `b : β` with the same Lipschitz constant `K`. Then it is continuous.

The actual statement uses (Lipschitz) continuity of `fun y ↦ f (a, y)` and `fun x ↦ f (x, b)`
instead of continuity of `f` on subsets of the product space. -/
/-
**continuous_prod_of_continuous_lipschitzWith** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_prod_of_continuous_lipschitzWith [PseudoEMetricSpace α] [Topolo
gicalSpace β] [PseudoEMetricSpace γ] (f : α × β -> γ) (K : Real>=0) (ha : forall
 a, Continuous fun y => f (a, y)) (hb : forall b, LipschitzWith K fun x => f (x,
 b)) : Continuous f
参数：f : α × β -> γ；K : Real>=0；ha : forall a, Continuous fun y => f (a, y)；hb : f
orall b, LipschitzWith K fun x => f (x, b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_prod_of_dense_continuous_lipschitzWith`：continuous_prod_of_de
nse_continuous_lipschitzWith [PseudoEMetricSpace α] [TopologicalSpace β] [Pseudo
EMetricSpace γ] (f : α × β -> γ) (K : R…
· 使用定理 `dense_univ`：dense_univ : Dense (univ : Set X)

--- 原说明 ---
Consider a function `f : α × β → γ`. Suppose that it is continuous on each “vert
ical section”
`{a} × univ`, `a : α`, and is Lipschitz continuous on each “horizontal section”
`univ × {b}`, `b : β` with the same Lipschitz constant `K`. Then it is continuou
s.

The actual statement uses (Lipschitz) continuity of `fun y ↦ f (a, y)` and `fun 
x ↦ f (x, b)`
instead of continuity of `f` on subsets of the product space.
-/
theorem continuous_prod_of_continuous_lipschitzWith [PseudoEMetricSpace α] [TopologicalSpace β]
    [PseudoEMetricSpace γ] (f : α × β → γ) (K : ℝ≥0) (ha : ∀ a, Continuous fun y => f (a, y))
    (hb : ∀ b, LipschitzWith K fun x => f (x, b)) : Continuous f :=
  continuous_prod_of_dense_continuous_lipschitzWith f K dense_univ (fun _ _ ↦ ha _) hb
/-
**continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith'** 是 Mathlib 
中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith' [Topolog
icalSpace α] [PseudoEMetricSpace β] [PseudoEMetricSpace γ] (f : α × β -> γ) {s :
 Set α} {t t' : Set β} (ht' : t' subseteq t) (htt' : t subseteq closure t') (K :
 Real>=0) (ha : forall a in s, LipschitzOnWith K (fun y => f (a, y)) t) (hb : fo
rall b in t', ContinuousOn (fun x => f (x, b)) s) : ContinuousOn f (s ×ˢ t)
参数：f : α × β -> γ；ht' : t' subseteq t；htt' : t subseteq closure t'；K : Real>=0；h
a : forall a in s, LipschitzOnWith K (fun y => f (a, y)) t；hb : forall b in t', 
ContinuousOn (fun x => f (x, b)) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith`：contin
uousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith [PseudoEMetricSpace α
] [TopologicalSpace β] [PseudoEMetricSpace γ] (f : α ×…
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuous_swap`：continuous_swap : Continuous (Prod.swap : X × Y -> Y × 
X)
· 使用定理 `Set.mapsTo_swap_prod`：mapsTo_swap_prod (s : Set α) (t : Set β) : MapsTo 
Prod.swap (s ×ˢ t) (t ×ˢ s)
-/
theorem continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith' [TopologicalSpace α]
    [PseudoEMetricSpace β] [PseudoEMetricSpace γ] (f : α × β → γ) {s : Set α} {t t' : Set β}
    (ht' : t' ⊆ t) (htt' : t ⊆ closure t') (K : ℝ≥0)
    (ha : ∀ a ∈ s, LipschitzOnWith K (fun y => f (a, y)) t)
    (hb : ∀ b ∈ t', ContinuousOn (fun x => f (x, b)) s) : ContinuousOn f (s ×ˢ t) :=
  have : ContinuousOn (f ∘ Prod.swap) (t ×ˢ s) :=
    continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith _ ht' htt' K hb ha
  this.comp continuous_swap.continuousOn (mapsTo_swap_prod _ _)
/-
**continuousOn_prod_of_continuousOn_lipschitzOnWith'** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：continuousOn_prod_of_continuousOn_lipschitzOnWith' [TopologicalSpace α] [P
seudoEMetricSpace β] [PseudoEMetricSpace γ] (f : α × β -> γ) {s : Set α} {t : Se
t β} (K : Real>=0) (ha : forall a in s, LipschitzOnWith K (fun y => f (a, y)) t)
 (hb : forall b in t, ContinuousOn (fun x => f (x, b)) s) : ContinuousOn f (s ×ˢ
 t)
参数：f : α × β -> γ；K : Real>=0；ha : forall a in s, LipschitzOnWith K (fun y => f 
(a, y)) t；hb : forall b in t, ContinuousOn (fun x => f (x, b)) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousOn_prod_of_continuousOn_lipschitzOnWith`：continuousOn_prod_of_
continuousOn_lipschitzOnWith [PseudoEMetricSpace α] [TopologicalSpace β] [Pseudo
EMetricSpace γ] (f : α × β -> γ) {s : S…
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuous_swap`：continuous_swap : Continuous (Prod.swap : X × Y -> Y × 
X)
· 使用定理 `Set.mapsTo_swap_prod`：mapsTo_swap_prod (s : Set α) (t : Set β) : MapsTo 
Prod.swap (s ×ˢ t) (t ×ˢ s)
-/
theorem continuousOn_prod_of_continuousOn_lipschitzOnWith' [TopologicalSpace α]
    [PseudoEMetricSpace β] [PseudoEMetricSpace γ] (f : α × β → γ) {s : Set α} {t : Set β} (K : ℝ≥0)
    (ha : ∀ a ∈ s, LipschitzOnWith K (fun y => f (a, y)) t)
    (hb : ∀ b ∈ t, ContinuousOn (fun x => f (x, b)) s) : ContinuousOn f (s ×ˢ t) :=
  have : ContinuousOn (f ∘ Prod.swap) (t ×ˢ s) :=
    continuousOn_prod_of_continuousOn_lipschitzOnWith _ K hb ha
  this.comp continuous_swap.continuousOn (mapsTo_swap_prod _ _)
/-
**continuous_prod_of_dense_continuous_lipschitzWith'** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：continuous_prod_of_dense_continuous_lipschitzWith' [TopologicalSpace α] [P
seudoEMetricSpace β] [PseudoEMetricSpace γ] (f : α × β -> γ) (K : Real>=0) {t : 
Set β} (ht : Dense t) (ha : forall a, LipschitzWith K fun y => f (a, y)) (hb : f
orall b in t, Continuous fun x => f (x, b)) : Continuous f
参数：f : α × β -> γ；K : Real>=0；ht : Dense t；ha : forall a, LipschitzWith K fun y 
=> f (a, y)；hb : forall b in t, Continuous fun x => f (x, b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_prod_of_dense_continuous_lipschitzWith`：continuous_prod_of_de
nse_continuous_lipschitzWith [PseudoEMetricSpace α] [TopologicalSpace β] [Pseudo
EMetricSpace γ] (f : α × β -> γ) (K : R…
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_swap`：continuous_swap : Continuous (Prod.swap : X × Y -> Y × 
X)
-/
theorem continuous_prod_of_dense_continuous_lipschitzWith' [TopologicalSpace α]
    [PseudoEMetricSpace β] [PseudoEMetricSpace γ] (f : α × β → γ) (K : ℝ≥0) {t : Set β}
    (ht : Dense t) (ha : ∀ a, LipschitzWith K fun y => f (a, y))
    (hb : ∀ b ∈ t, Continuous fun x => f (x, b)) : Continuous f :=
  have : Continuous (f ∘ Prod.swap) :=
    continuous_prod_of_dense_continuous_lipschitzWith _ K ht hb ha
  this.comp continuous_swap
/-
**continuous_prod_of_continuous_lipschitzWith'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_prod_of_continuous_lipschitzWith' [TopologicalSpace α] [PseudoE
MetricSpace β] [PseudoEMetricSpace γ] (f : α × β -> γ) (K : Real>=0) (ha : foral
l a, LipschitzWith K fun y => f (a, y)) (hb : forall b, Continuous fun x => f (x
, b)) : Continuous f
参数：f : α × β -> γ；K : Real>=0；ha : forall a, LipschitzWith K fun y => f (a, y)；h
b : forall b, Continuous fun x => f (x, b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_prod_of_continuous_lipschitzWith`：continuous_prod_of_continuo
us_lipschitzWith [PseudoEMetricSpace α] [TopologicalSpace β] [PseudoEMetricSpace
 γ] (f : α × β -> γ) (K : Real>=0…
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_swap`：continuous_swap : Continuous (Prod.swap : X × Y -> Y × 
X)
-/
theorem continuous_prod_of_continuous_lipschitzWith' [TopologicalSpace α] [PseudoEMetricSpace β]
    [PseudoEMetricSpace γ] (f : α × β → γ) (K : ℝ≥0) (ha : ∀ a, LipschitzWith K fun y => f (a, y))
    (hb : ∀ b, Continuous fun x => f (x, b)) : Continuous f :=
  have : Continuous (f ∘ Prod.swap) :=
    continuous_prod_of_continuous_lipschitzWith _ K hb ha
  this.comp continuous_swap
