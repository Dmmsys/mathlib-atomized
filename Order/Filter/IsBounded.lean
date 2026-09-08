/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Johannes Hölzl, Rémy Degenne
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Order.Filter.Cofinite

/-!
# Lemmas about `Is(Co)Bounded(Under)`

This file proves several lemmas about
`IsBounded`, `IsBoundedUnder`, `IsCobounded` and `IsCoboundedUnder`.
-/

public section

open Set Function

variable {α β γ ι : Type*}

namespace Filter

section Relation

variable {r : α → α → Prop} {f g : Filter α}

/-- `f` is eventually bounded if and only if, there exists an admissible set on which it is
bounded. -/
/-
**Filter.isBounded_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：isBounded_iff : f.IsBounded r ↔ exists s in f.sets, exists b, s subseteq {
 x | r x b }
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f

--- 原说明 ---
`f` is eventually bounded if and only if, there exists an admissible set on whic
h it is
bounded.
-/
theorem isBounded_iff : f.IsBounded r ↔ ∃ s ∈ f.sets, ∃ b, s ⊆ { x | r x b } :=
  Iff.intro (fun ⟨b, hb⟩ => ⟨{ a | r a b }, hb, b, Subset.refl _⟩) fun ⟨_, hs, b, hb⟩ =>
    ⟨b, mem_of_superset hs hb⟩

/-- A bounded function `u` is in particular eventually bounded. -/
/-
**Filter.isBoundedUnder_of** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {f : Filter β} {u : β →
 α},   (∃ b, ∀ (x : β), r (u x) b) → Filter.IsBoundedUnder r f u
参数：∃ b, ∀ (x : β), r (u x) b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x

--- 原说明 ---
A bounded function `u` is in particular eventually bounded.
-/
theorem isBoundedUnder_of {f : Filter β} {u : β → α} : (∃ b, ∀ x, r (u x) b) → f.IsBoundedUnder r u
  | ⟨b, hb⟩ => ⟨b, show ∀ᶠ x in f, r (u x) b from Eventually.of_forall hb⟩
/-
**Filter.isBounded_bot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：isBounded_bot : IsBounded r ⊥ ↔ Nonempty α
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
theorem isBounded_bot : IsBounded r ⊥ ↔ Nonempty α := by simp [IsBounded, exists_true_iff_nonempty]
/-
**Filter.isBounded_top** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：isBounded_top : IsBounded r ⊤ ↔ exists t, forall x, r x t
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
theorem isBounded_top : IsBounded r ⊤ ↔ ∃ t, ∀ x, r x t := by simp [IsBounded]
/-
**Filter.isBounded_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：isBounded_principal (s : Set α) : IsBounded r (𝓟 s) ↔ exists t, forall x i
n s, r x t
参数：s : Set α。
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
theorem isBounded_principal (s : Set α) : IsBounded r (𝓟 s) ↔ ∃ t, ∀ x ∈ s, r x t := by
  simp [IsBounded]
/-
**Filter.isBounded_sup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：isBounded_sup [IsTrans α r] [IsDirected α r] : IsBounded r f -> IsBounded 
r g -> IsBounded r (f ⊔ g) | ⟨b₁, h₁⟩, ⟨b₂, h₂⟩ => let ⟨b, rb₁b, rb₂b⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `directed_of`：directed_of (r : α -> α -> Prop) [IsDirected α r] (a b : α)
 : exists c, r a c ∧ r b c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_sup`：eventually_sup {p : α -> Prop} {f g : Filter α} :
 (forallᶠ x in f ⊔ g, p x) ↔ (forallᶠ x in f, p x) ∧ forallᶠ x in g, p x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
-/
theorem isBounded_sup [IsTrans α r] [IsDirected α r] :
    IsBounded r f → IsBounded r g → IsBounded r (f ⊔ g)
  | ⟨b₁, h₁⟩, ⟨b₂, h₂⟩ =>
    let ⟨b, rb₁b, rb₂b⟩ := directed_of r b₁ b₂
    ⟨b, eventually_sup.mpr
      ⟨h₁.mono fun _ h => _root_.trans h rb₁b, h₂.mono fun _ h => _root_.trans h rb₂b⟩⟩
/-
**Filter.IsBounded.mono** 是 Mathlib 中的一个定理，位于命名空间 `Filter.IsBounded`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {f g : Filter α}, f ≤ g → Filter.IsBou
nded r g → Filter.IsBounded r f
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsBounded.mono (h : f ≤ g) : IsBounded r g → IsBounded r f
  | ⟨b, hb⟩ => ⟨b, h hb⟩
/-
**Filter.IsBoundedUnder.mono** 是 Mathlib 中的一个定理，位于命名空间 `Filter.IsBoundedUnder`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {f g : Filter β} {u : β
 → α},   f ≤ g → Filter.IsBoundedUnder r g u → Filter.IsBoundedUnder r f u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.IsBounded.mono`：∀ {α : Type u_1} {r : α → α → Prop} {f g : Filter
 α}, f ≤ g → Filter.IsBounded r g → Filter.IsBounded r f
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
-/
theorem IsBoundedUnder.mono {f g : Filter β} {u : β → α} (h : f ≤ g) :
    g.IsBoundedUnder r u → f.IsBoundedUnder r u := fun hg => IsBounded.mono (map_mono h) hg

@[to_dual mono_ge]
/-
**Filter.IsBoundedUnder.mono_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter.IsBoundedUnder
`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder β] {l : Filter α} {u v : 
α → β},   Filter.IsBoundedUnder (fun x1 x2 => x1 ≤ x2) l u → v ≤ᶠ[l] u → Filter.
IsBoundedUnder (fun x1 x2 => x1 ≤ x2) l v
参数：fun x1 x2 => x1 ≤ x2；fun x1 x2 => x1 ≤ x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem IsBoundedUnder.mono_le [Preorder β] {l : Filter α} {u v : α → β}
    (hu : IsBoundedUnder (· ≤ ·) l u) (hv : v ≤ᶠ[l] u) : IsBoundedUnder (· ≤ ·) l v := by
  apply hu.imp
  exact fun b hb => (eventually_map.1 hb).mp <| hv.mono fun x => le_trans
/-
**Filter.isBoundedUnder_const** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：isBoundedUnder_const [Std.Refl r] {l : Filter β} {a : α} : IsBoundedUnder 
r l fun _ => a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
-/
theorem isBoundedUnder_const [Std.Refl r] {l : Filter β} {a : α} : IsBoundedUnder r l fun _ => a :=
  ⟨a, eventually_map.2 <| Eventually.of_forall fun _ => refl _⟩
/-
**Filter.IsBounded.isBoundedUnder** 是 Mathlib 中的一个定理，位于命名空间 `Filter.IsBounded`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {f : Filter α} {q : β →
 β → Prop} {u : α → β},   (∀ (a₀ a₁ : α), r a₀ a₁ → q (u a₀) (u a₁)) → Filter.Is
Bounded r f → Filter.IsBoundedUnder q f u
参数：∀ (a₀ a₁ : α), r a₀ a₁ → q (u a₀) (u a₁)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
-/
theorem IsBounded.isBoundedUnder {q : β → β → Prop} {u : α → β}
    (hu : ∀ a₀ a₁, r a₀ a₁ → q (u a₀) (u a₁)) : f.IsBounded r → f.IsBoundedUnder q u
  | ⟨b, h⟩ => ⟨u b, show ∀ᶠ x in f, q (u x) (u b) from h.mono fun x => hu x b⟩
/-
**Filter.IsBoundedUnder.comp** 是 Mathlib 中的一个定理，位于命名空间 `Filter.IsBoundedUnder`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r : α → α → Prop} {l : Fil
ter γ} {q : β → β → Prop} {u : γ → α}   {v : α → β},   (∀ (a₀ a₁ : α), r a₀ a₁ →
 q (v a₀) (v a₁)) → Filter.IsBoundedUnder r l u → Filter.IsBoundedUnder q l (v ∘
 u)
参数：∀ (a₀ a₁ : α), r a₀ a₁ → q (v a₀) (v a₁)；v ∘ u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
-/
theorem IsBoundedUnder.comp {l : Filter γ} {q : β → β → Prop} {u : γ → α} {v : α → β}
    (hv : ∀ a₀ a₁, r a₀ a₁ → q (v a₀) (v a₁)) : l.IsBoundedUnder r u → l.IsBoundedUnder q (v ∘ u)
  | ⟨a, h⟩ => ⟨v a, show ∀ᶠ x in map u l, q (v x) (v a) from h.mono fun x => hv x a⟩
/-
**Filter.isBoundedUnder_map_iff** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：isBoundedUnder_map_iff {ι κ X : Type*} {r : X -> X -> Prop} {f : ι -> X} {
φ : κ -> ι} {𝓕 : Filter κ} : (map φ 𝓕).IsBoundedUnder r f ↔ 𝓕.IsBoundedUnder r (
f ∘ φ)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isBoundedUnder_map_iff {ι κ X : Type*} {r : X → X → Prop} {f : ι → X} {φ : κ → ι}
    {𝓕 : Filter κ} :
    (map φ 𝓕).IsBoundedUnder r f ↔ 𝓕.IsBoundedUnder r (f ∘ φ) :=
  Iff.rfl
/-
**Filter.Tendsto.isBoundedUnder_comp** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {ι : Type u_5} {κ : Type u_6} {X : Type u_7} {r : X → X → Prop} {f : ι →
 X} {φ : κ → ι} {𝓕 : Filter ι} {𝓖 : Filter κ},   Filter.Tendsto φ 𝓖 𝓕 → Filter.I
sBoundedUnder r 𝓕 f → Filter.IsBoundedUnder r 𝓖 (f ∘ φ)
参数：f ∘ φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Filter.isBoundedUnder_map_iff`：isBoundedUnder_map_iff {ι κ X : Type*} {r
 : X -> X -> Prop} {f : ι -> X} {φ : κ -> ι} {𝓕 : Filter κ} : (map φ 𝓕).IsBounde
dUnder r f ↔ 𝓕.IsBo…
· 使用定理 `Filter.IsBoundedUnder.mono`：∀ {α : Type u_1} {β : Type u_2} {r : α → α →
 Prop} {f g : Filter β} {u : β → α},   f ≤ g → Filter.IsBoundedUnder r g u → Fil
ter.IsBoundedUnd…
-/
lemma Tendsto.isBoundedUnder_comp {ι κ X : Type*} {r : X → X → Prop} {f : ι → X} {φ : κ → ι}
    {𝓕 : Filter ι} {𝓖 : Filter κ} (φ_tendsto : Tendsto φ 𝓖 𝓕) (𝓕_bounded : 𝓕.IsBoundedUnder r f) :
    𝓖.IsBoundedUnder r (f ∘ φ) :=
  isBoundedUnder_map_iff.mp (𝓕_bounded.mono φ_tendsto)

section Preorder
variable [Preorder α] {f : Filter β} {u : β → α} {s : Set β}

@[to_dual eventually_ge]
/-
**Filter.IsBoundedUnder.eventually_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter.IsBounde
dUnder`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] {f : Filter β} {u : β 
→ α},   Filter.IsBoundedUnder (fun x1 x2 => x1 ≤ x2) f u → ∃ a, ∀ᶠ (x : β) in f,
 u x ≤ a
参数：fun x1 x2 => x1 ≤ x2；x : β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsBoundedUnder.eventually_le (h : IsBoundedUnder (· ≤ ·) f u) :
    ∃ a, ∀ᶠ x in f, u x ≤ a := by
  tauto

@[to_dual isBoundedUnder_of_eventually_ge]
/-
**Filter.isBoundedUnder_of_eventually_le** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：isBoundedUnder_of_eventually_le {a : α} (h : forallᶠ x in f, u x <= a) : I
sBoundedUnder (· <= ·) f u
参数：h : forallᶠ x in f, u x <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isBoundedUnder_of_eventually_le {a : α} (h : ∀ᶠ x in f, u x ≤ a) :
    IsBoundedUnder (· ≤ ·) f u := ⟨a, h⟩

@[to_dual]
/-
**Filter.isBoundedUnder_iff_eventually_bddAbove** 是 Mathlib 中的一个引理，位于命名空间 `Filte
r`。
形式化陈述：isBoundedUnder_iff_eventually_bddAbove : f.IsBoundedUnder (· <= ·) u ↔ exi
sts s, BddAbove (u '' s) ∧ forallᶠ x in f, x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma isBoundedUnder_iff_eventually_bddAbove :
    f.IsBoundedUnder (· ≤ ·) u ↔ ∃ s, BddAbove (u '' s) ∧ ∀ᶠ x in f, x ∈ s := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨{a | u a ≤ b}, ⟨b, by rintro _ ⟨a, ha, rfl⟩; exact ha⟩, hb⟩
  · rintro ⟨s, ⟨b, hb⟩, hs⟩
    exact ⟨b, hs.mono <| by simpa [upperBounds] using hb⟩

@[to_dual]
/-
**Filter._root_.BddAbove.isBoundedUnder** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.BddAbove.isBoundedUnder (hs : s ∈ f) (hu : BddAbove (u '' s)) :
    f.IsBoundedUnder (· ≤ ·) u := isBoundedUnder_iff_eventually_bddAbove.2 ⟨_, hu, hs⟩

/-- A bounded above function `u` is in particular eventually bounded above. -/
@[to_dual /-- A bounded below function `u` is in particular eventually bounded below. -/]
/-
**Filter._root_.BddAbove.isBoundedUnder_of_range** 是 Mathlib 中的一个引理，位于命名空间 `Filt
er`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bounded above function `u` is in particular eventually bounded above.
-/
lemma _root_.BddAbove.isBoundedUnder_of_range (hu : BddAbove (Set.range u)) :
    f.IsBoundedUnder (· ≤ ·) u := BddAbove.isBoundedUnder (s := univ) f.univ_mem (by simpa)

@[to_dual ge_of_finite]
/-
**Filter.IsBoundedUnder.le_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Filter.IsBounded
Under`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [Nonempty α] [IsDirect
edOrder α] [Finite β] {f : Filter β}   {u : β → α}, Filter.IsBoundedUnder (fun x
1 x2 => x1 ≤ x2) f u
参数：fun x1 x2 => x1 ≤ x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BddAbove.isBoundedUnder_of_range`：∀ {α : Type u_1} {β : Type u_2} [inst 
: Preorder α] {f : Filter β} {u : β → α},   BddAbove (Set.range u) → Filter.IsBo
undedUnder (fun x1 x2 …
· 使用定理 `Set.Finite.bddAbove`：∀ {α : Type u} [inst : Preorder α] [IsDirectedOrder
 α] [Nonempty α] {s : Set α}, s.Finite → BddAbove s
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
-/
lemma IsBoundedUnder.le_of_finite [Nonempty α] [IsDirectedOrder α] [Finite β]
    {f : Filter β} {u : β → α} : IsBoundedUnder (· ≤ ·) f u :=
  (Set.toFinite _).bddAbove.isBoundedUnder_of_range

end Preorder

@[to_dual isBoundedUnder_ge_comp]
/-
**Filter._root_.Monotone.isBoundedUnder_le_comp** 是 Mathlib 中的一个定理，位于命名空间 `Filte
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Monotone.isBoundedUnder_le_comp [Preorder α] [Preorder β] {l : Filter γ} {u : γ → α}
    {v : α → β} (hv : Monotone v) (hl : l.IsBoundedUnder (· ≤ ·) u) :
    l.IsBoundedUnder (· ≤ ·) (v ∘ u) :=
  hl.comp hv

@[to_dual isBoundedUnder_ge_comp]
/-
**Filter._root_.Antitone.isBoundedUnder_le_comp** 是 Mathlib 中的一个定理，位于命名空间 `Filte
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Antitone.isBoundedUnder_le_comp [Preorder α] [Preorder β] {l : Filter γ} {u : γ → α}
    {v : α → β} (hv : Antitone v) (hl : l.IsBoundedUnder (fun x1 x2 ↦ x2 ≤ x1) u) :
    l.IsBoundedUnder (· ≤ ·) (v ∘ u) :=
  hl.comp (swap hv)

@[to_dual]
/-
**Filter.not_isBoundedUnder_of_tendsto_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：not_isBoundedUnder_of_tendsto_atTop [Preorder β] [NoMaxOrder β] {f : α -> 
β} {l : Filter α} [l.NeBot] (hf : Tendsto f l atTop) : ¬IsBoundedUnder (· <= ·) 
l f
参数：hf : Tendsto f l atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.tendsto_atTop`：tendsto_atTop [Preorder β] {m : α -> β} {f : Filte
r α} : Tendsto m f atTop ↔ forall b, forallᶠ a in f, b <= m a
· 使用定理 `Set.eq_empty_of_subset_empty`：eq_empty_of_subset_empty {s : Set α} : s s
ubseteq ∅ -> s = ∅
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `Filter.nonempty_of_mem`：nonempty_of_mem {f : Filter α} [hf : NeBot f] {s
 : Set α} (hs : s in f) : s.Nonempty
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
-/
theorem not_isBoundedUnder_of_tendsto_atTop [Preorder β] [NoMaxOrder β] {f : α → β} {l : Filter α}
    [l.NeBot] (hf : Tendsto f l atTop) : ¬IsBoundedUnder (· ≤ ·) l f := by
  rintro ⟨b, hb⟩
  rw [eventually_map] at hb
  obtain ⟨b', h⟩ := exists_gt b
  have hb' := (tendsto_atTop.mp hf) b'
  have : { x : α | f x ≤ b } ∩ { x : α | b' ≤ f x } = ∅ :=
    eq_empty_of_subset_empty fun x hx => (not_le_of_gt h) (le_trans hx.2 hx.1)
  exact (nonempty_of_mem (hb.and hb')).ne_empty this

@[to_dual]
/-
**Filter.IsBoundedUnder.bddAbove_range_of_cofinite** 是 Mathlib 中的一个定理，位于命名空间 `Fi
lter.IsBoundedUnder`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder β] [IsDirectedOrder β] {f
 : α → β},   Filter.IsBoundedUnder (fun x1 x2 => x1 ≤ x2) Filter.cofinite f → Bd
dAbove (Set.range f)
参数：fun x1 x2 => x1 ≤ x2；Set.range f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ
· 使用定理 `Set.image_union`：image_union (f : α -> β) (s t : Set α) : f '' (s union 
t) = f '' s union f '' t
· 使用定理 `bddAbove_union`：bddAbove_union [IsDirectedOrder α] {s t : Set α} : BddAb
ove (s union t) ↔ BddAbove s ∧ BddAbove t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
· 使用定理 `Set.Finite.bddAbove`：∀ {α : Type u} [inst : Preorder α] [IsDirectedOrder
 α] [Nonempty α] {s : Set α}, s.Finite → BddAbove s
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
-/
theorem IsBoundedUnder.bddAbove_range_of_cofinite [Preorder β] [IsDirectedOrder β] {f : α → β}
    (hf : IsBoundedUnder (· ≤ ·) cofinite f) : BddAbove (range f) := by
  rcases hf with ⟨b, hb⟩
  have : Nonempty β := ⟨b⟩
  rw [← image_univ, ← union_compl_self { x | f x ≤ b }, image_union, bddAbove_union]
  exact ⟨⟨b, forall_mem_image.2 fun x => id⟩, (hb.image f).bddAbove⟩

@[to_dual]
/-
**Filter.IsBoundedUnder.bddAbove_range** 是 Mathlib 中的一个定理，位于命名空间 `Filter.IsBound
edUnder`。
形式化陈述：∀ {β : Type u_2} [inst : Preorder β] [IsDirectedOrder β] {f : ℕ → β},   Fi
lter.IsBoundedUnder (fun x1 x2 => x1 ≤ x2) Filter.atTop f → BddAbove (Set.range 
f)
参数：fun x1 x2 => x1 ≤ x2；Set.range f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.IsBoundedUnder.bddAbove_range_of_cofinite`：∀ {α : Type u_1} {β : 
Type u_2} [inst : Preorder β] [IsDirectedOrder β] {f : α → β},   Filter.IsBounde
dUnder (fun x1 x2 => x1 ≤ x2) Filter.c…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cofinite_eq_atTop`：Nat.cofinite_eq_atTop : @cofinite Nat = atTop
-/
theorem IsBoundedUnder.bddAbove_range [Preorder β] [IsDirectedOrder β] {f : ℕ → β}
    (hf : IsBoundedUnder (· ≤ ·) atTop f) : BddAbove (range f) := by
  rw [← Nat.cofinite_eq_atTop] at hf
  exact hf.bddAbove_range_of_cofinite

/-- To check that a filter is frequently bounded, it suffices to have a witness
which bounds `f` at some point for every admissible set.

This is only an implication, as the other direction is wrong for the trivial filter. -/
/-
**Filter.IsCobounded.mk** 是 Mathlib 中的一个定理，位于命名空间 `Filter.IsCobounded`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {f : Filter α} [IsTrans α r] (a : α), 
  (∀ s ∈ f, ∃ x ∈ s, r a x) → Filter.IsCobounded r f
参数：a : α；∀ s ∈ f, ∃ x ∈ s, r a x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c

--- 原说明 ---
To check that a filter is frequently bounded, it suffices to have a witness
which bounds `f` at some point for every admissible set.

This is only an implication, as the other direction is wrong for the trivial fil
ter.
-/
theorem IsCobounded.mk [IsTrans α r] (a : α) (h : ∀ s ∈ f, ∃ x ∈ s, r a x) : f.IsCobounded r :=
  ⟨a, fun _ s =>
    let ⟨_, h₁, h₂⟩ := h _ s
    _root_.trans h₂ h₁⟩

/-- A filter which is eventually bounded is in particular frequently bounded (in the opposite
direction). At least if the filter is not trivial. -/
/-
**Filter.IsBounded.isCobounded_flip** 是 Mathlib 中的一个定理，位于命名空间 `Filter.IsBounded`
。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {f : Filter α} [IsTrans α r] [f.NeBot]
,   Filter.IsBounded r f → Filter.IsCobounded (flip r) f
参数：flip r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c

--- 原说明 ---
A filter which is eventually bounded is in particular frequently bounded (in the
 opposite
direction). At least if the filter is not trivial.
-/
theorem IsBounded.isCobounded_flip [IsTrans α r] [NeBot f] : f.IsBounded r → f.IsCobounded (flip r)
  | ⟨a, ha⟩ =>
    ⟨a, fun b hb =>
      let ⟨_, rxa, rbx⟩ := (ha.and hb).exists
      show r b a from _root_.trans rbx rxa⟩

@[to_dual isCobounded_ge]
/-
**Filter.IsBounded.isCobounded_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter.IsBounded`。
形式化陈述：∀ {α : Type u_1} {f : Filter α} [inst : Preorder α] [f.NeBot],   Filter.Is
Bounded (fun x1 x2 => x2 ≤ x1) f → Filter.IsCobounded (fun x1 x2 => x1 ≤ x2) f
参数：fun x1 x2 => x2 ≤ x1；fun x1 x2 => x1 ≤ x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.IsBounded.isCobounded_flip`：∀ {α : Type u_1} {r : α → α → Prop} {
f : Filter α} [IsTrans α r] [f.NeBot],   Filter.IsBounded r f → Filter.IsCobound
ed (flip r) f
· 使用定理 `instIsTransGe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x2 ≤ x1
-/
theorem IsBounded.isCobounded_le [Preorder α] [NeBot f] (h : f.IsBounded (fun x1 x2 ↦ x2 ≤ x1)) :
    f.IsCobounded (· ≤ ·) :=
  h.isCobounded_flip
/-
**Filter.IsBoundedUnder.isCoboundedUnder_flip** 是 Mathlib 中的一个定理，位于命名空间 `Filter.
IsBoundedUnder`。
形式化陈述：∀ {α : Type u_1} {γ : Type u_3} {r : α → α → Prop} {u : γ → α} {l : Filter
 γ} [IsTrans α r] [l.NeBot],   Filter.IsBoundedUnder r l u → Filter.IsCoboundedU
nder (flip r) l u
参数：flip r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.IsBounded.isCobounded_flip`：∀ {α : Type u_1} {r : α → α → Prop} {
f : Filter α} [IsTrans α r] [f.NeBot],   Filter.IsBounded r f → Filter.IsCobound
ed (flip r) f
-/
theorem IsBoundedUnder.isCoboundedUnder_flip {u : γ → α} {l : Filter γ} [IsTrans α r] [NeBot l]
    (h : l.IsBoundedUnder r u) : l.IsCoboundedUnder (flip r) u :=
  h.isCobounded_flip

@[to_dual isCoboundedUnder_ge]
/-
**Filter.IsBoundedUnder.isCoboundedUnder_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Is
BoundedUnder`。
形式化陈述：∀ {α : Type u_1} {γ : Type u_3} {u : γ → α} {l : Filter γ} [inst : Preorde
r α] [l.NeBot],   Filter.IsBoundedUnder (fun x1 x2 => x2 ≤ x1) l u → Filter.IsCo
boundedUnder (fun x1 x2 => x1 ≤ x2) l u
参数：fun x1 x2 => x2 ≤ x1；fun x1 x2 => x1 ≤ x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.IsBoundedUnder.isCoboundedUnder_flip`：∀ {α : Type u_1} {γ : Type 
u_3} {r : α → α → Prop} {u : γ → α} {l : Filter γ} [IsTrans α r] [l.NeBot],   Fi
lter.IsBoundedUnder r l u → Filte…
· 使用定理 `instIsTransGe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x2 ≤ x1
-/
theorem IsBoundedUnder.isCoboundedUnder_le {u : γ → α} {l : Filter γ} [Preorder α] [NeBot l]
    (h : l.IsBoundedUnder (fun x1 x2 ↦ x2 ≤ x1) u) : l.IsCoboundedUnder (· ≤ ·) u :=
  h.isCoboundedUnder_flip

@[to_dual isCoboundedUnder_ge_of_eventually_le]
/-
**Filter.isCoboundedUnder_le_of_eventually_le** 是 Mathlib 中的一个引理，位于命名空间 `Filter`
。
形式化陈述：isCoboundedUnder_le_of_eventually_le [Preorder α] (l : Filter ι) [NeBot l]
 {f : ι -> α} {x : α} (hf : forallᶠ i in l, x <= f i) : IsCoboundedUnder (· <= ·
) l f
参数：l : Filter ι；hf : forallᶠ i in l, x <= f i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.IsBoundedUnder.isCoboundedUnder_le`：∀ {α : Type u_1} {γ : Type u_
3} {u : γ → α} {l : Filter γ} [inst : Preorder α] [l.NeBot],   Filter.IsBoundedU
nder (fun x1 x2 => x2 ≤ x1) l u…
-/
lemma isCoboundedUnder_le_of_eventually_le [Preorder α] (l : Filter ι) [NeBot l] {f : ι → α} {x : α}
    (hf : ∀ᶠ i in l, x ≤ f i) :
    IsCoboundedUnder (· ≤ ·) l f :=
  IsBoundedUnder.isCoboundedUnder_le ⟨x, hf⟩

@[to_dual isCoboundedUnder_ge_of_le]
/-
**Filter.isCoboundedUnder_le_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：isCoboundedUnder_le_of_le [Preorder α] (l : Filter ι) [NeBot l] {f : ι -> 
α} {x : α} (hf : forall i, x <= f i) : IsCoboundedUnder (· <= ·) l f
参数：l : Filter ι；hf : forall i, x <= f i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.isCoboundedUnder_le_of_eventually_le`：isCoboundedUnder_le_of_even
tually_le [Preorder α] (l : Filter ι) [NeBot l] {f : ι -> α} {x : α} (hf : foral
lᶠ i in l, x <= f i) : IsCobounde…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
lemma isCoboundedUnder_le_of_le [Preorder α] (l : Filter ι) [NeBot l] {f : ι → α} {x : α}
    (hf : ∀ i, x ≤ f i) :
    IsCoboundedUnder (· ≤ ·) l f :=
  isCoboundedUnder_le_of_eventually_le l (Eventually.of_forall hf)
/-
**Filter.isCobounded_bot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：isCobounded_bot : IsCobounded r ⊥ ↔ exists b, forall x, r b x
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
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isCobounded_bot : IsCobounded r ⊥ ↔ ∃ b, ∀ x, r b x := by simp [IsCobounded]
/-
**Filter.isCobounded_top** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：isCobounded_top : IsCobounded r ⊤ ↔ Nonempty α
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
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isCobounded_top : IsCobounded r ⊤ ↔ Nonempty α := by
  simp +contextual [IsCobounded,
    exists_true_iff_nonempty]
/-
**Filter.isCobounded_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：isCobounded_principal (s : Set α) : (𝓟 s).IsCobounded r ↔ exists b, forall
 a, (forall x in s, r x a) -> r b a
参数：s : Set α。
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
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isCobounded_principal (s : Set α) :
    (𝓟 s).IsCobounded r ↔ ∃ b, ∀ a, (∀ x ∈ s, r x a) → r b a := by simp [IsCobounded]
/-
**Filter.IsCobounded.mono** 是 Mathlib 中的一个定理，位于命名空间 `Filter.IsCobounded`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {f g : Filter α}, f ≤ g → Filter.IsCob
ounded r f → Filter.IsCobounded r g
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsCobounded.mono (h : f ≤ g) : f.IsCobounded r → g.IsCobounded r
  | ⟨b, hb⟩ => ⟨b, fun a ha => hb a (h ha)⟩

/-- For nontrivial filters in linear orders, coboundedness for `≤` implies frequent boundedness
from below. -/
@[to_dual frequently_le
/-- For nontrivial filters in linear orders, coboundedness for `≥` implies frequent boundedness
from above. -/]
/-
**Filter.IsCobounded.frequently_ge** 是 Mathlib 中的一个定理，位于命名空间 `Filter.IsCobounded
`。
形式化陈述：∀ {α : Type u_1} {f : Filter α} [inst : LinearOrder α] [f.NeBot],   Filter
.IsCobounded (fun x1 x2 => x1 ≤ x2) f → ∃ l, ∃ᶠ (x : α) in f, l ≤ x
参数：fun x1 x2 => x1 ≤ x2；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isBot_or_exists_lt`：∀ {α : Type u_1} [inst : Preorder α] [IsCodirectedOr
der α] (a : α), IsBot a ∨ ∃ b, b < a
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `Filter.Frequently.of_forall`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p 
: α → Prop}, (∀ (x : α), p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
-/
lemma IsCobounded.frequently_ge [LinearOrder α] [NeBot f] (cobdd : IsCobounded (· ≤ ·) f) :
    ∃ l, ∃ᶠ x in f, l ≤ x := by
  obtain ⟨t, ht⟩ := cobdd
  rcases isBot_or_exists_lt t with tbot | ⟨t', ht'⟩
  · exact ⟨t, .of_forall fun r ↦ tbot r⟩
  refine ⟨t', fun ev ↦ ?_⟩
  specialize ht t' (by filter_upwards [ev] with _ h using (not_le.mp h).le)
  exact not_lt_of_ge ht ht'

/-- In linear orders, frequent boundedness from below implies coboundedness for `≤`. -/
@[to_dual of_frequently_le
/-- In linear orders, frequent boundedness from above implies coboundedness for `≥`. -/]
/-
**Filter.IsCobounded.of_frequently_ge** 是 Mathlib 中的一个定理，位于命名空间 `Filter.IsCoboun
ded`。
形式化陈述：∀ {α : Type u_1} {f : Filter α} [inst : LinearOrder α] {l : α},   (∃ᶠ (x :
 α) in f, l ≤ x) → Filter.IsCobounded (fun x1 x2 => x1 ≤ x2) f
参数：∃ᶠ (x : α) in f, l ≤ x；fun x1 x2 => x1 ≤ x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isBot_or_exists_lt`：∀ {α : Type u_1} [inst : Preorder α] [IsCodirectedOr
der α] (a : α), IsBot a ∨ ∃ b, b < a
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `Filter.Frequently.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Frequently.and_eventually`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma IsCobounded.of_frequently_ge [LinearOrder α] {l : α} (freq_ge : ∃ᶠ x in f, l ≤ x) :
    IsCobounded (· ≤ ·) f := by
  rcases isBot_or_exists_lt l with lbot | ⟨l', hl'⟩
  · exact ⟨l, fun x _ ↦ lbot x⟩
  refine ⟨l', fun u hu ↦ ?_⟩
  obtain ⟨w, l_le_w, w_le_u⟩ := (freq_ge.and_eventually hu).exists
  exact hl'.le.trans (l_le_w.trans w_le_u)

@[to_dual frequently_le]
/-
**Filter.IsCoboundedUnder.frequently_ge** 是 Mathlib 中的一个定理，位于命名空间 `Filter.IsCobo
undedUnder`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_4} [inst : LinearOrder α] {f : Filter ι} [f.N
eBot] {u : ι → α},   Filter.IsCoboundedUnder (fun x1 x2 => x1 ≤ x2) f u → ∃ a, ∃
ᶠ (x : ι) in f, a ≤ u x
参数：fun x1 x2 => x1 ≤ x2；x : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.IsCobounded.frequently_ge`：∀ {α : Type u_1} {f : Filter α} [inst 
: LinearOrder α] [f.NeBot],   Filter.IsCobounded (fun x1 x2 => x1 ≤ x2) f → ∃ l,
 ∃ᶠ (x : α) in f, l ≤ …
-/
lemma IsCoboundedUnder.frequently_ge [LinearOrder α] {f : Filter ι} [NeBot f] {u : ι → α}
    (h : IsCoboundedUnder (· ≤ ·) f u) :
    ∃ a, ∃ᶠ x in f, a ≤ u x :=
  IsCobounded.frequently_ge h

@[to_dual of_frequently_le]
/-
**Filter.IsCoboundedUnder.of_frequently_ge** 是 Mathlib 中的一个定理，位于命名空间 `Filter.IsC
oboundedUnder`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_4} [inst : LinearOrder α] {f : Filter ι} {u :
 ι → α} {a : α},   (∃ᶠ (x : ι) in f, a ≤ u x) → Filter.IsCoboundedUnder (fun x1 
x2 => x1 ≤ x2) f u
参数：∃ᶠ (x : ι) in f, a ≤ u x；fun x1 x2 => x1 ≤ x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.IsCobounded.of_frequently_ge`：∀ {α : Type u_1} {f : Filter α} [in
st : LinearOrder α] {l : α},   (∃ᶠ (x : α) in f, l ≤ x) → Filter.IsCobounded (fu
n x1 x2 => x1 ≤ x2) f
-/
lemma IsCoboundedUnder.of_frequently_ge [LinearOrder α] {f : Filter ι} {u : ι → α}
    {a : α} (freq_ge : ∃ᶠ x in f, a ≤ u x) :
    IsCoboundedUnder (· ≤ ·) f u :=
  IsCobounded.of_frequently_ge freq_ge

end Relation

section add_and_sum

open Filter Set

variable {α : Type*} {f : Filter α}
variable {R : Type*}

/-
**Filter.isBoundedUnder_sum** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：isBoundedUnder_sum {κ : Type*} [AddCommMonoid R] {r : R -> R -> Prop} (hr 
: forall (v₁ v₂ : α -> R), f.IsBoundedUnder r v₁ -> f.IsBoundedUnder r v₂ -> f.I
sBoundedUnder r (v₁ + v₂)) (hr₀ : r 0 0) {u : κ -> α -> R} (s : Finset κ) (h : f
orall k in s, f.IsBoundedUnder r (u k)) : f.IsBoundedUnder r (∑ k in s, u k)
参数：hr : forall (v₁ v₂ : α -> R), f.IsBoundedUnder r v₁ -> f.IsBoundedUnder r v₂ 
-> f.IsBoundedUnder r (v₁ + v₂)；hr₀ : r 0 0；s : Finset κ；h : forall k in s, f.Is
BoundedUnder r (u k)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_empty`：∀ {ι : Type u_1} {M : Type u_3} {f : ι → M} [inst : Ad
dCommMonoid M], ∑ x ∈ ∅, f x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma isBoundedUnder_sum {κ : Type*} [AddCommMonoid R] {r : R → R → Prop}
    (hr : ∀ (v₁ v₂ : α → R), f.IsBoundedUnder r v₁ → f.IsBoundedUnder r v₂
      → f.IsBoundedUnder r (v₁ + v₂)) (hr₀ : r 0 0)
    {u : κ → α → R} (s : Finset κ) (h : ∀ k ∈ s, f.IsBoundedUnder r (u k)) :
    f.IsBoundedUnder r (∑ k ∈ s, u k) := by
  induction s using Finset.cons_induction
  case empty =>
    rw [Finset.sum_empty]
    exact ⟨0, by simp_all only [eventually_map, Pi.zero_apply, eventually_true]⟩
  case cons k₀ s k₀_notin_s ih =>
    simp only [Finset.forall_mem_cons] at *
    simpa only [Finset.sum_cons] using hr _ _ h.1 (ih h.2)

variable [Preorder R]

@[to_dual isBoundedUnder_ge_add]
/-
**Filter.isBoundedUnder_le_add** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：isBoundedUnder_le_add [Add R] [AddLeftMono R] [AddRightMono R] {u v : α ->
 R} (u_bdd_le : f.IsBoundedUnder (· <= ·) u) (v_bdd_le : f.IsBoundedUnder (· <= 
·) v) : f.IsBoundedUnder (· <= ·) (u + v)
参数：u_bdd_le : f.IsBoundedUnder (· <= ·) u；v_bdd_le : f.IsBoundedUnder (· <= ·) v
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
-/
lemma isBoundedUnder_le_add [Add R] [AddLeftMono R] [AddRightMono R]
    {u v : α → R} (u_bdd_le : f.IsBoundedUnder (· ≤ ·) u) (v_bdd_le : f.IsBoundedUnder (· ≤ ·) v) :
    f.IsBoundedUnder (· ≤ ·) (u + v) := by
  obtain ⟨U, hU⟩ := u_bdd_le
  obtain ⟨V, hV⟩ := v_bdd_le
  use U + V
  simp only [eventually_map, Pi.add_apply] at hU hV ⊢
  filter_upwards [hU, hV] with a hu hv using add_le_add hu hv

@[to_dual isBoundedUnder_ge_sum]
/-
**Filter.isBoundedUnder_le_sum** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：isBoundedUnder_le_sum {κ : Type*} [AddCommMonoid R] [AddLeftMono R] [AddRi
ghtMono R] {u : κ -> α -> R} (s : Finset κ) : (forall k in s, f.IsBoundedUnder (
· <= ·) (u k)) -> f.IsBoundedUnder (· <= ·) (∑ k in s, u k)
参数：s : Finset κ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.isBoundedUnder_sum`：isBoundedUnder_sum {κ : Type*} [AddCommMonoid
 R] {r : R -> R -> Prop} (hr : forall (v₁ v₂ : α -> R), f.IsBoundedUnder r v₁ ->
 f.IsBoundedUnd…
· 使用引理 `Filter.isBoundedUnder_le_add`：isBoundedUnder_le_add [Add R] [AddLeftMono
 R] [AddRightMono R] {u v : α -> R} (u_bdd_le : f.IsBoundedUnder (· <= ·) u) (v_
bdd_le : f.IsBound…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma isBoundedUnder_le_sum {κ : Type*} [AddCommMonoid R] [AddLeftMono R] [AddRightMono R]
    {u : κ → α → R} (s : Finset κ) :
    (∀ k ∈ s, f.IsBoundedUnder (· ≤ ·) (u k)) → f.IsBoundedUnder (· ≤ ·) (∑ k ∈ s, u k) :=
  fun h ↦ isBoundedUnder_sum (fun _ _ ↦ isBoundedUnder_le_add) le_rfl s h

end add_and_sum

section add_and_sum

variable {α R : Type*} [LinearOrder R] [Add R] {f : Filter α} [f.NeBot]
  [AddLeftMono R] [AddRightMono R]
  {u v : α → R}

@[to_dual isCoboundedUnder_ge_add]
/-
**Filter.isCoboundedUnder_le_add** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：isCoboundedUnder_le_add (hu : f.IsBoundedUnder (fun x1 x2 => x2 <= x1) u) 
(hv : f.IsCoboundedUnder (· <= ·) v) : f.IsCoboundedUnder (· <= ·) (u + v)
参数：hu : f.IsBoundedUnder (fun x1 x2 => x2 <= x1) u；hv : f.IsCoboundedUnder (· <=
 ·) v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.IsBoundedUnder.eventually_ge`：∀ {α : Type u_1} {β : Type u_2} [in
st : Preorder α] {f : Filter β} {u : β → α},   Filter.IsBoundedUnder (fun x1 x2 
=> x2 ≤ x1) f u → ∃ a, ∀ᶠ…
· 使用定理 `Filter.IsCoboundedUnder.frequently_ge`：∀ {α : Type u_1} {ι : Type u_4} [
inst : LinearOrder α] {f : Filter ι} [f.NeBot] {u : ι → α},   Filter.IsCobounded
Under (fun x1 x2 => x1 ≤ x2…
· 使用定理 `Filter.IsCoboundedUnder.of_frequently_ge`：∀ {α : Type u_1} {ι : Type u_4
} [inst : LinearOrder α] {f : Filter ι} {u : ι → α} {a : α},   (∃ᶠ (x : ι) in f,
 a ≤ u x) → Filter.IsCobounded…
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Filter.Frequently.and_eventually`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma isCoboundedUnder_le_add (hu : f.IsBoundedUnder (fun x1 x2 ↦ x2 ≤ x1) u)
    (hv : f.IsCoboundedUnder (· ≤ ·) v) :
    f.IsCoboundedUnder (· ≤ ·) (u + v) := by
  obtain ⟨U, hU⟩ := hu.eventually_ge
  obtain ⟨V, hV⟩ := hv.frequently_ge
  apply IsCoboundedUnder.of_frequently_ge (a := U + V)
  exact (hV.and_eventually hU).mono fun x hx ↦ add_le_add hx.2 hx.1

end add_and_sum

section mul

/-
**Filter.isBoundedUnder_le_mul_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：isBoundedUnder_le_mul_of_nonneg [Preorder α] [Mul α] [Zero α] [PosMulMono 
α] [MulPosMono α] {f : Filter ι} {u v : ι -> α} (h₁ : existsᶠ x in f, 0 <= u x) 
(h₂ : IsBoundedUnder (· <= ·) f u) (h₃ : 0 <=ᶠ[f] v) (h₄ : IsBoundedUnder (· <= 
·) f v) : IsBoundedUnder (· <= ·) f (u * v)
参数：h₁ : existsᶠ x in f, 0 <= u x；h₂ : IsBoundedUnder (· <= ·) f u；h₃ : 0 <=ᶠ[f] 
v；h₄ : IsBoundedUnder (· <= ·) f v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.IsBoundedUnder.eventually_le`：∀ {α : Type u_1} {β : Type u_2} [in
st : Preorder α] {f : Filter β} {u : β → α},   Filter.IsBoundedUnder (fun x1 x2 
=> x1 ≤ x2) f u → ∃ a, ∀ᶠ…
· 使用引理 `Filter.isBoundedUnder_of_eventually_le`：isBoundedUnder_of_eventually_le 
{a : α} (h : forallᶠ x in f, u x <= a) : IsBoundedUnder (· <= ·) f u
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.Frequently.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Frequently.and_eventually`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
-/
lemma isBoundedUnder_le_mul_of_nonneg [Preorder α] [Mul α] [Zero α] [PosMulMono α]
    [MulPosMono α] {f : Filter ι} {u v : ι → α} (h₁ : ∃ᶠ x in f, 0 ≤ u x)
    (h₂ : IsBoundedUnder (· ≤ ·) f u) (h₃ : 0 ≤ᶠ[f] v)
    (h₄ : IsBoundedUnder (· ≤ ·) f v) :
    IsBoundedUnder (· ≤ ·) f (u * v) := by
  obtain ⟨U, hU⟩ := h₂.eventually_le
  obtain ⟨V, hV⟩ := h₄.eventually_le
  refine isBoundedUnder_of_eventually_le (a := U * V) ?_
  filter_upwards [hU, hV, h₃] with x x_U x_V v_0
  have U_0 : 0 ≤ U := by
    obtain ⟨y, y_0, y_U⟩ := (h₁.and_eventually hU).exists
    exact y_0.trans y_U
  exact (mul_le_mul_of_nonneg_right x_U v_0).trans (mul_le_mul_of_nonneg_left x_V U_0)
/-
**Filter.isCoboundedUnder_ge_mul_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：isCoboundedUnder_ge_mul_of_nonneg [LinearOrder α] [Mul α] [Zero α] [PosMul
Mono α] [MulPosMono α] {f : Filter ι} [f.NeBot] {u v : ι -> α} (h₁ : 0 <=ᶠ[f] u)
 (h₂ : IsBoundedUnder (· <= ·) f u) (h₃ : 0 <=ᶠ[f] v) (h₄ : IsCoboundedUnder (fu
n x1 x2 => x2 <= x1) f v) : IsCoboundedUnder (fun x1 x2 => x2 <= x1) f (u * v)
参数：h₁ : 0 <=ᶠ[f] u；h₂ : IsBoundedUnder (· <= ·) f u；h₃ : 0 <=ᶠ[f] v；h₄ : IsCobou
ndedUnder (fun x1 x2 => x2 <= x1) f v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.IsBoundedUnder.eventually_le`：∀ {α : Type u_1} {β : Type u_2} [in
st : Preorder α] {f : Filter β} {u : β → α},   Filter.IsBoundedUnder (fun x1 x2 
=> x1 ≤ x2) f u → ∃ a, ∀ᶠ…
· 使用定理 `Filter.IsCoboundedUnder.frequently_le`：∀ {α : Type u_1} {ι : Type u_4} [
inst : LinearOrder α] {f : Filter ι} [f.NeBot] {u : ι → α},   Filter.IsCobounded
Under (fun x1 x2 => x2 ≤ x1…
· 使用定理 `Filter.IsCoboundedUnder.of_frequently_le`：∀ {α : Type u_1} {ι : Type u_4
} [inst : LinearOrder α] {f : Filter ι} {u : ι → α} {a : α},   (∃ᶠ (x : ι) in f,
 u x ≤ a) → Filter.IsCobounded…
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Filter.Frequently.and_eventually`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
-/
lemma isCoboundedUnder_ge_mul_of_nonneg [LinearOrder α] [Mul α] [Zero α] [PosMulMono α]
    [MulPosMono α] {f : Filter ι} [f.NeBot] {u v : ι → α} (h₁ : 0 ≤ᶠ[f] u)
    (h₂ : IsBoundedUnder (· ≤ ·) f u)
    (h₃ : 0 ≤ᶠ[f] v)
    (h₄ : IsCoboundedUnder (fun x1 x2 ↦ x2 ≤ x1) f v) :
    IsCoboundedUnder (fun x1 x2 ↦ x2 ≤ x1) f (u * v) := by
  obtain ⟨U, hU⟩ := h₂.eventually_le
  obtain ⟨V, hV⟩ := h₄.frequently_le
  refine IsCoboundedUnder.of_frequently_le (a := U * V) ?_
  apply (hV.and_eventually (hU.and (h₁.and h₃))).mono
  intro x ⟨x_V, x_U, u_0, v_0⟩
  exact (mul_le_mul_of_nonneg_right x_U v_0).trans (mul_le_mul_of_nonneg_left x_V (u_0.trans x_U))

end mul

section Nonempty
variable [Preorder α] [Nonempty α] {f : Filter β} {u : β → α}

@[to_dual isBounded_ge_atTop]
/-
**Filter.isBounded_le_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：isBounded_le_atBot : (atBot : Filter α).IsBounded (· <= ·)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
· 使用定理 `Filter.eventually_le_atBot`：∀ {α : Type u_3} [inst : Preorder α] (a : α)
, ∀ᶠ (x : α) in Filter.atBot, x ≤ a
-/
theorem isBounded_le_atBot : (atBot : Filter α).IsBounded (· ≤ ·) :=
  ‹Nonempty α›.elim fun a => ⟨a, eventually_le_atBot _⟩

@[to_dual isBoundedUnder_ge_atTop]
/-
**Filter.Tendsto.isBoundedUnder_le_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tends
to`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [Nonempty α] {f : Filt
er β} {u : β → α},   Filter.Tendsto u f Filter.atBot → Filter.IsBoundedUnder (fu
n x1 x2 => x1 ≤ x2) f u
参数：fun x1 x2 => x1 ≤ x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.IsBounded.mono`：∀ {α : Type u_1} {r : α → α → Prop} {f g : Filter
 α}, f ≤ g → Filter.IsBounded r g → Filter.IsBounded r f
· 使用定理 `Filter.isBounded_le_atBot`：isBounded_le_atBot : (atBot : Filter α).IsBou
nded (· <= ·)
-/
theorem Tendsto.isBoundedUnder_le_atBot (h : Tendsto u f atBot) : f.IsBoundedUnder (· ≤ ·) u :=
  isBounded_le_atBot.mono h

@[to_dual]
/-
**Filter.bddAbove_range_of_tendsto_atTop_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter
`。
形式化陈述：bddAbove_range_of_tendsto_atTop_atBot [IsDirectedOrder α] {u : Nat -> α} (
hx : Tendsto u atTop atBot) : BddAbove (Set.range u)
参数：hx : Tendsto u atTop atBot。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.IsBoundedUnder.bddAbove_range`：∀ {β : Type u_2} [inst : Preorder 
β] [IsDirectedOrder β] {f : ℕ → β},   Filter.IsBoundedUnder (fun x1 x2 => x1 ≤ x
2) Filter.atTop f → BddAbo…
· 使用定理 `Filter.Tendsto.isBoundedUnder_le_atBot`：∀ {α : Type u_1} {β : Type u_2} 
[inst : Preorder α] [Nonempty α] {f : Filter β} {u : β → α},   Filter.Tendsto u 
f Filter.atBot → Filter.IsBo…
-/
theorem bddAbove_range_of_tendsto_atTop_atBot [IsDirectedOrder α] {u : ℕ → α}
    (hx : Tendsto u atTop atBot) : BddAbove (Set.range u) :=
  hx.isBoundedUnder_le_atBot.bddAbove_range
/-
**Filter.bddBelow_range_of_tendsto_atTop_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter
`。
形式化陈述：bddBelow_range_of_tendsto_atTop_atTop [IsCodirectedOrder α] {u : Nat -> α}
 (hx : Tendsto u atTop atTop) : BddBelow (Set.range u)
参数：hx : Tendsto u atTop atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.IsBoundedUnder.bddBelow_range`：∀ {β : Type u_2} [inst : Preorder 
β] [IsCodirectedOrder β] {f : ℕ → β},   Filter.IsBoundedUnder (fun x1 x2 => x2 ≤
 x1) Filter.atTop f → BddB…
· 使用定理 `Filter.Tendsto.isBoundedUnder_ge_atTop`：∀ {α : Type u_1} {β : Type u_2} 
[inst : Preorder α] [Nonempty α] {f : Filter β} {u : β → α},   Filter.Tendsto u 
f Filter.atTop → Filter.IsBo…
-/
theorem bddBelow_range_of_tendsto_atTop_atTop [IsCodirectedOrder α] {u : ℕ → α}
    (hx : Tendsto u atTop atTop) : BddBelow (Set.range u) :=
  hx.isBoundedUnder_ge_atTop.bddBelow_range

end Nonempty

@[to_dual isCobounded_ge_of_top]
/-
**Filter.isCobounded_le_of_bot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：isCobounded_le_of_bot [LE α] [OrderBot α] {f : Filter α} : f.IsCobounded (
· <= ·)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem isCobounded_le_of_bot [LE α] [OrderBot α] {f : Filter α} : f.IsCobounded (· ≤ ·) :=
  ⟨⊥, fun _ _ => bot_le⟩

@[to_dual isBounded_ge_of_bot]
/-
**Filter.isBounded_le_of_top** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：isBounded_le_of_top [LE α] [OrderTop α] {f : Filter α} : f.IsBounded (· <=
 ·)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem isBounded_le_of_top [LE α] [OrderTop α] {f : Filter α} : f.IsBounded (· ≤ ·) :=
  ⟨⊤, Eventually.of_forall fun _ => le_top⟩

@[to_dual (attr := simp) isBoundedUnder_ge_comp]
/-
**Filter._root_.OrderIso.isBoundedUnder_le_comp** 是 Mathlib 中的一个定理，位于命名空间 `Filte
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.OrderIso.isBoundedUnder_le_comp [LE α] [LE β] (e : α ≃o β) {l : Filter γ}
    {u : γ → α} : (IsBoundedUnder (· ≤ ·) l fun x => e (u x)) ↔ IsBoundedUnder (· ≤ ·) l u :=
  (Function.Surjective.exists e.surjective).trans <|
    exists_congr fun a => by simp only [eventually_map, e.le_iff_le]

-- TODO: use `to_dual` in combination with `to_additive`
@[to_additive (attr := simp)]
/-
**Filter.isBoundedUnder_le_inv** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：isBoundedUnder_le_inv [CommGroup α] [Preorder α] [IsOrderedMonoid α] {l : 
Filter β} {u : β -> α} : (IsBoundedUnder (· <= ·) l fun x => (u x)⁻¹) ↔ IsBounde
dUnder (· >= ·) l u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.isBoundedUnder_ge_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Ty
pe u_3} [inst : LE α] [inst_1 : LE β] (e : α ≃o β) {l : Filter γ} {u : γ → α},  
 (Filter.IsBoundedUnd…
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem isBoundedUnder_le_inv [CommGroup α] [Preorder α] [IsOrderedMonoid α]
    {l : Filter β} {u : β → α} :
    (IsBoundedUnder (· ≤ ·) l fun x => (u x)⁻¹) ↔ IsBoundedUnder (· ≥ ·) l u :=
  (OrderIso.inv α).isBoundedUnder_ge_comp

@[to_additive (attr := simp)]
/-
**Filter.isBoundedUnder_ge_inv** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：isBoundedUnder_ge_inv [CommGroup α] [Preorder α] [IsOrderedMonoid α] {l : 
Filter β} {u : β -> α} : (IsBoundedUnder (· >= ·) l fun x => (u x)⁻¹) ↔ IsBounde
dUnder (· <= ·) l u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.isBoundedUnder_le_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Ty
pe u_3} [inst : LE α] [inst_1 : LE β] (e : α ≃o β) {l : Filter γ} {u : γ → α},  
 (Filter.IsBoundedUnd…
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
theorem isBoundedUnder_ge_inv [CommGroup α] [Preorder α] [IsOrderedMonoid α]
    {l : Filter β} {u : β → α} :
    (IsBoundedUnder (· ≥ ·) l fun x => (u x)⁻¹) ↔ IsBoundedUnder (· ≤ ·) l u :=
  (OrderIso.inv α).isBoundedUnder_le_comp

@[to_dual]
/-
**Filter.IsBoundedUnder.sup** 是 Mathlib 中的一个定理，位于命名空间 `Filter.IsBoundedUnder`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : SemilatticeSup α] {f : Filter β} {
u v : β → α},   Filter.IsBoundedUnder (fun x1 x2 => x1 ≤ x2) f u →     Filter.Is
BoundedUnder (fun x1 x2 => x1 ≤ x2) f v → Filter.IsBoundedUnder (fun x1 x2 => x1
 ≤ x2) f fun a => u a ⊔ v a
参数：fun x1 x2 => x1 ≤ x2；fun x1 x2 => x1 ≤ x2；fun x1 x2 => x1 ≤ x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
-/
theorem IsBoundedUnder.sup [SemilatticeSup α] {f : Filter β} {u v : β → α} :
    f.IsBoundedUnder (· ≤ ·) u →
      f.IsBoundedUnder (· ≤ ·) v → f.IsBoundedUnder (· ≤ ·) fun a => u a ⊔ v a
  | ⟨bu, (hu : ∀ᶠ x in f, u x ≤ bu)⟩, ⟨bv, (hv : ∀ᶠ x in f, v x ≤ bv)⟩ =>
    ⟨bu ⊔ bv, show ∀ᶠ x in f, u x ⊔ v x ≤ bu ⊔ bv
      by filter_upwards [hu, hv] with _ using sup_le_sup⟩

@[to_dual (attr := simp) isBoundedUnder_ge_inf]
/-
**Filter.isBoundedUnder_le_sup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：isBoundedUnder_le_sup [SemilatticeSup α] {f : Filter β} {u v : β -> α} : (
f.IsBoundedUnder (· <= ·) fun a => u a ⊔ v a) ↔ f.IsBoundedUnder (· <= ·) u ∧ f.
IsBoundedUnder (· <= ·) v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.IsBoundedUnder.mono_le`：∀ {α : Type u_1} {β : Type u_2} [inst : P
reorder β] {l : Filter α} {u v : α → β},   Filter.IsBoundedUnder (fun x1 x2 => x
1 ≤ x2) l u → v ≤ᶠ[…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `Filter.IsBoundedUnder.sup`：∀ {α : Type u_1} {β : Type u_2} [inst : Semil
atticeSup α] {f : Filter β} {u v : β → α},   Filter.IsBoundedUnder (fun x1 x2 =>
 x1 ≤ x2) f u →…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem isBoundedUnder_le_sup [SemilatticeSup α] {f : Filter β} {u v : β → α} :
    (f.IsBoundedUnder (· ≤ ·) fun a => u a ⊔ v a) ↔
      f.IsBoundedUnder (· ≤ ·) u ∧ f.IsBoundedUnder (· ≤ ·) v :=
  ⟨fun h =>
    ⟨h.mono_le <| Eventually.of_forall fun _ => le_sup_left,
      h.mono_le <| Eventually.of_forall fun _ => le_sup_right⟩,
    fun h => h.1.sup h.2⟩
/-
**Filter.isBoundedUnder_le_abs** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：isBoundedUnder_le_abs [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid
 α] {f : Filter β} {u : β -> α} : (f.IsBoundedUnder (· <= ·) fun a => |u a|) ↔ f
.IsBoundedUnder (· <= ·) u ∧ f.IsBoundedUnder (fun x1 x2 => x2 <= x1) u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.isBoundedUnder_le_sup`：isBoundedUnder_le_sup [SemilatticeSup α] {
f : Filter β} {u v : β -> α} : (f.IsBoundedUnder (· <= ·) fun a => u a ⊔ v a) ↔ 
f.IsBoundedUnder (…
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Filter.isBoundedUnder_le_neg`：∀ {α : Type u_1} {β : Type u_2} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α] {l : Filter β}   {u :
 β → α},   (Filter…
-/
theorem isBoundedUnder_le_abs [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    {f : Filter β} {u : β → α} :
    (f.IsBoundedUnder (· ≤ ·) fun a => |u a|) ↔
      f.IsBoundedUnder (· ≤ ·) u ∧ f.IsBoundedUnder (fun x1 x2 ↦ x2 ≤ x1) u :=
  isBoundedUnder_le_sup.trans <| and_congr Iff.rfl isBoundedUnder_le_neg

/-- Filters are automatically bounded or cobounded in complete lattices. To use the same statements
in complete and conditionally complete lattices but let automation fill automatically the
boundedness proofs in complete lattices, we use the tactic `isBoundedDefault` in the statements,
in the form `(hf : f.IsBounded (≥) := by isBoundedDefault)`. -/
macro "isBoundedDefault" : tactic =>
  `(tactic| first
    | apply isCobounded_le_of_bot
    | apply isCobounded_ge_of_top
    | apply isBounded_le_of_top
    | apply isBounded_ge_of_bot
    | assumption)

end Filter

open Filter

section Order

@[to_dual isBoundedUnder_ge_comp_iff]
/-
**Monotone.isBoundedUnder_le_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.isBoundedUnder_le_comp_iff [Nonempty β] [LinearOrder β] [Preorder
 γ] [NoMaxOrder γ] {g : β -> γ} {f : α -> β} {l : Filter α} (hg : Monotone g) (h
g' : Tendsto g atTop atTop) : IsBoundedUnder (· <= ·) l (g ∘ f) ↔ IsBoundedUnder
 (· <= ·) l f
参数：hg : Monotone g；hg' : Tendsto g atTop atTop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Filter.Tendsto.eventually_gt_atTop`：∀ {α : Type u_3} {β : Type u_4} [ins
t : Preorder β] [NoTopOrder β] {f : α → β} {l : Filter α},   Filter.Tendsto f l 
Filter.atTop → ∀ (c : β)…
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Filter.IsBounded.isBoundedUnder`：∀ {α : Type u_1} {β : Type u_2} {r : α 
→ α → Prop} {f : Filter α} {q : β → β → Prop} {u : α → β},   (∀ (a₀ a₁ : α), r a
₀ a₁ → q (u a₀) (u a₁…
-/
theorem Monotone.isBoundedUnder_le_comp_iff [Nonempty β] [LinearOrder β] [Preorder γ] [NoMaxOrder γ]
    {g : β → γ} {f : α → β} {l : Filter α} (hg : Monotone g) (hg' : Tendsto g atTop atTop) :
    IsBoundedUnder (· ≤ ·) l (g ∘ f) ↔ IsBoundedUnder (· ≤ ·) l f := by
  refine ⟨?_, fun h => h.isBoundedUnder (α := β) hg⟩
  rintro ⟨c, hc⟩; rw [eventually_map] at hc
  obtain ⟨b, hb⟩ : ∃ b, ∀ a ≥ b, c < g a := eventually_atTop.1 (hg'.eventually_gt_atTop c)
  exact ⟨b, hc.mono fun x hx => not_lt.1 fun h => (hb _ h.le).not_ge hx⟩

@[to_dual isBoundedUnder_ge_comp_iff]
/-
**Antitone.isBoundedUnder_le_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.isBoundedUnder_le_comp_iff [Nonempty β] [LinearOrder β] [Preorder
 γ] [NoMaxOrder γ] {g : β -> γ} {f : α -> β} {l : Filter α} (hg : Antitone g) (h
g' : Tendsto g atBot atTop) : IsBoundedUnder (· <= ·) l (g ∘ f) ↔ IsBoundedUnder
 (fun x1 x2 => x2 <= x1) l f
参数：hg : Antitone g；hg' : Tendsto g atBot atTop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.isBoundedUnder_ge_comp_iff`：∀ {α : Type u_1} {β : Type u_2} {γ 
: Type u_3} [Nonempty β] [inst : LinearOrder β] [inst_1 : Preorder γ] [NoMinOrde
r γ]   {g : β → γ} {f : α…
· 使用定理 `Antitone.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [in
st_1 : Preorder β] {f : α → β},   Antitone f → Monotone (⇑OrderDual.toDual ∘ f)
-/
theorem Antitone.isBoundedUnder_le_comp_iff [Nonempty β] [LinearOrder β] [Preorder γ] [NoMaxOrder γ]
    {g : β → γ} {f : α → β} {l : Filter α} (hg : Antitone g) (hg' : Tendsto g atBot atTop) :
    IsBoundedUnder (· ≤ ·) l (g ∘ f) ↔ IsBoundedUnder (fun x1 x2 ↦ x2 ≤ x1) l f :=
  hg.dual_right.isBoundedUnder_ge_comp_iff hg'

end Order

section MinMax

/-
**isCoboundedUnder_le_max** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCoboundedUnder_le_max [LinearOrder β] {f : Filter α} {u v : α -> β} (h :
 f.IsCoboundedUnder (· <= ·) u ∨ f.IsCoboundedUnder (· <= ·) v) : f.IsCoboundedU
nder (· <= ·) (fun a => max (u a) (v a))
参数：h : f.IsCoboundedUnder (· <= ·) u ∨ f.IsCoboundedUnder (· <= ·) v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem isCoboundedUnder_le_max [LinearOrder β] {f : Filter α} {u v : α → β}
    (h : f.IsCoboundedUnder (· ≤ ·) u ∨ f.IsCoboundedUnder (· ≤ ·) v) :
    f.IsCoboundedUnder (· ≤ ·) (fun a ↦ max (u a) (v a)) := by
  rcases h with (h' | h') <;>
  · rcases h' with ⟨b, hb⟩
    use b
    intro c hc
    apply hb c
    rw [eventually_map] at hc ⊢
    refine hc.mono (fun _ ↦ ?_)
    simp +contextual only [implies_true, max_le_iff]

open Finset

@[to_dual isBoundedUnder_ge_finset_inf']
/-
**isBoundedUnder_le_finset_sup'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isBoundedUnder_le_finset_sup' [LinearOrder β] [Nonempty β] {f : Filter α} 
{F : ι -> α -> β} {s : Finset ι} (hs : s.Nonempty) (h : forall i in s, f.IsBound
edUnder (· <= ·) (F i)) : f.IsBoundedUnder (· <= ·) (fun a => sup' s hs (fun i =
> F i a))
参数：hs : s.Nonempty；h : forall i in s, f.IsBoundedUnder (· <= ·) (F i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.eventually_all_finset`：∀ {α : Type u} {ι : Type u_2} (I : Finset 
ι) {l : Filter α} {p : ι → α → Prop},   (∀ᶠ (x : α) in l, ∀ i ∈ I, p i x) ↔ ∀ i 
∈ I, ∀ᶠ (x : α) in…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Finset.le_sup'`：le_sup' {b : β} (h : b in s) : f b <= s.sup' ⟨b, h⟩ f
· 使用定理 `Function.sometimes_spec`：sometimes_spec {p : Prop} {α} [Nonempty α] (P :
 α -> Prop) (f : p -> α) (a : p) (h : P (f a)) : P (sometimes f)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem isBoundedUnder_le_finset_sup' [LinearOrder β] [Nonempty β] {f : Filter α} {F : ι → α → β}
    {s : Finset ι} (hs : s.Nonempty) (h : ∀ i ∈ s, f.IsBoundedUnder (· ≤ ·) (F i)) :
    f.IsBoundedUnder (· ≤ ·) (fun a ↦ sup' s hs (fun i ↦ F i a)) := by
  choose! m hm using h
  use sup' s hs m
  simp only [eventually_map] at hm ⊢
  rw [← eventually_all_finset s] at hm
  refine hm.mono fun a h ↦ ?_
  simp only [sup'_le_iff]
  exact fun i i_s ↦ le_trans (h i i_s) (le_sup' m i_s)

@[to_dual isCoboundedUnder_ge_finset_inf']
/-
**isCoboundedUnder_le_finset_sup'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCoboundedUnder_le_finset_sup' [LinearOrder β] {f : Filter α} {F : ι -> α
 -> β} {s : Finset ι} (hs : s.Nonempty) (h : exists i in s, f.IsCoboundedUnder (
· <= ·) (F i)) : f.IsCoboundedUnder (· <= ·) (fun a => sup' s hs (fun i => F i a
))
参数：hs : s.Nonempty；h : exists i in s, f.IsCoboundedUnder (· <= ·) (F i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
-/
theorem isCoboundedUnder_le_finset_sup' [LinearOrder β] {f : Filter α} {F : ι → α → β}
    {s : Finset ι} (hs : s.Nonempty) (h : ∃ i ∈ s, f.IsCoboundedUnder (· ≤ ·) (F i)) :
    f.IsCoboundedUnder (· ≤ ·) (fun a ↦ sup' s hs (fun i ↦ F i a)) := by
  rcases h with ⟨i, i_s, b, hb⟩
  use b
  refine fun c hc ↦ hb c ?_
  rw [eventually_map] at hc ⊢
  refine hc.mono fun a h ↦ ?_
  simp only [sup'_le_iff] at h ⊢
  exact h i i_s

@[to_dual isBoundedUnder_ge_finset_inf]
/-
**isBoundedUnder_le_finset_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isBoundedUnder_le_finset_sup [LinearOrder β] [OrderBot β] {f : Filter α} {
F : ι -> α -> β} {s : Finset ι} (h : forall i in s, f.IsBoundedUnder (· <= ·) (F
 i)) : f.IsBoundedUnder (· <= ·) (fun a => sup s (fun i => F i a))
参数：h : forall i in s, f.IsBoundedUnder (· <= ·) (F i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.eventually_all_finset`：∀ {α : Type u} {ι : Type u_2} (I : Finset 
ι) {l : Filter α} {p : ι → α → Prop},   (∀ᶠ (x : α) in l, ∀ i ∈ I, p i x) ↔ ∀ i 
∈ I, ∀ᶠ (x : α) in…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.sup_mono_fun`：sup_mono_fun {g : β -> α} (h : forall b in s, f b <
= g b) : s.sup f <= s.sup g
· 使用定理 `bot_nonempty`：∀ (α : Type u_1) [Bot α], Nonempty α
· 使用定理 `Function.sometimes_spec`：sometimes_spec {p : Prop} {α} [Nonempty α] (P :
 α -> Prop) (f : p -> α) (a : p) (h : P (f a)) : P (sometimes f)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem isBoundedUnder_le_finset_sup [LinearOrder β] [OrderBot β] {f : Filter α} {F : ι → α → β}
    {s : Finset ι} (h : ∀ i ∈ s, f.IsBoundedUnder (· ≤ ·) (F i)) :
    f.IsBoundedUnder (· ≤ ·) (fun a ↦ sup s (fun i ↦ F i a)) := by
  choose! m hm using h
  use sup s m
  simp only [eventually_map] at hm ⊢
  rw [← eventually_all_finset s] at hm
  exact hm.mono fun _ h ↦ sup_mono_fun h

end MinMax

section FrequentlyBounded

variable {R S : Type*} {F : Filter R} [LinearOrder R] [LinearOrder S]

@[to_dual frequently_le_map_of_frequently_le]
/-
**Monotone.frequently_ge_map_of_frequently_ge** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Monotone.frequently_ge_map_of_frequently_ge {f : R -> S} (f_incr : Monoton
e f) {l : R} (freq_ge : existsᶠ x in F, l <= x) : existsᶠ x' in F.map f, f l <= 
x'
参数：f_incr : Monotone f；freq_ge : existsᶠ x in F, l <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
-/
lemma Monotone.frequently_ge_map_of_frequently_ge {f : R → S} (f_incr : Monotone f)
    {l : R} (freq_ge : ∃ᶠ x in F, l ≤ x) :
    ∃ᶠ x' in F.map f, f l ≤ x' := by
  refine fun ev ↦ freq_ge ?_
  simp only [not_le] at ev freq_ge ⊢
  filter_upwards [ev] with z hz
  by_contra con
  exact lt_irrefl (f l) <| lt_of_le_of_lt (f_incr <| not_lt.mp con) hz

@[to_dual frequently_ge_map_of_frequently_le]
/-
**Antitone.frequently_le_map_of_frequently_ge** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Antitone.frequently_le_map_of_frequently_ge {f : R -> S} (f_decr : Antiton
e f) {l : R} (frbdd : existsᶠ x in F, l <= x) : existsᶠ y in F.map f, y <= f l
参数：f_decr : Antitone f；frbdd : existsᶠ x in F, l <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Monotone.frequently_ge_map_of_frequently_ge`：Monotone.frequently_ge_map_
of_frequently_ge {f : R -> S} (f_incr : Monotone f) {l : R} (freq_ge : existsᶠ x
 in F, l <= x) : existsᶠ x' in F.…
-/
lemma Antitone.frequently_le_map_of_frequently_ge {f : R → S} (f_decr : Antitone f)
    {l : R} (frbdd : ∃ᶠ x in F, l ≤ x) :
    ∃ᶠ y in F.map f, y ≤ f l :=
  Monotone.frequently_ge_map_of_frequently_ge (S := Sᵒᵈ) f_decr frbdd

@[to_dual isCoboundedUnder_ge_of_isCobounded]
/-
**Monotone.isCoboundedUnder_le_of_isCobounded** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Monotone.isCoboundedUnder_le_of_isCobounded {f : R -> S} (f_incr : Monoton
e f) [NeBot F] (cobdd : IsCobounded (· <= ·) F) : F.IsCoboundedUnder (· <= ·) f
参数：f_incr : Monotone f；cobdd : IsCobounded (· <= ·) F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.IsCobounded.frequently_ge`：∀ {α : Type u_1} {f : Filter α} [inst 
: LinearOrder α] [f.NeBot],   Filter.IsCobounded (fun x1 x2 => x1 ≤ x2) f → ∃ l,
 ∃ᶠ (x : α) in f, l ≤ …
· 使用定理 `Filter.IsCobounded.of_frequently_ge`：∀ {α : Type u_1} {f : Filter α} [in
st : LinearOrder α] {l : α},   (∃ᶠ (x : α) in f, l ≤ x) → Filter.IsCobounded (fu
n x1 x2 => x1 ≤ x2) f
· 使用引理 `Monotone.frequently_ge_map_of_frequently_ge`：Monotone.frequently_ge_map_
of_frequently_ge {f : R -> S} (f_incr : Monotone f) {l : R} (freq_ge : existsᶠ x
 in F, l <= x) : existsᶠ x' in F.…
-/
lemma Monotone.isCoboundedUnder_le_of_isCobounded {f : R → S} (f_incr : Monotone f)
    [NeBot F] (cobdd : IsCobounded (· ≤ ·) F) :
    F.IsCoboundedUnder (· ≤ ·) f := by
  obtain ⟨l, hl⟩ := IsCobounded.frequently_ge cobdd
  exact IsCobounded.of_frequently_ge <| f_incr.frequently_ge_map_of_frequently_ge hl

@[to_dual isCoboundedUnder_ge_of_isCobounded]
/-
**Antitone.isCoboundedUnder_le_of_isCobounded** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Antitone.isCoboundedUnder_le_of_isCobounded {f : R -> S} (f_decr : Antiton
e f) [NeBot F] (cobdd : IsCobounded (fun x1 x2 => x2 <= x1) F) : F.IsCoboundedUn
der (· <= ·) f
参数：f_decr : Antitone f；cobdd : IsCobounded (fun x1 x2 => x2 <= x1) F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.IsCobounded.frequently_le`：∀ {α : Type u_1} {f : Filter α} [inst 
: LinearOrder α] [f.NeBot],   Filter.IsCobounded (fun x1 x2 => x2 ≤ x1) f → ∃ l,
 ∃ᶠ (x : α) in f, x ≤ …
· 使用定理 `Filter.IsCobounded.of_frequently_ge`：∀ {α : Type u_1} {f : Filter α} [in
st : LinearOrder α] {l : α},   (∃ᶠ (x : α) in f, l ≤ x) → Filter.IsCobounded (fu
n x1 x2 => x1 ≤ x2) f
· 使用定理 `Antitone.frequently_ge_map_of_frequently_le`：∀ {R : Type u_5} {S : Type 
u_6} {F : Filter R} [inst : LinearOrder R] [inst_1 : LinearOrder S] {f : R → S},
   Antitone f → ∀ {l : R}, (∃ᶠ (x…
-/
lemma Antitone.isCoboundedUnder_le_of_isCobounded {f : R → S} (f_decr : Antitone f)
    [NeBot F] (cobdd : IsCobounded (fun x1 x2 ↦ x2 ≤ x1) F) :
    F.IsCoboundedUnder (· ≤ ·) f := by
  obtain ⟨l, hl⟩ := IsCobounded.frequently_le cobdd
  exact IsCobounded.of_frequently_ge <| f_decr.frequently_ge_map_of_frequently_le hl

end FrequentlyBounded

