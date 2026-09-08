/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
module

public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Map

/-!
# Convergence in terms of filters

The general notion of limit of a map with respect to filters on the source and target types
is `Filter.Tendsto`. It is defined in terms of the order and the push-forward operation.

For instance, anticipating on Topology.Basic, the statement: "if a sequence `u` converges to
some `x` and `u n` belongs to a set `M` for `n` large enough then `x` is in the closure of
`M`" is formalized as: `Tendsto u atTop (𝓝 x) → (∀ᶠ n in atTop, u n ∈ M) → x ∈ closure M`,
which is a special case of `mem_closure_of_tendsto` from `Topology/Basic`.
-/

public section

open Set Filter

variable {α β γ : Type*} {ι : Sort*}

namespace Filter

/-
**Filter.tendsto_def** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_def {f : α -> β} {l₁ : Filter α} {l₂ : Filter β} : Tendsto f l₁ l₂
 ↔ forall s in l₂, f ⁻¹' s in l₁
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_def {f : α → β} {l₁ : Filter α} {l₂ : Filter β} :
    Tendsto f l₁ l₂ ↔ ∀ s ∈ l₂, f ⁻¹' s ∈ l₁ :=
  Iff.rfl
/-
**Filter.tendsto_iff_eventually** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_iff_eventually {f : α -> β} {l₁ : Filter α} {l₂ : Filter β} : Tend
sto f l₁ l₂ ↔ forall ⦃p : β -> Prop⦄, (forallᶠ y in l₂, p y) -> forallᶠ x in l₁,
 p (f x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_iff_eventually {f : α → β} {l₁ : Filter α} {l₂ : Filter β} :
    Tendsto f l₁ l₂ ↔ ∀ ⦃p : β → Prop⦄, (∀ᶠ y in l₂, p y) → ∀ᶠ x in l₁, p (f x) :=
  Iff.rfl
/-
**Filter.tendsto_iff_forall_eventually_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_iff_forall_eventually_mem {f : α -> β} {l₁ : Filter α} {l₂ : Filte
r β} : Tendsto f l₁ l₂ ↔ forall s in l₂, forallᶠ x in l₁, f x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_iff_forall_eventually_mem {f : α → β} {l₁ : Filter α} {l₂ : Filter β} :
    Tendsto f l₁ l₂ ↔ ∀ s ∈ l₂, ∀ᶠ x in l₁, f x ∈ s :=
  Iff.rfl
/-
**Filter.Tendsto.eventually_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ : Filter α} {l₂ : Filter β
} {s : Set β},   Filter.Tendsto f l₁ l₂ → s ∈ l₂ → ∀ᶠ (x : α) in l₁, f x ∈ s
参数：x : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Tendsto.eventually_mem {f : α → β} {l₁ : Filter α} {l₂ : Filter β} {s : Set β}
    (hf : Tendsto f l₁ l₂) (h : s ∈ l₂) : ∀ᶠ x in l₁, f x ∈ s :=
  hf h
/-
**Filter.Tendsto.eventually** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ : Filter α} {l₂ : Filter β
} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y : β) in l₂, p y) → ∀ᶠ (x : α
) in l₁, p (f x)
参数：∀ᶠ (y : β) in l₂, p y；x : α；f x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Tendsto.eventually {f : α → β} {l₁ : Filter α} {l₂ : Filter β} {p : β → Prop}
    (hf : Tendsto f l₁ l₂) (h : ∀ᶠ y in l₂, p y) : ∀ᶠ x in l₁, p (f x) :=
  hf h
/-
**Filter.not_tendsto_iff_exists_frequently_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Fil
ter`。
形式化陈述：not_tendsto_iff_exists_frequently_notMem {f : α -> β} {l₁ : Filter α} {l₂ 
: Filter β} : ¬Tendsto f l₁ l₂ ↔ exists s in l₂, existsᶠ x in l₁, f x ∉ s
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
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem not_tendsto_iff_exists_frequently_notMem {f : α → β} {l₁ : Filter α} {l₂ : Filter β} :
    ¬Tendsto f l₁ l₂ ↔ ∃ s ∈ l₂, ∃ᶠ x in l₁, f x ∉ s := by
  simp only [tendsto_iff_forall_eventually_mem, not_forall, exists_prop, not_eventually]
/-
**Filter.Tendsto.frequently** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ : Filter α} {l₂ : Filter β
} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∃ᶠ (x : α) in l₁, p (f x)) → ∃ᶠ (y
 : β) in l₂, p y
参数：∃ᶠ (x : α) in l₁, p (f x)；y : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
-/
theorem Tendsto.frequently {f : α → β} {l₁ : Filter α} {l₂ : Filter β} {p : β → Prop}
    (hf : Tendsto f l₁ l₂) (h : ∃ᶠ x in l₁, p (f x)) : ∃ᶠ y in l₂, p y :=
  mt hf.eventually h
/-
**Filter.Tendsto.frequently_map** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l₁ : Filter α} {l₂ : Filter β} {p : α → P
rop} {q : β → Prop} (f : α → β),   Filter.Tendsto f l₁ l₂ → (∀ (x : α), p x → q 
(f x)) → (∃ᶠ (x : α) in l₁, p x) → ∃ᶠ (y : β) in l₂, q y
参数：f : α → β；∀ (x : α), p x → q (f x)；∃ᶠ (x : α) in l₁, p x；y : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.frequently`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∃ᶠ (x
 : α) in l₁, p …
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
-/
theorem Tendsto.frequently_map {l₁ : Filter α} {l₂ : Filter β} {p : α → Prop} {q : β → Prop}
    (f : α → β) (c : Filter.Tendsto f l₁ l₂) (w : ∀ x, p x → q (f x)) (h : ∃ᶠ x in l₁, p x) :
    ∃ᶠ y in l₂, q y :=
  c.frequently (h.mono w)

@[simp]
/-
**Filter.tendsto_bot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_bot {f : α -> β} {l : Filter β} : Tendsto f ⊥ l
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_bot`：∀ {α : Type u_1} {β : Type u_2} {m : α → β}, Filter.map 
m ⊥ = ⊥
-/
theorem tendsto_bot {f : α → β} {l : Filter β} : Tendsto f ⊥ l := by simp [Tendsto]

@[simp]
/-
**Filter.tendsto_bot_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_bot_right_iff {f : α -> β} {l : Filter α} : Tendsto f l ⊥ ↔ l = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_bot_right_iff {f : α → β} {l : Filter α} : Tendsto f l ⊥ ↔ l = ⊥  := by
  simp [Tendsto]
/-
**Filter.Tendsto.of_neBot_imp** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {la : Filter α} {lb : Filter β
},   (la.NeBot → Filter.Tendsto f la lb) → Filter.Tendsto f la lb
参数：la.NeBot → Filter.Tendsto f la lb。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `Filter.tendsto_bot`：tendsto_bot {f : α -> β} {l : Filter β} : Tendsto f 
⊥ l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Tendsto.of_neBot_imp {f : α → β} {la : Filter α} {lb : Filter β}
    (h : NeBot la → Tendsto f la lb) : Tendsto f la lb := by
  rcases eq_or_neBot la with rfl | hla
  · exact tendsto_bot
  · exact h hla
/-
**Filter.tendsto_top** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : Filter α}, Filter.Tendsto
 f l ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_top`：le_top : a <= ⊤
-/
@[simp] theorem tendsto_top {f : α → β} {l : Filter α} : Tendsto f l ⊤ := le_top
/-
**Filter.le_map_of_right_inverse** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：le_map_of_right_inverse {mab : α -> β} {mba : β -> α} {f : Filter α} {g : 
Filter β} (h₁ : mab ∘ mba =ᶠ[g] id) (h₂ : Tendsto mba g f) : g <= map mab f
参数：h₁ : mab ∘ mba =ᶠ[g] id；h₂ : Tendsto mba g f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_id`：map_id : Filter.map id f = f
· 使用定理 `Filter.map_congr`：map_congr {m₁ m₂ : α -> β} {f : Filter α} (h : m₁ =ᶠ[f
] m₂) : map m₁ f = map m₂ f
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
-/
theorem le_map_of_right_inverse {mab : α → β} {mba : β → α} {f : Filter α} {g : Filter β}
    (h₁ : mab ∘ mba =ᶠ[g] id) (h₂ : Tendsto mba g f) : g ≤ map mab f := by
  rw [← @map_id _ g, ← map_congr h₁, ← map_map]
  exact map_mono h₂
/-
**Filter.tendsto_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_of_isEmpty [IsEmpty α] {f : α -> β} {la : Filter α} {lb : Filter β
} : Tendsto f la lb
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.filter_eq_bot_of_isEmpty`：filter_eq_bot_of_isEmpty [IsEmpty α] (f
 : Filter α) : f = ⊥
-/
theorem tendsto_of_isEmpty [IsEmpty α] {f : α → β} {la : Filter α} {lb : Filter β} :
    Tendsto f la lb := by simp only [filter_eq_bot_of_isEmpty la, tendsto_bot]
/-
**Filter.eventuallyEq_of_left_inv_of_right_inv** 是 Mathlib 中的一个定理，位于命名空间 `Filter
`。
形式化陈述：eventuallyEq_of_left_inv_of_right_inv {f : α -> β} {g₁ g₂ : β -> α} {fa : 
Filter α} {fb : Filter β} (hleft : forallᶠ x in fa, g₁ (f x) = x) (hright : fora
llᶠ y in fb, f (g₂ y) = y) (htendsto : Tendsto g₂ fb fa) : g₁ =ᶠ[fb] g₂
参数：hleft : forallᶠ x in fa, g₁ (f x) = x；hright : forallᶠ y in fb, f (g₂ y) = y；
htendsto : Tendsto g₂ fb fa。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem eventuallyEq_of_left_inv_of_right_inv {f : α → β} {g₁ g₂ : β → α} {fa : Filter α}
    {fb : Filter β} (hleft : ∀ᶠ x in fa, g₁ (f x) = x) (hright : ∀ᶠ y in fb, f (g₂ y) = y)
    (htendsto : Tendsto g₂ fb fa) : g₁ =ᶠ[fb] g₂ :=
  (htendsto.eventually hleft).mp <| hright.mono fun _ hr hl => (congr_arg g₁ hr.symm).trans hl
/-
**Filter.tendsto_iff_comap** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_iff_comap {f : α -> β} {l₁ : Filter α} {l₂ : Filter β} : Tendsto f
 l₁ l₂ ↔ l₁ <= l₂.comap f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.map_le_iff_le_comap`：map_le_iff_le_comap : map m f <= g ↔ f <= co
map m g
-/
theorem tendsto_iff_comap {f : α → β} {l₁ : Filter α} {l₂ : Filter β} :
    Tendsto f l₁ l₂ ↔ l₁ ≤ l₂.comap f :=
  map_le_iff_le_comap

alias ⟨Tendsto.le_comap, _⟩ := tendsto_iff_comap
/-
**Filter.Tendsto.disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {la₁ la₂ : Filter α} {lb₁ lb₂ 
: Filter β},   Filter.Tendsto f la₁ lb₁ → Disjoint lb₁ lb₂ → Filter.Tendsto f la
₂ lb₂ → Disjoint la₁ la₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `Filter.Tendsto.le_comap`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁
 : Filter α} {l₂ : Filter β},   Filter.Tendsto f l₁ l₂ → l₁ ≤ Filter.comap f l₂
· 使用定理 `Filter.disjoint_comap`：disjoint_comap (h : Disjoint g₁ g₂) : Disjoint (c
omap m g₁) (comap m g₂)
-/
protected theorem Tendsto.disjoint {f : α → β} {la₁ la₂ : Filter α} {lb₁ lb₂ : Filter β}
    (h₁ : Tendsto f la₁ lb₁) (hd : Disjoint lb₁ lb₂) (h₂ : Tendsto f la₂ lb₂) : Disjoint la₁ la₂ :=
  (disjoint_comap hd).mono h₁.le_comap h₂.le_comap
/-
**Filter.tendsto_congr'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_congr' {f₁ f₂ : α -> β} {l₁ : Filter α} {l₂ : Filter β} (hl : f₁ =
ᶠ[l₁] f₂) : Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂
参数：hl : f₁ =ᶠ[l₁] f₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.Tendsto.eq_1`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (l₁ : F
ilter α) (l₂ : Filter β),   Filter.Tendsto f l₁ l₂ = (Filter.map f l₁ ≤ l₂)
· 使用定理 `Filter.map_congr`：map_congr {m₁ m₂ : α -> β} {f : Filter α} (h : m₁ =ᶠ[f
] m₂) : map m₁ f = map m₂ f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_congr' {f₁ f₂ : α → β} {l₁ : Filter α} {l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂) :
    Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂ := by rw [Tendsto, Tendsto, map_congr hl]
/-
**Filter.Tendsto.congr'** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l₁ : Filter α} {l₂ : Filt
er β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filter.Tendsto f₂ l₁ l₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.tendsto_congr'`：tendsto_congr' {f₁ f₂ : α -> β} {l₁ : Filter α} {
l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂) : Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂
-/
theorem Tendsto.congr' {f₁ f₂ : α → β} {l₁ : Filter α} {l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂)
    (h : Tendsto f₁ l₁ l₂) : Tendsto f₂ l₁ l₂ :=
  (tendsto_congr' hl).1 h
/-
**Filter.tendsto_congr** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_congr {f₁ f₂ : α -> β} {l₁ : Filter α} {l₂ : Filter β} (h : forall
 x, f₁ x = f₂ x) : Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂
参数：h : forall x, f₁ x = f₂ x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_congr'`：tendsto_congr' {f₁ f₂ : α -> β} {l₁ : Filter α} {
l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂) : Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
theorem tendsto_congr {f₁ f₂ : α → β} {l₁ : Filter α} {l₂ : Filter β} (h : ∀ x, f₁ x = f₂ x) :
    Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂ :=
  tendsto_congr' (univ_mem' h)
/-
**Filter.Tendsto.congr** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l₁ : Filter α} {l₂ : Filt
er β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁ l₂ → Filter.Tendsto f₂ 
l₁ l₂
参数：∀ (x : α), f₁ x = f₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.tendsto_congr`：tendsto_congr {f₁ f₂ : α -> β} {l₁ : Filter α} {l₂
 : Filter β} (h : forall x, f₁ x = f₂ x) : Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂
-/
theorem Tendsto.congr {f₁ f₂ : α → β} {l₁ : Filter α} {l₂ : Filter β} (h : ∀ x, f₁ x = f₂ x) :
    Tendsto f₁ l₁ l₂ → Tendsto f₂ l₁ l₂ :=
  (tendsto_congr h).1
/-
**Filter.tendsto_id'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_id' {x y : Filter α} : Tendsto id x y ↔ x <= y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_id' {x y : Filter α} : Tendsto id x y ↔ x ≤ y :=
  Iff.rfl
/-
**Filter.tendsto_id** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_id {x : Filter α} : Tendsto id x x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem tendsto_id {x : Filter α} : Tendsto id x x :=
  le_refl x
/-
**Filter.Tendsto.comp** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β} {g : β → γ} {x 
: Filter α} {y : Filter β} {z : Filter γ},   Filter.Tendsto g y z → Filter.Tends
to f x y → Filter.Tendsto (g ∘ f) x z
参数：g ∘ f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Tendsto.comp {f : α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ}
    (hg : Tendsto g y z) (hf : Tendsto f x y) : Tendsto (g ∘ f) x z := fun _ hs => hf (hg hs)
/-
**Filter.Tendsto.iterate** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {f : α → α} {l : Filter α}, Filter.Tendsto f l l → ∀ (n :
 ℕ), Filter.Tendsto f^[n] l l
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Tendsto.iterate {f : α → α} {l : Filter α} (h : Tendsto f l l) :
    ∀ n, Tendsto (f^[n]) l l
  | 0 => tendsto_id
  | (n + 1) => (h.iterate n).comp h
/-
**Filter.Tendsto.mono_left** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x y : Filter α} {z : Filter β
},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f y z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
-/
theorem Tendsto.mono_left {f : α → β} {x y : Filter α} {z : Filter β} (hx : Tendsto f x z)
    (h : y ≤ x) : Tendsto f y z :=
  (map_mono h).trans hx
/-
**Filter.Tendsto.mono_right** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x : Filter α} {y z : Filter β
},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto f x z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem Tendsto.mono_right {f : α → β} {x : Filter α} {y z : Filter β} (hy : Tendsto f x y)
    (hz : y ≤ z) : Tendsto f x z :=
  le_trans hy hz
/-
**Filter.Tendsto.neBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x : Filter α} {y : Filter β},
   Filter.Tendsto f x y → ∀ [hx : x.NeBot], y.NeBot
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.NeBot.mono`：∀ {α : Type u} {f g : Filter α}, f.NeBot → f ≤ g → g.
NeBot
· 使用定理 `Filter.NeBot.map`：∀ {α : Type u_1} {β : Type u_2} {f : Filter α}, f.NeBo
t → ∀ (m : α → β), (Filter.map m f).NeBot
-/
theorem Tendsto.neBot {f : α → β} {x : Filter α} {y : Filter β} (h : Tendsto f x y) [hx : NeBot x] :
    NeBot y :=
  (hx.map _).mono h
/-
**Filter.tendsto_map** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_map {f : α -> β} {x : Filter α} : Tendsto f x (map f x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem tendsto_map {f : α → β} {x : Filter α} : Tendsto f x (map f x) :=
  le_refl (map f x)

@[simp]
/-
**Filter.tendsto_map'_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : β → γ} {g : α → β} {x 
: Filter α} {y : Filter γ},   Filter.Tendsto f (Filter.map g x) y ↔ Filter.Tends
to (f ∘ g) x y
参数：Filter.map g x；f ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.Tendsto.eq_1`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (l₁ : F
ilter α) (l₂ : Filter β),   Filter.Tendsto f l₁ l₂ = (Filter.map f l₁ ≤ l₂)
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_map'_iff {f : β → γ} {g : α → β} {x : Filter α} {y : Filter γ} :
    Tendsto f (map g x) y ↔ Tendsto (f ∘ g) x y := by
  rw [Tendsto, Tendsto, map_map]

alias ⟨_, tendsto_map'⟩ := tendsto_map'_iff
/-
**Filter.tendsto_comap** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_comap {f : α -> β} {x : Filter β} : Tendsto f (comap f x) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.map_comap_le`：map_comap_le : map m (comap m g) <= g
-/
theorem tendsto_comap {f : α → β} {x : Filter β} : Tendsto f (comap f x) x :=
  map_comap_le

@[simp]
/-
**Filter.tendsto_comap_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_comap_iff {f : α -> β} {g : β -> γ} {a : Filter α} {c : Filter γ} 
: Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_comap`：tendsto_comap {f : α -> β} {x : Filter β} : Tendst
o f (comap f x) x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.map_le_iff_le_comap`：map_le_iff_le_comap : map m f <= g ↔ f <= co
map m g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
-/
theorem tendsto_comap_iff {f : α → β} {g : β → γ} {a : Filter α} {c : Filter γ} :
    Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c :=
  ⟨fun h => tendsto_comap.comp h, fun h => map_le_iff_le_comap.mp <| by rwa [map_map]⟩
/-
**Filter.tendsto_comap'_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {m : α → β} {f : Filter α} 
{g : Filter β} {i : γ → α},   Set.range i ∈ f → (Filter.Tendsto (m ∘ i) (Filter.
comap i f) g ↔ Filter.Tendsto m f g)
参数：Filter.Tendsto (m ∘ i) (Filter.comap i f) g ↔ Filter.Tendsto m f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.Tendsto.eq_1`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (l₁ : F
ilter α) (l₂ : Filter β),   Filter.Tendsto f l₁ l₂ = (Filter.map f l₁ ≤ l₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_compose`：map_compose : Filter.map m' ∘ Filter.map m = Filter.
map (m' ∘ m)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.map_comap_of_mem`：map_comap_of_mem {f : Filter β} {m : α -> β} (h
f : range m in f) : (f.comap m).map m = f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_comap'_iff {m : α → β} {f : Filter α} {g : Filter β} {i : γ → α} (h : range i ∈ f) :
    Tendsto (m ∘ i) (comap i f) g ↔ Tendsto m f g := by
  rw [Tendsto, ← map_compose]
  simp only [(· ∘ ·), map_comap_of_mem h, Tendsto]
/-
**Filter.Tendsto.of_tendsto_comp** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β} {g : β → γ} {a 
: Filter α} {b : Filter β} {c : Filter γ},   Filter.Tendsto (g ∘ f) a c → Filter
.comap g c ≤ b → Filter.Tendsto f a b
参数：g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.tendsto_iff_comap`：tendsto_iff_comap {f : α -> β} {l₁ : Filter α}
 {l₂ : Filter β} : Tendsto f l₁ l₂ ↔ l₁ <= l₂.comap f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `Filter.comap_mono`：comap_mono : Monotone (comap m)
-/
theorem Tendsto.of_tendsto_comp {f : α → β} {g : β → γ} {a : Filter α} {b : Filter β} {c : Filter γ}
    (hfg : Tendsto (g ∘ f) a c) (hg : comap g c ≤ b) : Tendsto f a b := by
  rw [tendsto_iff_comap] at hfg ⊢
  calc
    a ≤ comap (g ∘ f) c := hfg
    _ ≤ comap f b := by simpa [comap_comap] using comap_mono hg
/-
**Filter.comap_eq_of_inverse** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_eq_of_inverse {f : Filter α} {g : Filter β} {φ : α -> β} (ψ : β -> α
) (eq : ψ ∘ φ = id) (hφ : Tendsto φ f g) (hψ : Tendsto ψ g f) : comap φ g = f
参数：ψ : β -> α；eq : ψ ∘ φ = id；hφ : Tendsto φ f g；hψ : Tendsto ψ g f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Filter.comap_mono`：comap_mono : Monotone (comap m)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.map_le_iff_le_comap`：map_le_iff_le_comap : map m f <= g ↔ f <= co
map m g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `Filter.comap_id`：comap_id : comap id f = f
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem comap_eq_of_inverse {f : Filter α} {g : Filter β} {φ : α → β} (ψ : β → α) (eq : ψ ∘ φ = id)
    (hφ : Tendsto φ f g) (hψ : Tendsto ψ g f) : comap φ g = f := by
  refine ((comap_mono <| map_le_iff_le_comap.1 hψ).trans ?_).antisymm (map_le_iff_le_comap.1 hφ)
  rw [comap_comap, eq, comap_id]
/-
**Filter.map_eq_of_inverse** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_eq_of_inverse {f : Filter α} {g : Filter β} {φ : α -> β} (ψ : β -> α) 
(eq : φ ∘ ψ = id) (hφ : Tendsto φ f g) (hψ : Tendsto ψ g f) : map φ f = g
参数：ψ : β -> α；eq : φ ∘ ψ = id；hφ : Tendsto φ f g；hψ : Tendsto ψ g f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `Filter.map_id`：map_id : Filter.map id f = f
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
-/
theorem map_eq_of_inverse {f : Filter α} {g : Filter β} {φ : α → β} (ψ : β → α) (eq : φ ∘ ψ = id)
    (hφ : Tendsto φ f g) (hψ : Tendsto ψ g f) : map φ f = g := by
  refine le_antisymm hφ (le_trans ?_ (map_mono hψ))
  rw [map_map, eq, map_id]
/-
**Filter.tendsto_inf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_inf {f : α -> β} {x : Filter α} {y₁ y₂ : Filter β} : Tendsto f x (
y₁ ⊓ y₂) ↔ Tendsto f x y₁ ∧ Tendsto f x y₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_inf {f : α → β} {x : Filter α} {y₁ y₂ : Filter β} :
    Tendsto f x (y₁ ⊓ y₂) ↔ Tendsto f x y₁ ∧ Tendsto f x y₂ := by
  simp only [Tendsto, le_inf_iff]
/-
**Filter.tendsto_inf_left** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_inf_left {f : α -> β} {x₁ x₂ : Filter α} {y : Filter β} (h : Tends
to f x₁ y) : Tendsto f (x₁ ⊓ x₂) y
参数：h : Tendsto f x₁ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem tendsto_inf_left {f : α → β} {x₁ x₂ : Filter α} {y : Filter β} (h : Tendsto f x₁ y) :
    Tendsto f (x₁ ⊓ x₂) y :=
  le_trans (map_mono inf_le_left) h
/-
**Filter.tendsto_inf_right** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_inf_right {f : α -> β} {x₁ x₂ : Filter α} {y : Filter β} (h : Tend
sto f x₂ y) : Tendsto f (x₁ ⊓ x₂) y
参数：h : Tendsto f x₂ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem tendsto_inf_right {f : α → β} {x₁ x₂ : Filter α} {y : Filter β} (h : Tendsto f x₂ y) :
    Tendsto f (x₁ ⊓ x₂) y :=
  le_trans (map_mono inf_le_right) h
/-
**Filter.Tendsto.inf** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x₁ x₂ : Filter α} {y₁ y₂ : Fi
lter β},   Filter.Tendsto f x₁ y₁ → Filter.Tendsto f x₂ y₂ → Filter.Tendsto f (x
₁ ⊓ x₂) (y₁ ⊓ y₂)
参数：x₁ ⊓ x₂；y₁ ⊓ y₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_inf`：tendsto_inf {f : α -> β} {x : Filter α} {y₁ y₂ : Fil
ter β} : Tendsto f x (y₁ ⊓ y₂) ↔ Tendsto f x y₁ ∧ Tendsto f x y₂
· 使用定理 `Filter.tendsto_inf_left`：tendsto_inf_left {f : α -> β} {x₁ x₂ : Filter α
} {y : Filter β} (h : Tendsto f x₁ y) : Tendsto f (x₁ ⊓ x₂) y
· 使用定理 `Filter.tendsto_inf_right`：tendsto_inf_right {f : α -> β} {x₁ x₂ : Filter
 α} {y : Filter β} (h : Tendsto f x₂ y) : Tendsto f (x₁ ⊓ x₂) y
-/
theorem Tendsto.inf {f : α → β} {x₁ x₂ : Filter α} {y₁ y₂ : Filter β} (h₁ : Tendsto f x₁ y₁)
    (h₂ : Tendsto f x₂ y₂) : Tendsto f (x₁ ⊓ x₂) (y₁ ⊓ y₂) :=
  tendsto_inf.2 ⟨tendsto_inf_left h₁, tendsto_inf_right h₂⟩

@[simp]
/-
**Filter.tendsto_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_iInf {f : α -> β} {x : Filter α} {y : ι -> Filter β} : Tendsto f x
 (⨅ i, y i) ↔ forall i, Tendsto f x (y i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_iInf {f : α → β} {x : Filter α} {y : ι → Filter β} :
    Tendsto f x (⨅ i, y i) ↔ ∀ i, Tendsto f x (y i) := by
  simp only [Tendsto, le_iInf_iff]
/-
**Filter.tendsto_iInf'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_iInf' {f : α -> β} {x : ι -> Filter α} {y : Filter β} (i : ι) (hi 
: Tendsto f (x i) y) : Tendsto f (⨅ i, x i) y
参数：i : ι；hi : Tendsto f (x i) y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
-/
theorem tendsto_iInf' {f : α → β} {x : ι → Filter α} {y : Filter β} (i : ι)
    (hi : Tendsto f (x i) y) : Tendsto f (⨅ i, x i) y :=
  hi.mono_left <| iInf_le _ _
/-
**Filter.tendsto_iInf_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_iInf_iInf {f : α -> β} {x : ι -> Filter α} {y : ι -> Filter β} (h 
: forall i, Tendsto f (x i) (y i)) : Tendsto f (iInf x) (iInf y)
参数：h : forall i, Tendsto f (x i) (y i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_iInf`：tendsto_iInf {f : α -> β} {x : Filter α} {y : ι -> 
Filter β} : Tendsto f x (⨅ i, y i) ↔ forall i, Tendsto f x (y i)
· 使用定理 `Filter.tendsto_iInf'`：tendsto_iInf' {f : α -> β} {x : ι -> Filter α} {y 
: Filter β} (i : ι) (hi : Tendsto f (x i) y) : Tendsto f (⨅ i, x i) y
-/
theorem tendsto_iInf_iInf {f : α → β} {x : ι → Filter α} {y : ι → Filter β}
    (h : ∀ i, Tendsto f (x i) (y i)) : Tendsto f (iInf x) (iInf y) :=
  tendsto_iInf.2 fun i => tendsto_iInf' i (h i)

@[simp]
/-
**Filter.tendsto_sup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_sup {f : α -> β} {x₁ x₂ : Filter α} {y : Filter β} : Tendsto f (x₁
 ⊔ x₂) y ↔ Tendsto f x₁ y ∧ Tendsto f x₂ y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_sup`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : Filter α} {m : 
α → β},   Filter.map m (f₁ ⊔ f₂) = Filter.map m f₁ ⊔ Filter.map m f₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_sup {f : α → β} {x₁ x₂ : Filter α} {y : Filter β} :
    Tendsto f (x₁ ⊔ x₂) y ↔ Tendsto f x₁ y ∧ Tendsto f x₂ y := by
  simp only [Tendsto, map_sup, sup_le_iff]
/-
**Filter.Tendsto.sup** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x₁ x₂ : Filter α} {y : Filter
 β},   Filter.Tendsto f x₁ y → Filter.Tendsto f x₂ y → Filter.Tendsto f (x₁ ⊔ x₂
) y
参数：x₁ ⊔ x₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_sup`：tendsto_sup {f : α -> β} {x₁ x₂ : Filter α} {y : Fil
ter β} : Tendsto f (x₁ ⊔ x₂) y ↔ Tendsto f x₁ y ∧ Tendsto f x₂ y
-/
theorem Tendsto.sup {f : α → β} {x₁ x₂ : Filter α} {y : Filter β} :
    Tendsto f x₁ y → Tendsto f x₂ y → Tendsto f (x₁ ⊔ x₂) y := fun h₁ h₂ => tendsto_sup.mpr ⟨h₁, h₂⟩
/-
**Filter.Tendsto.sup_sup** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x₁ x₂ : Filter α} {y₁ y₂ : Fi
lter β},   Filter.Tendsto f x₁ y₁ → Filter.Tendsto f x₂ y₂ → Filter.Tendsto f (x
₁ ⊔ x₂) (y₁ ⊔ y₂)
参数：x₁ ⊔ x₂；y₁ ⊔ y₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_sup`：tendsto_sup {f : α -> β} {x₁ x₂ : Filter α} {y : Fil
ter β} : Tendsto f (x₁ ⊔ x₂) y ↔ Tendsto f x₁ y ∧ Tendsto f x₂ y
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem Tendsto.sup_sup {f : α → β} {x₁ x₂ : Filter α} {y₁ y₂ : Filter β}
    (h₁ : Tendsto f x₁ y₁) (h₂ : Tendsto f x₂ y₂) : Tendsto f (x₁ ⊔ x₂) (y₁ ⊔ y₂) :=
  tendsto_sup.mpr ⟨h₁.mono_right le_sup_left, h₂.mono_right le_sup_right⟩

@[simp]
/-
**Filter.tendsto_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_iSup {f : α -> β} {x : ι -> Filter α} {y : Filter β} : Tendsto f (
⨆ i, x i) y ↔ forall i, Tendsto f (x i) y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_iSup`：map_iSup {f : ι -> Filter α} : map m (⨆ i, f i) = ⨆ i, 
map m (f i)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_iSup {f : α → β} {x : ι → Filter α} {y : Filter β} :
    Tendsto f (⨆ i, x i) y ↔ ∀ i, Tendsto f (x i) y := by simp only [Tendsto, map_iSup, iSup_le_iff]
/-
**Filter.tendsto_iSup_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_iSup_iSup {f : α -> β} {x : ι -> Filter α} {y : ι -> Filter β} (h 
: forall i, Tendsto f (x i) (y i)) : Tendsto f (iSup x) (iSup y)
参数：h : forall i, Tendsto f (x i) (y i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_iSup`：tendsto_iSup {f : α -> β} {x : ι -> Filter α} {y : 
Filter β} : Tendsto f (⨆ i, x i) y ↔ forall i, Tendsto f (x i) y
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
theorem tendsto_iSup_iSup {f : α → β} {x : ι → Filter α} {y : ι → Filter β}
    (h : ∀ i, Tendsto f (x i) (y i)) : Tendsto f (iSup x) (iSup y) :=
  tendsto_iSup.2 fun i => (h i).mono_right <| le_iSup _ _
/-
**Filter.tendsto_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : Filter α} {s : Set β},   
Filter.Tendsto f l (Filter.principal s) ↔ ∀ᶠ (a : α) in l, f a ∈ s
参数：Filter.principal s；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem tendsto_principal {f : α → β} {l : Filter α} {s : Set β} :
    Tendsto f l (𝓟 s) ↔ ∀ᶠ a in l, f a ∈ s := by
  simp only [Tendsto, le_principal_iff, mem_map', Filter.Eventually]
/-
**Filter.tendsto_principal_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_principal_principal {f : α -> β} {s : Set α} {t : Set β} : Tendsto
 f (𝓟 s) (𝓟 t) ↔ forall a in s, f a in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_principal_principal {f : α → β} {s : Set α} {t : Set β} :
    Tendsto f (𝓟 s) (𝓟 t) ↔ ∀ a ∈ s, f a ∈ t := by
  simp
/-
**Filter.tendsto_pure** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {a : Filter α} {b : β},   Filt
er.Tendsto f a (pure b) ↔ ∀ᶠ (x : α) in a, f x = b
参数：pure b；x : α。
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
@[simp] theorem tendsto_pure {f : α → β} {a : Filter α} {b : β} :
    Tendsto f a (pure b) ↔ ∀ᶠ x in a, f x = b := by
  simp only [Tendsto, le_pure_iff, mem_map', mem_singleton_iff, Filter.Eventually]
/-
**Filter.tendsto_pure_pure** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_pure_pure (f : α -> β) (a : α) : Tendsto f (pure a) (pure (f a))
参数：f : α -> β；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_pure`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {a : Fi
lter α} {b : β},   Filter.Tendsto f a (pure b) ↔ ∀ᶠ (x : α) in a, f x = b
-/
theorem tendsto_pure_pure (f : α → β) (a : α) : Tendsto f (pure a) (pure (f a)) :=
  tendsto_pure.2 rfl
/-
**Filter.tendsto_const_pure** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_const_pure {a : Filter α} {b : β} : Tendsto (fun _ => b) a (pure b
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_pure`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {a : Fi
lter α} {b : β},   Filter.Tendsto f a (pure b) ↔ ∀ᶠ (x : α) in a, f x = b
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
theorem tendsto_const_pure {a : Filter α} {b : β} : Tendsto (fun _ => b) a (pure b) :=
  tendsto_pure.2 <| univ_mem' fun _ => rfl
/-
**Filter.pure_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：pure_le_iff {a : α} {l : Filter α} : pure a <= l ↔ forall s in l, a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem pure_le_iff {a : α} {l : Filter α} : pure a ≤ l ↔ ∀ s ∈ l, a ∈ s :=
  Iff.rfl
/-
**Filter.tendsto_pure_left** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_pure_left {f : α -> β} {a : α} {l : Filter β} : Tendsto f (pure a)
 l ↔ forall s in l, f a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_pure_left {f : α → β} {a : α} {l : Filter β} :
    Tendsto f (pure a) l ↔ ∀ s ∈ l, f a ∈ s :=
  Iff.rfl

@[simp]
/-
**Filter.map_inf_principal_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：map_inf_principal_preimage {f : α -> β} {s : Set β} {l : Filter α} : map f
 (l ⊓ 𝓟 (f ⁻¹' s)) = map f l ⊓ 𝓟 s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_inf_principal_preimage {f : α → β} {s : Set β} {l : Filter α} :
    map f (l ⊓ 𝓟 (f ⁻¹' s)) = map f l ⊓ 𝓟 s :=
  Filter.ext fun t => by simp only [mem_map', mem_inf_principal, mem_ofPred_eq, mem_preimage]

/-- If two filters are disjoint, then a function cannot tend to both of them along a non-trivial
filter. -/
/-
**Filter.Tendsto.not_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {a : Filter α} {b₁ b₂ : Filter
 β},   Filter.Tendsto f a b₁ → ∀ [a.NeBot], Disjoint b₁ b₂ → ¬Filter.Tendsto f a
 b₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.NeBot.ne`：∀ {α : Type u} {f : Filter α}, f.NeBot → f ≠ ⊥
· 使用定理 `Filter.Tendsto.neBot`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x : F
ilter α} {y : Filter β},   Filter.Tendsto f x y → ∀ [hx : x.NeBot], y.NeBot
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_inf`：tendsto_inf {f : α -> β} {x : Filter α} {y₁ y₂ : Fil
ter β} : Tendsto f x (y₁ ⊓ y₂) ↔ Tendsto f x y₁ ∧ Tendsto f x y₂
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥

--- 原说明 ---
If two filters are disjoint, then a function cannot tend to both of them along a
 non-trivial
filter.
-/
theorem Tendsto.not_tendsto {f : α → β} {a : Filter α} {b₁ b₂ : Filter β} (hf : Tendsto f a b₁)
    [NeBot a] (hb : Disjoint b₁ b₂) : ¬Tendsto f a b₂ := fun hf' =>
  (tendsto_inf.2 ⟨hf, hf'⟩).neBot.ne hb.eq_bot
/-
**Filter.Tendsto.if** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l₁ : Filter α} {l₂ : Filter β} {f g : α →
 β} {p : α → Prop}   [inst : (x : α) → Decidable (p x)],   Filter.Tendsto f (l₁ 
⊓ Filter.principal {x | p x}) l₂ →     Filter.Tendsto g (l₁ ⊓ Filter.principal {
x | ¬p x}) l₂ → Filter.Tendsto (fun x => if p x then f x else g x) l₁ l₂
参数：x : α；p x；l₁ ⊓ Filter.principal {x | p x}；l₁ ⊓ Filter.principal {x | ¬p x}；fu
n x => if p x then f x else g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
protected theorem Tendsto.if {l₁ : Filter α} {l₂ : Filter β} {f g : α → β} {p : α → Prop}
    [∀ x, Decidable (p x)] (h₀ : Tendsto f (l₁ ⊓ 𝓟 { x | p x }) l₂)
    (h₁ : Tendsto g (l₁ ⊓ 𝓟 { x | ¬p x }) l₂) :
    Tendsto (fun x => if p x then f x else g x) l₁ l₂ := by
  simp only [tendsto_def, mem_inf_principal] at *
  intro s hs
  filter_upwards [h₀ s hs, h₁ s hs] with x hp₀ hp₁
  rw [mem_preimage]
  split_ifs with h
  exacts [hp₀ h, hp₁ h]
/-
**Filter.Tendsto.if'** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_5} {β : Type u_6} {l₁ : Filter α} {l₂ : Filter β} {f g : α →
 β} {p : α → Prop} [inst : DecidablePred p],   Filter.Tendsto f l₁ l₂ → Filter.T
endsto g l₁ l₂ → Filter.Tendsto (fun a => if p a then f a else g a) l₁ l₂
参数：fun a => if p a then f a else g a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.if`：∀ {α : Type u_1} {β : Type u_2} {l₁ : Filter α} {l₂ :
 Filter β} {f g : α → β} {p : α → Prop}   [inst : (x : α) → Decidable (p x)],   
Filter.…
· 使用定理 `Filter.tendsto_inf_left`：tendsto_inf_left {f : α -> β} {x₁ x₂ : Filter α
} {y : Filter β} (h : Tendsto f x₁ y) : Tendsto f (x₁ ⊓ x₂) y
-/
protected theorem Tendsto.if' {α β : Type*} {l₁ : Filter α} {l₂ : Filter β} {f g : α → β}
    {p : α → Prop} [DecidablePred p] (hf : Tendsto f l₁ l₂) (hg : Tendsto g l₁ l₂) :
    Tendsto (fun a => if p a then f a else g a) l₁ l₂ :=
  (tendsto_inf_left hf).if (tendsto_inf_left hg)
/-
**Filter.Tendsto.piecewise** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l₁ : Filter α} {l₂ : Filter β} {f g : α →
 β} {s : Set α}   [inst : (x : α) → Decidable (x ∈ s)],   Filter.Tendsto f (l₁ ⊓
 Filter.principal s) l₂ →     Filter.Tendsto g (l₁ ⊓ Filter.principal sᶜ) l₂ → F
ilter.Tendsto (s.piecewise f g) l₁ l₂
参数：x : α；x ∈ s；l₁ ⊓ Filter.principal s；l₁ ⊓ Filter.principal sᶜ；s.piecewise f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.if`：∀ {α : Type u_1} {β : Type u_2} {l₁ : Filter α} {l₂ :
 Filter β} {f g : α → β} {p : α → Prop}   [inst : (x : α) → Decidable (p x)],   
Filter.…
-/
protected theorem Tendsto.piecewise {l₁ : Filter α} {l₂ : Filter β} {f g : α → β} {s : Set α}
    [∀ x, Decidable (x ∈ s)] (h₀ : Tendsto f (l₁ ⊓ 𝓟 s) l₂) (h₁ : Tendsto g (l₁ ⊓ 𝓟 sᶜ) l₂) :
    Tendsto (piecewise s f g) l₁ l₂ :=
  Tendsto.if h₀ h₁

end Filter

/-
**Set.MapsTo.tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.MapsTo.tendsto {s : Set α} {t : Set β} {f : α -> β} (h : MapsTo f s t)
 : Filter.Tendsto f (𝓟 s) (𝓟 t)
参数：h : MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_principal_principal`：tendsto_principal_principal {f : α -
> β} {s : Set α} {t : Set β} : Tendsto f (𝓟 s) (𝓟 t) ↔ forall a in s, f a in t
-/
theorem Set.MapsTo.tendsto {s : Set α} {t : Set β} {f : α → β} (h : MapsTo f s t) :
    Filter.Tendsto f (𝓟 s) (𝓟 t) :=
  Filter.tendsto_principal_principal.2 h
/-
**Filter.EventuallyEq.comp_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.comp_tendsto {l : Filter α} {f : α -> β} {f' : α -> β}
 (H : f =ᶠ[l] f') {g : γ -> α} {lc : Filter γ} (hg : Tendsto g lc l) : f ∘ g =ᶠ[
lc] f' ∘ g
参数：H : f =ᶠ[l] f'；hg : Tendsto g lc l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
-/
theorem Filter.EventuallyEq.comp_tendsto {l : Filter α} {f : α → β} {f' : α → β}
    (H : f =ᶠ[l] f') {g : γ → α} {lc : Filter γ} (hg : Tendsto g lc l) :
    f ∘ g =ᶠ[lc] f' ∘ g :=
  hg.eventually H

variable {F : Filter α} {G : Filter β}
/-
**Filter.map_mapsTo_Iic_iff_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.map_mapsTo_Iic_iff_tendsto {m : α -> β} : MapsTo (map m) (Iic F) (I
ic G) ↔ Tendsto m F G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.self_mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Iic a
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
-/
theorem Filter.map_mapsTo_Iic_iff_tendsto {m : α → β} :
    MapsTo (map m) (Iic F) (Iic G) ↔ Tendsto m F G :=
  ⟨fun hm ↦ hm self_mem_Iic, fun hm _ ↦ hm.mono_left⟩

alias ⟨_, Filter.Tendsto.map_mapsTo_Iic⟩ := Filter.map_mapsTo_Iic_iff_tendsto
/-
**Filter.map_mapsTo_Iic_iff_mapsTo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.map_mapsTo_Iic_iff_mapsTo {s : Set α} {t : Set β} {m : α -> β} : Ma
psTo (map m) (Iic <| 𝓟 s) (Iic <| 𝓟 t) ↔ MapsTo m s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_mapsTo_Iic_iff_tendsto`：Filter.map_mapsTo_Iic_iff_tendsto {m 
: α -> β} : MapsTo (map m) (Iic F) (Iic G) ↔ Tendsto m F G
· 使用定理 `Filter.tendsto_principal_principal`：tendsto_principal_principal {f : α -
> β} {s : Set α} {t : Set β} : Tendsto f (𝓟 s) (𝓟 t) ↔ forall a in s, f a in t
· 使用定理 `Set.MapsTo.eq_1`：∀ {α : Type u} {β : Type v} (f : α → β) (s : Set α) (t 
: Set β), Set.MapsTo f s t = ∀ ⦃x : α⦄, x ∈ s → f x ∈ t
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Filter.map_mapsTo_Iic_iff_mapsTo {s : Set α} {t : Set β} {m : α → β} :
    MapsTo (map m) (Iic <| 𝓟 s) (Iic <| 𝓟 t) ↔ MapsTo m s t := by
  rw [map_mapsTo_Iic_iff_tendsto, tendsto_principal_principal, MapsTo]

alias ⟨_, Set.MapsTo.filter_map_Iic⟩ := Filter.map_mapsTo_Iic_iff_mapsTo
