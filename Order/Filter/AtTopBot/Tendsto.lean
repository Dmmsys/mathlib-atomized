/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov, Patrick Massot
-/
module

public import Mathlib.Order.Filter.AtTopBot.Disjoint
public import Mathlib.Order.Filter.Tendsto

/-!
# Limits of `Filter.atTop` and `Filter.atBot`

In this file we prove many lemmas on the combination of `Filter.atTop` and `Filter.atBot`
and `Tendsto`.
-/

public section

assert_not_exists Finset

variable {ι ι' α β γ : Type*}

open Set

namespace Filter

@[to_dual]
/-
**Filter.not_tendsto_const_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：not_tendsto_const_atTop [Preorder α] [NoTopOrder α] (x : α) (l : Filter β)
 [l.NeBot] : ¬Tendsto (fun _ => x) l atTop
参数：x : α；l : Filter β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.not_tendsto`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} 
{a : Filter α} {b₁ b₂ : Filter β},   Filter.Tendsto f a b₁ → ∀ [a.NeBot], Disjoi
nt b₁ b₂ → ¬Filt…
· 使用定理 `Filter.tendsto_const_pure`：tendsto_const_pure {a : Filter α} {b : β} : T
endsto (fun _ => b) a (pure b)
· 使用定理 `Filter.disjoint_pure_atTop`：disjoint_pure_atTop [Preorder α] [NoTopOrder
 α] (x : α) : Disjoint (pure x) atTop
-/
theorem not_tendsto_const_atTop [Preorder α] [NoTopOrder α] (x : α) (l : Filter β) [l.NeBot] :
    ¬Tendsto (fun _ => x) l atTop :=
  tendsto_const_pure.not_tendsto (disjoint_pure_atTop x)

@[to_dual eventually_lt_atBot]
/-
**Filter.Tendsto.eventually_gt_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_3} {β : Type u_4} [inst : Preorder β] [NoTopOrder β] {f : α 
→ β} {l : Filter α},   Filter.Tendsto f l Filter.atTop → ∀ (c : β), ∀ᶠ (x : α) i
n l, c < f x
参数：c : β；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
-/
protected theorem Tendsto.eventually_gt_atTop [Preorder β] [NoTopOrder β] {f : α → β} {l : Filter α}
    (hf : Tendsto f l atTop) (c : β) : ∀ᶠ x in l, c < f x :=
  hf.eventually (eventually_gt_atTop c)

@[to_dual eventually_le_atBot]
/-
**Filter.Tendsto.eventually_ge_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_3} {β : Type u_4} [inst : Preorder β] {f : α → β} {l : Filte
r α},   Filter.Tendsto f l Filter.atTop → ∀ (c : β), ∀ᶠ (x : α) in l, c ≤ f x
参数：c : β；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
-/
protected theorem Tendsto.eventually_ge_atTop [Preorder β] {f : α → β} {l : Filter α}
    (hf : Tendsto f l atTop) (c : β) : ∀ᶠ x in l, c ≤ f x :=
  hf.eventually (eventually_ge_atTop c)

@[to_dual]
/-
**Filter.Tendsto.eventually_ne_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_3} {β : Type u_4} [inst : Preorder β] [NoTopOrder β] {f : α 
→ β} {l : Filter α},   Filter.Tendsto f l Filter.atTop → ∀ (c : β), ∀ᶠ (x : α) i
n l, f x ≠ c
参数：c : β；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.eventually_ne_atTop`：eventually_ne_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, x != a
-/
protected theorem Tendsto.eventually_ne_atTop [Preorder β] [NoTopOrder β] {f : α → β} {l : Filter α}
    (hf : Tendsto f l atTop) (c : β) : ∀ᶠ x in l, f x ≠ c :=
  hf.eventually (eventually_ne_atTop c)
/-
**Filter.Tendsto.eventually_ne_atTop'** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`
。
形式化陈述：∀ {α : Type u_3} {β : Type u_4} [inst : Preorder β] [NoTopOrder β] {f : α 
→ β} {l : Filter α},   Filter.Tendsto f l Filter.atTop → ∀ (c : α), ∀ᶠ (x : α) i
n l, x ≠ c
参数：c : α；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Tendsto.eventually_ne_atTop`：∀ {α : Type u_3} {β : Type u_4} [ins
t : Preorder β] [NoTopOrder β] {f : α → β} {l : Filter α},   Filter.Tendsto f l 
Filter.atTop → ∀ (c : β)…
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
-/
protected theorem Tendsto.eventually_ne_atTop' [Preorder β] [NoTopOrder β] {f : α → β}
    {l : Filter α} (hf : Tendsto f l atTop) (c : α) : ∀ᶠ x in l, x ≠ c :=
  (hf.eventually_ne_atTop (f c)).mono fun _ => ne_of_apply_ne f

@[to_dual OrderBot.atBot_eq]
/-
**Filter.OrderTop.atTop_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter.OrderTop`。
形式化陈述：∀ (α : Type u_6) [inst : PartialOrder α] [inst_1 : OrderTop α], Filter.atT
op = pure ⊤
参数：α : Type u_6。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsTop.atTop_eq`：∀ {α : Type u_3} [inst : Preorder α] {a : α}, IsTop a → 
Filter.atTop = Filter.principal (Set.Ici a)
· 使用定理 `isTop_top`：isTop_top : IsTop (⊤ : α)
· 使用定理 `Set.Ici_top`：Ici_top [PartialOrder α] [OrderTop α] : Ici (⊤ : α) = {⊤}
· 使用定理 `Filter.principal_singleton`：principal_singleton (a : α) : 𝓟 {a} = pure a
-/
theorem OrderTop.atTop_eq (α) [PartialOrder α] [OrderTop α] : (atTop : Filter α) = pure ⊤ := by
  rw [isTop_top.atTop_eq, Ici_top, principal_singleton]

@[to_dual]
/-
**Filter.tendsto_atTop_pure** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_atTop_pure [PartialOrder α] [OrderTop α] (f : α -> β) : Tendsto f 
atTop (pure <| f ⊤)
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_pure_pure`：tendsto_pure_pure (f : α -> β) (a : α) : Tends
to f (pure a) (pure (f a))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.OrderTop.atTop_eq`：∀ (α : Type u_6) [inst : PartialOrder α] [inst
_1 : OrderTop α], Filter.atTop = pure ⊤
-/
theorem tendsto_atTop_pure [PartialOrder α] [OrderTop α] (f : α → β) :
    Tendsto f atTop (pure <| f ⊤) :=
  (OrderTop.atTop_eq α).symm ▸ tendsto_pure_pure _ _

@[to_dual]
/-
**Filter.tendsto_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_atTop [Preorder β] {m : α -> β} {f : Filter α} : Tendsto m f atTop
 ↔ forall b, forallᶠ a in f, b <= m a
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_atTop [Preorder β] {m : α → β} {f : Filter α} :
    Tendsto m f atTop ↔ ∀ b, ∀ᶠ a in f, b ≤ m a := by
  simp only [atTop, tendsto_iInf, tendsto_principal, mem_Ici]

@[to_dual]
/-
**Filter.tendsto_atTop_mono'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_atTop_mono' [Preorder β] (l : Filter α) ⦃f₁ f₂ : α -> β⦄ (h : f₁ <
=ᶠ[l] f₂) (h₁ : Tendsto f₁ l atTop) : Tendsto f₂ l atTop
参数：l : Filter α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_atTop`：tendsto_atTop [Preorder β] {m : α -> β} {f : Filte
r α} : Tendsto m f atTop ↔ forall b, forallᶠ a in f, b <= m a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem tendsto_atTop_mono' [Preorder β] (l : Filter α) ⦃f₁ f₂ : α → β⦄ (h : f₁ ≤ᶠ[l] f₂)
    (h₁ : Tendsto f₁ l atTop) : Tendsto f₂ l atTop :=
  tendsto_atTop.2 fun b => by filter_upwards [tendsto_atTop.1 h₁ b, h] with x using le_trans

@[to_dual]
/-
**Filter.tendsto_atTop_mono** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_atTop_mono [Preorder β] {l : Filter α} {f g : α -> β} (h : forall 
n, f n <= g n) : Tendsto f l atTop -> Tendsto g l atTop
参数：h : forall n, f n <= g n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_atTop_mono'`：tendsto_atTop_mono' [Preorder β] (l : Filter
 α) ⦃f₁ f₂ : α -> β⦄ (h : f₁ <=ᶠ[l] f₂) (h₁ : Tendsto f₁ l atTop) : Tendsto f₂ l
 atTop
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem tendsto_atTop_mono [Preorder β] {l : Filter α} {f g : α → β} (h : ∀ n, f n ≤ g n) :
    Tendsto f l atTop → Tendsto g l atTop :=
  tendsto_atTop_mono' l <| Eventually.of_forall h

end Filter

namespace Filter

/-!
### Sequences
-/

/-
**Filter._root_.StrictMono.tendsto_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Sequences
-/
theorem _root_.StrictMono.tendsto_atTop {φ : ℕ → ℕ} (h : StrictMono φ) : Tendsto φ atTop atTop :=
  tendsto_atTop_mono h.id_le tendsto_id

/-- If `f` is a monotone function and `g` tends to `atTop` along a nontrivial filter.
then the upper bounds of the range of `f ∘ g`
are the same as the upper bounds of the range of `f`.

This lemma together with `exists_seq_monotone_tendsto_atTop_atTop` below
is useful to reduce a statement
about a monotone family indexed by a type with countably generated `atTop` (e.g., `ℝ`)
to the case of a family indexed by natural numbers. -/
@[to_dual
/-- If `f` is a monotone function and `g` tends to `atBot` along a nontrivial filter.
then the lower bounds of the range of `f ∘ g`
are the same as the lower bounds of the range of `f`. -/]
/-
**Filter._root_.Monotone.upperBounds_range_comp_tendsto_atTop** 是 Mathlib 中的一个定理
，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Monotone.upperBounds_range_comp_tendsto_atTop [Preorder β] [Preorder γ]
    {l : Filter α} [l.NeBot] {f : β → γ} (hf : Monotone f) {g : α → β} (hg : Tendsto g l atTop) :
    upperBounds (range (f ∘ g)) = upperBounds (range f) := by
  refine Subset.antisymm ?_ (upperBounds_mono_set <| range_comp_subset_range _ _)
  rintro c hc _ ⟨b, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, b ≤ g a := (hg.eventually_ge_atTop b).exists
  exact (hf ha).trans <| hc <| mem_range_self _

/-- If `f` is an antitone function and `g` tends to `atTop` along a nontrivial filter.
then the upper bounds of the range of `f ∘ g`
are the same as the upper bounds of the range of `f`. -/
@[to_dual
/-- If `f` is an antitone function and `g` tends to `atBot` along a nontrivial filter.
then the upper bounds of the range of `f ∘ g`
are the same as the upper bounds of the range of `f`. -/]
/-
**Filter._root_.Antitone.lowerBounds_range_comp_tendsto_atTop** 是 Mathlib 中的一个定理
，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Antitone.lowerBounds_range_comp_tendsto_atTop [Preorder β] [Preorder γ]
    {l : Filter α} [l.NeBot] {f : β → γ} (hf : Antitone f) {g : α → β} (hg : Tendsto g l atTop) :
    lowerBounds (range (f ∘ g)) = lowerBounds (range f) :=
  hf.dual_left.lowerBounds_range_comp_tendsto_atBot hg

@[to_dual]
/-
**Filter.tendsto_atTop_atTop_of_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_atTop_atTop_of_monotone [Preorder α] [Preorder β] {f : α -> β} (hf
 : Monotone f) (h : forall b, exists a, b <= f a) : Tendsto f atTop atTop
参数：hf : Monotone f；h : forall b, exists a, b <= f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_iInf`：tendsto_iInf {f : α -> β} {x : Filter α} {y : ι -> 
Filter β} : Tendsto f x (⨅ i, y i) ↔ forall i, Tendsto f x (y i)
· 使用定理 `Filter.tendsto_principal`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l
 : Filter α} {s : Set β},   Filter.Tendsto f l (Filter.principal s) ↔ ∀ᶠ (a : α)
 in l, f a ∈ s
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Filter.mem_atTop`：mem_atTop [Preorder α] (a : α) : { b : α | a <= b } in
 @atTop α _
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem tendsto_atTop_atTop_of_monotone [Preorder α] [Preorder β] {f : α → β} (hf : Monotone f)
    (h : ∀ b, ∃ a, b ≤ f a) : Tendsto f atTop atTop :=
  tendsto_iInf.2 fun b =>
    tendsto_principal.2 <|
      let ⟨a, ha⟩ := h b
      mem_of_superset (mem_atTop a) fun _a' ha' => le_trans ha (hf ha')

@[to_dual]
/-
**Filter.tendsto_atTop_atBot_of_antitone** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_atTop_atBot_of_antitone [Preorder α] [Preorder β] {f : α -> β} (hf
 : Antitone f) (h : forall b, exists a, f a <= b) : Tendsto f atTop atBot
参数：hf : Antitone f；h : forall b, exists a, f a <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_atTop_atTop_of_monotone`：tendsto_atTop_atTop_of_monotone 
[Preorder α] [Preorder β] {f : α -> β} (hf : Monotone f) (h : forall b, exists a
, b <= f a) : Tendsto f atTo…
-/
theorem tendsto_atTop_atBot_of_antitone [Preorder α] [Preorder β] {f : α → β} (hf : Antitone f)
    (h : ∀ b, ∃ a, f a ≤ b) : Tendsto f atTop atBot :=
  @tendsto_atTop_atTop_of_monotone _ βᵒᵈ _ _ _ hf h

@[to_dual]
alias _root_.Monotone.tendsto_atTop_atTop := tendsto_atTop_atTop_of_monotone

@[to_dual]
/-
**Filter.comap_embedding_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：comap_embedding_atTop [Preorder β] [Preorder γ] {e : β -> γ} (hm : forall 
b₁ b₂, e b₁ <= e b₂ ↔ b₁ <= b₂) (hu : forall c, exists b, c <= e b) : comap e at
Top = atTop
参数：hm : forall b₁ b₂, e b₁ <= e b₂ ↔ b₁ <= b₂；hu : forall c, exists b, c <= e b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `Filter.mem_comap`：∀ {α : Type u_1} {β : Type u_2} {g : Filter β} {m : α 
→ β} {s : Set α}, s ∈ Filter.comap m g ↔ ∃ t ∈ g, m ⁻¹' t ⊆ s
· 使用定理 `Filter.mem_atTop`：mem_atTop [Preorder α] (a : α) : { b : α | a <= b } in
 @atTop α _
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.Tendsto.le_comap`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁
 : Filter α} {l₂ : Filter β},   Filter.Tendsto f l₁ l₂ → l₁ ≤ Filter.comap f l₂
· 使用定理 `Filter.tendsto_atTop_atTop_of_monotone`：tendsto_atTop_atTop_of_monotone 
[Preorder α] [Preorder β] {f : α -> β} (hf : Monotone f) (h : forall b, exists a
, b <= f a) : Tendsto f atTo…
-/
theorem comap_embedding_atTop [Preorder β] [Preorder γ] {e : β → γ}
    (hm : ∀ b₁ b₂, e b₁ ≤ e b₂ ↔ b₁ ≤ b₂) (hu : ∀ c, ∃ b, c ≤ e b) : comap e atTop = atTop :=
  le_antisymm
    (le_iInf fun b =>
      le_principal_iff.2 <| mem_comap.2 ⟨Ici (e b), mem_atTop _, fun _ => (hm _ _).1⟩)
    (tendsto_atTop_atTop_of_monotone (fun _ _ => (hm _ _).2) hu).le_comap

/-- A function `f` goes to `∞` independent of an order-preserving embedding `e`. -/
@[to_dual (reorder := hm (b₁ b₂))
/-- A function `f` goes to `-∞` independent of an order-preserving embedding `e`. -/]
/-
**Filter.tendsto_atTop_embedding** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_atTop_embedding [Preorder β] [Preorder γ] {f : α -> β} {e : β -> γ
} {l : Filter α} (hm : forall b₁ b₂, e b₁ <= e b₂ ↔ b₁ <= b₂) (hu : forall c, ex
ists b, c <= e b) : Tendsto (e ∘ f) l atTop ↔ Tendsto f l atTop
参数：hm : forall b₁ b₂, e b₁ <= e b₂ ↔ b₁ <= b₂；hu : forall c, exists b, c <= e b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.comap_embedding_atTop`：comap_embedding_atTop [Preorder β] [Preord
er γ] {e : β -> γ} (hm : forall b₁ b₂, e b₁ <= e b₂ ↔ b₁ <= b₂) (hu : forall c, 
exists b, c <= e b…
· 使用定理 `Filter.tendsto_comap_iff`：tendsto_comap_iff {f : α -> β} {g : β -> γ} {a
 : Filter α} {c : Filter γ} : Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_atTop_embedding [Preorder β] [Preorder γ] {f : α → β} {e : β → γ} {l : Filter α}
    (hm : ∀ b₁ b₂, e b₁ ≤ e b₂ ↔ b₁ ≤ b₂) (hu : ∀ c, ∃ b, c ≤ e b) :
    Tendsto (e ∘ f) l atTop ↔ Tendsto f l atTop := by
  rw [← comap_embedding_atTop hm hu, tendsto_comap_iff]

/-- If `u` is a monotone function with linear ordered codomain and the range of `u` is not bounded
above, then `Tendsto u atTop atTop`. -/
@[to_dual
/-- If `u` is a monotone function with linear ordered codomain and the range of `u` is not bounded
below, then `Tendsto u atBot atBot`. -/]
/-
**Filter.tendsto_atTop_atTop_of_monotone'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_atTop_atTop_of_monotone' [Preorder ι] [LinearOrder α] {u : ι -> α}
 (h : Monotone u) (H : ¬BddAbove (range u)) : Tendsto u atTop atTop
参数：h : Monotone u；H : ¬BddAbove (range u)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.tendsto_atTop_atTop`：∀ {α : Type u_3} {β : Type u_4} [inst : Pr
eorder α] [inst_1 : Preorder β] {f : α → β},   Monotone f → (∀ (b : β), ∃ a, b ≤
 f a) → Filter.Ten…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_bddAbove_iff`：not_bddAbove_iff {α : Type*} [LinearOrder α] {s : Set 
α} : ¬BddAbove s ↔ forall x, exists y in s, x < y
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem tendsto_atTop_atTop_of_monotone' [Preorder ι] [LinearOrder α] {u : ι → α} (h : Monotone u)
    (H : ¬BddAbove (range u)) : Tendsto u atTop atTop := by
  apply h.tendsto_atTop_atTop
  intro b
  rcases not_bddAbove_iff.1 H b with ⟨_, ⟨N, rfl⟩, hN⟩
  exact ⟨N, le_of_lt hN⟩

/-- If a monotone function `u : ι → α` tends to `atTop` along *some* non-trivial filter `l`, then
it tends to `atTop` along `atTop`. -/
@[to_dual
/-- If a monotone function `u : ι → α` tends to `atBot` along *some* non-trivial filter `l`, then
it tends to `atBot` along `atBot`. -/]
/-
**Filter.tendsto_atTop_of_monotone_of_filter** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_atTop_of_monotone_of_filter [Preorder ι] [Preorder α] {l : Filter 
ι} {u : ι -> α} (h : Monotone u) [NeBot l] (hu : Tendsto u l atTop) : Tendsto u 
atTop atTop
参数：h : Monotone u；hu : Tendsto u l atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.tendsto_atTop_atTop`：∀ {α : Type u_3} {β : Type u_4} [inst : Pr
eorder α] [inst_1 : Preorder β] {f : α → β},   Monotone f → (∀ (b : β), ∃ a, b ≤
 f a) → Filter.Ten…
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.mem_atTop`：mem_atTop [Preorder α] (a : α) : { b : α | a <= b } in
 @atTop α _
-/
theorem tendsto_atTop_of_monotone_of_filter [Preorder ι] [Preorder α] {l : Filter ι} {u : ι → α}
    (h : Monotone u) [NeBot l] (hu : Tendsto u l atTop) : Tendsto u atTop atTop :=
  h.tendsto_atTop_atTop fun b => (hu.eventually (mem_atTop b)).exists

@[to_dual]
/-
**Filter.tendsto_atTop_of_monotone_of_subseq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_atTop_of_monotone_of_subseq [Preorder ι] [Preorder α] {u : ι -> α}
 {φ : ι' -> ι} (h : Monotone u) {l : Filter ι'} [NeBot l] (H : Tendsto (u ∘ φ) l
 atTop) : Tendsto u atTop atTop
参数：h : Monotone u；H : Tendsto (u ∘ φ) l atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_atTop_of_monotone_of_filter`：tendsto_atTop_of_monotone_of
_filter [Preorder ι] [Preorder α] {l : Filter ι} {u : ι -> α} (h : Monotone u) [
NeBot l] (hu : Tendsto u l atTop…
· 使用定理 `Filter.tendsto_map'`：tendsto_map'_iff {f : β -> γ} {g : α -> β} {x : Fil
ter α} {y : Filter γ} : Tendsto f (map g x) y ↔ Tendsto (f ∘ g) x y
-/
theorem tendsto_atTop_of_monotone_of_subseq [Preorder ι] [Preorder α] {u : ι → α} {φ : ι' → ι}
    (h : Monotone u) {l : Filter ι'} [NeBot l] (H : Tendsto (u ∘ φ) l atTop) :
    Tendsto u atTop atTop :=
  tendsto_atTop_of_monotone_of_filter h (tendsto_map' H)

end Filter

