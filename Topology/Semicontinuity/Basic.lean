/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Antoine Chambert-Loir, Anatole Dedecker
-/
module

public import Mathlib.Topology.Semicontinuity.Defs
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Topology.Piecewise
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Lower and Upper Semicontinuity

This file develops key properties of upper and lower semicontinuous functions.

## Main definitions and results

We have some equivalent definitions of lower- and upper-semicontinuity (under certain
restrictions on the order on the codomain):
* `lowerSemicontinuous_iff_isOpen_preimage` in a linear order;
* `lowerSemicontinuous_iff_isClosed_preimage` in a linear order;
* `lowerSemicontinuousAt_iff_le_liminf` in a complete linear order;
* `lowerSemicontinuous_iff_isClosed_epigraph` in a linear order with the order
  topology.

We also prove:

* `indicator s (fun _ ↦ y)` is lower semicontinuous when `s` is open and `0 ≤ y`,
  or when `s` is closed and `y ≤ 0`;
* continuous functions are lower semicontinuous;
* left composition with a continuous monotone functions maps lower semicontinuous functions to lower
  semicontinuous functions. If the function is anti-monotone, it instead maps lower semicontinuous
  functions to upper semicontinuous functions;
* a sum of two (or finitely many) lower semicontinuous functions is lower semicontinuous;
* a supremum of a family of lower semicontinuous functions is lower semicontinuous;
* An infinite sum of `ℝ≥0∞`-valued lower semicontinuous functions is lower semicontinuous.

Similar results are stated and proved for upper semicontinuity.

We also prove that a function is continuous if and only if it is both lower and upper
semicontinuous.

## Implementation details

All the nontrivial results for upper semicontinuous functions are deduced from the corresponding
ones for lower semicontinuous functions using `OrderDual`.

## References

* <https://en.wikipedia.org/wiki/Closed_convex_function>
* <https://en.wikipedia.org/wiki/Semi-continuity>


+ lower and upper semicontinuity correspond to `r := (f · > ·)` and `r := (f · < ·)`;
+ lower and upper hemicontinuity correspond to `r := (fun x s ↦ IsOpen s ∧ ((f x) ∩ s).Nonempty)`
  and `r := (fun x s ↦ s ∈ 𝓝ˢ (f x))`, respectively.
-/

public section

open Topology ENNReal

open Set Function Filter

variable {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace γ] {f : α → β} {s t : Set α}
  {x : α} {y z : β}

/-! ### lower bounds -/

section

variable [LinearOrder β]

/-- A lower semicontinuous function attains its lower bound on a nonempty compact set. -/
/-
**LowerSemicontinuousOn.exists_isMinOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerSemicontinuousOn.exists_isMinOn {s : Set α} (ne_s : s.Nonempty) (hs :
 IsCompact s) (hf : LowerSemicontinuousOn f s) : exists a in s, IsMinOn f s a
参数：ne_s : s.Nonempty；hs : IsCompact s；hf : LowerSemicontinuousOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Exists.nonempty`：∀ {α : Sort u_1} {p : α → Prop}, (∃ x, p x) → Nonempty 
α
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `Filter.iInf_neBot_of_directed`：iInf_neBot_of_directed {f : ι -> Filter α
} [hn : Nonempty α] (hd : Directed (· >= ·) f) (hb : forall i, NeBot (f i)) : Ne
Bot (iInf f)
· 使用定理 `Directed.mono_comp`：Directed.mono_comp (r : α -> α -> Prop) {ι} {rb : β 
-> β -> Prop} {g : α -> β} {f : ι -> α} (hg : forall ⦃x y⦄, r x y -> rb (g x) (g
 y)) (hf…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.principal_mono`：principal_mono {s t : Set α} : 𝓟 s <= 𝓟 t ↔ s sub
seteq t
· 使用定理 `Set.inter_subset_inter_right`：inter_subset_inter_right {s t : Set α} (u 
: Set α) (H : s subseteq t) : u inter s subseteq u inter t
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `Set.Iic_subset_Iic`：Iic_subset_Iic : Iic a subseteq Iic b ↔ a <= b
· 使用定理 `Std.Total.directed`：Std.Total.directed [Std.Total r] (f : ι -> α) : Dire
cted r f
· 使用定理 `LE.total'`：∀ {α : Type u} [inst : LinearOrder α], Std.Total fun x1 x2 =>
 x2 ≤ x1
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Filter.neBot_of_le`：neBot_of_le {f g : Filter α} [hf : NeBot f] (hg : f 
<= g) : NeBot g
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Filter.mem_iInf_of_mem`：mem_iInf_of_mem {f : ι -> Filter α} (i : ι) {s} 
(hs : s in f i) : s in ⨅ i, f i
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `inf_le_inf_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α} (c :
 α), b ≤ a → c ⊓ b ≤ c ⊓ a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Filter.eventually_const`：eventually_const {f : Filter α} [t : NeBot f] {
p : Prop} : (forallᶠ _ in f, p) ↔ p

--- 原说明 ---
A lower semicontinuous function attains its lower bound on a nonempty compact se
t.
-/
theorem LowerSemicontinuousOn.exists_isMinOn {s : Set α} (ne_s : s.Nonempty)
    (hs : IsCompact s) (hf : LowerSemicontinuousOn f s) :
    ∃ a ∈ s, IsMinOn f s a := by
  simp only [isMinOn_iff]
  have _ : Nonempty α := Exists.nonempty ne_s
  have _ : Nonempty s := Nonempty.to_subtype ne_s
  let φ : β → Filter α := fun b ↦ 𝓟 (s ∩ f ⁻¹' Iic b)
  let ℱ : Filter α := ⨅ a : s, φ (f a)
  have : ℱ.NeBot := by
    apply iInf_neBot_of_directed _ _
    · change Directed GE.ge (fun x ↦ (φ ∘ (fun (a : s) ↦ f ↑a)) x)
      exact Directed.mono_comp GE.ge (fun x y hxy ↦
        principal_mono.mpr (inter_subset_inter_right _ (preimage_mono <| Iic_subset_Iic.mpr hxy)))
        (Std.Total.directed _)
    · intro x
      have : (pure x : Filter α) ≤ φ (f x) := le_principal_iff.mpr ⟨x.2, le_refl (f x)⟩
      exact neBot_of_le this
  have hℱs : ℱ ≤ 𝓟 s :=
    iInf_le_of_le (Classical.choice inferInstance) (principal_mono.mpr <| inter_subset_left)
  have hℱ (x) (hx : x ∈ s) : ∀ᶠ y in ℱ, f y ≤ f x :=
    mem_iInf_of_mem ⟨x, hx⟩ (by apply inter_subset_right)
  obtain ⟨a, ha, h⟩ := hs hℱs
  refine ⟨a, ha, fun x hx ↦ le_of_not_gt fun hxa ↦ ?_⟩
  let _ : (𝓝 a ⊓ ℱ).NeBot := h
  suffices ∀ᶠ _ in 𝓝 a ⊓ ℱ, False by rwa [eventually_const] at this
  filter_upwards [(hf a ha (f x) hxa).filter_mono (inf_le_inf_left _ hℱs),
    (hℱ x hx).filter_mono (inf_le_right : 𝓝 a ⊓ ℱ ≤ ℱ)] using fun y h₁ h₂ ↦ not_le_of_gt h₁ h₂

/-- A lower semicontinuous function is bounded below on a compact set. -/
/-
**LowerSemicontinuousOn.bddBelow_of_isCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerSemicontinuousOn.bddBelow_of_isCompact [Nonempty β] {s : Set α} (hs :
 IsCompact s) (hf : LowerSemicontinuousOn f s) : BddBelow (f '' s)
参数：hs : IsCompact s；hf : LowerSemicontinuousOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `bddBelow_empty`：∀ {α : Type u_1} [inst : Preorder α] [Nonempty α], BddBe
low ∅
· 使用定理 `LowerSemicontinuousOn.exists_isMinOn`：LowerSemicontinuousOn.exists_isMin
On {s : Set α} (ne_s : s.Nonempty) (hs : IsCompact s) (hf : LowerSemicontinuousO
n f s) : exists a in s, Is…
· 使用定理 `IsMinOn.bddBelow`：IsMinOn.bddBelow (h : IsMinOn f s a) : BddBelow (f '' 
s)

--- 原说明 ---
A lower semicontinuous function is bounded below on a compact set.
-/
theorem LowerSemicontinuousOn.bddBelow_of_isCompact [Nonempty β] {s : Set α} (hs : IsCompact s)
    (hf : LowerSemicontinuousOn f s) : BddBelow (f '' s) := by
  cases s.eq_empty_or_nonempty with
  | inl h =>
      simp only [h, Set.image_empty]
      exact bddBelow_empty
  | inr h =>
      obtain ⟨a, _, has⟩ := LowerSemicontinuousOn.exists_isMinOn h hs hf
      exact has.bddBelow

end

/-! #### Indicators -/


section

variable [Zero β] [Preorder β]

/-
**IsOpen.lowerSemicontinuous_indicator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.lowerSemicontinuous_indicator (hs : IsOpen s) (hy : 0 <= y) : Lower
Semicontinuous (indicator s fun _x => y)
参数：hs : IsOpen s；hy : 0 <= y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem IsOpen.lowerSemicontinuous_indicator (hs : IsOpen s) (hy : 0 ≤ y) :
    LowerSemicontinuous (indicator s fun _x => y) := by
  intro x z hz
  by_cases h : x ∈ s <;> simp [h] at hz
  · filter_upwards [hs.mem_nhds h]
    simp +contextual [hz]
  · refine Filter.Eventually.of_forall fun x' => ?_
    by_cases h' : x' ∈ s <;> simp [h', hz.trans_le hy, hz]
/-
**IsOpen.lowerSemicontinuousOn_indicator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.lowerSemicontinuousOn_indicator (hs : IsOpen s) (hy : 0 <= y) : Low
erSemicontinuousOn (indicator s fun _x => y) t
参数：hs : IsOpen s；hy : 0 <= y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSemicontinuous.lowerSemicontinuousOn`：LowerSemicontinuous.lowerSemi
continuousOn (h : LowerSemicontinuous f) (s : Set α) : LowerSemicontinuousOn f s
· 使用定理 `IsOpen.lowerSemicontinuous_indicator`：IsOpen.lowerSemicontinuous_indicat
or (hs : IsOpen s) (hy : 0 <= y) : LowerSemicontinuous (indicator s fun _x => y)
-/
theorem IsOpen.lowerSemicontinuousOn_indicator (hs : IsOpen s) (hy : 0 ≤ y) :
    LowerSemicontinuousOn (indicator s fun _x => y) t :=
  (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousOn t
/-
**IsOpen.lowerSemicontinuousAt_indicator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.lowerSemicontinuousAt_indicator (hs : IsOpen s) (hy : 0 <= y) : Low
erSemicontinuousAt (indicator s fun _x => y) x
参数：hs : IsOpen s；hy : 0 <= y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSemicontinuous.lowerSemicontinuousAt`：LowerSemicontinuous.lowerSemi
continuousAt (h : LowerSemicontinuous f) (x : α) : LowerSemicontinuousAt f x
· 使用定理 `IsOpen.lowerSemicontinuous_indicator`：IsOpen.lowerSemicontinuous_indicat
or (hs : IsOpen s) (hy : 0 <= y) : LowerSemicontinuous (indicator s fun _x => y)
-/
theorem IsOpen.lowerSemicontinuousAt_indicator (hs : IsOpen s) (hy : 0 ≤ y) :
    LowerSemicontinuousAt (indicator s fun _x => y) x :=
  (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousAt x
/-
**IsOpen.lowerSemicontinuousWithinAt_indicator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.lowerSemicontinuousWithinAt_indicator (hs : IsOpen s) (hy : 0 <= y)
 : LowerSemicontinuousWithinAt (indicator s fun _x => y) t x
参数：hs : IsOpen s；hy : 0 <= y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSemicontinuous.lowerSemicontinuousWithinAt`：LowerSemicontinuous.low
erSemicontinuousWithinAt (h : LowerSemicontinuous f) (s : Set α) (x : α) : Lower
SemicontinuousWithinAt f s x
· 使用定理 `IsOpen.lowerSemicontinuous_indicator`：IsOpen.lowerSemicontinuous_indicat
or (hs : IsOpen s) (hy : 0 <= y) : LowerSemicontinuous (indicator s fun _x => y)
-/
theorem IsOpen.lowerSemicontinuousWithinAt_indicator (hs : IsOpen s) (hy : 0 ≤ y) :
    LowerSemicontinuousWithinAt (indicator s fun _x => y) t x :=
  (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousWithinAt t x
/-
**IsClosed.lowerSemicontinuous_indicator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.lowerSemicontinuous_indicator (hs : IsClosed s) (hy : y <= 0) : L
owerSemicontinuous (indicator s fun _x => y)
参数：hs : IsClosed s；hy : y <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem IsClosed.lowerSemicontinuous_indicator (hs : IsClosed s) (hy : y ≤ 0) :
    LowerSemicontinuous (indicator s fun _x => y) := by
  intro x z hz
  by_cases h : x ∈ s <;> simp [h] at hz
  · refine Filter.Eventually.of_forall fun x' => ?_
    by_cases h' : x' ∈ s <;> simp [h', hz, hz.trans_le hy]
  · filter_upwards [hs.isOpen_compl.mem_nhds h]
    simp +contextual [hz]
/-
**IsClosed.lowerSemicontinuousOn_indicator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.lowerSemicontinuousOn_indicator (hs : IsClosed s) (hy : y <= 0) :
 LowerSemicontinuousOn (indicator s fun _x => y) t
参数：hs : IsClosed s；hy : y <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSemicontinuous.lowerSemicontinuousOn`：LowerSemicontinuous.lowerSemi
continuousOn (h : LowerSemicontinuous f) (s : Set α) : LowerSemicontinuousOn f s
· 使用定理 `IsClosed.lowerSemicontinuous_indicator`：IsClosed.lowerSemicontinuous_ind
icator (hs : IsClosed s) (hy : y <= 0) : LowerSemicontinuous (indicator s fun _x
 => y)
-/
theorem IsClosed.lowerSemicontinuousOn_indicator (hs : IsClosed s) (hy : y ≤ 0) :
    LowerSemicontinuousOn (indicator s fun _x => y) t :=
  (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousOn t
/-
**IsClosed.lowerSemicontinuousAt_indicator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.lowerSemicontinuousAt_indicator (hs : IsClosed s) (hy : y <= 0) :
 LowerSemicontinuousAt (indicator s fun _x => y) x
参数：hs : IsClosed s；hy : y <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSemicontinuous.lowerSemicontinuousAt`：LowerSemicontinuous.lowerSemi
continuousAt (h : LowerSemicontinuous f) (x : α) : LowerSemicontinuousAt f x
· 使用定理 `IsClosed.lowerSemicontinuous_indicator`：IsClosed.lowerSemicontinuous_ind
icator (hs : IsClosed s) (hy : y <= 0) : LowerSemicontinuous (indicator s fun _x
 => y)
-/
theorem IsClosed.lowerSemicontinuousAt_indicator (hs : IsClosed s) (hy : y ≤ 0) :
    LowerSemicontinuousAt (indicator s fun _x => y) x :=
  (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousAt x
/-
**IsClosed.lowerSemicontinuousWithinAt_indicator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.lowerSemicontinuousWithinAt_indicator (hs : IsClosed s) (hy : y <
= 0) : LowerSemicontinuousWithinAt (indicator s fun _x => y) t x
参数：hs : IsClosed s；hy : y <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSemicontinuous.lowerSemicontinuousWithinAt`：LowerSemicontinuous.low
erSemicontinuousWithinAt (h : LowerSemicontinuous f) (s : Set α) (x : α) : Lower
SemicontinuousWithinAt f s x
· 使用定理 `IsClosed.lowerSemicontinuous_indicator`：IsClosed.lowerSemicontinuous_ind
icator (hs : IsClosed s) (hy : y <= 0) : LowerSemicontinuous (indicator s fun _x
 => y)
-/
theorem IsClosed.lowerSemicontinuousWithinAt_indicator (hs : IsClosed s) (hy : y ≤ 0) :
    LowerSemicontinuousWithinAt (indicator s fun _x => y) t x :=
  (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousWithinAt t x

end

/-! #### Relationship with continuity -/

section

variable [Preorder β]

/-
**lowerSemicontinuous_iff_isOpen_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuous_iff_isOpen_preimage : LowerSemicontinuous f ↔ forall y
, IsOpen (f ⁻¹' Ioi y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
-/
theorem lowerSemicontinuous_iff_isOpen_preimage :
    LowerSemicontinuous f ↔ ∀ y, IsOpen (f ⁻¹' Ioi y) :=
  ⟨fun H y => isOpen_iff_mem_nhds.2 fun x hx => H x y hx, fun H _x y y_lt =>
    IsOpen.mem_nhds (H y) y_lt⟩
/-
**LowerSemicontinuous.isOpen_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerSemicontinuous.isOpen_preimage (hf : LowerSemicontinuous f) (y : β) :
 IsOpen (f ⁻¹' Ioi y)
参数：hf : LowerSemicontinuous f；y : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `lowerSemicontinuous_iff_isOpen_preimage`：lowerSemicontinuous_iff_isOpen_
preimage : LowerSemicontinuous f ↔ forall y, IsOpen (f ⁻¹' Ioi y)
-/
theorem LowerSemicontinuous.isOpen_preimage (hf : LowerSemicontinuous f) (y : β) :
    IsOpen (f ⁻¹' Ioi y) :=
  lowerSemicontinuous_iff_isOpen_preimage.1 hf y
/-
**lowerSemicontinuousOn_iff_preimage_Ioi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuousOn_iff_preimage_Ioi : LowerSemicontinuousOn f s ↔ foral
l b, exists u, IsOpen u ∧ s inter f ⁻¹' Set.Ioi b = s inter u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lowerSemicontinuousOn_iff_preimage_Ioi :
    LowerSemicontinuousOn f s ↔ ∀ b, ∃ u, IsOpen u ∧ s ∩ f ⁻¹' Set.Ioi b = s ∩ u := by
  simp only [← lowerSemicontinuous_restrict_iff, domRestrict_eq,
    lowerSemicontinuous_iff_isOpen_preimage, preimage_comp, isOpen_induced_iff,
    Subtype.preimage_coe_eq_preimage_coe_iff, eq_comm]

end

section

variable {ι : Type*} {f : ι → α → β} [Preorder β] {I : Set ι}

/-- Given a family of lower semicontinuous functions `f : ι → α → β` such that
for each `x : α`, there is a choice `M x : ι` such that the maximum value of
evaluation at `x` is achieved by the function `f (M x)`, then the pointwise
maximum of the family `f` is lower semicontinuous.
In the statement we restrict to subsets `I : Set ι` and `s : Set α` for more generality. -/
/-
**lowerSemicontinuousOn_of_forall_isMaxOn_and_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuousOn_of_forall_isMaxOn_and_mem (hfy : forall i in I, Lowe
rSemicontinuousOn (f i) s) {M : α -> ι} (M_mem : forall x in s, M x in I) (M_max
 : forall x in s, IsMaxOn (fun y => f y x) I (M x)) : LowerSemicontinuousOn (fun
 x => f (M x) x) s
参数：hfy : forall i in I, LowerSemicontinuousOn (f i) s；M_mem : forall x in s, M x
 in I；M_max : forall x in s, IsMaxOn (fun y => f y x) I (M x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `eventually_nhdsWithin_of_forall`：eventually_nhdsWithin_of_forall {s : Se
t α} {a : α} {p : α -> Prop} (h : forall x in s, p x) : forallᶠ x in 𝓝[s] a, p x
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c

--- 原说明 ---
Given a family of lower semicontinuous functions `f : ι → α → β` such that
for each `x : α`, there is a choice `M x : ι` such that the maximum value of
evaluation at `x` is achieved by the function `f (M x)`, then the pointwise
maximum of the family `f` is lower semicontinuous.
In the statement we restrict to subsets `I : Set ι` and `s : Set α` for more gen
erality.
-/
theorem lowerSemicontinuousOn_of_forall_isMaxOn_and_mem
    (hfy : ∀ i ∈ I, LowerSemicontinuousOn (f i) s)
    {M : α → ι}
    (M_mem : ∀ x ∈ s, M x ∈ I)
    (M_max : ∀ x ∈ s, IsMaxOn (fun y ↦ f y x) I (M x)) :
    LowerSemicontinuousOn (fun x ↦ f (M x) x) s := by
  intro x hx b hb
  apply Filter.Eventually.mp <| hfy (M x) (M_mem x hx) x hx b hb
  apply eventually_nhdsWithin_of_forall
  intro z hz h
  exact lt_of_lt_of_le h (M_max z hz (M_mem x hx))

/-- Given a family of upper semicontinuous functions `f : ι → α → β` such that
for each `x : α`, there is a choice `m x : ι` such that the minimum value of
evaluation at `x` is achieved by the function `f (m x)`, then the pointwise
maximum of the family `f` is upper semicontinuous.
In the statement we restrict to subsets `I : Set ι` and `s : Set α` for more generality. -/
/-
**upperSemicontinuousOn_of_forall_isMinOn_and_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperSemicontinuousOn_of_forall_isMinOn_and_mem (hfy : forall i in I, Uppe
rSemicontinuousOn (f i) s) {m : α -> ι} (m_mem : forall x in s, m x in I) (m_min
 : forall x in s, IsMinOn (fun i => f i x) I (m x)) : UpperSemicontinuousOn (fun
 x => f (m x) x) s
参数：hfy : forall i in I, UpperSemicontinuousOn (f i) s；m_mem : forall x in s, m x
 in I；m_min : forall x in s, IsMinOn (fun i => f i x) I (m x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lowerSemicontinuousOn_of_forall_isMaxOn_and_mem`：lowerSemicontinuousOn_o
f_forall_isMaxOn_and_mem (hfy : forall i in I, LowerSemicontinuousOn (f i) s) {M
 : α -> ι} (M_mem : forall x in s, M …

--- 原说明 ---
Given a family of upper semicontinuous functions `f : ι → α → β` such that
for each `x : α`, there is a choice `m x : ι` such that the minimum value of
evaluation at `x` is achieved by the function `f (m x)`, then the pointwise
maximum of the family `f` is upper semicontinuous.
In the statement we restrict to subsets `I : Set ι` and `s : Set α` for more gen
erality.
-/
theorem upperSemicontinuousOn_of_forall_isMinOn_and_mem
    (hfy : ∀ i ∈ I, UpperSemicontinuousOn (f i) s)
    {m : α → ι}
    (m_mem : ∀ x ∈ s, m x ∈ I)
    (m_min : ∀ x ∈ s, IsMinOn (fun i ↦ f i x) I (m x)) :
    UpperSemicontinuousOn (fun x ↦ f (m x) x) s :=
  lowerSemicontinuousOn_of_forall_isMaxOn_and_mem (β := βᵒᵈ) hfy m_mem m_min

end

section

variable {γ : Type*} [LinearOrder γ]

/-
**lowerSemicontinuous_iff_isClosed_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuous_iff_isClosed_preimage {f : α -> γ} : LowerSemicontinuo
us f ↔ forall y, IsClosed (f ⁻¹' Iic y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lowerSemicontinuous_iff_isOpen_preimage`：lowerSemicontinuous_iff_isOpen_
preimage : LowerSemicontinuous f ↔ forall y, IsOpen (f ⁻¹' Ioi y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Set.compl_Iic`：compl_Iic : (Iic a)ᶜ = Ioi a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lowerSemicontinuous_iff_isClosed_preimage {f : α → γ} :
    LowerSemicontinuous f ↔ ∀ y, IsClosed (f ⁻¹' Iic y) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  simp only [← isOpen_compl_iff, ← preimage_compl, compl_Iic]
/-
**LowerSemicontinuous.isClosed_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerSemicontinuous.isClosed_preimage {f : α -> γ} (hf : LowerSemicontinuo
us f) (y : γ) : IsClosed (f ⁻¹' Iic y)
参数：hf : LowerSemicontinuous f；y : γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `lowerSemicontinuous_iff_isClosed_preimage`：lowerSemicontinuous_iff_isClo
sed_preimage {f : α -> γ} : LowerSemicontinuous f ↔ forall y, IsClosed (f ⁻¹' Ii
c y)
-/
theorem LowerSemicontinuous.isClosed_preimage {f : α → γ} (hf : LowerSemicontinuous f) (y : γ) :
    IsClosed (f ⁻¹' Iic y) :=
  lowerSemicontinuous_iff_isClosed_preimage.1 hf y
/-
**lowerSemicontinuousOn_iff_preimage_Iic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuousOn_iff_preimage_Iic {f : α -> γ} : LowerSemicontinuousO
n f s ↔ forall b, exists v, IsClosed v ∧ s inter f ⁻¹' Set.Iic b = s inter v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lowerSemicontinuousOn_iff_preimage_Iic {f : α → γ} :
    LowerSemicontinuousOn f s ↔ ∀ b, ∃ v, IsClosed v ∧ s ∩ f ⁻¹' Set.Iic b = s ∩ v := by
  simp only [← lowerSemicontinuous_restrict_iff, domRestrict_eq,
      lowerSemicontinuous_iff_isClosed_preimage, preimage_comp,
      isClosed_induced_iff, Subtype.preimage_coe_eq_preimage_coe_iff, eq_comm]

variable [TopologicalSpace γ] [OrderTopology γ]
/-
**ContinuousWithinAt.lowerSemicontinuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.lowerSemicontinuousWithinAt {f : α -> γ} (h : Continuou
sWithinAt f s x) : LowerSemicontinuousWithinAt f s x
参数：h : ContinuousWithinAt f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ioi_mem_nhds`：Ioi_mem_nhds (h : a < b) : Ioi a in 𝓝 b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
-/
theorem ContinuousWithinAt.lowerSemicontinuousWithinAt {f : α → γ} (h : ContinuousWithinAt f s x) :
    LowerSemicontinuousWithinAt f s x := fun _y hy => h (Ioi_mem_nhds hy)
/-
**ContinuousAt.lowerSemicontinuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.lowerSemicontinuousAt {f : α -> γ} (h : ContinuousAt f x) : L
owerSemicontinuousAt f x
参数：h : ContinuousAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ioi_mem_nhds`：Ioi_mem_nhds (h : a < b) : Ioi a in 𝓝 b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
-/
theorem ContinuousAt.lowerSemicontinuousAt {f : α → γ} (h : ContinuousAt f x) :
    LowerSemicontinuousAt f x := fun _y hy => h (Ioi_mem_nhds hy)
/-
**ContinuousOn.lowerSemicontinuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.lowerSemicontinuousOn {f : α -> γ} (h : ContinuousOn f s) : L
owerSemicontinuousOn f s
参数：h : ContinuousOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.lowerSemicontinuousWithinAt`：ContinuousWithinAt.lower
SemicontinuousWithinAt {f : α -> γ} (h : ContinuousWithinAt f s x) : LowerSemico
ntinuousWithinAt f s x
-/
theorem ContinuousOn.lowerSemicontinuousOn {f : α → γ} (h : ContinuousOn f s) :
    LowerSemicontinuousOn f s := fun x hx => (h x hx).lowerSemicontinuousWithinAt
/-
**Continuous.lowerSemicontinuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.lowerSemicontinuous {f : α -> γ} (h : Continuous f) : LowerSemi
continuous f
参数：h : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.lowerSemicontinuousAt`：ContinuousAt.lowerSemicontinuousAt {
f : α -> γ} (h : ContinuousAt f x) : LowerSemicontinuousAt f x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
theorem Continuous.lowerSemicontinuous {f : α → γ} (h : Continuous f) : LowerSemicontinuous f :=
  fun _x => h.continuousAt.lowerSemicontinuousAt

end

/-! #### Equivalent definitions -/

section

variable {γ : Type*} [CompleteLinearOrder γ]

/-
**lowerSemicontinuousWithinAt_iff_le_liminf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuousWithinAt_iff_le_liminf {f : α -> γ} : LowerSemicontinuo
usWithinAt f s x ↔ f x <= liminf f (𝓝[s] x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `LT.lt.exists_disjoint_Iio_Ioi`：LT.lt.exists_disjoint_Iio_Ioi (h : a < b)
 : exists a' > a, exists b' < b, forall x < a', forall y > b', x < y
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Filter.le_liminf_of_le`：le_liminf_of_le {f : Filter β} {u : β -> α} {a} 
(hf : f.IsCoboundedUnder (· >= ·) u
· 使用定理 `Filter.isCobounded_ge_of_top`：∀ {α : Type u_1} [inst : LE α] [OrderTop α
] {f : Filter α}, Filter.IsCobounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `Filter.eventually_lt_of_lt_liminf`：eventually_lt_of_lt_liminf {f : Filte
r α} [ConditionallyCompleteLinearOrder β] {u : α -> β} {b : β} (h : b < liminf u
 f) (hu : f.IsBoundedUn…
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f
-/
theorem lowerSemicontinuousWithinAt_iff_le_liminf {f : α → γ} :
    LowerSemicontinuousWithinAt f s x ↔ f x ≤ liminf f (𝓝[s] x) := by
  constructor
  · intro h; unfold LowerSemicontinuousWithinAt at h
    by_contra! hf
    obtain ⟨z, ltz, y, ylt, h₁⟩ := hf.exists_disjoint_Iio_Ioi
    exact ltz.not_ge
      (le_liminf_of_le (by isBoundedDefault) ((h y ylt).mono fun _ h₂ =>
        le_of_not_gt fun h₃ => (h₁ _ h₃ _ h₂).false))
  exact fun hf y ylt => eventually_lt_of_lt_liminf (ylt.trans_le hf)

alias ⟨LowerSemicontinuousWithinAt.le_liminf, _⟩ := lowerSemicontinuousWithinAt_iff_le_liminf
/-
**lowerSemicontinuousAt_iff_le_liminf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuousAt_iff_le_liminf {f : α -> γ} : LowerSemicontinuousAt f
 x ↔ f x <= liminf f (𝓝 x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lowerSemicontinuousWithinAt_univ_iff`：lowerSemicontinuousWithinAt_univ_i
ff : LowerSemicontinuousWithinAt f univ x ↔ LowerSemicontinuousAt f x
· 使用定理 `lowerSemicontinuousWithinAt_iff_le_liminf`：lowerSemicontinuousWithinAt_i
ff_le_liminf {f : α -> γ} : LowerSemicontinuousWithinAt f s x ↔ f x <= liminf f 
(𝓝[s] x)
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lowerSemicontinuousAt_iff_le_liminf {f : α → γ} :
    LowerSemicontinuousAt f x ↔ f x ≤ liminf f (𝓝 x) := by
  rw [← lowerSemicontinuousWithinAt_univ_iff, lowerSemicontinuousWithinAt_iff_le_liminf,
    ← nhdsWithin_univ]

alias ⟨LowerSemicontinuousAt.le_liminf, _⟩ := lowerSemicontinuousAt_iff_le_liminf
/-
**lowerSemicontinuous_iff_le_liminf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuous_iff_le_liminf {f : α -> γ} : LowerSemicontinuous f ↔ f
orall x, f x <= liminf f (𝓝 x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lowerSemicontinuous_iff_le_liminf {f : α → γ} :
    LowerSemicontinuous f ↔ ∀ x, f x ≤ liminf f (𝓝 x) := by
  simp only [← lowerSemicontinuousAt_iff_le_liminf, lowerSemicontinuous_iff]

alias ⟨LowerSemicontinuous.le_liminf, _⟩ := lowerSemicontinuous_iff_le_liminf
/-
**lowerSemicontinuousOn_iff_le_liminf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuousOn_iff_le_liminf {f : α -> γ} : LowerSemicontinuousOn f
 s ↔ forall x in s, f x <= liminf f (𝓝[s] x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lowerSemicontinuousOn_iff_le_liminf {f : α → γ} :
    LowerSemicontinuousOn f s ↔ ∀ x ∈ s, f x ≤ liminf f (𝓝[s] x) := by
  simp only [← lowerSemicontinuousWithinAt_iff_le_liminf, lowerSemicontinuousOn_iff]

alias ⟨LowerSemicontinuousOn.le_liminf, _⟩ := lowerSemicontinuousOn_iff_le_liminf

end

section

variable {γ : Type*} [LinearOrder γ]

/-- The sublevel sets of a lower semicontinuous function on a compact set are compact. -/
/-
**LowerSemicontinuousOn.isCompact_inter_preimage_Iic** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：LowerSemicontinuousOn.isCompact_inter_preimage_Iic {f : α -> γ} (hfs : Low
erSemicontinuousOn f s) (ks : IsCompact s) (c : γ) : IsCompact (s inter f ⁻¹' Ii
c c)
参数：hfs : LowerSemicontinuousOn f s；ks : IsCompact s；c : γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lowerSemicontinuousOn_iff_preimage_Iic`：lowerSemicontinuousOn_iff_preima
ge_Iic {f : α -> γ} : LowerSemicontinuousOn f s ↔ forall b, exists v, IsClosed v
 ∧ s inter f ⁻¹' Set.Iic b =…
· 使用定理 `IsCompact.inter_right`：IsCompact.inter_right (hs : IsCompact s) (ht : Is
Closed t) : IsCompact (s inter t)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The sublevel sets of a lower semicontinuous function on a compact set are compac
t.
-/
theorem LowerSemicontinuousOn.isCompact_inter_preimage_Iic {f : α → γ}
    (hfs : LowerSemicontinuousOn f s) (ks : IsCompact s) (c : γ) :
    IsCompact (s ∩ f ⁻¹' Iic c) := by
  rw [lowerSemicontinuousOn_iff_preimage_Iic] at hfs
  obtain ⟨v, hv, hv'⟩ := hfs c
  exact hv' ▸ ks.inter_right hv

open scoped Set.Notation in
/-- An intersection of sublevel sets of a lower semicontinuous function
on a compact set is empty if and only if a finite sub-intersection is already empty. -/
/-
**LowerSemicontinuousOn.inter_biInter_preimage_Iic_eq_empty_iff_exists_finset** 
是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerSemicontinuousOn.inter_biInter_preimage_Iic_eq_empty_iff_exists_finse
t {ι : Type*} {f : ι -> α -> γ} (ks : IsCompact s) {I : Set ι} {c : γ} (hfi : fo
rall i in I, LowerSemicontinuousOn (f i) s) : s inter ⋂ i in I, (f i) ⁻¹' Iic c 
= ∅ ↔ exists u : Finset I, forall x in s, exists i in u, c < f i x
参数：ks : IsCompact s；hfi : forall i in I, LowerSemicontinuousOn (f i) s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSemicontinuous.isClosed_preimage`：LowerSemicontinuous.isClosed_prei
mage {f : α -> γ} (hf : LowerSemicontinuous f) (y : γ) : IsClosed (f ⁻¹' Iic y)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lowerSemicontinuous_restrict_iff`：∀ {α : Type u_1} {β : Type u_2} [inst 
: TopologicalSpace α] [inst_1 : Preorder β] {f : α → β} {s : Set α},   LowerSemi
continuous (s.domRestr…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.iInter_coe_set`：iInter_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋂ i, f i = ⋂ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `IsCompact.elim_finite_subfamily_isClosed_subtype`：IsCompact.elim_finite_
subfamily_isClosed_subtype {X : Type*} [TopologicalSpace X] {s : Set X} (ks : Is
Compact s) {ι : Type*} (t : ι -> Set X…
· 使用定理 `Set.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Set α} :
 s = ∅ ↔ forall x, x ∉ s

--- 原说明 ---
An intersection of sublevel sets of a lower semicontinuous function
on a compact set is empty if and only if a finite sub-intersection is already em
pty.
-/
theorem LowerSemicontinuousOn.inter_biInter_preimage_Iic_eq_empty_iff_exists_finset
    {ι : Type*} {f : ι → α → γ}
    (ks : IsCompact s) {I : Set ι} {c : γ} (hfi : ∀ i ∈ I, LowerSemicontinuousOn (f i) s) :
    s ∩ ⋂ i ∈ I, (f i) ⁻¹' Iic c = ∅ ↔ ∃ u : Finset I, ∀ x ∈ s, ∃ i ∈ u, c < f i x := by
  refine ⟨fun H ↦ ?_, fun ⟨u, hu⟩ ↦ ?_⟩
  · suffices ∀ i ∈ I, IsClosed (s ↓∩ (fun i ↦ f i ⁻¹' Iic c) i) by
      simpa [Set.eq_empty_iff_forall_notMem] using
        ks.elim_finite_subfamily_isClosed_subtype _ this H
    exact fun i hi ↦ lowerSemicontinuous_restrict_iff.mpr (hfi i hi) |>.isClosed_preimage c
  · rw [Set.eq_empty_iff_forall_notMem]
    simp only [mem_inter_iff, mem_iInter, mem_preimage, mem_Iic, not_and, not_forall,
      exists_prop, not_le]
    grind

variable [TopologicalSpace γ] [ClosedIciTopology γ]
/-
**lowerSemicontinuousOn_iff_isClosed_epigraph** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuousOn_iff_isClosed_epigraph {f : α -> γ} {s : Set α} (hs :
 IsClosed s) : LowerSemicontinuousOn f s ↔ IsClosed {p : α × γ | p.1 in s ∧ f p.
1 <= p.2}
参数：hs : IsClosed s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用引理 `LT.lt.exists_disjoint_Iio_Ioi`：LT.lt.exists_disjoint_Iio_Ioi (h : a < b)
 : exists a' > a, exists b' < b, forall x < a', forall y > b', x < y
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Eventually.prodMk_nhds`：Filter.Eventually.prodMk_nhds {px : X -> 
Prop} {x} (hx : forallᶠ x in 𝓝 x, px x) {py : Y -> Prop} {y} (hy : forallᶠ y in 
𝓝 y, py y) : forall…
· 使用定理 `eventually_lt_nhds`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 :
 LinearOrder α] [ClosedIciTopology α] {a b : α},   a < b → ∀ᶠ (x : α) in nhds a,
 x < b
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `IsOpen.eventually_mem`：IsOpen.eventually_mem (hs : IsOpen s) (hx : x in 
s) : forallᶠ x in 𝓝 x, x in s
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `Continuous.prodMk_left`：Continuous.prodMk_left (y : Y) : Continuous fun 
x : X => (x, y)
-/
theorem lowerSemicontinuousOn_iff_isClosed_epigraph {f : α → γ} {s : Set α} (hs : IsClosed s) :
    LowerSemicontinuousOn f s ↔ IsClosed {p : α × γ | p.1 ∈ s ∧ f p.1 ≤ p.2} := by
  simp_rw [lowerSemicontinuousOn_iff, lowerSemicontinuousWithinAt_iff,
    eventually_nhdsWithin_iff, ← isOpen_compl_iff, compl_ofPred, isOpen_iff_eventually, mem_ofPred,
    not_and, not_le]
  constructor
  · intro hf ⟨x, y⟩ h
    by_cases hx : x ∈ s
    · have ⟨y', hy', z, hz, h₁⟩ := (h hx).exists_disjoint_Iio_Ioi
      filter_upwards [(hf x hx z hz).prodMk_nhds (eventually_lt_nhds hy')]
        with _ ⟨h₂, h₃⟩ h₄ using h₁ _ h₃ _ <| h₂ h₄
    · filter_upwards [(continuous_fst.tendsto _).eventually (hs.isOpen_compl.eventually_mem hx)]
        with _ h₁ h₂ using (h₁ h₂).elim
  · intro hf x _ y hy
    exact ((Continuous.prodMk_left y).tendsto x).eventually (hf (x, y) (fun _ => hy))
/-
**lowerSemicontinuous_iff_isClosed_epigraph** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuous_iff_isClosed_epigraph {f : α -> γ} : LowerSemicontinuo
us f ↔ IsClosed {p : α × γ | f p.1 <= p.2}
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
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lowerSemicontinuous_iff_isClosed_epigraph {f : α → γ} :
    LowerSemicontinuous f ↔ IsClosed {p : α × γ | f p.1 ≤ p.2} := by
  simp [← lowerSemicontinuousOn_univ_iff, lowerSemicontinuousOn_iff_isClosed_epigraph]

alias ⟨LowerSemicontinuous.isClosed_epigraph, _⟩ := lowerSemicontinuous_iff_isClosed_epigraph

end

/-! ### Composition -/

section

variable [Preorder β]
variable {γ : Type*} [LinearOrder γ] [TopologicalSpace γ] [OrderTopology γ]
variable {δ : Type*} [LinearOrder δ] [TopologicalSpace δ] [OrderTopology δ]
variable {ι : Type*} [TopologicalSpace ι]

/-
**ContinuousAt.comp_lowerSemicontinuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.comp_lowerSemicontinuousWithinAt {g : γ -> δ} {f : α -> γ} (h
g : ContinuousAt g (f x)) (hf : LowerSemicontinuousWithinAt f s x) (gmon : Monot
one g) : LowerSemicontinuousWithinAt (g ∘ f) s x
参数：hg : ContinuousAt g (f x)；hf : LowerSemicontinuousWithinAt f s x；gmon : Monot
one g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_Ioc_subset_of_mem_nhds`：exists_Ioc_subset_of_mem_nhds {a : α} {s 
: Set α} (hs : s in 𝓝 a) (h : exists l, l < a) : exists l < a, Ioc l a subseteq 
s
· 使用定理 `Ioi_mem_nhds`：Ioi_mem_nhds (h : a < b) : Ioi a in 𝓝 b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem ContinuousAt.comp_lowerSemicontinuousWithinAt {g : γ → δ} {f : α → γ}
    (hg : ContinuousAt g (f x)) (hf : LowerSemicontinuousWithinAt f s x) (gmon : Monotone g) :
    LowerSemicontinuousWithinAt (g ∘ f) s x := by
  intro y hy
  by_cases! h : ∃ l, l < f x
  · obtain ⟨z, zlt, hz⟩ : ∃ z < f x, Ioc z (f x) ⊆ g ⁻¹' Ioi y :=
      exists_Ioc_subset_of_mem_nhds (hg (Ioi_mem_nhds hy)) h
    filter_upwards [hf z zlt] with a ha
    calc
      y < g (min (f x) (f a)) := hz (by simp [zlt, ha])
      _ ≤ g (f a) := gmon (min_le_right _ _)
  · exact Filter.Eventually.of_forall fun a => hy.trans_le (gmon (h (f a)))
/-
**ContinuousAt.comp_lowerSemicontinuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.comp_lowerSemicontinuousAt {g : γ -> δ} {f : α -> γ} (hg : Co
ntinuousAt g (f x)) (hf : LowerSemicontinuousAt f x) (gmon : Monotone g) : Lower
SemicontinuousAt (g ∘ f) x
参数：hg : ContinuousAt g (f x)；hf : LowerSemicontinuousAt f x；gmon : Monotone g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp_lowerSemicontinuousWithinAt`：ContinuousAt.comp_lowerSe
micontinuousWithinAt {g : γ -> δ} {f : α -> γ} (hg : ContinuousAt g (f x)) (hf :
 LowerSemicontinuousWithinAt f s x)…
-/
theorem ContinuousAt.comp_lowerSemicontinuousAt {g : γ → δ} {f : α → γ} (hg : ContinuousAt g (f x))
    (hf : LowerSemicontinuousAt f x) (gmon : Monotone g) : LowerSemicontinuousAt (g ∘ f) x := by
  simp only [← lowerSemicontinuousWithinAt_univ_iff] at hf ⊢
  exact hg.comp_lowerSemicontinuousWithinAt hf gmon
/-
**Continuous.comp_lowerSemicontinuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.comp_lowerSemicontinuousOn {g : γ -> δ} {f : α -> γ} (hg : Cont
inuous g) (hf : LowerSemicontinuousOn f s) (gmon : Monotone g) : LowerSemicontin
uousOn (g ∘ f) s
参数：hg : Continuous g；hf : LowerSemicontinuousOn f s；gmon : Monotone g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp_lowerSemicontinuousWithinAt`：ContinuousAt.comp_lowerSe
micontinuousWithinAt {g : γ -> δ} {f : α -> γ} (hg : ContinuousAt g (f x)) (hf :
 LowerSemicontinuousWithinAt f s x)…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
theorem Continuous.comp_lowerSemicontinuousOn {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : LowerSemicontinuousOn f s) (gmon : Monotone g) : LowerSemicontinuousOn (g ∘ f) s :=
  fun x hx => hg.continuousAt.comp_lowerSemicontinuousWithinAt (hf x hx) gmon
/-
**Continuous.comp_lowerSemicontinuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.comp_lowerSemicontinuous {g : γ -> δ} {f : α -> γ} (hg : Contin
uous g) (hf : LowerSemicontinuous f) (gmon : Monotone g) : LowerSemicontinuous (
g ∘ f)
参数：hg : Continuous g；hf : LowerSemicontinuous f；gmon : Monotone g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp_lowerSemicontinuousAt`：ContinuousAt.comp_lowerSemicont
inuousAt {g : γ -> δ} {f : α -> γ} (hg : ContinuousAt g (f x)) (hf : LowerSemico
ntinuousAt f x) (gmon : Monot…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
theorem Continuous.comp_lowerSemicontinuous {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : LowerSemicontinuous f) (gmon : Monotone g) : LowerSemicontinuous (g ∘ f) := fun x =>
  hg.continuousAt.comp_lowerSemicontinuousAt (hf x) gmon
/-
**ContinuousAt.comp_lowerSemicontinuousWithinAt_antitone** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：ContinuousAt.comp_lowerSemicontinuousWithinAt_antitone {g : γ -> δ} {f : α
 -> γ} (hg : ContinuousAt g (f x)) (hf : LowerSemicontinuousWithinAt f s x) (gmo
n : Antitone g) : UpperSemicontinuousWithinAt (g ∘ f) s x
参数：hg : ContinuousAt g (f x)；hf : LowerSemicontinuousWithinAt f s x；gmon : Antit
one g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp_lowerSemicontinuousWithinAt`：ContinuousAt.comp_lowerSe
micontinuousWithinAt {g : γ -> δ} {f : α -> γ} (hg : ContinuousAt g (f x)) (hf :
 LowerSemicontinuousWithinAt f s x)…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
theorem ContinuousAt.comp_lowerSemicontinuousWithinAt_antitone {g : γ → δ} {f : α → γ}
    (hg : ContinuousAt g (f x)) (hf : LowerSemicontinuousWithinAt f s x) (gmon : Antitone g) :
    UpperSemicontinuousWithinAt (g ∘ f) s x :=
  ContinuousAt.comp_lowerSemicontinuousWithinAt (δ := δᵒᵈ) hg hf gmon
/-
**ContinuousAt.comp_lowerSemicontinuousAt_antitone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.comp_lowerSemicontinuousAt_antitone {g : γ -> δ} {f : α -> γ}
 (hg : ContinuousAt g (f x)) (hf : LowerSemicontinuousAt f x) (gmon : Antitone g
) : UpperSemicontinuousAt (g ∘ f) x
参数：hg : ContinuousAt g (f x)；hf : LowerSemicontinuousAt f x；gmon : Antitone g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp_lowerSemicontinuousAt`：ContinuousAt.comp_lowerSemicont
inuousAt {g : γ -> δ} {f : α -> γ} (hg : ContinuousAt g (f x)) (hf : LowerSemico
ntinuousAt f x) (gmon : Monot…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
theorem ContinuousAt.comp_lowerSemicontinuousAt_antitone {g : γ → δ} {f : α → γ}
    (hg : ContinuousAt g (f x)) (hf : LowerSemicontinuousAt f x) (gmon : Antitone g) :
    UpperSemicontinuousAt (g ∘ f) x :=
  ContinuousAt.comp_lowerSemicontinuousAt (δ := δᵒᵈ) hg hf gmon
/-
**Continuous.comp_lowerSemicontinuousOn_antitone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.comp_lowerSemicontinuousOn_antitone {g : γ -> δ} {f : α -> γ} (
hg : Continuous g) (hf : LowerSemicontinuousOn f s) (gmon : Antitone g) : UpperS
emicontinuousOn (g ∘ f) s
参数：hg : Continuous g；hf : LowerSemicontinuousOn f s；gmon : Antitone g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp_lowerSemicontinuousWithinAt_antitone`：ContinuousAt.com
p_lowerSemicontinuousWithinAt_antitone {g : γ -> δ} {f : α -> γ} (hg : Continuou
sAt g (f x)) (hf : LowerSemicontinuousWithin…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
theorem Continuous.comp_lowerSemicontinuousOn_antitone {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : LowerSemicontinuousOn f s) (gmon : Antitone g) : UpperSemicontinuousOn (g ∘ f) s :=
  fun x hx => hg.continuousAt.comp_lowerSemicontinuousWithinAt_antitone (hf x hx) gmon
/-
**Continuous.comp_lowerSemicontinuous_antitone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.comp_lowerSemicontinuous_antitone {g : γ -> δ} {f : α -> γ} (hg
 : Continuous g) (hf : LowerSemicontinuous f) (gmon : Antitone g) : UpperSemicon
tinuous (g ∘ f)
参数：hg : Continuous g；hf : LowerSemicontinuous f；gmon : Antitone g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp_lowerSemicontinuousAt_antitone`：ContinuousAt.comp_lowe
rSemicontinuousAt_antitone {g : γ -> δ} {f : α -> γ} (hg : ContinuousAt g (f x))
 (hf : LowerSemicontinuousAt f x) (gmo…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
theorem Continuous.comp_lowerSemicontinuous_antitone {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : LowerSemicontinuous f) (gmon : Antitone g) : UpperSemicontinuous (g ∘ f) := fun x =>
  hg.continuousAt.comp_lowerSemicontinuousAt_antitone (hf x) gmon

end

/-! #### Addition -/


section

variable {ι : Type*} {γ : Type*} [AddCommMonoid γ] [LinearOrder γ] [IsOrderedAddMonoid γ]
  [TopologicalSpace γ] [OrderTopology γ]

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `EReal`. The unprimed version of
the lemma uses `[ContinuousAdd]`. -/
/-
**LowerSemicontinuousWithinAt.add'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerSemicontinuousWithinAt.add' {f g : α -> γ} (hf : LowerSemicontinuousW
ithinAt f s x) (hg : LowerSemicontinuousWithinAt g s x) (hcont : ContinuousAt (f
un p : γ × γ => p.1 + p.2) (f x, g x)) : LowerSemicontinuousWithinAt (fun z => f
 z + g z) s x
参数：hf : LowerSemicontinuousWithinAt f s x；hg : LowerSemicontinuousWithinAt g s x
；hcont : ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_prod_iff'`：mem_nhds_prod_iff' {x : X} {y : Y} {s : Set (X × Y)}
 : s in 𝓝 (x, y) ↔ exists u v, IsOpen u ∧ x in u ∧ IsOpen v ∧ y in v ∧ u ×ˢ v su
bseteq s
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_Ioi`：isOpen_Ioi : IsOpen (Ioi a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `exists_Ioc_subset_of_mem_nhds`：exists_Ioc_subset_of_mem_nhds {a : α} {s 
: Set α} (hs : s in 𝓝 a) (h : exists l, l < a) : exists l < a, Ioc l a subseteq 
s
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x

--- 原说明 ---
The sum of two lower semicontinuous functions is lower semicontinuous. Formulate
d with an
explicit continuity assumption on addition, for application to `EReal`. The unpr
imed version of
the lemma uses `[ContinuousAdd]`.
-/
theorem LowerSemicontinuousWithinAt.add' {f g : α → γ} (hf : LowerSemicontinuousWithinAt f s x)
    (hg : LowerSemicontinuousWithinAt g s x)
    (hcont : ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    LowerSemicontinuousWithinAt (fun z => f z + g z) s x := by
  intro y hy
  obtain ⟨u, v, u_open, xu, v_open, xv, h⟩ :
    ∃ u v : Set γ,
      IsOpen u ∧ f x ∈ u ∧ IsOpen v ∧ g x ∈ v ∧ u ×ˢ v ⊆ { p : γ × γ | y < p.fst + p.snd } :=
    mem_nhds_prod_iff'.1 (hcont (isOpen_Ioi.mem_nhds hy))
  by_cases hx₁ : ∃ l, l < f x
  · obtain ⟨z₁, z₁lt, h₁⟩ : ∃ z₁ < f x, Ioc z₁ (f x) ⊆ u :=
      exists_Ioc_subset_of_mem_nhds (u_open.mem_nhds xu) hx₁
    by_cases hx₂ : ∃ l, l < g x
    · obtain ⟨z₂, z₂lt, h₂⟩ : ∃ z₂ < g x, Ioc z₂ (g x) ⊆ v :=
        exists_Ioc_subset_of_mem_nhds (v_open.mem_nhds xv) hx₂
      filter_upwards [hf z₁ z₁lt, hg z₂ z₂lt] with z h₁z h₂z
      have A1 : min (f z) (f x) ∈ u := by
        by_cases! H : f z ≤ f x
        · simpa [H] using h₁ ⟨h₁z, H⟩
        · simpa [H.le]
      have A2 : min (g z) (g x) ∈ v := by
        by_cases! H : g z ≤ g x
        · simpa [H] using h₂ ⟨h₂z, H⟩
        · simpa [H.le]
      have : (min (f z) (f x), min (g z) (g x)) ∈ u ×ˢ v := ⟨A1, A2⟩
      calc
        y < min (f z) (f x) + min (g z) (g x) := h this
        _ ≤ f z + g z := add_le_add (min_le_left _ _) (min_le_left _ _)
    · simp only [not_exists, not_lt] at hx₂
      filter_upwards [hf z₁ z₁lt] with z h₁z
      have A1 : min (f z) (f x) ∈ u := by
        by_cases! H : f z ≤ f x
        · simpa [H] using h₁ ⟨h₁z, H⟩
        · simpa [H.le]
      have : (min (f z) (f x), g x) ∈ u ×ˢ v := ⟨A1, xv⟩
      calc
        y < min (f z) (f x) + g x := h this
        _ ≤ f z + g z := add_le_add (min_le_left _ _) (hx₂ (g z))
  · simp only [not_exists, not_lt] at hx₁
    by_cases hx₂ : ∃ l, l < g x
    · obtain ⟨z₂, z₂lt, h₂⟩ : ∃ z₂ < g x, Ioc z₂ (g x) ⊆ v :=
        exists_Ioc_subset_of_mem_nhds (v_open.mem_nhds xv) hx₂
      filter_upwards [hg z₂ z₂lt] with z h₂z
      have A2 : min (g z) (g x) ∈ v := by
        by_cases! H : g z ≤ g x
        · simpa [H] using h₂ ⟨h₂z, H⟩
        · simpa [H.le] using h₂ ⟨z₂lt, le_rfl⟩
      have : (f x, min (g z) (g x)) ∈ u ×ˢ v := ⟨xu, A2⟩
      calc
        y < f x + min (g z) (g x) := h this
        _ ≤ f z + g z := add_le_add (hx₁ (f z)) (min_le_left _ _)
    · simp only [not_exists, not_lt] at hx₁ hx₂
      apply Filter.Eventually.of_forall
      intro z
      have : (f x, g x) ∈ u ×ˢ v := ⟨xu, xv⟩
      calc
        y < f x + g x := h this
        _ ≤ f z + g z := add_le_add (hx₁ (f z)) (hx₂ (g z))

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `EReal`. The unprimed version of
the lemma uses `[ContinuousAdd]`. -/
/-
**LowerSemicontinuousAt.add'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerSemicontinuousAt.add' {f g : α -> γ} (hf : LowerSemicontinuousAt f x)
 (hg : LowerSemicontinuousAt g x) (hcont : ContinuousAt (fun p : γ × γ => p.1 + 
p.2) (f x, g x)) : LowerSemicontinuousAt (fun z => f z + g z) x
参数：hf : LowerSemicontinuousAt f x；hg : LowerSemicontinuousAt g x；hcont : Continu
ousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSemicontinuousWithinAt.add'`：LowerSemicontinuousWithinAt.add' {f g 
: α -> γ} (hf : LowerSemicontinuousWithinAt f s x) (hg : LowerSemicontinuousWith
inAt g s x) (hcont : C…

--- 原说明 ---
The sum of two lower semicontinuous functions is lower semicontinuous. Formulate
d with an
explicit continuity assumption on addition, for application to `EReal`. The unpr
imed version of
the lemma uses `[ContinuousAdd]`.
-/
theorem LowerSemicontinuousAt.add' {f g : α → γ} (hf : LowerSemicontinuousAt f x)
    (hg : LowerSemicontinuousAt g x)
    (hcont : ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    LowerSemicontinuousAt (fun z => f z + g z) x := by
  simp_rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  exact hf.add' hg hcont

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `EReal`. The unprimed version of
the lemma uses `[ContinuousAdd]`. -/
/-
**LowerSemicontinuousOn.add'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerSemicontinuousOn.add' {f g : α -> γ} (hf : LowerSemicontinuousOn f s)
 (hg : LowerSemicontinuousOn g s) (hcont : forall x in s, ContinuousAt (fun p : 
γ × γ => p.1 + p.2) (f x, g x)) : LowerSemicontinuousOn (fun z => f z + g z) s
参数：hf : LowerSemicontinuousOn f s；hg : LowerSemicontinuousOn g s；hcont : forall 
x in s, ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSemicontinuousWithinAt.add'`：LowerSemicontinuousWithinAt.add' {f g 
: α -> γ} (hf : LowerSemicontinuousWithinAt f s x) (hg : LowerSemicontinuousWith
inAt g s x) (hcont : C…

--- 原说明 ---
The sum of two lower semicontinuous functions is lower semicontinuous. Formulate
d with an
explicit continuity assumption on addition, for application to `EReal`. The unpr
imed version of
the lemma uses `[ContinuousAdd]`.
-/
theorem LowerSemicontinuousOn.add' {f g : α → γ} (hf : LowerSemicontinuousOn f s)
    (hg : LowerSemicontinuousOn g s)
    (hcont : ∀ x ∈ s, ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    LowerSemicontinuousOn (fun z => f z + g z) s := fun x hx =>
  LowerSemicontinuousWithinAt.add' (hf x hx) (hg x hx) (hcont x hx)

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `EReal`. The unprimed version of
the lemma uses `[ContinuousAdd]`. -/
/-
**LowerSemicontinuous.add'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerSemicontinuous.add' {f g : α -> γ} (hf : LowerSemicontinuous f) (hg :
 LowerSemicontinuous g) (hcont : forall x, ContinuousAt (fun p : γ × γ => p.1 + 
p.2) (f x, g x)) : LowerSemicontinuous fun z => f z + g z
参数：hf : LowerSemicontinuous f；hg : LowerSemicontinuous g；hcont : forall x, Conti
nuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSemicontinuousAt.add'`：LowerSemicontinuousAt.add' {f g : α -> γ} (h
f : LowerSemicontinuousAt f x) (hg : LowerSemicontinuousAt g x) (hcont : Continu
ousAt (fun p : γ…

--- 原说明 ---
The sum of two lower semicontinuous functions is lower semicontinuous. Formulate
d with an
explicit continuity assumption on addition, for application to `EReal`. The unpr
imed version of
the lemma uses `[ContinuousAdd]`.
-/
theorem LowerSemicontinuous.add' {f g : α → γ} (hf : LowerSemicontinuous f)
    (hg : LowerSemicontinuous g)
    (hcont : ∀ x, ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    LowerSemicontinuous fun z => f z + g z :=
  fun x => LowerSemicontinuousAt.add' (hf x) (hg x) (hcont x)

variable [ContinuousAdd γ]

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with
`[ContinuousAdd]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `EReal`. -/
/-
**LowerSemicontinuousWithinAt.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerSemicontinuousWithinAt.add {f g : α -> γ} (hf : LowerSemicontinuousWi
thinAt f s x) (hg : LowerSemicontinuousWithinAt g s x) : LowerSemicontinuousWith
inAt (fun z => f z + g z) s x
参数：hf : LowerSemicontinuousWithinAt f s x；hg : LowerSemicontinuousWithinAt g s x
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSemicontinuousWithinAt.add'`：LowerSemicontinuousWithinAt.add' {f g 
: α -> γ} (hf : LowerSemicontinuousWithinAt f s x) (hg : LowerSemicontinuousWith
inAt g s x) (hcont : C…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_add`：continuous_add : Continuous (fun x : X × X ↦ x.1 + x.2)

--- 原说明 ---
The sum of two lower semicontinuous functions is lower semicontinuous. Formulate
d with
`[ContinuousAdd]`. The primed version of the lemma uses an explicit continuity a
ssumption on
addition, for application to `EReal`.
-/
theorem LowerSemicontinuousWithinAt.add {f g : α → γ} (hf : LowerSemicontinuousWithinAt f s x)
    (hg : LowerSemicontinuousWithinAt g s x) :
    LowerSemicontinuousWithinAt (fun z => f z + g z) s x :=
  hf.add' hg continuous_add.continuousAt

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with
`[ContinuousAdd]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `EReal`. -/
/-
**LowerSemicontinuousAt.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerSemicontinuousAt.add {f g : α -> γ} (hf : LowerSemicontinuousAt f x) 
(hg : LowerSemicontinuousAt g x) : LowerSemicontinuousAt (fun z => f z + g z) x
参数：hf : LowerSemicontinuousAt f x；hg : LowerSemicontinuousAt g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSemicontinuousAt.add'`：LowerSemicontinuousAt.add' {f g : α -> γ} (h
f : LowerSemicontinuousAt f x) (hg : LowerSemicontinuousAt g x) (hcont : Continu
ousAt (fun p : γ…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_add`：continuous_add : Continuous (fun x : X × X ↦ x.1 + x.2)

--- 原说明 ---
The sum of two lower semicontinuous functions is lower semicontinuous. Formulate
d with
`[ContinuousAdd]`. The primed version of the lemma uses an explicit continuity a
ssumption on
addition, for application to `EReal`.
-/
theorem LowerSemicontinuousAt.add {f g : α → γ} (hf : LowerSemicontinuousAt f x)
    (hg : LowerSemicontinuousAt g x) : LowerSemicontinuousAt (fun z => f z + g z) x :=
  hf.add' hg continuous_add.continuousAt

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with
`[ContinuousAdd]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `EReal`. -/
/-
**LowerSemicontinuousOn.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerSemicontinuousOn.add {f g : α -> γ} (hf : LowerSemicontinuousOn f s) 
(hg : LowerSemicontinuousOn g s) : LowerSemicontinuousOn (fun z => f z + g z) s
参数：hf : LowerSemicontinuousOn f s；hg : LowerSemicontinuousOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSemicontinuousOn.add'`：LowerSemicontinuousOn.add' {f g : α -> γ} (h
f : LowerSemicontinuousOn f s) (hg : LowerSemicontinuousOn g s) (hcont : forall 
x in s, Continuo…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_add`：continuous_add : Continuous (fun x : X × X ↦ x.1 + x.2)

--- 原说明 ---
The sum of two lower semicontinuous functions is lower semicontinuous. Formulate
d with
`[ContinuousAdd]`. The primed version of the lemma uses an explicit continuity a
ssumption on
addition, for application to `EReal`.
-/
theorem LowerSemicontinuousOn.add {f g : α → γ} (hf : LowerSemicontinuousOn f s)
    (hg : LowerSemicontinuousOn g s) : LowerSemicontinuousOn (fun z => f z + g z) s :=
  hf.add' hg fun _x _hx => continuous_add.continuousAt

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with
`[ContinuousAdd]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `EReal`. -/
/-
**LowerSemicontinuous.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerSemicontinuous.add {f g : α -> γ} (hf : LowerSemicontinuous f) (hg : 
LowerSemicontinuous g) : LowerSemicontinuous fun z => f z + g z
参数：hf : LowerSemicontinuous f；hg : LowerSemicontinuous g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSemicontinuous.add'`：LowerSemicontinuous.add' {f g : α -> γ} (hf : 
LowerSemicontinuous f) (hg : LowerSemicontinuous g) (hcont : forall x, Continuou
sAt (fun p : γ…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_add`：continuous_add : Continuous (fun x : X × X ↦ x.1 + x.2)

--- 原说明 ---
The sum of two lower semicontinuous functions is lower semicontinuous. Formulate
d with
`[ContinuousAdd]`. The primed version of the lemma uses an explicit continuity a
ssumption on
addition, for application to `EReal`.
-/
theorem LowerSemicontinuous.add {f g : α → γ} (hf : LowerSemicontinuous f)
    (hg : LowerSemicontinuous g) : LowerSemicontinuous fun z => f z + g z :=
  hf.add' hg fun _x => continuous_add.continuousAt
/-
**lowerSemicontinuousWithinAt_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuousWithinAt_sum {f : ι -> α -> γ} {a : Finset ι} (ha : for
all i in a, LowerSemicontinuousWithinAt (f i) s x) : LowerSemicontinuousWithinAt
 (fun z => ∑ i in a, f i z) s x
参数：ha : forall i in a, LowerSemicontinuousWithinAt (f i) s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `lowerSemicontinuousWithinAt_const`：lowerSemicontinuousWithinAt_const : L
owerSemicontinuousWithinAt (fun _x => z) s x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LowerSemicontinuousWithinAt.add`：LowerSemicontinuousWithinAt.add {f g : 
α -> γ} (hf : LowerSemicontinuousWithinAt f s x) (hg : LowerSemicontinuousWithin
At g s x) : LowerSemi…
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
-/
theorem lowerSemicontinuousWithinAt_sum {f : ι → α → γ} {a : Finset ι}
    (ha : ∀ i ∈ a, LowerSemicontinuousWithinAt (f i) s x) :
    LowerSemicontinuousWithinAt (fun z => ∑ i ∈ a, f i z) s x := by
  classical
    induction a using Finset.induction_on with
    | empty => exact lowerSemicontinuousWithinAt_const
    | insert _ _ ia IH =>
      simp only [ia, Finset.sum_insert, not_false_iff]
      exact
        LowerSemicontinuousWithinAt.add (ha _ (Finset.mem_insert_self ..))
          (IH fun j ja => ha j (Finset.mem_insert_of_mem ja))
/-
**lowerSemicontinuousAt_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuousAt_sum {f : ι -> α -> γ} {a : Finset ι} (ha : forall i 
in a, LowerSemicontinuousAt (f i) x) : LowerSemicontinuousAt (fun z => ∑ i in a,
 f i z) x
参数：ha : forall i in a, LowerSemicontinuousAt (f i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lowerSemicontinuousWithinAt_sum`：lowerSemicontinuousWithinAt_sum {f : ι 
-> α -> γ} {a : Finset ι} (ha : forall i in a, LowerSemicontinuousWithinAt (f i)
 s x) : LowerSemicont…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem lowerSemicontinuousAt_sum {f : ι → α → γ} {a : Finset ι}
    (ha : ∀ i ∈ a, LowerSemicontinuousAt (f i) x) :
    LowerSemicontinuousAt (fun z => ∑ i ∈ a, f i z) x := by
  simp_rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  exact lowerSemicontinuousWithinAt_sum ha
/-
**lowerSemicontinuousOn_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuousOn_sum {f : ι -> α -> γ} {a : Finset ι} (ha : forall i 
in a, LowerSemicontinuousOn (f i) s) : LowerSemicontinuousOn (fun z => ∑ i in a,
 f i z) s
参数：ha : forall i in a, LowerSemicontinuousOn (f i) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lowerSemicontinuousWithinAt_sum`：lowerSemicontinuousWithinAt_sum {f : ι 
-> α -> γ} {a : Finset ι} (ha : forall i in a, LowerSemicontinuousWithinAt (f i)
 s x) : LowerSemicont…
-/
theorem lowerSemicontinuousOn_sum {f : ι → α → γ} {a : Finset ι}
    (ha : ∀ i ∈ a, LowerSemicontinuousOn (f i) s) :
    LowerSemicontinuousOn (fun z => ∑ i ∈ a, f i z) s := fun x hx =>
  lowerSemicontinuousWithinAt_sum fun i hi => ha i hi x hx
/-
**lowerSemicontinuous_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuous_sum {f : ι -> α -> γ} {a : Finset ι} (ha : forall i in
 a, LowerSemicontinuous (f i)) : LowerSemicontinuous fun z => ∑ i in a, f i z
参数：ha : forall i in a, LowerSemicontinuous (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lowerSemicontinuousAt_sum`：lowerSemicontinuousAt_sum {f : ι -> α -> γ} {
a : Finset ι} (ha : forall i in a, LowerSemicontinuousAt (f i) x) : LowerSemicon
tinuousAt (fun …
-/
theorem lowerSemicontinuous_sum {f : ι → α → γ} {a : Finset ι}
    (ha : ∀ i ∈ a, LowerSemicontinuous (f i)) : LowerSemicontinuous fun z => ∑ i ∈ a, f i z :=
  fun x => lowerSemicontinuousAt_sum fun i hi => ha i hi x

end

/-! #### Supremum -/

section

variable {α : Type*} {β : Type*} [TopologicalSpace α] [LinearOrder β]
  {f g : α → β} {s : Set α} {a : α}

/-
**LowerSemicontinuousWithinAt.sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerSemicontinuousWithinAt.sup (hf : LowerSemicontinuousWithinAt f s a) (
hg : LowerSemicontinuousWithinAt g s a) : LowerSemicontinuousWithinAt (fun x => 
f x ⊔ g x) s a
参数：hf : LowerSemicontinuousWithinAt f s a；hg : LowerSemicontinuousWithinAt g s a
。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `Or.intro_left`：∀ {a : Prop} (b : Prop), a → a ∨ b
· 使用定理 `Or.intro_right`：∀ {b : Prop} (a : Prop), b → a ∨ b
-/
theorem LowerSemicontinuousWithinAt.sup
    (hf : LowerSemicontinuousWithinAt f s a) (hg : LowerSemicontinuousWithinAt g s a) :
    LowerSemicontinuousWithinAt (fun x ↦ f x ⊔ g x) s a := by
  intro b hb
  simp only [lt_sup_iff] at hb ⊢
  rcases hb with hb | hb
  · filter_upwards [hf b hb] with x using Or.intro_left _
  · filter_upwards [hg b hb] with x using Or.intro_right _
/-
**LowerSemicontinuousAt.sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerSemicontinuousAt.sup (hf : LowerSemicontinuousAt f a) (hg : LowerSemi
continuousAt g a) : LowerSemicontinuousAt (fun x => f x ⊔ g x) a
参数：hf : LowerSemicontinuousAt f a；hg : LowerSemicontinuousAt g a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lowerSemicontinuousWithinAt_univ_iff`：lowerSemicontinuousWithinAt_univ_i
ff : LowerSemicontinuousWithinAt f univ x ↔ LowerSemicontinuousAt f x
· 使用定理 `LowerSemicontinuousWithinAt.sup`：LowerSemicontinuousWithinAt.sup (hf : L
owerSemicontinuousWithinAt f s a) (hg : LowerSemicontinuousWithinAt g s a) : Low
erSemicontinuousWithi…
-/
theorem LowerSemicontinuousAt.sup
    (hf : LowerSemicontinuousAt f a) (hg : LowerSemicontinuousAt g a) :
    LowerSemicontinuousAt (fun x ↦ f x ⊔ g x) a := by
  rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  exact hf.sup hg
/-
**LowerSemicontinuousOn.sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerSemicontinuousOn.sup (hf : LowerSemicontinuousOn f s) (hg : LowerSemi
continuousOn g s) : LowerSemicontinuousOn (fun x => f x ⊔ g x) s
参数：hf : LowerSemicontinuousOn f s；hg : LowerSemicontinuousOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSemicontinuousWithinAt.sup`：LowerSemicontinuousWithinAt.sup (hf : L
owerSemicontinuousWithinAt f s a) (hg : LowerSemicontinuousWithinAt g s a) : Low
erSemicontinuousWithi…
-/
theorem LowerSemicontinuousOn.sup
    (hf : LowerSemicontinuousOn f s) (hg : LowerSemicontinuousOn g s) :
    LowerSemicontinuousOn (fun x ↦ f x ⊔ g x) s := fun a ha ↦
  LowerSemicontinuousWithinAt.sup (hf a ha) (hg a ha)
/-
**LowerSemicontinuous.sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerSemicontinuous.sup (hf : LowerSemicontinuous f) (hg : LowerSemicontin
uous g) : LowerSemicontinuous fun x => f x ⊔ g x
参数：hf : LowerSemicontinuous f；hg : LowerSemicontinuous g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSemicontinuousAt.sup`：LowerSemicontinuousAt.sup (hf : LowerSemicont
inuousAt f a) (hg : LowerSemicontinuousAt g a) : LowerSemicontinuousAt (fun x =>
 f x ⊔ g x) a
-/
theorem LowerSemicontinuous.sup
    (hf : LowerSemicontinuous f) (hg : LowerSemicontinuous g) :
    LowerSemicontinuous fun x ↦ f x ⊔ g x := fun a ↦
  LowerSemicontinuousAt.sup (hf a) (hg a)
/-
**LowerSemicontinuousWithinAt.inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerSemicontinuousWithinAt.inf (hf : LowerSemicontinuousWithinAt f s a) (
hg : LowerSemicontinuousWithinAt g s a) : LowerSemicontinuousWithinAt (fun x => 
f x ⊓ g x) s a
参数：hf : LowerSemicontinuousWithinAt f s a；hg : LowerSemicontinuousWithinAt g s a
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem LowerSemicontinuousWithinAt.inf
    (hf : LowerSemicontinuousWithinAt f s a) (hg : LowerSemicontinuousWithinAt g s a) :
    LowerSemicontinuousWithinAt (fun x ↦ f x ⊓ g x) s a := by
  intro b hb
  simp only [lt_inf_iff] at hb ⊢
  exact Eventually.and (hf b hb.1) (hg b hb.2)
/-
**LowerSemicontinuousAt.inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerSemicontinuousAt.inf (hf : LowerSemicontinuousAt f a) (hg : LowerSemi
continuousAt g a) : LowerSemicontinuousAt (fun x => f x ⊓ g x) a
参数：hf : LowerSemicontinuousAt f a；hg : LowerSemicontinuousAt g a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lowerSemicontinuousWithinAt_univ_iff`：lowerSemicontinuousWithinAt_univ_i
ff : LowerSemicontinuousWithinAt f univ x ↔ LowerSemicontinuousAt f x
· 使用定理 `LowerSemicontinuousWithinAt.inf`：LowerSemicontinuousWithinAt.inf (hf : L
owerSemicontinuousWithinAt f s a) (hg : LowerSemicontinuousWithinAt g s a) : Low
erSemicontinuousWithi…
-/
theorem LowerSemicontinuousAt.inf
    (hf : LowerSemicontinuousAt f a) (hg : LowerSemicontinuousAt g a) :
    LowerSemicontinuousAt (fun x ↦ f x ⊓ g x) a := by
  rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  exact hf.inf hg
/-
**LowerSemicontinuousOn.inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerSemicontinuousOn.inf (hf : LowerSemicontinuousOn f s) (hg : LowerSemi
continuousOn g s) : LowerSemicontinuousOn (fun x => f x ⊓ g x) s
参数：hf : LowerSemicontinuousOn f s；hg : LowerSemicontinuousOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSemicontinuousWithinAt.inf`：LowerSemicontinuousWithinAt.inf (hf : L
owerSemicontinuousWithinAt f s a) (hg : LowerSemicontinuousWithinAt g s a) : Low
erSemicontinuousWithi…
-/
theorem LowerSemicontinuousOn.inf
    (hf : LowerSemicontinuousOn f s) (hg : LowerSemicontinuousOn g s) :
    LowerSemicontinuousOn (fun x ↦ f x ⊓ g x) s := fun a ha ↦
  LowerSemicontinuousWithinAt.inf (hf a ha) (hg a ha)
/-
**LowerSemicontinuous.inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerSemicontinuous.inf (hf : LowerSemicontinuous f) (hg : LowerSemicontin
uous g) : LowerSemicontinuous fun x => f x ⊓ g x
参数：hf : LowerSemicontinuous f；hg : LowerSemicontinuous g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSemicontinuousAt.inf`：LowerSemicontinuousAt.inf (hf : LowerSemicont
inuousAt f a) (hg : LowerSemicontinuousAt g a) : LowerSemicontinuousAt (fun x =>
 f x ⊓ g x) a
-/
theorem LowerSemicontinuous.inf (hf : LowerSemicontinuous f)
    (hg : LowerSemicontinuous g) :
    LowerSemicontinuous fun x ↦ f x ⊓ g x := fun a ↦
  LowerSemicontinuousAt.inf (hf a) (hg a)

end

section

variable {ι : Sort*} {δ δ' : Type*} [CompleteLinearOrder δ] [ConditionallyCompleteLinearOrder δ']

/-
**lowerSemicontinuousWithinAt_ciSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuousWithinAt_ciSup {f : ι -> α -> δ'} (bdd : forallᶠ y in 𝓝
[s] x, BddAbove (range fun i => f i y)) (h : forall i, LowerSemicontinuousWithin
At (f i) s x) : LowerSemicontinuousWithinAt (fun x' => ⨆ i, f i x') s x
参数：bdd : forallᶠ y in 𝓝[s] x, BddAbove (range fun i => f i y)；h : forall i, Lowe
rSemicontinuousWithinAt (f i) s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_of_empty'`：iSup_of_empty' {α ι} [SupSet α] [IsEmpty ι] (f : ι -> α)
 : iSup f = sSup (∅ : Set α)
· 使用定理 `lowerSemicontinuousWithinAt_const`：lowerSemicontinuousWithinAt_const : L
owerSemicontinuousWithinAt (fun _x => z) s x
· 使用定理 `exists_lt_of_lt_ciSup`：exists_lt_of_lt_ciSup [Nonempty ι] {f : ι -> α} (
h : b < iSup f) : exists i, b < f i
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
-/
theorem lowerSemicontinuousWithinAt_ciSup {f : ι → α → δ'}
    (bdd : ∀ᶠ y in 𝓝[s] x, BddAbove (range fun i => f i y))
    (h : ∀ i, LowerSemicontinuousWithinAt (f i) s x) :
    LowerSemicontinuousWithinAt (fun x' => ⨆ i, f i x') s x := by
  cases isEmpty_or_nonempty ι
  · simpa only [iSup_of_empty'] using lowerSemicontinuousWithinAt_const
  · intro y hy
    rcases exists_lt_of_lt_ciSup hy with ⟨i, hi⟩
    filter_upwards [h i y hi, bdd] with y hy hy' using hy.trans_le (le_ciSup hy' i)
/-
**lowerSemicontinuousWithinAt_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuousWithinAt_iSup {f : ι -> α -> δ} (h : forall i, LowerSem
icontinuousWithinAt (f i) s x) : LowerSemicontinuousWithinAt (fun x' => ⨆ i, f i
 x') s x
参数：h : forall i, LowerSemicontinuousWithinAt (f i) s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lowerSemicontinuousWithinAt_ciSup`：lowerSemicontinuousWithinAt_ciSup {f 
: ι -> α -> δ'} (bdd : forallᶠ y in 𝓝[s] x, BddAbove (range fun i => f i y)) (h 
: forall i, LowerSemico…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem lowerSemicontinuousWithinAt_iSup {f : ι → α → δ}
    (h : ∀ i, LowerSemicontinuousWithinAt (f i) s x) :
    LowerSemicontinuousWithinAt (fun x' => ⨆ i, f i x') s x :=
  lowerSemicontinuousWithinAt_ciSup (by simp) h
/-
**lowerSemicontinuousWithinAt_biSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuousWithinAt_biSup {p : ι -> Prop} {f : forall i, p i -> α 
-> δ} (h : forall i hi, LowerSemicontinuousWithinAt (f i hi) s x) : LowerSemicon
tinuousWithinAt (fun x' => ⨆ (i) (hi), f i hi x') s x
参数：h : forall i hi, LowerSemicontinuousWithinAt (f i hi) s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lowerSemicontinuousWithinAt_iSup`：lowerSemicontinuousWithinAt_iSup {f : 
ι -> α -> δ} (h : forall i, LowerSemicontinuousWithinAt (f i) s x) : LowerSemico
ntinuousWithinAt (fun …
-/
theorem lowerSemicontinuousWithinAt_biSup {p : ι → Prop} {f : ∀ i, p i → α → δ}
    (h : ∀ i hi, LowerSemicontinuousWithinAt (f i hi) s x) :
    LowerSemicontinuousWithinAt (fun x' => ⨆ (i) (hi), f i hi x') s x :=
  lowerSemicontinuousWithinAt_iSup fun i => lowerSemicontinuousWithinAt_iSup fun hi => h i hi
/-
**lowerSemicontinuousAt_ciSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuousAt_ciSup {f : ι -> α -> δ'} (bdd : forallᶠ y in 𝓝 x, Bd
dAbove (range fun i => f i y)) (h : forall i, LowerSemicontinuousAt (f i) x) : L
owerSemicontinuousAt (fun x' => ⨆ i, f i x') x
参数：bdd : forallᶠ y in 𝓝 x, BddAbove (range fun i => f i y)；h : forall i, LowerSe
micontinuousAt (f i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lowerSemicontinuousWithinAt_ciSup`：lowerSemicontinuousWithinAt_ciSup {f 
: ι -> α -> δ'} (bdd : forallᶠ y in 𝓝[s] x, BddAbove (range fun i => f i y)) (h 
: forall i, LowerSemico…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem lowerSemicontinuousAt_ciSup {f : ι → α → δ'}
    (bdd : ∀ᶠ y in 𝓝 x, BddAbove (range fun i => f i y)) (h : ∀ i, LowerSemicontinuousAt (f i) x) :
    LowerSemicontinuousAt (fun x' => ⨆ i, f i x') x := by
  simp_rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  rw [← nhdsWithin_univ] at bdd
  exact lowerSemicontinuousWithinAt_ciSup bdd h
/-
**lowerSemicontinuousAt_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuousAt_iSup {f : ι -> α -> δ} (h : forall i, LowerSemiconti
nuousAt (f i) x) : LowerSemicontinuousAt (fun x' => ⨆ i, f i x') x
参数：h : forall i, LowerSemicontinuousAt (f i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lowerSemicontinuousAt_ciSup`：lowerSemicontinuousAt_ciSup {f : ι -> α -> 
δ'} (bdd : forallᶠ y in 𝓝 x, BddAbove (range fun i => f i y)) (h : forall i, Low
erSemicontinuousA…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem lowerSemicontinuousAt_iSup {f : ι → α → δ} (h : ∀ i, LowerSemicontinuousAt (f i) x) :
    LowerSemicontinuousAt (fun x' => ⨆ i, f i x') x :=
  lowerSemicontinuousAt_ciSup (by simp) h
/-
**lowerSemicontinuousAt_biSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuousAt_biSup {p : ι -> Prop} {f : forall i, p i -> α -> δ} 
(h : forall i hi, LowerSemicontinuousAt (f i hi) x) : LowerSemicontinuousAt (fun
 x' => ⨆ (i) (hi), f i hi x') x
参数：h : forall i hi, LowerSemicontinuousAt (f i hi) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lowerSemicontinuousAt_iSup`：lowerSemicontinuousAt_iSup {f : ι -> α -> δ}
 (h : forall i, LowerSemicontinuousAt (f i) x) : LowerSemicontinuousAt (fun x' =
> ⨆ i, f i x') x
-/
theorem lowerSemicontinuousAt_biSup {p : ι → Prop} {f : ∀ i, p i → α → δ}
    (h : ∀ i hi, LowerSemicontinuousAt (f i hi) x) :
    LowerSemicontinuousAt (fun x' => ⨆ (i) (hi), f i hi x') x :=
  lowerSemicontinuousAt_iSup fun i => lowerSemicontinuousAt_iSup fun hi => h i hi
/-
**lowerSemicontinuousOn_ciSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuousOn_ciSup {f : ι -> α -> δ'} (bdd : forall x in s, BddAb
ove (range fun i => f i x)) (h : forall i, LowerSemicontinuousOn (f i) s) : Lowe
rSemicontinuousOn (fun x' => ⨆ i, f i x') s
参数：bdd : forall x in s, BddAbove (range fun i => f i x)；h : forall i, LowerSemic
ontinuousOn (f i) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lowerSemicontinuousWithinAt_ciSup`：lowerSemicontinuousWithinAt_ciSup {f 
: ι -> α -> δ'} (bdd : forallᶠ y in 𝓝[s] x, BddAbove (range fun i => f i y)) (h 
: forall i, LowerSemico…
· 使用定理 `eventually_nhdsWithin_of_forall`：eventually_nhdsWithin_of_forall {s : Se
t α} {a : α} {p : α -> Prop} (h : forall x in s, p x) : forallᶠ x in 𝓝[s] a, p x
-/
theorem lowerSemicontinuousOn_ciSup {f : ι → α → δ'}
    (bdd : ∀ x ∈ s, BddAbove (range fun i => f i x)) (h : ∀ i, LowerSemicontinuousOn (f i) s) :
    LowerSemicontinuousOn (fun x' => ⨆ i, f i x') s := fun x hx =>
  lowerSemicontinuousWithinAt_ciSup (eventually_nhdsWithin_of_forall bdd) fun i => h i x hx
/-
**lowerSemicontinuousOn_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuousOn_iSup {f : ι -> α -> δ} (h : forall i, LowerSemiconti
nuousOn (f i) s) : LowerSemicontinuousOn (fun x' => ⨆ i, f i x') s
参数：h : forall i, LowerSemicontinuousOn (f i) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lowerSemicontinuousOn_ciSup`：lowerSemicontinuousOn_ciSup {f : ι -> α -> 
δ'} (bdd : forall x in s, BddAbove (range fun i => f i x)) (h : forall i, LowerS
emicontinuousOn (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem lowerSemicontinuousOn_iSup {f : ι → α → δ} (h : ∀ i, LowerSemicontinuousOn (f i) s) :
    LowerSemicontinuousOn (fun x' => ⨆ i, f i x') s :=
  lowerSemicontinuousOn_ciSup (by simp) h
/-
**lowerSemicontinuousOn_biSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuousOn_biSup {p : ι -> Prop} {f : forall i, p i -> α -> δ} 
(h : forall i hi, LowerSemicontinuousOn (f i hi) s) : LowerSemicontinuousOn (fun
 x' => ⨆ (i) (hi), f i hi x') s
参数：h : forall i hi, LowerSemicontinuousOn (f i hi) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lowerSemicontinuousOn_iSup`：lowerSemicontinuousOn_iSup {f : ι -> α -> δ}
 (h : forall i, LowerSemicontinuousOn (f i) s) : LowerSemicontinuousOn (fun x' =
> ⨆ i, f i x') s
-/
theorem lowerSemicontinuousOn_biSup {p : ι → Prop} {f : ∀ i, p i → α → δ}
    (h : ∀ i hi, LowerSemicontinuousOn (f i hi) s) :
    LowerSemicontinuousOn (fun x' => ⨆ (i) (hi), f i hi x') s :=
  lowerSemicontinuousOn_iSup fun i => lowerSemicontinuousOn_iSup fun hi => h i hi
/-
**lowerSemicontinuous_ciSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuous_ciSup {f : ι -> α -> δ'} (bdd : forall x, BddAbove (ra
nge fun i => f i x)) (h : forall i, LowerSemicontinuous (f i)) : LowerSemicontin
uous fun x' => ⨆ i, f i x'
参数：bdd : forall x, BddAbove (range fun i => f i x)；h : forall i, LowerSemicontin
uous (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lowerSemicontinuousAt_ciSup`：lowerSemicontinuousAt_ciSup {f : ι -> α -> 
δ'} (bdd : forallᶠ y in 𝓝 x, BddAbove (range fun i => f i y)) (h : forall i, Low
erSemicontinuousA…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem lowerSemicontinuous_ciSup {f : ι → α → δ'} (bdd : ∀ x, BddAbove (range fun i => f i x))
    (h : ∀ i, LowerSemicontinuous (f i)) : LowerSemicontinuous fun x' => ⨆ i, f i x' := fun x =>
  lowerSemicontinuousAt_ciSup (Eventually.of_forall bdd) fun i => h i x
/-
**lowerSemicontinuous_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuous_iSup {f : ι -> α -> δ} (h : forall i, LowerSemicontinu
ous (f i)) : LowerSemicontinuous fun x' => ⨆ i, f i x'
参数：h : forall i, LowerSemicontinuous (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lowerSemicontinuous_ciSup`：lowerSemicontinuous_ciSup {f : ι -> α -> δ'} 
(bdd : forall x, BddAbove (range fun i => f i x)) (h : forall i, LowerSemicontin
uous (f i)) : L…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem lowerSemicontinuous_iSup {f : ι → α → δ} (h : ∀ i, LowerSemicontinuous (f i)) :
    LowerSemicontinuous fun x' => ⨆ i, f i x' :=
  lowerSemicontinuous_ciSup (by simp) h
/-
**lowerSemicontinuous_biSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuous_biSup {p : ι -> Prop} {f : forall i, p i -> α -> δ} (h
 : forall i hi, LowerSemicontinuous (f i hi)) : LowerSemicontinuous fun x' => ⨆ 
(i) (hi), f i hi x'
参数：h : forall i hi, LowerSemicontinuous (f i hi)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lowerSemicontinuous_iSup`：lowerSemicontinuous_iSup {f : ι -> α -> δ} (h 
: forall i, LowerSemicontinuous (f i)) : LowerSemicontinuous fun x' => ⨆ i, f i 
x'
-/
theorem lowerSemicontinuous_biSup {p : ι → Prop} {f : ∀ i, p i → α → δ}
    (h : ∀ i hi, LowerSemicontinuous (f i hi)) :
    LowerSemicontinuous fun x' => ⨆ (i) (hi), f i hi x' :=
  lowerSemicontinuous_iSup fun i => lowerSemicontinuous_iSup fun hi => h i hi

end

/-! #### Infinite sums -/


section

variable {ι : Type*}

/-
**lowerSemicontinuousWithinAt_tsum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuousWithinAt_tsum {f : ι -> α -> Real>=0∞} (h : forall i, L
owerSemicontinuousWithinAt (f i) s x) : LowerSemicontinuousWithinAt (fun x' => ∑
' i, f i x') s x
参数：h : forall i, LowerSemicontinuousWithinAt (f i) s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.tsum_eq_iSup_sum`：∀ {α : Type u_1} {f : α → ENNReal}, ∑' (a : α)
, f a = ⨆ s, ∑ a ∈ s, f a
· 使用定理 `lowerSemicontinuousWithinAt_iSup`：lowerSemicontinuousWithinAt_iSup {f : 
ι -> α -> δ} (h : forall i, LowerSemicontinuousWithinAt (f i) s x) : LowerSemico
ntinuousWithinAt (fun …
· 使用定理 `lowerSemicontinuousWithinAt_sum`：lowerSemicontinuousWithinAt_sum {f : ι 
-> α -> γ} {a : Finset ι} (ha : forall i in a, LowerSemicontinuousWithinAt (f i)
 s x) : LowerSemicont…
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
-/
theorem lowerSemicontinuousWithinAt_tsum {f : ι → α → ℝ≥0∞}
    (h : ∀ i, LowerSemicontinuousWithinAt (f i) s x) :
    LowerSemicontinuousWithinAt (fun x' => ∑' i, f i x') s x := by
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  refine lowerSemicontinuousWithinAt_iSup fun b => ?_
  exact lowerSemicontinuousWithinAt_sum fun i _hi => h i
/-
**lowerSemicontinuousAt_tsum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuousAt_tsum {f : ι -> α -> Real>=0∞} (h : forall i, LowerSe
micontinuousAt (f i) x) : LowerSemicontinuousAt (fun x' => ∑' i, f i x') x
参数：h : forall i, LowerSemicontinuousAt (f i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lowerSemicontinuousWithinAt_tsum`：lowerSemicontinuousWithinAt_tsum {f : 
ι -> α -> Real>=0∞} (h : forall i, LowerSemicontinuousWithinAt (f i) s x) : Lowe
rSemicontinuousWithinA…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem lowerSemicontinuousAt_tsum {f : ι → α → ℝ≥0∞} (h : ∀ i, LowerSemicontinuousAt (f i) x) :
    LowerSemicontinuousAt (fun x' => ∑' i, f i x') x := by
  simp_rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  exact lowerSemicontinuousWithinAt_tsum h
/-
**lowerSemicontinuousOn_tsum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuousOn_tsum {f : ι -> α -> Real>=0∞} (h : forall i, LowerSe
micontinuousOn (f i) s) : LowerSemicontinuousOn (fun x' => ∑' i, f i x') s
参数：h : forall i, LowerSemicontinuousOn (f i) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lowerSemicontinuousWithinAt_tsum`：lowerSemicontinuousWithinAt_tsum {f : 
ι -> α -> Real>=0∞} (h : forall i, LowerSemicontinuousWithinAt (f i) s x) : Lowe
rSemicontinuousWithinA…
-/
theorem lowerSemicontinuousOn_tsum {f : ι → α → ℝ≥0∞} (h : ∀ i, LowerSemicontinuousOn (f i) s) :
    LowerSemicontinuousOn (fun x' => ∑' i, f i x') s := fun x hx =>
  lowerSemicontinuousWithinAt_tsum fun i => h i x hx
/-
**lowerSemicontinuous_tsum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuous_tsum {f : ι -> α -> Real>=0∞} (h : forall i, LowerSemi
continuous (f i)) : LowerSemicontinuous fun x' => ∑' i, f i x'
参数：h : forall i, LowerSemicontinuous (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lowerSemicontinuousAt_tsum`：lowerSemicontinuousAt_tsum {f : ι -> α -> Re
al>=0∞} (h : forall i, LowerSemicontinuousAt (f i) x) : LowerSemicontinuousAt (f
un x' => ∑' i, f…
-/
theorem lowerSemicontinuous_tsum {f : ι → α → ℝ≥0∞} (h : ∀ i, LowerSemicontinuous (f i)) :
    LowerSemicontinuous fun x' => ∑' i, f i x' := fun x => lowerSemicontinuousAt_tsum fun i => h i x

end

/-!
### Upper semicontinuous functions
-/

/-! ### upper bounds -/

section

variable {α : Type*} [TopologicalSpace α] {β : Type*} [LinearOrder β] {f : α → β} {s : Set α}

/-- An upper semicontinuous function attains its upper bound on a nonempty compact set. -/
/-
**UpperSemicontinuousOn.exists_isMaxOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperSemicontinuousOn.exists_isMaxOn {s : Set α} (ne_s : s.Nonempty) (hs :
 IsCompact s) (hf : UpperSemicontinuousOn f s) : exists a in s, IsMaxOn f s a
参数：ne_s : s.Nonempty；hs : IsCompact s；hf : UpperSemicontinuousOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSemicontinuousOn.exists_isMinOn`：LowerSemicontinuousOn.exists_isMin
On {s : Set α} (ne_s : s.Nonempty) (hs : IsCompact s) (hf : LowerSemicontinuousO
n f s) : exists a in s, Is…

--- 原说明 ---
An upper semicontinuous function attains its upper bound on a nonempty compact s
et.
-/
theorem UpperSemicontinuousOn.exists_isMaxOn {s : Set α} (ne_s : s.Nonempty)
    (hs : IsCompact s) (hf : UpperSemicontinuousOn f s) :
    ∃ a ∈ s, IsMaxOn f s a :=
  LowerSemicontinuousOn.exists_isMinOn (β := βᵒᵈ) ne_s hs hf

/-- An upper semicontinuous function is bounded above on a compact set. -/
/-
**UpperSemicontinuousOn.bddAbove_of_isCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperSemicontinuousOn.bddAbove_of_isCompact [Nonempty β] {s : Set α} (hs :
 IsCompact s) (hf : UpperSemicontinuousOn f s) : BddAbove (f '' s)
参数：hs : IsCompact s；hf : UpperSemicontinuousOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSemicontinuousOn.bddBelow_of_isCompact`：LowerSemicontinuousOn.bddBe
low_of_isCompact [Nonempty β] {s : Set α} (hs : IsCompact s) (hf : LowerSemicont
inuousOn f s) : BddBelow (f '' s)
· 使用定理 `OrderDual.instNonempty`：∀ (α : Type u_2) [h : Nonempty α], Nonempty αᵒᵈ

--- 原说明 ---
An upper semicontinuous function is bounded above on a compact set.
-/
theorem UpperSemicontinuousOn.bddAbove_of_isCompact [Nonempty β] {s : Set α}
    (hs : IsCompact s) (hf : UpperSemicontinuousOn f s) : BddAbove (f '' s) :=
  LowerSemicontinuousOn.bddBelow_of_isCompact (β := βᵒᵈ) hs hf

end

/-! #### Indicators -/


section

variable [Zero β] [Preorder β]

/-
**IsOpen.upperSemicontinuous_indicator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.upperSemicontinuous_indicator (hs : IsOpen s) (hy : y <= 0) : Upper
Semicontinuous (indicator s fun _x => y)
参数：hs : IsOpen s；hy : y <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.lowerSemicontinuous_indicator`：IsOpen.lowerSemicontinuous_indicat
or (hs : IsOpen s) (hy : 0 <= y) : LowerSemicontinuous (indicator s fun _x => y)
-/
theorem IsOpen.upperSemicontinuous_indicator (hs : IsOpen s) (hy : y ≤ 0) :
    UpperSemicontinuous (indicator s fun _x => y) :=
  IsOpen.lowerSemicontinuous_indicator (β := βᵒᵈ) hs hy
/-
**IsOpen.upperSemicontinuousOn_indicator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.upperSemicontinuousOn_indicator (hs : IsOpen s) (hy : y <= 0) : Upp
erSemicontinuousOn (indicator s fun _x => y) t
参数：hs : IsOpen s；hy : y <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperSemicontinuous.upperSemicontinuousOn`：UpperSemicontinuous.upperSemi
continuousOn (h : UpperSemicontinuous f) (s : Set α) : UpperSemicontinuousOn f s
· 使用定理 `IsOpen.upperSemicontinuous_indicator`：IsOpen.upperSemicontinuous_indicat
or (hs : IsOpen s) (hy : y <= 0) : UpperSemicontinuous (indicator s fun _x => y)
-/
theorem IsOpen.upperSemicontinuousOn_indicator (hs : IsOpen s) (hy : y ≤ 0) :
    UpperSemicontinuousOn (indicator s fun _x => y) t :=
  (hs.upperSemicontinuous_indicator hy).upperSemicontinuousOn t
/-
**IsOpen.upperSemicontinuousAt_indicator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.upperSemicontinuousAt_indicator (hs : IsOpen s) (hy : y <= 0) : Upp
erSemicontinuousAt (indicator s fun _x => y) x
参数：hs : IsOpen s；hy : y <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperSemicontinuous.upperSemicontinuousAt`：UpperSemicontinuous.upperSemi
continuousAt (h : UpperSemicontinuous f) (x : α) : UpperSemicontinuousAt f x
· 使用定理 `IsOpen.upperSemicontinuous_indicator`：IsOpen.upperSemicontinuous_indicat
or (hs : IsOpen s) (hy : y <= 0) : UpperSemicontinuous (indicator s fun _x => y)
-/
theorem IsOpen.upperSemicontinuousAt_indicator (hs : IsOpen s) (hy : y ≤ 0) :
    UpperSemicontinuousAt (indicator s fun _x => y) x :=
  (hs.upperSemicontinuous_indicator hy).upperSemicontinuousAt x
/-
**IsOpen.upperSemicontinuousWithinAt_indicator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.upperSemicontinuousWithinAt_indicator (hs : IsOpen s) (hy : y <= 0)
 : UpperSemicontinuousWithinAt (indicator s fun _x => y) t x
参数：hs : IsOpen s；hy : y <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperSemicontinuous.upperSemicontinuousWithinAt`：UpperSemicontinuous.upp
erSemicontinuousWithinAt (h : UpperSemicontinuous f) (s : Set α) (x : α) : Upper
SemicontinuousWithinAt f s x
· 使用定理 `IsOpen.upperSemicontinuous_indicator`：IsOpen.upperSemicontinuous_indicat
or (hs : IsOpen s) (hy : y <= 0) : UpperSemicontinuous (indicator s fun _x => y)
-/
theorem IsOpen.upperSemicontinuousWithinAt_indicator (hs : IsOpen s) (hy : y ≤ 0) :
    UpperSemicontinuousWithinAt (indicator s fun _x => y) t x :=
  (hs.upperSemicontinuous_indicator hy).upperSemicontinuousWithinAt t x
/-
**IsClosed.upperSemicontinuous_indicator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.upperSemicontinuous_indicator (hs : IsClosed s) (hy : 0 <= y) : U
pperSemicontinuous (indicator s fun _x => y)
参数：hs : IsClosed s；hy : 0 <= y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.lowerSemicontinuous_indicator`：IsClosed.lowerSemicontinuous_ind
icator (hs : IsClosed s) (hy : y <= 0) : LowerSemicontinuous (indicator s fun _x
 => y)
-/
theorem IsClosed.upperSemicontinuous_indicator (hs : IsClosed s) (hy : 0 ≤ y) :
    UpperSemicontinuous (indicator s fun _x => y) :=
  IsClosed.lowerSemicontinuous_indicator (β := βᵒᵈ) hs hy
/-
**IsClosed.upperSemicontinuousOn_indicator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.upperSemicontinuousOn_indicator (hs : IsClosed s) (hy : 0 <= y) :
 UpperSemicontinuousOn (indicator s fun _x => y) t
参数：hs : IsClosed s；hy : 0 <= y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperSemicontinuous.upperSemicontinuousOn`：UpperSemicontinuous.upperSemi
continuousOn (h : UpperSemicontinuous f) (s : Set α) : UpperSemicontinuousOn f s
· 使用定理 `IsClosed.upperSemicontinuous_indicator`：IsClosed.upperSemicontinuous_ind
icator (hs : IsClosed s) (hy : 0 <= y) : UpperSemicontinuous (indicator s fun _x
 => y)
-/
theorem IsClosed.upperSemicontinuousOn_indicator (hs : IsClosed s) (hy : 0 ≤ y) :
    UpperSemicontinuousOn (indicator s fun _x => y) t :=
  (hs.upperSemicontinuous_indicator hy).upperSemicontinuousOn t
/-
**IsClosed.upperSemicontinuousAt_indicator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.upperSemicontinuousAt_indicator (hs : IsClosed s) (hy : 0 <= y) :
 UpperSemicontinuousAt (indicator s fun _x => y) x
参数：hs : IsClosed s；hy : 0 <= y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperSemicontinuous.upperSemicontinuousAt`：UpperSemicontinuous.upperSemi
continuousAt (h : UpperSemicontinuous f) (x : α) : UpperSemicontinuousAt f x
· 使用定理 `IsClosed.upperSemicontinuous_indicator`：IsClosed.upperSemicontinuous_ind
icator (hs : IsClosed s) (hy : 0 <= y) : UpperSemicontinuous (indicator s fun _x
 => y)
-/
theorem IsClosed.upperSemicontinuousAt_indicator (hs : IsClosed s) (hy : 0 ≤ y) :
    UpperSemicontinuousAt (indicator s fun _x => y) x :=
  (hs.upperSemicontinuous_indicator hy).upperSemicontinuousAt x
/-
**IsClosed.upperSemicontinuousWithinAt_indicator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsClosed.upperSemicontinuousWithinAt_indicator (hs : IsClosed s) (hy : 0 <
= y) : UpperSemicontinuousWithinAt (indicator s fun _x => y) t x
参数：hs : IsClosed s；hy : 0 <= y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperSemicontinuous.upperSemicontinuousWithinAt`：UpperSemicontinuous.upp
erSemicontinuousWithinAt (h : UpperSemicontinuous f) (s : Set α) (x : α) : Upper
SemicontinuousWithinAt f s x
· 使用定理 `IsClosed.upperSemicontinuous_indicator`：IsClosed.upperSemicontinuous_ind
icator (hs : IsClosed s) (hy : 0 <= y) : UpperSemicontinuous (indicator s fun _x
 => y)
-/
theorem IsClosed.upperSemicontinuousWithinAt_indicator (hs : IsClosed s) (hy : 0 ≤ y) :
    UpperSemicontinuousWithinAt (indicator s fun _x => y) t x :=
  (hs.upperSemicontinuous_indicator hy).upperSemicontinuousWithinAt t x

end

/-! #### Relationship with continuity -/

section

variable [Preorder β]

/-
**upperSemicontinuous_iff_isOpen_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperSemicontinuous_iff_isOpen_preimage : UpperSemicontinuous f ↔ forall y
, IsOpen (f ⁻¹' Iio y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
-/
theorem upperSemicontinuous_iff_isOpen_preimage :
    UpperSemicontinuous f ↔ ∀ y, IsOpen (f ⁻¹' Iio y) :=
  ⟨fun H y => isOpen_iff_mem_nhds.2 fun x hx => H x y hx, fun H _x y y_lt =>
    IsOpen.mem_nhds (H y) y_lt⟩
/-
**UpperSemicontinuous.isOpen_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperSemicontinuous.isOpen_preimage (hf : UpperSemicontinuous f) (y : β) :
 IsOpen (f ⁻¹' Iio y)
参数：hf : UpperSemicontinuous f；y : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `upperSemicontinuous_iff_isOpen_preimage`：upperSemicontinuous_iff_isOpen_
preimage : UpperSemicontinuous f ↔ forall y, IsOpen (f ⁻¹' Iio y)
-/
theorem UpperSemicontinuous.isOpen_preimage (hf : UpperSemicontinuous f) (y : β) :
    IsOpen (f ⁻¹' Iio y) :=
  upperSemicontinuous_iff_isOpen_preimage.1 hf y

end
section

variable {γ : Type*} [LinearOrder γ]

/-
**upperSemicontinuous_iff_isClosed_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperSemicontinuous_iff_isClosed_preimage {f : α -> γ} : UpperSemicontinuo
us f ↔ forall y, IsClosed (f ⁻¹' Ici y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `upperSemicontinuous_iff_isOpen_preimage`：upperSemicontinuous_iff_isOpen_
preimage : UpperSemicontinuous f ↔ forall y, IsOpen (f ⁻¹' Iio y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Set.compl_Ici`：∀ {α : Type u_1} [inst : LinearOrder α] {a : α}, (Set.Ici
 a)ᶜ = Set.Iio a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem upperSemicontinuous_iff_isClosed_preimage {f : α → γ} :
    UpperSemicontinuous f ↔ ∀ y, IsClosed (f ⁻¹' Ici y) := by
  rw [upperSemicontinuous_iff_isOpen_preimage]
  simp only [← isOpen_compl_iff, ← preimage_compl, compl_Ici]
/-
**UpperSemicontinuous.isClosed_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperSemicontinuous.isClosed_preimage {f : α -> γ} (hf : UpperSemicontinuo
us f) (y : γ) : IsClosed (f ⁻¹' Ici y)
参数：hf : UpperSemicontinuous f；y : γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `upperSemicontinuous_iff_isClosed_preimage`：upperSemicontinuous_iff_isClo
sed_preimage {f : α -> γ} : UpperSemicontinuous f ↔ forall y, IsClosed (f ⁻¹' Ic
i y)
-/
theorem UpperSemicontinuous.isClosed_preimage {f : α → γ} (hf : UpperSemicontinuous f) (y : γ) :
    IsClosed (f ⁻¹' Ici y) :=
  upperSemicontinuous_iff_isClosed_preimage.1 hf y

variable [TopologicalSpace γ] [OrderTopology γ]
/-
**ContinuousWithinAt.upperSemicontinuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.upperSemicontinuousWithinAt {f : α -> γ} (h : Continuou
sWithinAt f s x) : UpperSemicontinuousWithinAt f s x
参数：h : ContinuousWithinAt f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iio_mem_nhds`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Linea
rOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Iio a ∈ nhds b
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
-/
theorem ContinuousWithinAt.upperSemicontinuousWithinAt {f : α → γ} (h : ContinuousWithinAt f s x) :
    UpperSemicontinuousWithinAt f s x := fun _y hy => h (Iio_mem_nhds hy)
/-
**ContinuousAt.upperSemicontinuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.upperSemicontinuousAt {f : α -> γ} (h : ContinuousAt f x) : U
pperSemicontinuousAt f x
参数：h : ContinuousAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iio_mem_nhds`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Linea
rOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Iio a ∈ nhds b
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
-/
theorem ContinuousAt.upperSemicontinuousAt {f : α → γ} (h : ContinuousAt f x) :
    UpperSemicontinuousAt f x := fun _y hy => h (Iio_mem_nhds hy)
/-
**ContinuousOn.upperSemicontinuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.upperSemicontinuousOn {f : α -> γ} (h : ContinuousOn f s) : U
pperSemicontinuousOn f s
参数：h : ContinuousOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.upperSemicontinuousWithinAt`：ContinuousWithinAt.upper
SemicontinuousWithinAt {f : α -> γ} (h : ContinuousWithinAt f s x) : UpperSemico
ntinuousWithinAt f s x
-/
theorem ContinuousOn.upperSemicontinuousOn {f : α → γ} (h : ContinuousOn f s) :
    UpperSemicontinuousOn f s := fun x hx => (h x hx).upperSemicontinuousWithinAt
/-
**Continuous.upperSemicontinuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.upperSemicontinuous {f : α -> γ} (h : Continuous f) : UpperSemi
continuous f
参数：h : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.upperSemicontinuousAt`：ContinuousAt.upperSemicontinuousAt {
f : α -> γ} (h : ContinuousAt f x) : UpperSemicontinuousAt f x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
theorem Continuous.upperSemicontinuous {f : α → γ} (h : Continuous f) : UpperSemicontinuous f :=
  fun _x => h.continuousAt.upperSemicontinuousAt

end

/-! #### Equivalent definitions -/

section

variable {γ : Type*} [CompleteLinearOrder γ]

/-
**upperSemicontinuousWithinAt_iff_limsup_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperSemicontinuousWithinAt_iff_limsup_le {f : α -> γ} : UpperSemicontinuo
usWithinAt f s x ↔ limsup f (𝓝[s] x) <= f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lowerSemicontinuousWithinAt_iff_le_liminf`：lowerSemicontinuousWithinAt_i
ff_le_liminf {f : α -> γ} : LowerSemicontinuousWithinAt f s x ↔ f x <= liminf f 
(𝓝[s] x)
-/
theorem upperSemicontinuousWithinAt_iff_limsup_le {f : α → γ} :
    UpperSemicontinuousWithinAt f s x ↔ limsup f (𝓝[s] x) ≤ f x :=
  lowerSemicontinuousWithinAt_iff_le_liminf (γ := γᵒᵈ)

alias ⟨UpperSemicontinuousWithinAt.limsup_le, _⟩ := upperSemicontinuousWithinAt_iff_limsup_le
/-
**upperSemicontinuousAt_iff_limsup_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperSemicontinuousAt_iff_limsup_le {f : α -> γ} : UpperSemicontinuousAt f
 x ↔ limsup f (𝓝 x) <= f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lowerSemicontinuousAt_iff_le_liminf`：lowerSemicontinuousAt_iff_le_liminf
 {f : α -> γ} : LowerSemicontinuousAt f x ↔ f x <= liminf f (𝓝 x)
-/
theorem upperSemicontinuousAt_iff_limsup_le {f : α → γ} :
    UpperSemicontinuousAt f x ↔ limsup f (𝓝 x) ≤ f x :=
  lowerSemicontinuousAt_iff_le_liminf (γ := γᵒᵈ)

alias ⟨UpperSemicontinuousAt.limsup_le, _⟩ := upperSemicontinuousAt_iff_limsup_le
/-
**upperSemicontinuous_iff_limsup_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperSemicontinuous_iff_limsup_le {f : α -> γ} : UpperSemicontinuous f ↔ f
orall x, limsup f (𝓝 x) <= f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lowerSemicontinuous_iff_le_liminf`：lowerSemicontinuous_iff_le_liminf {f 
: α -> γ} : LowerSemicontinuous f ↔ forall x, f x <= liminf f (𝓝 x)
-/
theorem upperSemicontinuous_iff_limsup_le {f : α → γ} :
    UpperSemicontinuous f ↔ ∀ x, limsup f (𝓝 x) ≤ f x :=
  lowerSemicontinuous_iff_le_liminf (γ := γᵒᵈ)

alias ⟨UpperSemicontinuous.limsup_le, _⟩ := upperSemicontinuous_iff_limsup_le
/-
**upperSemicontinuousOn_iff_limsup_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperSemicontinuousOn_iff_limsup_le {f : α -> γ} : UpperSemicontinuousOn f
 s ↔ forall x in s, limsup f (𝓝[s] x) <= f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lowerSemicontinuousOn_iff_le_liminf`：lowerSemicontinuousOn_iff_le_liminf
 {f : α -> γ} : LowerSemicontinuousOn f s ↔ forall x in s, f x <= liminf f (𝓝[s]
 x)
-/
theorem upperSemicontinuousOn_iff_limsup_le {f : α → γ} :
    UpperSemicontinuousOn f s ↔ ∀ x ∈ s, limsup f (𝓝[s] x) ≤ f x :=
  lowerSemicontinuousOn_iff_le_liminf (γ := γᵒᵈ)

alias ⟨UpperSemicontinuousOn.limsup_le, _⟩ := upperSemicontinuousOn_iff_limsup_le

end

section

variable {γ : Type*} [LinearOrder γ]

/-- The overlevel sets of an upper semicontinuous function on a compact set are compact. -/
/-
**UpperSemicontinuousOn.isCompact_inter_preimage_Ici** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：UpperSemicontinuousOn.isCompact_inter_preimage_Ici {f : α -> γ} (hfs : Upp
erSemicontinuousOn f s) (ks : IsCompact s) (c : γ) : IsCompact (s inter f ⁻¹' Ic
i c)
参数：hfs : UpperSemicontinuousOn f s；ks : IsCompact s；c : γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSemicontinuousOn.isCompact_inter_preimage_Iic`：LowerSemicontinuousO
n.isCompact_inter_preimage_Iic {f : α -> γ} (hfs : LowerSemicontinuousOn f s) (k
s : IsCompact s) (c : γ) : IsCompact (s …

--- 原说明 ---
The overlevel sets of an upper semicontinuous function on a compact set are comp
act.
-/
theorem UpperSemicontinuousOn.isCompact_inter_preimage_Ici {f : α → γ}
    (hfs : UpperSemicontinuousOn f s) (ks : IsCompact s) (c : γ) :
    IsCompact (s ∩ f ⁻¹' Ici c) :=
  LowerSemicontinuousOn.isCompact_inter_preimage_Iic (γ := γᵒᵈ) hfs ks c

open scoped Set.Notation in
/-- An intersection of overlevel sets of a lower semicontinuous function
on a compact set is empty if and only if a finite sub-intersection is already empty. -/
/-
**UpperSemicontinuousOn.inter_biInter_preimage_Ici_eq_empty_iff_exists_finset** 
是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperSemicontinuousOn.inter_biInter_preimage_Ici_eq_empty_iff_exists_finse
t {ι : Type*} {f : ι -> α -> γ} (ks : IsCompact s) {I : Set ι} {c : γ} (hfi : fo
rall i in I, UpperSemicontinuousOn (f i) s) : s inter ⋂ i in I, (f i) ⁻¹' Ici c 
= ∅ ↔ exists u : Finset I, forall x in s, exists i in u, f i x < c
参数：ks : IsCompact s；hfi : forall i in I, UpperSemicontinuousOn (f i) s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSemicontinuousOn.inter_biInter_preimage_Iic_eq_empty_iff_exists_fin
set`：LowerSemicontinuousOn.inter_biInter_preimage_Iic_eq_empty_iff_exists_finset
 {ι : Type*} {f : ι -> α -> γ} (ks : IsCompact s) {I : Set ι} {c …

--- 原说明 ---
An intersection of overlevel sets of a lower semicontinuous function
on a compact set is empty if and only if a finite sub-intersection is already em
pty.
-/
theorem UpperSemicontinuousOn.inter_biInter_preimage_Ici_eq_empty_iff_exists_finset
    {ι : Type*} {f : ι → α → γ}
    (ks : IsCompact s) {I : Set ι} {c : γ} (hfi : ∀ i ∈ I, UpperSemicontinuousOn (f i) s) :
    s ∩ ⋂ i ∈ I, (f i) ⁻¹' Ici c = ∅ ↔ ∃ u : Finset I, ∀ x ∈ s, ∃ i ∈ u, f i x < c :=
  LowerSemicontinuousOn.inter_biInter_preimage_Iic_eq_empty_iff_exists_finset ks hfi (γ := γᵒᵈ)

variable [TopologicalSpace γ] [ClosedIicTopology γ]
/-
**upperSemicontinuousOn_iff_isClosed_hypograph** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperSemicontinuousOn_iff_isClosed_hypograph {f : α -> γ} (hs : IsClosed s
) : UpperSemicontinuousOn f s ↔ IsClosed {p : α × γ | p.1 in s ∧ p.2 <= f p.1}
参数：hs : IsClosed s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lowerSemicontinuousOn_iff_isClosed_epigraph`：lowerSemicontinuousOn_iff_i
sClosed_epigraph {f : α -> γ} {s : Set α} (hs : IsClosed s) : LowerSemicontinuou
sOn f s ↔ IsClosed {p : α × γ | p…
· 使用定理 `instClosedIciTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : Preorder α] [ClosedIicTopology α], ClosedIciTopology αᵒᵈ
-/
theorem upperSemicontinuousOn_iff_isClosed_hypograph {f : α → γ} (hs : IsClosed s) :
    UpperSemicontinuousOn f s ↔ IsClosed {p : α × γ | p.1 ∈ s ∧ p.2 ≤ f p.1} :=
  lowerSemicontinuousOn_iff_isClosed_epigraph hs (γ := γᵒᵈ)
/-
**upperSemicontinuous_iff_IsClosed_hypograph** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperSemicontinuous_iff_IsClosed_hypograph {f : α -> γ} : UpperSemicontinu
ous f ↔ IsClosed {p : α × γ | p.2 <= f p.1}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lowerSemicontinuous_iff_isClosed_epigraph`：lowerSemicontinuous_iff_isClo
sed_epigraph {f : α -> γ} : LowerSemicontinuous f ↔ IsClosed {p : α × γ | f p.1 
<= p.2}
· 使用定理 `instClosedIciTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : Preorder α] [ClosedIicTopology α], ClosedIciTopology αᵒᵈ
-/
theorem upperSemicontinuous_iff_IsClosed_hypograph {f : α → γ} :
    UpperSemicontinuous f ↔ IsClosed {p : α × γ | p.2 ≤ f p.1} :=
  lowerSemicontinuous_iff_isClosed_epigraph (γ := γᵒᵈ)

alias ⟨UpperSemicontinuous.IsClosed_hypograph, _⟩ := upperSemicontinuous_iff_IsClosed_hypograph

end

/-! ### Composition -/

section

variable {α : Type*} [TopologicalSpace α]
variable {β : Type*}
variable {γ : Type*} [TopologicalSpace γ]
variable {f : α → β} {g : γ → α} {s : Set α} {a : α} {c : γ} {t : Set γ}

/-
**upperSemicontinuousOn_iff_preimage_Iio** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperSemicontinuousOn_iff_preimage_Iio [Preorder β] : UpperSemicontinuousO
n f s ↔ forall b, exists u : Set α, IsOpen u ∧ s inter f ⁻¹' Set.Iio b = s inter
 u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lowerSemicontinuousOn_iff_preimage_Ioi`：lowerSemicontinuousOn_iff_preima
ge_Ioi : LowerSemicontinuousOn f s ↔ forall b, exists u, IsOpen u ∧ s inter f ⁻¹
' Set.Ioi b = s inter u
-/
theorem upperSemicontinuousOn_iff_preimage_Iio [Preorder β] :
    UpperSemicontinuousOn f s ↔ ∀ b, ∃ u : Set α, IsOpen u ∧ s ∩ f ⁻¹' Set.Iio b = s ∩ u :=
  lowerSemicontinuousOn_iff_preimage_Ioi (β := βᵒᵈ)
/-
**upperSemicontinuousOn_iff_preimage_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperSemicontinuousOn_iff_preimage_Ici [LinearOrder β] : UpperSemicontinuo
usOn f s ↔ forall b, exists v : Set α, IsClosed v ∧ s inter f ⁻¹' Set.Ici b = s 
inter v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lowerSemicontinuousOn_iff_preimage_Iic`：lowerSemicontinuousOn_iff_preima
ge_Iic {f : α -> γ} : LowerSemicontinuousOn f s ↔ forall b, exists v, IsClosed v
 ∧ s inter f ⁻¹' Set.Iic b =…
-/
theorem upperSemicontinuousOn_iff_preimage_Ici [LinearOrder β] :
    UpperSemicontinuousOn f s ↔ ∀ b, ∃ v : Set α, IsClosed v ∧ s ∩ f ⁻¹' Set.Ici b = s ∩ v :=
  lowerSemicontinuousOn_iff_preimage_Iic (γ := βᵒᵈ)

variable [PartialOrder β] [CommGroup β] [IsOrderedMonoid β]

@[to_additive (attr := simp)]
/-
**lowerSemicontinuousWithinAt_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuousWithinAt_inv_iff : LowerSemicontinuousWithinAt f⁻¹ s a 
↔ UpperSemicontinuousWithinAt f s a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `lowerSemicontinuousWithinAt_iff`：lowerSemicontinuousWithinAt_iff {f : α 
-> β} {s : Set α} {x : α} : LowerSemicontinuousWithinAt f s x ↔ forall y, y < f 
x -> forallᶠ x' in 𝓝[…
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `inv_surjective`：inv_surjective : Function.Surjective (Inv.inv : G -> G)
· 使用引理 `upperSemicontinuousWithinAt_iff`：upperSemicontinuousWithinAt_iff {f : α 
-> β} {s : Set α} {x : α} : UpperSemicontinuousWithinAt f s x ↔ forall y, f x < 
y -> forallᶠ x' in 𝓝[…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLT`：∀ {α : Type u_1} [inst : CommM
onoid α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], MulLeftReflectLT α
· 使用定理 `IsOrderedMonoid.toIsOrderedCancelMonoid`：∀ {α : Type u} [inst : CommGrou
p α] [inst_1 : Preorder α] [IsOrderedMonoid α], IsOrderedCancelMonoid α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lowerSemicontinuousWithinAt_inv_iff :
    LowerSemicontinuousWithinAt f⁻¹ s a ↔ UpperSemicontinuousWithinAt f s a := by
  rw [lowerSemicontinuousWithinAt_iff, inv_surjective.forall, upperSemicontinuousWithinAt_iff]
  simp

@[to_additive]
alias ⟨_, UpperSemicontinuousWithinAt.inv⟩ := lowerSemicontinuousWithinAt_inv_iff

@[to_additive (attr := simp)]
/-
**upperSemicontinuousWithinAt_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperSemicontinuousWithinAt_inv_iff : UpperSemicontinuousWithinAt f⁻¹ s a 
↔ LowerSemicontinuousWithinAt f s a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem upperSemicontinuousWithinAt_inv_iff :
    UpperSemicontinuousWithinAt f⁻¹ s a ↔ LowerSemicontinuousWithinAt f s a := by
  simp [← lowerSemicontinuousWithinAt_inv_iff]

@[to_additive]
alias ⟨_, LowerSemicontinuousWithinAt.inv⟩ := upperSemicontinuousWithinAt_inv_iff

@[to_additive (attr := simp)]
/-
**lowerSemicontinuouAt_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuouAt_inv_iff : LowerSemicontinuousAt f⁻¹ a ↔ UpperSemicont
inuousAt f a
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
theorem lowerSemicontinuouAt_inv_iff :
    LowerSemicontinuousAt f⁻¹ a ↔ UpperSemicontinuousAt f a := by
  simp [← lowerSemicontinuousWithinAt_univ_iff, ← upperSemicontinuousWithinAt_univ_iff]

@[to_additive]
alias ⟨_, UpperSemicontinuousAt.inv⟩ := lowerSemicontinuouAt_inv_iff

@[to_additive (attr := simp)]
/-
**upperSemicontinuousAt_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperSemicontinuousAt_inv_iff : UpperSemicontinuousAt f⁻¹ a ↔ LowerSemicon
tinuousAt f a
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
theorem upperSemicontinuousAt_inv_iff :
    UpperSemicontinuousAt f⁻¹ a ↔ LowerSemicontinuousAt f a := by
  simp [← lowerSemicontinuousWithinAt_univ_iff, ← upperSemicontinuousWithinAt_univ_iff]

@[to_additive]
alias ⟨_, LowerSemicontinuousAt.inv⟩ := upperSemicontinuousAt_inv_iff

@[to_additive (attr := simp)]
/-
**lowerSemicontinuousOn_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuousOn_inv_iff : LowerSemicontinuousOn f⁻¹ s ↔ UpperSemicon
tinuousOn f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lowerSemicontinuousOn_inv_iff :
    LowerSemicontinuousOn f⁻¹ s ↔ UpperSemicontinuousOn f s := by
  simp [lowerSemicontinuousOn_iff, upperSemicontinuousOn_iff]

@[to_additive]
alias ⟨_, UpperSemicontinuousOn.inv⟩ := lowerSemicontinuousOn_inv_iff

@[to_additive (attr := simp)]
/-
**upperSemicontinuousOn_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperSemicontinuousOn_inv_iff : UpperSemicontinuousOn f⁻¹ s ↔ LowerSemicon
tinuousOn f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem upperSemicontinuousOn_inv_iff :
    UpperSemicontinuousOn f⁻¹ s ↔ LowerSemicontinuousOn f s := by
  simp [← lowerSemicontinuousOn_inv_iff]

@[to_additive]
alias ⟨_, LowerSemicontinuousOn.inv⟩ := upperSemicontinuousOn_inv_iff

@[to_additive (attr := simp)]
/-
**lowerSemiContinuous_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemiContinuous_inv_iff : LowerSemicontinuous f⁻¹ ↔ UpperSemicontinuou
s f
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
theorem lowerSemiContinuous_inv_iff :
    LowerSemicontinuous f⁻¹ ↔ UpperSemicontinuous f := by
  simp [← upperSemicontinuousOn_univ_iff, ← lowerSemicontinuousOn_univ_iff]

@[to_additive]
alias ⟨_, UpperSemicontinuous.inv⟩ := lowerSemiContinuous_inv_iff

@[to_additive (attr := simp)]
/-
**upperSemiContinuous_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperSemiContinuous_inv_iff : UpperSemicontinuous f⁻¹ ↔ LowerSemicontinuou
s f
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
theorem upperSemiContinuous_inv_iff :
    UpperSemicontinuous f⁻¹ ↔ LowerSemicontinuous f := by
  simp [← upperSemicontinuousOn_univ_iff, ← lowerSemicontinuousOn_univ_iff]

@[to_additive]
alias ⟨_, LowerSemicontinuous.inv⟩ := upperSemiContinuous_inv_iff

end

section

variable {γ : Type*} [LinearOrder γ] [TopologicalSpace γ] [OrderTopology γ]
variable {δ : Type*} [LinearOrder δ] [TopologicalSpace δ] [OrderTopology δ]
variable {ι : Type*} [TopologicalSpace ι]

/-
**ContinuousAt.comp_upperSemicontinuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.comp_upperSemicontinuousWithinAt {g : γ -> δ} {f : α -> γ} (h
g : ContinuousAt g (f x)) (hf : UpperSemicontinuousWithinAt f s x) (gmon : Monot
one g) : UpperSemicontinuousWithinAt (g ∘ f) s x
参数：hg : ContinuousAt g (f x)；hf : UpperSemicontinuousWithinAt f s x；gmon : Monot
one g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp_lowerSemicontinuousWithinAt`：ContinuousAt.comp_lowerSe
micontinuousWithinAt {g : γ -> δ} {f : α -> γ} (hg : ContinuousAt g (f x)) (hf :
 LowerSemicontinuousWithinAt f s x)…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `Monotone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Monotone f → Monotone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…
-/
theorem ContinuousAt.comp_upperSemicontinuousWithinAt {g : γ → δ} {f : α → γ}
    (hg : ContinuousAt g (f x)) (hf : UpperSemicontinuousWithinAt f s x) (gmon : Monotone g) :
    UpperSemicontinuousWithinAt (g ∘ f) s x :=
  ContinuousAt.comp_lowerSemicontinuousWithinAt (γ := γᵒᵈ) (δ := δᵒᵈ) hg hf gmon.dual
/-
**ContinuousAt.comp_upperSemicontinuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.comp_upperSemicontinuousAt {g : γ -> δ} {f : α -> γ} (hg : Co
ntinuousAt g (f x)) (hf : UpperSemicontinuousAt f x) (gmon : Monotone g) : Upper
SemicontinuousAt (g ∘ f) x
参数：hg : ContinuousAt g (f x)；hf : UpperSemicontinuousAt f x；gmon : Monotone g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp_lowerSemicontinuousAt`：ContinuousAt.comp_lowerSemicont
inuousAt {g : γ -> δ} {f : α -> γ} (hg : ContinuousAt g (f x)) (hf : LowerSemico
ntinuousAt f x) (gmon : Monot…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `Monotone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Monotone f → Monotone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…
-/
theorem ContinuousAt.comp_upperSemicontinuousAt {g : γ → δ} {f : α → γ} (hg : ContinuousAt g (f x))
    (hf : UpperSemicontinuousAt f x) (gmon : Monotone g) : UpperSemicontinuousAt (g ∘ f) x :=
  ContinuousAt.comp_lowerSemicontinuousAt (γ := γᵒᵈ) (δ := δᵒᵈ) hg hf gmon.dual
/-
**Continuous.comp_upperSemicontinuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.comp_upperSemicontinuousOn {g : γ -> δ} {f : α -> γ} (hg : Cont
inuous g) (hf : UpperSemicontinuousOn f s) (gmon : Monotone g) : UpperSemicontin
uousOn (g ∘ f) s
参数：hg : Continuous g；hf : UpperSemicontinuousOn f s；gmon : Monotone g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp_upperSemicontinuousWithinAt`：ContinuousAt.comp_upperSe
micontinuousWithinAt {g : γ -> δ} {f : α -> γ} (hg : ContinuousAt g (f x)) (hf :
 UpperSemicontinuousWithinAt f s x)…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
theorem Continuous.comp_upperSemicontinuousOn {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : UpperSemicontinuousOn f s) (gmon : Monotone g) : UpperSemicontinuousOn (g ∘ f) s :=
  fun x hx => hg.continuousAt.comp_upperSemicontinuousWithinAt (hf x hx) gmon
/-
**Continuous.comp_upperSemicontinuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.comp_upperSemicontinuous {g : γ -> δ} {f : α -> γ} (hg : Contin
uous g) (hf : UpperSemicontinuous f) (gmon : Monotone g) : UpperSemicontinuous (
g ∘ f)
参数：hg : Continuous g；hf : UpperSemicontinuous f；gmon : Monotone g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp_upperSemicontinuousAt`：ContinuousAt.comp_upperSemicont
inuousAt {g : γ -> δ} {f : α -> γ} (hg : ContinuousAt g (f x)) (hf : UpperSemico
ntinuousAt f x) (gmon : Monot…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
theorem Continuous.comp_upperSemicontinuous {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : UpperSemicontinuous f) (gmon : Monotone g) : UpperSemicontinuous (g ∘ f) := fun x =>
  hg.continuousAt.comp_upperSemicontinuousAt (hf x) gmon
/-
**ContinuousAt.comp_upperSemicontinuousWithinAt_antitone** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：ContinuousAt.comp_upperSemicontinuousWithinAt_antitone {g : γ -> δ} {f : α
 -> γ} (hg : ContinuousAt g (f x)) (hf : UpperSemicontinuousWithinAt f s x) (gmo
n : Antitone g) : LowerSemicontinuousWithinAt (g ∘ f) s x
参数：hg : ContinuousAt g (f x)；hf : UpperSemicontinuousWithinAt f s x；gmon : Antit
one g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp_upperSemicontinuousWithinAt`：ContinuousAt.comp_upperSe
micontinuousWithinAt {g : γ -> δ} {f : α -> γ} (hg : ContinuousAt g (f x)) (hf :
 UpperSemicontinuousWithinAt f s x)…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
theorem ContinuousAt.comp_upperSemicontinuousWithinAt_antitone {g : γ → δ} {f : α → γ}
    (hg : ContinuousAt g (f x)) (hf : UpperSemicontinuousWithinAt f s x) (gmon : Antitone g) :
    LowerSemicontinuousWithinAt (g ∘ f) s x :=
  ContinuousAt.comp_upperSemicontinuousWithinAt (δ := δᵒᵈ) hg hf gmon
/-
**ContinuousAt.comp_upperSemicontinuousAt_antitone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.comp_upperSemicontinuousAt_antitone {g : γ -> δ} {f : α -> γ}
 (hg : ContinuousAt g (f x)) (hf : UpperSemicontinuousAt f x) (gmon : Antitone g
) : LowerSemicontinuousAt (g ∘ f) x
参数：hg : ContinuousAt g (f x)；hf : UpperSemicontinuousAt f x；gmon : Antitone g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp_upperSemicontinuousAt`：ContinuousAt.comp_upperSemicont
inuousAt {g : γ -> δ} {f : α -> γ} (hg : ContinuousAt g (f x)) (hf : UpperSemico
ntinuousAt f x) (gmon : Monot…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
theorem ContinuousAt.comp_upperSemicontinuousAt_antitone {g : γ → δ} {f : α → γ}
    (hg : ContinuousAt g (f x)) (hf : UpperSemicontinuousAt f x) (gmon : Antitone g) :
    LowerSemicontinuousAt (g ∘ f) x :=
  ContinuousAt.comp_upperSemicontinuousAt (δ := δᵒᵈ) hg hf gmon
/-
**Continuous.comp_upperSemicontinuousOn_antitone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.comp_upperSemicontinuousOn_antitone {g : γ -> δ} {f : α -> γ} (
hg : Continuous g) (hf : UpperSemicontinuousOn f s) (gmon : Antitone g) : LowerS
emicontinuousOn (g ∘ f) s
参数：hg : Continuous g；hf : UpperSemicontinuousOn f s；gmon : Antitone g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp_upperSemicontinuousWithinAt_antitone`：ContinuousAt.com
p_upperSemicontinuousWithinAt_antitone {g : γ -> δ} {f : α -> γ} (hg : Continuou
sAt g (f x)) (hf : UpperSemicontinuousWithin…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
theorem Continuous.comp_upperSemicontinuousOn_antitone {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : UpperSemicontinuousOn f s) (gmon : Antitone g) : LowerSemicontinuousOn (g ∘ f) s :=
  fun x hx => hg.continuousAt.comp_upperSemicontinuousWithinAt_antitone (hf x hx) gmon
/-
**Continuous.comp_upperSemicontinuous_antitone** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.comp_upperSemicontinuous_antitone {g : γ -> δ} {f : α -> γ} (hg
 : Continuous g) (hf : UpperSemicontinuous f) (gmon : Antitone g) : LowerSemicon
tinuous (g ∘ f)
参数：hg : Continuous g；hf : UpperSemicontinuous f；gmon : Antitone g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp_upperSemicontinuousAt_antitone`：ContinuousAt.comp_uppe
rSemicontinuousAt_antitone {g : γ -> δ} {f : α -> γ} (hg : ContinuousAt g (f x))
 (hf : UpperSemicontinuousAt f x) (gmo…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
theorem Continuous.comp_upperSemicontinuous_antitone {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : UpperSemicontinuous f) (gmon : Antitone g) : LowerSemicontinuous (g ∘ f) := fun x =>
  hg.continuousAt.comp_upperSemicontinuousAt_antitone (hf x) gmon

variable [Preorder β]

end

/-! #### Addition -/


section

variable {ι : Type*} {γ : Type*} [AddCommMonoid γ] [LinearOrder γ] [IsOrderedAddMonoid γ]
  [TopologicalSpace γ] [OrderTopology γ]

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `EReal`. The unprimed version of
the lemma uses `[ContinuousAdd]`. -/
/-
**UpperSemicontinuousWithinAt.add'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperSemicontinuousWithinAt.add' {f g : α -> γ} (hf : UpperSemicontinuousW
ithinAt f s x) (hg : UpperSemicontinuousWithinAt g s x) (hcont : ContinuousAt (f
un p : γ × γ => p.1 + p.2) (f x, g x)) : UpperSemicontinuousWithinAt (fun z => f
 z + g z) s x
参数：hf : UpperSemicontinuousWithinAt f s x；hg : UpperSemicontinuousWithinAt g s x
；hcont : ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSemicontinuousWithinAt.add'`：LowerSemicontinuousWithinAt.add' {f g 
: α -> γ} (hf : LowerSemicontinuousWithinAt f s x) (hg : LowerSemicontinuousWith
inAt g s x) (hcont : C…
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ

--- 原说明 ---
The sum of two upper semicontinuous functions is upper semicontinuous. Formulate
d with an
explicit continuity assumption on addition, for application to `EReal`. The unpr
imed version of
the lemma uses `[ContinuousAdd]`.
-/
theorem UpperSemicontinuousWithinAt.add' {f g : α → γ} (hf : UpperSemicontinuousWithinAt f s x)
    (hg : UpperSemicontinuousWithinAt g s x)
    (hcont : ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    UpperSemicontinuousWithinAt (fun z => f z + g z) s x :=
  LowerSemicontinuousWithinAt.add' (γ := γᵒᵈ) hf hg hcont

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `EReal`. The unprimed version of
the lemma uses `[ContinuousAdd]`. -/
/-
**UpperSemicontinuousAt.add'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperSemicontinuousAt.add' {f g : α -> γ} (hf : UpperSemicontinuousAt f x)
 (hg : UpperSemicontinuousAt g x) (hcont : ContinuousAt (fun p : γ × γ => p.1 + 
p.2) (f x, g x)) : UpperSemicontinuousAt (fun z => f z + g z) x
参数：hf : UpperSemicontinuousAt f x；hg : UpperSemicontinuousAt g x；hcont : Continu
ousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperSemicontinuousWithinAt.add'`：UpperSemicontinuousWithinAt.add' {f g 
: α -> γ} (hf : UpperSemicontinuousWithinAt f s x) (hg : UpperSemicontinuousWith
inAt g s x) (hcont : C…

--- 原说明 ---
The sum of two upper semicontinuous functions is upper semicontinuous. Formulate
d with an
explicit continuity assumption on addition, for application to `EReal`. The unpr
imed version of
the lemma uses `[ContinuousAdd]`.
-/
theorem UpperSemicontinuousAt.add' {f g : α → γ} (hf : UpperSemicontinuousAt f x)
    (hg : UpperSemicontinuousAt g x)
    (hcont : ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    UpperSemicontinuousAt (fun z => f z + g z) x := by
  simp_rw [← upperSemicontinuousWithinAt_univ_iff] at *
  exact hf.add' hg hcont

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `EReal`. The unprimed version of
the lemma uses `[ContinuousAdd]`. -/
/-
**UpperSemicontinuousOn.add'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperSemicontinuousOn.add' {f g : α -> γ} (hf : UpperSemicontinuousOn f s)
 (hg : UpperSemicontinuousOn g s) (hcont : forall x in s, ContinuousAt (fun p : 
γ × γ => p.1 + p.2) (f x, g x)) : UpperSemicontinuousOn (fun z => f z + g z) s
参数：hf : UpperSemicontinuousOn f s；hg : UpperSemicontinuousOn g s；hcont : forall 
x in s, ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperSemicontinuousWithinAt.add'`：UpperSemicontinuousWithinAt.add' {f g 
: α -> γ} (hf : UpperSemicontinuousWithinAt f s x) (hg : UpperSemicontinuousWith
inAt g s x) (hcont : C…

--- 原说明 ---
The sum of two upper semicontinuous functions is upper semicontinuous. Formulate
d with an
explicit continuity assumption on addition, for application to `EReal`. The unpr
imed version of
the lemma uses `[ContinuousAdd]`.
-/
theorem UpperSemicontinuousOn.add' {f g : α → γ} (hf : UpperSemicontinuousOn f s)
    (hg : UpperSemicontinuousOn g s)
    (hcont : ∀ x ∈ s, ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    UpperSemicontinuousOn (fun z => f z + g z) s := fun x hx =>
  UpperSemicontinuousWithinAt.add' (hf x hx) (hg x hx) (hcont x hx)

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `EReal`. The unprimed version of
the lemma uses `[ContinuousAdd]`. -/
/-
**UpperSemicontinuous.add'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperSemicontinuous.add' {f g : α -> γ} (hf : UpperSemicontinuous f) (hg :
 UpperSemicontinuous g) (hcont : forall x, ContinuousAt (fun p : γ × γ => p.1 + 
p.2) (f x, g x)) : UpperSemicontinuous fun z => f z + g z
参数：hf : UpperSemicontinuous f；hg : UpperSemicontinuous g；hcont : forall x, Conti
nuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperSemicontinuousAt.add'`：UpperSemicontinuousAt.add' {f g : α -> γ} (h
f : UpperSemicontinuousAt f x) (hg : UpperSemicontinuousAt g x) (hcont : Continu
ousAt (fun p : γ…

--- 原说明 ---
The sum of two upper semicontinuous functions is upper semicontinuous. Formulate
d with an
explicit continuity assumption on addition, for application to `EReal`. The unpr
imed version of
the lemma uses `[ContinuousAdd]`.
-/
theorem UpperSemicontinuous.add' {f g : α → γ} (hf : UpperSemicontinuous f)
    (hg : UpperSemicontinuous g)
    (hcont : ∀ x, ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    UpperSemicontinuous fun z => f z + g z :=
  fun x => UpperSemicontinuousAt.add' (hf x) (hg x) (hcont x)

variable [ContinuousAdd γ]

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with
`[ContinuousAdd]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `EReal`. -/
/-
**UpperSemicontinuousWithinAt.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperSemicontinuousWithinAt.add {f g : α -> γ} (hf : UpperSemicontinuousWi
thinAt f s x) (hg : UpperSemicontinuousWithinAt g s x) : UpperSemicontinuousWith
inAt (fun z => f z + g z) s x
参数：hf : UpperSemicontinuousWithinAt f s x；hg : UpperSemicontinuousWithinAt g s x
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperSemicontinuousWithinAt.add'`：UpperSemicontinuousWithinAt.add' {f g 
: α -> γ} (hf : UpperSemicontinuousWithinAt f s x) (hg : UpperSemicontinuousWith
inAt g s x) (hcont : C…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_add`：continuous_add : Continuous (fun x : X × X ↦ x.1 + x.2)

--- 原说明 ---
The sum of two upper semicontinuous functions is upper semicontinuous. Formulate
d with
`[ContinuousAdd]`. The primed version of the lemma uses an explicit continuity a
ssumption on
addition, for application to `EReal`.
-/
theorem UpperSemicontinuousWithinAt.add {f g : α → γ} (hf : UpperSemicontinuousWithinAt f s x)
    (hg : UpperSemicontinuousWithinAt g s x) :
    UpperSemicontinuousWithinAt (fun z => f z + g z) s x :=
  hf.add' hg continuous_add.continuousAt

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with
`[ContinuousAdd]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `EReal`. -/
/-
**UpperSemicontinuousAt.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperSemicontinuousAt.add {f g : α -> γ} (hf : UpperSemicontinuousAt f x) 
(hg : UpperSemicontinuousAt g x) : UpperSemicontinuousAt (fun z => f z + g z) x
参数：hf : UpperSemicontinuousAt f x；hg : UpperSemicontinuousAt g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperSemicontinuousAt.add'`：UpperSemicontinuousAt.add' {f g : α -> γ} (h
f : UpperSemicontinuousAt f x) (hg : UpperSemicontinuousAt g x) (hcont : Continu
ousAt (fun p : γ…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_add`：continuous_add : Continuous (fun x : X × X ↦ x.1 + x.2)

--- 原说明 ---
The sum of two upper semicontinuous functions is upper semicontinuous. Formulate
d with
`[ContinuousAdd]`. The primed version of the lemma uses an explicit continuity a
ssumption on
addition, for application to `EReal`.
-/
theorem UpperSemicontinuousAt.add {f g : α → γ} (hf : UpperSemicontinuousAt f x)
    (hg : UpperSemicontinuousAt g x) : UpperSemicontinuousAt (fun z => f z + g z) x :=
  hf.add' hg continuous_add.continuousAt

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with
`[ContinuousAdd]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `EReal`. -/
/-
**UpperSemicontinuousOn.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperSemicontinuousOn.add {f g : α -> γ} (hf : UpperSemicontinuousOn f s) 
(hg : UpperSemicontinuousOn g s) : UpperSemicontinuousOn (fun z => f z + g z) s
参数：hf : UpperSemicontinuousOn f s；hg : UpperSemicontinuousOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperSemicontinuousOn.add'`：UpperSemicontinuousOn.add' {f g : α -> γ} (h
f : UpperSemicontinuousOn f s) (hg : UpperSemicontinuousOn g s) (hcont : forall 
x in s, Continuo…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_add`：continuous_add : Continuous (fun x : X × X ↦ x.1 + x.2)

--- 原说明 ---
The sum of two upper semicontinuous functions is upper semicontinuous. Formulate
d with
`[ContinuousAdd]`. The primed version of the lemma uses an explicit continuity a
ssumption on
addition, for application to `EReal`.
-/
theorem UpperSemicontinuousOn.add {f g : α → γ} (hf : UpperSemicontinuousOn f s)
    (hg : UpperSemicontinuousOn g s) : UpperSemicontinuousOn (fun z => f z + g z) s :=
  hf.add' hg fun _x _hx => continuous_add.continuousAt

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with
`[ContinuousAdd]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `EReal`. -/
/-
**UpperSemicontinuous.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperSemicontinuous.add {f g : α -> γ} (hf : UpperSemicontinuous f) (hg : 
UpperSemicontinuous g) : UpperSemicontinuous fun z => f z + g z
参数：hf : UpperSemicontinuous f；hg : UpperSemicontinuous g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UpperSemicontinuous.add'`：UpperSemicontinuous.add' {f g : α -> γ} (hf : 
UpperSemicontinuous f) (hg : UpperSemicontinuous g) (hcont : forall x, Continuou
sAt (fun p : γ…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_add`：continuous_add : Continuous (fun x : X × X ↦ x.1 + x.2)

--- 原说明 ---
The sum of two upper semicontinuous functions is upper semicontinuous. Formulate
d with
`[ContinuousAdd]`. The primed version of the lemma uses an explicit continuity a
ssumption on
addition, for application to `EReal`.
-/
theorem UpperSemicontinuous.add {f g : α → γ} (hf : UpperSemicontinuous f)
    (hg : UpperSemicontinuous g) : UpperSemicontinuous fun z => f z + g z :=
  hf.add' hg fun _x => continuous_add.continuousAt
/-
**upperSemicontinuousWithinAt_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperSemicontinuousWithinAt_sum {f : ι -> α -> γ} {a : Finset ι} (ha : for
all i in a, UpperSemicontinuousWithinAt (f i) s x) : UpperSemicontinuousWithinAt
 (fun z => ∑ i in a, f i z) s x
参数：ha : forall i in a, UpperSemicontinuousWithinAt (f i) s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lowerSemicontinuousWithinAt_sum`：lowerSemicontinuousWithinAt_sum {f : ι 
-> α -> γ} {a : Finset ι} (ha : forall i in a, LowerSemicontinuousWithinAt (f i)
 s x) : LowerSemicont…
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `instContinuousAddOrderDual`：∀ {M : Type u_3} [inst : TopologicalSpace M]
 [inst_1 : Add M] [ContinuousAdd M], ContinuousAdd Mᵒᵈ
-/
theorem upperSemicontinuousWithinAt_sum {f : ι → α → γ} {a : Finset ι}
    (ha : ∀ i ∈ a, UpperSemicontinuousWithinAt (f i) s x) :
    UpperSemicontinuousWithinAt (fun z => ∑ i ∈ a, f i z) s x :=
  lowerSemicontinuousWithinAt_sum (γ := γᵒᵈ) ha
/-
**upperSemicontinuousAt_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperSemicontinuousAt_sum {f : ι -> α -> γ} {a : Finset ι} (ha : forall i 
in a, UpperSemicontinuousAt (f i) x) : UpperSemicontinuousAt (fun z => ∑ i in a,
 f i z) x
参数：ha : forall i in a, UpperSemicontinuousAt (f i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `upperSemicontinuousWithinAt_sum`：upperSemicontinuousWithinAt_sum {f : ι 
-> α -> γ} {a : Finset ι} (ha : forall i in a, UpperSemicontinuousWithinAt (f i)
 s x) : UpperSemicont…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem upperSemicontinuousAt_sum {f : ι → α → γ} {a : Finset ι}
    (ha : ∀ i ∈ a, UpperSemicontinuousAt (f i) x) :
    UpperSemicontinuousAt (fun z => ∑ i ∈ a, f i z) x := by
  simp_rw [← upperSemicontinuousWithinAt_univ_iff] at *
  exact upperSemicontinuousWithinAt_sum ha
/-
**upperSemicontinuousOn_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperSemicontinuousOn_sum {f : ι -> α -> γ} {a : Finset ι} (ha : forall i 
in a, UpperSemicontinuousOn (f i) s) : UpperSemicontinuousOn (fun z => ∑ i in a,
 f i z) s
参数：ha : forall i in a, UpperSemicontinuousOn (f i) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `upperSemicontinuousWithinAt_sum`：upperSemicontinuousWithinAt_sum {f : ι 
-> α -> γ} {a : Finset ι} (ha : forall i in a, UpperSemicontinuousWithinAt (f i)
 s x) : UpperSemicont…
-/
theorem upperSemicontinuousOn_sum {f : ι → α → γ} {a : Finset ι}
    (ha : ∀ i ∈ a, UpperSemicontinuousOn (f i) s) :
    UpperSemicontinuousOn (fun z => ∑ i ∈ a, f i z) s := fun x hx =>
  upperSemicontinuousWithinAt_sum fun i hi => ha i hi x hx
/-
**upperSemicontinuous_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperSemicontinuous_sum {f : ι -> α -> γ} {a : Finset ι} (ha : forall i in
 a, UpperSemicontinuous (f i)) : UpperSemicontinuous fun z => ∑ i in a, f i z
参数：ha : forall i in a, UpperSemicontinuous (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `upperSemicontinuousAt_sum`：upperSemicontinuousAt_sum {f : ι -> α -> γ} {
a : Finset ι} (ha : forall i in a, UpperSemicontinuousAt (f i) x) : UpperSemicon
tinuousAt (fun …
-/
theorem upperSemicontinuous_sum {f : ι → α → γ} {a : Finset ι}
    (ha : ∀ i ∈ a, UpperSemicontinuous (f i)) : UpperSemicontinuous fun z => ∑ i ∈ a, f i z :=
  fun x => upperSemicontinuousAt_sum fun i hi => ha i hi x

end

/-! #### Infimum -/

section

variable {α : Type*} {β : Type*} [TopologicalSpace α] [LinearOrder β]
    {f g : α → β} {s : Set α} {a : α}

/-
**UpperSemicontinuousWithinAt.inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperSemicontinuousWithinAt.inf (hf : UpperSemicontinuousWithinAt f s a) (
hg : UpperSemicontinuousWithinAt g s a) : UpperSemicontinuousWithinAt (fun x => 
f x ⊓ g x) s a
参数：hf : UpperSemicontinuousWithinAt f s a；hg : UpperSemicontinuousWithinAt g s a
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSemicontinuousWithinAt.sup`：LowerSemicontinuousWithinAt.sup (hf : L
owerSemicontinuousWithinAt f s a) (hg : LowerSemicontinuousWithinAt g s a) : Low
erSemicontinuousWithi…
-/
theorem UpperSemicontinuousWithinAt.inf
    (hf : UpperSemicontinuousWithinAt f s a) (hg : UpperSemicontinuousWithinAt g s a) :
    UpperSemicontinuousWithinAt (fun x ↦ f x ⊓ g x) s a :=
  LowerSemicontinuousWithinAt.sup (β := βᵒᵈ) hf hg
/-
**UpperSemicontinuousAt.inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperSemicontinuousAt.inf (hf : UpperSemicontinuousAt f a) (hg : UpperSemi
continuousAt g a) : UpperSemicontinuousAt (fun x => f x ⊓ g x) a
参数：hf : UpperSemicontinuousAt f a；hg : UpperSemicontinuousAt g a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSemicontinuousAt.sup`：LowerSemicontinuousAt.sup (hf : LowerSemicont
inuousAt f a) (hg : LowerSemicontinuousAt g a) : LowerSemicontinuousAt (fun x =>
 f x ⊔ g x) a
-/
theorem UpperSemicontinuousAt.inf
    (hf : UpperSemicontinuousAt f a) (hg : UpperSemicontinuousAt g a) :
    UpperSemicontinuousAt (fun x ↦ f x ⊓ g x) a :=
  LowerSemicontinuousAt.sup (β := βᵒᵈ) hf hg
/-
**UpperSemicontinuousOn.inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperSemicontinuousOn.inf (hf : UpperSemicontinuousOn f s) (hg : UpperSemi
continuousOn g s) : UpperSemicontinuousOn (fun x => f x ⊓ g x) s
参数：hf : UpperSemicontinuousOn f s；hg : UpperSemicontinuousOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSemicontinuousOn.sup`：LowerSemicontinuousOn.sup (hf : LowerSemicont
inuousOn f s) (hg : LowerSemicontinuousOn g s) : LowerSemicontinuousOn (fun x =>
 f x ⊔ g x) s
-/
theorem UpperSemicontinuousOn.inf
    (hf : UpperSemicontinuousOn f s) (hg : UpperSemicontinuousOn g s) :
    UpperSemicontinuousOn (fun x ↦ f x ⊓ g x) s :=
  LowerSemicontinuousOn.sup (β := βᵒᵈ) hf hg
/-
**UpperSemicontinuous.inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperSemicontinuous.inf (hf : UpperSemicontinuous f) (hg : UpperSemicontin
uous g) : UpperSemicontinuous (fun x => f x ⊓ g x)
参数：hf : UpperSemicontinuous f；hg : UpperSemicontinuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSemicontinuous.sup`：LowerSemicontinuous.sup (hf : LowerSemicontinuo
us f) (hg : LowerSemicontinuous g) : LowerSemicontinuous fun x => f x ⊔ g x
-/
theorem UpperSemicontinuous.inf (hf : UpperSemicontinuous f) (hg : UpperSemicontinuous g) :
    UpperSemicontinuous (fun x ↦ f x ⊓ g x) :=
  LowerSemicontinuous.sup (β := βᵒᵈ) hf hg
/-
**UpperSemicontinuousWithinAt.sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperSemicontinuousWithinAt.sup (hf : UpperSemicontinuousWithinAt f s a) (
hg : UpperSemicontinuousWithinAt g s a) : UpperSemicontinuousWithinAt (fun x => 
f x ⊔ g x) s a
参数：hf : UpperSemicontinuousWithinAt f s a；hg : UpperSemicontinuousWithinAt g s a
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSemicontinuousWithinAt.inf`：LowerSemicontinuousWithinAt.inf (hf : L
owerSemicontinuousWithinAt f s a) (hg : LowerSemicontinuousWithinAt g s a) : Low
erSemicontinuousWithi…
-/
theorem UpperSemicontinuousWithinAt.sup
    (hf : UpperSemicontinuousWithinAt f s a) (hg : UpperSemicontinuousWithinAt g s a) :
    UpperSemicontinuousWithinAt (fun x ↦ f x ⊔ g x) s a :=
  LowerSemicontinuousWithinAt.inf (β := βᵒᵈ) hf hg
/-
**UpperSemicontinuousAt.sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperSemicontinuousAt.sup (hf : UpperSemicontinuousAt f a) (hg : UpperSemi
continuousAt g a) : UpperSemicontinuousAt (fun x => f x ⊔ g x) a
参数：hf : UpperSemicontinuousAt f a；hg : UpperSemicontinuousAt g a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSemicontinuousAt.inf`：LowerSemicontinuousAt.inf (hf : LowerSemicont
inuousAt f a) (hg : LowerSemicontinuousAt g a) : LowerSemicontinuousAt (fun x =>
 f x ⊓ g x) a
-/
theorem UpperSemicontinuousAt.sup
    (hf : UpperSemicontinuousAt f a) (hg : UpperSemicontinuousAt g a) :
    UpperSemicontinuousAt (fun x ↦ f x ⊔ g x) a :=
  LowerSemicontinuousAt.inf (β := βᵒᵈ) hf hg
/-
**UpperSemicontinuousOn.sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperSemicontinuousOn.sup (hf : UpperSemicontinuousOn f s) (hg : UpperSemi
continuousOn g s) : UpperSemicontinuousOn (fun x => f x ⊔ g x) s
参数：hf : UpperSemicontinuousOn f s；hg : UpperSemicontinuousOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSemicontinuousOn.inf`：LowerSemicontinuousOn.inf (hf : LowerSemicont
inuousOn f s) (hg : LowerSemicontinuousOn g s) : LowerSemicontinuousOn (fun x =>
 f x ⊓ g x) s
-/
theorem UpperSemicontinuousOn.sup
    (hf : UpperSemicontinuousOn f s) (hg : UpperSemicontinuousOn g s) :
    UpperSemicontinuousOn (fun x ↦ f x ⊔ g x) s :=
  LowerSemicontinuousOn.inf (β := βᵒᵈ) hf hg
/-
**UpperSemicontinuous.sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperSemicontinuous.sup (hf : UpperSemicontinuous f) (hg : UpperSemicontin
uous g) : UpperSemicontinuous fun x => f x ⊔ g x
参数：hf : UpperSemicontinuous f；hg : UpperSemicontinuous g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSemicontinuous.inf`：LowerSemicontinuous.inf (hf : LowerSemicontinuo
us f) (hg : LowerSemicontinuous g) : LowerSemicontinuous fun x => f x ⊓ g x
-/
theorem UpperSemicontinuous.sup (hf : UpperSemicontinuous f) (hg : UpperSemicontinuous g) :
    UpperSemicontinuous fun x ↦ f x ⊔ g x :=
  LowerSemicontinuous.inf (β := βᵒᵈ) hf hg


end

section

variable {ι : Sort*} {δ δ' : Type*} [CompleteLinearOrder δ] [ConditionallyCompleteLinearOrder δ']

/-
**upperSemicontinuousWithinAt_ciInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperSemicontinuousWithinAt_ciInf {f : ι -> α -> δ'} (bdd : forallᶠ y in 𝓝
[s] x, BddBelow (range fun i => f i y)) (h : forall i, UpperSemicontinuousWithin
At (f i) s x) : UpperSemicontinuousWithinAt (fun x' => ⨅ i, f i x') s x
参数：bdd : forallᶠ y in 𝓝[s] x, BddBelow (range fun i => f i y)；h : forall i, Uppe
rSemicontinuousWithinAt (f i) s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lowerSemicontinuousWithinAt_ciSup`：lowerSemicontinuousWithinAt_ciSup {f 
: ι -> α -> δ'} (bdd : forallᶠ y in 𝓝[s] x, BddAbove (range fun i => f i y)) (h 
: forall i, LowerSemico…
-/
theorem upperSemicontinuousWithinAt_ciInf {f : ι → α → δ'}
    (bdd : ∀ᶠ y in 𝓝[s] x, BddBelow (range fun i => f i y))
    (h : ∀ i, UpperSemicontinuousWithinAt (f i) s x) :
    UpperSemicontinuousWithinAt (fun x' => ⨅ i, f i x') s x :=
  lowerSemicontinuousWithinAt_ciSup (δ' := δ'ᵒᵈ) bdd h
/-
**upperSemicontinuousWithinAt_iInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperSemicontinuousWithinAt_iInf {f : ι -> α -> δ} (h : forall i, UpperSem
icontinuousWithinAt (f i) s x) : UpperSemicontinuousWithinAt (fun x' => ⨅ i, f i
 x') s x
参数：h : forall i, UpperSemicontinuousWithinAt (f i) s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lowerSemicontinuousWithinAt_iSup`：lowerSemicontinuousWithinAt_iSup {f : 
ι -> α -> δ} (h : forall i, LowerSemicontinuousWithinAt (f i) s x) : LowerSemico
ntinuousWithinAt (fun …
-/
theorem upperSemicontinuousWithinAt_iInf {f : ι → α → δ}
    (h : ∀ i, UpperSemicontinuousWithinAt (f i) s x) :
    UpperSemicontinuousWithinAt (fun x' => ⨅ i, f i x') s x :=
  lowerSemicontinuousWithinAt_iSup (δ := δᵒᵈ) h
/-
**upperSemicontinuousWithinAt_biInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperSemicontinuousWithinAt_biInf {p : ι -> Prop} {f : forall i, p i -> α 
-> δ} (h : forall i hi, UpperSemicontinuousWithinAt (f i hi) s x) : UpperSemicon
tinuousWithinAt (fun x' => ⨅ (i) (hi), f i hi x') s x
参数：h : forall i hi, UpperSemicontinuousWithinAt (f i hi) s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `upperSemicontinuousWithinAt_iInf`：upperSemicontinuousWithinAt_iInf {f : 
ι -> α -> δ} (h : forall i, UpperSemicontinuousWithinAt (f i) s x) : UpperSemico
ntinuousWithinAt (fun …
-/
theorem upperSemicontinuousWithinAt_biInf {p : ι → Prop} {f : ∀ i, p i → α → δ}
    (h : ∀ i hi, UpperSemicontinuousWithinAt (f i hi) s x) :
    UpperSemicontinuousWithinAt (fun x' => ⨅ (i) (hi), f i hi x') s x :=
  upperSemicontinuousWithinAt_iInf fun i => upperSemicontinuousWithinAt_iInf fun hi => h i hi
/-
**upperSemicontinuousAt_ciInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperSemicontinuousAt_ciInf {f : ι -> α -> δ'} (bdd : forallᶠ y in 𝓝 x, Bd
dBelow (range fun i => f i y)) (h : forall i, UpperSemicontinuousAt (f i) x) : U
pperSemicontinuousAt (fun x' => ⨅ i, f i x') x
参数：bdd : forallᶠ y in 𝓝 x, BddBelow (range fun i => f i y)；h : forall i, UpperSe
micontinuousAt (f i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lowerSemicontinuousAt_ciSup`：lowerSemicontinuousAt_ciSup {f : ι -> α -> 
δ'} (bdd : forallᶠ y in 𝓝 x, BddAbove (range fun i => f i y)) (h : forall i, Low
erSemicontinuousA…
-/
theorem upperSemicontinuousAt_ciInf {f : ι → α → δ'}
    (bdd : ∀ᶠ y in 𝓝 x, BddBelow (range fun i => f i y)) (h : ∀ i, UpperSemicontinuousAt (f i) x) :
    UpperSemicontinuousAt (fun x' => ⨅ i, f i x') x :=
  @lowerSemicontinuousAt_ciSup α _ x ι δ'ᵒᵈ _ f bdd h
/-
**upperSemicontinuousAt_iInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperSemicontinuousAt_iInf {f : ι -> α -> δ} (h : forall i, UpperSemiconti
nuousAt (f i) x) : UpperSemicontinuousAt (fun x' => ⨅ i, f i x') x
参数：h : forall i, UpperSemicontinuousAt (f i) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lowerSemicontinuousAt_iSup`：lowerSemicontinuousAt_iSup {f : ι -> α -> δ}
 (h : forall i, LowerSemicontinuousAt (f i) x) : LowerSemicontinuousAt (fun x' =
> ⨆ i, f i x') x
-/
theorem upperSemicontinuousAt_iInf {f : ι → α → δ} (h : ∀ i, UpperSemicontinuousAt (f i) x) :
    UpperSemicontinuousAt (fun x' => ⨅ i, f i x') x :=
  @lowerSemicontinuousAt_iSup α _ x ι δᵒᵈ _ f h
/-
**upperSemicontinuousAt_biInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperSemicontinuousAt_biInf {p : ι -> Prop} {f : forall i, p i -> α -> δ} 
(h : forall i hi, UpperSemicontinuousAt (f i hi) x) : UpperSemicontinuousAt (fun
 x' => ⨅ (i) (hi), f i hi x') x
参数：h : forall i hi, UpperSemicontinuousAt (f i hi) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `upperSemicontinuousAt_iInf`：upperSemicontinuousAt_iInf {f : ι -> α -> δ}
 (h : forall i, UpperSemicontinuousAt (f i) x) : UpperSemicontinuousAt (fun x' =
> ⨅ i, f i x') x
-/
theorem upperSemicontinuousAt_biInf {p : ι → Prop} {f : ∀ i, p i → α → δ}
    (h : ∀ i hi, UpperSemicontinuousAt (f i hi) x) :
    UpperSemicontinuousAt (fun x' => ⨅ (i) (hi), f i hi x') x :=
  upperSemicontinuousAt_iInf fun i => upperSemicontinuousAt_iInf fun hi => h i hi
/-
**upperSemicontinuousOn_ciInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperSemicontinuousOn_ciInf {f : ι -> α -> δ'} (bdd : forall x in s, BddBe
low (range fun i => f i x)) (h : forall i, UpperSemicontinuousOn (f i) s) : Uppe
rSemicontinuousOn (fun x' => ⨅ i, f i x') s
参数：bdd : forall x in s, BddBelow (range fun i => f i x)；h : forall i, UpperSemic
ontinuousOn (f i) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `upperSemicontinuousWithinAt_ciInf`：upperSemicontinuousWithinAt_ciInf {f 
: ι -> α -> δ'} (bdd : forallᶠ y in 𝓝[s] x, BddBelow (range fun i => f i y)) (h 
: forall i, UpperSemico…
· 使用定理 `eventually_nhdsWithin_of_forall`：eventually_nhdsWithin_of_forall {s : Se
t α} {a : α} {p : α -> Prop} (h : forall x in s, p x) : forallᶠ x in 𝓝[s] a, p x
-/
theorem upperSemicontinuousOn_ciInf {f : ι → α → δ'}
    (bdd : ∀ x ∈ s, BddBelow (range fun i => f i x)) (h : ∀ i, UpperSemicontinuousOn (f i) s) :
    UpperSemicontinuousOn (fun x' => ⨅ i, f i x') s := fun x hx =>
  upperSemicontinuousWithinAt_ciInf (eventually_nhdsWithin_of_forall bdd) fun i => h i x hx
/-
**upperSemicontinuousOn_iInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperSemicontinuousOn_iInf {f : ι -> α -> δ} (h : forall i, UpperSemiconti
nuousOn (f i) s) : UpperSemicontinuousOn (fun x' => ⨅ i, f i x') s
参数：h : forall i, UpperSemicontinuousOn (f i) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `upperSemicontinuousWithinAt_iInf`：upperSemicontinuousWithinAt_iInf {f : 
ι -> α -> δ} (h : forall i, UpperSemicontinuousWithinAt (f i) s x) : UpperSemico
ntinuousWithinAt (fun …
-/
theorem upperSemicontinuousOn_iInf {f : ι → α → δ} (h : ∀ i, UpperSemicontinuousOn (f i) s) :
    UpperSemicontinuousOn (fun x' => ⨅ i, f i x') s := fun x hx =>
  upperSemicontinuousWithinAt_iInf fun i => h i x hx
/-
**upperSemicontinuousOn_biInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperSemicontinuousOn_biInf {p : ι -> Prop} {f : forall i, p i -> α -> δ} 
(h : forall i hi, UpperSemicontinuousOn (f i hi) s) : UpperSemicontinuousOn (fun
 x' => ⨅ (i) (hi), f i hi x') s
参数：h : forall i hi, UpperSemicontinuousOn (f i hi) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `upperSemicontinuousOn_iInf`：upperSemicontinuousOn_iInf {f : ι -> α -> δ}
 (h : forall i, UpperSemicontinuousOn (f i) s) : UpperSemicontinuousOn (fun x' =
> ⨅ i, f i x') s
-/
theorem upperSemicontinuousOn_biInf {p : ι → Prop} {f : ∀ i, p i → α → δ}
    (h : ∀ i hi, UpperSemicontinuousOn (f i hi) s) :
    UpperSemicontinuousOn (fun x' => ⨅ (i) (hi), f i hi x') s :=
  upperSemicontinuousOn_iInf fun i => upperSemicontinuousOn_iInf fun hi => h i hi
/-
**upperSemicontinuous_ciInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperSemicontinuous_ciInf {f : ι -> α -> δ'} (bdd : forall x, BddBelow (ra
nge fun i => f i x)) (h : forall i, UpperSemicontinuous (f i)) : UpperSemicontin
uous fun x' => ⨅ i, f i x'
参数：bdd : forall x, BddBelow (range fun i => f i x)；h : forall i, UpperSemicontin
uous (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `upperSemicontinuousAt_ciInf`：upperSemicontinuousAt_ciInf {f : ι -> α -> 
δ'} (bdd : forallᶠ y in 𝓝 x, BddBelow (range fun i => f i y)) (h : forall i, Upp
erSemicontinuousA…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem upperSemicontinuous_ciInf {f : ι → α → δ'} (bdd : ∀ x, BddBelow (range fun i => f i x))
    (h : ∀ i, UpperSemicontinuous (f i)) : UpperSemicontinuous fun x' => ⨅ i, f i x' := fun x =>
  upperSemicontinuousAt_ciInf (Eventually.of_forall bdd) fun i => h i x
/-
**upperSemicontinuous_iInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperSemicontinuous_iInf {f : ι -> α -> δ} (h : forall i, UpperSemicontinu
ous (f i)) : UpperSemicontinuous fun x' => ⨅ i, f i x'
参数：h : forall i, UpperSemicontinuous (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `upperSemicontinuousAt_iInf`：upperSemicontinuousAt_iInf {f : ι -> α -> δ}
 (h : forall i, UpperSemicontinuousAt (f i) x) : UpperSemicontinuousAt (fun x' =
> ⨅ i, f i x') x
-/
theorem upperSemicontinuous_iInf {f : ι → α → δ} (h : ∀ i, UpperSemicontinuous (f i)) :
    UpperSemicontinuous fun x' => ⨅ i, f i x' := fun x => upperSemicontinuousAt_iInf fun i => h i x
/-
**upperSemicontinuous_biInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperSemicontinuous_biInf {p : ι -> Prop} {f : forall i, p i -> α -> δ} (h
 : forall i hi, UpperSemicontinuous (f i hi)) : UpperSemicontinuous fun x' => ⨅ 
(i) (hi), f i hi x'
参数：h : forall i hi, UpperSemicontinuous (f i hi)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `upperSemicontinuous_iInf`：upperSemicontinuous_iInf {f : ι -> α -> δ} (h 
: forall i, UpperSemicontinuous (f i)) : UpperSemicontinuous fun x' => ⨅ i, f i 
x'
-/
theorem upperSemicontinuous_biInf {p : ι → Prop} {f : ∀ i, p i → α → δ}
    (h : ∀ i hi, UpperSemicontinuous (f i hi)) :
    UpperSemicontinuous fun x' => ⨅ (i) (hi), f i hi x' :=
  upperSemicontinuous_iInf fun i => upperSemicontinuous_iInf fun hi => h i hi

end

section

variable {γ : Type*} [LinearOrder γ] [TopologicalSpace γ] [OrderTopology γ]

/-
**continuousWithinAt_iff_lower_upperSemicontinuousWithinAt** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：continuousWithinAt_iff_lower_upperSemicontinuousWithinAt {f : α -> γ} : Co
ntinuousWithinAt f s x ↔ LowerSemicontinuousWithinAt f s x ∧ UpperSemicontinuous
WithinAt f s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.lowerSemicontinuousWithinAt`：ContinuousWithinAt.lower
SemicontinuousWithinAt {f : α -> γ} (h : ContinuousWithinAt f s x) : LowerSemico
ntinuousWithinAt f s x
· 使用定理 `ContinuousWithinAt.upperSemicontinuousWithinAt`：ContinuousWithinAt.upper
SemicontinuousWithinAt {f : α -> γ} (h : ContinuousWithinAt f s x) : UpperSemico
ntinuousWithinAt f s x
· 使用定理 `exists_Ioc_subset_of_mem_nhds`：exists_Ioc_subset_of_mem_nhds {a : α} {s 
: Set α} (hs : s in 𝓝 a) (h : exists l, l < a) : exists l < a, Ioc l a subseteq 
s
· 使用定理 `exists_Ico_subset_of_mem_nhds`：∀ {α : Type u} [inst : TopologicalSpace α
] [inst_1 : LinearOrder α] [OrderTopology α] {a : α} {s : Set α},   s ∈ nhds a →
 (∃ l, a < l) → ∃ l…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
-/
theorem continuousWithinAt_iff_lower_upperSemicontinuousWithinAt {f : α → γ} :
    ContinuousWithinAt f s x ↔
      LowerSemicontinuousWithinAt f s x ∧ UpperSemicontinuousWithinAt f s x := by
  refine ⟨fun h => ⟨h.lowerSemicontinuousWithinAt, h.upperSemicontinuousWithinAt⟩, ?_⟩
  rintro ⟨h₁, h₂⟩
  intro v hv
  simp only [Filter.mem_map]
  by_cases! Hl : ∃ l, l < f x
  · rcases exists_Ioc_subset_of_mem_nhds hv Hl with ⟨l, lfx, hl⟩
    by_cases! Hu : ∃ u, f x < u
    · rcases exists_Ico_subset_of_mem_nhds hv Hu with ⟨u, fxu, hu⟩
      filter_upwards [h₁ l lfx, h₂ u fxu] with a lfa fau
      rcases le_or_gt (f a) (f x) with h | h
      · exact hl ⟨lfa, h⟩
      · exact hu ⟨le_of_lt h, fau⟩
    · filter_upwards [h₁ l lfx] with a lfa using hl ⟨lfa, Hu (f a)⟩
  · by_cases! Hu : ∃ u, f x < u
    · rcases exists_Ico_subset_of_mem_nhds hv Hu with ⟨u, fxu, hu⟩
      filter_upwards [h₂ u fxu] with a lfa
      apply hu
      exact ⟨Hl (f a), lfa⟩
    · apply Filter.Eventually.of_forall
      intro a
      have : f a = f x := le_antisymm (Hu _) (Hl _)
      rw [this]
      exact mem_of_mem_nhds hv
/-
**continuousAt_iff_lower_upperSemicontinuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_iff_lower_upperSemicontinuousAt {f : α -> γ} : ContinuousAt f
 x ↔ LowerSemicontinuousAt f x ∧ UpperSemicontinuousAt f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuousAt_iff_lower_upperSemicontinuousAt {f : α → γ} :
    ContinuousAt f x ↔ LowerSemicontinuousAt f x ∧ UpperSemicontinuousAt f x := by
  simp_rw [← continuousWithinAt_univ, ← lowerSemicontinuousWithinAt_univ_iff, ←
    upperSemicontinuousWithinAt_univ_iff, continuousWithinAt_iff_lower_upperSemicontinuousWithinAt]
/-
**continuousOn_iff_lower_upperSemicontinuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_iff_lower_upperSemicontinuousOn {f : α -> γ} : ContinuousOn f
 s ↔ LowerSemicontinuousOn f s ∧ UpperSemicontinuousOn f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem continuousOn_iff_lower_upperSemicontinuousOn {f : α → γ} :
    ContinuousOn f s ↔ LowerSemicontinuousOn f s ∧ UpperSemicontinuousOn f s := by
  simp only [ContinuousOn, continuousWithinAt_iff_lower_upperSemicontinuousWithinAt]
  exact
    ⟨fun H => ⟨fun x hx => (H x hx).1, fun x hx => (H x hx).2⟩, fun H x hx => ⟨H.1 x hx, H.2 x hx⟩⟩
/-
**continuous_iff_lower_upperSemicontinuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_iff_lower_upperSemicontinuous {f : α -> γ} : Continuous f ↔ Low
erSemicontinuous f ∧ UpperSemicontinuous f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuous_iff_lower_upperSemicontinuous {f : α → γ} :
    Continuous f ↔ LowerSemicontinuous f ∧ UpperSemicontinuous f := by
  simp_rw [← continuousOn_univ, continuousOn_iff_lower_upperSemicontinuousOn,
    lowerSemicontinuousOn_univ_iff, upperSemicontinuousOn_univ_iff]

end

