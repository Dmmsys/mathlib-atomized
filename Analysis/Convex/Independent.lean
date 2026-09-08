/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Extreme

/-!
# Convex independence

This file defines convex independent families of points.

Convex independence is closely related to affine independence. In both cases, no point can be
written as a combination of others. When the combination is affine (that is, any coefficients), this
yields affine independence. When the combination is convex (that is, all coefficients are
nonnegative), then this yields convex independence. In particular, affine independence implies
convex independence.

## Main declarations

* `ConvexIndependent p`: Convex independence of the indexed family `p : ι → E`. Every point of the
  family only belongs to convex hulls of sets of the family containing it.
* `convexIndependent_iff_finset`: Carathéodory's theorem allows us to only check finsets to
  conclude convex independence.
* `Convex.convexIndependent_extremePoints`: Extreme points of a convex set are convex independent.

## References

* https://en.wikipedia.org/wiki/Convex_position

## TODO

Prove `AffineIndependent.convexIndependent`. This requires some glue between `affineCombination`
and `Finset.centerMass`.

## Tags

independence, convex position
-/

@[expose] public section


open Affine Finset Function

variable {𝕜 E ι : Type*}

section OrderedSemiring

variable (𝕜) [Semiring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- An indexed family is said to be convex independent if every point only belongs to convex hulls
of sets containing it. -/
/-
**ConvexIndependent** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ConvexIndependent (p : ι -> E) : Prop
参数：p : ι -> E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An indexed family is said to be convex independent if every point only belongs t
o convex hulls
of sets containing it.
-/
def ConvexIndependent (p : ι → E) : Prop :=
  ∀ (s : Set ι) (x : ι), p x ∈ convexHull 𝕜 (p '' s) → x ∈ s

variable {𝕜}

/-- A family with at most one point is convex independent. -/
/-
**Subsingleton.convexIndependent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subsingleton.convexIndependent [Subsingleton ι] (p : ι -> E) : ConvexIndep
endent 𝕜 p
参数：p : ι -> E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.mem_iff_nonempty`：mem_iff_nonempty {α : Type*} [Subsingleto
n α] {s : Set α} {x : α} : x in s ↔ s.Nonempty
· 使用定理 `Set.image_nonempty`：image_nonempty {f : α -> β} {s : Set α} : (f '' s).N
onempty ↔ s.Nonempty
· 使用定理 `convexHull_nonempty_iff`：convexHull_nonempty_iff : (convexHull 𝕜 s).None
mpty ↔ s.Nonempty

--- 原说明 ---
A family with at most one point is convex independent.
-/
theorem Subsingleton.convexIndependent [Subsingleton ι] (p : ι → E) : ConvexIndependent 𝕜 p := by
  intro s x hx
  have : (convexHull 𝕜 (p '' s)).Nonempty := ⟨p x, hx⟩
  rw [convexHull_nonempty_iff, Set.image_nonempty] at this
  rwa [Subsingleton.mem_iff_nonempty]

/-- A convex independent family is injective. -/
/-
**ConvexIndependent.injective** 是 Mathlib 中的一个定理，位于命名空间 `ConvexIndependent`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {ι : Type u_3} [inst : Semiring 𝕜] [inst_1
 : PartialOrder 𝕜] [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module 𝕜 E] {p :
 ι → E}, ConvexIndependent 𝕜 p → Function.Injective p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `convexHull_singleton`：convexHull_singleton (x : E) : convexHull 𝕜 ({x} :
 Set E) = {x}
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)

--- 原说明 ---
A convex independent family is injective.
-/
protected theorem ConvexIndependent.injective {p : ι → E} (hc : ConvexIndependent 𝕜 p) :
    Function.Injective p := by
  refine fun i j hij => hc {j} i ?_
  rw [hij, Set.image_singleton, convexHull_singleton]
  exact Set.mem_singleton _

/-- If a family is convex independent, so is any subfamily given by composition of an embedding into
index type with the original family. -/
/-
**ConvexIndependent.comp_embedding** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexIndependent.comp_embedding {ι' : Type*} (f : ι' ↪ ι) {p : ι -> E} (h
c : ConvexIndependent 𝕜 p) : ConvexIndependent 𝕜 (p ∘ f)
参数：f : ι' ↪ ι；hc : ConvexIndependent 𝕜 p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s

--- 原说明 ---
If a family is convex independent, so is any subfamily given by composition of a
n embedding into
index type with the original family.
-/
theorem ConvexIndependent.comp_embedding {ι' : Type*} (f : ι' ↪ ι) {p : ι → E}
    (hc : ConvexIndependent 𝕜 p) : ConvexIndependent 𝕜 (p ∘ f) := by
  intro s x hx
  rw [← f.injective.mem_set_image]
  exact hc _ _ (by rwa [Set.image_image])

/-- If a family is convex independent, so is any subfamily indexed by a subtype of the index type.
-/
/-
**ConvexIndependent.subtype** 是 Mathlib 中的一个定理，位于命名空间 `ConvexIndependent`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {ι : Type u_3} [inst : Semiring 𝕜] [inst_1
 : PartialOrder 𝕜] [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module 𝕜 E] {p :
 ι → E}, ConvexIndependent 𝕜 p → ∀ (s : Set ι), ConvexIndependent 𝕜 fun i => p ↑
i
参数：s : Set ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexIndependent.comp_embedding`：ConvexIndependent.comp_embedding {ι' :
 Type*} (f : ι' ↪ ι) {p : ι -> E} (hc : ConvexIndependent 𝕜 p) : ConvexIndepende
nt 𝕜 (p ∘ f)

--- 原说明 ---
If a family is convex independent, so is any subfamily indexed by a subtype of t
he index type.
-/
protected theorem ConvexIndependent.subtype {p : ι → E} (hc : ConvexIndependent 𝕜 p) (s : Set ι) :
    ConvexIndependent 𝕜 fun i : s => p i :=
  hc.comp_embedding (Embedding.subtype _)

set_option backward.isDefEq.respectTransparency false in
/-- If an indexed family of points is convex independent, so is the corresponding set of points. -/
/-
**ConvexIndependent.range** 是 Mathlib 中的一个定理，位于命名空间 `ConvexIndependent`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {ι : Type u_3} [inst : Semiring 𝕜] [inst_1
 : PartialOrder 𝕜] [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module 𝕜 E] {p :
 ι → E}, ConvexIndependent 𝕜 p → ConvexIndependent 𝕜 Subtype.val
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Embedding.coeFn_mk`：coeFn_mk {α β} (f : α -> β) (i) : (@mk _ _ 
f i : α -> β) = f
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `ConvexIndependent.comp_embedding`：ConvexIndependent.comp_embedding {ι' :
 Type*} (f : ι' ↪ ι) {p : ι -> E} (hc : ConvexIndependent 𝕜 p) : ConvexIndepende
nt 𝕜 (p ∘ f)

--- 原说明 ---
If an indexed family of points is convex independent, so is the corresponding se
t of points.
-/
protected theorem ConvexIndependent.range {p : ι → E} (hc : ConvexIndependent 𝕜 p) :
    ConvexIndependent 𝕜 ((↑) : Set.range p → E) := by
  let f : Set.range p → ι := fun x => x.property.choose
  have hf : ∀ x, p (f x) = x := fun x => x.property.choose_spec
  let fe : Set.range p ↪ ι := ⟨f, fun x₁ x₂ he => Subtype.ext (hf x₁ ▸ hf x₂ ▸ he ▸ rfl)⟩
  convert! hc.comp_embedding fe
  ext
  rw [Embedding.coeFn_mk, comp_apply, hf]

/-- A subset of a convex independent set of points is convex independent as well. -/
/-
**ConvexIndependent.mono** 是 Mathlib 中的一个定理，位于命名空间 `ConvexIndependent`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [inst_1 : PartialOrder
 𝕜] [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module 𝕜 E] {s t : Set E}, Conv
exIndependent 𝕜 Subtype.val → s ⊆ t → ConvexIndependent 𝕜 Subtype.val
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexIndependent.comp_embedding`：ConvexIndependent.comp_embedding {ι' :
 Type*} (f : ι' ↪ ι) {p : ι -> E} (hc : ConvexIndependent 𝕜 p) : ConvexIndepende
nt 𝕜 (p ∘ f)

--- 原说明 ---
A subset of a convex independent set of points is convex independent as well.
-/
protected theorem ConvexIndependent.mono {s t : Set E} (hc : ConvexIndependent 𝕜 ((↑) : t → E))
    (hs : s ⊆ t) : ConvexIndependent 𝕜 ((↑) : s → E) :=
  hc.comp_embedding (s.embeddingOfSubset t hs)

/-- The range of an injective indexed family of points is convex independent iff that family is. -/
/-
**Function.Injective.convexIndependent_iff_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Injective.convexIndependent_iff_set {p : ι -> E} (hi : Function.I
njective p) : ConvexIndependent 𝕜 ((↑) : Set.range p -> E) ↔ ConvexIndependent 𝕜
 p
参数：hi : Function.Injective p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexIndependent.comp_embedding`：ConvexIndependent.comp_embedding {ι' :
 Type*} (f : ι' ↪ ι) {p : ι -> E} (hc : ConvexIndependent 𝕜 p) : ConvexIndepende
nt 𝕜 (p ∘ f)
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.mk_eq_mk`：mk_eq_mk {a h a' h'} : @mk α p a h = @mk α p a' h' ↔ a
 = a'
· 使用定理 `ConvexIndependent.range`：∀ {𝕜 : Type u_1} {E : Type u_2} {ι : Type u_3} 
[inst : Semiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommGroup E]   [inst_
3 : _root_.Mo…

--- 原说明 ---
The range of an injective indexed family of points is convex independent iff tha
t family is.
-/
theorem Function.Injective.convexIndependent_iff_set {p : ι → E} (hi : Function.Injective p) :
    ConvexIndependent 𝕜 ((↑) : Set.range p → E) ↔ ConvexIndependent 𝕜 p :=
  ⟨fun hc =>
    hc.comp_embedding
      (⟨fun i => ⟨p i, Set.mem_range_self _⟩, fun _ _ h => hi (Subtype.mk_eq_mk.1 h)⟩ :
        ι ↪ Set.range p),
    ConvexIndependent.range⟩

/-- If a family is convex independent, a point in the family is in the convex hull of some of the
points given by a subset of the index type if and only if the point's index is in this subset. -/
@[simp]
/-
**ConvexIndependent.mem_convexHull_iff** 是 Mathlib 中的一个定理，位于命名空间 `ConvexIndepend
ent`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {ι : Type u_3} [inst : Semiring 𝕜] [inst_1
 : PartialOrder 𝕜] [inst_2 : AddCommGroup E]   [inst_3 : _root_.Module 𝕜 E] {p :
 ι → E},   ConvexIndependent 𝕜 p → ∀ (s : Set ι) (i : ι), p i ∈ (convexHull 𝕜) (
p '' s) ↔ i ∈ s
参数：s : Set ι；i : ι；convexHull 𝕜；p '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_convexHull`：subset_convexHull : s subseteq convexHull 𝕜 s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a

--- 原说明 ---
If a family is convex independent, a point in the family is in the convex hull o
f some of the
points given by a subset of the index type if and only if the point's index is i
n this subset.
-/
protected theorem ConvexIndependent.mem_convexHull_iff {p : ι → E} (hc : ConvexIndependent 𝕜 p)
    (s : Set ι) (i : ι) : p i ∈ convexHull 𝕜 (p '' s) ↔ i ∈ s :=
  ⟨hc _ _, fun hi => subset_convexHull 𝕜 _ (Set.mem_image_of_mem p hi)⟩

/-- If a family is convex independent, a point in the family is not in the convex hull of the other
points. See `convexIndependent_set_iff_notMem_convexHull_sdiff` for the `Set` version. -/
/-
**convexIndependent_iff_notMem_convexHull_sdiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexIndependent_iff_notMem_convexHull_sdiff {p : ι -> E} : ConvexIndepen
dent 𝕜 p ↔ forall i s, p i ∉ convexHull 𝕜 (p '' (s \ {i}))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ConvexIndependent.mem_convexHull_iff`：∀ {𝕜 : Type u_1} {E : Type u_2} {ι
 : Type u_3} [inst : Semiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommGrou
p E]   [inst_3 : _root_.Mo…
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用引理 `Set.sdiff_singleton_eq_self`：sdiff_singleton_eq_self (h : a ∉ s) : s \ {
a} = s

--- 原说明 ---
If a family is convex independent, a point in the family is not in the convex hu
ll of the other
points. See `convexIndependent_set_iff_notMem_convexHull_sdiff` for the `Set` ve
rsion.
-/
theorem convexIndependent_iff_notMem_convexHull_sdiff {p : ι → E} :
    ConvexIndependent 𝕜 p ↔ ∀ i s, p i ∉ convexHull 𝕜 (p '' (s \ {i})) := by
  refine ⟨fun hc i s h => ?_, fun h s i hi => ?_⟩
  · rw [hc.mem_convexHull_iff] at h
    exact h.2 (Set.mem_singleton _)
  · by_contra H
    refine h i s ?_
    rw [Set.sdiff_singleton_eq_self H]
    exact hi

@[deprecated (since := "2026-06-03")]
alias convexIndependent_iff_notMem_convexHull_diff := convexIndependent_iff_notMem_convexHull_sdiff
/-
**convexIndependent_set_iff_inter_convexHull_subset** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：convexIndependent_set_iff_inter_convexHull_subset {s : Set E} : ConvexInde
pendent 𝕜 ((↑) : s -> E) ↔ forall t, t subseteq s -> s inter convexHull 𝕜 t subs
eteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.coe_image_of_subset`：coe_image_of_subset {s t : Set α} (h : t su
bseteq s) : (↑) '' { x : ↥s | ↑x in t } = t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `Subtype.coe_image_subset`：coe_image_subset (s : Set α) (t : Set s) : ((↑
) : s -> α) '' t subseteq s
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem convexIndependent_set_iff_inter_convexHull_subset {s : Set E} :
    ConvexIndependent 𝕜 ((↑) : s → E) ↔ ∀ t, t ⊆ s → s ∩ convexHull 𝕜 t ⊆ t := by
  constructor
  · rintro hc t h x ⟨hxs, hxt⟩
    refine hc { x | ↑x ∈ t } ⟨x, hxs⟩ ?_
    rw [Subtype.coe_image_of_subset h]
    exact hxt
  · intro hc t x h
    rw [← Subtype.coe_injective.mem_set_image]
    exact hc (t.image ((↑) : s → E)) (Subtype.coe_image_subset s t) ⟨x.prop, h⟩

/-- If a set is convex independent, a point in the set is not in the convex hull of the other
points. See `convexIndependent_iff_notMem_convexHull_sdiff` for the indexed family version. -/
/-
**convexIndependent_set_iff_notMem_convexHull_sdiff** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：convexIndependent_set_iff_notMem_convexHull_sdiff {s : Set E} : ConvexInde
pendent 𝕜 ((↑) : s -> E) ↔ forall x in s, x ∉ convexHull 𝕜 (s \ {x})
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `convexIndependent_set_iff_inter_convexHull_subset`：convexIndependent_set
_iff_inter_convexHull_subset {s : Set E} : ConvexIndependent 𝕜 ((↑) : s -> E) ↔ 
forall t, t subseteq s -> s inter conve…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `convexHull_mono`：convexHull_mono (hst : s subseteq t) : convexHull 𝕜 s s
ubseteq convexHull 𝕜 t
· 使用引理 `Set.subset_sdiff_singleton`：subset_sdiff_singleton (h : s subseteq t) (h
a : a ∉ s) : s subseteq t \ {a}

--- 原说明 ---
If a set is convex independent, a point in the set is not in the convex hull of 
the other
points. See `convexIndependent_iff_notMem_convexHull_sdiff` for the indexed fami
ly version.
-/
theorem convexIndependent_set_iff_notMem_convexHull_sdiff {s : Set E} :
    ConvexIndependent 𝕜 ((↑) : s → E) ↔ ∀ x ∈ s, x ∉ convexHull 𝕜 (s \ {x}) := by
  rw [convexIndependent_set_iff_inter_convexHull_subset]
  constructor
  · rintro hs x hxs hx
    exact (hs _ Set.sdiff_subset ⟨hxs, hx⟩).2 (Set.mem_singleton _)
  · rintro hs t ht x ⟨hxs, hxt⟩
    by_contra h
    exact hs _ hxs (convexHull_mono (Set.subset_sdiff_singleton ht h) hxt)

@[deprecated (since := "2026-06-03")]
alias convexIndependent_set_iff_notMem_convexHull_diff :=
  convexIndependent_set_iff_notMem_convexHull_sdiff

end OrderedSemiring

section LinearOrderedField

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] {s : Set E}

open scoped Classical in
/-- To check convex independence, one only has to check finsets thanks to Carathéodory's theorem. -/
/-
**convexIndependent_iff_finset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexIndependent_iff_finset {p : ι -> E} : ConvexIndependent 𝕜 p ↔ forall
 (s : Finset ι) (x : ι), p x in convexHull 𝕜 (s.image p : Set E) -> x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `Finset.image_singleton`：image_singleton (f : α -> β) (a : α) : image f {
a} = {f a}
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `convexHull_singleton`：convexHull_singleton (x : E) : convexHull 𝕜 ({x} :
 Set E) = {x}
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `convexHull_eq_union_convexHull_finite_subsets`：convexHull_eq_union_conve
xHull_finite_subsets (s : Set E) : convexHull R s = ⋃ (t : Finset E) (_ : ↑t sub
seteq s), convexHull R ↑t
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Finset.image_preimage`：image_preimage [DecidableEq β] (f : α -> β) (s : 
Finset β) [forall x, Decidable (x in Set.range f)] (hf : Set.InjOn f (f ⁻¹' ↑s))
 : image f …
· 使用定理 `Finset.filter_true_of_mem`：∀ {α : Type u_1} {p : α → Prop} [inst : Decid
ablePred p] {s : Finset α}, (∀ x ∈ s, p x) → Finset.filter p s = s
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `Finset.mem_preimage`：mem_preimage {f : α -> β} {s : Finset β} {hf : Set.
InjOn f (f ⁻¹' ↑s)} {x : α} : x in preimage s f hf ↔ f x in s

--- 原说明 ---
To check convex independence, one only has to check finsets thanks to Carathéodo
ry's theorem.
-/
theorem convexIndependent_iff_finset {p : ι → E} :
    ConvexIndependent 𝕜 p ↔
      ∀ (s : Finset ι) (x : ι), p x ∈ convexHull 𝕜 (s.image p : Set E) → x ∈ s := by
  refine ⟨fun hc s x hx => hc s x ?_, fun h s x hx => ?_⟩
  · rwa [Finset.coe_image] at hx
  have hp : Injective p := by
    rintro a b hab
    rw [← mem_singleton]
    refine h {b} a ?_
    rw [hab, image_singleton, coe_singleton, convexHull_singleton]
    exact Set.mem_singleton _
  rw [convexHull_eq_union_convexHull_finite_subsets] at hx
  simp_rw [Set.mem_iUnion] at hx
  obtain ⟨t, ht, hx⟩ := hx
  rw [← hp.mem_set_image]
  refine ht ?_
  suffices x ∈ t.preimage p hp.injOn by rwa [mem_preimage, ← mem_coe] at this
  refine h _ x ?_
  rwa [t.image_preimage p hp.injOn, filter_true_of_mem]
  exact fun y hy => s.image_subset_range p (ht <| mem_coe.2 hy)

/-! ### Extreme points -/


/-
**Convex.convexIndependent_extremePoints** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.convexIndependent_extremePoints (hs : Convex 𝕜 s) : ConvexIndepende
nt 𝕜 ((↑) : s.extremePoints 𝕜 -> E)
参数：hs : Convex 𝕜 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `convexIndependent_set_iff_notMem_convexHull_sdiff`：convexIndependent_set
_iff_notMem_convexHull_sdiff {s : Set E} : ConvexIndependent 𝕜 ((↑) : s -> E) ↔ 
forall x in s, x ∉ convexHull 𝕜 (s \ {x…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `extremePoints_convexHull_subset`：extremePoints_convexHull_subset : (conv
exHull 𝕜 A).extremePoints 𝕜 subseteq A
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `IsStrictOrderedRing.isDomain`：∀ {R : Type u} [inst : Semiring R] [inst_1
 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], IsDomain R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `inter_extremePoints_subset_extremePoints_of_subset`：inter_extremePoints_
subset_extremePoints_of_subset (hBA : B subseteq A) : B inter A.extremePoints 𝕜 
subseteq B.extremePoints 𝕜
· 使用定理 `convexHull_min`：convexHull_min : s subseteq t -> Convex 𝕜 t -> convexHul
l 𝕜 s subseteq t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `extremePoints_subset`：extremePoints_subset : A.extremePoints 𝕜 subseteq 
A
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)

--- 原说明 ---
### Extreme points
-/
theorem Convex.convexIndependent_extremePoints (hs : Convex 𝕜 s) :
    ConvexIndependent 𝕜 ((↑) : s.extremePoints 𝕜 → E) :=
  convexIndependent_set_iff_notMem_convexHull_sdiff.2 fun _ hx h =>
    (extremePoints_convexHull_subset
          (inter_extremePoints_subset_extremePoints_of_subset
            (convexHull_min (Set.sdiff_subset.trans extremePoints_subset) hs) ⟨h, hx⟩)).2
      (Set.mem_singleton _)

end LinearOrderedField

