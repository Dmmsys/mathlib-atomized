/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Combinatorics.Additive.FreimanHom

/-!
# Corners

This file defines corners, namely triples of the form `(x, y), (x, y + d), (x + d, y)`, and the
property of being corner-free.

## References

* [Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
* [Wikipedia, *Corners theorem*](https://en.wikipedia.org/wiki/Corners_theorem)
-/

@[expose] public section

assert_not_exists Field Ideal TwoSidedIdeal

open Set

variable {G H : Type*}

section AddCommMonoid
variable [AddCommMonoid G] [AddCommMonoid H] {A B : Set (G × G)} {s : Set G} {t : Set H} {f : G → H}
  {x₁ y₁ x₂ y₂ : G}

/-- A **corner** of a set `A` in an abelian group is a triple of points of the form
`(x, y), (x + d, y), (x, y + d)`. It is **nontrivial** if `d ≠ 0`.

Here we define it as triples `(x₁, y₁), (x₂, y₁), (x₁, y₂)` where `x₁ + y₂ = x₂ + y₁` in order for
the definition to make sense in commutative monoids, the motivating example being `ℕ`. -/
@[mk_iff]
/-
**IsCorner** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{G : Type u_1} → [AddCommMonoid G] → Set (G × G) → G → G → G → G → Prop
参数：G × G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A **corner** of a set `A` in an abelian group is a triple of points of the form
`(x, y), (x + d, y), (x, y + d)`. It is **nontrivial** if `d ≠ 0`.

Here we define it as triples `(x₁, y₁), (x₂, y₁), (x₁, y₂)` where `x₁ + y₂ = x₂ 
+ y₁` in order for
the definition to make sense in commutative monoids, the motivating example bein
g `ℕ`.
-/
structure IsCorner (A : Set (G × G)) (x₁ y₁ x₂ y₂ : G) : Prop where
  fst_fst_mem : (x₁, y₁) ∈ A
  fst_snd_mem : (x₁, y₂) ∈ A
  snd_fst_mem : (x₂, y₁) ∈ A
  add_eq_add : x₁ + y₂ = x₂ + y₁

/-- A **corner-free set** in an abelian group is a set containing no non-trivial corner. -/
/-
**IsCornerFree** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsCornerFree (A : Set (G × G)) : Prop
参数：A : Set (G × G)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A **corner-free set** in an abelian group is a set containing no non-trivial cor
ner.
-/
def IsCornerFree (A : Set (G × G)) : Prop := ∀ ⦃x₁ y₁ x₂ y₂⦄, IsCorner A x₁ y₁ x₂ y₂ → x₁ = x₂

/-- A convenient restatement of corner-freeness in terms of an ambient product set. -/
/-
**isCornerFree_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isCornerFree_iff (hAs : A subseteq s ×ˢ s) : IsCornerFree A ↔ forall ⦃x₁⦄,
 x₁ in s -> forall ⦃y₁⦄, y₁ in s -> forall ⦃x₂⦄, x₂ in s -> forall ⦃y₂⦄, y₂ in s
 -> IsCorner A x₁ y₁ x₂ y₂ -> x₁ = x₂ where mp hA _x₁ _ _y₁ _ _x₂ _ _y₂ _ hxy
参数：hAs : A subseteq s ×ˢ s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsCorner.fst_fst_mem`：∀ {G : Type u_1} [inst : AddCommMonoid G] {A : Set
 (G × G)} {x₁ y₁ x₂ y₂ : G}, IsCorner A x₁ y₁ x₂ y₂ → (x₁, y₁) ∈ A
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsCorner.snd_fst_mem`：∀ {G : Type u_1} [inst : AddCommMonoid G] {A : Set
 (G × G)} {x₁ y₁ x₂ y₂ : G}, IsCorner A x₁ y₁ x₂ y₂ → (x₂, y₁) ∈ A
· 使用定理 `IsCorner.fst_snd_mem`：∀ {G : Type u_1} [inst : AddCommMonoid G] {A : Set
 (G × G)} {x₁ y₁ x₂ y₂ : G}, IsCorner A x₁ y₁ x₂ y₂ → (x₁, y₂) ∈ A

--- 原说明 ---
A convenient restatement of corner-freeness in terms of an ambient product set.
-/
lemma isCornerFree_iff (hAs : A ⊆ s ×ˢ s) :
    IsCornerFree A ↔ ∀ ⦃x₁⦄, x₁ ∈ s → ∀ ⦃y₁⦄, y₁ ∈ s → ∀ ⦃x₂⦄, x₂ ∈ s → ∀ ⦃y₂⦄, y₂ ∈ s →
      IsCorner A x₁ y₁ x₂ y₂ → x₁ = x₂ where
  mp hA _x₁ _ _y₁ _ _x₂ _ _y₂ _ hxy := hA hxy
  mpr hA _x₁ _y₁ _x₂ _y₂ hxy := hA (hAs hxy.fst_fst_mem).1 (hAs hxy.fst_fst_mem).2
    (hAs hxy.snd_fst_mem).1 (hAs hxy.fst_snd_mem).2 hxy
/-
**IsCorner.mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCorner.mono (hAB : A subseteq B) (hA : IsCorner A x₁ y₁ x₂ y₂) : IsCorne
r B x₁ y₁ x₂ y₂ where fst_fst_mem
参数：hAB : A subseteq B；hA : IsCorner A x₁ y₁ x₂ y₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCorner.fst_fst_mem`：∀ {G : Type u_1} [inst : AddCommMonoid G] {A : Set
 (G × G)} {x₁ y₁ x₂ y₂ : G}, IsCorner A x₁ y₁ x₂ y₂ → (x₁, y₁) ∈ A
· 使用定理 `IsCorner.fst_snd_mem`：∀ {G : Type u_1} [inst : AddCommMonoid G] {A : Set
 (G × G)} {x₁ y₁ x₂ y₂ : G}, IsCorner A x₁ y₁ x₂ y₂ → (x₁, y₂) ∈ A
· 使用定理 `IsCorner.snd_fst_mem`：∀ {G : Type u_1} [inst : AddCommMonoid G] {A : Set
 (G × G)} {x₁ y₁ x₂ y₂ : G}, IsCorner A x₁ y₁ x₂ y₂ → (x₂, y₁) ∈ A
· 使用定理 `IsCorner.add_eq_add`：∀ {G : Type u_1} [inst : AddCommMonoid G] {A : Set 
(G × G)} {x₁ y₁ x₂ y₂ : G},   IsCorner A x₁ y₁ x₂ y₂ → x₁ + y₂ = x₂ + y₁
-/
lemma IsCorner.mono (hAB : A ⊆ B) (hA : IsCorner A x₁ y₁ x₂ y₂) : IsCorner B x₁ y₁ x₂ y₂ where
  fst_fst_mem := hAB hA.fst_fst_mem
  fst_snd_mem := hAB hA.fst_snd_mem
  snd_fst_mem := hAB hA.snd_fst_mem
  add_eq_add := hA.add_eq_add
/-
**IsCornerFree.mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCornerFree.mono (hAB : A subseteq B) (hB : IsCornerFree B) : IsCornerFre
e A
参数：hAB : A subseteq B；hB : IsCornerFree B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsCorner.mono`：IsCorner.mono (hAB : A subseteq B) (hA : IsCorner A x₁ y₁
 x₂ y₂) : IsCorner B x₁ y₁ x₂ y₂ where fst_fst_mem
-/
lemma IsCornerFree.mono (hAB : A ⊆ B) (hB : IsCornerFree B) : IsCornerFree A :=
  fun _x₁ _y₁ _x₂ _y₂ hxyd ↦ hB <| hxyd.mono hAB
/-
**not_isCorner_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G : Type u_1} [inst : AddCommMonoid G] {x₁ y₁ x₂ y₂ : G}, ¬IsCorner ∅ x
₁ y₁ x₂ y₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
@[simp] lemma not_isCorner_empty : ¬ IsCorner ∅ x₁ y₁ x₂ y₂ := by simp [isCorner_iff]
/-
**Set.Subsingleton.isCornerFree** 是 Mathlib 中的一个定理，位于命名空间 `Set.Subsingleton`。
形式化陈述：∀ {G : Type u_1} [inst : AddCommMonoid G] {A : Set (G × G)}, A.Subsingleto
n → IsCornerFree A
参数：G × G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `IsCorner.fst_fst_mem`：∀ {G : Type u_1} [inst : AddCommMonoid G] {A : Set
 (G × G)} {x₁ y₁ x₂ y₂ : G}, IsCorner A x₁ y₁ x₂ y₂ → (x₁, y₁) ∈ A
· 使用定理 `IsCorner.snd_fst_mem`：∀ {G : Type u_1} [inst : AddCommMonoid G] {A : Set
 (G × G)} {x₁ y₁ x₂ y₂ : G}, IsCorner A x₁ y₁ x₂ y₂ → (x₂, y₁) ∈ A
-/
@[simp] lemma Set.Subsingleton.isCornerFree (hA : A.Subsingleton) : IsCornerFree A :=
  fun _x₁ _y₁ _x₂ _y₂ hxyd ↦ by simpa using hA hxyd.fst_fst_mem hxyd.snd_fst_mem
/-
**isCornerFree_empty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isCornerFree_empty : IsCornerFree (∅ : Set (G × G))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.isCornerFree`：∀ {G : Type u_1} [inst : AddCommMonoid G]
 {A : Set (G × G)}, A.Subsingleton → IsCornerFree A
· 使用定理 `Set.subsingleton_empty`：subsingleton_empty : (∅ : Set α).Subsingleton
-/
lemma isCornerFree_empty : IsCornerFree (∅ : Set (G × G)) := subsingleton_empty.isCornerFree
/-
**isCornerFree_singleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isCornerFree_singleton (x : G × G) : IsCornerFree {x}
参数：x : G × G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.isCornerFree`：∀ {G : Type u_1} [inst : AddCommMonoid G]
 {A : Set (G × G)}, A.Subsingleton → IsCornerFree A
· 使用定理 `Set.subsingleton_singleton`：subsingleton_singleton {a} : ({a} : Set α).S
ubsingleton
-/
lemma isCornerFree_singleton (x : G × G) : IsCornerFree {x} := subsingleton_singleton.isCornerFree

/-- Corners are preserved under `2`-Freiman homomorphisms. -/
/-
**IsCorner.image** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCorner.image (hf : IsAddFreimanHom 2 s t f) (hAs : (A : Set (G × G)) sub
seteq s ×ˢ s) (hA : IsCorner A x₁ y₁ x₂ y₂) : IsCorner (Prod.map f f '' A) (f x₁
) (f y₁) (f x₂) (f y₂)
参数：hf : IsAddFreimanHom 2 s t f；hAs : (A : Set (G × G)) subseteq s ×ˢ s；hA : IsC
orner A x₁ y₁ x₂ y₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `IsAddFreimanHom.add_eq_add`：∀ {α : Type u_2} {β : Type u_3} [inst : AddC
ommMonoid α] [inst_1 : AddCommMonoid β] {A : Set α} {B : Set β} {f : α → β},   I
sAddFreimanHom 2…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Corners are preserved under `2`-Freiman homomorphisms.
-/
lemma IsCorner.image (hf : IsAddFreimanHom 2 s t f) (hAs : (A : Set (G × G)) ⊆ s ×ˢ s)
    (hA : IsCorner A x₁ y₁ x₂ y₂) : IsCorner (Prod.map f f '' A) (f x₁) (f y₁) (f x₂) (f y₂) := by
  obtain ⟨hx₁y₁, hx₁y₂, hx₂y₁, hxy⟩ := hA
  exact ⟨mem_image_of_mem _ hx₁y₁, mem_image_of_mem _ hx₁y₂, mem_image_of_mem _ hx₂y₁,
    hf.add_eq_add (hAs hx₁y₁).1 (hAs hx₁y₂).2 (hAs hx₂y₁).1 (hAs hx₁y₁).2 hxy⟩

/-- Corners are preserved under `2`-Freiman homomorphisms. -/
/-
**IsCornerFree.of_image** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCornerFree.of_image (hf : IsAddFreimanHom 2 s t f) (hf' : s.InjOn f) (hA
s : (A : Set (G × G)) subseteq s ×ˢ s) (hA : IsCornerFree (Prod.map f f '' A)) :
 IsCornerFree A
参数：hf : IsAddFreimanHom 2 s t f；hf' : s.InjOn f；hAs : (A : Set (G × G)) subseteq
 s ×ˢ s；hA : IsCornerFree (Prod.map f f '' A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsCorner.fst_fst_mem`：∀ {G : Type u_1} [inst : AddCommMonoid G] {A : Set
 (G × G)} {x₁ y₁ x₂ y₂ : G}, IsCorner A x₁ y₁ x₂ y₂ → (x₁, y₁) ∈ A
· 使用定理 `IsCorner.snd_fst_mem`：∀ {G : Type u_1} [inst : AddCommMonoid G] {A : Set
 (G × G)} {x₁ y₁ x₂ y₂ : G}, IsCorner A x₁ y₁ x₂ y₂ → (x₂, y₁) ∈ A
· 使用引理 `IsCorner.image`：IsCorner.image (hf : IsAddFreimanHom 2 s t f) (hAs : (A 
: Set (G × G)) subseteq s ×ˢ s) (hA : IsCorner A x₁ y₁ x₂ y₂) : IsCorner (Prod.m
ap f…

--- 原说明 ---
Corners are preserved under `2`-Freiman homomorphisms.
-/
lemma IsCornerFree.of_image (hf : IsAddFreimanHom 2 s t f) (hf' : s.InjOn f)
    (hAs : (A : Set (G × G)) ⊆ s ×ˢ s) (hA : IsCornerFree (Prod.map f f '' A)) : IsCornerFree A :=
  fun _x₁ _y₁ _x₂ _y₂ hxy ↦
    hf' (hAs hxy.fst_fst_mem).1 (hAs hxy.snd_fst_mem).1 <| hA <| hxy.image hf hAs
/-
**isCorner_image** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isCorner_image (hf : IsAddFreimanIso 2 s t f) (hAs : A subseteq s ×ˢ s) (h
x₁ : x₁ in s) (hy₁ : y₁ in s) (hx₂ : x₂ in s) (hy₂ : y₂ in s) : IsCorner (Prod.m
ap f f '' A) (f x₁) (f y₁) (f x₂) (f y₂) ↔ IsCorner A x₁ y₁ x₂ y₂
参数：hf : IsAddFreimanIso 2 s t f；hAs : A subseteq s ×ˢ s；hx₁ : x₁ in s；hy₁ : y₁ i
n s；hx₂ : x₂ in s；hy₂ : y₂ in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.InjOn.prodMap`：∀ {α₁ : Type u_7} {α₂ : Type u_8} {β₁ : Type u_9} {β₂
 : Type u_10} {s₁ : Set α₁} {s₂ : Set α₂} {f₁ : α₁ → β₁}   {f₂ : α₂ → β₂}, Set.I
njOn f₁…
· 使用定理 `Set.BijOn.injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
 {f : α → β}, Set.BijOn f s t → Set.InjOn f s
· 使用定理 `IsAddFreimanIso.bijOn`：∀ {α : Type u_2} {β : Type u_3} [inst : AddCommMo
noid α] [inst_1 : AddCommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f : α → β}
, IsAddFrei…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isCorner_iff`：∀ {G : Type u_1} [inst : AddCommMonoid G] (A : Set (G × G)
) (x₁ y₁ x₂ y₂ : G),   IsCorner A x₁ y₁ x₂ y₂ ↔ (x₁, y₁) ∈ A ∧ (x₁, y₂) ∈ A ∧ (x
₂,…
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.InjOn.mem_image_iff`：∀ {α : Type u_1} {β : Type u_2} {s s₁ : Set α} 
{f : α → β} {x : α},   Set.InjOn f s → s₁ ⊆ s → x ∈ s → (f x ∈ f '' s₁ ↔ x ∈ s₁)
· 使用定理 `Set.mk_mem_prod`：mk_mem_prod (ha : a in s) (hb : b in t) : (a, b) in s ×
ˢ t
· 使用定理 `IsAddFreimanIso.add_eq_add`：∀ {α : Type u_2} {β : Type u_3} [inst : AddC
ommMonoid α] [inst_1 : AddCommMonoid β] {A : Set α} {B : Set β} {f : α → β},   I
sAddFreimanIso 2…
-/
lemma isCorner_image (hf : IsAddFreimanIso 2 s t f) (hAs : A ⊆ s ×ˢ s)
    (hx₁ : x₁ ∈ s) (hy₁ : y₁ ∈ s) (hx₂ : x₂ ∈ s) (hy₂ : y₂ ∈ s) :
    IsCorner (Prod.map f f '' A) (f x₁) (f y₁) (f x₂) (f y₂) ↔ IsCorner A x₁ y₁ x₂ y₂ := by
  have hf' := hf.bijOn.injOn.prodMap hf.bijOn.injOn
  rw [isCorner_iff, isCorner_iff]
  congr!
  · exact hf'.mem_image_iff hAs (mk_mem_prod hx₁ hy₁)
  · exact hf'.mem_image_iff hAs (mk_mem_prod hx₁ hy₂)
  · exact hf'.mem_image_iff hAs (mk_mem_prod hx₂ hy₁)
  · exact hf.add_eq_add hx₁ hy₂ hx₂ hy₁
/-
**isCornerFree_image** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isCornerFree_image (hf : IsAddFreimanIso 2 s t f) (hAs : A subseteq s ×ˢ s
) : IsCornerFree (Prod.map f f '' A) ↔ IsCornerFree A
参数：hf : IsAddFreimanIso 2 s t f；hAs : A subseteq s ×ˢ s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
· 使用定理 `Set.MapsTo.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t₁ t₂ 
: Set β} {f : α → β},   Set.MapsTo f s₁ t₁ → s₂ ⊆ s₁ → t₁ ⊆ t₂ → Set.MapsTo f s₂
 t₂
· 使用定理 `Set.MapsTo.prodMap`：∀ {α₁ : Type u_7} {α₂ : Type u_8} {β₁ : Type u_9} {β
₂ : Type u_10} {s₁ : Set α₁} {s₂ : Set α₂} {t₁ : Set β₁}   {t₂ : Set β₂} {f₁ : α
₁ → β₁} …
· 使用定理 `Set.BijOn.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.MapsTo f s t
· 使用定理 `IsAddFreimanIso.bijOn`：∀ {α : Type u_2} {β : Type u_3} [inst : AddCommMo
noid α] [inst_1 : AddCommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f : α → β}
, IsAddFrei…
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isCornerFree_iff`：isCornerFree_iff (hAs : A subseteq s ×ˢ s) : IsCornerF
ree A ↔ forall ⦃x₁⦄, x₁ in s -> forall ⦃y₁⦄, y₁ in s -> forall ⦃x₂⦄, x₂ in s -> 
forall…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.BijOn.forall`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β} {p : β → Prop},   Set.BijOn f s t → ((∀ b ∈ t, p b) ↔ ∀ a ∈ s, p (
f a))
· 使用引理 `isCorner_image`：isCorner_image (hf : IsAddFreimanIso 2 s t f) (hAs : A s
ubseteq s ×ˢ s) (hx₁ : x₁ in s) (hy₁ : y₁ in s) (hx₂ : x₂ in s) (hy₂ : y₂ in s) 
: Is…
· 使用定理 `Set.InjOn.eq_iff`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β
} {x y : α}, Set.InjOn f s → x ∈ s → y ∈ s → (f x = f y ↔ x = y)
· 使用定理 `Set.BijOn.injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
 {f : α → β}, Set.BijOn f s t → Set.InjOn f s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isCornerFree_image (hf : IsAddFreimanIso 2 s t f) (hAs : A ⊆ s ×ˢ s) :
    IsCornerFree (Prod.map f f '' A) ↔ IsCornerFree A := by
  have : Prod.map f f '' A ⊆ t ×ˢ t :=
    ((hf.bijOn.mapsTo.prodMap hf.bijOn.mapsTo).mono hAs Subset.rfl).image_subset
  rw [isCornerFree_iff hAs, isCornerFree_iff this]
  simp +contextual only [hf.bijOn.forall, isCorner_image hf hAs, hf.bijOn.injOn.eq_iff]

alias ⟨IsCorner.of_image, _⟩ := isCorner_image
alias ⟨_, IsCornerFree.image⟩ := isCornerFree_image

end AddCommMonoid

