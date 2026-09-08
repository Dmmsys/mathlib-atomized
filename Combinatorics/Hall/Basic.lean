/-
Copyright (c) 2021 Alena Gusakov, Bhavik Mehta, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alena Gusakov, Bhavik Mehta, Kyle Miller
-/
module

public import Mathlib.Combinatorics.Hall.Finite
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.Data.Rel

/-!
# Hall's Marriage Theorem

Given a list of finite subsets $X_1, X_2, \dots, X_n$ of some given set
$S$, P. Hall in [Hall1935] gave a necessary and sufficient condition for
there to be a list of distinct elements $x_1, x_2, \dots, x_n$ with
$x_i\in X_i$ for each $i$: it is when for each $k$, the union of every
$k$ of these subsets has at least $k$ elements.

Rather than a list of finite subsets, one may consider indexed families
`t : ι → Finset α` of finite subsets with `ι` a `Fintype`, and then the list
of distinct representatives is given by an injective function `f : ι → α`
such that `∀ i, f i ∈ t i`, called a *matching*.
This version is formalized as `Finset.all_card_le_biUnion_card_iff_exists_injective'`
in a separate module.

The theorem can be generalized to remove the constraint that `ι` be a `Fintype`.
As observed in [Halpern1966], one may use the constrained version of the theorem
in a compactness argument to remove this constraint.
The formulation of compactness we use is that inverse limits of nonempty finite sets
are nonempty (`nonempty_sections_of_finite_inverse_system`), which uses the
Tychonoff theorem.
The core of this module is constructing the inverse system: for every finite subset `ι'` of
`ι`, we can consider the matchings on the restriction of the indexed family `t` to `ι'`.

## Main statements

* `Finset.all_card_le_biUnion_card_iff_exists_injective` is in terms of `t : ι → Finset α`.
* `Fintype.all_card_le_rel_image_card_iff_exists_injective` is in terms of a relation
  `r : α → β → Prop` such that `R.image {a}` is a finite set for all `a : α`.
* `Fintype.all_card_le_filter_rel_iff_exists_injective` is in terms of a relation
  `r : α → β → Prop` on finite types, with the Hall condition given in terms of
  `finset.univ.filter`.

## Tags

Hall's Marriage Theorem, indexed families
-/

@[expose] public section

open Finset Function CategoryTheory
open scoped SetRel

universe u v

/-- The set of matchings for `t` when restricted to a `Finset` of `ι`. -/
/-
**hallMatchingsOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：hallMatchingsOn {ι : Type u} {α : Type v} (t : ι -> Finset α) (ι' : Finset
 ι)
参数：t : ι -> Finset α；ι' : Finset ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of matchings for `t` when restricted to a `Finset` of `ι`.
-/
def hallMatchingsOn {ι : Type u} {α : Type v} (t : ι → Finset α) (ι' : Finset ι) :=
  { f : ι' → α | Function.Injective f ∧ ∀ (x : {x // x ∈ ι'}), f x ∈ t x }

/-- Given a matching on a finset, construct the restriction of that matching to a subset. -/
/-
**hallMatchingsOn.restrict** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：hallMatchingsOn.restrict {ι : Type u} {α : Type v} (t : ι -> Finset α) {ι'
 ι'' : Finset ι} (h : ι' subseteq ι'') (f : hallMatchingsOn t ι'') : hallMatchin
gsOn t ι'
参数：t : ι -> Finset α；h : ι' subseteq ι''；f : hallMatchingsOn t ι''。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a matching on a finset, construct the restriction of that matching to a su
bset.
-/
def hallMatchingsOn.restrict {ι : Type u} {α : Type v} (t : ι → Finset α) {ι' ι'' : Finset ι}
    (h : ι' ⊆ ι'') (f : hallMatchingsOn t ι'') : hallMatchingsOn t ι' := by
  refine ⟨fun i => f.val ⟨i, h i.property⟩, ?_⟩
  obtain ⟨hinj, hc⟩ := f.property
  refine ⟨?_, fun i => hc ⟨i, h i.property⟩⟩
  rintro ⟨i, hi⟩ ⟨j, hj⟩ hh
  simpa only [Subtype.mk_eq_mk] using hinj hh

/-- When the Hall condition is satisfied, the set of matchings on a finite set is nonempty.
This is where `Finset.all_card_le_biUnion_card_iff_existsInjective'` comes into the argument. -/
/-
**hallMatchingsOn.nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hallMatchingsOn.nonempty {ι : Type u} {α : Type v} [DecidableEq α] (t : ι 
-> Finset α) (h : forall s : Finset ι, #s <= #(s.biUnion t)) (ι' : Finset ι) : N
onempty (hallMatchingsOn t ι')
参数：t : ι -> Finset α；h : forall s : Finset ι, #s <= #(s.biUnion t)；ι' : Finset ι
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.all_card_le_biUnion_card_iff_existsInjective'`：Finset.all_card_le
_biUnion_card_iff_existsInjective' {ι α : Type*} [Finite ι] [DecidableEq α] (t :
 ι -> Finset α) : (forall s : Finset ι, #s…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_image_of_injective`：card_image_of_injective [DecidableEq β] 
(s : Finset α) (H : Injective f) : #(s.image f) = #s
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.image_biUnion`：image_biUnion [DecidableEq γ] {f : α -> β} {s : Fi
nset α} {t : β -> Finset γ} : (s.image f).biUnion t = s.biUnion fun a => t (f a)

--- 原说明 ---
When the Hall condition is satisfied, the set of matchings on a finite set is no
nempty.
This is where `Finset.all_card_le_biUnion_card_iff_existsInjective'` comes into 
the argument.
-/
theorem hallMatchingsOn.nonempty {ι : Type u} {α : Type v} [DecidableEq α] (t : ι → Finset α)
    (h : ∀ s : Finset ι, #s ≤ #(s.biUnion t)) (ι' : Finset ι) :
    Nonempty (hallMatchingsOn t ι') := by
  classical
    refine ⟨Classical.indefiniteDescription _ ?_⟩
    apply (all_card_le_biUnion_card_iff_existsInjective' fun i : ι' => t i).mp
    intro s'
    convert! h (s'.image (↑)) using 1
    · simp only [card_image_of_injective s' Subtype.coe_injective]
    · rw [image_biUnion]

/-- This is the `hallMatchingsOn` sets assembled into a directed system.
-/
/-
**hallMatchingsFunctor** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：hallMatchingsFunctor {ι : Type u} {α : Type v} (t : ι -> Finset α) : (Fins
et ι)ᵒᵖ ⥤ Type (max u v) where obj ι'
参数：t : ι -> Finset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the `hallMatchingsOn` sets assembled into a directed system.
-/
def hallMatchingsFunctor {ι : Type u} {α : Type v} (t : ι → Finset α) :
    (Finset ι)ᵒᵖ ⥤ Type (max u v) where
  obj ι' := hallMatchingsOn t ι'.unop
  map {_ _} g := ↾(hallMatchingsOn.restrict t (CategoryTheory.leOfHom g.unop))
/-
**hallMatchingsOn.finite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：hallMatchingsOn.finite {ι : Type u} {α : Type v} (t : ι -> Finset α) (ι' :
 Finset ι) : Finite (hallMatchingsOn t ι')
参数：t : ι -> Finset α；ι' : Finset ι。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hallMatchingsOn.eq_1`：∀ {ι : Type u} {α : Type v} (t : ι → Finset α) (ι'
 : Finset ι),   hallMatchingsOn t ι' = {f | Function.Injective f ∧ ∀ (x : ↥ι'), 
f x ∈ t ↑x…
· 使用定理 `Finset.mem_biUnion`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t : 
α → Finset β} [inst : DecidableEq β] {b : β},   b ∈ s.biUnion t ↔ ∃ a ∈ s, b ∈ t
 a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
-/
instance hallMatchingsOn.finite {ι : Type u} {α : Type v} (t : ι → Finset α) (ι' : Finset ι) :
    Finite (hallMatchingsOn t ι') := by
  classical
    rw [hallMatchingsOn]
    let g : hallMatchingsOn t ι' → ι' → ι'.biUnion t := by
      rintro f i
      refine ⟨f.val i, ?_⟩
      rw [mem_biUnion]
      exact ⟨i, i.property, f.property.2 i⟩
    apply Finite.of_injective g
    intro f f' h
    ext a
    rw [funext_iff] at h
    simpa [g] using h a

/-- This is the version of **Hall's Marriage Theorem** in terms of indexed
families of finite sets `t : ι → Finset α`.  It states that there is a
set of distinct representatives if and only if every union of `k` of the
sets has at least `k` elements.

Recall that `s.biUnion t` is the union of all the sets `t i` for `i ∈ s`.

This theorem is bootstrapped from `Finset.all_card_le_biUnion_card_iff_exists_injective'`,
which has the additional constraint that `ι` is a `Fintype`.
-/
/-
**Finset.all_card_le_biUnion_card_iff_exists_injective** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：Finset.all_card_le_biUnion_card_iff_exists_injective {ι : Type u} {α : Typ
e v} [DecidableEq α] (t : ι -> Finset α) : (forall s : Finset ι, #s <= #(s.biUni
on t)) ↔ exists f : ι -> α, Function.Injective f ∧ forall x, f x in t x
参数：t : ι -> Finset α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hallMatchingsOn.nonempty`：hallMatchingsOn.nonempty {ι : Type u} {α : Typ
e v} [DecidableEq α] (t : ι -> Finset α) (h : forall s : Finset ι, #s <= #(s.biU
nion t)) (ι' :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hallMatchingsFunctor.eq_1`：∀ {ι : Type u} {α : Type v} (t : ι → Finset α
),   hallMatchingsFunctor t =     { obj := fun ι' => ↑(hallMatchingsOn t (Opposi
te.unop ι')),  …
· 使用定理 `nonempty_sections_of_finite_inverse_system`：nonempty_sections_of_finite_
inverse_system {J : Type u} [Preorder J] [IsDirectedOrder J] (F : Jᵒᵖ ⥤ Type v) 
[forall j : Jᵒᵖ, Finite (F.obj j…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.mk_eq_mk`：mk_eq_mk {a h a' h'} : @mk α p a h = @mk α p a' h' ↔ a
 = a'
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.card_image_of_injective`：card_image_of_injective [DecidableEq β] 
(s : Finset α) (H : Injective f) : #(s.image f) = #s
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t

--- 原说明 ---
This is the version of **Hall's Marriage Theorem** in terms of indexed
families of finite sets `t : ι → Finset α`.  It states that there is a
set of distinct representatives if and only if every union of `k` of the
sets has at least `k` elements.

Recall that `s.biUnion t` is the union of all the sets `t i` for `i ∈ s`.

This theorem is bootstrapped from `Finset.all_card_le_biUnion_card_iff_exists_in
jective'`,
which has the additional constraint that `ι` is a `Fintype`.
-/
theorem Finset.all_card_le_biUnion_card_iff_exists_injective {ι : Type u} {α : Type v}
    [DecidableEq α] (t : ι → Finset α) :
    (∀ s : Finset ι, #s ≤ #(s.biUnion t)) ↔
      ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x := by
  constructor
  · intro h
    -- Set up the functor
    have : ∀ ι' : (Finset ι)ᵒᵖ, Nonempty ((hallMatchingsFunctor t).obj ι') := fun ι' =>
      hallMatchingsOn.nonempty t h ι'.unop
    classical
      have : ∀ ι' : (Finset ι)ᵒᵖ, Finite ((hallMatchingsFunctor t).obj ι') := by
        intro ι'
        rw [hallMatchingsFunctor]
        infer_instance
      -- Apply the compactness argument
      obtain ⟨u, hu⟩ := nonempty_sections_of_finite_inverse_system (hallMatchingsFunctor t)
      -- Interpret the resulting section of the inverse limit
      refine ⟨?_, ?_, ?_⟩
      · -- Build the matching function from the section
        exact fun i =>
          (u (Opposite.op ({i} : Finset ι))).val ⟨i, by simp only [mem_singleton]⟩
      · -- Show that it is injective
        intro i i'
        have subi : ({i} : Finset ι) ⊆ {i, i'} := by simp
        have subi' : ({i'} : Finset ι) ⊆ {i, i'} := by simp
        simp only
        rw [← hu (CategoryTheory.homOfLE subi).op, ← hu (CategoryTheory.homOfLE subi').op]
        let uii' := u (Opposite.op ({i, i'} : Finset ι))
        exact fun h => Subtype.mk_eq_mk.mp (uii'.property.1 h)
      · -- Show that it maps each index to the corresponding finite set
        intro i
        apply (u (Opposite.op ({i} : Finset ι))).property.2
  · -- The reverse direction is a straightforward cardinality argument
    rintro ⟨f, hf₁, hf₂⟩ s
    rw [← Finset.card_image_of_injective s hf₁]
    apply Finset.card_le_card
    grind

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a relation such that the image of every singleton set is finite, then the image of every
finite set is finite. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a relation such that the image of every singleton set is finite, then the 
image of every
finite set is finite.
-/
instance {α : Type u} {β : Type v} [DecidableEq β] (R : SetRel α β)
    [∀ a : α, Fintype (R.image {a})] (A : Finset α) : Fintype (R.image A) := by
  have h : R.image A = (A.biUnion fun a => (R.image {a}).toFinset : Set β) := by
    ext
    simp [SetRel.image]
  rw [h]
  apply FinsetCoe.fintype

set_option backward.isDefEq.respectTransparency.types false in
/-- This is a version of **Hall's Marriage Theorem** in terms of a relation
between types `α` and `β` such that `α` is finite and the image of
each `x : α` is finite (it suffices for `β` to be finite; see
`Fintype.all_card_le_filter_rel_iff_exists_injective`).  There is
a transversal of the relation (an injective function `α → β` whose graph is
a subrelation of the relation) iff every subset of
`k` terms of `α` is related to at least `k` terms of `β`.

Note: if `[Fintype β]`, then there exist instances for `[∀ (a : α), Fintype (R.image {a})]`.
-/
/-
**Fintype.all_card_le_rel_image_card_iff_exists_injective** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：Fintype.all_card_le_rel_image_card_iff_exists_injective {α : Type u} {β : 
Type v} [DecidableEq β] (R : SetRel α β) [forall a : α, Fintype (R.image {a})] :
 (forall A : Finset α, #A <= Fintype.card (R.image A)) ↔ exists f : α -> β, Func
tion.Injective f ∧ forall x, x ~[R] f x
参数：R : SetRel α β；R.image {a}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.all_card_le_biUnion_card_iff_exists_injective`：Finset.all_card_le
_biUnion_card_iff_exists_injective {ι : Type u} {α : Type v} [DecidableEq α] (t 
: ι -> Finset α) : (forall s : Finset ι, #…

--- 原说明 ---
This is a version of **Hall's Marriage Theorem** in terms of a relation
between types `α` and `β` such that `α` is finite and the image of
each `x : α` is finite (it suffices for `β` to be finite; see
`Fintype.all_card_le_filter_rel_iff_exists_injective`).  There is
a transversal of the relation (an injective function `α → β` whose graph is
a subrelation of the relation) iff every subset of
`k` terms of `α` is related to at least `k` terms of `β`.

Note: if `[Fintype β]`, then there exist instances for `[∀ (a : α), Fintype (R.i
mage {a})]`.
-/
theorem Fintype.all_card_le_rel_image_card_iff_exists_injective {α : Type u} {β : Type v}
    [DecidableEq β] (R : SetRel α β) [∀ a : α, Fintype (R.image {a})] :
    (∀ A : Finset α, #A ≤ Fintype.card (R.image A)) ↔
      ∃ f : α → β, Function.Injective f ∧ ∀ x, x ~[R] f x := by
  let r' a := (R.image {a}).toFinset
  have h : ∀ A : Finset α, Fintype.card (R.image A) = #(A.biUnion r') := by
    intro A
    rw [← Set.toFinset_card]
    apply congr_arg
    ext b
    simp [r', SetRel.image]
  have h' : ∀ (f : α → β) (x), x ~[R] f x ↔ f x ∈ r' x := by simp [r', SetRel.image]
  simp only [h, h']
  apply Finset.all_card_le_biUnion_card_iff_exists_injective

/-- This is a version of **Hall's Marriage Theorem** in terms of a relation to a finite type.
There is a transversal of the relation (an injective function `α → β` whose graph is a subrelation
of the relation) iff every subset of `k` terms of `α` is related to at least `k` terms of `β`.

It is like `Fintype.all_card_le_rel_image_card_iff_exists_injective` but uses `Finset.filter`
rather than `Rel.image`.
-/
/-
**Fintype.all_card_le_filter_rel_iff_exists_injective** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：Fintype.all_card_le_filter_rel_iff_exists_injective {α : Type u} {β : Type
 v} [Fintype β] (r : α -> β -> Prop) [DecidableRel r] : (forall A : Finset α, #A
 <= #{b | exists a in A, r a b}) ↔ exists f : α -> β, Injective f ∧ forall x, r 
x (f x)
参数：r : α -> β -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.all_card_le_biUnion_card_iff_exists_injective`：Finset.all_card_le
_biUnion_card_iff_exists_injective {ι : Type u} {α : Type v} [DecidableEq α] (t 
: ι -> Finset α) : (forall s : Finset ι, #…

--- 原说明 ---
This is a version of **Hall's Marriage Theorem** in terms of a relation to a fin
ite type.
There is a transversal of the relation (an injective function `α → β` whose grap
h is a subrelation
of the relation) iff every subset of `k` terms of `α` is related to at least `k`
 terms of `β`.

It is like `Fintype.all_card_le_rel_image_card_iff_exists_injective` but uses `F
inset.filter`
rather than `Rel.image`.
-/
theorem Fintype.all_card_le_filter_rel_iff_exists_injective {α : Type u} {β : Type v} [Fintype β]
    (r : α → β → Prop) [DecidableRel r] :
    (∀ A : Finset α, #A ≤ #{b | ∃ a ∈ A, r a b}) ↔ ∃ f : α → β, Injective f ∧ ∀ x, r x (f x) := by
  have := Classical.decEq β
  let r' a : Finset β := {b | r a b}
  have h : ∀ A : Finset α, ({b | ∃ a ∈ A, r a b} : Finset _) = A.biUnion r' := by
    intro A
    ext b
    simp [r']
  have h' : ∀ (f : α → β) (x), r x (f x) ↔ f x ∈ r' x := by simp [r']
  simp_rw [h, h']
  apply Finset.all_card_le_biUnion_card_iff_exists_injective
