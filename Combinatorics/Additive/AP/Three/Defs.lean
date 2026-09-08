/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Order.Interval.Finset.Basic
public import Mathlib.Combinatorics.Additive.FreimanHom
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar

/-!
# Sets without arithmetic progressions of length three and Roth numbers

This file defines sets without arithmetic progressions of length three, aka 3AP-free sets, and the
Roth number of a set.

The corresponding notion, sets without geometric progressions of length three, are called 3GP-free
sets.

The Roth number of a finset is the size of its biggest 3AP-free subset. This is a more general
definition than the one often found in mathematical literature, where the `n`-th Roth number is
the size of the biggest 3AP-free subset of `{0, ..., n - 1}`.

## Main declarations

* `ThreeGPFree`: Predicate for a set to be 3GP-free.
* `ThreeAPFree`: Predicate for a set to be 3AP-free.
* `mulRothNumber`: The multiplicative Roth number of a finset.
* `addRothNumber`: The additive Roth number of a finset.
* `rothNumberNat`: The Roth number of a natural, namely `addRothNumber (Finset.range n)`.

## TODO

* Can `threeAPFree_iff_eq_right` be made more general?
* Generalize `ThreeGPFree.image` to Freiman homs

## References

* [Wikipedia, *Salem-Spencer set*](https://en.wikipedia.org/wiki/Salem–Spencer_set)

## Tags

3AP-free, Salem-Spencer, Roth, arithmetic progression, average, three-free
-/

@[expose] public section

assert_not_exists Field Ideal TwoSidedIdeal

open Finset Function
open scoped Pointwise

variable {F α β : Type*}

section ThreeAPFree

open Set

section Monoid

variable [Monoid α] [Monoid β] (s t : Set α)

/-- A set is **3GP-free** if it does not contain any non-trivial geometric progression of length
three. -/
@[to_additive /-- A set is **3AP-free** if it does not contain any non-trivial arithmetic
progression of length three.

This is also sometimes called a **non-averaging set** or **Salem-Spencer set**. -/]
/-
**ThreeGPFree** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ThreeGPFree : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ThreeGPFree : Prop := ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → ∀ ⦃c⦄, c ∈ s → a * c = b * b → a = b

/-- Whether a given finset is 3GP-free is decidable. -/
@[to_additive /-- Whether a given finset is 3AP-free is decidable. -/]
/-
**ThreeGPFree.instDecidable** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ThreeGPFree.instDecidable [DecidableEq α] {s : Finset α} : Decidable (Thre
eGPFree (s : Set α))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Whether a given finset is 3GP-free is decidable.
-/
instance ThreeGPFree.instDecidable [DecidableEq α] {s : Finset α} :
    Decidable (ThreeGPFree (s : Set α)) :=
  decidable_of_iff (∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a * c = b * b → a = b) Iff.rfl

variable {s t}

@[to_additive]
/-
**ThreeGPFree.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ThreeGPFree.mono (h : t subseteq s) (hs : ThreeGPFree s) : ThreeGPFree t
参数：h : t subseteq s；hs : ThreeGPFree s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ThreeGPFree.mono (h : t ⊆ s) (hs : ThreeGPFree s) : ThreeGPFree t :=
  fun _ ha _ hb _ hc ↦ hs (h ha) (h hb) (h hc)

@[to_additive (attr := simp)]
/-
**threeGPFree_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：threeGPFree_empty : ThreeGPFree (∅ : Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem threeGPFree_empty : ThreeGPFree (∅ : Set α) := fun _ _ _ ha => ha.elim

@[to_additive]
/-
**Set.Subsingleton.threeGPFree** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Subsingleton.threeGPFree (hs : s.Subsingleton) : ThreeGPFree s
参数：hs : s.Subsingleton。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Set.Subsingleton.threeGPFree (hs : s.Subsingleton) : ThreeGPFree s :=
  fun _ ha _ hb _ _ _ ↦ hs ha hb

@[to_additive (attr := simp)]
/-
**threeGPFree_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：threeGPFree_singleton (a : α) : ThreeGPFree ({a} : Set α)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.threeGPFree`：Set.Subsingleton.threeGPFree (hs : s.Subsi
ngleton) : ThreeGPFree s
· 使用定理 `Set.subsingleton_singleton`：subsingleton_singleton {a} : ({a} : Set α).S
ubsingleton
-/
theorem threeGPFree_singleton (a : α) : ThreeGPFree ({a} : Set α) :=
  subsingleton_singleton.threeGPFree

@[to_additive ThreeAPFree.prod]
/-
**ThreeGPFree.prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ThreeGPFree.prod {t : Set β} (hs : ThreeGPFree s) (ht : ThreeGPFree t) : T
hreeGPFree (s ×ˢ t)
参数：hs : ThreeGPFree s；ht : ThreeGPFree t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Prod.ext_iff`：∀ {α : Type u} {β : Type v} {x y : α × β}, x = y ↔ x.1 = y
.1 ∧ x.2 = y.2
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem ThreeGPFree.prod {t : Set β} (hs : ThreeGPFree s) (ht : ThreeGPFree t) :
    ThreeGPFree (s ×ˢ t) := fun _ ha _ hb _ hc h ↦
  Prod.ext (hs ha.1 hb.1 hc.1 (Prod.ext_iff.1 h).1) (ht ha.2 hb.2 hc.2 (Prod.ext_iff.1 h).2)

@[to_additive]
/-
**threeGPFree_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：threeGPFree_pi {ι : Type*} {α : ι -> Type*} [forall i, Monoid (α i)] {s : 
forall i, Set (α i)} (hs : forall i, ThreeGPFree (s i)) : ThreeGPFree ((univ : S
et ι).pi s)
参数：α i；α i；hs : forall i, ThreeGPFree (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `trivial`：True
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
theorem threeGPFree_pi {ι : Type*} {α : ι → Type*} [∀ i, Monoid (α i)] {s : ∀ i, Set (α i)}
    (hs : ∀ i, ThreeGPFree (s i)) : ThreeGPFree ((univ : Set ι).pi s) :=
  fun _ ha _ hb _ hc h ↦
  funext fun i => hs i (ha i trivial) (hb i trivial) (hc i trivial) <| congr_fun h i

end Monoid

section CommMonoid
variable [CommMonoid α] [CommMonoid β] {s A : Set α} {t : Set β} {f : α → β}

/-- Geometric progressions of length three are reflected under `2`-Freiman homomorphisms. -/
@[to_additive
/-- Arithmetic progressions of length three are reflected under `2`-Freiman homomorphisms. -/]
/-
**ThreeGPFree.of_image** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ThreeGPFree.of_image (hf : IsMulFreimanHom 2 s t f) (hf' : s.InjOn f) (hAs
 : A subseteq s) (hA : ThreeGPFree (f '' A)) : ThreeGPFree A
参数：hf : IsMulFreimanHom 2 s t f；hf' : s.InjOn f；hAs : A subseteq s；hA : ThreeGPF
ree (f '' A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用引理 `IsMulFreimanHom.mul_eq_mul`：IsMulFreimanHom.mul_eq_mul (hf : IsMulFreima
nHom 2 A B f) {a b c d : α} (ha : a in A) (hb : b in A) (hc : c in A) (hd : d in
 A) (h : a * b =…
-/
lemma ThreeGPFree.of_image (hf : IsMulFreimanHom 2 s t f) (hf' : s.InjOn f) (hAs : A ⊆ s)
    (hA : ThreeGPFree (f '' A)) : ThreeGPFree A :=
  fun _ ha _ hb _ hc habc ↦ hf' (hAs ha) (hAs hb) <| hA (mem_image_of_mem _ ha)
    (mem_image_of_mem _ hb) (mem_image_of_mem _ hc) <|
    hf.mul_eq_mul (hAs ha) (hAs hc) (hAs hb) (hAs hb) habc

/-- Geometric progressions of length three are unchanged under `2`-Freiman isomorphisms. -/
@[to_additive
/-- Arithmetic progressions of length three are unchanged under `2`-Freiman isomorphisms. -/]
/-
**threeGPFree_image** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：threeGPFree_image (hf : IsMulFreimanIso 2 s t f) (hAs : A subseteq s) : Th
reeGPFree (f '' A) ↔ ThreeGPFree A
参数：hf : IsMulFreimanIso 2 s t f；hAs : A subseteq s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ThreeGPFree.eq_1`：∀ {α : Type u_2} [inst : Monoid α] (s : Set α),   Thre
eGPFree s = ∀ ⦃a : α⦄, a ∈ s → ∀ ⦃b : α⦄, b ∈ s → ∀ ⦃c : α⦄, c ∈ s → a * c = b *
 b → a…
· 使用定理 `Set.InjOn.bijOn_image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : 
α → β}, Set.InjOn f s → Set.BijOn f s (f '' s)
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `Set.BijOn.injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
 {f : α → β}, Set.BijOn f s t → Set.InjOn f s
· 使用定理 `IsMulFreimanIso.bijOn`：∀ {α : Type u_2} {β : Type u_3} [inst : CommMonoi
d α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f : α → β}, IsMu
lFreimanIso…
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
· 使用引理 `IsMulFreimanIso.mul_eq_mul`：IsMulFreimanIso.mul_eq_mul (hf : IsMulFreima
nIso 2 A B f) {a b c d : α} (ha : a in A) (hb : b in A) (hc : c in A) (hd : d in
 A) : f a * f b …
· 使用定理 `Set.InjOn.eq_iff`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β
} {x y : α}, Set.InjOn f s → x ∈ s → y ∈ s → (f x = f y ↔ x = y)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma threeGPFree_image (hf : IsMulFreimanIso 2 s t f) (hAs : A ⊆ s) :
    ThreeGPFree (f '' A) ↔ ThreeGPFree A := by
  rw [ThreeGPFree, ThreeGPFree]
  have := (hf.bijOn.injOn.mono hAs).bijOn_image (f := f)
  simp +contextual only
    [((hf.bijOn.injOn.mono hAs).bijOn_image (f := f)).forall,
    hf.mul_eq_mul (hAs _) (hAs _) (hAs _) (hAs _), this.injOn.eq_iff]

@[to_additive] alias ⟨_, ThreeGPFree.image⟩ := threeGPFree_image

/-- Geometric progressions of length three are reflected under `2`-Freiman homomorphisms. -/
@[to_additive
/-- Arithmetic progressions of length three are reflected under `2`-Freiman homomorphisms. -/]
/-
**IsMulFreimanHom.threeGPFree** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMulFreimanHom.threeGPFree (hf : IsMulFreimanHom 2 s t f) (hf' : s.InjOn 
f) (ht : ThreeGPFree t) : ThreeGPFree s
参数：hf : IsMulFreimanHom 2 s t f；hf' : s.InjOn f；ht : ThreeGPFree t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ThreeGPFree.of_image`：ThreeGPFree.of_image (hf : IsMulFreimanHom 2 s t f
) (hf' : s.InjOn f) (hAs : A subseteq s) (hA : ThreeGPFree (f '' A)) : ThreeGPFr
ee A
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
· 使用定理 `ThreeGPFree.mono`：ThreeGPFree.mono (h : t subseteq s) (hs : ThreeGPFree 
s) : ThreeGPFree t
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
· 使用定理 `IsMulFreimanHom.mapsTo`：∀ {α : Type u_2} {β : Type u_3} [inst : CommMono
id α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f : α → β}, IsM
ulFreimanHom…
-/
lemma IsMulFreimanHom.threeGPFree (hf : IsMulFreimanHom 2 s t f) (hf' : s.InjOn f)
    (ht : ThreeGPFree t) : ThreeGPFree s :=
  (ht.mono hf.mapsTo.image_subset).of_image hf hf' subset_rfl

/-- Geometric progressions of length three are unchanged under `2`-Freiman isomorphisms. -/
@[to_additive
/-- Arithmetic progressions of length three are unchanged under `2`-Freiman isomorphisms. -/]
/-
**IsMulFreimanIso.threeGPFree_congr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMulFreimanIso.threeGPFree_congr (hf : IsMulFreimanIso 2 s t f) : ThreeGP
Free s ↔ ThreeGPFree t
参数：hf : IsMulFreimanIso 2 s t f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `threeGPFree_image`：threeGPFree_image (hf : IsMulFreimanIso 2 s t f) (hAs
 : A subseteq s) : ThreeGPFree (f '' A) ↔ ThreeGPFree A
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
· 使用定理 `Set.BijOn.image_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set
 β} {f : α → β}, Set.BijOn f s t → f '' s = t
· 使用定理 `IsMulFreimanIso.bijOn`：∀ {α : Type u_2} {β : Type u_3} [inst : CommMonoi
d α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f : α → β}, IsMu
lFreimanIso…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma IsMulFreimanIso.threeGPFree_congr (hf : IsMulFreimanIso 2 s t f) :
    ThreeGPFree s ↔ ThreeGPFree t := by
  rw [← threeGPFree_image hf subset_rfl, hf.bijOn.image_eq]

/-- Geometric progressions of length three are preserved under semigroup homomorphisms. -/
@[to_additive
/-- Arithmetic progressions of length three are preserved under semigroup homomorphisms. -/]
/-
**ThreeGPFree.image'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ThreeGPFree.image' [FunLike F α β] [MulHomClass F α β] (f : F) (hf : (s * 
s).InjOn f) (h : ThreeGPFree s) : ThreeGPFree (f '' s)
参数：f : F；hf : (s * s).InjOn f；h : ThreeGPFree s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mul_mem_mul`：mul_mem_mul : a in s -> b in t -> a * b in s * t
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
-/
theorem ThreeGPFree.image' [FunLike F α β] [MulHomClass F α β] (f : F) (hf : (s * s).InjOn f)
    (h : ThreeGPFree s) : ThreeGPFree (f '' s) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ habc
  rw [h ha hb hc (hf (mul_mem_mul ha hc) (mul_mem_mul hb hb) <| by rwa [map_mul, map_mul])]

end CommMonoid

section CancelCommMonoid

variable [CommMonoid α] [IsCancelMul α] {s : Set α} {a : α}

/-
**ThreeGPFree.eq_right** 是 Mathlib 中的一个定理，位于命名空间 `ThreeGPFree`。
形式化陈述：∀ {α : Type u_2} [inst : CommMonoid α] [IsCancelMul α] {s : Set α},   Thre
eGPFree s → ∀ ⦃a : α⦄, a ∈ s → ∀ ⦃b : α⦄, b ∈ s → ∀ ⦃c : α⦄, c ∈ s → a * c = b *
 b → b = c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCancelMul.toIsLeftCancelMul`：∀ {G : Type u} {inst : Mul G} [self : IsC
ancelMul G], IsLeftCancelMul G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[to_additive] lemma ThreeGPFree.eq_right (hs : ThreeGPFree s) :
    ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → ∀ ⦃c⦄, c ∈ s → a * c = b * b → b = c := by
  rintro a ha b hb c hc habc
  obtain rfl := hs ha hb hc habc
  simpa using habc.symm
/-
**threeGPFree_insert** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} [inst : CommMonoid α] [IsCancelMul α] {s : Set α} {a : α}
,   ThreeGPFree (insert a s) ↔     ThreeGPFree s ∧       (∀ ⦃b : α⦄, b ∈ s → ∀ ⦃
c : α⦄, c ∈ s → a * c = b * b → a = b) ∧         ∀ ⦃b : α⦄, b ∈ s → ∀ ⦃c : α⦄, c
 ∈ s → b * c = a * a → b = a
参数：insert a s；∀ ⦃b : α⦄, b ∈ s → ∀ ⦃c : α⦄, c ∈ s → a * c = b * b → a = b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ThreeGPFree.mono`：ThreeGPFree.mono (h : t subseteq s) (hs : ThreeGPFree 
s) : ThreeGPFree t
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_insert_iff`：mem_insert_iff {x a : α} {s : Set α} : x in insert a
 s ↔ x = a ∨ x in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_right_cancel`：mul_right_cancel : a * b = c * b -> a = c
· 使用定理 `IsCancelMul.toIsRightCancelMul`：∀ {G : Type u} {inst : Mul G} [self : Is
CancelMul G], IsRightCancelMul G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
@[to_additive] lemma threeGPFree_insert :
    ThreeGPFree (insert a s) ↔ ThreeGPFree s ∧
      (∀ ⦃b⦄, b ∈ s → ∀ ⦃c⦄, c ∈ s → a * c = b * b → a = b) ∧
        ∀ ⦃b⦄, b ∈ s → ∀ ⦃c⦄, c ∈ s → b * c = a * a → b = a := by
  refine ⟨fun hs ↦ ⟨hs.mono (subset_insert _ _),
    fun b hb c hc ↦ hs (Or.inl rfl) (Or.inr hb) (Or.inr hc),
    fun b hb c hc ↦ hs (Or.inr hb) (Or.inl rfl) (Or.inr hc)⟩, ?_⟩
  rintro ⟨hs, ha, ha'⟩ b hb c hc d hd h
  rw [mem_insert_iff] at hb hc hd
  obtain rfl | hb := hb <;> obtain rfl | hc := hc
  · rfl
  all_goals obtain rfl | hd := hd
  · exact (ha' hc hc h.symm).symm
  · exact ha hc hd h
  · exact mul_right_cancel h
  · exact ha' hb hd h
  · obtain rfl := ha hc hb ((mul_comm _ _).trans h)
    exact ha' hb hc h
  · exact hs hb hc hd h

@[to_additive]
/-
**ThreeGPFree.smul_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ThreeGPFree.smul_set (hs : ThreeGPFree s) : ThreeGPFree (a • s)
参数：hs : ThreeGPFree s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用定理 `IsCancelMul.toIsLeftCancelMul`：∀ {G : Type u} {inst : Mul G} [self : IsC
ancelMul G], IsLeftCancelMul G
-/
theorem ThreeGPFree.smul_set (hs : ThreeGPFree s) : ThreeGPFree (a • s) := by
  rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩ h
  exact congr_arg (a • ·) <| hs hb hc hd <| by simpa [mul_mul_mul_comm _ _ a] using h
/-
**threeGPFree_smul_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} [inst : CommMonoid α] [IsCancelMul α] {s : Set α} {a : α}
, ThreeGPFree (a • s) ↔ ThreeGPFree s
参数：a • s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_left_cancel`：mul_left_cancel : a * b = a * c -> b = c
· 使用定理 `IsCancelMul.toIsLeftCancelMul`：∀ {G : Type u} {inst : Mul G} [self : IsC
ancelMul G], IsLeftCancelMul G
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `ThreeGPFree.smul_set`：ThreeGPFree.smul_set (hs : ThreeGPFree s) : ThreeG
PFree (a • s)
-/
@[to_additive] lemma threeGPFree_smul_set : ThreeGPFree (a • s) ↔ ThreeGPFree s where
  mp hs b hb c hc d hd h := mul_left_cancel
      (hs (mem_image_of_mem _ hb) (mem_image_of_mem _ hc) (mem_image_of_mem _ hd) <| by
        rw [mul_mul_mul_comm, smul_eq_mul, smul_eq_mul, mul_mul_mul_comm, h])
  mpr := ThreeGPFree.smul_set

end CancelCommMonoid

section OrderedCancelCommMonoid

variable [CommMonoid α] [PartialOrder α] [IsOrderedCancelMonoid α] {s : Set α} {a : α}

@[to_additive]
/-
**threeGPFree_insert_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：threeGPFree_insert_of_lt (hs : forall i in s, i < a) : ThreeGPFree (insert
 a s) ↔ ThreeGPFree s ∧ forall ⦃b⦄, b in s -> forall ⦃c⦄, c in s -> a * c = b * 
b -> a = b
参数：hs : forall i in s, i < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `threeGPFree_insert`：∀ {α : Type u_2} [inst : CommMonoid α] [IsCancelMul 
α] {s : Set α} {a : α},   ThreeGPFree (insert a s) ↔     ThreeGPFree s ∧       (
∀ ⦃b : α…
· 使用定理 `IsOrderedCancelMonoid.toIsCancelMul`：∀ {α : Type u_1} [inst : CommMonoid
 α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], IsCancelMul α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_assoc`：∀ {a b c : Prop}, (a ∧ b) ∧ c ↔ a ∧ b ∧ c
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `mul_lt_mul_of_lt_of_lt`：mul_lt_mul_of_lt_of_lt [MulLeftStrictMono α] [Mu
lRightStrictMono α] {a b c d : α} (h₁ : a < b) (h₂ : c < d) : a * c < b * d
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLE`：∀ {α : Type u_2} [inst : CommM
onoid α] [inst_1 : Preorder α] [IsOrderedCancelMonoid α], MulLeftReflectLE α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `IsOrderedCancelMonoid.toIsOrderedMonoid`：∀ {α : Type u_2} {inst : CommMo
noid α} {inst_1 : Preorder α} [self : IsOrderedCancelMonoid α], IsOrderedMonoid 
α
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `IsCancelMul.toIsLeftCancelMul`：∀ {G : Type u} {inst : Mul G} [self : IsC
ancelMul G], IsLeftCancelMul G
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLT`：∀ {α : Type u_1} [inst : CommM
onoid α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], MulLeftReflectLT α
-/
theorem threeGPFree_insert_of_lt (hs : ∀ i ∈ s, i < a) :
    ThreeGPFree (insert a s) ↔
      ThreeGPFree s ∧ ∀ ⦃b⦄, b ∈ s → ∀ ⦃c⦄, c ∈ s → a * c = b * b → a = b := by
  refine threeGPFree_insert.trans ?_
  rw [← and_assoc]
  exact and_iff_left fun b hb c hc h => ((mul_lt_mul_of_lt_of_lt (hs _ hb) (hs _ hc)).ne h).elim

end OrderedCancelCommMonoid

section CancelCommMonoidWithZero

variable [CommMonoidWithZero α] [IsCancelMulZero α] [NoZeroDivisors α] {s : Set α} {a : α}

/-
**ThreeGPFree.smul_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ThreeGPFree.smul_set (hs : ThreeGPFree s) : ThreeGPFree (a • s)
参数：hs : ThreeGPFree s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用定理 `IsCancelMul.toIsLeftCancelMul`：∀ {G : Type u} {inst : Mul G} [self : IsC
ancelMul G], IsLeftCancelMul G
-/
lemma ThreeGPFree.smul_set₀ (hs : ThreeGPFree s) (ha : a ≠ 0) : ThreeGPFree (a • s) := by
  rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩ h
  exact congr_arg (a • ·) <| hs hb hc hd <| by simpa [mul_mul_mul_comm _ _ a, ha] using h
/-
**threeGPFree_smul_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_2} [inst : CommMonoid α] [IsCancelMul α] {s : Set α} {a : α}
, ThreeGPFree (a • s) ↔ ThreeGPFree s
参数：a • s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_left_cancel`：mul_left_cancel : a * b = a * c -> b = c
· 使用定理 `IsCancelMul.toIsLeftCancelMul`：∀ {G : Type u} {inst : Mul G} [self : IsC
ancelMul G], IsLeftCancelMul G
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `ThreeGPFree.smul_set`：ThreeGPFree.smul_set (hs : ThreeGPFree s) : ThreeG
PFree (a • s)
-/
theorem threeGPFree_smul_set₀ (ha : a ≠ 0) : ThreeGPFree (a • s) ↔ ThreeGPFree s :=
  ⟨fun hs b hb c hc d hd h ↦
    mul_left_cancel₀ ha
      (hs (Set.mem_image_of_mem _ hb) (Set.mem_image_of_mem _ hc) (Set.mem_image_of_mem _ hd) <| by
        rw [smul_eq_mul, smul_eq_mul, mul_mul_mul_comm, h, mul_mul_mul_comm]),
    fun hs => hs.smul_set₀ ha⟩

end CancelCommMonoidWithZero

section Nat

/-
**threeAPFree_iff_eq_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：threeAPFree_iff_eq_right {s : Set Nat} : ThreeAPFree s ↔ forall ⦃a⦄, a in 
s -> forall ⦃b⦄, b in s -> forall ⦃c⦄, c in s -> a + c = b + b -> a = c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₄_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → 
Sort u_3} {δ : (a : α) → (b : β a) → γ a b → Sort u_4}   {p q : (a : α) → (b : β
 a)…
· 使用定理 `forall₃_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → 
Sort u_3} {p q : (a : α) → (b : β a) → γ a b → Prop},   (∀ (a : α) (b : β a) (c 
: γ…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_left_cancel`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] {a 
b c : G}, a + b = a + c → b = c
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `mul_left_cancel₀`：mul_left_cancel₀ (ha : a != 0) (h : a * b = a * c) : b
 = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem threeAPFree_iff_eq_right {s : Set ℕ} :
    ThreeAPFree s ↔ ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → ∀ ⦃c⦄, c ∈ s → a + c = b + b → a = c := by
  refine forall₄_congr fun a _ha b hb => forall₃_congr fun c hc habc => ⟨?_, ?_⟩
  · rintro rfl
    exact (add_left_cancel habc).symm
  · rintro rfl
    simp_rw [← two_mul] at habc
    exact mul_left_cancel₀ two_ne_zero habc

end Nat
end ThreeAPFree

open Finset

section RothNumber

variable [DecidableEq α]

section Monoid

variable [Monoid α] [DecidableEq β] [Monoid β] (s t : Finset α)

/-- The multiplicative Roth number of a finset is the cardinality of its biggest 3GP-free subset. -/
@[to_additive /-- The additive Roth number of a finset is the cardinality of its biggest 3AP-free
subset.

The usual Roth number corresponds to `addRothNumber (Finset.range n)`, see `rothNumberNat`. -/]
/-
**mulRothNumber** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：mulRothNumber : Finset α ->o Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mulRothNumber : Finset α →o ℕ :=
  ⟨fun s ↦ Nat.findGreatest (fun m ↦ ∃ t ⊆ s, #t = m ∧ ThreeGPFree (t : Set α)) #s, by
    rintro t u htu
    refine Nat.findGreatest_mono (fun m => ?_) (card_le_card htu)
    rintro ⟨v, hvt, hv⟩
    exact ⟨v, hvt.trans htu, hv⟩⟩

@[to_additive]
/-
**mulRothNumber_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulRothNumber_le : mulRothNumber s <= #s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.findGreatest_le`：findGreatest_le (n : Nat) : Nat.findGreatest P n <=
 n
-/
theorem mulRothNumber_le : mulRothNumber s ≤ #s := Nat.findGreatest_le #s

@[to_additive]
/-
**mulRothNumber_spec** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulRothNumber_spec : exists t subseteq s, #t = mulRothNumber s ∧ ThreeGPFr
ee (t : Set α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.findGreatest_spec`：findGreatest_spec (hmb : m <= n) (hm : P m) : P (
Nat.findGreatest P n)
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Finset.empty_subset`：empty_subset (s : Finset α) : ∅ subseteq s
· 使用定理 `Finset.card_empty`：card_empty : #(∅ : Finset α) = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `threeGPFree_empty`：threeGPFree_empty : ThreeGPFree (∅ : Set α)
-/
theorem mulRothNumber_spec :
    ∃ t ⊆ s, #t = mulRothNumber s ∧ ThreeGPFree (t : Set α) :=
  Nat.findGreatest_spec (P := fun m ↦ ∃ t ⊆ s, #t = m ∧ ThreeGPFree (t : Set α))
    (Nat.zero_le _) ⟨∅, empty_subset _, card_empty, by norm_cast; exact threeGPFree_empty⟩

variable {s t} {n : ℕ}

@[to_additive]
/-
**ThreeGPFree.le_mulRothNumber** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ThreeGPFree.le_mulRothNumber (hs : ThreeGPFree (s : Set α)) (h : s subsete
q t) : #s <= mulRothNumber t
参数：hs : ThreeGPFree (s : Set α)；h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.le_findGreatest`：le_findGreatest (hmb : m <= n) (hm : P m) : m <= Na
t.findGreatest P n
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
-/
theorem ThreeGPFree.le_mulRothNumber (hs : ThreeGPFree (s : Set α)) (h : s ⊆ t) :
    #s ≤ mulRothNumber t :=
  Nat.le_findGreatest (card_le_card h) ⟨s, h, rfl, hs⟩

@[to_additive]
/-
**ThreeGPFree.mulRothNumber_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ThreeGPFree.mulRothNumber_eq (hs : ThreeGPFree (s : Set α)) : mulRothNumbe
r s = #s
参数：hs : ThreeGPFree (s : Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `mulRothNumber_le`：mulRothNumber_le : mulRothNumber s <= #s
· 使用定理 `ThreeGPFree.le_mulRothNumber`：ThreeGPFree.le_mulRothNumber (hs : ThreeGP
Free (s : Set α)) (h : s subseteq t) : #s <= mulRothNumber t
· 使用定理 `Finset.Subset.refl`：∀ {α : Type u_1} (s : Finset α), s ⊆ s
-/
theorem ThreeGPFree.mulRothNumber_eq (hs : ThreeGPFree (s : Set α)) :
    mulRothNumber s = #s :=
  (mulRothNumber_le _).antisymm <| hs.le_mulRothNumber <| Subset.refl _

@[to_additive (attr := simp)]
/-
**mulRothNumber_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulRothNumber_empty : mulRothNumber (∅ : Finset α) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_of_le_zero`：∀ {n : ℕ}, n ≤ 0 → n = 0
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mulRothNumber_le`：mulRothNumber_le : mulRothNumber s <= #s
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Finset.card_empty`：card_empty : #(∅ : Finset α) = 0
-/
theorem mulRothNumber_empty : mulRothNumber (∅ : Finset α) = 0 :=
  Nat.eq_zero_of_le_zero <| (mulRothNumber_le _).trans card_empty.le

@[to_additive (attr := simp)]
/-
**mulRothNumber_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulRothNumber_singleton (a : α) : mulRothNumber ({a} : Finset α) = 1
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ThreeGPFree.mulRothNumber_eq`：ThreeGPFree.mulRothNumber_eq (hs : ThreeGP
Free (s : Set α)) : mulRothNumber s = #s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `threeGPFree_singleton`：threeGPFree_singleton (a : α) : ThreeGPFree ({a} 
: Set α)
-/
theorem mulRothNumber_singleton (a : α) : mulRothNumber ({a} : Finset α) = 1 := by
  refine ThreeGPFree.mulRothNumber_eq ?_
  rw [coe_singleton]
  exact threeGPFree_singleton a

@[to_additive]
/-
**mulRothNumber_union_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulRothNumber_union_le (s t : Finset α) : mulRothNumber (s union t) <= mul
RothNumber s + mulRothNumber t
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mulRothNumber_spec`：mulRothNumber_spec : exists t subseteq s, #t = mulRo
thNumber s ∧ ThreeGPFree (t : Set α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.inter_union_distrib_left`：inter_union_distrib_left (s t u : Finse
t α) : s inter (t union u) = s inter t union s inter u
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.inter_eq_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Fin
set α}, s ∩ t = s ↔ s ⊆ t
· 使用定理 `Finset.card_union_le`：card_union_le (s t : Finset α) : #(s union t) <= #
s + #t
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `ThreeGPFree.le_mulRothNumber`：ThreeGPFree.le_mulRothNumber (hs : ThreeGP
Free (s : Set α)) (h : s subseteq t) : #s <= mulRothNumber t
· 使用定理 `ThreeGPFree.mono`：ThreeGPFree.mono (h : t subseteq s) (hs : ThreeGPFree 
s) : ThreeGPFree t
· 使用定理 `Finset.inter_subset_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ∩ s₂ ⊆ s₁
· 使用定理 `Finset.inter_subset_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s
₂ : Finset α}, s₁ ∩ s₂ ⊆ s₂
-/
theorem mulRothNumber_union_le (s t : Finset α) :
    mulRothNumber (s ∪ t) ≤ mulRothNumber s + mulRothNumber t :=
  let ⟨u, hus, hcard, hu⟩ := mulRothNumber_spec (s ∪ t)
  calc
    mulRothNumber (s ∪ t) = #u := hcard.symm
    _ = #(u ∩ s ∪ u ∩ t) := by rw [← inter_union_distrib_left, inter_eq_left.2 hus]
    _ ≤ #(u ∩ s) + #(u ∩ t) := card_union_le _ _
    _ ≤ mulRothNumber s + mulRothNumber t := _root_.add_le_add
      ((hu.mono inter_subset_left).le_mulRothNumber inter_subset_right)
      ((hu.mono inter_subset_left).le_mulRothNumber inter_subset_right)

@[to_additive]
/-
**le_mulRothNumber_product** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_mulRothNumber_product (s : Finset α) (t : Finset β) : mulRothNumber s *
 mulRothNumber t <= mulRothNumber (s ×ˢ t)
参数：s : Finset α；t : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mulRothNumber_spec`：mulRothNumber_spec : exists t subseteq s, #t = mulRo
thNumber s ∧ ThreeGPFree (t : Set α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_product`：card_product (s : Finset α) (t : Finset β) : card (
s ×ˢ t) = card s * card t
· 使用定理 `ThreeGPFree.le_mulRothNumber`：ThreeGPFree.le_mulRothNumber (hs : ThreeGP
Free (s : Set α)) (h : s subseteq t) : #s <= mulRothNumber t
· 使用定理 `Finset.coe_product`：coe_product (s : Finset α) (t : Finset β) : (↑(s ×ˢ 
t) : Set (α × β)) = (s : Set α) ×ˢ t
· 使用定理 `ThreeGPFree.prod`：ThreeGPFree.prod {t : Set β} (hs : ThreeGPFree s) (ht 
: ThreeGPFree t) : ThreeGPFree (s ×ˢ t)
· 使用定理 `Finset.product_subset_product`：product_subset_product (hs : s subseteq s
') (ht : t subseteq t') : s ×ˢ t subseteq s' ×ˢ t'
-/
theorem le_mulRothNumber_product (s : Finset α) (t : Finset β) :
    mulRothNumber s * mulRothNumber t ≤ mulRothNumber (s ×ˢ t) := by
  obtain ⟨u, hus, hucard, hu⟩ := mulRothNumber_spec s
  obtain ⟨v, hvt, hvcard, hv⟩ := mulRothNumber_spec t
  rw [← hucard, ← hvcard, ← card_product]
  refine ThreeGPFree.le_mulRothNumber ?_ (product_subset_product hus hvt)
  rw [coe_product]
  exact hu.prod hv

@[to_additive]
/-
**mulRothNumber_lt_of_forall_not_threeGPFree** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulRothNumber_lt_of_forall_not_threeGPFree (h : forall t in powersetCard n
 s, ¬ThreeGPFree ((t : Finset α) : Set α)) : mulRothNumber s < n
参数：h : forall t in powersetCard n s, ¬ThreeGPFree ((t : Finset α) : Set α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mulRothNumber_spec`：mulRothNumber_spec : exists t subseteq s, #t = mulRo
thNumber s ∧ ThreeGPFree (t : Set α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用引理 `Finset.exists_subset_card_eq`：exists_subset_card_eq (hns : n <= #s) : ex
ists t subseteq s, #t = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_powersetCard`：∀ {α : Type u_1} {n : ℕ} {s t : Finset α}, s ∈ 
Finset.powersetCard n t ↔ s ⊆ t ∧ s.card = n
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `ThreeGPFree.mono`：ThreeGPFree.mono (h : t subseteq s) (hs : ThreeGPFree 
s) : ThreeGPFree t
-/
theorem mulRothNumber_lt_of_forall_not_threeGPFree
    (h : ∀ t ∈ powersetCard n s, ¬ThreeGPFree ((t : Finset α) : Set α)) :
    mulRothNumber s < n := by
  obtain ⟨t, hts, hcard, ht⟩ := mulRothNumber_spec s
  rw [← hcard, ← not_le]
  intro hn
  obtain ⟨u, hut, rfl⟩ := exists_subset_card_eq hn
  exact h _ (mem_powersetCard.2 ⟨hut.trans hts, rfl⟩) (ht.mono hut)

end Monoid

section CommMonoid
variable [CommMonoid α] [CommMonoid β] [DecidableEq β] {A : Finset α} {B : Finset β} {f : α → β}

/-- Arithmetic progressions can be pushed forward along bijective 2-Freiman homs. -/
@[to_additive /-- Arithmetic progressions can be pushed forward along bijective 2-Freiman homs. -/]
/-
**IsMulFreimanHom.mulRothNumber_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMulFreimanHom.mulRothNumber_mono (hf : IsMulFreimanHom 2 A B f) (hf' : S
et.BijOn f A B) : mulRothNumber B <= mulRothNumber A
参数：hf : IsMulFreimanHom 2 A B f；hf' : Set.BijOn f A B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mulRothNumber_spec`：mulRothNumber_spec : exists t subseteq s, #t = mulRo
thNumber s ∧ ThreeGPFree (t : Set α)
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
· 使用定理 `Set.MapsTo.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t₁ t₂ 
: Set β} {f : α → β},   Set.MapsTo f s₁ t₁ → s₂ ⊆ s₁ → t₁ ⊆ t₂ → Set.MapsTo f s₂
 t₂
· 使用定理 `Set.SurjOn.mapsTo_invFunOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} 
{t : Set β} {f : α → β} [inst : Nonempty α],   Set.SurjOn f s t → Set.MapsTo (Fu
nction.invFunOn …
· 使用定理 `Set.BijOn.surjOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.SurjOn f s t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `Finset.Subset.rfl`：∀ {α : Type u_1} {s : Finset α}, s ⊆ s
· 使用定理 `Set.SurjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t₁ t₂ 
: Set β} {f : α → β},   s₁ ⊆ s₂ → t₁ ⊆ t₂ → Set.SurjOn f s₁ t₂ → Set.SurjOn f s₂
 t₁
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_image_of_injOn`：card_image_of_injOn [DecidableEq β] (H : Set
.InjOn f s) : #(s.image f) = #s
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `Function.invFunOn_injOn_image`：∀ {α : Type u_1} {β : Type u_2} [inst : N
onempty α] (f : α → β) (s : Set α), Set.InjOn (Function.invFunOn f s) (f '' s)
· 使用定理 `ThreeGPFree.le_mulRothNumber`：ThreeGPFree.le_mulRothNumber (hs : ThreeGP
Free (s : Set α)) (h : s subseteq t) : #s <= mulRothNumber t
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用引理 `IsMulFreimanHom.threeGPFree`：IsMulFreimanHom.threeGPFree (hf : IsMulFrei
manHom 2 s t f) (hf' : s.InjOn f) (ht : ThreeGPFree t) : ThreeGPFree s
· 使用定理 `IsMulFreimanHom.subset`：∀ {α : Type u_2} {β : Type u_3} [inst : CommMono
id α] [inst_1 : CommMonoid β] {A₁ A₂ : Set α} {B₁ B₂ : Set β}   {f : α → β} {n :
 ℕ}, A₁ ⊆ A₂…
· 使用定理 `Set.BijOn.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.MapsTo f s t
· 使用定理 `Set.SurjOn.bijOn_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β} [inst : Nonempty α],   Set.SurjOn f s t → Set.BijOn f (Func
tion.invFunOn…
· 使用定理 `Set.BijOn.injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
 {f : α → β}, Set.BijOn f s t → Set.InjOn f s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B

--- 原说明 ---
Arithmetic progressions can be pushed forward along bijective 2-Freiman homs.
-/
lemma IsMulFreimanHom.mulRothNumber_mono (hf : IsMulFreimanHom 2 A B f) (hf' : Set.BijOn f A B) :
    mulRothNumber B ≤ mulRothNumber A := by
  obtain ⟨s, hsB, hcard, hs⟩ := mulRothNumber_spec B
  have hsA : invFunOn f A '' s ⊆ A :=
    (hf'.surjOn.mapsTo_invFunOn.mono (coe_subset.2 hsB) Subset.rfl).image_subset
  have hfsA : Set.SurjOn f A s := hf'.surjOn.mono Subset.rfl (coe_subset.2 hsB)
  rw [← hcard, ← s.card_image_of_injOn ((invFunOn_injOn_image f _).mono hfsA)]
  refine ThreeGPFree.le_mulRothNumber ?_ (mod_cast hsA)
  rw [coe_image]
  simpa using (hf.subset hsA hfsA.bijOn_subset.mapsTo).threeGPFree (hf'.injOn.mono hsA) hs

/-- Arithmetic progressions are preserved under 2-Freiman isos. -/
@[to_additive /-- Arithmetic progressions are preserved under 2-Freiman isos. -/]
/-
**IsMulFreimanIso.mulRothNumber_congr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMulFreimanIso.mulRothNumber_congr (hf : IsMulFreimanIso 2 A B f) : mulRo
thNumber A = mulRothNumber B
参数：hf : IsMulFreimanIso 2 A B f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `mulRothNumber_spec`：mulRothNumber_spec : exists t subseteq s, #t = mulRo
thNumber s ∧ ThreeGPFree (t : Set α)
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `Set.BijOn.injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
 {f : α → β}, Set.BijOn f s t → Set.InjOn f s
· 使用定理 `IsMulFreimanIso.bijOn`：∀ {α : Type u_2} {β : Type u_3} [inst : CommMonoi
d α] [inst_1 : CommMonoid β] {n : ℕ} {A : Set α} {B : Set β}   {f : α → β}, IsMu
lFreimanIso…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `IsMulFreimanIso.threeGPFree_congr`：IsMulFreimanIso.threeGPFree_congr (hf
 : IsMulFreimanIso 2 s t f) : ThreeGPFree s ↔ ThreeGPFree t
· 使用定理 `IsMulFreimanIso.subset`：∀ {α : Type u_2} {β : Type u_3} [inst : CommMono
id α] [inst_1 : CommMonoid β] {A₁ A₂ : Set α} {B₁ B₂ : Set β}   {f : α → β} {n :
 ℕ}, A₁ ⊆ A₂…
· 使用定理 `Set.InjOn.bijOn_image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : 
α → β}, Set.InjOn f s → Set.BijOn f s (f '' s)
· 使用定理 `Finset.card_image_of_injOn`：card_image_of_injOn [DecidableEq β] (H : Set
.InjOn f s) : #(s.image f) = #s
· 使用定理 `ThreeGPFree.le_mulRothNumber`：ThreeGPFree.le_mulRothNumber (hs : ThreeGP
Free (s : Set α)) (h : s subseteq t) : #s <= mulRothNumber t
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
· 使用定理 `Set.MapsTo.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t₁ t₂ 
: Set β} {f : α → β},   Set.MapsTo f s₁ t₁ → s₂ ⊆ s₁ → t₁ ⊆ t₂ → Set.MapsTo f s₂
 t₂
· 使用定理 `Set.BijOn.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.MapsTo f s t
· 使用定理 `Finset.Subset.rfl`：∀ {α : Type u_1} {s : Finset α}, s ⊆ s
· 使用引理 `IsMulFreimanHom.mulRothNumber_mono`：IsMulFreimanHom.mulRothNumber_mono (
hf : IsMulFreimanHom 2 A B f) (hf' : Set.BijOn f A B) : mulRothNumber B <= mulRo
thNumber A
· 使用引理 `IsMulFreimanIso.isMulFreimanHom`：IsMulFreimanIso.isMulFreimanHom (hf : I
sMulFreimanIso n A B f) : IsMulFreimanHom n A B f where mapsTo

--- 原说明 ---
Arithmetic progressions are preserved under 2-Freiman isos.
-/
lemma IsMulFreimanIso.mulRothNumber_congr (hf : IsMulFreimanIso 2 A B f) :
    mulRothNumber A = mulRothNumber B := by
  refine le_antisymm ?_ (hf.isMulFreimanHom.mulRothNumber_mono hf.bijOn)
  obtain ⟨s, hsA, hcard, hs⟩ := mulRothNumber_spec A
  rw [← coe_subset] at hsA
  have hfs : Set.InjOn f s := hf.bijOn.injOn.mono hsA
  have := (hf.subset hsA hfs.bijOn_image).threeGPFree_congr.1 hs
  rw [← coe_image] at this
  rw [← hcard, ← Finset.card_image_of_injOn hfs]
  refine this.le_mulRothNumber ?_
  rw [← coe_subset, coe_image]
  exact (hf.bijOn.mapsTo.mono hsA Subset.rfl).image_subset

end CommMonoid

section CancelCommMonoid

variable [CancelCommMonoid α] (s : Finset α) (a : α)

@[to_additive (attr := simp)]
/-
**mulRothNumber_map_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulRothNumber_map_mul_left : mulRothNumber (s.map <| mulLeftEmbedding a) =
 mulRothNumber s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `mulRothNumber_spec`：mulRothNumber_spec : exists t subseteq s, #t = mulRo
thNumber s ∧ ThreeGPFree (t : Set α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.subset_map_iff`：subset_map_iff {f : α ↪ β} {s : Finset β} {t : Fi
nset α} : s subseteq t.map f ↔ exists u subseteq t, s = u.map f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `ThreeGPFree.le_mulRothNumber`：ThreeGPFree.le_mulRothNumber (hs : ThreeGP
Free (s : Set α)) (h : s subseteq t) : #s <= mulRothNumber t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `threeGPFree_smul_set`：∀ {α : Type u_2} [inst : CommMonoid α] [IsCancelMu
l α] {s : Set α} {a : α}, ThreeGPFree (a • s) ↔ ThreeGPFree s
· 使用定理 `CancelMonoid.toIsCancelMul`：∀ (M : Type u) [inst : CancelMonoid M], IsCa
ncelMul M
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `ThreeGPFree.smul_set`：ThreeGPFree.smul_set (hs : ThreeGPFree s) : ThreeG
PFree (a • s)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.map_subset_map`：map_subset_map {s₁ s₂ : Finset α} : s₁.map f subs
eteq s₂.map f ↔ s₁ subseteq s₂
-/
theorem mulRothNumber_map_mul_left :
    mulRothNumber (s.map <| mulLeftEmbedding a) = mulRothNumber s := by
  refine le_antisymm ?_ ?_
  · obtain ⟨u, hus, hcard, hu⟩ := mulRothNumber_spec (s.map <| mulLeftEmbedding a)
    rw [subset_map_iff] at hus
    obtain ⟨u, hus, rfl⟩ := hus
    rw [coe_map] at hu
    rw [← hcard, card_map]
    exact (threeGPFree_smul_set.1 hu).le_mulRothNumber hus
  · obtain ⟨u, hus, hcard, hu⟩ := mulRothNumber_spec s
    have h : ThreeGPFree (u.map <| mulLeftEmbedding a : Set α) := by rw [coe_map]; exact hu.smul_set
    convert! h.le_mulRothNumber (map_subset_map.2 hus) using 1
    rw [card_map, hcard]

@[to_additive (attr := simp)]
/-
**mulRothNumber_map_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulRothNumber_map_mul_right : mulRothNumber (s.map <| mulRightEmbedding a)
 = mulRothNumber s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
· 使用定理 `IsCancelMul.toIsLeftCancelMul`：∀ {G : Type u} {inst : Mul G} [self : IsC
ancelMul G], IsLeftCancelMul G
· 使用定理 `CancelMonoid.toIsCancelMul`：∀ (M : Type u) [inst : CancelMonoid M], IsCa
ncelMul M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCancelMul.toIsRightCancelMul`：∀ {G : Type u} {inst : Mul G} [self : Is
CancelMul G], IsRightCancelMul G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mulLeftEmbedding_eq_mulRightEmbedding`：mulLeftEmbedding_eq_mulRightEmbed
ding [CommMagma G] [IsCancelMul G] (g : G) : mulLeftEmbedding g = mulRightEmbedd
ing g
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `mulRothNumber_map_mul_left`：mulRothNumber_map_mul_left : mulRothNumber (
s.map <| mulLeftEmbedding a) = mulRothNumber s
-/
theorem mulRothNumber_map_mul_right :
    mulRothNumber (s.map <| mulRightEmbedding a) = mulRothNumber s := by
  rw [← mulLeftEmbedding_eq_mulRightEmbedding, mulRothNumber_map_mul_left s a]

end CancelCommMonoid

end RothNumber

section rothNumberNat

variable {k n : ℕ}

/-- The Roth number of a natural `N` is the largest integer `m` for which there is a subset of
`range N` of size `m` with no arithmetic progression of length 3.
Trivially, `rothNumberNat N ≤ N`, but Roth's theorem (proved in 1953) shows that
`rothNumberNat N = o(N)` and the construction by Behrend gives a lower bound of the form
`N * exp(-C sqrt(log(N))) ≤ rothNumberNat N`.
A significant refinement of Roth's theorem by Bloom and Sisask announced in 2020 gives
`rothNumberNat N = O(N / (log N)^(1+c))` for an absolute constant `c`. -/
/-
**rothNumberNat** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：rothNumberNat : Nat ->o Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Roth number of a natural `N` is the largest integer `m` for which there is a
 subset of
`range N` of size `m` with no arithmetic progression of length 3.
Trivially, `rothNumberNat N ≤ N`, but Roth's theorem (proved in 1953) shows that
`rothNumberNat N = o(N)` and the construction by Behrend gives a lower bound of 
the form
`N * exp(-C sqrt(log(N))) ≤ rothNumberNat N`.
A significant refinement of Roth's theorem by Bloom and Sisask announced in 2020
 gives
`rothNumberNat N = O(N / (log N)^(1+c))` for an absolute constant `c`.
-/
def rothNumberNat : ℕ →o ℕ :=
  ⟨fun n => addRothNumber (range n), addRothNumber.mono.comp range_mono⟩
/-
**rothNumberNat_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rothNumberNat_def (n : Nat) : rothNumberNat n = addRothNumber (range n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rothNumberNat_def (n : ℕ) : rothNumberNat n = addRothNumber (range n) :=
  rfl
/-
**rothNumberNat_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rothNumberNat_le (N : Nat) : rothNumberNat N <= N
参数：N : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `addRothNumber_le`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : AddM
onoid α] (s : Finset α), addRothNumber s ≤ s.card
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
-/
theorem rothNumberNat_le (N : ℕ) : rothNumberNat N ≤ N :=
  (addRothNumber_le _).trans (card_range _).le
/-
**rothNumberNat_spec** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rothNumberNat_spec (n : Nat) : exists t subseteq range n, #t = rothNumberN
at n ∧ ThreeAPFree (t : Set Nat)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `addRothNumber_spec`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Ad
dMonoid α] (s : Finset α),   ∃ t ⊆ s, t.card = addRothNumber s ∧ ThreeAPFree ↑t
-/
theorem rothNumberNat_spec (n : ℕ) :
    ∃ t ⊆ range n, #t = rothNumberNat n ∧ ThreeAPFree (t : Set ℕ) :=
  addRothNumber_spec _

/-- A verbose specialization of `threeAPFree.le_addRothNumber`, sometimes convenient in
practice. -/
/-
**ThreeAPFree.le_rothNumberNat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ThreeAPFree.le_rothNumberNat (s : Finset Nat) (hs : ThreeAPFree (s : Set N
at)) (hsn : forall x in s, x < n) (hsk : #s = k) : k <= rothNumberNat n
参数：s : Finset Nat；hs : ThreeAPFree (s : Set Nat)；hsn : forall x in s, x < n；hsk 
: #s = k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `ThreeAPFree.le_addRothNumber`：∀ {α : Type u_2} [inst : DecidableEq α] [i
nst_1 : AddMonoid α] {s t : Finset α},   ThreeAPFree ↑s → s ⊆ t → s.card ≤ addRo
thNumber t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n

--- 原说明 ---
A verbose specialization of `threeAPFree.le_addRothNumber`, sometimes convenient
 in
practice.
-/
theorem ThreeAPFree.le_rothNumberNat (s : Finset ℕ) (hs : ThreeAPFree (s : Set ℕ))
    (hsn : ∀ x ∈ s, x < n) (hsk : #s = k) : k ≤ rothNumberNat n :=
  hsk.ge.trans <| hs.le_addRothNumber fun x hx => mem_range.2 <| hsn x hx

/-- The Roth number is a subadditive function. Note that by Fekete's lemma this shows that
the limit `rothNumberNat N / N` exists, but Roth's theorem gives the stronger result that this
limit is actually `0`. -/
/-
**rothNumberNat_add_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rothNumberNat_add_le (M N : Nat) : rothNumberNat (M + N) <= rothNumberNat 
M + rothNumberNat N
参数：M N : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.range_add_eq_union`：range_add_eq_union : range (a + b) = range a 
union (range b).map (addLeftEmbedding a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `addRothNumber_map_add_left`：∀ {α : Type u_2} [inst : DecidableEq α] [ins
t_1 : AddCancelCommMonoid α] (s : Finset α) (a : α),   addRothNumber (Finset.map
 (addLeftEmbeddi…
· 使用定理 `addRothNumber_union_le`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 
: AddMonoid α] (s t : Finset α),   addRothNumber (s ∪ t) ≤ addRothNumber s + add
RothNumber t

--- 原说明 ---
The Roth number is a subadditive function. Note that by Fekete's lemma this show
s that
the limit `rothNumberNat N / N` exists, but Roth's theorem gives the stronger re
sult that this
limit is actually `0`.
-/
theorem rothNumberNat_add_le (M N : ℕ) :
    rothNumberNat (M + N) ≤ rothNumberNat M + rothNumberNat N := by
  simp_rw [rothNumberNat_def]
  rw [range_add_eq_union, ← addRothNumber_map_add_left (range N) M]
  exact addRothNumber_union_le _ _

@[simp]
/-
**rothNumberNat_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rothNumberNat_zero : rothNumberNat 0 = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rothNumberNat_zero : rothNumberNat 0 = 0 :=
  rfl
/-
**addRothNumber_Ico** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：addRothNumber_Ico (a b : Nat) : addRothNumber (Ico a b) = rothNumberNat (b
 - a)
参数：a b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `Finset.Ico_eq_empty_of_le`：Ico_eq_empty_of_le (h : b <= a) : Ico a b = ∅
· 使用定理 `rothNumberNat_zero`：rothNumberNat_zero : rothNumberNat 0 = 0
· 使用定理 `addRothNumber_empty`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : A
ddMonoid α], addRothNumber ∅ = 0
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.range_eq_Ico`：∀ (a : ℕ), Finset.range a = Finset.Ico 0 a
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.image_add_left_Ico`：∀ {α : Type u_2} [inst : AddCommMonoid α] [in
st_1 : PartialOrder α] [IsOrderedCancelAddMonoid α] [ExistsAddOfLE α]   [inst_4 
: LocallyFinite…
· 使用定理 `addRothNumber_map_add_left`：∀ {α : Type u_2} [inst : DecidableEq α] [ins
t_1 : AddCancelCommMonoid α] (s : Finset α) (a : α),   addRothNumber (Finset.map
 (addLeftEmbeddi…
-/
theorem addRothNumber_Ico (a b : ℕ) : addRothNumber (Ico a b) = rothNumberNat (b - a) := by
  obtain h | h := le_total b a
  · rw [Nat.sub_eq_zero_of_le h, Ico_eq_empty_of_le h, rothNumberNat_zero, addRothNumber_empty]
  convert! addRothNumber_map_add_left _ a
  rw [range_eq_Ico, map_eq_image]
  convert! (image_add_left_Ico 0 (b - a) _).symm
  exact (add_tsub_cancel_of_le h).symm
/-
**Fin.addRothNumber_eq_rothNumberNat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Fin.addRothNumber_eq_rothNumberNat {k : Fin (n + 1)} (hkn : 2 * k <= n) : 
addRothNumber (Iio k : Finset (Fin n.succ)) = rothNumberNat k
参数：n + 1；hkn : 2 * k <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAddFreimanIso.addRothNumber_congr`：∀ {α : Type u_2} {β : Type u_3} [in
st : DecidableEq α] [inst_1 : AddCommMonoid α] [inst_2 : AddCommMonoid β]   [ins
t_3 : DecidableEq β] {A :…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.cast_val_eq_self`：∀ {n : ℕ} (a : Fin n), ↑↑a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.coe_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iio a) = Set.Iio a
· 使用定理 `Finset.coe_range`：coe_range (n : Nat) : (range n : Set Nat) = Set.Iio n
· 使用引理 `Fin.isAddFreimanIso_Iio`：isAddFreimanIso_Iio (hm : m != 0) (hkmn : m * k
 <= n) : IsAddFreimanIso m (Iio (k : Fin (n + 1))) (Iio k) val
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
-/
lemma Fin.addRothNumber_eq_rothNumberNat {k : Fin (n + 1)} (hkn : 2 * k ≤ n) :
    addRothNumber (Iio k : Finset (Fin n.succ)) = rothNumberNat k :=
  IsAddFreimanIso.addRothNumber_congr <| mod_cast isAddFreimanIso_Iio two_ne_zero hkn
/-
**Fin.addRothNumber_le_rothNumberNat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Fin.addRothNumber_le_rothNumberNat {n : Nat} (k : Fin (n + 1)) : addRothNu
mber (Iio k : Finset (Fin n.succ)) <= rothNumberNat k
参数：k : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_range`：coe_range (n : Nat) : (range n : Set Nat) = Set.Iio n
· 使用定理 `Finset.coe_Iio`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] (a : α), ↑(Finset.Iio a) = Set.Iio a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Fin.cast_val_eq_self`：∀ {n : ℕ} (a : Fin n), ↑↑a = a
· 使用引理 `Fin.natCast_strictMono`：natCast_strictMono (hbn : b <= n) (hab : a < b) 
: (a : Fin (n + 1)) < b
· 使用定理 `Fin.is_le`：∀ {n : ℕ} (i : Fin (n + 1)), ↑i ≤ n
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CharP.natCast_injOn_Iio`：natCast_injOn_Iio : (Set.Iio p).InjOn ((↑) : Na
t -> R)
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsAddFreimanHom.addRothNumber_mono`：∀ {α : Type u_2} {β : Type u_3} [ins
t : DecidableEq α] [inst_1 : AddCommMonoid α] [inst_2 : AddCommMonoid β]   [inst
_3 : DecidableEq β] {A :…
· 使用定理 `AddHomClass.isAddFreimanHom`：∀ {F : Type u_1} {α : Type u_2} {β : Type u
_3} [inst : AddCommMonoid α] [inst_1 : AddCommMonoid β] {A : Set α}   {B : Set β
} {n : ℕ} [inst_2…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Set.BijOn.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.MapsTo f s t
-/
lemma Fin.addRothNumber_le_rothNumberNat {n : ℕ} (k : Fin (n + 1)) :
    addRothNumber (Iio k : Finset (Fin n.succ)) ≤ rothNumberNat k := by
  open Fin.CommRing in -- TODO: should this be refactored to avoid needing the coercion?
  suffices h : Set.BijOn (Nat.cast : ℕ → Fin n.succ) (range k) (Iio k : Finset (Fin n.succ)) by
    exact (AddHomClass.isAddFreimanHom (Nat.castRingHom _) h.mapsTo).addRothNumber_mono h
  refine ⟨?_, (CharP.natCast_injOn_Iio _ n.succ).mono (by simp), ?_⟩
  · simpa using! fun x ↦ natCast_strictMono (is_le k)
  simp only [Set.SurjOn, coe_Iio, Set.subset_def, Set.mem_Iio, Set.mem_image, lt_def, coe_range]
  exact fun x hx ↦ ⟨x, hx, by simp⟩

end rothNumberNat

