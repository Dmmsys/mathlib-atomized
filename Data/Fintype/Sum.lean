/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Sum
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Embedding.Set

/-!
## Instances

We provide the `Fintype` instance for the sum of two fintypes.
-/

@[expose] public section


universe u v

variable {α β : Type*}

open Finset

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type u) (β : Type v) [Fintype α] [Fintype β] : Fintype (α ⊕ β) where
  elems := univ.disjSum univ
  complete := by rintro (_ | _) <;> simp

namespace Finset
variable {α β : Type*} {u : Finset (α ⊕ β)} {s : Finset α} {t : Finset β}

section left
variable [Fintype α] {u : Finset (α ⊕ β)}

/-
**Finset.toLeft_eq_univ** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：toLeft_eq_univ : u.toLeft = univ ↔ univ.map .inl subseteq u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toLeft_eq_univ : u.toLeft = univ ↔ univ.map .inl ⊆ u := by
  simp [map_inl_subset_iff_subset_toLeft]
/-
**Finset.toRight_eq_empty** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：toRight_eq_empty : u.toRight = ∅ ↔ u subseteq univ.map .inl
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toRight_eq_empty : u.toRight = ∅ ↔ u ⊆ univ.map .inl := by simp [subset_map_inl]

end left

section right
variable [Fintype β] {u : Finset (α ⊕ β)}

/-
**Finset.toRight_eq_univ** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：toRight_eq_univ : u.toRight = univ ↔ univ.map .inr subseteq u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toRight_eq_univ : u.toRight = univ ↔ univ.map .inr ⊆ u := by
  simp [map_inr_subset_iff_subset_toRight]
/-
**Finset.toLeft_eq_empty** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：toLeft_eq_empty : u.toLeft = ∅ ↔ u subseteq univ.map .inr
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toLeft_eq_empty : u.toLeft = ∅ ↔ u ⊆ univ.map .inr := by simp [subset_map_inr]

end right

variable [Fintype α] [Fintype β]

/-
**Finset.univ_disjSum_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_3} {β : Type u_4} [inst : Fintype α] [inst_1 : Fintype β], F
inset.univ.disjSum Finset.univ = Finset.univ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma univ_disjSum_univ : univ.disjSum univ = (univ : Finset (α ⊕ β)) := rfl
/-
**Finset.toLeft_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_3} {β : Type u_4} [inst : Fintype α] [inst_1 : Fintype β], F
inset.univ.toLeft = Finset.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma toLeft_univ : (univ : Finset (α ⊕ β)).toLeft = univ := by ext; simp
/-
**Finset.toRight_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_3} {β : Type u_4} [inst : Fintype α] [inst_1 : Fintype β], F
inset.univ.toRight = Finset.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma toRight_univ : (univ : Finset (α ⊕ β)).toRight = univ := by ext; simp

end Finset

@[simp]
/-
**Fintype.card_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_sum [Fintype α] [Fintype β] : Fintype.card (α oplus β) = Fint
ype.card α + Fintype.card β
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_disjSum`：card_disjSum : (s.disjSum t).card = s.card + t.card
-/
theorem Fintype.card_sum [Fintype α] [Fintype β] :
    Fintype.card (α ⊕ β) = Fintype.card α + Fintype.card β :=
  card_disjSum _ _

/-- If the subtype of all-but-one elements is a `Fintype` then the type itself is a `Fintype`. -/
@[instance_reducible]
/-
**fintypeOfFintypeNe** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：fintypeOfFintypeNe (a : α) (_ : Fintype { b // b != a }) : Fintype α
参数：a : α；_ : Fintype { b // b != a }。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the subtype of all-but-one elements is a `Fintype` then the type itself is a 
`Fintype`.
-/
def fintypeOfFintypeNe (a : α) (_ : Fintype { b // b ≠ a }) : Fintype α :=
  Fintype.ofBijective (Sum.elim ((↑) : { b // b = a } → α) ((↑) : { b // b ≠ a } → α)) <| by
    classical exact (Equiv.sumCompl (· = a)).bijective
/-
**image_subtype_ne_univ_eq_image_erase** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：image_subtype_ne_univ_eq_image_erase [Fintype α] [DecidableEq β] (k : β) (
b : α -> β) : image (fun i : { a // b a != k } => b ↑i) univ = (image b univ).er
ase k
参数：k : β；b : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.image_subset_iff`：image_subset_iff : s.image f subseteq t ↔ foral
l x in s, f x in t
· 使用定理 `Finset.mem_erase_of_ne_of_mem`：mem_erase_of_ne_of_mem : a != b -> a in s
 -> a in erase s b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.erase_subset`：erase_subset (a : α) (s : Finset α) : erase s a sub
seteq s
· 使用定理 `Finset.ne_of_mem_erase`：ne_of_mem_erase : b in erase s a -> b != a
-/
theorem image_subtype_ne_univ_eq_image_erase [Fintype α] [DecidableEq β] (k : β) (b : α → β) :
    image (fun i : { a // b a ≠ k } => b ↑i) univ = (image b univ).erase k := by
  apply subset_antisymm
  · rw [image_subset_iff]
    intro i _
    apply mem_erase_of_ne_of_mem i.2 (mem_image_of_mem _ (mem_univ _))
  · intro i hi
    rw [mem_image]
    rcases mem_image.1 (erase_subset _ _ hi) with ⟨a, _, ha⟩
    subst ha
    exact ⟨⟨a, ne_of_mem_erase hi⟩, mem_univ _, rfl⟩
/-
**image_subtype_univ_ssubset_image_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：image_subtype_univ_ssubset_image_univ [Fintype α] [DecidableEq β] (k : β) 
(b : α -> β) (hk : k in Finset.image b univ) (p : β -> Prop) [DecidablePred p] (
hp : ¬p k) : image (fun i : { a // p (b a) } => b ↑i) univ ⊂ image b univ
参数：k : β；b : α -> β；hk : k in Finset.image b univ；p : β -> Prop；hp : ¬p k。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_subtype_univ_ssubset_image_univ [Fintype α] [DecidableEq β] (k : β) (b : α → β)
    (hk : k ∈ Finset.image b univ) (p : β → Prop) [DecidablePred p] (hp : ¬p k) :
    image (fun i : { a // p (b a) } => b ↑i) univ ⊂ image b univ := by
  grind

/-- Any injection from a finset `s` in a fintype `α` to a finset `t` of the same cardinality as `α`
can be extended to a bijection between `α` and `t`. -/
/-
**Finset.exists_equiv_extend_of_card_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.exists_equiv_extend_of_card_eq [Fintype α] [DecidableEq β] {t : Fin
set β} (hαt : Fintype.card α = #t) {s : Finset α} {f : α -> β} (hfst : Finset.im
age f s subseteq t) (hfs : Set.InjOn f s) : exists g : α ≃ t, forall i in s, (g 
i : β) = f i
参数：hαt : Fintype.card α = #t；hfst : Finset.image f s subseteq t；hfs : Set.InjOn 
f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_eq`：card_eq {α β} [_F : Fintype α] [_G : Fintype β] : card 
α = card β ↔ Nonempty (α ≃ β)
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.image_mono`：image_mono (f : α -> β) : Monotone (Finset.image f)
· 使用定理 `Finset.subset_insert`：∀ {α : Type u_1} [inst : DecidableEq α] (a : α) (s
 : Finset α), s ⊆ insert a s
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.swap_apply_right`：swap_apply_right (a b : α) : swap a b b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.trans_apply`：∀ {α : Sort u} {β : Sort v} {γ : Sort w} (f : α ≃ β) 
(g : β ≃ γ) (a : α), (f.trans g) a = g (f a)
· 使用定理 `Equiv.swap_apply_of_ne_of_ne`：swap_apply_of_ne_of_ne {a b x : α} : x != 
a -> x != b -> swap a b x = x
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用引理 `ne_of_eq_of_ne`：ne_of_eq_of_ne {α : Sort*} {a b c : α} (h₁ : a = b) (h₂ 
: b != c) : a != c
· 使用定理 `Set.InjOn.ne`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β} {x
 y : α}, Set.InjOn f s → x ∈ s → y ∈ s → x ≠ y → f x ≠ f y
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Any injection from a finset `s` in a fintype `α` to a finset `t` of the same car
dinality as `α`
can be extended to a bijection between `α` and `t`.
-/
theorem Finset.exists_equiv_extend_of_card_eq [Fintype α] [DecidableEq β] {t : Finset β}
    (hαt : Fintype.card α = #t) {s : Finset α} {f : α → β} (hfst : Finset.image f s ⊆ t)
    (hfs : Set.InjOn f s) : ∃ g : α ≃ t, ∀ i ∈ s, (g i : β) = f i := by
  classical
    induction s using Finset.induction generalizing f with
    | empty =>
      obtain ⟨e⟩ : Nonempty (α ≃ ↥t) := by rwa [← Fintype.card_eq, Fintype.card_coe]
      use e
      simp
    | insert a s has H => ?_
    have hfst' : Finset.image f s ⊆ t := (Finset.image_mono _ (s.subset_insert a)).trans hfst
    have hfs' : Set.InjOn f s := hfs.mono (s.subset_insert a)
    obtain ⟨g', hg'⟩ := H hfst' hfs'
    have hfat : f a ∈ t := hfst (mem_image_of_mem _ (s.mem_insert_self a))
    use g'.trans (Equiv.swap (⟨f a, hfat⟩ : t) (g' a))
    simp_rw [mem_insert]
    rintro i (rfl | hi)
    · simp
    rw [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne, hg' _ hi]
    · exact
        ne_of_apply_ne Subtype.val
          (ne_of_eq_of_ne (hg' _ hi) <|
            hfs.ne (subset_insert _ _ hi) (mem_insert_self _ _) <| ne_of_mem_of_not_mem hi has)
    · exact g'.injective.ne (ne_of_mem_of_not_mem hi has)

/-- Any injection from a set `s` in a fintype `α` to a finset `t` of the same cardinality as `α`
can be extended to a bijection between `α` and `t`. -/
/-
**Set.MapsTo.exists_equiv_extend_of_card_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.MapsTo.exists_equiv_extend_of_card_eq [Fintype α] {t : Finset β} (hαt 
: Fintype.card α = #t) {s : Set α} {f : α -> β} (hfst : s.MapsTo f t) (hfs : Set
.InjOn f s) : exists g : α ≃ t, forall i in s, (g i : β) = f i
参数：hαt : Fintype.card α = #t；hfst : s.MapsTo f t；hfs : Set.InjOn f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
· 使用定理 `Finset.exists_equiv_extend_of_card_eq`：Finset.exists_equiv_extend_of_car
d_eq [Fintype α] [DecidableEq β] {t : Finset β} (hαt : Fintype.card α = #t) {s :
 Finset α} {f : α -> β} (hf…

--- 原说明 ---
Any injection from a set `s` in a fintype `α` to a finset `t` of the same cardin
ality as `α`
can be extended to a bijection between `α` and `t`.
-/
theorem Set.MapsTo.exists_equiv_extend_of_card_eq [Fintype α] {t : Finset β}
    (hαt : Fintype.card α = #t) {s : Set α} {f : α → β} (hfst : s.MapsTo f t)
    (hfs : Set.InjOn f s) : ∃ g : α ≃ t, ∀ i ∈ s, (g i : β) = f i := by
  classical
    let s' : Finset α := s.toFinset
    have hfst' : s'.image f ⊆ t := by simpa [s', ← Finset.coe_subset] using! hfst
    have hfs' : Set.InjOn f s' := by simpa [s'] using! hfs
    obtain ⟨g, hg⟩ := Finset.exists_equiv_extend_of_card_eq hαt hfst' hfs'
    refine ⟨g, fun i hi => ?_⟩
    apply hg
    simpa [s'] using! hi
/-
**Fintype.card_subtype_or** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_subtype_or (p q : α -> Prop) [Fintype { x // p x }] [Fintype 
{ x // q x }] [Fintype { x // p x ∨ q x }] : Fintype.card { x // p x ∨ q x } <= 
Fintype.card { x // p x } + Fintype.card { x // q x }
参数：p q : α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_sum`：Fintype.card_sum [Fintype α] [Fintype β] : Fintype.car
d (α oplus β) = Fintype.card α + Fintype.card β
· 使用定理 `Fintype.card_le_of_embedding`：card_le_of_embedding (f : α ↪ β) : card α 
<= card β
-/
theorem Fintype.card_subtype_or (p q : α → Prop) [Fintype { x // p x }] [Fintype { x // q x }]
    [Fintype { x // p x ∨ q x }] :
    Fintype.card { x // p x ∨ q x } ≤ Fintype.card { x // p x } + Fintype.card { x // q x } := by
  classical
    convert! Fintype.card_le_of_embedding (subtypeOrLeftEmbedding p q)
    rw [Fintype.card_sum]
/-
**Fintype.card_subtype_or_disjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_subtype_or_disjoint (p q : α -> Prop) (h : Disjoint p q) [Fin
type { x // p x }] [Fintype { x // q x }] [Fintype { x // p x ∨ q x }] : Fintype
.card { x // p x ∨ q x } = Fintype.card { x // p x } + Fintype.card { x // q x }
参数：p q : α -> Prop；h : Disjoint p q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_sum`：Fintype.card_sum [Fintype α] [Fintype β] : Fintype.car
d (α oplus β) = Fintype.card α + Fintype.card β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
-/
theorem Fintype.card_subtype_or_disjoint (p q : α → Prop) (h : Disjoint p q) [Fintype { x // p x }]
    [Fintype { x // q x }] [Fintype { x // p x ∨ q x }] :
    Fintype.card { x // p x ∨ q x } = Fintype.card { x // p x } + Fintype.card { x // q x } := by
  classical
    convert! Fintype.card_congr (subtypeOrEquiv p q h)
    simp
/-
**Fintype.card_subtype_eq_or_eq_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_subtype_eq_or_eq_of_ne {α : Type*} [Fintype α] [DecidableEq α
] {a b : α} (h : a != b) : Fintype.card { c : α // c = a ∨ c = b } = 2
参数：h : a != b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_subtype_or_disjoint`：Fintype.card_subtype_or_disjoint (p q 
: α -> Prop) (h : Disjoint p q) [Fintype { x // p x }] [Fintype { x // q x }] [F
intype { x // p x ∨ q …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Fintype.card_subtype_eq_or_eq_of_ne {α : Type*} [Fintype α] [DecidableEq α] {a b : α}
    (h : a ≠ b) : Fintype.card { c : α // c = a ∨ c = b } = 2 :=
  Fintype.card_subtype_or_disjoint _ _ fun _ ha hb _ hc ↦ ha _ hc ▸ hb _ hc ▸ h <| rfl

attribute [local instance] Fintype.ofFinite in
@[simp]
/-
**infinite_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：infinite_sum : Infinite (α oplus β) ↔ Infinite α ∨ Infinite β
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
-/
theorem infinite_sum : Infinite (α ⊕ β) ↔ Infinite α ∨ Infinite β := by
  refine ⟨fun H => ?_, fun H => H.elim (@Sum.infinite_of_left α β) (@Sum.infinite_of_right α β)⟩
  contrapose! H; cases H
  infer_instance
