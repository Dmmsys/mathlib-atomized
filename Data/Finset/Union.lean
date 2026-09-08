/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Fold
public import Mathlib.Data.Multiset.Bind
public import Mathlib.Order.SetNotation

/-!
# Unions of finite sets

This file defines the union of a family `t : α → Finset β` of finsets bounded by a finset
`s : Finset α`.

## Main declarations

* `Finset.disjUnion`: Given a hypothesis `h` which states that finsets `s` and `t` are disjoint,
  `s.disjUnion t h` is the set such that `a ∈ disjUnion s t h` iff `a ∈ s` or `a ∈ t`; this does
  not require decidable equality on the type `α`.
* `Finset.biUnion`: Finite unions of finsets; given an indexing function `f : α → Finset β` and an
  `s : Finset α`, `s.biUnion f` is the union of all finsets of the form `f a` for `a ∈ s`.

## TODO

Remove `Finset.biUnion` in favour of `Finset.sup`.
-/

@[expose] public section

assert_not_exists MonoidWithZero MulAction

variable {α β γ : Type*} {s s₁ s₂ : Finset α} {t t₁ t₂ : α → Finset β}

namespace Finset
section DisjiUnion

/-- `disjiUnion s f h` is the set such that `a ∈ disjiUnion s f` iff `a ∈ f i` for some `i ∈ s`.
It is the same as `s.biUnion f`, but it does not require decidable equality on the type. The
hypothesis ensures that the sets are disjoint. -/
/-
**Finset.disjiUnion** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：disjiUnion (s : Finset α) (t : α -> Finset β) (hf : (s : Set α).PairwiseDi
sjoint t) : Finset β
参数：s : Finset α；t : α -> Finset β；hf : (s : Set α).PairwiseDisjoint t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`disjiUnion s f h` is the set such that `a ∈ disjiUnion s f` iff `a ∈ f i` for s
ome `i ∈ s`.
It is the same as `s.biUnion f`, but it does not require decidable equality on t
he type. The
hypothesis ensures that the sets are disjoint.
-/
def disjiUnion (s : Finset α) (t : α → Finset β) (hf : (s : Set α).PairwiseDisjoint t) : Finset β :=
  ⟨s.val.bind (Finset.val ∘ t), Multiset.nodup_bind.2
    ⟨fun a _ ↦ (t a).nodup, s.nodup.pairwise fun _ ha _ hb hab ↦ disjoint_val.2 <| hf ha hb hab⟩⟩

@[simp]
/-
**Finset.disjiUnion_val** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：disjiUnion_val (s : Finset α) (t : α -> Finset β) (h) : (s.disjiUnion t h)
.1 = s.1.bind fun a => (t a).1
参数：s : Finset α；t : α -> Finset β；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma disjiUnion_val (s : Finset α) (t : α → Finset β) (h) :
    (s.disjiUnion t h).1 = s.1.bind fun a ↦ (t a).1 := rfl
/-
**Finset.disjiUnion_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (t : α → Finset β), ∅.disjiUnion t ⋯ = ∅
参数：t : α → Finset β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma disjiUnion_empty (t : α → Finset β) : disjiUnion ∅ t (by simp) = ∅ := rfl
/-
**Finset.mem_disjiUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t : α → Finset β} {b : β} 
{h : (↑s).PairwiseDisjoint t},   b ∈ s.disjiUnion t h ↔ ∃ a ∈ s, b ∈ t a
参数：↑s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp, grind =] lemma mem_disjiUnion {b : β} {h} : b ∈ s.disjiUnion t h ↔ ∃ a ∈ s, b ∈ t a := by
  simp only [mem_def, disjiUnion_val, Multiset.mem_bind]

@[simp, norm_cast]
/-
**Finset.coe_disjiUnion** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：coe_disjiUnion {h} : (s.disjiUnion t h : Set β) = ⋃ x in (s : Set α), t x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma coe_disjiUnion {h} : (s.disjiUnion t h : Set β) = ⋃ x ∈ (s : Set α), t x := by
  simp [Set.ext_iff, mem_disjiUnion, Set.mem_iUnion]
/-
**Finset.disjiUnion_cons** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (a : α) (s : Finset α) (ha : a ∉ s) (f : α
 → Finset β)   (H : (↑(Finset.cons a s ha)).PairwiseDisjoint f),   (Finset.cons 
a s ha).disjiUnion f H = (f a).disjUnion (s.disjiUnion f ⋯) ⋯
参数：a : α；s : Finset α；ha : a ∉ s；f : α → Finset β；H : (↑(Finset.cons a s ha)).Pa
irwiseDisjoint f；Finset.cons a s ha；f a；s.disjiUnion f ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `Finset.mem_cons_of_mem`：mem_cons_of_mem {a b : α} {s : Finset α} {hb : b
 ∉ s} (ha : a in s) : a in cons b s hb
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_disjiUnion`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t
 : α → Finset β} {b : β} {h : (↑s).PairwiseDisjoint t},   b ∈ s.disjiUnion t h ↔
 ∃ a ∈ s, b…
· 使用定理 `Finset.mem_cons_self`：mem_cons_self (a : α) (s : Finset α) {h} : a in co
ns a s h
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `Multiset.cons_bind`：cons_bind : (a ::ₘ s).bind f = f a + s.bind f
-/
@[simp] lemma disjiUnion_cons (a : α) (s : Finset α) (ha : a ∉ s) (f : α → Finset β) (H) :
    disjiUnion (cons a s ha) f H =
    (f a).disjUnion ((s.disjiUnion f) fun _ hb _ hc ↦ H (mem_cons_of_mem hb) (mem_cons_of_mem hc))
      (disjoint_left.2 fun _ hb h ↦
        let ⟨_, hc, h⟩ := mem_disjiUnion.mp h
        disjoint_left.mp
          (H (mem_cons_self a s) (mem_cons_of_mem hc) (ne_of_mem_of_not_mem hc ha).symm) hb h) :=
  eq_of_veq <| Multiset.cons_bind _ _ _
/-
**Finset.singleton_disjiUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {t : α → Finset β} (a : α) {h : (↑{a}).Pai
rwiseDisjoint t}, {a}.disjiUnion t h = t a
参数：a : α；↑{a}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `Multiset.singleton_bind`：singleton_bind : bind {a} f = f a
-/
@[simp] lemma singleton_disjiUnion (a : α) {h} : Finset.disjiUnion {a} t h = t a :=
  eq_of_veq <| Multiset.singleton_bind _ _
/-
**Finset.disjiUnion_disjiUnion** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：disjiUnion_disjiUnion (s : Finset α) (f : α -> Finset β) (g : β -> Finset 
γ) (h1 h2) : (s.disjiUnion f h1).disjiUnion g h2 = s.attach.disjiUnion (fun a =>
 ((f a).disjiUnion g) fun _ hb _ hc => h2 (mem_disjiUnion.mpr ⟨_, a.prop, hb⟩) (
mem_disjiUnion.mpr ⟨_, a.prop, hc⟩)) fun a _ b _ hab => disjoint_left.mpr fun x 
hxa hxb => by obtain ⟨xa, hfa, hga⟩
参数：s : Finset α；f : α -> Finset β；g : β -> Finset γ；h1 h2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_disjiUnion`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t
 : α → Finset β} {b : β} {h : (↑s).PairwiseDisjoint t},   b ∈ s.disjiUnion t h ↔
 ∃ a ∈ s, b…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.bind_assoc`：bind_assoc {s : Multiset α} {f : α -> Multiset β} {
g : β -> Multiset γ} : (s.bind f).bind g = s.bind fun a => (f a).bind g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.attach_bind_coe`：attach_bind_coe (s : Multiset α) (f : α -> Mul
tiset β) : (s.attach.bind fun i => f i) = s.bind f
-/
lemma disjiUnion_disjiUnion (s : Finset α) (f : α → Finset β) (g : β → Finset γ) (h1 h2) :
    (s.disjiUnion f h1).disjiUnion g h2 =
      s.attach.disjiUnion
        (fun a ↦ ((f a).disjiUnion g) fun _ hb _ hc ↦
            h2 (mem_disjiUnion.mpr ⟨_, a.prop, hb⟩) (mem_disjiUnion.mpr ⟨_, a.prop, hc⟩))
        fun a _ b _ hab ↦
        disjoint_left.mpr fun x hxa hxb ↦ by
          obtain ⟨xa, hfa, hga⟩ := mem_disjiUnion.mp hxa
          obtain ⟨xb, hfb, hgb⟩ := mem_disjiUnion.mp hxb
          refine disjoint_left.mp
            (h2 (mem_disjiUnion.mpr ⟨_, a.prop, hfa⟩) (mem_disjiUnion.mpr ⟨_, b.prop, hfb⟩) ?_) hga
            hgb
          rintro rfl
          exact disjoint_left.mp (h1 a.prop b.prop <| Subtype.coe_injective.ne hab) hfa hfb :=
  eq_of_veq <| Multiset.bind_assoc.trans (Multiset.attach_bind_coe _ _).symm
/-
**Finset.sUnion_disjiUnion** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sUnion_disjiUnion {f : α -> Finset (Set β)} (I : Finset α) (hf : (I : Set 
α).PairwiseDisjoint f) : ⋃₀ (I.disjiUnion f hf : Set (Set β)) = ⋃ a in I, ⋃₀ ↑(f
 a)
参数：Set β；I : Finset α；hf : (I : Set α).PairwiseDisjoint f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.coe_disjiUnion`：coe_disjiUnion {h} : (s.disjiUnion t h : Set β) =
 ⋃ x in (s : Set α), t x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
-/
lemma sUnion_disjiUnion {f : α → Finset (Set β)} (I : Finset α)
    (hf : (I : Set α).PairwiseDisjoint f) :
    ⋃₀ (I.disjiUnion f hf : Set (Set β)) = ⋃ a ∈ I, ⋃₀ ↑(f a) := by
  ext
  simp only [coe_disjiUnion, Set.mem_sUnion, Set.mem_iUnion, mem_coe, exists_prop]
  tauto

section DecidableEq

variable [DecidableEq β] {s : Finset α} {t : Finset β} {f : α → β}

set_option backward.privateInPublic true in
/-
**Finset.pairwiseDisjoint_fibers** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma pairwiseDisjoint_fibers : Set.PairwiseDisjoint ↑t fun a ↦ s.filter (f · = a) :=
  fun x' hx y' hy hne ↦ by
    simp_rw [disjoint_left, mem_filter]; rintro i ⟨_, rfl⟩ ⟨_, rfl⟩; exact hne rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Finset.disjiUnion_filter_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : DecidableEq β] (s : Finset α) (t :
 Finset β) (f : α → β),   t.disjiUnion (fun a => {x ∈ s | f x = a}) ⋯ = {c ∈ s |
 f c ∈ t}
参数：s : Finset α；t : Finset β；f : α → β；fun a => {x ∈ s | f x = a}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `_private.Mathlib.Data.Finset.Union.0.Finset.pairwiseDisjoint_fibers`：∀ {
α : Type u_1} {β : Type u_2} [inst : DecidableEq β] {s : Finset α} {t : Finset β
} {f : α → β},   (↑t).PairwiseDisjoint fun a => {x ∈ s | …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
-/
@[simp] lemma disjiUnion_filter_eq (s : Finset α) (t : Finset β) (f : α → β) :
    t.disjiUnion (fun a ↦ s.filter (f · = a)) pairwiseDisjoint_fibers =
      s.filter fun c ↦ f c ∈ t :=
  ext fun b => by simpa using and_comm

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Finset.disjiUnion_filter_eq_of_maps_to** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：disjiUnion_filter_eq_of_maps_to (h : forall x in s, f x in t) : t.disjiUni
on (fun a => s.filter (f · = a)) pairwiseDisjoint_fibers = s
参数：h : forall x in s, f x in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Data.Finset.Union.0.Finset.pairwiseDisjoint_fibers`：∀ {
α : Type u_1} {β : Type u_2} [inst : DecidableEq β] {s : Finset α} {t : Finset β
} {f : α → β},   (↑t).PairwiseDisjoint fun a => {x ∈ s | …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.disjiUnion_filter_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : Dec
idableEq β] (s : Finset α) (t : Finset β) (f : α → β),   t.disjiUnion (fun a => 
{x ∈ s | f x = a}…
-/
lemma disjiUnion_filter_eq_of_maps_to (h : ∀ x ∈ s, f x ∈ t) :
    t.disjiUnion (fun a ↦ s.filter (f · = a)) pairwiseDisjoint_fibers = s := by
  simpa [filter_eq_self]

end DecidableEq

/-
**Finset.map_disjiUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_disjiUnion {f : α ↪ β} {s : Finset α} {t : β -> Finset γ} {h} : (s.map
 f).disjiUnion t h = s.disjiUnion (fun a => t (f a)) fun _ ha _ hb hab => h (mem
_map_of_mem _ ha) (mem_map_of_mem _ hb) (f.injective.ne hab)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `Finset.mem_map_of_mem`：mem_map_of_mem (f : α ↪ β) {a} {s : Finset α} : a
 in s -> f a in s.map f
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Multiset.bind_map`：bind_map (m : Multiset α) (n : β -> Multiset γ) (f : 
α -> β) : bind (map f m) n = bind m fun a => n (f a)
-/
theorem map_disjiUnion {f : α ↪ β} {s : Finset α} {t : β → Finset γ} {h} :
    (s.map f).disjiUnion t h =
      s.disjiUnion (fun a => t (f a)) fun _ ha _ hb hab =>
        h (mem_map_of_mem _ ha) (mem_map_of_mem _ hb) (f.injective.ne hab) :=
  eq_of_veq <| Multiset.bind_map _ _ _
/-
**Finset.disjiUnion_map** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjiUnion_map {s : Finset α} {t : α -> Finset β} {f : β ↪ γ} {h} : (s.dis
jiUnion t h).map f = s.disjiUnion (fun a => (t a).map f) (h.mono' fun _ _ => (di
sjoint_map _).2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `Set.Pairwise.mono'`：∀ {α : Type u_1} {r p : α → α → Prop} {s : Set α}, r
 ≤ p → s.Pairwise r → s.Pairwise p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_map`：disjoint_map {s t : Finset α} (f : α ↪ β) : Disjoin
t (s.map f) (t.map f) ↔ Disjoint s t
· 使用定理 `Multiset.map_bind`：map_bind (m : Multiset α) (n : α -> Multiset β) (f : 
β -> γ) : map f (bind m n) = bind m fun a => map f (n a)
-/
theorem disjiUnion_map {s : Finset α} {t : α → Finset β} {f : β ↪ γ} {h} :
    (s.disjiUnion t h).map f =
      s.disjiUnion (fun a => (t a).map f) (h.mono' fun _ _ ↦ (disjoint_map _).2) :=
  eq_of_veq <| Multiset.map_bind _ _ _

@[simp]
/-
**Finset.disjiUnion_singleton_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjiUnion_singleton_eq_self (s : Finset α) : s.disjiUnion singleton (fun 
_ _ => by simp) = s
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjiUnion_singleton_eq_self (s : Finset α) :
    s.disjiUnion singleton (fun _ _ => by simp) = s := by
  grind

variable {f : α → β} {op : β → β → β} [hc : Std.Commutative op] [ha : Std.Associative op]
/-
**Finset.fold_disjiUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：fold_disjiUnion {ι : Type*} {s : Finset ι} {t : ι -> Finset α} {b : ι -> β
} {b₀ : β} (h) : (s.disjiUnion t h).fold op (s.fold op b₀ b) f = s.fold op b₀ fu
n i => (t i).fold op (b i) f
参数：h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Multiset.map_bind`：map_bind (m : Multiset α) (n : α -> Multiset β) (f : 
β -> γ) : map f (bind m n) = bind m fun a => map f (n a)
· 使用定理 `Multiset.fold_bind`：fold_bind {ι : Type*} (s : Multiset ι) (t : ι -> Mul
tiset α) (b : ι -> α) (b₀ : α) : (s.bind t).fold op ((s.map b).fold op b₀) = (s.
map fun …
-/
theorem fold_disjiUnion {ι : Type*} {s : Finset ι} {t : ι → Finset α} {b : ι → β} {b₀ : β} (h) :
    (s.disjiUnion t h).fold op (s.fold op b₀ b) f = s.fold op b₀ fun i => (t i).fold op (b i) f :=
  (congr_arg _ <| Multiset.map_bind _ _ _).trans (Multiset.fold_bind _ _ _ _ _)
/-
**Finset.pairwiseDisjoint_filter** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：pairwiseDisjoint_filter {f : α -> Finset β} (h : Set.PairwiseDisjoint ↑s f
) (p : β -> Prop) [DecidablePred p] : Set.PairwiseDisjoint ↑s fun a => (f a).fil
ter p
参数：h : Set.PairwiseDisjoint ↑s f；p : β -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.disjoint_filter_filter`：∀ {α : Type u_1} {s t : Finset α} {p q : 
α → Prop} [inst : DecidablePred p] [inst_1 : DecidablePred q],   Disjoint s t → 
Disjoint (Finset.fi…
-/
lemma pairwiseDisjoint_filter {f : α → Finset β} (h : Set.PairwiseDisjoint ↑s f)
    (p : β → Prop) [DecidablePred p] : Set.PairwiseDisjoint ↑s fun a ↦ (f a).filter p :=
  fun _ h₁ _ h₂ hne ↦ Finset.disjoint_filter_filter (h h₁ h₂ hne)
/-
**Finset.filter_disjiUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：filter_disjiUnion (s : Finset α) (f : α -> Finset β) (h) (p : β -> Prop) [
DecidablePred p] : (s.disjiUnion f h).filter p = s.disjiUnion (fun a => (f a).fi
lter p) (pairwiseDisjoint_filter h p)
参数：s : Finset α；f : α -> Finset β；h；p : β -> Prop。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem filter_disjiUnion (s : Finset α) (f : α → Finset β) (h) (p : β → Prop) [DecidablePred p] :
    (s.disjiUnion f h).filter p
      = s.disjiUnion (fun a ↦ (f a).filter p) (pairwiseDisjoint_filter h p) := by grind

set_option backward.isDefEq.respectTransparency false in
/-
**Finset.disjiUnion_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjiUnion_singleton {f : α -> β} (hf : f.Injective) : s.disjiUnion (fun a
 => {f a}) (fun _ _ _ _ => disjoint_singleton.mpr ∘ hf.ne) = s.map ⟨f, hf⟩
参数：hf : f.Injective。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_singleton`：disjoint_singleton : Disjoint ({a} : Finset α
) {b} ↔ a != b
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjiUnion_singleton {f : α → β} (hf : f.Injective) :
    s.disjiUnion (fun a ↦ {f a}) (fun _ _ _ _ ↦ disjoint_singleton.mpr ∘ hf.ne) =
      s.map ⟨f, hf⟩ := by
  ext; simp [eq_comm]

set_option backward.isDefEq.respectTransparency false in
/-
**Finset.disjoint_disjiUnion_left** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：disjoint_disjiUnion_left (s : Finset α) (f : α -> Finset β) (hf : Set.Pair
wiseDisjoint s f) (t : Finset β) : Disjoint (s.disjiUnion f hf) t ↔ forall i in 
s, Disjoint (f i) t
参数：s : Finset α；f : α -> Finset β；hf : Set.PairwiseDisjoint s f；t : Finset β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
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
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Finset.mem_cons_of_mem`：mem_cons_of_mem {a b : α} {s : Finset α} {hb : b
 ∉ s} (ha : a in s) : a in cons b s hb
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_disjiUnion`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t
 : α → Finset β} {b : β} {h : (↑s).PairwiseDisjoint t},   b ∈ s.disjiUnion t h ↔
 ∃ a ∈ s, b…
· 使用定理 `Finset.mem_cons_self`：mem_cons_self (a : α) (s : Finset α) {h} : a in co
ns a s h
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.disjiUnion_cons`：∀ {α : Type u_1} {β : Type u_2} (a : α) (s : Fin
set α) (ha : a ∉ s) (f : α → Finset β)   (H : (↑(Finset.cons a s ha)).PairwiseDi
sjoint f),  …
-/
lemma disjoint_disjiUnion_left
    (s : Finset α) (f : α → Finset β) (hf : Set.PairwiseDisjoint s f) (t : Finset β) :
    Disjoint (s.disjiUnion f hf) t ↔ ∀ i ∈ s, Disjoint (f i) t := by
  induction s using Finset.cons_induction <;> simp_all
/-
**Finset.disjoint_disjiUnion_right** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：disjoint_disjiUnion_right (s : Finset β) (t : Finset α) (f : α -> Finset β
) (hf : Set.PairwiseDisjoint t f) : Disjoint s (t.disjiUnion f hf) ↔ forall i in
 t, Disjoint s (f i)
参数：s : Finset β；t : Finset α；f : α -> Finset β；hf : Set.PairwiseDisjoint t f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Finset.disjoint_disjiUnion_left`：disjoint_disjiUnion_left (s : Finset α)
 (f : α -> Finset β) (hf : Set.PairwiseDisjoint s f) (t : Finset β) : Disjoint (
s.disjiUnion f hf) t …
-/
lemma disjoint_disjiUnion_right
    (s : Finset β) (t : Finset α) (f : α → Finset β) (hf : Set.PairwiseDisjoint t f) :
    Disjoint s (t.disjiUnion f hf) ↔ ∀ i ∈ t, Disjoint s (f i) := by
  simpa only [_root_.disjoint_comm] using disjoint_disjiUnion_left t f hf s
/-
**Finset.pairwiseDisjoint_disjUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：pairwiseDisjoint_disjUnion {f g : α -> Finset β} (hfg : forall a, Disjoint
 (f a) (g a)) (hfg' : Set.Pairwise s fun a₁ a₂ => Disjoint (f a₁) (g a₂)) (hf : 
Set.PairwiseDisjoint s f) (hg : Set.PairwiseDisjoint s g) : Set.PairwiseDisjoint
 s (fun a => (f a).disjUnion (g a) (hfg a))
参数：hfg : forall a, Disjoint (f a) (g a)；hfg' : Set.Pairwise s fun a₁ a₂ => Disjo
int (f a₁) (g a₂)；hf : Set.PairwiseDisjoint s f；hg : Set.PairwiseDisjoint s g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem pairwiseDisjoint_disjUnion {f g : α → Finset β}
    (hfg : ∀ a, Disjoint (f a) (g a))
    (hfg' : Set.Pairwise s fun a₁ a₂ ↦ Disjoint (f a₁) (g a₂))
    (hf : Set.PairwiseDisjoint s f) (hg : Set.PairwiseDisjoint s g) :
    Set.PairwiseDisjoint s (fun a ↦ (f a).disjUnion (g a) (hfg a)) := by
  intros i hi j hj hij
  simp [hf hi hj hij, hg hi hj hij, hfg' hi hj hij, (hfg' hj hi hij.symm).symm]
/-
**Finset.disjiUnion_disjUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：disjiUnion_disjUnion {f g : α -> Finset β} (hfg : forall a, Disjoint (f a)
 (g a)) (hfg' : Set.Pairwise s fun a₁ a₂ => Disjoint (f a₁) (g a₂)) (hf : Set.Pa
irwiseDisjoint s f) (hg : Set.PairwiseDisjoint s g) : s.disjiUnion (fun a => (f 
a).disjUnion (g a) (hfg a)) (pairwiseDisjoint_disjUnion hfg hfg' hf hg) = (s.dis
jiUnion f hf).disjUnion (s.disjiUnion g hg) (by simp_rw [disjoint_disjiUnion_lef
t, disjoint_disjiUnion_right] intros i hi j hj specialize hfg' hi hj grind)
参数：hfg : forall a, Disjoint (f a) (g a)；hfg' : Set.Pairwise s fun a₁ a₂ => Disjo
int (f a₁) (g a₂)；hf : Set.PairwiseDisjoint s f；hg : Set.PairwiseDisjoint s g。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem disjiUnion_disjUnion {f g : α → Finset β} (hfg : ∀ a, Disjoint (f a) (g a))
    (hfg' : Set.Pairwise s fun a₁ a₂ ↦ Disjoint (f a₁) (g a₂))
    (hf : Set.PairwiseDisjoint s f) (hg : Set.PairwiseDisjoint s g) :
    s.disjiUnion (fun a ↦ (f a).disjUnion (g a) (hfg a))
        (pairwiseDisjoint_disjUnion hfg hfg' hf hg) =
      (s.disjiUnion f hf).disjUnion (s.disjiUnion g hg) (by
        simp_rw [disjoint_disjiUnion_left, disjoint_disjiUnion_right]
        intros i hi j hj
        specialize hfg' hi hj
        grind) := by
  grind

end DisjiUnion

section BUnion
variable [DecidableEq β]

/-- `Finset.biUnion s t` is the union of `t a` over `a ∈ s`.

(This was formerly `bind` due to the monad structure on types with `DecidableEq`.) -/
/-
**Finset.biUnion** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → [DecidableEq β] → Finset α → (α → Finset
 β) → Finset β
参数：α → Finset β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Finset.biUnion s t` is the union of `t a` over `a ∈ s`.

(This was formerly `bind` due to the monad structure on types with `DecidableEq`
.)
-/
protected def biUnion (s : Finset α) (t : α → Finset β) : Finset β :=
  (s.1.bind fun a ↦ (t a).1).toFinset
/-
**Finset.biUnion_val** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : DecidableEq β] (s : Finset α) (t :
 α → Finset β),   (s.biUnion t).val = (s.val.bind fun a => (t a).val).dedup
参数：s : Finset α；t : α → Finset β；s.biUnion t；s.val.bind fun a => (t a).val。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma biUnion_val (s : Finset α) (t : α → Finset β) :
    (s.biUnion t).1 = (s.1.bind fun a ↦ (t a).1).dedup := rfl
/-
**Finset.biUnion_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {t : α → Finset β} [inst : DecidableEq β],
 ∅.biUnion t = ∅
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma biUnion_empty : Finset.biUnion ∅ t = ∅ := rfl
/-
**Finset.mem_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t : α → Finset β} [inst : 
DecidableEq β] {b : β},   b ∈ s.biUnion t ↔ ∃ a ∈ s, b ∈ t a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp, grind =] lemma mem_biUnion {b : β} : b ∈ s.biUnion t ↔ ∃ a ∈ s, b ∈ t a := by
  simp only [mem_def, biUnion_val, Multiset.mem_dedup, Multiset.mem_bind]

@[simp, norm_cast]
/-
**Finset.coe_biUnion** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：coe_biUnion : (s.biUnion t : Set β) = ⋃ x in (s : Set α), t x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma coe_biUnion : (s.biUnion t : Set β) = ⋃ x ∈ (s : Set α), t x := by
  simp [Set.ext_iff, mem_biUnion, Set.mem_iUnion]

@[simp]
/-
**Finset.biUnion_insert** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：biUnion_insert [DecidableEq α] {a : α} : (insert a s).biUnion t = t a unio
n s.biUnion t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma biUnion_insert [DecidableEq α] {a : α} : (insert a s).biUnion t = t a ∪ s.biUnion t := by
  aesop
/-
**Finset.biUnion_congr** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：biUnion_congr (hs : s₁ = s₂) (ht : forall a in s₁, t₁ a = t₂ a) : s₁.biUni
on t₁ = s₂.biUnion t₂
参数：hs : s₁ = s₂；ht : forall a in s₁, t₁ a = t₂ a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma biUnion_congr (hs : s₁ = s₂) (ht : ∀ a ∈ s₁, t₁ a = t₂ a) :
    s₁.biUnion t₁ = s₂.biUnion t₂ := by
  grind

@[simp]
/-
**Finset.disjiUnion_eq_biUnion** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：disjiUnion_eq_biUnion (s : Finset α) (f : α -> Finset β) (hf) : s.disjiUni
on f hf = s.biUnion f
参数：s : Finset α；f : α -> Finset β；hf。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.Nodup.dedup`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Multi
set α}, s.Nodup → s.dedup = s
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
-/
lemma disjiUnion_eq_biUnion (s : Finset α) (f : α → Finset β) (hf) :
    s.disjiUnion f hf = s.biUnion f := eq_of_veq (s.disjiUnion f hf).nodup.dedup.symm
/-
**Finset.biUnion_subset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：biUnion_subset {s' : Finset β} : s.biUnion t subseteq s' ↔ forall x in s, 
t x subseteq s'
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma biUnion_subset {s' : Finset β} : s.biUnion t ⊆ s' ↔ ∀ x ∈ s, t x ⊆ s' := by grind

@[simp]
/-
**Finset.singleton_biUnion** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：singleton_biUnion {a : α} : Finset.biUnion {a} t = t a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma singleton_biUnion {a : α} : Finset.biUnion {a} t = t a := by grind
/-
**Finset.biUnion_inter** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：biUnion_inter (s : Finset α) (f : α -> Finset β) (t : Finset β) : s.biUnio
n f inter t = s.biUnion fun x => f x inter t
参数：s : Finset α；f : α -> Finset β；t : Finset β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma biUnion_inter (s : Finset α) (f : α → Finset β) (t : Finset β) :
    s.biUnion f ∩ t = s.biUnion fun x ↦ f x ∩ t := by grind
/-
**Finset.inter_biUnion** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：inter_biUnion (t : Finset β) (s : Finset α) (f : α -> Finset β) : t inter 
s.biUnion f = s.biUnion fun x => t inter f x
参数：t : Finset β；s : Finset α；f : α -> Finset β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inter_biUnion (t : Finset β) (s : Finset α) (f : α → Finset β) :
    t ∩ s.biUnion f = s.biUnion fun x ↦ t ∩ f x := by grind
/-
**Finset.biUnion_biUnion** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：biUnion_biUnion [DecidableEq γ] (s : Finset α) (f : α -> Finset β) (g : β 
-> Finset γ) : (s.biUnion f).biUnion g = s.biUnion fun a => (f a).biUnion g
参数：s : Finset α；f : α -> Finset β；g : β -> Finset γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma biUnion_biUnion [DecidableEq γ] (s : Finset α) (f : α → Finset β) (g : β → Finset γ) :
    (s.biUnion f).biUnion g = s.biUnion fun a ↦ (f a).biUnion g := by grind
/-
**Finset.bind_toFinset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：bind_toFinset [DecidableEq α] (s : Multiset α) (t : α -> Multiset β) : (s.
bind t).toFinset = s.toFinset.biUnion fun a => (t a).toFinset
参数：s : Multiset α；t : α -> Multiset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma bind_toFinset [DecidableEq α] (s : Multiset α) (t : α → Multiset β) :
    (s.bind t).toFinset = s.toFinset.biUnion fun a ↦ (t a).toFinset :=
  ext fun x ↦ by simp only [Multiset.mem_toFinset, mem_biUnion, Multiset.mem_bind]
/-
**Finset.biUnion_mono** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：biUnion_mono (h : forall a in s, t₁ a subseteq t₂ a) : s.biUnion t₁ subset
eq s.biUnion t₂
参数：h : forall a in s, t₁ a subseteq t₂ a。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma biUnion_mono (h : ∀ a ∈ s, t₁ a ⊆ t₂ a) : s.biUnion t₁ ⊆ s.biUnion t₂ := by grind

@[gcongr]
/-
**Finset.biUnion_subset_biUnion_of_subset_left** 是 Mathlib 中的一个引理，位于命名空间 `Finset
`。
形式化陈述：biUnion_subset_biUnion_of_subset_left (t : α -> Finset β) (h : s₁ subseteq
 s₂) : s₁.biUnion t subseteq s₂.biUnion t
参数：t : α -> Finset β；h : s₁ subseteq s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma biUnion_subset_biUnion_of_subset_left (t : α → Finset β) (h : s₁ ⊆ s₂) :
    s₁.biUnion t ⊆ s₂.biUnion t := by grind
/-
**Finset.subset_biUnion_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：subset_biUnion_of_mem (u : α -> Finset β) {x : α} (xs : x in s) : u x subs
eteq s.biUnion u
参数：u : α -> Finset β；xs : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subset_biUnion_of_mem (u : α → Finset β) {x : α} (xs : x ∈ s) : u x ⊆ s.biUnion u := by grind

@[simp]
/-
**Finset.biUnion_subset_iff_forall_subset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：biUnion_subset_iff_forall_subset {α β : Type*} [DecidableEq β] {s : Finset
 α} {t : Finset β} {f : α -> Finset β} : s.biUnion f subseteq t ↔ forall x in s,
 f x subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma biUnion_subset_iff_forall_subset {α β : Type*} [DecidableEq β] {s : Finset α}
    {t : Finset β} {f : α → Finset β} : s.biUnion f ⊆ t ↔ ∀ x ∈ s, f x ⊆ t := by grind

@[simp]
/-
**Finset.biUnion_singleton_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：biUnion_singleton_eq_self [DecidableEq α] : s.biUnion (singleton : α -> Fi
nset α) = s
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma biUnion_singleton_eq_self [DecidableEq α] : s.biUnion (singleton : α → Finset α) = s := by
  grind
/-
**Finset.filter_biUnion** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：filter_biUnion (s : Finset α) (f : α -> Finset β) (p : β -> Prop) [Decidab
lePred p] : (s.biUnion f).filter p = s.biUnion fun a => (f a).filter p
参数：s : Finset α；f : α -> Finset β；p : β -> Prop。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma filter_biUnion (s : Finset α) (f : α → Finset β) (p : β → Prop) [DecidablePred p] :
    (s.biUnion f).filter p = s.biUnion fun a ↦ (f a).filter p := by grind
/-
**Finset.biUnion_filter_eq_of_maps_to** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：biUnion_filter_eq_of_maps_to [DecidableEq α] {s : Finset α} {t : Finset β}
 {f : α -> β} (h : forall x in s, f x in t) : (t.biUnion fun a => s.filter fun c
 => f c = a) = s
参数：h : forall x in s, f x in t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma biUnion_filter_eq_of_maps_to [DecidableEq α] {s : Finset α} {t : Finset β} {f : α → β}
    (h : ∀ x ∈ s, f x ∈ t) : (t.biUnion fun a ↦ s.filter fun c ↦ f c = a) = s := by grind
/-
**Finset.erase_biUnion** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：erase_biUnion (f : α -> Finset β) (s : Finset α) (b : β) : (s.biUnion f).e
rase b = s.biUnion fun x => (f x).erase b
参数：f : α -> Finset β；s : Finset α；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma erase_biUnion (f : α → Finset β) (s : Finset α) (b : β) :
    (s.biUnion f).erase b = s.biUnion fun x ↦ (f x).erase b := by grind

@[simp]
/-
**Finset.biUnion_nonempty** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：biUnion_nonempty : (s.biUnion t).Nonempty ↔ exists x in s, (t x).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∃ a b,
 p a b) ↔ ∃ b a, p a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma biUnion_nonempty : (s.biUnion t).Nonempty ↔ ∃ x ∈ s, (t x).Nonempty := by
  simp only [Finset.Nonempty, mem_biUnion]
  rw [exists_comm]
  simp [exists_and_left]
/-
**Finset.Nonempty.biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t : α → Finset β} [inst : 
DecidableEq β],   s.Nonempty → (∀ x ∈ s, (t x).Nonempty) → (s.biUnion t).Nonempt
y
参数：∀ x ∈ s, (t x).Nonempty；s.biUnion t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.biUnion_nonempty`：biUnion_nonempty : (s.biUnion t).Nonempty ↔ exi
sts x in s, (t x).Nonempty
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
-/
lemma Nonempty.biUnion (hs : s.Nonempty) (ht : ∀ x ∈ s, (t x).Nonempty) :
    (s.biUnion t).Nonempty := biUnion_nonempty.2 <| hs.imp fun x hx ↦ ⟨hx, ht x hx⟩
/-
**Finset.disjoint_biUnion_left** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：disjoint_biUnion_left (s : Finset α) (f : α -> Finset β) (t : Finset β) : 
Disjoint (s.biUnion f) t ↔ forall i in s, Disjoint (f i) t
参数：s : Finset α；f : α -> Finset β；t : Finset β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
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
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.biUnion_insert`：biUnion_insert [DecidableEq α] {a : α} : (insert 
a s).biUnion t = t a union s.biUnion t
-/
lemma disjoint_biUnion_left (s : Finset α) (f : α → Finset β) (t : Finset β) :
    Disjoint (s.biUnion f) t ↔ ∀ i ∈ s, Disjoint (f i) t := by
  classical
  refine s.induction ?_ ?_
  · simp
  · intro i s his ih
    simp only [disjoint_union_left, biUnion_insert, forall_mem_insert, ih]
/-
**Finset.disjoint_biUnion_right** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：disjoint_biUnion_right (s : Finset β) (t : Finset α) (f : α -> Finset β) :
 Disjoint s (t.biUnion f) ↔ forall i in t, Disjoint s (f i)
参数：s : Finset β；t : Finset α；f : α -> Finset β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Finset.disjoint_biUnion_left`：disjoint_biUnion_left (s : Finset α) (f : 
α -> Finset β) (t : Finset β) : Disjoint (s.biUnion f) t ↔ forall i in s, Disjoi
nt (f i) t
-/
lemma disjoint_biUnion_right (s : Finset β) (t : Finset α) (f : α → Finset β) :
    Disjoint s (t.biUnion f) ↔ ∀ i ∈ t, Disjoint s (f i) := by
  simpa only [_root_.disjoint_comm] using disjoint_biUnion_left t f s
/-
**Finset.image_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_biUnion [DecidableEq γ] {f : α -> β} {s : Finset α} {t : β -> Finset
 γ} : (s.image f).biUnion t = s.biUnion fun a => t (f a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.image_insert`：image_insert [DecidableEq α] (f : α -> β) (a : α) (
s : Finset α) : (insert a s).image f = insert (f a) (s.image f)
· 使用引理 `Finset.biUnion_insert`：biUnion_insert [DecidableEq α] {a : α} : (insert 
a s).biUnion t = t a union s.biUnion t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_biUnion [DecidableEq γ] {f : α → β} {s : Finset α} {t : β → Finset γ} :
    (s.image f).biUnion t = s.biUnion fun a => t (f a) :=
  haveI := Classical.decEq α
  Finset.induction_on s rfl fun a s _ ih => by simp only [image_insert, biUnion_insert, ih]
/-
**Finset.biUnion_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：biUnion_image [DecidableEq γ] {s : Finset α} {t : α -> Finset β} {f : β ->
 γ} : (s.biUnion t).image f = s.biUnion fun a => (t a).image f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.biUnion_insert`：biUnion_insert [DecidableEq α] {a : α} : (insert 
a s).biUnion t = t a union s.biUnion t
· 使用定理 `Finset.image_union`：image_union [DecidableEq α] {f : α -> β} (s₁ s₂ : Fi
nset α) : (s₁ union s₂).image f = s₁.image f union s₂.image f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem biUnion_image [DecidableEq γ] {s : Finset α} {t : α → Finset β} {f : β → γ} :
    (s.biUnion t).image f = s.biUnion fun a => (t a).image f :=
  haveI := Classical.decEq α
  Finset.induction_on s rfl fun a s _ ih => by simp only [biUnion_insert, image_union, ih]
/-
**Finset.image_biUnion_filter_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_biUnion_filter_eq [DecidableEq α] (s : Finset β) (g : β -> α) : ((s.
image g).biUnion fun a => s.filter fun c => g c = a) = s
参数：s : Finset β；g : β -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.biUnion_filter_eq_of_maps_to`：biUnion_filter_eq_of_maps_to [Decid
ableEq α] {s : Finset α} {t : Finset β} {f : α -> β} (h : forall x in s, f x in 
t) : (t.biUnion fun a => …
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
-/
theorem image_biUnion_filter_eq [DecidableEq α] (s : Finset β) (g : β → α) :
    ((s.image g).biUnion fun a => s.filter fun c => g c = a) = s :=
  biUnion_filter_eq_of_maps_to fun _ => mem_image_of_mem g
/-
**Finset.union_biUnion** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：union_biUnion [DecidableEq α] : (s₁ union s₂).biUnion t = s₁.biUnion t uni
on s₂.biUnion t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma union_biUnion [DecidableEq α] : (s₁ ∪ s₂).biUnion t = s₁.biUnion t ∪ s₂.biUnion t := by
  grind
/-
**Finset.biUnion_union** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：biUnion_union : s.biUnion (fun x => t₁ x union t₂ x) = s.biUnion t₁ union 
s.biUnion t₂
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma biUnion_union : s.biUnion (fun x ↦ t₁ x ∪ t₂ x) = s.biUnion t₁ ∪ s.biUnion t₂ := by grind
/-
**Finset.biUnion_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：biUnion_singleton {f : α -> β} : (s.biUnion fun a => {f a}) = s.image f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem biUnion_singleton {f : α → β} : (s.biUnion fun a => {f a}) = s.image f := by grind

/-- Rewrite a `biUnion` over `s.attach` as a `biUnion` over `s`, in the case where the indexing
function on `s.attach` happens to factor through `α`. See `Finset.attach_biUnion'` for the version
without that hypothesis. -/
/-
**Finset.attach_biUnion** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：attach_biUnion {f : α -> Finset β} : s.attach.biUnion (f ·) = s.biUnion f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Rewrite a `biUnion` over `s.attach` as a `biUnion` over `s`, in the case where t
he indexing
function on `s.attach` happens to factor through `α`. See `Finset.attach_biUnion
'` for the version
without that hypothesis.
-/
lemma attach_biUnion {f : α → Finset β} : s.attach.biUnion (f ·) = s.biUnion f := by aesop

/-- Rewrite a `biUnion` over `s.attach` as a `biUnion` over `s` by extending the function to all of
`α` with `∅` outside `s`. See `Finset.attach_biUnion` for the version when the indexing function is
already defined on all of `α`. -/
/-
**Finset.attach_biUnion'** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：attach_biUnion' [DecidableEq α] {f : s -> Finset β} : s.attach.biUnion f =
 s.biUnion fun a => if h : a in s then f ⟨a, h⟩ else ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯

--- 原说明 ---
Rewrite a `biUnion` over `s.attach` as a `biUnion` over `s` by extending the fun
ction to all of
`α` with `∅` outside `s`. See `Finset.attach_biUnion` for the version when the i
ndexing function is
already defined on all of `α`.
-/
lemma attach_biUnion' [DecidableEq α] {f : s → Finset β} :
    s.attach.biUnion f = s.biUnion fun a ↦ if h : a ∈ s then f ⟨a, h⟩ else ∅ := by aesop

end BUnion
end Finset

