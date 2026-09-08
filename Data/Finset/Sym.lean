/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Data.Multiset.Sym
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Symmetric powers of a finset

This file defines the symmetric powers of a finset as `Finset (Sym α n)` and `Finset (Sym2 α)`.

## Main declarations

* `Finset.sym`: The symmetric power of a finset. `s.sym n` is all the multisets of cardinality `n`
  whose elements are in `s`.
* `Finset.sym2`: The symmetric square of a finset. `s.sym2` is all the pairs whose elements are in
  `s`.
* A `Fintype (Sym2 α)` instance that does not require `DecidableEq α`.

## TODO

`Finset.sym` forms a Galois connection between `Finset α` and `Finset (Sym α n)`. Similar for
`Finset.sym2`.
-/

@[expose] public section

namespace Finset

variable {α β : Type*}

/-- `s.sym2` is the finset of all unordered pairs of elements from `s`.
It is the image of `s ×ˢ s` under the quotient `α × α → Sym2 α`. -/
@[simps]
/-
**Finset.sym2** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{α : Type u_1} → Finset α → Finset (Sym2 α)
参数：Sym2 α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`s.sym2` is the finset of all unordered pairs of elements from `s`.
It is the image of `s ×ˢ s` under the quotient `α × α → Sym2 α`.
-/
protected def sym2 (s : Finset α) : Finset (Sym2 α) := ⟨s.1.sym2, s.2.sym2⟩

section
variable {s t : Finset α} {a b : α}

/-
**Finset.mk_mem_sym2_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mk_mem_sym2_iff : s(a, b) in s.sym2 ↔ a in s ∧ b in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
· 使用定理 `Finset.mem_mk`：mem_mk {a : α} {s nd} : a in @Finset.mk α s nd ↔ a in s
· 使用定理 `Finset.sym2_val`：∀ {α : Type u_1} (s : Finset α), s.sym2.val = s.val.sym
2
· 使用定理 `Multiset.mk_mem_sym2_iff`：mk_mem_sym2_iff {m : Multiset α} {a b : α} : s
(a, b) in m.sym2 ↔ a in m ∧ b in m
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_mem_sym2_iff : s(a, b) ∈ s.sym2 ↔ a ∈ s ∧ b ∈ s := by
  rw [mem_mk, sym2_val, Multiset.mk_mem_sym2_iff, mem_mk, mem_mk]

@[simp, grind =]
/-
**Finset.mem_sym2_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_sym2_iff {m : Sym2 α} : m in s.sym2 ↔ forall a in m, a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
· 使用定理 `Finset.mem_mk`：mem_mk {a : α} {s nd} : a in @Finset.mk α s nd ↔ a in s
· 使用定理 `Finset.sym2_val`：∀ {α : Type u_1} (s : Finset α), s.sym2.val = s.val.sym
2
· 使用定理 `Multiset.mem_sym2_iff`：mem_sym2_iff {m : Multiset α} {z : Sym2 α} : z in
 m.sym2 ↔ forall y in z, y in m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_sym2_iff {m : Sym2 α} : m ∈ s.sym2 ↔ ∀ a ∈ m, a ∈ s := by
  rw [mem_mk, sym2_val, Multiset.mem_sym2_iff]
  simp only [mem_val]
/-
**Finset.coe_sym2** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} {m : Finset α}, ↑m.sym2 = (↑m).sym2
参数：↑m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
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
@[simp] lemma coe_sym2 {m : Finset α} : (m.sym2 : Set (Sym2 α)) = (m : Set α).sym2 :=
  Set.ext fun z ↦ z.ind fun a b => by simp
/-
**Finset.sym2_cons** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sym2_cons (a : α) (s : Finset α) (ha : a ∉ s) : (s.cons a ha).sym2 = ((s.c
ons a ha).map <| Sym2.mkEmbedding a).disjUnion s.sym2 (by simp [Finset.disjoint_
left, ha])
参数：a : α；s : Finset α；ha : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.val_injective`：val_injective : Injective (val : Finset α -> Multi
set α)
· 使用定理 `Multiset.sym2_cons`：sym2_cons (a : α) (m : Multiset α) : (m.cons a).sym2
 = ((m.cons a).map <| fun b => s(a, b)) + m.sym2
-/
theorem sym2_cons (a : α) (s : Finset α) (ha : a ∉ s) :
    (s.cons a ha).sym2 = ((s.cons a ha).map <| Sym2.mkEmbedding a).disjUnion s.sym2 (by
      simp [Finset.disjoint_left, ha]) :=
  val_injective <| Multiset.sym2_cons _ _
/-
**Finset.sym2_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sym2_insert [DecidableEq α] (a : α) (s : Finset α) : (insert a s).sym2 = (
(insert a s).image fun b => s(a, b)) union s.sym2
参数：a : α；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.em`：∀ (p : Prop) [Decidable p], p ∨ ¬p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.insert_eq_of_mem`：insert_eq_of_mem (h : a in s) : insert a s = s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Finset.image_insert`：image_insert [DecidableEq α] (f : α -> β) (a : α) (
s : Finset α) : (insert a s).image f = insert (f a) (s.image f)
· 使用定理 `Finset.insert_union`：insert_union (a : α) (s t : Finset α) : insert a s 
union t = insert a (s union t)
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `Sym2.mkEmbedding_apply`：∀ {α : Type u_1} (a b : α), (Sym2.mkEmbedding a)
 b = s(a, b)
· 使用定理 `Finset.disjUnion.congr_simp`：∀ {α : Type u_2} (s s_1 : Finset α) (e_s : 
s = s_1) (t t_1 : Finset α) (e_t : t = t_1) (h : Disjoint s t),   s.disjUnion t 
h = s_1.disjUnion…
· 使用定理 `Finset.disjUnion_eq_union`：disjUnion_eq_union (s t h) : @disjUnion α s t
 h = s union t
· 使用定理 `Finset.sym2_cons`：sym2_cons (a : α) (s : Finset α) (ha : a ∉ s) : (s.con
s a ha).sym2 = ((s.cons a ha).map <| Sym2.mkEmbedding a).disjUnion s.sym2 (by si
mp [Fi…
-/
theorem sym2_insert [DecidableEq α] (a : α) (s : Finset α) :
    (insert a s).sym2 = ((insert a s).image fun b => s(a, b)) ∪ s.sym2 := by
  obtain ha | ha := Decidable.em (a ∈ s)
  · simp only [insert_eq_of_mem ha, right_eq_union, image_subset_iff]
    simp_all
  · simpa [map_eq_image] using! sym2_cons a s ha
/-
**Finset.sym2_map** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sym2_map (f : α ↪ β) (s : Finset α) : (s.map f).sym2 = s.sym2.map (.sym2Ma
p f)
参数：f : α ↪ β；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.val_injective`：val_injective : Injective (val : Finset α -> Multi
set α)
· 使用定理 `Multiset.sym2_map`：sym2_map (f : α -> β) (m : Multiset α) : (m.map f).sy
m2 = m.sym2.map (Sym2.map f)
-/
theorem sym2_map (f : α ↪ β) (s : Finset α) : (s.map f).sym2 = s.sym2.map (.sym2Map f) :=
  val_injective <| s.val.sym2_map _
/-
**Finset.sym2_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sym2_image [DecidableEq β] (f : α -> β) (s : Finset α) : (s.image f).sym2 
= s.sym2.image (Sym2.map f)
参数：f : α -> β；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.val_injective`：val_injective : Injective (val : Finset α -> Multi
set α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.dedup_sym2`：dedup_sym2 [DecidableEq α] (m : Multiset α) : m.sym
2.dedup = m.dedup.sym2
· 使用定理 `Multiset.sym2_map`：sym2_map (f : α -> β) (m : Multiset α) : (m.map f).sy
m2 = m.sym2.map (Sym2.map f)
-/
theorem sym2_image [DecidableEq β] (f : α → β) (s : Finset α) :
    (s.image f).sym2 = s.sym2.image (Sym2.map f) := by
  apply val_injective
  dsimp [Finset.sym2]
  rw [← Multiset.dedup_sym2, Multiset.sym2_map]
/-
**Finset._root_.Sym2.instFintype** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.Sym2.instFintype [Fintype α] : Fintype (Sym2 α) where
  elems := Finset.univ.sym2
  complete := fun x ↦ by rw [mem_sym2_iff]; exact (fun a _ ↦ mem_univ a)

-- Note(kmill): Using a default argument to make this simp lemma more general.
@[simp]
/-
**Finset.sym2_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sym2_univ [Fintype α] (inst : Fintype (Sym2 α)
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
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
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sym2_univ [Fintype α] (inst : Fintype (Sym2 α) := Sym2.instFintype) :
    (univ : Finset α).sym2 = univ := by
  ext
  simp only [mem_sym2_iff, mem_univ, implies_true]

@[simp, mono]
/-
**Finset.sym2_mono** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sym2_mono (h : s subseteq t) : s.sym2 subseteq t.sym2
参数：h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sym2_mono (h : s ⊆ t) : s.sym2 ⊆ t.sym2 := by
  grind
/-
**Finset.monotone_sym2** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：monotone_sym2 : Monotone (Finset.sym2 : Finset α -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sym2_mono`：sym2_mono (h : s subseteq t) : s.sym2 subseteq t.sym2
-/
theorem monotone_sym2 : Monotone (Finset.sym2 : Finset α → _) := fun _ _ => sym2_mono
/-
**Finset.injective_sym2** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：injective_sym2 : Function.Injective (Finset.sym2 : Finset α -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
-/
theorem injective_sym2 : Function.Injective (Finset.sym2 : Finset α → _) := by
  intro s t h
  ext x
  simpa using congr(s(x, x) ∈ $h)
/-
**Finset.strictMono_sym2** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：strictMono_sym2 : StrictMono (Finset.sym2 : Finset α -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.strictMono_of_injective`：Monotone.strictMono_of_injective (h₁ :
 Monotone f) (h₂ : Injective f) : StrictMono f
· 使用定理 `Finset.monotone_sym2`：monotone_sym2 : Monotone (Finset.sym2 : Finset α -
> _)
· 使用定理 `Finset.injective_sym2`：injective_sym2 : Function.Injective (Finset.sym2 
: Finset α -> _)
-/
theorem strictMono_sym2 : StrictMono (Finset.sym2 : Finset α → _) :=
  monotone_sym2.strictMono_of_injective injective_sym2
/-
**Finset.sym2_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sym2_toFinset [DecidableEq α] (m : Multiset α) : m.toFinset.sym2 = m.sym2.
toFinset
参数：m : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sym2_toFinset [DecidableEq α] (m : Multiset α) :
    m.toFinset.sym2 = m.sym2.toFinset := by
  ext z
  refine z.ind fun x y ↦ ?_
  simp only [mk_mem_sym2_iff, Multiset.mem_toFinset, Multiset.mk_mem_sym2_iff]

@[simp]
/-
**Finset.sym2_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sym2_empty : (∅ : Finset α).sym2 = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sym2_empty : (∅ : Finset α).sym2 = ∅ := rfl

@[simp]
/-
**Finset.sym2_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sym2_eq_empty : s.sym2 = ∅ ↔ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.val_eq_zero`：val_eq_zero {s : Finset α} : s.1 = 0 ↔ s = ∅
· 使用定理 `Finset.sym2_val`：∀ {α : Type u_1} (s : Finset α), s.sym2.val = s.val.sym
2
· 使用定理 `Multiset.sym2_eq_zero_iff`：sym2_eq_zero_iff {m : Multiset α} : m.sym2 = 
0 ↔ m = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sym2_eq_empty : s.sym2 = ∅ ↔ s = ∅ := by
  rw [← val_eq_zero, sym2_val, Multiset.sym2_eq_zero_iff, val_eq_zero]

@[simp]
/-
**Finset.sym2_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sym2_nonempty : s.sym2.Nonempty ↔ s.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sym2_eq_empty`：sym2_eq_empty : s.sym2 = ∅ ↔ s = ∅
-/
theorem sym2_nonempty : s.sym2.Nonempty ↔ s.Nonempty := by
  contrapose!; exact sym2_eq_empty

@[aesop safe apply (rule_sets := [finsetNonempty])]
protected alias ⟨_, Nonempty.sym2⟩ := sym2_nonempty

@[simp]
/-
**Finset.sym2_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sym2_singleton (a : α) : ({a} : Finset α).sym2 = {Sym2.diag a}
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sym2_singleton (a : α) : ({a} : Finset α).sym2 = {Sym2.diag a} := rfl

/-- Finset **stars and bars** for the case `n = 2`. -/
/-
**Finset.card_sym2** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_sym2 (s : Finset α) : s.sym2.card = Nat.choose (s.card + 1) 2
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_def`：card_def (s : Finset α) : #s = Multiset.card s.1
· 使用定理 `Finset.sym2_val`：∀ {α : Type u_1} (s : Finset α), s.sym2.val = s.val.sym
2
· 使用定理 `Multiset.card_sym2`：card_sym2 {m : Multiset α} : Multiset.card m.sym2 = 
Nat.choose (Multiset.card m + 1) 2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Finset **stars and bars** for the case `n = 2`.
-/
theorem card_sym2 (s : Finset α) : s.sym2.card = Nat.choose (s.card + 1) 2 := by
  rw [card_def, sym2_val, Multiset.card_sym2, ← card_def]

end

variable {s t : Finset α} {a b : α}

/-
**Finset.sym2_eq_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sym2_eq_image [DecidableEq α] : s.sym2 = (s ×ˢ s).image Sym2.mk.uncurry
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
-/
theorem sym2_eq_image [DecidableEq α] : s.sym2 = (s ×ˢ s).image Sym2.mk.uncurry := by
  ext ⟨a, b⟩; simp; grind
/-
**Finset.isDiag_mk_of_mem_diag** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：isDiag_mk_of_mem_diag {a b : α} (h : (a, b) in s.diag) : s(a, b).IsDiag
参数：h : (a, b) in s.diag。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isDiag_mk_of_mem_diag {a b : α} (h : (a, b) ∈ s.diag) : s(a, b).IsDiag := by
  simp at *; grind
/-
**Finset.not_isDiag_mk_of_mem_offDiag** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：not_isDiag_mk_of_mem_offDiag {a b : α} (h : (a, b) in s.offDiag) : ¬ s(a, 
b).IsDiag
参数：h : (a, b) in s.offDiag。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem not_isDiag_mk_of_mem_offDiag {a b : α} (h : (a, b) ∈ s.offDiag) : ¬ s(a, b).IsDiag := by
  simp at *; grind

section Sym2

variable {m : Sym2 α}

@[simp]
/-
**Finset.diag_mem_sym2_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：diag_mem_sym2_mem_iff : (forall b, b in Sym2.diag a -> b in s) ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mem_sym2_iff`：mem_sym2_iff {m : Sym2 α} : m in s.sym2 ↔ forall a 
in m, a in s
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finset.mk_mem_sym2_iff`：mk_mem_sym2_iff : s(a, b) in s.sym2 ↔ a in s ∧ b
 in s
· 使用定理 `and_self_iff`：∀ {a : Prop}, a ∧ a ↔ a
-/
theorem diag_mem_sym2_mem_iff : (∀ b, b ∈ Sym2.diag a → b ∈ s) ↔ a ∈ s := by
  rw [← mem_sym2_iff]
  exact mk_mem_sym2_iff.trans <| and_self_iff
/-
**Finset.diag_mem_sym2_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：diag_mem_sym2_iff : Sym2.diag a in s.sym2 ↔ a in s
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
theorem diag_mem_sym2_iff : Sym2.diag a ∈ s.sym2 ↔ a ∈ s := by simp [diag_mem_sym2_mem_iff]
/-
**Finset.image_diag_union_image_offDiag** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_diag_union_image_offDiag [DecidableEq α] : s.diag.image Sym2.mk.uncu
rry union s.offDiag.image Sym2.mk.uncurry = s.sym2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.image_union`：image_union [DecidableEq α] {f : α -> β} (s₁ s₂ : Fi
nset α) : (s₁ union s₂).image f = s₁.image f union s₂.image f
· 使用定理 `Finset.diag_union_offDiag`：diag_union_offDiag [DecidableEq α] : s.diag u
nion s.offDiag = s ×ˢ s
· 使用定理 `Finset.sym2_eq_image`：sym2_eq_image [DecidableEq α] : s.sym2 = (s ×ˢ s).
image Sym2.mk.uncurry
-/
theorem image_diag_union_image_offDiag [DecidableEq α] :
    s.diag.image Sym2.mk.uncurry ∪ s.offDiag.image Sym2.mk.uncurry = s.sym2 := by
  rw [← image_union, diag_union_offDiag, sym2_eq_image]

end Sym2

section Sym

variable [DecidableEq α] {n : ℕ}

/-- Lifts a finset to `Sym α n`. `s.sym n` is the finset of all unordered tuples of cardinality `n`
with elements in `s`. -/
/-
**Finset.sym** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{α : Type u_1} → [DecidableEq α] → Finset α → (n : ℕ) → Finset (Sym α n)
参数：n : ℕ；Sym α n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lifts a finset to `Sym α n`. `s.sym n` is the finset of all unordered tuples of 
cardinality `n`
with elements in `s`.
-/
protected def sym (s : Finset α) : ∀ n, Finset (Sym α n)
  | 0 => {∅}
  | n + 1 => s.sup fun a ↦ Finset.image (Sym.cons a) (s.sym n)

@[simp]
/-
**Finset.sym_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sym_zero : s.sym 0 = {∅}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sym_zero : s.sym 0 = {∅} := rfl

@[simp]
/-
**Finset.sym_succ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sym_succ : s.sym (n + 1) = s.sup fun a => (s.sym n).image Sym.cons a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sym_succ : s.sym (n + 1) = s.sup fun a ↦ (s.sym n).image <| Sym.cons a := rfl

@[simp]
/-
**Finset.mem_sym_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_sym_iff {m : Sym α n} : m in s.sym n ↔ forall a in m, a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `Finset.notMem_empty`：notMem_empty (a : α) : a ∉ (∅ : Finset α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Sym.eq_nil_of_card_zero`：eq_nil_of_card_zero (s : Sym α 0) : s = nil
· 使用定理 `Finset.mem_sup`：∀ {α : Type u_2} {ι : Type u_5} [inst : DecidableEq α] {
s : Finset ι} {f : ι → Finset α} {a : α},   a ∈ s.sup f ↔ ∃ i ∈ s, a ∈ f i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `Sym.mem_cons`：mem_cons : a in b ::ₛ s ↔ a = b ∨ a in s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Sym.exists_eq_cons_of_succ`：exists_eq_cons_of_succ (s : Sym α n.succ) : 
exists (a : α) (s' : Sym α n), s = a ::ₛ s'
· 使用定理 `Sym.mem_cons_self`：mem_cons_self (a : α) (s : Sym α n) : a in a ::ₛ s
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Sym.mem_cons_of_mem`：mem_cons_of_mem (h : a in s) : a in b ::ₛ s
-/
theorem mem_sym_iff {m : Sym α n} : m ∈ s.sym n ↔ ∀ a ∈ m, a ∈ s := by
  induction n with
  | zero =>
    refine mem_singleton.trans ⟨?_, fun _ ↦ Sym.eq_nil_of_card_zero _⟩
    rintro rfl
    exact fun a ha ↦ (Finset.notMem_empty _ ha).elim
  | succ n ih => ?_
  refine mem_sup.trans ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨a, ha, he⟩ b hb
    rw [mem_image] at he
    obtain ⟨m, he, rfl⟩ := he
    rw [Sym.mem_cons] at hb
    obtain rfl | hb := hb
    · exact ha
    · exact ih.1 he _ hb
  · obtain ⟨a, m, rfl⟩ := m.exists_eq_cons_of_succ
    exact
      ⟨a, h _ <| Sym.mem_cons_self _ _,
        mem_image_of_mem _ <| ih.2 fun b hb ↦ h _ <| Sym.mem_cons_of_mem hb⟩
/-
**Finset.sym_map** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sym_map [DecidableEq β] {n : Nat} (g : α ↪ β) (s : Finset α) : (s.map g).s
ym n = (s.sym n).map ⟨Sym.map g, Sym.map_injective g.injective _⟩
参数：g : α ↪ β；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Sym.map_injective`：map_injective {f : α -> β} (hf : Injective f) (n : Na
t) : Injective (map f : Sym α n -> Sym β n)
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Sym.map_congr`：map_congr {f g : α -> β} {s : Sym α n} (h : forall x in s
, f x = g x) : map f s = map g s
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Sym.map_map`：map_map {α β γ : Type*} {n : Nat} (g : β -> γ) (f : α -> β)
 (s : Sym α n) : Sym.map g (Sym.map f s) = Sym.map (g ∘ f) s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Sym.attach_map_coe`：attach_map_coe (s : Sym α n) : s.attach.map (↑) = s
· 使用定理 `Sym.mem_map`：mem_map {n : Nat} {f : α -> β} {b : β} {l : Sym α n} : b in
 Sym.map f l ↔ exists a, a in l ∧ f a = b
-/
lemma sym_map [DecidableEq β] {n : ℕ} (g : α ↪ β) (s : Finset α) :
    (s.map g).sym n = (s.sym n).map ⟨Sym.map g, Sym.map_injective g.injective _⟩ := by
  ext d
  simp only [mem_sym_iff, mem_map, Function.Embedding.coeFn_mk]
  refine ⟨fun hd ↦ ?_, fun ⟨b, hb, hd'⟩ d' hd ↦ ?_⟩
  · let g' : {x // x ∈ d} → α := fun ⟨x, hx⟩ ↦ (hd x hx).choose
    refine ⟨(fun p ↦ Sym.map g' p) d.attach, ?_, ?_⟩
    · simp only [Sym.mem_map, Sym.mem_attach, true_and, Subtype.exists, forall_exists_index, g']
      intro i e he hi
      rw [← hi]
      exact (hd e he).choose_spec.1
    · simp only [Sym.map_map, Function.comp_apply, g']
      convert! Sym.attach_map_coe d with ⟨x, hx⟩ hx'
      exact (hd x hx).choose_spec.2
  · rw [← hd', Sym.mem_map] at hd
    obtain ⟨a, ha, rfl⟩ := hd
    exact ⟨a, hb a ha, rfl⟩

#adaptation_note /-- https://github.com/leanprover/lean4/pull/8419: the simpNF complained -/
-- @[simp]
/-
**Finset.sym_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sym_empty (n : Nat) : (∅ : Finset α).sym (n + 1) = ∅
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sym_empty (n : ℕ) : (∅ : Finset α).sym (n + 1) = ∅ := rfl
/-
**Finset.replicate_mem_sym** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：replicate_mem_sym (ha : a in s) (n : Nat) : Sym.replicate n a in s.sym n
参数：ha : a in s；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_sym_iff`：mem_sym_iff {m : Sym α n} : m in s.sym n ↔ forall a 
in m, a in s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Sym.mem_replicate`：mem_replicate : b in replicate n a ↔ n != 0 ∧ b = a
-/
theorem replicate_mem_sym (ha : a ∈ s) (n : ℕ) : Sym.replicate n a ∈ s.sym n :=
  mem_sym_iff.2 fun b hb ↦ by rwa [(Sym.mem_replicate.1 hb).2]
/-
**Finset.Nonempty.sym** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_1} {s : Finset α} [inst : DecidableEq α], s.Nonempty → ∀ (n 
: ℕ), (s.sym n).Nonempty
参数：n : ℕ；s.sym n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.replicate_mem_sym`：replicate_mem_sym (ha : a in s) (n : Nat) : Sy
m.replicate n a in s.sym n
-/
protected theorem Nonempty.sym (h : s.Nonempty) (n : ℕ) : (s.sym n).Nonempty :=
  let ⟨_a, ha⟩ := h
  ⟨_, replicate_mem_sym ha n⟩

@[simp]
/-
**Finset.sym_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sym_singleton (a : α) (n : Nat) : ({a} : Finset α).sym n = {Sym.replicate 
n a}
参数：a : α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.eq_singleton_iff_unique_mem`：eq_singleton_iff_unique_mem {s : Fin
set α} {a : α} : s = {a} ↔ a in s ∧ forall x in s, x = a
· 使用定理 `Finset.replicate_mem_sym`：replicate_mem_sym (ha : a in s) (n : Nat) : Sy
m.replicate n a in s.sym n
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `Sym.eq_replicate_iff`：eq_replicate_iff : s = replicate n a ↔ forall b in
 s, b = a
· 使用定理 `Finset.eq_of_mem_singleton`：eq_of_mem_singleton {x y : α} (h : x in ({y}
 : Finset α)) : x = y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_sym_iff`：mem_sym_iff {m : Sym α n} : m in s.sym n ↔ forall a 
in m, a in s
-/
theorem sym_singleton (a : α) (n : ℕ) : ({a} : Finset α).sym n = {Sym.replicate n a} :=
  eq_singleton_iff_unique_mem.2
    ⟨replicate_mem_sym (mem_singleton.2 rfl) _, fun _s hs ↦
      Sym.eq_replicate_iff.2 fun _b hb ↦ eq_of_mem_singleton <| mem_sym_iff.1 hs _ hb⟩
/-
**Finset.eq_empty_of_sym_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：eq_empty_of_sym_eq_empty (h : s.sym n = ∅) : s = ∅
参数：h : s.sym n = ∅。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.Nonempty.sym`：∀ {α : Type u_1} {s : Finset α} [inst : DecidableEq
 α], s.Nonempty → ∀ (n : ℕ), (s.sym n).Nonempty
-/
theorem eq_empty_of_sym_eq_empty (h : s.sym n = ∅) : s = ∅ := by
  contrapose! h; exact h.sym _

@[simp]
/-
**Finset.sym_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sym_eq_empty : s.sym n = ∅ ↔ n != 0 ∧ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iff_of_false`：∀ {a b : Prop}, ¬a → ¬b → (a ↔ b)
· 使用定理 `Finset.singleton_ne_empty`：singleton_ne_empty (a : α) : ({a} : Finset α)
 != ∅
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `Finset.eq_empty_of_sym_eq_empty`：eq_empty_of_sym_eq_empty (h : s.sym n =
 ∅) : s = ∅
· 使用定理 `Finset.sym_empty`：sym_empty (n : Nat) : (∅ : Finset α).sym (n + 1) = ∅
-/
theorem sym_eq_empty : s.sym n = ∅ ↔ n ≠ 0 ∧ s = ∅ := by
  cases n
  · exact iff_of_false (singleton_ne_empty _) fun h ↦ (h.1 rfl).elim
  · refine ⟨fun h ↦ ⟨Nat.succ_ne_zero _, eq_empty_of_sym_eq_empty h⟩, ?_⟩
    rintro ⟨_, rfl⟩
    exact sym_empty _

@[simp]
/-
**Finset.sym_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sym_nonempty : (s.sym n).Nonempty ↔ n = 0 ∨ s.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sym_eq_empty`：sym_eq_empty : s.sym n = ∅ ↔ n != 0 ∧ s = ∅
-/
theorem sym_nonempty : (s.sym n).Nonempty ↔ n = 0 ∨ s.Nonempty := by
  contrapose!; exact sym_eq_empty

@[simp]
/-
**Finset.sym_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sym_univ [Fintype α] (n : Nat) : (univ : Finset α).sym n = univ
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.eq_univ_iff_forall`：eq_univ_iff_forall : s = univ ↔ forall x, x i
n s
· 使用定理 `Finset.mem_sym_iff`：mem_sym_iff {m : Sym α n} : m in s.sym n ↔ forall a 
in m, a in s
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
theorem sym_univ [Fintype α] (n : ℕ) : (univ : Finset α).sym n = univ :=
  eq_univ_iff_forall.2 fun _s ↦ mem_sym_iff.2 fun _a _ ↦ mem_univ _

@[simp]
/-
**Finset.sym_mono** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sym_mono (h : s subseteq t) (n : Nat) : s.sym n subseteq t.sym n
参数：h : s subseteq t；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_sym_iff`：mem_sym_iff {m : Sym α n} : m in s.sym n ↔ forall a 
in m, a in s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem sym_mono (h : s ⊆ t) (n : ℕ) : s.sym n ⊆ t.sym n := fun _m hm ↦
  mem_sym_iff.2 fun _a ha ↦ h <| mem_sym_iff.1 hm _ ha

@[simp]
/-
**Finset.sym_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sym_inter (s t : Finset α) (n : Nat) : (s inter t).sym n = s.sym n inter t
.sym n
参数：s t : Finset α；n : Nat。
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
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sym_inter (s t : Finset α) (n : ℕ) : (s ∩ t).sym n = s.sym n ∩ t.sym n := by
  ext m
  simp only [mem_inter, mem_sym_iff, imp_and, forall_and]

@[simp]
/-
**Finset.sym_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sym_union (s t : Finset α) (n : Nat) : s.sym n union t.sym n subseteq (s u
nion t).sym n
参数：s t : Finset α；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.union_subset`：union_subset (hs : s subseteq u) : t subseteq u -> 
s union t subseteq u
· 使用定理 `Finset.sym_mono`：sym_mono (h : s subseteq t) (n : Nat) : s.sym n subsete
q t.sym n
· 使用定理 `Finset.subset_union_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ⊆ s₁ ∪ s₂
· 使用定理 `Finset.subset_union_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s
₂ : Finset α}, s₂ ⊆ s₁ ∪ s₂
-/
theorem sym_union (s t : Finset α) (n : ℕ) : s.sym n ∪ t.sym n ⊆ (s ∪ t).sym n :=
  union_subset (sym_mono subset_union_left n) (sym_mono subset_union_right n)
/-
**Finset.sym_fill_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sym_fill_mem (a : α) {i : Fin (n + 1)} {m : Sym α (n - i)} (h : m in s.sym
 (n - i)) : m.fill a i in (insert a s).sym n
参数：a : α；n + 1；n - i；h : m in s.sym (n - i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_sym_iff`：mem_sym_iff {m : Sym α n} : m in s.sym n ↔ forall a 
in m, a in s
· 使用定理 `Finset.mem_insert`：mem_insert : a in insert b s ↔ a = b ∨ a in s
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Sym.mem_fill_iff`：mem_fill_iff {a b : α} {i : Fin (n + 1)} {s : Sym α (n
 - i)} : a in Sym.fill b i s ↔ (i : Nat) != 0 ∧ a = b ∨ a in s
-/
theorem sym_fill_mem (a : α) {i : Fin (n + 1)} {m : Sym α (n - i)} (h : m ∈ s.sym (n - i)) :
    m.fill a i ∈ (insert a s).sym n :=
  mem_sym_iff.2 fun b hb ↦
    mem_insert.2 <| (Sym.mem_fill_iff.1 hb).imp And.right <| mem_sym_iff.1 h b
/-
**Finset.sym_filterNe_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sym_filterNe_mem {m : Sym α n} (a : α) (h : m in s.sym n) : (m.filterNe a)
.2 in (Finset.erase s a).sym (n - (m.filterNe a).1)
参数：a : α；h : m in s.sym n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_sym_iff`：mem_sym_iff {m : Sym α n} : m in s.sym n ↔ forall a 
in m, a in s
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
· 使用定理 `And.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∧ b → c ∧ d
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `And.symm`：∀ {a b : Prop}, a ∧ b → b ∧ a
· 使用定理 `Multiset.mem_filter`：mem_filter {a : α} {s} : a in filter p s ↔ a in s ∧
 p a
-/
theorem sym_filterNe_mem {m : Sym α n} (a : α) (h : m ∈ s.sym n) :
    (m.filterNe a).2 ∈ (Finset.erase s a).sym (n - (m.filterNe a).1) :=
  mem_sym_iff.2 fun b H ↦
    mem_erase.2 <| (Multiset.mem_filter.1 H).symm.imp Ne.symm <| mem_sym_iff.1 h b

/-- If `a` does not belong to the finset `s`, then the `n`th symmetric power of `{a} ∪ s` is
  in 1-1 correspondence with the disjoint union of the `n - i`th symmetric powers of `s`,
  for `0 ≤ i ≤ n`. -/
@[simps]
/-
**Finset.symInsertEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：symInsertEquiv (h : a ∉ s) : (insert a s).sym n ≃ Σ i : Fin (n + 1), s.sym
 (n - i) where toFun m
参数：h : a ∉ s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `a` does not belong to the finset `s`, then the `n`th symmetric power of `{a}
 ∪ s` is
  in 1-1 correspondence with the disjoint union of the `n - i`th symmetric power
s of `s`,
  for `0 ≤ i ≤ n`.
-/
def symInsertEquiv (h : a ∉ s) : (insert a s).sym n ≃ Σ i : Fin (n + 1), s.sym (n - i) where
  toFun m := ⟨_, (m.1.filterNe a).2, by convert! sym_filterNe_mem a m.2; rw [erase_insert h]⟩
  invFun m := ⟨m.2.1.fill a m.1, sym_fill_mem a m.2.2⟩
  left_inv m := Subtype.ext <| m.1.fill_filterNe a
  right_inv := fun ⟨i, m, hm⟩ ↦ by
    refine Function.Injective.sigma_map (β₂ := ?_) (f₂ := ?_)
        (Function.injective_id) (fun i ↦ ?_) ?_
    · exact fun i ↦ Sym α (n - i)
    swap
    · exact Subtype.coe_injective
    refine Eq.trans ?_ (Sym.filter_ne_fill a _ ?_)
    exacts [rfl, h ∘ mem_sym_iff.1 hm a]

@[to_additive]
/-
**Finset.val_prod_eq_prod_count_pow** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：val_prod_eq_prod_count_pow [CommMonoid α] {n : Nat} {k : Sym α n} {s : Fin
set α} (hk : k in s.sym n) : k.val.prod = ∏ d in s, d ^ Multiset.count d k
参数：hk : k in s.sym n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_multiset_count_of_subset`：prod_multiset_count_of_subset [Dec
idableEq M] (m : Multiset M) (s : Finset M) (hs : m.toFinset subseteq s) : m.pro
d = ∏ i in s, i ^ m.count …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem val_prod_eq_prod_count_pow [CommMonoid α] {n : ℕ} {k : Sym α n}
    {s : Finset α} (hk : k ∈ s.sym n) :
    k.val.prod = ∏ d ∈ s, d ^ Multiset.count d k := by
  rw [Finset.prod_multiset_count_of_subset _ s]
  · apply Finset.prod_congr rfl (by simp)
  intro x hx
  simp only [Sym.val_eq_coe, Multiset.mem_toFinset, Sym.mem_coe] at hx
  simp only [Finset.mem_sym_iff] at hk
  exact hk x hx

end Sym

end Finset

