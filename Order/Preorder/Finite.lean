/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Hom.Set
public import Mathlib.Order.Minimal

/-!
# Finite preorders and finite sets in a preorder

This file shows that non-empty finite sets in a preorder have minimal/maximal elements, and
contrapositively that non-empty sets without minimal or maximal elements are infinite.

It also provides uniqueness results for order embeddings and order homomorphisms on finite linear
orders.
-/

public section

variable {ι α β : Type*}

namespace Finset
section IsTrans
variable [LE α] [IsTrans α LE.le] {s : Finset α} {a : α}

@[to_dual]
/-
**Finset.exists_maximalFor** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：exists_maximalFor (f : ι -> α) (s : Finset ι) (hs : s.Nonempty) : exists i
, MaximalFor (· in s) f i
参数：f : ι -> α；s : Finset ι；hs : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.cons_induction`：∀ {α : Type u_3} {motive : (s : Finset α
) → s.Nonempty → Prop},   (∀ (a : α), motive {a} ⋯) →     (∀ (a : α) (s : Finset
 α) (h : a ∉ s) (hs …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.mem_cons_self`：mem_cons_self (a : α) (s : Finset α) {h} : a in co
ns a s h
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.mem_cons_of_mem`：mem_cons_of_mem {a b : α} {s : Finset α} {hb : b
 ∉ s} (ha : a in s) : a in cons b s hb
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
-/
lemma exists_maximalFor (f : ι → α) (s : Finset ι) (hs : s.Nonempty) :
    ∃ i, MaximalFor (· ∈ s) f i := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => exact ⟨i, by simp⟩
  | @cons i s hi hs ih =>
    obtain ⟨j, hj⟩ := ih
    by_cases hji : f j ≤ f i
    · refine ⟨i, mem_cons_self .., ?_⟩
      simp only [mem_cons, forall_eq_or_imp, imp_self, true_and]
      exact fun k hk hik ↦ _root_.trans (hj.2 hk <| _root_.trans hji hik) hji
    · exact ⟨j, mem_cons_of_mem hj.1, by simpa [hji] using hj.2⟩

@[to_dual]
/-
**Finset.exists_maximal** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：exists_maximal (hs : s.Nonempty) : exists i, Maximal (· in s) i
参数：hs : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.exists_maximalFor`：exists_maximalFor (f : ι -> α) (s : Finset ι) 
(hs : s.Nonempty) : exists i, MaximalFor (· in s) f i
-/
lemma exists_maximal (hs : s.Nonempty) : ∃ i, Maximal (· ∈ s) i := s.exists_maximalFor id hs

end IsTrans

section Preorder
variable [Preorder α] {s : Finset α} {a : α}

@[to_dual]
/-
**Finset.exists_le_maximal** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：exists_le_maximal (s : Finset α) (ha : a in s) : exists b, a <= b ∧ Maxima
l (· in s) b
参数：s : Finset α；ha : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Finset.exists_maximal`：exists_maximal (hs : s.Nonempty) : exists i, Maxi
mal (· in s) i
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma exists_le_maximal (s : Finset α) (ha : a ∈ s) : ∃ b, a ≤ b ∧ Maximal (· ∈ s) b := by
  classical
  obtain ⟨b, hb, hab, hbmin⟩ : ∃ b ∈ s, a ≤ b ∧ _ := by
    simpa [Maximal, and_assoc] using {x ∈ s | a ≤ x}.exists_maximal ⟨a, mem_filter.2 ⟨ha, le_rfl⟩⟩
  exact ⟨b, hab, hb, fun c hc hbc ↦ hbmin hc (hab.trans hbc) hbc⟩

end Preorder
end Finset

namespace Set
section IsTrans
variable [LE α] [IsTrans α LE.le] {s : Set α} {a : α}

@[to_dual]
/-
**Set.Finite.exists_maximalFor** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} [inst : LE α] [IsTrans α LE.le] (f : ι → α
) (s : Set ι),   s.Finite → s.Nonempty → ∃ i, MaximalFor (fun x => x ∈ s) f i
参数：f : ι → α；s : Set ι；fun x => x ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用引理 `Finset.exists_maximalFor`：exists_maximalFor (f : ι -> α) (s : Finset ι) 
(hs : s.Nonempty) : exists i, MaximalFor (· in s) f i
-/
lemma Finite.exists_maximalFor (f : ι → α) (s : Set ι) (h : s.Finite) (hs : s.Nonempty) :
    ∃ i, MaximalFor (· ∈ s) f i := by
  lift s to Finset ι using h; exact s.exists_maximalFor f hs

@[to_dual]
/-
**Set.Finite.exists_maximal** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_2} [inst : LE α] [IsTrans α LE.le] {s : Set α}, s.Finite → s
.Nonempty → ∃ i, Maximal (fun x => x ∈ s) i
参数：fun x => x ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.exists_maximalFor`：∀ {ι : Type u_1} {α : Type u_2} [inst : LE
 α] [IsTrans α LE.le] (f : ι → α) (s : Set ι),   s.Finite → s.Nonempty → ∃ i, Ma
ximalFor (fun x =>…
-/
lemma Finite.exists_maximal (h : s.Finite) (hs : s.Nonempty) : ∃ i, Maximal (· ∈ s) i :=
  h.exists_maximalFor id _ hs

/-- A version of `Finite.exists_maximalFor` with the (weaker) hypothesis that the image of `s`
is finite rather than `s` itself. -/
@[to_dual /- A version of `Finite.exists_minimalFor` with the (weaker) hypothesis that the image of
`s` is finite rather than `s` itself.-/]
/-
**Set.Finite.exists_maximalFor'** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} [inst : LE α] [IsTrans α LE.le] (f : ι → α
) (s : Set ι),   (f '' s).Finite → s.Nonempty → ∃ i, MaximalFor (fun x => x ∈ s)
 f i
参数：f : ι → α；s : Set ι；f '' s；fun x => x ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.exists_maximalFor`：∀ {ι : Type u_1} {α : Type u_2} [inst : LE
 α] [IsTrans α LE.le] (f : ι → α) (s : Set ι),   s.Finite → s.Nonempty → ∃ i, Ma
ximalFor (fun x =>…
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
lemma Finite.exists_maximalFor' (f : ι → α) (s : Set ι) (h : (f '' s).Finite) (hs : s.Nonempty) :
    ∃ i, MaximalFor (· ∈ s) f i := by
  obtain ⟨_, ⟨a, ha, rfl⟩, hmax⟩ := Finite.exists_maximalFor id (f '' s) h (hs.image f)
  exact ⟨a, ha, fun a' ha' hf ↦ hmax (mem_image_of_mem f ha') hf⟩

end IsTrans

section Preorder
variable [Preorder α] {s : Set α} {a : α}

@[to_dual]
/-
**Set.Finite.exists_le_maximal** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_2} [inst : Preorder α] {s : Set α} {a : α}, s.Finite → a ∈ s
 → ∃ b, a ≤ b ∧ Maximal (fun x => x ∈ s) b
参数：fun x => x ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用引理 `Finset.exists_le_maximal`：exists_le_maximal (s : Finset α) (ha : a in s)
 : exists b, a <= b ∧ Maximal (· in s) b
-/
lemma Finite.exists_le_maximal (hs : s.Finite) (ha : a ∈ s) : ∃ b, a ≤ b ∧ Maximal (· ∈ s) b := by
  lift s to Finset α using hs; exact s.exists_le_maximal ha

variable [Nonempty α]
/-
**Set.infinite_of_forall_exists_gt** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：infinite_of_forall_exists_gt (h : forall a, exists b in s, a < b) : s.Infi
nite
参数：h : forall a, exists b in s, a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Set.infinite_of_injective_forall_mem`：infinite_of_injective_forall_mem [
Infinite α] {s : Set β} {f : α -> β} (hi : Injective f) (hf : forall x : α, f x 
in s) : s.Infinite
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `strictMono_nat_of_lt_succ`：strictMono_nat_of_lt_succ {f : Nat -> α} (hf 
: forall n, f n < f (n + 1)) : StrictMono f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma infinite_of_forall_exists_gt (h : ∀ a, ∃ b ∈ s, a < b) : s.Infinite := by
  inhabit α
  let f (n : ℕ) : α := Nat.recOn n (h default).choose fun _ a ↦ (h a).choose
  have hf : ∀ n, f n ∈ s := by rintro (_ | _) <;> exact (h _).choose_spec.1
  exact infinite_of_injective_forall_mem
    (strictMono_nat_of_lt_succ fun n => (h _).choose_spec.2).injective hf

@[to_dual existing infinite_of_forall_exists_gt]
/-
**Set.infinite_of_forall_exists_lt** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：infinite_of_forall_exists_lt (h : forall a, exists b in s, b < a) : s.Infi
nite
参数：h : forall a, exists b in s, b < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.infinite_of_forall_exists_gt`：infinite_of_forall_exists_gt (h : fora
ll a, exists b in s, a < b) : s.Infinite
· 使用定理 `OrderDual.instNonempty`：∀ (α : Type u_2) [h : Nonempty α], Nonempty αᵒᵈ
-/
lemma infinite_of_forall_exists_lt (h : ∀ a, ∃ b ∈ s, b < a) : s.Infinite :=
  infinite_of_forall_exists_gt (α := αᵒᵈ) h

end Preorder

section PartialOrder
variable (α) [PartialOrder α]

@[to_dual]
/-
**Set.finite_isTop** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：finite_isTop : {a : α | IsTop a}.Finite
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.finite`：∀ {α : Type u} {s : Set α}, s.Subsingleton → s.
Finite
· 使用定理 `Set.subsingleton_isTop`：subsingleton_isTop (α : Type*) [PartialOrder α] 
: { x : α | IsTop x }.Subsingleton
-/
lemma finite_isTop : {a : α | IsTop a}.Finite := (subsingleton_isTop α).finite

end PartialOrder

section LinearOrder
variable [LinearOrder α] {s : Set α} {t : Set β} {f : α → β}

/-
**Set.Infinite.exists_lt_map_eq_of_mapsTo** 是 Mathlib 中的一个定理，位于命名空间 `Set.Infinit
e`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : LinearOrder α] {s : Set α} {t : Se
t β} {f : α → β},   s.Infinite → Set.MapsTo f s t → t.Finite → ∃ x ∈ s, ∃ y ∈ s,
 x < y ∧ f x = f y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Infinite.exists_ne_map_eq_of_mapsTo`：∀ {α : Type u} {β : Type v} {s 
: Set α} {t : Set β} {f : α → β},   s.Infinite → Set.MapsTo f s t → t.Finite → ∃
 x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x …
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Infinite.exists_lt_map_eq_of_mapsTo (hs : s.Infinite) (hf : MapsTo f s t) (ht : t.Finite) :
    ∃ x ∈ s, ∃ y ∈ s, x < y ∧ f x = f y :=
  let ⟨x, hx, y, hy, hxy, hf⟩ := hs.exists_ne_map_eq_of_mapsTo hf ht
  hxy.lt_or_gt.elim (fun hxy => ⟨x, hx, y, hy, hxy, hf⟩) fun hyx => ⟨y, hy, x, hx, hyx, hf.symm⟩
/-
**Set.Finite.exists_lt_map_eq_of_forall_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finit
e`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : LinearOrder α] {t : Set β} {f : α 
→ β} [Infinite α],   (∀ (a : α), f a ∈ t) → t.Finite → ∃ a b, a < b ∧ f a = f b
参数：∀ (a : α), f a ∈ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Infinite.exists_lt_map_eq_of_mapsTo`：∀ {α : Type u_2} {β : Type u_3}
 [inst : LinearOrder α] {s : Set α} {t : Set β} {f : α → β},   s.Infinite → Set.
MapsTo f s t → t.Finite → ∃ x…
· 使用定理 `Set.infinite_univ`：infinite_univ [h : Infinite α] : (@univ α).Infinite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.mapsTo_univ_iff`：mapsTo_univ_iff : MapsTo f univ t ↔ forall x, f x i
n t
-/
lemma Finite.exists_lt_map_eq_of_forall_mem [Infinite α] (hf : ∀ a, f a ∈ t) (ht : t.Finite) :
    ∃ a b, a < b ∧ f a = f b := by
  rw [← mapsTo_univ_iff] at hf
  obtain ⟨a, -, b, -, h⟩ := infinite_univ.exists_lt_map_eq_of_mapsTo hf ht
  exact ⟨a, b, h⟩

/-- If the cofinality of a linear order is finite, it's at most one. -/
/-
**Set.Finite.exists_subsingleton_isCofinal** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite
`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrder α] {s : Set α}, s.Finite → IsCofinal 
s → ∃ t, t.Subsingleton ∧ IsCofinal t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Finite.exists_maximal`：∀ {α : Type u_2} [inst : LE α] [IsTrans α LE.
le] {s : Set α}, s.Finite → s.Nonempty → ∃ i, Maximal (fun x => x ∈ s) i
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Maximal.le`：∀ {α : Type u_2} {P : α → Prop} {x y : α} [inst : LinearOrde
r α], Maximal P x → P y → y ≤ x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
If the cofinality of a linear order is finite, it's at most one.
-/
theorem Finite.exists_subsingleton_isCofinal {s : Set α} (hs : s.Finite) (hs' : IsCofinal s) :
    ∃ t : Set α, t.Subsingleton ∧ IsCofinal t := by
  obtain rfl | hn := s.eq_empty_or_nonempty
  · use ∅; simpa
  · obtain ⟨a, ha⟩ := hs.exists_maximal hn
    use {a}
    suffices IsTop a by simpa [IsCofinal]
    intro b
    obtain ⟨c, hc, hbc⟩ := hs' b
    exact hbc.trans (ha.le hc)

end LinearOrder
end Set

section Preorder
variable [Preorder α] [Finite α] {p : α → Prop} {a : α}

@[to_dual]
/-
**Finite.exists_le_maximal** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Finite.exists_le_maximal (hs : s.Finite) (ha : a in s) : exists b, a <= b 
∧ Maximal (· in s) b
参数：hs : s.Finite；ha : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.exists_le_maximal`：∀ {α : Type u_2} [inst : Preorder α] {s : 
Set α} {a : α}, s.Finite → a ∈ s → ∃ b, a ≤ b ∧ Maximal (fun x => x ∈ s) b
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
-/
lemma Finite.exists_le_maximal (h : p a) : ∃ b, a ≤ b ∧ Maximal p b :=
  {x | p x}.toFinite.exists_le_maximal h

end Preorder

@[elab_as_elim, deprecated "Use `WellFoundedLT.induction _ h` instead." (since := "2026-04-10")]
/-
**LinearOrder.strong_induction_of_finite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearOrder.strong_induction_of_finite {α : Type*} [LinearOrder α] [Finite
 α] {motive : α -> Prop} (h : forall (j : α) (_ : forall (k : α), k < j -> motiv
e k), motive j) (i : α) : motive i
参数：h : forall (j : α) (_ : forall (k : α), k < j -> motive k), motive j；i : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFoundedLT.induction`：induction {motive : α -> Prop} (a : α) (ind : f
orall x, (forall y, y < x -> motive y) -> motive x) : motive a
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Finite.to_wellFoundedLT`：∀ {α : Type u_1} [Finite α] [inst : Preorder α]
, WellFoundedLT α
-/
lemma LinearOrder.strong_induction_of_finite
    {α : Type*} [LinearOrder α] [Finite α] {motive : α → Prop}
    (h : ∀ (j : α) (_ : ∀ (k : α), k < j → motive k), motive j) (i : α) :
    motive i := WellFoundedLT.induction _ h
/-
**OrderEmbedding.range_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：OrderEmbedding.range_eq_iff {α β : Type*} [LinearOrder α] [PartialOrder β]
 [Finite α] {f g : α ↪o β} : Set.range f = Set.range g ↔ f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.strictMonoOn`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   StrictMono f → ∀ (s : Set α), StrictMonoOn
 f s
· 使用定理 `OrderEmbedding.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preor
der α] [inst_1 : Preorder β] (f : α ↪o β), StrictMono ⇑f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `isWellOrder_gt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedGT α],
 IsWellOrder α fun x1 x2 => x2 < x1
· 使用定理 `Finite.to_wellFoundedGT`：∀ {α : Type u_1} [Finite α] [inst : Preorder α]
, WellFoundedGT α
· 使用定理 `RelEmbedding.ext`：ext ⦃f g : r ↪r s⦄ (h : forall x, f x = g x) : f = g
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `OrderIso.apply_symm_apply`：apply_symm_apply (e : α ≃o β) (x : β) : e (e.
symm x) = x
-/
lemma OrderEmbedding.range_eq_iff
    {α β : Type*} [LinearOrder α] [PartialOrder β] [Finite α]
    {f g : α ↪o β} :
    Set.range f = Set.range g ↔ f = g := by
  refine ⟨fun h ↦ ?_, by rintro rfl; rfl⟩
  let ef := (f.strictMono.strictMonoOn .univ).orderIso
  let eg := (g.strictMono.strictMonoOn .univ).orderIso
  let i : f '' .univ ≃o g '' .univ :=
    { __ := Equiv.setCongr (by simpa using! h)
      map_rel_iff' := by rfl }
  have : (ef.trans i).trans eg.symm = .refl _ := by
    exact Subsingleton.elim _ _
  ext x
  simpa only [OrderIso.trans_apply, OrderIso.apply_symm_apply, OrderIso.refl_apply, Subtype.ext_iff]
    using! congr(eg ($this ⟨x, Set.mem_univ x⟩))
/-
**OrderHom.range_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：OrderHom.range_eq_iff {α β : Type*} [LinearOrder α] [PartialOrder β] [Fini
te α] {f g : α ->o β} (hf : Function.Injective f) (hg : Function.Injective g) : 
Set.range f = Set.range g ↔ f = g
参数：hf : Function.Injective f；hg : Function.Injective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.ext`：ext (f g : α ->o β) (h : (f : α -> β) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Monotone.strictMono_of_injective`：Monotone.strictMono_of_injective (h₁ :
 Monotone f) (h₂ : Injective f) : StrictMono f
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `OrderEmbedding.range_eq_iff`：OrderEmbedding.range_eq_iff {α β : Type*} [
LinearOrder α] [PartialOrder β] [Finite α] {f g : α ↪o β} : Set.range f = Set.ra
nge g ↔ f = g
-/
lemma OrderHom.range_eq_iff {α β : Type*} [LinearOrder α] [PartialOrder β]
    [Finite α] {f g : α →o β}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Set.range f = Set.range g ↔ f = g := by
  refine ⟨fun h ↦ ?_, by rintro rfl; rfl⟩
  ext : 2
  exact DFunLike.congr_fun ((OrderEmbedding.range_eq_iff
    (f := .ofStrictMono f (f.monotone.strictMono_of_injective hf))
    (g := .ofStrictMono g (g.monotone.strictMono_of_injective hg))).1 (by simpa)) _
/-
**OrderHom.eq_id_of_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：OrderHom.eq_id_of_injective {α : Type*} [LinearOrder α] [Finite α] (f : α 
->o α) (hf : Function.Injective f) : f = .id
参数：f : α ->o α；hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `OrderHom.range_eq_iff`：OrderHom.range_eq_iff {α β : Type*} [LinearOrder 
α] [PartialOrder β] [Finite α] {f g : α ->o β} (hf : Function.Injective f) (hg :
 Function.I…
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderHom.id_coe`：∀ {α : Type u_2} [inst : Preorder α], ⇑OrderHom.id = id
· 使用定理 `Set.range_id`：range_id : range (@id α) = univ
· 使用定理 `Finite.surjective_of_injective`：surjective_of_injective {f : α -> α} (hi
nj : Injective f) : Surjective f
-/
lemma OrderHom.eq_id_of_injective {α : Type*} [LinearOrder α] [Finite α] (f : α →o α)
    (hf : Function.Injective f) :
    f = .id :=
  (range_eq_iff hf Function.injective_id).1 (by
    simpa [Set.range_eq_univ] using Finite.surjective_of_injective hf)

/-- A strictly monotone self-map of a finite linear order is the identity. -/
/-
**StrictMono.eq_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMono.eq_id {α : Type*} [LinearOrder α] [Finite α] {f : α -> α} (hf :
 StrictMono f) : f = id
参数：hf : StrictMono f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `StrictMono.le_id`：StrictMono.le_id [WellFoundedGT β] {f : β -> β} (hf : 
StrictMono f) : f <= id
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `isWellOrder_gt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedGT α],
 IsWellOrder α fun x1 x2 => x2 < x1
· 使用定理 `Finite.to_wellFoundedGT`：∀ {α : Type u_1} [Finite α] [inst : Preorder α]
, WellFoundedGT α
· 使用定理 `StrictMono.id_le`：StrictMono.id_le [WellFoundedLT β] {f : β -> β} (hf : 
StrictMono f) : id <= f
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Finite.to_wellFoundedLT`：∀ {α : Type u_1} [Finite α] [inst : Preorder α]
, WellFoundedLT α

--- 原说明 ---
A strictly monotone self-map of a finite linear order is the identity.
-/
theorem StrictMono.eq_id {α : Type*} [LinearOrder α] [Finite α] {f : α → α}
    (hf : StrictMono f) : f = id :=
  le_antisymm hf.le_id hf.id_le

/-- A strictly monotone self-map of a finite linear order fixes every point. -/
/-
**StrictMono.apply_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMono.apply_eq {α : Type*} [LinearOrder α] [Finite α] {f : α -> α} {x
 : α} (hf : StrictMono f) : f x = x
参数：hf : StrictMono f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `StrictMono.eq_id`：StrictMono.eq_id {α : Type*} [LinearOrder α] [Finite α
] {f : α -> α} (hf : StrictMono f) : f = id

--- 原说明 ---
A strictly monotone self-map of a finite linear order fixes every point.
-/
theorem StrictMono.apply_eq {α : Type*} [LinearOrder α] [Finite α] {f : α → α}
    {x : α} (hf : StrictMono f) : f x = x :=
  congrFun hf.eq_id x
