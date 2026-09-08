/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Multiset.Antidiagonal

import Mathlib.Data.Finsupp.Order

/-!
# The `Finsupp` counterpart of `Multiset.antidiagonal`.

The antidiagonal of `s : α →₀ ℕ` consists of
all pairs `(t₁, t₂) : (α →₀ ℕ) × (α →₀ ℕ)` such that `t₁ + t₂ = s`.
-/

@[expose] public section

namespace Finsupp

open Finset

universe u

variable {α : Type u} [DecidableEq α]

/-- The `Finsupp` counterpart of `Multiset.antidiagonal`: the antidiagonal of
`s : α →₀ ℕ` consists of all pairs `(t₁, t₂) : (α →₀ ℕ) × (α →₀ ℕ)` such that `t₁ + t₂ = s`.
The finitely supported function `antidiagonal s` is equal to the multiplicities of these pairs. -/
/-
**Finsupp.antidiagonal'** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：antidiagonal' (f : α ->₀ Nat) : (α ->₀ Nat) × (α ->₀ Nat) ->₀ Nat
参数：f : α ->₀ Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Finsupp` counterpart of `Multiset.antidiagonal`: the antidiagonal of
`s : α →₀ ℕ` consists of all pairs `(t₁, t₂) : (α →₀ ℕ) × (α →₀ ℕ)` such that `t
₁ + t₂ = s`.
The finitely supported function `antidiagonal s` is equal to the multiplicities 
of these pairs.
-/
noncomputable def antidiagonal' (f : α →₀ ℕ) : (α →₀ ℕ) × (α →₀ ℕ) →₀ ℕ :=
  Multiset.toFinsupp
    ((Finsupp.toMultiset f).antidiagonal.map (Prod.map Multiset.toFinsupp Multiset.toFinsupp))

/-- The antidiagonal of `s : α →₀ ℕ` is the finset of all pairs `(t₁, t₂) : (α →₀ ℕ) × (α →₀ ℕ)`
such that `t₁ + t₂ = s`. -/
/-
**Finsupp.instHasAntidiagonal** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：instHasAntidiagonal : HasAntidiagonal (α ->₀ Nat) where antidiagonal f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The antidiagonal of `s : α →₀ ℕ` is the finset of all pairs `(t₁, t₂) : (α →₀ ℕ)
 × (α →₀ ℕ)`
such that `t₁ + t₂ = s`.
-/
noncomputable instance instHasAntidiagonal : HasAntidiagonal (α →₀ ℕ) where
  antidiagonal f := f.antidiagonal'.support
  mem_antidiagonal {f} {p} := by
    rcases p with ⟨p₁, p₂⟩
    simp [antidiagonal', ← and_assoc, Multiset.toFinsupp_eq_iff,
    ← Multiset.toFinsupp_eq_iff (f := f)]

@[simp]
/-
**Finsupp.antidiagonal_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：antidiagonal_zero : antidiagonal (0 : α ->₀ Nat) = singleton (0, 0)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem antidiagonal_zero : antidiagonal (0 : α →₀ ℕ) = singleton (0, 0) := rfl

@[to_additive]
/-
**Finsupp.prod_antidiagonal_swap** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：prod_antidiagonal_swap {M : Type*} [CommMonoid M] (n : α ->₀ Nat) (f : (α 
->₀ Nat) -> (α ->₀ Nat) -> M) : ∏ p in antidiagonal n, f p.1 p.2 = ∏ p in antidi
agonal n, f p.2 p.1
参数：n : α ->₀ Nat；f : (α ->₀ Nat) -> (α ->₀ Nat) -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.prod_equiv`：prod_equiv (e : ι ≃ κ) (hst : forall i, i in s ↔ e i 
in t) (hfg : forall i in s, f i = g (e i)) : ∏ i in s, f i = ∏ i in t, g i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_antidiagonal_swap {M : Type*} [CommMonoid M] (n : α →₀ ℕ)
    (f : (α →₀ ℕ) → (α →₀ ℕ) → M) :
    ∏ p ∈ antidiagonal n, f p.1 p.2 = ∏ p ∈ antidiagonal n, f p.2 p.1 :=
  prod_equiv (Equiv.prodComm _ _) (by simp [add_comm]) (by simp)

@[simp]
/-
**Finsupp.antidiagonal_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：antidiagonal_single (a : α) (n : Nat) : antidiagonal (single a n) = (antid
iagonal n).map (Function.Embedding.prodMap ⟨_, single_injective a⟩ ⟨_, single_in
jective a⟩)
参数：a : α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Finsupp.single_injective`：single_injective (a : α) : Function.Injective 
(single a : M -> α ->₀ M)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `Decidable.eq_or_ne`：Decidable.eq_or_ne {α : Sort*} (x y : α) [Decidable 
(x = y)] : x = y ∨ x != y
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `And.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∧ b → c ∧ d
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用引理 `Finsupp.single_add`：single_add (a : ι) (b₁ b₂ : M) : single a (b₁ + b₂) 
= single a b₁ + single a b₂
-/
theorem antidiagonal_single (a : α) (n : ℕ) :
    antidiagonal (single a n) = (antidiagonal n).map
      (Function.Embedding.prodMap ⟨_, single_injective a⟩ ⟨_, single_injective a⟩) := by
  ext ⟨x, y⟩
  simp only [mem_antidiagonal, mem_map, mem_antidiagonal, Function.Embedding.coe_prodMap,
    Function.Embedding.coeFn_mk, Prod.map_apply, Prod.mk.injEq, Prod.exists]
  constructor
  · intro h
    refine ⟨x a, y a, DFunLike.congr_fun h a |>.trans single_eq_same, ?_⟩
    simp_rw [DFunLike.ext_iff, ← forall_and]
    intro i
    replace h := DFunLike.congr_fun h i
    simp_rw [single_apply, Finsupp.add_apply] at h ⊢
    obtain rfl | hai := Decidable.eq_or_ne a i
    · exact ⟨if_pos rfl, if_pos rfl⟩
    · simp_rw [if_neg hai, add_eq_zero] at h ⊢
      exact h.imp Eq.symm Eq.symm
  · rintro ⟨a, b, rfl, rfl, rfl⟩
    exact (single_add _ _ _).symm
/-
**Finsupp.image_prodMap_embDomain_antidiagonal** 是 Mathlib 中的一个定理，位于命名空间 `Finsup
p`。
形式化陈述：image_prodMap_embDomain_antidiagonal {β : Type*} [DecidableEq β] (f : α ↪ 
β) (y : α ->₀ Nat) : image (Prod.map (embDomain f) (embDomain f)) (antidiagonal 
y) = antidiagonal (embDomain f y)
参数：f : α ↪ β；y : α ->₀ Nat。
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
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finsupp.embDomain_add`：embDomain_add (f : ι ↪ F) (v w : ι ->₀ M) : embDo
main f (v + w) = embDomain f v + embDomain f w
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Finsupp.comapDomain_add_of_injective`：comapDomain_add_of_injective (hf :
 Function.Injective f) (v₁ v₂ : β ->₀ M) : comapDomain f (v₁ + v₂) hf.injOn = co
mapDomain f v₁ hf.injOn + …
· 使用定理 `Finsupp.comapDomain_embDomain`：comapDomain_embDomain (f : α ↪ β) (l : α 
->₀ M) : comapDomain f (embDomain f l) f.injective.injOn = l
· 使用引理 `Finsupp.embDomain_comapDomain`：embDomain_comapDomain {f : α ↪ β} {g : β 
->₀ M} (hg : ↑g.support subseteq Set.range f) : embDomain f (comapDomain f g f.i
njective.injOn) = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Finsupp.mem_range_embDomain_iff`：mem_range_embDomain_iff [AddCommMonoid 
M] (f : α ↪ β) (x : β ->₀ M) : x in Set.range (embDomain f) ↔ ↑x.support subsete
q Set.range f
· 使用定理 `Finsupp.isLowerSet_range_embDomain`：isLowerSet_range_embDomain (f : α ↪ 
β) : IsLowerSet ((Set.range (embDomain f)) : Set (β ->₀ Nat))
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_iff_exists_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [Canoni
callyOrderedAdd α] {a b : α}, a ≤ b ↔ ∃ c, b = a + c
· 使用定理 `Finsupp.instCanonicallyOrderedAddOfAddLeftMono`：∀ {ι : Type u_1} {α : Ty
pe u_3} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [CanonicallyOrderedAd
d α]   [inst_3 : Sub α] [OrderedSub …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `le_iff_exists_add'`：∀ {α : Type u} [inst : AddCommMagma α] [inst_1 : Pre
order α] [CanonicallyOrderedAdd α] {a b : α}, a ≤ b ↔ ∃ c, b = c + a
-/
theorem image_prodMap_embDomain_antidiagonal {β : Type*} [DecidableEq β] (f : α ↪ β)
    (y : α →₀ ℕ) : image (Prod.map (embDomain f) (embDomain f)) (antidiagonal y) =
      antidiagonal (embDomain f y) := by
  ext ⟨u, v⟩
  simp only [mem_image, mem_antidiagonal, Prod.exists, Prod.map_apply,
    Prod.mk.injEq]
  refine ⟨fun ⟨w, z, h, hw, hz⟩ ↦ ?_, fun h ↦ ⟨u.comapDomain f f.injective.injOn,
    ⟨v.comapDomain f f.injective.injOn, ?_, ?_, ?_⟩⟩⟩
  · rw [← hw, ← hz, ← embDomain_add, h]
  · rw [← comapDomain_add_of_injective f.injective, h, comapDomain_embDomain]
  · rw [embDomain_comapDomain ((mem_range_embDomain_iff ..).mp
      (isLowerSet_range_embDomain f (le_iff_exists_add.mpr ⟨v, h.symm⟩) (by simp)))]
  · rw [embDomain_comapDomain ((mem_range_embDomain_iff ..).mp
      (isLowerSet_range_embDomain f (le_iff_exists_add'.mpr ⟨u, h.symm⟩) (by simp)))]

open Finset in
/-
**Finsupp.image_sumElim_product_antidiagonal** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`
。
形式化陈述：image_sumElim_product_antidiagonal {β : Type*} [DecidableEq β] {x : α ->₀ 
Nat} {y : β ->₀ Nat} : image (fun ((x, y), z, w) => (x.sumElim z, y.sumElim w)) 
(antidiagonal x ×ˢ antidiagonal y) = antidiagonal (x.sumElim y)
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
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finsupp.sumElim_add`：sumElim_add [AddZeroClass M] (a b : α ->₀ M) (c d :
 β ->₀ M) : (a + b).sumElim (c + d) = a.sumElim c + b.sumElim d
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
· 使用定理 `Finsupp.comapDomain_add_of_injective`：comapDomain_add_of_injective (hf :
 Function.Injective f) (v₁ v₂ : β ->₀ M) : comapDomain f (v₁ + v₂) hf.injOn = co
mapDomain f v₁ hf.injOn + …
· 使用引理 `Finsupp.comapDomain_inl_sumElim`：comapDomain_inl_sumElim (f : α ->₀ γ) (
g : β ->₀ γ) : comapDomain Sum.inl (f.sumElim g) Sum.inl_injective.injOn = f
· 使用引理 `Finsupp.comapDomain_inr_sumElim`：comapDomain_inr_sumElim (f : α ->₀ γ) (
g : β ->₀ γ) : comapDomain Sum.inr (f.sumElim g) Sum.inr_injective.injOn = g
· 使用引理 `Finsupp.comapDomain_sumElim_comapDomain`：comapDomain_sumElim_comapDomain
 (c : α oplus β ->₀ γ) : (comapDomain Sum.inl c Sum.inl_injective.injOn).sumElim
 (comapDomain Sum.inr c Sum.i…
-/
theorem image_sumElim_product_antidiagonal {β : Type*} [DecidableEq β] {x : α →₀ ℕ}
    {y : β →₀ ℕ} : image (fun ((x, y), z, w) ↦ (x.sumElim z, y.sumElim w))
      (antidiagonal x ×ˢ antidiagonal y) = antidiagonal (x.sumElim y) := by
  ext ⟨u, v⟩
  simp only [mem_antidiagonal, mem_image, mem_product, Prod.mk.injEq, Prod.exists]
  refine ⟨fun ⟨a, b, a', b', h1, h2, h3⟩ ↦ ?_, fun h ↦
    ⟨u.comapDomain Sum.inl Sum.inl_injective.injOn, v.comapDomain Sum.inl Sum.inl_injective.injOn,
    u.comapDomain Sum.inr Sum.inr_injective.injOn, v.comapDomain Sum.inr Sum.inr_injective.injOn,
    ⟨?_, ?_⟩, comapDomain_sumElim_comapDomain .., comapDomain_sumElim_comapDomain ..⟩⟩
  · rw [← h2, ← h3, ← sumElim_add, h1.left, h1.right]
  · rw [← comapDomain_add_of_injective Sum.inl_injective, h, comapDomain_inl_sumElim]
  · rw [← comapDomain_add_of_injective Sum.inr_injective, h, comapDomain_inr_sumElim]

end Finsupp

