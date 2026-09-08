/-
Copyright (c) 2020 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Torsion

/-!
# Basic results on subgroups

We prove basic results on the definitions of subgroups. The bundled subgroups use bundled monoid
homomorphisms.

Special thanks goes to Amelia Livingston and Yury Kudryashov for their help and inspiration.

## Main definitions

Notation used here:

- `G N` are `Group`s

- `A` is an `AddGroup`

- `H K` are `Subgroup`s of `G` or `AddSubgroup`s of `A`

- `x` is an element of type `G` or type `A`

- `f g : N →* G` are group homomorphisms

- `s k` are sets of elements of type `G`

Definitions in the file:

* `Subgroup.prod H K` : the product of subgroups `H`, `K` of groups `G`, `N` respectively, `H × K`
  is a subgroup of `G × N`

## Implementation notes

Subgroup inclusion is denoted `≤` rather than `⊆`, although `∈` is defined as
membership of a subgroup's underlying set.

## Tags
subgroup, subgroups
-/

@[expose] public section

assert_not_exists IsOrderedMonoid Multiset Ring

open Function
open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']
variable {A : Type*} [AddGroup A]

section SubgroupClass

variable {M S : Type*} [DivInvMonoid M] [SetLike S M] [hSM : SubgroupClass S M] {H K : S}

variable [SetLike S G] [SubgroupClass S G]

@[to_additive]
/-
**div_mem_comm_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_mem_comm_iff {a b : G} : a / b in H ↔ b / a in H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_mem_iff`：inv_mem_iff {S G} [InvolutiveInv G] {_ : SetLike S G} [InvM
emClass S G] {H : S} {x : G} : x⁻¹ in H ↔ x in H
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
-/
theorem div_mem_comm_iff {a b : G} : a / b ∈ H ↔ b / a ∈ H :=
  inv_div b a ▸ inv_mem_iff

end SubgroupClass

namespace Subgroup

variable (H K : Subgroup G)

@[to_additive]
/-
**Subgroup.div_mem_comm_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {a b : G}, a / b ∈ H ↔ 
b / a ∈ H
参数：H : Subgroup G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `div_mem_comm_iff`：div_mem_comm_iff {a b : G} : a / b in H ↔ b / a in H
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
protected theorem div_mem_comm_iff {a b : G} : a / b ∈ H ↔ b / a ∈ H :=
  div_mem_comm_iff

variable {k : Set G}

open Set

variable {N : Type*} [Group N] {P : Type*} [Group P]

/-- Given `Subgroup`s `H`, `K` of groups `G`, `N` respectively, `H × K` as a subgroup of `G × N`. -/
@[to_additive prod
      /-- Given `AddSubgroup`s `H`, `K` of `AddGroup`s `A`, `B` respectively, `H × K`
      as an `AddSubgroup` of `A × B`. -/]
/-
**Subgroup.prod** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：prod (H : Subgroup G) (K : Subgroup N) : Subgroup (G × N)
参数：H : Subgroup G；K : Subgroup N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def prod (H : Subgroup G) (K : Subgroup N) : Subgroup (G × N) :=
  { Submonoid.prod H.toSubmonoid K.toSubmonoid with
    inv_mem' := fun hx => ⟨H.inv_mem' hx.1, K.inv_mem' hx.2⟩ }

@[to_additive (attr := norm_cast) coe_prod]
/-
**Subgroup.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：coe_prod (H : Subgroup G) (K : Subgroup N) : (H.prod K : Set (G × N)) = (H
 : Set G) ×ˢ (K : Set N)
参数：H : Subgroup G；K : Subgroup N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prod (H : Subgroup G) (K : Subgroup N) :
    (H.prod K : Set (G × N)) = (H : Set G) ×ˢ (K : Set N) :=
  rfl

@[to_additive mem_prod]
/-
**Subgroup.mem_prod** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mem_prod {H : Subgroup G} {K : Subgroup N} {p : G × N} : p in H.prod K ↔ p
.1 in H ∧ p.2 in K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_prod {H : Subgroup G} {K : Subgroup N} {p : G × N} : p ∈ H.prod K ↔ p.1 ∈ H ∧ p.2 ∈ K :=
  Iff.rfl

open scoped Relator in
@[to_additive prod_mono]
/-
**Subgroup.prod_mono** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：prod_mono : ((· <= ·) ⇒ (· <= ·) ⇒ (· <= ·)) (@prod G _ N _) (@prod G _ N 
_)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.prod_mono`：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s
₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
-/
theorem prod_mono : ((· ≤ ·) ⇒ (· ≤ ·) ⇒ (· ≤ ·)) (@prod G _ N _) (@prod G _ N _) :=
  fun _s _s' hs _t _t' ht => Set.prod_mono hs ht

@[to_additive prod_mono_right]
/-
**Subgroup.prod_mono_right** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：prod_mono_right (K : Subgroup G) : Monotone fun t : Subgroup N => K.prod t
参数：K : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.prod_mono`：prod_mono : ((· <= ·) ⇒ (· <= ·) ⇒ (· <= ·)) (@prod 
G _ N _) (@prod G _ N _)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem prod_mono_right (K : Subgroup G) : Monotone fun t : Subgroup N => K.prod t :=
  prod_mono (le_refl K)

@[to_additive prod_mono_left]
/-
**Subgroup.prod_mono_left** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：prod_mono_left (H : Subgroup N) : Monotone fun K : Subgroup G => K.prod H
参数：H : Subgroup N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.prod_mono`：prod_mono : ((· <= ·) ⇒ (· <= ·) ⇒ (· <= ·)) (@prod 
G _ N _) (@prod G _ N _)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem prod_mono_left (H : Subgroup N) : Monotone fun K : Subgroup G => K.prod H := fun _ _ hs =>
  prod_mono hs (le_refl H)

@[to_additive prod_top]
/-
**Subgroup.prod_top** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：prod_top (K : Subgroup G) : K.prod (⊤ : Subgroup N) = K.comap (MonoidHom.f
st G N)
参数：K : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_top (K : Subgroup G) : K.prod (⊤ : Subgroup N) = K.comap (MonoidHom.fst G N) :=
  ext fun x => by simp [mem_prod, MonoidHom.coe_fst]

@[to_additive top_prod]
/-
**Subgroup.top_prod** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：top_prod (H : Subgroup N) : (⊤ : Subgroup G).prod H = H.comap (MonoidHom.s
nd G N)
参数：H : Subgroup N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem top_prod (H : Subgroup N) : (⊤ : Subgroup G).prod H = H.comap (MonoidHom.snd G N) :=
  ext fun x => by simp [mem_prod, MonoidHom.coe_snd]

@[to_additive (attr := simp) top_prod_top]
/-
**Subgroup.top_prod_top** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：top_prod_top : (⊤ : Subgroup G).prod (⊤ : Subgroup N) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subgroup.top_prod`：top_prod (H : Subgroup N) : (⊤ : Subgroup G).prod H =
 H.comap (MonoidHom.snd G N)
· 使用定理 `Subgroup.comap_top`：comap_top (f : G ->* N) : (⊤ : Subgroup N).comap f =
 ⊤
-/
theorem top_prod_top : (⊤ : Subgroup G).prod (⊤ : Subgroup N) = ⊤ :=
  (top_prod _).trans <| comap_top _

@[to_additive (attr := simp) bot_prod_bot]
/-
**Subgroup.bot_prod_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：bot_prod_bot : (⊥ : Subgroup G).prod (⊥ : Subgroup N) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.singleton_prod_singleton`：singleton_prod_singleton : ({a} : Set α) ×
ˢ ({b} : Set β) = {(a, b)}
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem bot_prod_bot : (⊥ : Subgroup G).prod (⊥ : Subgroup N) = ⊥ :=
  SetLike.coe_injective <| by simp [coe_prod]

@[to_additive le_prod_iff]
/-
**Subgroup.le_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：le_prod_iff {H : Subgroup G} {K : Subgroup N} {J : Subgroup (G × N)} : J <
= H.prod K ↔ map (MonoidHom.fst G N) J <= H ∧ map (MonoidHom.snd G N) J <= K
参数：G × N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.le_prod_iff`：le_prod_iff {s : Submonoid M} {t : Submonoid N} {
u : Submonoid (M × N)} : u <= s.prod t ↔ u.map (fst M N) <= s ∧ u.map (snd M N) 
<= t
-/
theorem le_prod_iff {H : Subgroup G} {K : Subgroup N} {J : Subgroup (G × N)} :
    J ≤ H.prod K ↔ map (MonoidHom.fst G N) J ≤ H ∧ map (MonoidHom.snd G N) J ≤ K := by
  simpa only [← Subgroup.toSubmonoid_le] using! Submonoid.le_prod_iff

@[to_additive prod_le_iff]
/-
**Subgroup.prod_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：prod_le_iff {H : Subgroup G} {K : Subgroup N} {J : Subgroup (G × N)} : H.p
rod K <= J ↔ map (MonoidHom.inl G N) H <= J ∧ map (MonoidHom.inr G N) K <= J
参数：G × N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.prod_le_iff`：prod_le_iff {s : Submonoid M} {t : Submonoid N} {
u : Submonoid (M × N)} : s.prod t <= u ↔ s.map (inl M N) <= u ∧ t.map (inr M N) 
<= u
-/
theorem prod_le_iff {H : Subgroup G} {K : Subgroup N} {J : Subgroup (G × N)} :
    H.prod K ≤ J ↔ map (MonoidHom.inl G N) H ≤ J ∧ map (MonoidHom.inr G N) K ≤ J := by
  simpa only [← Subgroup.toSubmonoid_le] using! Submonoid.prod_le_iff

@[to_additive (attr := simp) prod_eq_bot_iff]
/-
**Subgroup.prod_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：prod_eq_bot_iff {H : Subgroup G} {K : Subgroup N} : H.prod K = ⊥ ↔ H = ⊥ ∧
 K = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.prod_eq_bot_iff`：prod_eq_bot_iff {s : Submonoid M} {t : Submon
oid N} : s.prod t = ⊥ ↔ s = ⊥ ∧ t = ⊥
-/
theorem prod_eq_bot_iff {H : Subgroup G} {K : Subgroup N} : H.prod K = ⊥ ↔ H = ⊥ ∧ K = ⊥ := by
  simpa only [← Subgroup.toSubmonoid_inj] using! Submonoid.prod_eq_bot_iff

@[to_additive closure_prod]
/-
**Subgroup.closure_prod** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：closure_prod {s : Set G} {t : Set N} (hs : 1 in s) (ht : 1 in t) : closure
 (s ×ˢ t) = (closure s).prod (closure t)
参数：hs : 1 in s；ht : 1 in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.closure_le`：closure_le : closure k <= K ↔ k subseteq K
· 使用定理 `Set.prod_subset_prod_iff`：prod_subset_prod_iff : s ×ˢ t subseteq s₁ ×ˢ t
₁ ↔ s subseteq s₁ ∧ t subseteq t₁ ∨ s = ∅ ∨ t = ∅
· 使用定理 `Subgroup.subset_closure`：subset_closure : k subseteq closure k
· 使用定理 `Subgroup.prod_le_iff`：prod_le_iff {H : Subgroup G} {K : Subgroup N} {J :
 Subgroup (G × N)} : H.prod K <= J ↔ map (MonoidHom.inl G N) H <= J ∧ map (Monoi
dHom.inr G…
· 使用定理 `Subgroup.map_le_iff_le_comap`：map_le_iff_le_comap {f : G ->* N} {K : Sub
group G} {H : Subgroup N} : K.map f <= H ↔ K <= H.comap f
-/
theorem closure_prod {s : Set G} {t : Set N} (hs : 1 ∈ s) (ht : 1 ∈ t) :
    closure (s ×ˢ t) = (closure s).prod (closure t) :=
  le_antisymm
    (closure_le _ |>.2 <| Set.prod_subset_prod_iff.2 <| .inl ⟨subset_closure, subset_closure⟩)
    (prod_le_iff.2 ⟨
      map_le_iff_le_comap.2 <| closure_le _ |>.2 fun _x hx => subset_closure ⟨hx, ht⟩,
      map_le_iff_le_comap.2 <| closure_le _ |>.2 fun _y hy => subset_closure ⟨hs, hy⟩⟩)

/-- Product of subgroups is isomorphic to their product as groups. -/
@[to_additive prodEquiv
      /-- Product of additive subgroups is isomorphic to their product
      as additive groups -/]
/-
**Subgroup.prodEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：prodEquiv (H : Subgroup G) (K : Subgroup N) : H.prod K ≃* H × K
参数：H : Subgroup G；K : Subgroup N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def prodEquiv (H : Subgroup G) (K : Subgroup N) : H.prod K ≃* H × K :=
  { Equiv.Set.prod (H : Set G) (K : Set N) with map_mul' := fun _ _ => rfl }

section Pi

variable {η : Type*} {f : η → Type*}

variable [∀ i, Group (f i)]

/-- A version of `Set.pi` for subgroups. Given an index set `I` and a family of submodules
`s : Π i, Subgroup f i`, `pi I s` is the subgroup of dependent functions `f : Π i, f i` such that
`f i` belongs to `pi I s` whenever `i ∈ I`. -/
@[to_additive
      /-- A version of `Set.pi` for `AddSubgroup`s. Given an index set `I` and a family
      of submodules `s : Π i, AddSubgroup f i`, `pi I s` is the `AddSubgroup` of dependent functions
      `f : Π i, f i` such that `f i` belongs to `pi I s` whenever `i ∈ I`. -/]
/-
**Subgroup.pi** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：pi (I : Set η) (H : forall i, Subgroup (f i)) : Subgroup (forall i, f i)
参数：I : Set η；H : forall i, Subgroup (f i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def pi (I : Set η) (H : ∀ i, Subgroup (f i)) : Subgroup (∀ i, f i) :=
  { Submonoid.pi I fun i => (H i).toSubmonoid with
    inv_mem' := fun hp i hI => (H i).inv_mem (hp i hI) }

@[to_additive]
/-
**Subgroup.coe_pi** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：coe_pi (I : Set η) (H : forall i, Subgroup (f i)) : (pi I H : Set (forall 
i, f i)) = Set.pi I fun i => (H i : Set (f i))
参数：I : Set η；H : forall i, Subgroup (f i)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pi (I : Set η) (H : ∀ i, Subgroup (f i)) :
    (pi I H : Set (∀ i, f i)) = Set.pi I fun i => (H i : Set (f i)) :=
  rfl

@[to_additive]
/-
**Subgroup.mem_pi** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mem_pi (I : Set η) {H : forall i, Subgroup (f i)} {p : forall i, f i} : p 
in pi I H ↔ forall i : η, i in I -> p i in H i
参数：I : Set η；f i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_pi (I : Set η) {H : ∀ i, Subgroup (f i)} {p : ∀ i, f i} :
    p ∈ pi I H ↔ ∀ i : η, i ∈ I → p i ∈ H i :=
  Iff.rfl

@[to_additive]
/-
**Subgroup.pi_top** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：pi_top (I : Set η) : (pi I fun i => (⊤ : Subgroup (f i))) = ⊤
参数：I : Set η。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
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
theorem pi_top (I : Set η) : (pi I fun i => (⊤ : Subgroup (f i))) = ⊤ :=
  ext fun x => by simp [mem_pi]

@[to_additive]
/-
**Subgroup.pi_empty** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：pi_empty (H : forall i, Subgroup (f i)) : pi ∅ H = ⊤
参数：H : forall i, Subgroup (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
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
-/
theorem pi_empty (H : ∀ i, Subgroup (f i)) : pi ∅ H = ⊤ :=
  ext fun x => by simp [mem_pi]

@[to_additive]
/-
**Subgroup.pi_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：pi_bot : (pi Set.univ fun i => (⊥ : Subgroup (f i))) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
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
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pi_bot : (pi Set.univ fun i => (⊥ : Subgroup (f i))) = ⊥ :=
  ext fun x => by simp [mem_pi, funext_iff]

@[to_additive]
/-
**Subgroup.le_pi_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：le_pi_iff {I : Set η} {H : forall i, Subgroup (f i)} {J : Subgroup (forall
 i, f i)} : J <= pi I H ↔ forall i in I, J <= comap (Pi.evalMonoidHom f i) (H i)
参数：f i；forall i, f i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_pi_iff`：subset_pi_iff {s'} : s' subseteq pi s t ↔ forall i in
 s, s' subseteq (· i) ⁻¹' t i
-/
theorem le_pi_iff {I : Set η} {H : ∀ i, Subgroup (f i)} {J : Subgroup (∀ i, f i)} :
    J ≤ pi I H ↔ ∀ i ∈ I, J ≤ comap (Pi.evalMonoidHom f i) (H i) :=
  Set.subset_pi_iff

@[to_additive (attr := simp)]
/-
**Subgroup.mulSingle_mem_pi** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mulSingle_mem_pi [DecidableEq η] {I : Set η} {H : forall i, Subgroup (f i)
} (i : η) (x : f i) : Pi.mulSingle i x in pi I H ↔ i in I -> x in H i
参数：f i；i : η；x : f i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.update_mem_pi_iff_of_mem`：update_mem_pi_iff_of_mem [DecidableEq ι] {
a : forall i, α i} {i : ι} {b : α i} (ha : a in pi s t) : update a i b in pi s t
 ↔ i in s -> b in …
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
theorem mulSingle_mem_pi [DecidableEq η] {I : Set η} {H : ∀ i, Subgroup (f i)} (i : η) (x : f i) :
    Pi.mulSingle i x ∈ pi I H ↔ i ∈ I → x ∈ H i :=
  Set.update_mem_pi_iff_of_mem (one_mem (pi I H))

@[to_additive]
/-
**Subgroup.pi_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：pi_eq_bot_iff (H : forall i, Subgroup (f i)) : pi Set.univ H = ⊥ ↔ forall 
i, H i = ⊥
参数：H : forall i, Subgroup (f i)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Set.univ_pi_eq_singleton_iff`：univ_pi_eq_singleton_iff {a} : pi univ t =
 {a} ↔ forall i, t i = {a i}
-/
theorem pi_eq_bot_iff (H : ∀ i, Subgroup (f i)) : pi Set.univ H = ⊥ ↔ ∀ i, H i = ⊥ := by
  simp_rw [SetLike.ext'_iff]
  exact Set.univ_pi_eq_singleton_iff

end Pi

@[to_additive]
/-
**Subgroup.instIsMulTorsionFree** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：instIsMulTorsionFree [IsMulTorsionFree G] : IsMulTorsionFree H where pow_l
eft_injective n hn a b
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `pow_left_injective`：pow_left_injective (hn : n != 0) : Injective fun a :
 M => a ^ n
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
instance instIsMulTorsionFree [IsMulTorsionFree G] : IsMulTorsionFree H where
  pow_left_injective n hn a b := by
    have := pow_left_injective hn (M := G) (a₁ := a) (a₂ := b)
    dsimp at *
    norm_cast at this

end Subgroup

namespace Subgroup

variable {H K : Subgroup G}

variable (H)

/-- A subgroup is characteristic if it is fixed by all automorphisms.
  Several equivalent conditions are provided by lemmas of the form `Characteristic.iff...` -/
/-
**Subgroup.Characteristic** 是 Mathlib 中的一个归纳类型，位于命名空间 `Subgroup`。
形式化陈述：{G : Type u_1} → [inst : Group G] → Subgroup G → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subgroup is characteristic if it is fixed by all automorphisms.
  Several equivalent conditions are provided by lemmas of the form `Characterist
ic.iff...`
-/
structure Characteristic : Prop where
  /-- `H` is fixed by all automorphisms -/
  fixed : ∀ ϕ : G ≃* G, H.comap ϕ.toMonoidHom = H

attribute [class] Characteristic
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) normal_of_characteristic [h : H.Characteristic] : H.Normal :=
  ⟨fun a ha b => (SetLike.ext_iff.mp (h.fixed (MulAut.conj b)) a).mpr ha⟩

end Subgroup

namespace AddSubgroup

variable (H : AddSubgroup A)

/-- An `AddSubgroup` is characteristic if it is fixed by all automorphisms.
  Several equivalent conditions are provided by lemmas of the form `Characteristic.iff...` -/
/-
**AddSubgroup.Characteristic** 是 Mathlib 中的一个归纳类型，位于命名空间 `AddSubgroup`。
形式化陈述：{A : Type u_4} → [inst : AddGroup A] → AddSubgroup A → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `AddSubgroup` is characteristic if it is fixed by all automorphisms.
  Several equivalent conditions are provided by lemmas of the form `Characterist
ic.iff...`
-/
structure Characteristic : Prop where
  /-- `H` is fixed by all automorphisms -/
  fixed : ∀ ϕ : A ≃+ A, H.comap ϕ.toAddMonoidHom = H

attribute [to_additive] Subgroup.Characteristic

attribute [class] Characteristic
/-
**AddSubgroup.** 是 Mathlib 中的一个实例，位于命名空间 `AddSubgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) normal_of_characteristic [h : H.Characteristic] : H.Normal :=
  ⟨fun a ha b => (SetLike.ext_iff.mp (h.fixed (AddAut.addConj b)) a).mpr ha⟩

end AddSubgroup

namespace Subgroup

/-- The whole group `G` is normal. -/
@[to_additive (attr := simp) /-- The whole group `G` is normal. -/]
/-
**Subgroup.normal_top** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：normal_top : (⊤ : Subgroup G).Normal where conj_mem _ a _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The whole group `G` is normal.
-/
instance normal_top : (⊤ : Subgroup G).Normal where
  conj_mem _ a _ := a

/-- The trivial subgroup `{1}` is normal. -/
@[to_additive (attr := simp) /-- The trivial subgroup `{0}` is normal. -/]
/-
**Subgroup.normal_bot** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：normal_bot : (⊥ : Subgroup G).Normal where conj_mem
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
The trivial subgroup `{1}` is normal.
-/
instance normal_bot : (⊥ : Subgroup G).Normal where
  conj_mem := by simp

variable {H K : Subgroup G}

@[to_additive]
/-
**Subgroup.characteristic_iff_comap_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：characteristic_iff_comap_eq : H.Characteristic ↔ forall ϕ : G ≃* G, H.coma
p ϕ.toMonoidHom = H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.Characteristic.fixed`：∀ {G : Type u_1} [inst : Group G] {H : Su
bgroup G},   H.Characteristic → ∀ (ϕ : G ≃* G), Subgroup.comap ϕ.toMonoidHom H =
 H
-/
theorem characteristic_iff_comap_eq : H.Characteristic ↔ ∀ ϕ : G ≃* G, H.comap ϕ.toMonoidHom = H :=
  ⟨Characteristic.fixed, Characteristic.mk⟩

@[to_additive]
/-
**Subgroup.characteristic_iff_comap_le** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：characteristic_iff_comap_le : H.Characteristic ↔ forall ϕ : G ≃* G, H.coma
p ϕ.toMonoidHom <= H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Subgroup.characteristic_iff_comap_eq`：characteristic_iff_comap_eq : H.Ch
aracteristic ↔ forall ϕ : G ≃* G, H.comap ϕ.toMonoidHom = H
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MulEquiv.symm_apply_apply`：symm_apply_apply (e : M ≃* N) (x : M) : e.sym
m (e x) = x
-/
theorem characteristic_iff_comap_le : H.Characteristic ↔ ∀ ϕ : G ≃* G, H.comap ϕ.toMonoidHom ≤ H :=
  characteristic_iff_comap_eq.trans
    ⟨fun h ϕ => le_of_eq (h ϕ), fun h ϕ =>
      le_antisymm (h ϕ) fun g hg => h ϕ.symm ((congr_arg (· ∈ H) (ϕ.symm_apply_apply g)).mpr hg)⟩

@[to_additive]
/-
**Subgroup.characteristic_iff_le_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：characteristic_iff_le_comap : H.Characteristic ↔ forall ϕ : G ≃* G, H <= H
.comap ϕ.toMonoidHom
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Subgroup.characteristic_iff_comap_eq`：characteristic_iff_comap_eq : H.Ch
aracteristic ↔ forall ϕ : G ≃* G, H.comap ϕ.toMonoidHom = H
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MulEquiv.symm_apply_apply`：symm_apply_apply (e : M ≃* N) (x : M) : e.sym
m (e x) = x
-/
theorem characteristic_iff_le_comap : H.Characteristic ↔ ∀ ϕ : G ≃* G, H ≤ H.comap ϕ.toMonoidHom :=
  characteristic_iff_comap_eq.trans
    ⟨fun h ϕ => ge_of_eq (h ϕ), fun h ϕ =>
      le_antisymm (fun g hg => (congr_arg (· ∈ H) (ϕ.symm_apply_apply g)).mp (h ϕ.symm hg)) (h ϕ)⟩

@[to_additive]
/-
**Subgroup.characteristic_iff_map_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：characteristic_iff_map_eq : H.Characteristic ↔ forall ϕ : G ≃* G, H.map ϕ.
toMonoidHom = H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subgroup.map_equiv_eq_comap_symm'`：map_equiv_eq_comap_symm' (f : G ≃* N)
 (K : Subgroup G) : K.map f.toMonoidHom = K.comap f.symm.toMonoidHom
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Subgroup.characteristic_iff_comap_eq`：characteristic_iff_comap_eq : H.Ch
aracteristic ↔ forall ϕ : G ≃* G, H.comap ϕ.toMonoidHom = H
-/
theorem characteristic_iff_map_eq : H.Characteristic ↔ ∀ ϕ : G ≃* G, H.map ϕ.toMonoidHom = H := by
  simp_rw [map_equiv_eq_comap_symm']
  exact characteristic_iff_comap_eq.trans ⟨fun h ϕ => h ϕ.symm, fun h ϕ => h ϕ.symm⟩

@[to_additive]
/-
**Subgroup.characteristic_iff_map_le** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：characteristic_iff_map_le : H.Characteristic ↔ forall ϕ : G ≃* G, H.map ϕ.
toMonoidHom <= H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subgroup.map_equiv_eq_comap_symm'`：map_equiv_eq_comap_symm' (f : G ≃* N)
 (K : Subgroup G) : K.map f.toMonoidHom = K.comap f.symm.toMonoidHom
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Subgroup.characteristic_iff_comap_le`：characteristic_iff_comap_le : H.Ch
aracteristic ↔ forall ϕ : G ≃* G, H.comap ϕ.toMonoidHom <= H
-/
theorem characteristic_iff_map_le : H.Characteristic ↔ ∀ ϕ : G ≃* G, H.map ϕ.toMonoidHom ≤ H := by
  simp_rw [map_equiv_eq_comap_symm']
  exact characteristic_iff_comap_le.trans ⟨fun h ϕ => h ϕ.symm, fun h ϕ => h ϕ.symm⟩

@[to_additive]
/-
**Subgroup.characteristic_iff_le_map** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：characteristic_iff_le_map : H.Characteristic ↔ forall ϕ : G ≃* G, H <= H.m
ap ϕ.toMonoidHom
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Subgroup.map_equiv_eq_comap_symm'`：map_equiv_eq_comap_symm' (f : G ≃* N)
 (K : Subgroup G) : K.map f.toMonoidHom = K.comap f.symm.toMonoidHom
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Subgroup.characteristic_iff_le_comap`：characteristic_iff_le_comap : H.Ch
aracteristic ↔ forall ϕ : G ≃* G, H <= H.comap ϕ.toMonoidHom
-/
theorem characteristic_iff_le_map : H.Characteristic ↔ ∀ ϕ : G ≃* G, H ≤ H.map ϕ.toMonoidHom := by
  simp_rw [map_equiv_eq_comap_symm']
  exact characteristic_iff_le_comap.trans ⟨fun h ϕ => h ϕ.symm, fun h ϕ => h ϕ.symm⟩

@[to_additive]
/-
**Subgroup.botCharacteristic** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：botCharacteristic : Characteristic (⊥ : Subgroup G)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.characteristic_iff_le_map`：characteristic_iff_le_map : H.Charac
teristic ↔ forall ϕ : G ≃* G, H <= H.map ϕ.toMonoidHom
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
instance botCharacteristic : Characteristic (⊥ : Subgroup G) :=
  characteristic_iff_le_map.mpr fun _ϕ => bot_le

@[to_additive]
/-
**Subgroup.topCharacteristic** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：topCharacteristic : Characteristic (⊤ : Subgroup G)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.characteristic_iff_map_le`：characteristic_iff_map_le : H.Charac
teristic ↔ forall ϕ : G ≃* G, H.map ϕ.toMonoidHom <= H
· 使用定理 `le_top`：le_top : a <= ⊤
-/
instance topCharacteristic : Characteristic (⊤ : Subgroup G) :=
  characteristic_iff_map_le.mpr fun _ϕ => le_top

@[to_additive]
/-
**Subgroup.characteristic_sup** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：characteristic_sup [H.Characteristic] [K.Characteristic] : (H ⊔ K).Charact
eristic
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `Subgroup.map_sup`：map_sup (H K : Subgroup G) (f : G ->* N) : (H ⊔ K).map
 f = H.map f ⊔ K.map f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
instance characteristic_sup [H.Characteristic] [K.Characteristic] :
    (H ⊔ K).Characteristic := by
  simp_all [characteristic_iff_map_eq, map_sup]

@[to_additive]
/-
**Subgroup.characteristic_iSup** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：characteristic_iSup {ι : Sort*} {H : ι -> Subgroup G} [forall i, (H i).Cha
racteristic] : (⨆ i, H i).Characteristic
参数：H i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `Subgroup.map_iSup`：map_iSup {ι : Sort*} (f : G ->* N) (s : ι -> Subgroup
 G) : (iSup s).map f = ⨆ i, (s i).map f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
instance characteristic_iSup {ι : Sort*} {H : ι → Subgroup G} [∀ i, (H i).Characteristic] :
    (⨆ i, H i).Characteristic := by
  simp_all [characteristic_iff_map_eq, map_iSup]

@[to_additive]
/-
**Subgroup.characteristic_biSup** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：characteristic_biSup {ι : Type*} {s : Set ι} {H : ι -> Subgroup G} (h : fo
rall i in s, (H i).Characteristic) : (⨆ i in s, H i).Characteristic
参数：h : forall i in s, (H i).Characteristic。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem characteristic_biSup {ι : Type*} {s : Set ι} {H : ι → Subgroup G}
    (h : ∀ i ∈ s, (H i).Characteristic) : (⨆ i ∈ s, H i).Characteristic := by
  simp [← iSup_subtype'', characteristic_iSup, h]

@[to_additive]
/-
**Subgroup.characteristic_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：characteristic_sSup {Hs : Set (Subgroup G)} (h : forall H in Hs, H.Charact
eristic) : (sSup Hs).Characteristic
参数：Subgroup G；h : forall H in Hs, H.Characteristic。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_eq_iSup'`：sSup_eq_iSup' (s : Set α) : sSup s = ⨆ a : s, (a : α)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem characteristic_sSup {Hs : Set (Subgroup G)} (h : ∀ H ∈ Hs, H.Characteristic) :
    (sSup Hs).Characteristic := by
  simp [sSup_eq_iSup', characteristic_iSup, h]

@[to_additive]
/-
**Subgroup.characteristic_inf** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：characteristic_inf [H.Characteristic] [K.Characteristic] : (H ⊓ K).Charact
eristic
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `Subgroup.comap_inf`：comap_inf (H K : Subgroup N) (f : G ->* N) : (H ⊓ K)
.comap f = H.comap f ⊓ K.comap f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
instance characteristic_inf [H.Characteristic] [K.Characteristic] :
    (H ⊓ K).Characteristic := by
  simp_all [characteristic_iff_comap_eq, comap_inf]

@[to_additive]
/-
**Subgroup.characteristic_iInf** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：characteristic_iInf {ι : Sort*} {H : ι -> Subgroup G} [forall i, (H i).Cha
racteristic] : (⨅ i, H i).Characteristic
参数：H i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `Subgroup.comap_iInf`：comap_iInf {ι : Sort*} (f : G ->* N) (s : ι -> Subg
roup N) : (iInf s).comap f = ⨅ i, (s i).comap f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
instance characteristic_iInf {ι : Sort*} {H : ι → Subgroup G} [∀ i, (H i).Characteristic] :
    (⨅ i, H i).Characteristic := by
  simp_all [characteristic_iff_comap_eq, comap_iInf]

@[to_additive]
/-
**Subgroup.characteristic_biInf** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：characteristic_biInf {ι : Type*} {s : Set ι} {H : ι -> Subgroup G} (h : fo
rall i in s, (H i).Characteristic) : (⨅ i in s, H i).Characteristic
参数：h : forall i in s, (H i).Characteristic。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem characteristic_biInf {ι : Type*} {s : Set ι} {H : ι → Subgroup G}
    (h : ∀ i ∈ s, (H i).Characteristic) : (⨅ i ∈ s, H i).Characteristic := by
  simp [← iInf_subtype'', characteristic_iInf, h]

@[to_additive]
/-
**Subgroup.characteristic_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：characteristic_sInf {Hs : Set (Subgroup G)} (h : forall H in Hs, H.Charact
eristic) : (sInf Hs).Characteristic
参数：Subgroup G；h : forall H in Hs, H.Characteristic。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sInf_eq_iInf'`：∀ {α : Type u_1} [inst : InfSet α] (s : Set α), sInf s = 
⨅ a, ↑a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem characteristic_sInf {Hs : Set (Subgroup G)} (h : ∀ H ∈ Hs, H.Characteristic) :
    (sInf Hs).Characteristic := by
  simp [sInf_eq_iInf', characteristic_iInf, h]

/-- If `H` is a characteristic subgroup of `G`, then every automorphism of `G` induces an
automorphism of `H`. -/
@[to_additive (attr := simps!)
  /-- If `H` is a characteristic additive subgroup of `G`, then every automorphism of `G` induces an
  automorphism of `H`. -/]
/-
**Subgroup._root_.MulAut.characteristic** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def _root_.MulAut.characteristic (H : Subgroup G) [H.Characteristic] : MulAut G →* MulAut H where
  toFun φ :=
    { toFun := fun h => ⟨φ h, characteristic_iff_le_comap.mp inferInstance φ h.2⟩
      invFun := fun h => ⟨φ.symm h, characteristic_iff_le_comap.mp inferInstance φ.symm h.2⟩
      left_inv h := Subtype.ext (φ.symm_apply_apply h)
      right_inv h := Subtype.ext (φ.apply_symm_apply h)
      map_mul' h k := Subtype.ext (map_mul φ (h : G) (k : G)) }
  map_one' := rfl
  map_mul' _ _ := rfl

/-- If `H` is a characteristic subgroup of `G` and `K` is a characteristic subgroup of `H`, then
`K` is a characteristic subgroup of `G`. -/
@[to_additive
  /-- If `H` is a characteristic additive subgroup of `G` and `K` is a characteristic additive
  subgroup of `H`, then `K` is a characteristic additive subgroup of `G`. -/]
/-
**Subgroup.characteristic_of_characteristic_of_characteristic** 是 Mathlib 中的一个实例
，位于命名空间 `Subgroup`。
形式化陈述：characteristic_of_characteristic_of_characteristic [H.Characteristic] {K :
 Subgroup H} [hK : K.Characteristic] : (K.map H.subtype).Characteristic
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.characteristic_iff_map_eq`：characteristic_iff_map_eq : H.Charac
teristic ↔ forall ϕ : G ≃* G, H.map ϕ.toMonoidHom = H
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.map_map`：map_map (g : N ->* P) (f : G ->* N) : (K.map f).map g 
= K.map (g.comp f)
-/
instance characteristic_of_characteristic_of_characteristic [H.Characteristic]
    {K : Subgroup H} [hK : K.Characteristic] : (K.map H.subtype).Characteristic := by
  refine characteristic_iff_map_eq.2 fun φ ↦ ?_
  have := congr_arg (map H.subtype) <| characteristic_iff_map_eq.1 hK (MulAut.characteristic H φ)
  simpa [Subgroup.map_map, MulAut.characteristic]

variable (H)

section Normalizer

@[to_additive]
/-
**Subgroup.normalizer_empty** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：normalizer_empty : normalizer (∅ : Set G) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `trivial`：True
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem normalizer_empty : normalizer (∅ : Set G) = ⊤ :=
  ext fun _ ↦ ⟨fun _ ↦ trivial, fun _ _ ↦ .rfl⟩

@[to_additive]
/-
**Subgroup._root_.CommGroup.normalizer_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Subgrou
p`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.CommGroup.normalizer_eq_top {G : Type*} [CommGroup G] (s : Set G) :
    normalizer s = ⊤ := by
  ext
  simp [mem_set_normalizer_iff]

@[to_additive]
/-
**Subgroup.mem_normalizer_iff_conj_image_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`
。
形式化陈述：mem_normalizer_iff_conj_image_eq {s : Set G} {g : G} : g in normalizer s ↔
 MulAut.conj g '' s = s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_normalizer_iff_conj_image_eq {s : Set G} {g : G} :
    g ∈ normalizer s ↔ MulAut.conj g '' s = s := by
  simp_rw [mem_set_normalizer_iff'', Set.ext_iff, Set.mem_image, MulAut.conj_apply]
  refine forall_congr' fun h ↦ ?_
  simp_rw [mul_inv_eq_iff_eq_mul, ← eq_inv_mul_iff_mul_eq, ← mul_assoc, exists_eq_right, iff_comm]

@[to_additive]
/-
**Subgroup.mem_normalizer_iff_map_conj_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mem_normalizer_iff_map_conj_eq {H : Subgroup G} {g : G} : g in normalizer 
H ↔ H.map (MulAut.conj g) = H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `Subgroup.mem_normalizer_iff_conj_image_eq`：mem_normalizer_iff_conj_image
_eq {s : Set G} {g : G} : g in normalizer s ↔ MulAut.conj g '' s = s
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
-/
theorem mem_normalizer_iff_map_conj_eq {H : Subgroup G} {g : G} :
    g ∈ normalizer H ↔ H.map (MulAut.conj g) = H :=
  .trans mem_normalizer_iff_conj_image_eq (.symm SetLike.ext'_iff)

@[deprecated (since := "2026-05-12")]
alias _root_.AddSubgroup.mem_normalizer_iff_conj_image_eq :=
  AddSubgroup.mem_normalizer_iff_addConj_image_eq

@[to_additive]
/-
**Subgroup.normalizer_le_normalizer_closure** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`
。
形式化陈述：normalizer_le_normalizer_closure (s : Set G) : normalizer s <= normalizer 
(closure s)
参数：s : Set G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.mem_normalizer_iff_map_conj_eq`：mem_normalizer_iff_map_conj_eq 
{H : Subgroup G} {g : G} : g in normalizer H ↔ H.map (MulAut.conj g) = H
· 使用定理 `MonoidHom.map_closure`：map_closure (f : G ->* N) (s : Set G) : (closure 
s).map f = closure (f '' s)
· 使用定理 `MonoidHom.coe_coe`：MonoidHom.coe_coe [MonoidHomClass F M N] (f : F) : ((
f : M ->* N) : M -> N) = f
· 使用定理 `Subgroup.mem_normalizer_iff_conj_image_eq`：mem_normalizer_iff_conj_image
_eq {s : Set G} {g : G} : g in normalizer s ↔ MulAut.conj g '' s = s
-/
theorem normalizer_le_normalizer_closure (s : Set G) : normalizer s ≤ normalizer (closure s) := by
  intro g hg
  rw [mem_normalizer_iff_conj_image_eq] at hg
  rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_closure, MonoidHom.coe_coe, hg]

variable {H}

@[to_additive]
/-
**Subgroup.normalizer_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：normalizer_eq_top_iff : normalizer (H : Set G) = ⊤ ↔ H.Normal
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.mem_top`：mem_top (x : G) : x in (⊤ : Subgroup G)
· 使用定理 `Subgroup.Normal.conj_mem`：∀ {G : Type u_1} [inst : Group G] {H : Subgrou
p G}, H.Normal → ∀ n ∈ H, ∀ (g : G), g * n * g⁻¹ ∈ H
· 使用定理 `Subgroup.Normal.mem_comm_iff`：mem_comm_iff (nH : H.Normal) {a b : G} : a
 * b in H ↔ b * a in H
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
-/
theorem normalizer_eq_top_iff : normalizer (H : Set G) = ⊤ ↔ H.Normal :=
  eq_top_iff.trans
    ⟨fun h => ⟨fun a ha b => (h (mem_top b) a).mp ha⟩, fun h a _ha b =>
      ⟨fun hb => h.conj_mem b hb a, fun hb => inv_mul_cancel_left a b ▸ h.mem_comm_iff.mp hb⟩⟩

variable (H) in
@[to_additive]
/-
**Subgroup.normalizer_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：normalizer_eq_top [h : H.Normal] : normalizer (H : Set G) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.normalizer_eq_top_iff`：normalizer_eq_top_iff : normalizer (H : 
Set G) = ⊤ ↔ H.Normal
-/
theorem normalizer_eq_top [h : H.Normal] : normalizer (H : Set G) = ⊤ :=
  normalizer_eq_top_iff.mpr h

@[to_additive]
/-
**Subgroup.normal_iff_map_conj_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：normal_iff_map_conj_eq : H.Normal ↔ forall g : G, H.map (MulAut.conj g) = 
H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem normal_iff_map_conj_eq : H.Normal ↔ ∀ g : G, H.map (MulAut.conj g) = H := by
  simp_rw [← normalizer_eq_top_iff, Subgroup.eq_top_iff', mem_normalizer_iff_map_conj_eq]

variable (H) in
@[to_additive]
/-
**Subgroup.Normal.map_conj_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.Normal`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) [H.Normal] (g : G), Sub
group.map (↑(MulAut.conj g)) H = H
参数：H : Subgroup G；g : G；↑(MulAut.conj g)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `Subgroup.normal_iff_map_conj_eq`：normal_iff_map_conj_eq : H.Normal ↔ for
all g : G, H.map (MulAut.conj g) = H
-/
theorem Normal.map_conj_eq [H.Normal] (g : G) : H.map (MulAut.conj g) = H :=
  normal_iff_map_conj_eq.mp ‹_› g

@[to_additive]
/-
**Subgroup.le_set_normalizer_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：le_set_normalizer_iff {s : Set G} : H <= normalizer s ↔ forall h in H, for
all g in s, h * g * h⁻¹ in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
theorem le_set_normalizer_iff {s : Set G} :
    H ≤ normalizer s ↔ ∀ h ∈ H, ∀ g ∈ s, h * g * h⁻¹ ∈ s := by
  refine ⟨fun hH h hh g hg ↦ hH hh g |>.mp hg, fun hH h hh k ↦ ⟨fun hk ↦ hH h hh k hk, fun hk ↦ ?_⟩⟩
  simpa [mul_assoc] using hH h⁻¹ (inv_mem hh) _ hk

@[to_additive]
/-
**Subgroup.le_normalizer_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：le_normalizer_iff : H <= normalizer K ↔ forall h in H, forall k in K, h * 
k * h⁻¹ in K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
theorem le_normalizer_iff : H ≤ normalizer K ↔ ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K := by
  refine ⟨fun hH h hh g hg ↦ hH hh g |>.mp hg, fun hH h hh k ↦ ⟨fun hk ↦ hH h hh k hk, fun hk ↦ ?_⟩⟩
  simpa [mul_assoc] using hH h⁻¹ (inv_mem hh) _ hk

@[to_additive]
/-
**Subgroup.le_normalizer_closure_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：le_normalizer_closure_iff {s : Set G} : H <= normalizer (closure s) ↔ fora
ll h in H, forall g in s, h * g * h⁻¹ in closure s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.mem_closure_of_mem`：mem_closure_of_mem {s : Set G} {x : G} (hx 
: x in s) : x in closure s
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.mem_normalizer_iff_map_conj_eq`：mem_normalizer_iff_map_conj_eq 
{H : Subgroup G} {g : G} : g in normalizer H ↔ H.map (MulAut.conj g) = H
· 使用定理 `MonoidHom.map_closure`：map_closure (f : G ->* N) (s : Set G) : (closure 
s).map f = closure (f '' s)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subgroup.closure_le`：closure_le : closure k <= K ↔ k subseteq K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem le_normalizer_closure_iff {s : Set G} :
    H ≤ normalizer (closure s) ↔ ∀ h ∈ H, ∀ g ∈ s, h * g * h⁻¹ ∈ closure s := by
  refine ⟨fun hH h hh g hg ↦ hH hh g |>.mp <| mem_closure_of_mem hg, fun hH h hh ↦ ?_⟩
  rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_closure]
  apply le_antisymm <| by simpa using! hH h hh
  rw [closure_le, ← MonoidHom.map_closure]
  exact fun g hg ↦ ⟨_, hH _ (inv_mem hh) g hg, by simp [mul_assoc]⟩

variable {N : Type*} [Group N]

/-- The preimage of the normalizer is contained in the normalizer of the preimage. -/
@[to_additive /-- The preimage of the normalizer is contained in the normalizer of the preimage. -/]
/-
**Subgroup.le_normalizer_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：le_normalizer_comap (f : N ->* G) : (normalizer H).comap f <= normalizer (
H.comap f)
参数：f : N ->* G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The preimage of the normalizer is contained in the normalizer of the preimage.
-/
theorem le_normalizer_comap (f : N →* G) :
    (normalizer H).comap f ≤ normalizer (H.comap f) := fun x => by
  simp only [mem_normalizer_iff, mem_comap]
  intro h n
  simp [h (f n)]

/-- The image of the normalizer is contained in the normalizer of the image. -/
@[to_additive /-- The image of the normalizer is contained in the normalizer of the image. -/]
/-
**Subgroup.le_normalizer_map** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：le_normalizer_map (f : G ->* N) : (normalizer H).map f <= normalizer (H.ma
p f)
参数：f : G ->* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.mem_map`：mem_map {f : G ->* N} {K : Subgroup G} {y : N} : y in 
K.map f ↔ exists x in K, f x = y
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Subgroup.mem_normalizer_iff_map_conj_eq`：mem_normalizer_iff_map_conj_eq 
{H : Subgroup G} {g : G} : g in normalizer H ↔ H.map (MulAut.conj g) = H
· 使用定理 `Subgroup.map_map`：map_map (g : N ->* P) (f : G ->* N) : (K.map f).map g 
= K.map (g.comp f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The image of the normalizer is contained in the normalizer of the image.
-/
theorem le_normalizer_map (f : G →* N) : (normalizer H).map f ≤ normalizer (H.map f) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  have : .comp (MulAut.conj (f y)) f = f.comp (MulAut.conj y) := by ext; simp -- todo: extract lemma
  rw [mem_normalizer_iff_map_conj_eq] at hy ⊢
  rw [map_map, this, ← map_map, hy]

@[to_additive]
/-
**Subgroup.comap_normalizer_eq_of_le_range** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：comap_normalizer_eq_of_le_range {f : N ->* G} (h : H <= f.range) : (normal
izer H).comap f = normalizer (H.comap f)
参数：h : H <= f.range。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Subgroup.le_normalizer_comap`：le_normalizer_comap (f : N ->* G) : (norma
lizer H).comap f <= normalizer (H.comap f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.map_le_iff_le_comap`：map_le_iff_le_comap {f : G ->* N} {K : Sub
group G} {H : Subgroup N} : K.map f <= H ↔ K <= H.comap f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Subgroup.le_normalizer_map`：le_normalizer_map (f : G ->* N) : (normalize
r H).map f <= normalizer (H.map f)
· 使用定理 `Subgroup.map_comap_eq_self`：map_comap_eq_self {f : G ->* N} {H : Subgrou
p N} (h : H <= f.range) : map f (comap f H) = H
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem comap_normalizer_eq_of_le_range {f : N →* G} (h : H ≤ f.range) :
    (normalizer H).comap f = normalizer (H.comap f) := by
  apply le_antisymm (le_normalizer_comap f)
  rw [← map_le_iff_le_comap]
  apply (le_normalizer_map f).trans
  rw [map_comap_eq_self h]

@[to_additive]
/-
**Subgroup.subgroupOf_normalizer_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：subgroupOf_normalizer_eq {H N : Subgroup G} (h : H <= N) : (normalizer H).
subgroupOf N = normalizer (H.subgroupOf N)
参数：h : H <= N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.comap_normalizer_eq_of_le_range`：comap_normalizer_eq_of_le_rang
e {f : N ->* G} (h : H <= f.range) : (normalizer H).comap f = normalizer (H.coma
p f)
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.range_subtype`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup 
G), H.subtype.range = H
-/
theorem subgroupOf_normalizer_eq {H N : Subgroup G} (h : H ≤ N) :
    (normalizer H).subgroupOf N = normalizer (H.subgroupOf N) :=
  comap_normalizer_eq_of_le_range (h.trans_eq N.range_subtype.symm)

@[to_additive]
/-
**Subgroup.normal_subgroupOf_iff_le_normalizer** 是 Mathlib 中的一个定理，位于命名空间 `Subgro
up`。
形式化陈述：normal_subgroupOf_iff_le_normalizer (h : H <= K) : (H.subgroupOf K).Normal
 ↔ K <= normalizer H
参数：h : H <= K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.subgroupOf_eq_top`：subgroupOf_eq_top {H K : Subgroup G} : H.sub
groupOf K = ⊤ ↔ K <= H
· 使用定理 `Subgroup.subgroupOf_normalizer_eq`：subgroupOf_normalizer_eq {H N : Subgr
oup G} (h : H <= N) : (normalizer H).subgroupOf N = normalizer (H.subgroupOf N)
· 使用定理 `Subgroup.normalizer_eq_top_iff`：normalizer_eq_top_iff : normalizer (H : 
Set G) = ⊤ ↔ H.Normal
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem normal_subgroupOf_iff_le_normalizer (h : H ≤ K) :
    (H.subgroupOf K).Normal ↔ K ≤ normalizer H := by
  rw [← subgroupOf_eq_top, subgroupOf_normalizer_eq h, normalizer_eq_top_iff]

@[to_additive]
/-
**Subgroup.normal_subgroupOf_iff_le_normalizer_inf** 是 Mathlib 中的一个定理，位于命名空间 `Su
bgroup`。
形式化陈述：normal_subgroupOf_iff_le_normalizer_inf : (H.subgroupOf K).Normal ↔ K <= n
ormalizer (H ⊓ K : Subgroup G)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.normal_subgroupOf_iff_le_normalizer`：normal_subgroupOf_iff_le_n
ormalizer (h : H <= K) : (H.subgroupOf K).Normal ↔ K <= normalizer H
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `Subgroup.inf_subgroupOf_right`：inf_subgroupOf_right (H K : Subgroup G) :
 (H ⊓ K).subgroupOf K = H.subgroupOf K
-/
theorem normal_subgroupOf_iff_le_normalizer_inf :
    (H.subgroupOf K).Normal ↔ K ≤ normalizer (H ⊓ K : Subgroup G) :=
  inf_subgroupOf_right H K ▸ normal_subgroupOf_iff_le_normalizer inf_le_right

@[to_additive]
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) normal_in_normalizer : (H.subgroupOf <| normalizer H).Normal :=
  (normal_subgroupOf_iff_le_normalizer H.le_normalizer).mpr le_rfl

@[to_additive]
/-
**Subgroup.maximal_normal_subgroupOf_normalizer** 是 Mathlib 中的一个定理，位于命名空间 `Subgr
oup`。
形式化陈述：maximal_normal_subgroupOf_normalizer : Maximal (H.subgroupOf · |>.Normal) 
(normalizer H)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.normal_in_normalizer`：∀ {G : Type u_1} [inst : Group G] {H : Su
bgroup G}, (H.subgroupOf (Subgroup.normalizer ↑H)).Normal
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.normal_subgroupOf_iff_le_normalizer`：normal_subgroupOf_iff_le_n
ormalizer (h : H <= K) : (H.subgroupOf K).Normal ↔ K <= normalizer H
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Subgroup.le_normalizer`：le_normalizer : H <= normalizer H
-/
theorem maximal_normal_subgroupOf_normalizer : Maximal (H.subgroupOf · |>.Normal) (normalizer H) :=
  ⟨inferInstance,
    fun _ hnormal hle ↦ (normal_subgroupOf_iff_le_normalizer <| le_normalizer.trans hle).mp hnormal⟩

@[to_additive]
/-
**Subgroup.le_normalizer_of_normal_subgroupOf** 是 Mathlib 中的一个定理，位于命名空间 `Subgrou
p`。
形式化陈述：le_normalizer_of_normal_subgroupOf [hK : (H.subgroupOf K).Normal] (HK : H 
<= K) : K <= normalizer H
参数：H.subgroupOf K；HK : H <= K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.normal_subgroupOf_iff_le_normalizer`：normal_subgroupOf_iff_le_n
ormalizer (h : H <= K) : (H.subgroupOf K).Normal ↔ K <= normalizer H
-/
theorem le_normalizer_of_normal_subgroupOf [hK : (H.subgroupOf K).Normal] (HK : H ≤ K) :
    K ≤ normalizer H :=
  (normal_subgroupOf_iff_le_normalizer HK).mp hK

@[to_additive]
/-
**Subgroup.subset_normalizer_of_normal** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：subset_normalizer_of_normal {S : Set G} [hH : H.Normal] : S subseteq norma
lizer (H : Set G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.normalizer_eq_top`：normalizer_eq_top [h : H.Normal] : normalize
r (H : Set G) = ⊤
-/
theorem subset_normalizer_of_normal {S : Set G} [hH : H.Normal] : S ⊆ normalizer (H : Set G) :=
  (@normalizer_eq_top _ _ H hH) ▸ le_top

@[to_additive]
/-
**Subgroup.le_normalizer_of_normal** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：le_normalizer_of_normal [H.Normal] : K <= normalizer H
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.subset_normalizer_of_normal`：subset_normalizer_of_normal {S : S
et G} [hH : H.Normal] : S subseteq normalizer (H : Set G)
-/
theorem le_normalizer_of_normal [H.Normal] : K ≤ normalizer H := subset_normalizer_of_normal

@[to_additive]
/-
**Subgroup.inf_normalizer_le_normalizer_inf** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`
。
形式化陈述：inf_normalizer_le_normalizer_inf : normalizer H ⊓ normalizer K <= normaliz
er ((H ⊓ K :) : Set G)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem inf_normalizer_le_normalizer_inf :
    normalizer H ⊓ normalizer K ≤ normalizer ((H ⊓ K :) : Set G) :=
  fun _ h g ↦ and_congr (h.1 g) (h.2 g)

@[to_additive]
/-
**Subgroup.iInf_normalizer_le_normalizer_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Subgrou
p`。
形式化陈述：iInf_normalizer_le_normalizer_iInf {ι : Sort*} (H : ι -> Subgroup G) : ⨅ i
, normalizer (H i) <= normalizer ((⨅ i, H i : Subgroup G) : Set G)
参数：H : ι -> Subgroup G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iInf_normalizer_le_normalizer_iInf {ι : Sort*} (H : ι → Subgroup G) :
    ⨅ i, normalizer (H i) ≤ normalizer ((⨅ i, H i : Subgroup G) : Set G) := by
  grind [le_normalizer_iff, mem_iInf, mem_normalizer_iff]

variable (G) in
/-- Every proper subgroup `H` of `G` is a proper normal subgroup of the normalizer of `H` in `G`. -/
/-
**Subgroup._root_.NormalizerCondition** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every proper subgroup `H` of `G` is a proper normal subgroup of the normalizer o
f `H` in `G`.
-/
def _root_.NormalizerCondition :=
  ∀ H : Subgroup G, H < ⊤ → H < normalizer H

/-- Alternative phrasing of the normalizer condition: Only the full group is self-normalizing.
This may be easier to work with, as it avoids inequalities and negations. -/
/-
**Subgroup._root_.normalizerCondition_iff_only_full_group_self_normalizing** 是 M
athlib 中的一个定理，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Alternative phrasing of the normalizer condition: Only the full group is self-no
rmalizing.
This may be easier to work with, as it avoids inequalities and negations.
-/
theorem _root_.normalizerCondition_iff_only_full_group_self_normalizing :
    NormalizerCondition G ↔ ∀ H : Subgroup G, normalizer H = H → H = ⊤ := by
  apply forall_congr'; intro H
  simp only [lt_iff_le_and_ne, le_normalizer, Ne]
  tauto

end Normalizer

end Subgroup

namespace Group

variable {s : Set G}

/-- Given a set `s`, `conjugatesOfSet s` is the set of all conjugates of
the elements of `s`. -/
@[to_additive /-- Given a set `s`, `addConjugatesOfSet s` is the set of all additive conjugates of
the elements of `s`. -/]
/-
**Group.conjugatesOfSet** 是 Mathlib 中的一个定义，位于命名空间 `Group`。
形式化陈述：conjugatesOfSet (s : Set G) : Set G
参数：s : Set G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def conjugatesOfSet (s : Set G) : Set G :=
  ⋃ a ∈ s, conjugatesOf a

@[to_additive]
/-
**Group.mem_conjugatesOfSet_iff** 是 Mathlib 中的一个定理，位于命名空间 `Group`。
形式化陈述：mem_conjugatesOfSet_iff {x : G} : x in conjugatesOfSet s ↔ exists a in s, 
IsConj a x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Group.conjugatesOfSet.eq_1`：∀ {G : Type u_1} [inst : Group G] (s : Set G
), Group.conjugatesOfSet s = ⋃ a ∈ s, conjugatesOf a
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_conjugatesOfSet_iff {x : G} : x ∈ conjugatesOfSet s ↔ ∃ a ∈ s, IsConj a x := by
  rw [conjugatesOfSet, Set.mem_iUnion₂]
  simp only [conjugatesOf, isConj_iff, Set.mem_ofPred_eq, exists_prop]

@[to_additive]
/-
**Group.subset_conjugatesOfSet** 是 Mathlib 中的一个定理，位于命名空间 `Group`。
形式化陈述：subset_conjugatesOfSet : s subseteq conjugatesOfSet s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Group.mem_conjugatesOfSet_iff`：mem_conjugatesOfSet_iff {x : G} : x in co
njugatesOfSet s ↔ exists a in s, IsConj a x
· 使用定理 `IsConj.refl`：IsConj.refl (a : α) : IsConj a a
-/
theorem subset_conjugatesOfSet : s ⊆ conjugatesOfSet s := fun (x : G) (h : x ∈ s) =>
  mem_conjugatesOfSet_iff.2 ⟨x, h, IsConj.refl _⟩

@[to_additive]
/-
**Group.conjugatesOfSet_mono** 是 Mathlib 中的一个定理，位于命名空间 `Group`。
形式化陈述：conjugatesOfSet_mono {s t : Set G} (h : s subseteq t) : conjugatesOfSet s 
subseteq conjugatesOfSet t
参数：h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.biUnion_subset_biUnion_left`：biUnion_subset_biUnion_left {s s' : Set
 α} {t : α -> Set β} (h : s subseteq s') : ⋃ x in s, t x subseteq ⋃ x in s', t x
-/
theorem conjugatesOfSet_mono {s t : Set G} (h : s ⊆ t) : conjugatesOfSet s ⊆ conjugatesOfSet t :=
  Set.biUnion_subset_biUnion_left h

@[to_additive]
/-
**Group.conjugates_subset_normal** 是 Mathlib 中的一个定理，位于命名空间 `Group`。
形式化陈述：conjugates_subset_normal {N : Subgroup G} [tn : N.Normal] {a : G} (h : a i
n N) : conjugatesOf a subseteq N
参数：h : a in N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isConj_iff`：isConj_iff {a b : α} : IsConj a b ↔ exists c : α, c * a * c⁻
¹ = b
· 使用定理 `Subgroup.Normal.conj_mem`：∀ {G : Type u_1} [inst : Group G] {H : Subgrou
p G}, H.Normal → ∀ n ∈ H, ∀ (g : G), g * n * g⁻¹ ∈ H
-/
theorem conjugates_subset_normal {N : Subgroup G} [tn : N.Normal] {a : G} (h : a ∈ N) :
    conjugatesOf a ⊆ N := by
  rintro a hc
  obtain ⟨c, rfl⟩ := isConj_iff.1 hc
  exact tn.conj_mem a h c

@[to_additive]
/-
**Group.conjugatesOfSet_subset** 是 Mathlib 中的一个定理，位于命名空间 `Group`。
形式化陈述：conjugatesOfSet_subset {s : Set G} {N : Subgroup G} [N.Normal] (h : s subs
eteq N) : conjugatesOfSet s subseteq N
参数：h : s subseteq N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iUnion₂_subset`：iUnion₂_subset {s : forall i, κ i -> Set α} {t : Set
 α} (h : forall i j, s i j subseteq t) : ⋃ (i) (j), s i j subseteq t
· 使用定理 `Group.conjugates_subset_normal`：conjugates_subset_normal {N : Subgroup G
} [tn : N.Normal] {a : G} (h : a in N) : conjugatesOf a subseteq N
-/
theorem conjugatesOfSet_subset {s : Set G} {N : Subgroup G} [N.Normal] (h : s ⊆ N) :
    conjugatesOfSet s ⊆ N :=
  Set.iUnion₂_subset fun _x H => conjugates_subset_normal (h H)

/-- The set of conjugates of `s` is closed under conjugation. -/
@[to_additive /-- The set of additive conjugates of `s` is closed under additive conjugation. -/]
/-
**Group.conj_mem_conjugatesOfSet** 是 Mathlib 中的一个定理，位于命名空间 `Group`。
形式化陈述：conj_mem_conjugatesOfSet {x c : G} : x in conjugatesOfSet s -> c * x * c⁻¹
 in conjugatesOfSet s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Group.mem_conjugatesOfSet_iff`：mem_conjugatesOfSet_iff {x : G} : x in co
njugatesOfSet s ↔ exists a in s, IsConj a x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsConj.trans`：∀ {α : Type u} [inst : Monoid α] {a b c : α}, IsConj a b →
 IsConj b c → IsConj a c
· 使用定理 `isConj_iff`：isConj_iff {a b : α} : IsConj a b ↔ exists c : α, c * a * c⁻
¹ = b

--- 原说明 ---
The set of conjugates of `s` is closed under conjugation.
-/
theorem conj_mem_conjugatesOfSet {x c : G} :
    x ∈ conjugatesOfSet s → c * x * c⁻¹ ∈ conjugatesOfSet s := fun H => by
  rcases mem_conjugatesOfSet_iff.1 H with ⟨a, h₁, h₂⟩
  exact mem_conjugatesOfSet_iff.2 ⟨a, h₁, h₂.trans (isConj_iff.2 ⟨c, rfl⟩)⟩

/-- The set of conjugates of the union of two sets is the union of the conjugates -/
@[to_additive /-- The set of additive conjugates of the union of two sets is the union
of the additive conjugates. -/]
/-
**Group.conjugatesOfSet_union** 是 Mathlib 中的一个定理，位于命名空间 `Group`。
形式化陈述：conjugatesOfSet_union {G : Type*} [Group G] (s t : Set G) : conjugatesOfSe
t (s union t) = conjugatesOfSet s union conjugatesOfSet t
参数：s t : Set G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biUnion_union`：biUnion_union (s t : Set α) (u : α -> Set β) : ⋃ x in
 s union t, u x = (⋃ x in s, u x) union ⋃ x in t, u x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem conjugatesOfSet_union {G : Type*} [Group G] (s t : Set G) :
    conjugatesOfSet (s ∪ t) = conjugatesOfSet s ∪ conjugatesOfSet t := by
  simp_rw [conjugatesOfSet, Set.biUnion_union]

end Group

namespace Subgroup

open Group

variable {s : Set G}

/-- The normal closure of a set `s` is the subgroup closure of all the conjugates of
elements of `s`. It is the smallest normal subgroup containing `s`. -/
@[to_additive /-- The normal closure of a set `s` is the closure of all the additive conjugates of
elements of `s`. It is the smallest normal additive subgroup containing `s`. -/]
/-
**Subgroup.normalClosure** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：normalClosure (s : Set G) : Subgroup G
参数：s : Set G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def normalClosure (s : Set G) : Subgroup G :=
  closure (conjugatesOfSet s)

@[to_additive]
/-
**Subgroup.conjugatesOfSet_subset_normalClosure** 是 Mathlib 中的一个定理，位于命名空间 `Subgr
oup`。
形式化陈述：conjugatesOfSet_subset_normalClosure : conjugatesOfSet s subseteq normalCl
osure s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.subset_closure`：subset_closure : k subseteq closure k
-/
theorem conjugatesOfSet_subset_normalClosure : conjugatesOfSet s ⊆ normalClosure s :=
  subset_closure

@[to_additive]
/-
**Subgroup.subset_normalClosure** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：subset_normalClosure : s subseteq normalClosure s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Group.subset_conjugatesOfSet`：subset_conjugatesOfSet : s subseteq conjug
atesOfSet s
· 使用定理 `Subgroup.conjugatesOfSet_subset_normalClosure`：conjugatesOfSet_subset_no
rmalClosure : conjugatesOfSet s subseteq normalClosure s
-/
theorem subset_normalClosure : s ⊆ normalClosure s :=
  Set.Subset.trans subset_conjugatesOfSet conjugatesOfSet_subset_normalClosure

@[to_additive]
/-
**Subgroup.le_normalClosure** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：le_normalClosure {H : Subgroup G} : H <= normalClosure ↑H
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.subset_normalClosure`：subset_normalClosure : s subseteq normalC
losure s
-/
theorem le_normalClosure {H : Subgroup G} : H ≤ normalClosure ↑H := fun _ h =>
  subset_normalClosure h

/-- The normal closure of `s` is a normal subgroup. -/
@[to_additive /-- The normal closure of `s` is a normal additive subgroup. -/]
/-
**Subgroup.normalClosure_normal** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：normalClosure_normal : (normalClosure s).Normal
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.closure_induction`：closure_induction {p : (g : G) -> g in closu
re k -> Prop} (mem : forall x (hx : x in k), p x (subset_closure hx)) (one : p 1
 (one_mem _)) (m…
· 使用定理 `Subgroup.conjugatesOfSet_subset_normalClosure`：conjugatesOfSet_subset_no
rmalClosure : conjugatesOfSet s subseteq normalClosure s
· 使用定理 `Group.conj_mem_conjugatesOfSet`：conj_mem_conjugatesOfSet {x c : G} : x i
n conjugatesOfSet s -> c * x * c⁻¹ in conjugatesOfSet s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `conj_mul`：conj_mul {a b c : α} : b * a * b⁻¹ * (b * c * b⁻¹) = b * (a * 
c) * b⁻¹
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `conj_inv`：conj_inv {a b : α} : (b * a * b⁻¹)⁻¹ = b * a⁻¹ * b⁻¹
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G

--- 原说明 ---
The normal closure of `s` is a normal subgroup.
-/
instance normalClosure_normal : (normalClosure s).Normal :=
  ⟨fun n h g => by
    refine Subgroup.closure_induction (fun x hx => ?_) ?_ (fun x y _ _ ihx ihy => ?_)
      (fun x _ ihx => ?_) h
    · exact conjugatesOfSet_subset_normalClosure (conj_mem_conjugatesOfSet hx)
    · simp
    · rw [← conj_mul]
      exact mul_mem ihx ihy
    · rw [← conj_inv]
      exact inv_mem ihx⟩

/-- The normal closure of `s` is the smallest normal subgroup containing `s`. -/
@[to_additive /-- The normal closure of `s` is the smallest normal additive subgroup containing`s`.
-/]
/-
**Subgroup.normalClosure_le_normal** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：normalClosure_le_normal {N : Subgroup G} [N.Normal] (h : s subseteq N) : n
ormalClosure s <= N
参数：h : s subseteq N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.closure_induction`：closure_induction {p : (g : G) -> g in closu
re k -> Prop} (mem : forall x (hx : x in k), p x (subset_closure hx)) (one : p 1
 (one_mem _)) (m…
· 使用定理 `Group.conjugatesOfSet_subset`：conjugatesOfSet_subset {s : Set G} {N : Su
bgroup G} [N.Normal] (h : s subseteq N) : conjugatesOfSet s subseteq N
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
-/
theorem normalClosure_le_normal {N : Subgroup G} [N.Normal] (h : s ⊆ N) : normalClosure s ≤ N := by
  intro a w
  refine closure_induction (fun x hx => ?_) ?_ (fun x y _ _ ihx ihy => ?_) (fun x _ ihx => ?_) w
  · exact conjugatesOfSet_subset h hx
  · exact one_mem _
  · exact mul_mem ihx ihy
  · exact inv_mem ihx

@[to_additive]
/-
**Subgroup.normalClosure_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：normalClosure_subset_iff {N : Subgroup G} [N.Normal] : s subseteq N ↔ norm
alClosure s <= N
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.normalClosure_le_normal`：normalClosure_le_normal {N : Subgroup 
G} [N.Normal] (h : s subseteq N) : normalClosure s <= N
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Subgroup.subset_normalClosure`：subset_normalClosure : s subseteq normalC
losure s
-/
theorem normalClosure_subset_iff {N : Subgroup G} [N.Normal] : s ⊆ N ↔ normalClosure s ≤ N :=
  ⟨normalClosure_le_normal, Set.Subset.trans subset_normalClosure⟩

@[simp]
/-
**Subgroup.normalClosure_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：normalClosure_eq_bot_iff : normalClosure s = ⊥ ↔ s subseteq {1}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.normalClosure_subset_iff`：normalClosure_subset_iff {N : Subgrou
p G} [N.Normal] : s subseteq N ↔ normalClosure s <= N
· 使用定理 `Subgroup.coe_bot`：coe_bot : ((⊥ : Subgroup G) : Set G) = {1}
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem normalClosure_eq_bot_iff : normalClosure s = ⊥ ↔ s ⊆ {1} := by
  rw [eq_bot_iff, ← normalClosure_subset_iff, coe_bot]

@[to_additive (attr := gcongr)]
/-
**Subgroup.normalClosure_mono** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：normalClosure_mono {s t : Set G} (h : s subseteq t) : normalClosure s <= n
ormalClosure t
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.normalClosure_le_normal`：normalClosure_le_normal {N : Subgroup 
G} [N.Normal] (h : s subseteq N) : normalClosure s <= N
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Subgroup.subset_normalClosure`：subset_normalClosure : s subseteq normalC
losure s
-/
theorem normalClosure_mono {s t : Set G} (h : s ⊆ t) : normalClosure s ≤ normalClosure t :=
  normalClosure_le_normal (Set.Subset.trans h subset_normalClosure)

@[to_additive]
/-
**Subgroup.normalClosure_eq_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：normalClosure_eq_iInf : normalClosure s = ⨅ (N : Subgroup G) (_ : Normal N
) (_ : s subseteq N), N
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `Subgroup.normalClosure_le_normal`：normalClosure_le_normal {N : Subgroup 
G} [N.Normal] (h : s subseteq N) : normalClosure s <= N
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用定理 `Subgroup.subset_normalClosure`：subset_normalClosure : s subseteq normalC
losure s
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem normalClosure_eq_iInf :
    normalClosure s = ⨅ (N : Subgroup G) (_ : Normal N) (_ : s ⊆ N), N :=
  le_antisymm (le_iInf fun _ => le_iInf fun _ => le_iInf normalClosure_le_normal)
    (iInf_le_of_le (normalClosure s)
      (iInf_le_of_le (by infer_instance) (iInf_le_of_le subset_normalClosure le_rfl)))

@[to_additive (attr := simp)]
/-
**Subgroup.normalClosure_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：normalClosure_eq_self (H : Subgroup G) [H.Normal] : normalClosure ↑H = H
参数：H : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Subgroup.normalClosure_le_normal`：normalClosure_le_normal {N : Subgroup 
G} [N.Normal] (h : s subseteq N) : normalClosure s <= N
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Subgroup.le_normalClosure`：le_normalClosure {H : Subgroup G} : H <= norm
alClosure ↑H
-/
theorem normalClosure_eq_self (H : Subgroup G) [H.Normal] : normalClosure ↑H = H :=
  le_antisymm (normalClosure_le_normal rfl.subset) le_normalClosure

@[to_additive]
/-
**Subgroup.normalClosure_idempotent** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：normalClosure_idempotent : normalClosure ↑(normalClosure s) = normalClosur
e s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.normalClosure_eq_self`：normalClosure_eq_self (H : Subgroup G) [
H.Normal] : normalClosure ↑H = H
-/
theorem normalClosure_idempotent : normalClosure ↑(normalClosure s) = normalClosure s :=
  normalClosure_eq_self _

@[to_additive]
/-
**Subgroup.closure_le_normalClosure** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：closure_le_normalClosure {s : Set G} : closure s <= normalClosure s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem closure_le_normalClosure {s : Set G} : closure s ≤ normalClosure s := by
  simp only [subset_normalClosure, closure_le]

@[to_additive (attr := simp)]
/-
**Subgroup.normalClosure_closure_eq_normalClosure** 是 Mathlib 中的一个定理，位于命名空间 `Sub
group`。
形式化陈述：normalClosure_closure_eq_normalClosure {s : Set G} : normalClosure ↑(closu
re s) = normalClosure s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Subgroup.normalClosure_le_normal`：normalClosure_le_normal {N : Subgroup 
G} [N.Normal] (h : s subseteq N) : normalClosure s <= N
· 使用定理 `Subgroup.closure_le_normalClosure`：closure_le_normalClosure {s : Set G} 
: closure s <= normalClosure s
· 使用定理 `Subgroup.normalClosure_mono`：normalClosure_mono {s t : Set G} (h : s sub
seteq t) : normalClosure s <= normalClosure t
· 使用定理 `Subgroup.subset_closure`：subset_closure : k subseteq closure k
-/
theorem normalClosure_closure_eq_normalClosure {s : Set G} :
    normalClosure ↑(closure s) = normalClosure s :=
  le_antisymm (normalClosure_le_normal closure_le_normalClosure) (normalClosure_mono subset_closure)

/-- The normal closure of an empty set is the trivial subgroup. -/
@[to_additive (attr := simp)]
/-
**Subgroup.normalClosure_empty** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：normalClosure_empty : normalClosure (∅ : Set G) = (⊥ : Subgroup G)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.normalClosure_closure_eq_normalClosure`：normalClosure_closure_e
q_normalClosure {s : Set G} : normalClosure ↑(closure s) = normalClosure s
· 使用定理 `Subgroup.closure_empty`：closure_empty : closure (∅ : Set G) = ⊥
· 使用定理 `Subgroup.normalClosure_eq_self`：normalClosure_eq_self (H : Subgroup G) [
H.Normal] : normalClosure ↑H = H

--- 原说明 ---
The normal closure of an empty set is the trivial subgroup.
-/
lemma normalClosure_empty : normalClosure (∅ : Set G) = (⊥ : Subgroup G) := by
  rw [← normalClosure_closure_eq_normalClosure, closure_empty, normalClosure_eq_self]

/-- The normal closure of the union of sets is the join of the normal closures of each set. -/
@[to_additive]
/-
**Subgroup.normalClosure_union** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：normalClosure_union {G : Type*} [Group G] (s t : Set G) : normalClosure (s
 union t) = normalClosure s ⊔ normalClosure t
参数：s t : Set G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Group.conjugatesOfSet_union`：conjugatesOfSet_union {G : Type*} [Group G]
 (s t : Set G) : conjugatesOfSet (s union t) = conjugatesOfSet s union conjugate
sOfSet t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subgroup.closure_union`：closure_union (s t : Set G) : closure (s union t
) = closure s ⊔ closure t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The normal closure of the union of sets is the join of the normal closures of ea
ch set.
-/
theorem normalClosure_union {G : Type*} [Group G] (s t : Set G) :
    normalClosure (s ∪ t) = normalClosure s ⊔ normalClosure t := by
  simp_rw [normalClosure, Group.conjugatesOfSet_union, closure_union]

/-- The normal core of a subgroup `H` is the largest normal subgroup of `G` contained in `H`,
as shown by `Subgroup.normalCore_eq_iSup`. -/
@[to_additive /-- The normal core of an additive subgroup `H` is the largest normal additive
subgroup of `G` contained in `H`, as shown by `AddSubgroup.normalCore_eq_iSup`. -/]
/-
**Subgroup.normalCore** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：normalCore (H : Subgroup G) : Subgroup G where carrier
参数：H : Subgroup G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def normalCore (H : Subgroup G) : Subgroup G where
  carrier := { a : G | ∀ b : G, b * a * b⁻¹ ∈ H }
  one_mem' a := by rw [mul_one, mul_inv_cancel]; exact H.one_mem
  inv_mem' {_} h b := (congr_arg (· ∈ H) conj_inv).mp (H.inv_mem (h b))
  mul_mem' {_ _} ha hb c := (congr_arg (· ∈ H) conj_mul).mp (H.mul_mem (ha c) (hb c))

@[to_additive]
/-
**Subgroup.normalCore_le** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：normalCore_le (H : Subgroup G) : H.normalCore <= H
参数：H : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem normalCore_le (H : Subgroup G) : H.normalCore ≤ H := fun a h => by
  rw [← mul_one a, ← inv_one, ← one_mul a]
  exact h 1

@[to_additive]
/-
**Subgroup.normalCore_normal** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：normalCore_normal (H : Subgroup G) : H.normalCore.Normal
参数：H : Subgroup G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
-/
instance normalCore_normal (H : Subgroup G) : H.normalCore.Normal :=
  ⟨fun a h b c => by
    rw [mul_assoc, mul_assoc, ← mul_inv_rev, ← mul_assoc, ← mul_assoc]; exact h (c * b)⟩

@[to_additive]
/-
**Subgroup.normal_le_normalCore** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：normal_le_normalCore {H : Subgroup G} {N : Subgroup G} [hN : N.Normal] : N
 <= H.normalCore ↔ N <= H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ge_trans`：ge_trans : b <= a -> c <= b -> c <= a
· 使用定理 `Subgroup.normalCore_le`：normalCore_le (H : Subgroup G) : H.normalCore <=
 H
· 使用定理 `Subgroup.Normal.conj_mem`：∀ {G : Type u_1} [inst : Group G] {H : Subgrou
p G}, H.Normal → ∀ n ∈ H, ∀ (g : G), g * n * g⁻¹ ∈ H
-/
theorem normal_le_normalCore {H : Subgroup G} {N : Subgroup G} [hN : N.Normal] :
    N ≤ H.normalCore ↔ N ≤ H :=
  ⟨ge_trans H.normalCore_le, fun h_le n hn g => h_le (hN.conj_mem n hn g)⟩

@[to_additive]
/-
**Subgroup.normalCore_mono** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：normalCore_mono {H K : Subgroup G} (h : H <= K) : H.normalCore <= K.normal
Core
参数：h : H <= K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.normal_le_normalCore`：normal_le_normalCore {H : Subgroup G} {N 
: Subgroup G} [hN : N.Normal] : N <= H.normalCore ↔ N <= H
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Subgroup.normalCore_le`：normalCore_le (H : Subgroup G) : H.normalCore <=
 H
-/
theorem normalCore_mono {H K : Subgroup G} (h : H ≤ K) : H.normalCore ≤ K.normalCore :=
  normal_le_normalCore.mpr (H.normalCore_le.trans h)

@[to_additive]
/-
**Subgroup.normalCore_eq_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：normalCore_eq_iSup (H : Subgroup G) : H.normalCore = ⨆ (N : Subgroup G) (_
 : Normal N) (_ : N <= H), N
参数：H : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `Subgroup.normalCore_le`：normalCore_le (H : Subgroup G) : H.normalCore <=
 H
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.normal_le_normalCore`：normal_le_normalCore {H : Subgroup G} {N 
: Subgroup G} [hN : N.Normal] : N <= H.normalCore ↔ N <= H
-/
theorem normalCore_eq_iSup (H : Subgroup G) :
    H.normalCore = ⨆ (N : Subgroup G) (_ : Normal N) (_ : N ≤ H), N :=
  le_antisymm
    (le_iSup_of_le H.normalCore
      (le_iSup_of_le H.normalCore_normal (le_iSup_of_le H.normalCore_le le_rfl)))
    (iSup_le fun _ => iSup_le fun _ => iSup_le normal_le_normalCore.mpr)

@[to_additive (attr := simp)]
/-
**Subgroup.normalCore_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：normalCore_eq_self (H : Subgroup G) [H.Normal] : H.normalCore = H
参数：H : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Subgroup.normalCore_le`：normalCore_le (H : Subgroup G) : H.normalCore <=
 H
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.normal_le_normalCore`：normal_le_normalCore {H : Subgroup G} {N 
: Subgroup G} [hN : N.Normal] : N <= H.normalCore ↔ N <= H
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem normalCore_eq_self (H : Subgroup G) [H.Normal] : H.normalCore = H :=
  le_antisymm H.normalCore_le (normal_le_normalCore.mpr le_rfl)

@[to_additive]
/-
**Subgroup.normalCore_idempotent** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：normalCore_idempotent (H : Subgroup G) : H.normalCore.normalCore = H.norma
lCore
参数：H : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.normalCore_eq_self`：normalCore_eq_self (H : Subgroup G) [H.Norm
al] : H.normalCore = H
-/
theorem normalCore_idempotent (H : Subgroup G) : H.normalCore.normalCore = H.normalCore :=
  H.normalCore.normalCore_eq_self

@[to_additive]
/-
**Subgroup.normalCore_eq_iInf_map_conj** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：normalCore_eq_iInf_map_conj (H : Subgroup G) : H.normalCore = ⨅ g : G, H.m
ap (MulAut.conj g)
参数：H : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.normal_iff_map_conj_eq`：normal_iff_map_conj_eq : H.Normal ↔ for
all g : G, H.map (MulAut.conj g) = H
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.iInf_comp`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} [inst :
 InfSet α] {g : ι' → α} (e : ι ≃ ι'), ⨅ x, g (e x) = ⨅ y, g y
· 使用定理 `Subgroup.map_iInf`：map_iInf {ι : Sort*} [Nonempty ι] (f : G ->* N) (hf :
 Function.Injective f) (s : ι -> Subgroup G) : (iInf s).map f = ⨅ i, (s i).map f
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `MulEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst
_1 : Mul N] (e : M ≃* N), Function.Injective ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subgroup.map_map`：map_map (g : N ->* P) (f : G ->* N) : (K.map f).map g 
= K.map (g.comp f)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonoidHomClass.toMonoidHom.congr_simp`：∀ {M : Type u_4} {N : Type u_5} {
F : Type u_9} [inst : MulOne M] [inst_1 : MulOne N] [inst_2 : FunLike F M N]   [
inst_3 : MonoidHomClass F M…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `Subgroup.Normal.map_conj_eq`：∀ {G : Type u_1} [inst : Group G] (H : Subg
roup G) [H.Normal] (g : G), Subgroup.map (↑(MulAut.conj g)) H = H
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Subgroup.map_mono`：map_mono {f : G ->* N} {K K' : Subgroup G} : K <= K' 
-> map f K <= map f K'
· 使用定理 `Subgroup.normalCore_le`：normalCore_le (H : Subgroup G) : H.normalCore <=
 H
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Subgroup.normal_le_normalCore`：normal_le_normalCore {H : Subgroup G} {N 
: Subgroup G} [hN : N.Normal] : N <= H.normalCore ↔ N <= H
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
（共 32 条，此处仅展示前 30 条）
-/
theorem normalCore_eq_iInf_map_conj (H : Subgroup G) :
    H.normalCore = ⨅ g : G, H.map (MulAut.conj g) := by
  have : (⨅ g : G, H.map (MulAut.conj g) : Subgroup G).Normal := by
    refine normal_iff_map_conj_eq.mpr fun g ↦ ?_
    conv_rhs => rw [← Equiv.iInf_comp (Equiv.mulLeft g)]
    rw [map_iInf _ (MulAut.conj g).injective]
    simp [map_map, MulAut.mul_def]
  refine le_antisymm (le_iInf fun g ↦ ?_) ?_
  · grw [← Normal.map_conj_eq H.normalCore g, normalCore_le]
  · rw [normal_le_normalCore]
    apply iInf_le_of_le 1
    simp [MulAut.one_def]

@[to_additive]
/-
**Subgroup.normalCore_eq_iInf_comap_conj** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：normalCore_eq_iInf_comap_conj (H : Subgroup G) : H.normalCore = ⨅ g : G, H
.comap (MulAut.conj g)
参数：H : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.iInf_comp`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} [inst :
 InfSet α] {g : ι' → α} (e : ι ≃ ι'), ⨅ x, g (e x) = ⨅ y, g y
· 使用定理 `Subgroup.normalCore_eq_iInf_map_conj`：normalCore_eq_iInf_map_conj (H : S
ubgroup G) : H.normalCore = ⨅ g : G, H.map (MulAut.conj g)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subgroup.map_equiv_eq_comap_symm`：map_equiv_eq_comap_symm (f : G ≃* N) (
K : Subgroup G) : K.map f = K.comap (G
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonoidHomClass.toMonoidHom.congr_simp`：∀ {M : Type u_4} {N : Type u_5} {
F : Type u_9} [inst : MulOne M] [inst_1 : MulOne N] [inst_2 : FunLike F M N]   [
inst_3 : MonoidHomClass F M…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.inv_apply`：∀ (G : Type u_14) [inst : InvolutiveInv G], ⇑(Equiv.inv
 G) = Inv.inv
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem normalCore_eq_iInf_comap_conj (H : Subgroup G) :
    H.normalCore = ⨅ g : G, H.comap (MulAut.conj g) := by
  rw [← (Equiv.inv G).iInf_comp, normalCore_eq_iInf_map_conj]
  simp [MulAut.inv_def, map_equiv_eq_comap_symm]

end Subgroup

namespace MonoidHom

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

open Subgroup

section Ker

variable {M : Type*} [MulOneClass M]

@[to_additive prodMap_comap_prod]
/-
**MonoidHom.prodMap_comap_prod** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：prodMap_comap_prod {G' : Type*} {N' : Type*} [Group G'] [Group N'] (f : G 
->* N) (g : G' ->* N') (S : Subgroup N) (S' : Subgroup N') : (S.prod S').comap (
prodMap f g) = (S.comap f).prod (S'.comap g)
参数：f : G ->* N；g : G' ->* N'；S : Subgroup N；S' : Subgroup N'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.preimage_prod_map_prod`：preimage_prod_map_prod (f : α -> β) (g : γ -
> δ) (s : Set β) (t : Set δ) : Prod.map f g ⁻¹' s ×ˢ t = (f ⁻¹' s) ×ˢ (g ⁻¹' t)
-/
theorem prodMap_comap_prod {G' : Type*} {N' : Type*} [Group G'] [Group N'] (f : G →* N)
    (g : G' →* N') (S : Subgroup N) (S' : Subgroup N') :
    (S.prod S').comap (prodMap f g) = (S.comap f).prod (S'.comap g) :=
  SetLike.coe_injective <| Set.preimage_prod_map_prod f g _ _

@[to_additive ker_prodMap]
/-
**MonoidHom.ker_prodMap** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：ker_prodMap {G' : Type*} {N' : Type*} [Group G'] [Group N'] (f : G ->* N) 
(g : G' ->* N') : (prodMap f g).ker = f.ker.prod g.ker
参数：f : G ->* N；g : G' ->* N'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.comap_bot`：comap_bot (f : G ->* N) : (⊥ : Subgroup N).comap f 
= f.ker
· 使用定理 `MonoidHom.prodMap_comap_prod`：prodMap_comap_prod {G' : Type*} {N' : Type
*} [Group G'] [Group N'] (f : G ->* N) (g : G' ->* N') (S : Subgroup N) (S' : Su
bgroup N') : (S.pr…
· 使用定理 `Subgroup.bot_prod_bot`：bot_prod_bot : (⊥ : Subgroup G).prod (⊥ : Subgrou
p N) = ⊥
-/
theorem ker_prodMap {G' : Type*} {N' : Type*} [Group G'] [Group N'] (f : G →* N) (g : G' →* N') :
    (prodMap f g).ker = f.ker.prod g.ker := by
  rw [← comap_bot, ← comap_bot, ← comap_bot, ← prodMap_comap_prod, bot_prod_bot]

@[to_additive (attr := simp)]
/-
**MonoidHom.ker_fst** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：ker_fst : ker (fst G G') = .prod ⊥ ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma ker_fst : ker (fst G G') = .prod ⊥ ⊤ := SetLike.ext fun _ => (iff_of_eq (and_true _)).symm

@[to_additive (attr := simp)]
/-
**MonoidHom.ker_snd** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：ker_snd : ker (snd G G') = .prod ⊤ ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
lemma ker_snd : ker (snd G G') = .prod ⊤ ⊥ := SetLike.ext fun _ => (iff_of_eq (true_and _)).symm

end Ker

@[to_additive (attr := simp) range_prodMap]
/-
**MonoidHom.range_prodMap** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：range_prodMap {G' N' : Type*} [Group G'] [Group N'] (f : G ->* N) (g : G' 
->* N') : (f.prodMap g).range = f.range.prod g.range
参数：f : G ->* N；g : G' ->* N'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.range_prodMap`：range_prodMap {m₁ : α -> γ} {m₂ : β -> δ} : range (Pr
od.map m₁ m₂) = range m₁ ×ˢ range m₂
-/
lemma range_prodMap {G' N' : Type*} [Group G'] [Group N'] (f : G →* N) (g : G' →* N') :
    (f.prodMap g).range = f.range.prod g.range :=
  SetLike.coe_injective Set.range_prodMap

end MonoidHom

namespace Subgroup

variable {N : Type*} [Group N] (H : Subgroup G)

@[to_additive]
/-
**Subgroup.Normal.map** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.Normal`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {N : Type u_5} [inst_1 : Group N] {H : S
ubgroup G},   H.Normal → ∀ (f : G →* N), Function.Surjective ⇑f → (Subgroup.map 
f H).Normal
参数：f : G →* N；Subgroup.map f H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.normalizer_eq_top_iff`：normalizer_eq_top_iff : normalizer (H : 
Set G) = ⊤ ↔ H.Normal
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `MonoidHom.range_eq_top_of_surjective`：range_eq_top_of_surjective {N} [Gr
oup N] (f : G ->* N) (hf : Function.Surjective f) : f.range = (⊤ : Subgroup N)
· 使用定理 `MonoidHom.range_eq_map`：range_eq_map (f : G ->* N) : f.range = (⊤ : Subg
roup G).map f
· 使用定理 `Subgroup.normalizer_eq_top`：normalizer_eq_top [h : H.Normal] : normalize
r (H : Set G) = ⊤
· 使用定理 `Subgroup.le_normalizer_map`：le_normalizer_map (f : G ->* N) : (normalize
r H).map f <= normalizer (H.map f)
-/
theorem Normal.map {H : Subgroup G} (h : H.Normal) (f : G →* N) (hf : Function.Surjective f) :
    (H.map f).Normal := by
  rw [← normalizer_eq_top_iff, ← top_le_iff, ← f.range_eq_top_of_surjective hf, f.range_eq_map,
    ← H.normalizer_eq_top]
  exact le_normalizer_map _

end Subgroup

namespace Subgroup

open MonoidHom

variable {N : Type*} [Group N] (f : G →* N)

/-- The preimage of the normalizer is equal to the normalizer of the preimage of a surjective
  function. -/
@[to_additive
      /-- The preimage of the normalizer is equal to the normalizer of the preimage of
      a surjective function. -/]
/-
**Subgroup.comap_normalizer_eq_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup
`。
形式化陈述：comap_normalizer_eq_of_surjective (H : Subgroup G) {f : N ->* G} (hf : Fun
ction.Surjective f) : (normalizer H).comap f = normalizer (H.comap f)
参数：H : Subgroup G；hf : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.comap_normalizer_eq_of_le_range`：comap_normalizer_eq_of_le_rang
e {f : N ->* G} (h : H <= f.range) : (normalizer H).comap f = normalizer (H.coma
p f)
-/
theorem comap_normalizer_eq_of_surjective (H : Subgroup G) {f : N →* G}
    (hf : Function.Surjective f) : (normalizer H).comap f = normalizer (H.comap f) :=
  comap_normalizer_eq_of_le_range fun x _ ↦ hf x

/-- The image of the normalizer is equal to the normalizer of the image of an isomorphism. -/
@[to_additive
      /-- The image of the normalizer is equal to the normalizer of the image of an
      isomorphism. -/]
/-
**Subgroup.map_equiv_normalizer_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_equiv_normalizer_eq (H : Subgroup G) (f : G ≃* N) : (normalizer H).map
 f.toMonoidHom = normalizer (H.map f.toMonoidHom)
参数：H : Subgroup G；f : G ≃* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Equiv.forall_congr`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} {q : β → 
Prop} (e : α ≃ β),   (∀ (a : α), p a ↔ q (e a)) → ((∀ (a : α), p a) ↔ ∀ (b : β),
 q b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MulEquiv.symm_apply_apply`：symm_apply_apply (e : M ≃* N) (x : M) : e.sym
m (e x) = x
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem map_equiv_normalizer_eq (H : Subgroup G) (f : G ≃* N) :
    (normalizer H).map f.toMonoidHom = normalizer (H.map f.toMonoidHom) := by
  ext x
  simp only [mem_normalizer_iff, mem_map_equiv]
  rw [f.toEquiv.forall_congr]
  intro
  simp

/-- The image of the normalizer is equal to the normalizer of the image of a bijective
  function. -/
@[to_additive
      /-- The image of the normalizer is equal to the normalizer of the image of a bijective
        function. -/]
/-
**Subgroup.map_normalizer_eq_of_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_normalizer_eq_of_bijective (H : Subgroup G) {f : G ->* N} (hf : Functi
on.Bijective f) : (normalizer H).map f = normalizer (H.map f)
参数：H : Subgroup G；hf : Function.Bijective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.map_equiv_normalizer_eq`：map_equiv_normalizer_eq (H : Subgroup 
G) (f : G ≃* N) : (normalizer H).map f.toMonoidHom = normalizer (H.map f.toMonoi
dHom)
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
theorem map_normalizer_eq_of_bijective (H : Subgroup G) {f : G →* N} (hf : Function.Bijective f) :
    (normalizer H).map f = normalizer (H.map f) :=
  map_equiv_normalizer_eq H (MulEquiv.ofBijective f hf)

end Subgroup

namespace MonoidHom

variable {G₁ G₂ G₃ : Type*} [Group G₁] [Group G₂] [Group G₃]
variable (f : G₁ →* G₂) (f_inv : G₂ → G₁)

/-- Auxiliary definition used to define `liftOfRightInverse` -/
@[to_additive /-- Auxiliary definition used to define `liftOfRightInverse` -/]
/-
**MonoidHom.liftOfRightInverseAux** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：liftOfRightInverseAux (hf : Function.RightInverse f_inv f) (g : G₁ ->* G₃)
 (hg : f.ker <= g.ker) : G₂ ->* G₃ where toFun b
参数：hf : Function.RightInverse f_inv f；g : G₁ ->* G₃；hg : f.ker <= g.ker。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition used to define `liftOfRightInverse`
-/
def liftOfRightInverseAux (hf : Function.RightInverse f_inv f) (g : G₁ →* G₃) (hg : f.ker ≤ g.ker) :
    G₂ →* G₃ where
  toFun b := g (f_inv b)
  map_one' := hg (hf 1)
  map_mul' := by
    intro x y
    rw [← g.map_mul, ← mul_inv_eq_one, ← g.map_inv, ← g.map_mul, ← g.mem_ker]
    apply hg
    rw [f.mem_ker, f.map_mul, f.map_inv, mul_inv_eq_one, f.map_mul]
    simp only [hf _]

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
/-
**MonoidHom.liftOfRightInverseAux_comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHo
m`。
形式化陈述：liftOfRightInverseAux_comp_apply (hf : Function.RightInverse f_inv f) (g :
 G₁ ->* G₃) (hg : f.ker <= g.ker) (x : G₁) : (f.liftOfRightInverseAux f_inv hf g
 hg) (f x) = g x
参数：hf : Function.RightInverse f_inv f；g : G₁ ->* G₃；hg : f.ker <= g.ker；x : G₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_inv_eq_one`：mul_inv_eq_one : a * b⁻¹ = 1 ↔ a = b
· 使用定理 `MonoidHom.map_inv`：∀ {α : Type u_2} {β : Type u_3} [inst : Group α] [ins
t_1 : DivisionMonoid β] (f : α →* β) (a : α), f a⁻¹ = (f a)⁻¹
· 使用定理 `MonoidHom.map_mul`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N) (a b : M), f (a * b) = f a * f b
· 使用定理 `MonoidHom.mem_ker`：mem_ker {f : G ->* M} {x : G} : x in f.ker ↔ f x = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem liftOfRightInverseAux_comp_apply (hf : Function.RightInverse f_inv f) (g : G₁ →* G₃)
    (hg : f.ker ≤ g.ker) (x : G₁) : (f.liftOfRightInverseAux f_inv hf g hg) (f x) = g x := by
  dsimp [liftOfRightInverseAux]
  rw [← mul_inv_eq_one, ← g.map_inv, ← g.map_mul, ← g.mem_ker]
  apply hg
  rw [f.mem_ker, f.map_mul, f.map_inv, mul_inv_eq_one]
  simp only [hf _]

/-- `liftOfRightInverse f hf g hg` is the unique group homomorphism `φ`

* such that `φ.comp f = g` (`MonoidHom.liftOfRightInverse_comp`),
* where `f : G₁ →+* G₂` has a RightInverse `f_inv` (`hf`),
* and `g : G₂ →+* G₃` satisfies `hg : f.ker ≤ g.ker`.

See `MonoidHom.eq_liftOfRightInverse` for the uniqueness lemma.

```
   G₁.
   |  \
 f |   \ g
   |    \
   v     \⌟
   G₂----> G₃
      ∃!φ
```
-/
@[to_additive
      /-- `liftOfRightInverse f f_inv hf g hg` is the unique additive group homomorphism `φ`
      * such that `φ.comp f = g` (`AddMonoidHom.liftOfRightInverse_comp`),
      * where `f : G₁ →+ G₂` has a RightInverse `f_inv` (`hf`),
      * and `g : G₂ →+ G₃` satisfies `hg : f.ker ≤ g.ker`.
      See `AddMonoidHom.eq_liftOfRightInverse` for the uniqueness lemma.
      ```
         G₁.
         |  \
       f |   \ g
         |    \
         v     \⌟
         G₂----> G₃
            ∃!φ
      ``` -/]
/-
**MonoidHom.liftOfRightInverse** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：liftOfRightInverse (hf : Function.RightInverse f_inv f) : { g : G₁ ->* G₃ 
// f.ker <= g.ker } ≃ (G₂ ->* G₃) where toFun g
参数：hf : Function.RightInverse f_inv f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def liftOfRightInverse (hf : Function.RightInverse f_inv f) :
    { g : G₁ →* G₃ // f.ker ≤ g.ker } ≃ (G₂ →* G₃) where
  toFun g := f.liftOfRightInverseAux f_inv hf g.1 g.2
  invFun φ := ⟨φ.comp f, fun x hx ↦ mem_ker.mpr <| by simp [mem_ker.mp hx]⟩
  left_inv g := by
    ext
    simp only [comp_apply, liftOfRightInverseAux_comp_apply]
  right_inv φ := by
    ext b
    simp [liftOfRightInverseAux, hf b]

/-- A non-computable version of `MonoidHom.liftOfRightInverse` for when no computable right
inverse is available, that uses `Function.surjInv`. -/
@[to_additive (attr := simp)
      /-- A non-computable version of `AddMonoidHom.liftOfRightInverse` for when no
      computable right inverse is available. -/]
/-
**MonoidHom.liftOfSurjective** 是 Mathlib 中的一个缩写定义，位于命名空间 `MonoidHom`。
形式化陈述：liftOfSurjective (hf : Function.Surjective f) : { g : G₁ ->* G₃ // f.ker <
= g.ker } ≃ (G₂ ->* G₃)
参数：hf : Function.Surjective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable abbrev liftOfSurjective (hf : Function.Surjective f) :
    { g : G₁ →* G₃ // f.ker ≤ g.ker } ≃ (G₂ →* G₃) :=
  f.liftOfRightInverse (Function.surjInv hf) (Function.rightInverse_surjInv hf)

@[to_additive (attr := simp)]
/-
**MonoidHom.liftOfRightInverse_comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：liftOfRightInverse_comp_apply (hf : Function.RightInverse f_inv f) (g : { 
g : G₁ ->* G₃ // f.ker <= g.ker }) (x : G₁) : (f.liftOfRightInverse f_inv hf g) 
(f x) = g.1 x
参数：hf : Function.RightInverse f_inv f；g : { g : G₁ ->* G₃ // f.ker <= g.ker }；x 
: G₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.liftOfRightInverseAux_comp_apply`：liftOfRightInverseAux_comp_a
pply (hf : Function.RightInverse f_inv f) (g : G₁ ->* G₃) (hg : f.ker <= g.ker) 
(x : G₁) : (f.liftOfRightInverse…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem liftOfRightInverse_comp_apply (hf : Function.RightInverse f_inv f)
    (g : { g : G₁ →* G₃ // f.ker ≤ g.ker }) (x : G₁) :
    (f.liftOfRightInverse f_inv hf g) (f x) = g.1 x :=
  f.liftOfRightInverseAux_comp_apply f_inv hf g.1 g.2 x

@[to_additive (attr := simp)]
/-
**MonoidHom.liftOfRightInverse_comp** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：liftOfRightInverse_comp (hf : Function.RightInverse f_inv f) (g : { g : G₁
 ->* G₃ // f.ker <= g.ker }) : (f.liftOfRightInverse f_inv hf g).comp f = g
参数：hf : Function.RightInverse f_inv f；g : { g : G₁ ->* G₃ // f.ker <= g.ker }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `MonoidHom.liftOfRightInverse_comp_apply`：liftOfRightInverse_comp_apply (
hf : Function.RightInverse f_inv f) (g : { g : G₁ ->* G₃ // f.ker <= g.ker }) (x
 : G₁) : (f.liftOfRightInvers…
-/
theorem liftOfRightInverse_comp (hf : Function.RightInverse f_inv f)
    (g : { g : G₁ →* G₃ // f.ker ≤ g.ker }) : (f.liftOfRightInverse f_inv hf g).comp f = g :=
  MonoidHom.ext <| f.liftOfRightInverse_comp_apply f_inv hf g

@[to_additive]
/-
**MonoidHom.eq_liftOfRightInverse** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：eq_liftOfRightInverse (hf : Function.RightInverse f_inv f) (g : G₁ ->* G₃)
 (hg : f.ker <= g.ker) (h : G₂ ->* G₃) (hh : h.comp f = g) : h = f.liftOfRightIn
verse f_inv hf ⟨g, hg⟩
参数：hf : Function.RightInverse f_inv f；g : G₁ ->* G₃；hg : f.ker <= g.ker；h : G₂ -
>* G₃；hh : h.comp f = g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
theorem eq_liftOfRightInverse (hf : Function.RightInverse f_inv f) (g : G₁ →* G₃)
    (hg : f.ker ≤ g.ker) (h : G₂ →* G₃) (hh : h.comp f = g) :
    h = f.liftOfRightInverse f_inv hf ⟨g, hg⟩ := by
  simp_rw [← hh]
  exact ((f.liftOfRightInverse f_inv hf).apply_symm_apply _).symm

end MonoidHom

variable {N : Type*} [Group N]

namespace Subgroup

-- Here `H.Normal` is an explicit argument so we can use dot notation with `comap`.
@[to_additive]
/-
**Subgroup.Normal.comap** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.Normal`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {N : Type u_5} [inst_1 : Group N] {H : S
ubgroup N},   H.Normal → ∀ (f : G →* N), (Subgroup.comap f H).Normal
参数：f : G →* N；Subgroup.comap f H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Subgroup.Normal.conj_mem`：∀ {G : Type u_1} [inst : Group G] {H : Subgrou
p G}, H.Normal → ∀ n ∈ H, ∀ (g : G), g * n * g⁻¹ ∈ H
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem Normal.comap {H : Subgroup N} (hH : H.Normal) (f : G →* N) : (H.comap f).Normal :=
  ⟨fun _ => by simp +contextual [Subgroup.mem_comap, hH.conj_mem]⟩

@[to_additive]
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) normal_comap {H : Subgroup N} [nH : H.Normal] (f : G →* N) :
    (H.comap f).Normal :=
  nH.comap _

-- Here `H.Normal` is an explicit argument so we can use dot notation with `subgroupOf`.
@[to_additive]
/-
**Subgroup.Normal.subgroupOf** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.Normal`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {H : Subgroup G}, H.Normal → ∀ (K : Subg
roup G), (H.subgroupOf K).Normal
参数：K : Subgroup G；H.subgroupOf K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.Normal.comap`：∀ {G : Type u_1} [inst : Group G] {N : Type u_5} 
[inst_1 : Group N] {H : Subgroup N},   H.Normal → ∀ (f : G →* N), (Subgroup.coma
p f H).Norm…
-/
theorem Normal.subgroupOf {H : Subgroup G} (hH : H.Normal) (K : Subgroup G) :
    (H.subgroupOf K).Normal :=
  hH.comap _

@[to_additive]
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) normal_subgroupOf {H N : Subgroup G} [N.Normal] :
    (N.subgroupOf H).Normal :=
  Subgroup.normal_comap _

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/-
**Subgroup.comap_normalClosure_image_ge** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：comap_normalClosure_image_ge (s : Set G) (f : G ->* N) : (normalClosure s)
 <= (normalClosure (f '' s)).comap f
参数：s : Set G；f : G ->* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Subgroup.normal_comap`：∀ {G : Type u_1} [inst : Group G] {N : Type u_5} 
[inst_1 : Group N] {H : Subgroup N} [nH : H.Normal] (f : G →* N),   (Subgroup.co
map f H).No…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem comap_normalClosure_image_ge (s : Set G) (f : G →* N) :
    (normalClosure s) ≤ (normalClosure (f '' s)).comap f := by
  simp [normalClosure_le_normal, ← Set.image_subset_iff, subset_normalClosure]

@[to_additive]
/-
**Subgroup.map_normalClosure_le** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_normalClosure_le (s : Set G) (f : G ->* N) : (normalClosure s).map f <
= normalClosure (f '' s)
参数：s : Set G；f : G ->* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem map_normalClosure_le (s : Set G) (f : G →* N) :
    (normalClosure s).map f ≤ normalClosure (f '' s) := by
  simp [map_le_iff_le_comap, comap_normalClosure_image_ge]

@[to_additive]
/-
**Subgroup.map_normalClosure** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_normalClosure (s : Set G) (f : G ->* N) (hf : Surjective f) : (normalC
losure s).map f = normalClosure (f '' s)
参数：s : Set G；f : G ->* N；hf : Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.Normal.map`：∀ {G : Type u_1} [inst : Group G] {N : Type u_5} [i
nst_1 : Group N] {H : Subgroup G},   H.Normal → ∀ (f : G →* N), Function.Surject
ive ⇑f → …
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Subgroup.map_normalClosure_le`：map_normalClosure_le (s : Set G) (f : G -
>* N) : (normalClosure s).map f <= normalClosure (f '' s)
· 使用定理 `Subgroup.normalClosure_le_normal`：normalClosure_le_normal {N : Subgroup 
G} [N.Normal] (h : s subseteq N) : normalClosure s <= N
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Subgroup.subset_normalClosure`：subset_normalClosure : s subseteq normalC
losure s
-/
theorem map_normalClosure (s : Set G) (f : G →* N) (hf : Surjective f) :
    (normalClosure s).map f = normalClosure (f '' s) := by
  have : Normal (map f (normalClosure s)) := Normal.map inferInstance f hf
  apply le_antisymm
  · exact map_normalClosure_le s f
  · exact normalClosure_le_normal (Set.image_mono subset_normalClosure)

@[to_additive]
/-
**Subgroup.comap_normalClosure** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：comap_normalClosure (s : Set N) (f : G ≃* N) : normalClosure (f ⁻¹' s) = (
normalClosure s).comap f
参数：s : Set N；f : G ≃* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `Equiv.image_symm_eq_preimage`：image_symm_eq_preimage (e : α ≃ β) (s : Se
t β) : e.symm '' s = e ⁻¹' s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.comap_equiv_eq_map_symm`：comap_equiv_eq_map_symm (f : N ≃* G) (
K : Subgroup G) : K.comap (G
· 使用定理 `Subgroup.map_normalClosure`：map_normalClosure (s : Set G) (f : G ->* N) 
(hf : Surjective f) : (normalClosure s).map f = normalClosure (f '' s)
· 使用定理 `MulEquiv.surjective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [ins
t_1 : Mul N] (e : M ≃* N), Function.Surjective ⇑e
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comap_normalClosure (s : Set N) (f : G ≃* N) :
    normalClosure (f ⁻¹' s) = (normalClosure s).comap f := by
  have := f.toEquiv.image_symm_eq_preimage s
  simp_all [comap_equiv_eq_map_symm, map_normalClosure s (f.symm : N →* G) f.symm.surjective]
/-
**Subgroup.Normal.of_map_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.Normal`。
形式化陈述：∀ {G : Type u_6} {H : Type u_7} [inst : Group G] [inst_1 : Group H] {φ : G
 →* H},   Function.Injective ⇑φ → ∀ {L : Subgroup G}, (Subgroup.map φ L).Normal 
→ L.Normal
参数：Subgroup.map φ L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.Normal.comap`：∀ {G : Type u_1} [inst : Group G] {N : Type u_5} 
[inst_1 : Group N] {H : Subgroup N},   H.Normal → ∀ (f : G →* N), (Subgroup.coma
p f H).Norm…
· 使用定理 `Subgroup.comap_map_eq_self_of_injective`：comap_map_eq_self_of_injective 
{f : G ->* N} (h : Function.Injective f) (H : Subgroup G) : comap f (map f H) = 
H
-/
lemma Normal.of_map_injective {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (hφ : Function.Injective φ) {L : Subgroup G} (n : (L.map φ).Normal) : L.Normal :=
  L.comap_map_eq_self_of_injective hφ ▸ n.comap φ
/-
**Subgroup.Normal.of_map_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.Normal`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {K : Subgroup G} {L : Subgroup ↥K}, (Sub
group.map K.subtype L).Normal → L.Normal
参数：Subgroup.map K.subtype L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.Normal.of_map_injective`：∀ {G : Type u_6} {H : Type u_7} [inst 
: Group G] [inst_1 : Group H] {φ : G →* H},   Function.Injective ⇑φ → ∀ {L : Sub
group G}, (Subgroup.ma…
· 使用引理 `Subgroup.subtype_injective`：subtype_injective (s : Subgroup G) : Functio
n.Injective s.subtype
-/
theorem Normal.of_map_subtype {K : Subgroup G} {L : Subgroup K}
    (n : (Subgroup.map K.subtype L).Normal) : L.Normal :=
  n.of_map_injective K.subtype_injective
/-
**Subgroup.normal_comap_iff_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：normal_comap_iff_of_surjective {f : G ->* N} (hf : Function.Surjective f) 
{H : Subgroup N} : (H.comap f).Normal ↔ H.Normal
参数：hf : Function.Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.normalizer_eq_top_iff`：normalizer_eq_top_iff : normalizer (H : 
Set G) = ⊤ ↔ H.Normal
· 使用定理 `Subgroup.comap_normalizer_eq_of_surjective`：comap_normalizer_eq_of_surje
ctive (H : Subgroup G) {f : N ->* G} (hf : Function.Surjective f) : (normalizer 
H).comap f = normalizer (H.comap…
· 使用定理 `Subgroup.comap_top`：comap_top (f : G ->* N) : (⊤ : Subgroup N).comap f =
 ⊤
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Subgroup.comap_injective`：comap_injective {f : G ->* N} (h : Function.Su
rjective f) : Function.Injective (comap f)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem normal_comap_iff_of_surjective {f : G →* N} (hf : Function.Surjective f) {H : Subgroup N} :
    (H.comap f).Normal ↔ H.Normal := by
  rw [← normalizer_eq_top_iff, ← comap_normalizer_eq_of_surjective H hf, ← comap_top f,
    (comap_injective hf).eq_iff, normalizer_eq_top_iff]
/-
**Subgroup._root_.MulEquiv.normal_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MulEquiv.normal_map_iff {f : G ≃* G'} {H : Subgroup G} :
    (H.map (f : G →* G')).Normal ↔ H.Normal := by
  rw [map_equiv_eq_comap_symm, normal_comap_iff_of_surjective f.symm.surjective]

section SubgroupNormal

@[to_additive]
/-
**Subgroup.normal_subgroupOf_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：normal_subgroupOf_iff {H K : Subgroup G} (hHK : H <= K) : (H.subgroupOf K)
.Normal ↔ forall h k, h in H -> k in K -> k * h * k⁻¹ in H
参数：hHK : H <= K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.Normal.conj_mem`：∀ {G : Type u_1} [inst : Group G] {H : Subgrou
p G}, H.Normal → ∀ n ∈ H, ∀ (g : G), g * n * g⁻¹ ∈ H
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem normal_subgroupOf_iff {H K : Subgroup G} (hHK : H ≤ K) :
    (H.subgroupOf K).Normal ↔ ∀ h k, h ∈ H → k ∈ K → k * h * k⁻¹ ∈ H :=
  ⟨fun hN h k hH hK => hN.conj_mem ⟨h, hHK hH⟩ hH ⟨k, hK⟩, fun hN =>
    { conj_mem := fun h hm k => hN h.1 k.1 hm k.2 }⟩

@[to_additive prod_addSubgroupOf_prod_normal]
/-
**Subgroup.prod_subgroupOf_prod_normal** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：prod_subgroupOf_prod_normal {H₁ K₁ : Subgroup G} {H₂ K₂ : Subgroup N} [h₁ 
: (H₁.subgroupOf K₁).Normal] [h₂ : (H₂.subgroupOf K₂).Normal] : ((H₁.prod H₂).su
bgroupOf (K₁.prod K₂)).Normal where conj_mem n hgHK g
参数：H₁.subgroupOf K₁；H₂.subgroupOf K₂。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.Normal.conj_mem`：∀ {G : Type u_1} [inst : Group G] {H : Subgrou
p G}, H.Normal → ∀ n ∈ H, ∀ (g : G), g * n * g⁻¹ ∈ H
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.mem_prod`：mem_prod {H : Subgroup G} {K : Subgroup N} {p : G × N
} : p in H.prod K ↔ p.1 in H ∧ p.2 in K
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
instance prod_subgroupOf_prod_normal {H₁ K₁ : Subgroup G} {H₂ K₂ : Subgroup N}
    [h₁ : (H₁.subgroupOf K₁).Normal] [h₂ : (H₂.subgroupOf K₂).Normal] :
    ((H₁.prod H₂).subgroupOf (K₁.prod K₂)).Normal where
  conj_mem n hgHK g :=
    ⟨h₁.conj_mem ⟨(n : G × N).fst, (mem_prod.mp n.2).1⟩ hgHK.1
        ⟨(g : G × N).fst, (mem_prod.mp g.2).1⟩,
      h₂.conj_mem ⟨(n : G × N).snd, (mem_prod.mp n.2).2⟩ hgHK.2
        ⟨(g : G × N).snd, (mem_prod.mp g.2).2⟩⟩

@[to_additive prod_normal]
/-
**Subgroup.prod_normal** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：prod_normal (H : Subgroup G) (K : Subgroup N) [hH : H.Normal] [hK : K.Norm
al] : (H.prod K).Normal where conj_mem n hg g
参数：H : Subgroup G；K : Subgroup N。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.Normal.conj_mem`：∀ {G : Type u_1} [inst : Group G] {H : Subgrou
p G}, H.Normal → ∀ n ∈ H, ∀ (g : G), g * n * g⁻¹ ∈ H
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.mem_prod`：mem_prod {H : Subgroup G} {K : Subgroup N} {p : G × N
} : p in H.prod K ↔ p.1 in H ∧ p.2 in K
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
instance prod_normal (H : Subgroup G) (K : Subgroup N) [hH : H.Normal] [hK : K.Normal] :
    (H.prod K).Normal where
  conj_mem n hg g :=
    ⟨hH.conj_mem n.fst (Subgroup.mem_prod.mp hg).1 g.fst,
      hK.conj_mem n.snd (Subgroup.mem_prod.mp hg).2 g.snd⟩

@[to_additive]
/-
**Subgroup.inf_subgroupOf_inf_normal_of_right** 是 Mathlib 中的一个定理，位于命名空间 `Subgrou
p`。
形式化陈述：inf_subgroupOf_inf_normal_of_right (A B' B : Subgroup G) [hN : (B'.subgrou
pOf B).Normal] : ((A ⊓ B').subgroupOf (A ⊓ B)).Normal
参数：A B' B : Subgroup G；B'.subgroupOf B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.normal_subgroupOf_iff_le_normalizer_inf`：normal_subgroupOf_iff_
le_normalizer_inf : (H.subgroupOf K).Normal ↔ K <= normalizer (H ⊓ K : Subgroup 
G)
· 使用定理 `inf_inf_inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c d : α)
, a ⊓ b ⊓ (c ⊓ d) = a ⊓ c ⊓ (b ⊓ d)
· 使用定理 `inf_idem`：∀ {α : Type u} [inst : SemilatticeInf α] (a : α), a ⊓ a = a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `inf_le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c d : α}, b ≤ 
a → d ≤ c → b ⊓ d ≤ a ⊓ c
· 使用定理 `Subgroup.le_normalizer`：le_normalizer : H <= normalizer H
· 使用定理 `Subgroup.inf_normalizer_le_normalizer_inf`：inf_normalizer_le_normalizer_
inf : normalizer H ⊓ normalizer K <= normalizer ((H ⊓ K :) : Set G)
-/
theorem inf_subgroupOf_inf_normal_of_right (A B' B : Subgroup G)
    [hN : (B'.subgroupOf B).Normal] : ((A ⊓ B').subgroupOf (A ⊓ B)).Normal := by
  rw [normal_subgroupOf_iff_le_normalizer_inf] at hN ⊢
  rw [inf_inf_inf_comm, inf_idem]
  exact le_trans (inf_le_inf A.le_normalizer hN) inf_normalizer_le_normalizer_inf

@[to_additive]
/-
**Subgroup.inf_subgroupOf_inf_normal_of_left** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup
`。
形式化陈述：inf_subgroupOf_inf_normal_of_left {A' A : Subgroup G} (B : Subgroup G) [hN
 : (A'.subgroupOf A).Normal] : ((A' ⊓ B).subgroupOf (A ⊓ B)).Normal
参数：B : Subgroup G；A'.subgroupOf A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.normal_subgroupOf_iff_le_normalizer_inf`：normal_subgroupOf_iff_
le_normalizer_inf : (H.subgroupOf K).Normal ↔ K <= normalizer (H ⊓ K : Subgroup 
G)
· 使用定理 `inf_inf_inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c d : α)
, a ⊓ b ⊓ (c ⊓ d) = a ⊓ c ⊓ (b ⊓ d)
· 使用定理 `inf_idem`：∀ {α : Type u} [inst : SemilatticeInf α] (a : α), a ⊓ a = a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `inf_le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c d : α}, b ≤ 
a → d ≤ c → b ⊓ d ≤ a ⊓ c
· 使用定理 `Subgroup.le_normalizer`：le_normalizer : H <= normalizer H
· 使用定理 `Subgroup.inf_normalizer_le_normalizer_inf`：inf_normalizer_le_normalizer_
inf : normalizer H ⊓ normalizer K <= normalizer ((H ⊓ K :) : Set G)
-/
theorem inf_subgroupOf_inf_normal_of_left {A' A : Subgroup G} (B : Subgroup G)
    [hN : (A'.subgroupOf A).Normal] : ((A' ⊓ B).subgroupOf (A ⊓ B)).Normal := by
  rw [normal_subgroupOf_iff_le_normalizer_inf] at hN ⊢
  rw [inf_inf_inf_comm, inf_idem]
  exact le_trans (inf_le_inf hN B.le_normalizer) inf_normalizer_le_normalizer_inf

@[to_additive]
/-
**Subgroup.normal_inf_normal** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：normal_inf_normal (H K : Subgroup G) [hH : H.Normal] [hK : K.Normal] : (H 
⊓ K).Normal
参数：H K : Subgroup G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.Normal.conj_mem`：∀ {G : Type u_1} [inst : Group G] {H : Subgrou
p G}, H.Normal → ∀ n ∈ H, ∀ (g : G), g * n * g⁻¹ ∈ H
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
instance normal_inf_normal (H K : Subgroup G) [hH : H.Normal] [hK : K.Normal] : (H ⊓ K).Normal :=
  ⟨fun n hmem g => ⟨hH.conj_mem n hmem.1 g, hK.conj_mem n hmem.2 g⟩⟩

@[to_additive]
/-
**Subgroup.normal_iInf_normal** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：normal_iInf_normal {ι : Sort*} {a : ι -> Subgroup G} (norm : forall i : ι,
 (a i).Normal) : (iInf a).Normal
参数：norm : forall i : ι, (a i).Normal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.mem_iInf`：mem_iInf {ι : Sort*} {S : ι -> Subgroup G} {x : G} : 
x in ⨅ i, S i ↔ forall i, x in S i
· 使用定理 `Subgroup.Normal.conj_mem`：∀ {G : Type u_1} [inst : Group G] {H : Subgrou
p G}, H.Normal → ∀ n ∈ H, ∀ (g : G), g * n * g⁻¹ ∈ H
-/
theorem normal_iInf_normal {ι : Sort*} {a : ι → Subgroup G}
    (norm : ∀ i : ι, (a i).Normal) : (iInf a).Normal := by
  constructor
  intro g g_in_iInf h
  rw [Subgroup.mem_iInf] at g_in_iInf ⊢
  intro i
  exact (norm i).conj_mem g (g_in_iInf i) h

@[to_additive]
/-
**Subgroup.SubgroupNormal.mem_comm** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.SubgroupN
ormal`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {H K : Subgroup G},   H ≤ K → ∀ [hN : (H
.subgroupOf K).Normal] {a b : G}, b ∈ K → a * b ∈ H → b * a ∈ H
参数：H.subgroupOf K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.normal_subgroupOf_iff`：normal_subgroupOf_iff {H K : Subgroup G}
 (hHK : H <= K) : (H.subgroupOf K).Normal ↔ forall h k, h in H -> k in K -> k * 
h * k⁻¹ in H
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem SubgroupNormal.mem_comm {H K : Subgroup G} (hK : H ≤ K) [hN : (H.subgroupOf K).Normal]
    {a b : G} (hb : b ∈ K) (h : a * b ∈ H) : b * a ∈ H := by
  have := (normal_subgroupOf_iff hK).mp hN (a * b) b h hb
  rwa [mul_assoc, mul_assoc, mul_inv_cancel, mul_one] at this

/-- Elements of disjoint, normal subgroups commute. -/
@[to_additive /-- Elements of disjoint, normal subgroups commute. -/]
/-
**Subgroup.commute_of_normal_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：commute_of_normal_of_disjoint (H₁ H₂ : Subgroup G) (hH₁ : H₁.Normal) (hH₂ 
: H₂.Normal) (hdis : Disjoint H₁ H₂) (x y : G) (hx : x in H₁) (hy : y in H₂) : C
ommute x y
参数：H₁ H₂ : Subgroup G；hH₁ : H₁.Normal；hH₂ : H₂.Normal；hdis : Disjoint H₁ H₂；x y 
: G；hx : x in H₁；hy : y in H₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
· 使用定理 `Subgroup.mul_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
y : G}, x ∈ H → y ∈ H → x * y ∈ H
· 使用定理 `Subgroup.Normal.conj_mem`：∀ {G : Type u_1} [inst : Group G] {H : Subgrou
p G}, H.Normal → ∀ n ∈ H, ∀ (g : G), g * n * g⁻¹ ∈ H
· 使用定理 `Subgroup.inv_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
: G}, x ∈ H → x⁻¹ ∈ H
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_eq_one_iff_eq_inv`：mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹

--- 原说明 ---
Elements of disjoint, normal subgroups commute.
-/
theorem commute_of_normal_of_disjoint (H₁ H₂ : Subgroup G) (hH₁ : H₁.Normal) (hH₂ : H₂.Normal)
    (hdis : Disjoint H₁ H₂) (x y : G) (hx : x ∈ H₁) (hy : y ∈ H₂) : Commute x y := by
  suffices x * y * x⁻¹ * y⁻¹ = 1 by
    change x * y = y * x
    · rw [mul_assoc, mul_eq_one_iff_eq_inv] at this
      simpa
  apply hdis.le_bot
  constructor
  · suffices x * (y * x⁻¹ * y⁻¹) ∈ H₁ by simpa [mul_assoc]
    exact H₁.mul_mem hx (hH₁.conj_mem _ (H₁.inv_mem hx) _)
  · change x * y * x⁻¹ * y⁻¹ ∈ H₂
    apply H₂.mul_mem _ (H₂.inv_mem hy)
    apply hH₂.conj_mem _ hy

@[to_additive]
/-
**Subgroup.normal_subgroupOf_of_le_normalizer** 是 Mathlib 中的一个定理，位于命名空间 `Subgrou
p`。
形式化陈述：normal_subgroupOf_of_le_normalizer {H N : Subgroup G} (hLE : H <= normaliz
er N) : (N.subgroupOf H).Normal
参数：hLE : H <= normalizer N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.normal_subgroupOf_iff_le_normalizer_inf`：normal_subgroupOf_iff_
le_normalizer_inf : (H.subgroupOf K).Normal ↔ K <= normalizer (H ⊓ K : Subgroup 
G)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `Subgroup.le_normalizer`：le_normalizer : H <= normalizer H
· 使用定理 `Subgroup.inf_normalizer_le_normalizer_inf`：inf_normalizer_le_normalizer_
inf : normalizer H ⊓ normalizer K <= normalizer ((H ⊓ K :) : Set G)
-/
theorem normal_subgroupOf_of_le_normalizer {H N : Subgroup G}
    (hLE : H ≤ normalizer N) : (N.subgroupOf H).Normal := by
  rw [normal_subgroupOf_iff_le_normalizer_inf]
  exact (le_inf hLE H.le_normalizer).trans inf_normalizer_le_normalizer_inf

@[to_additive]
/-
**Subgroup.normal_subgroupOf_sup_of_le_normalizer** 是 Mathlib 中的一个定理，位于命名空间 `Sub
group`。
形式化陈述：normal_subgroupOf_sup_of_le_normalizer {H N : Subgroup G} (hLE : H <= norm
alizer N) : (N.subgroupOf (H ⊔ N)).Normal
参数：hLE : H <= normalizer N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.normal_subgroupOf_iff_le_normalizer`：normal_subgroupOf_iff_le_n
ormalizer (h : H <= K) : (H.subgroupOf K).Normal ↔ K <= normalizer H
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `Subgroup.le_normalizer`：le_normalizer : H <= normalizer H
-/
theorem normal_subgroupOf_sup_of_le_normalizer {H N : Subgroup G}
    (hLE : H ≤ normalizer N) : (N.subgroupOf (H ⊔ N)).Normal := by
  rw [normal_subgroupOf_iff_le_normalizer le_sup_right]
  exact sup_le hLE le_normalizer

end SubgroupNormal

@[to_additive]
/-
**Subgroup.normal_subgroupOf_closure_normalizer** 是 Mathlib 中的一个实例，位于命名空间 `Subgr
oup`。
形式化陈述：normal_subgroupOf_closure_normalizer (s : Set G) : (closure s |>.subgroupO
f <| normalizer s).Normal
参数：s : Set G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.normal_subgroupOf_of_le_normalizer`：normal_subgroupOf_of_le_nor
malizer {H N : Subgroup G} (hLE : H <= normalizer N) : (N.subgroupOf H).Normal
· 使用定理 `Subgroup.normalizer_le_normalizer_closure`：normalizer_le_normalizer_clos
ure (s : Set G) : normalizer s <= normalizer (closure s)
-/
instance normal_subgroupOf_closure_normalizer (s : Set G) :
    (closure s |>.subgroupOf <| normalizer s).Normal :=
  normal_subgroupOf_of_le_normalizer <| normalizer_le_normalizer_closure s

end Subgroup

namespace IsConj

open Subgroup

set_option backward.isDefEq.respectTransparency false in
/-
**IsConj.normalClosure_eq_top_of** 是 Mathlib 中的一个定理，位于命名空间 `IsConj`。
形式化陈述：normalClosure_eq_top_of {N : Subgroup G} [hn : N.Normal] {g g' : G} {hg : 
g in N} {hg' : g' in N} (hc : IsConj g g') (ht : normalClosure ({⟨g, hg⟩} : Set 
N) = ⊤) : normalClosure ({⟨g', hg'⟩} : Set N) = ⊤
参数：hc : IsConj g g'；ht : normalClosure ({⟨g, hg⟩} : Set N) = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isConj_iff`：isConj_iff {a b : α} : IsConj a b ↔ exists c : α, c * a * c⁻
¹ = b
· 使用定理 `Subgroup.Normal.conj_mem`：∀ {G : Type u_1} [inst : Group G] {H : Subgrou
p G}, H.Normal → ∀ n ∈ H, ∀ (g : G), g * n * g⁻¹ ∈ H
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MonoidHom.codRestrict_apply`：∀ {M : Type u_1} {N : Type u_2} [inst : Mul
OneClass M] [inst_1 : MulOneClass N] {S : Type u_5} [inst_2 : SetLike S N]   [in
st_3 : SubmonoidC…
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MonoidHom.range_eq_top`：range_eq_top {N} [Group N] {f : G ->* N} : f.ran
ge = (⊤ : Subgroup N) ↔ Function.Surjective f
· 使用定理 `MonoidHom.range_eq_map`：range_eq_map (f : G ->* N) : f.range = (⊤ : Subg
roup G).map f
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Subgroup.map_mono`：map_mono {f : G ->* N} {K K' : Subgroup G} : K <= K' 
-> map f K <= map f K'
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Subgroup.map_le_iff_le_comap`：map_le_iff_le_comap {f : G ->* N} {K : Sub
group G} {H : Subgroup N} : K.map f <= H ↔ K <= H.comap f
· 使用定理 `Subgroup.normalClosure_le_normal`：normalClosure_le_normal {N : Subgroup 
G} [N.Normal] (h : s subseteq N) : normalClosure s <= N
· 使用定理 `Subgroup.normal_comap`：∀ {G : Type u_1} [inst : Group G] {N : Type u_5} 
[inst_1 : Group N] {H : Subgroup N} [nH : H.Normal] (f : G →* N),   (Subgroup.co
map f H).No…
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Subgroup.subset_normalClosure`：subset_normalClosure : s subseteq normalC
losure s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
-/
theorem normalClosure_eq_top_of {N : Subgroup G} [hn : N.Normal] {g g' : G} {hg : g ∈ N}
    {hg' : g' ∈ N} (hc : IsConj g g') (ht : normalClosure ({⟨g, hg⟩} : Set N) = ⊤) :
    normalClosure ({⟨g', hg'⟩} : Set N) = ⊤ := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hc
  have h : ∀ x : N, (MulAut.conj c) x ∈ N := by
    rintro ⟨x, hx⟩
    exact hn.conj_mem _ hx c
  have hs : Function.Surjective (((MulAut.conj c).toMonoidHom.domRestrict N).codRestrict _ h) := by
    rintro ⟨x, hx⟩
    refine ⟨⟨c⁻¹ * x * c, ?_⟩, ?_⟩
    · have h := hn.conj_mem _ hx c⁻¹
      rwa [inv_inv] at h
    simp only [MonoidHom.codRestrict_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.domRestrict_apply, Subtype.mk_eq_mk, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [mul_assoc, mul_inv_cancel, mul_one]
  rw [eq_top_iff, ← MonoidHom.range_eq_top.2 hs, MonoidHom.range_eq_map]
  grw [eq_top_iff.1 ht]
  refine map_le_iff_le_comap.2 (normalClosure_le_normal ?_)
  rw [Set.singleton_subset_iff, SetLike.mem_coe]
  simp only [MonoidHom.codRestrict_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    MonoidHom.domRestrict_apply, mem_comap]
  exact subset_normalClosure (Set.mem_singleton _)

end IsConj

namespace ConjClasses

/-- The conjugacy classes that are not trivial. -/
/-
**ConjClasses.noncenter** 是 Mathlib 中的一个定义，位于命名空间 `ConjClasses`。
形式化陈述：noncenter (G : Type*) [Monoid G] : Set (ConjClasses G)
参数：G : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The conjugacy classes that are not trivial.
-/
def noncenter (G : Type*) [Monoid G] : Set (ConjClasses G) :=
  {x | x.carrier.Nontrivial}
/-
**ConjClasses.mem_noncenter** 是 Mathlib 中的一个定理，位于命名空间 `ConjClasses`。
形式化陈述：∀ {G : Type u_6} [inst : Monoid G] (g : ConjClasses G), g ∈ ConjClasses.no
ncenter G ↔ g.carrier.Nontrivial
参数：g : ConjClasses G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_noncenter {G} [Monoid G] (g : ConjClasses G) :
    g ∈ noncenter G ↔ g.carrier.Nontrivial := Iff.rfl

end ConjClasses

namespace AddSubgroup

variable {M : Type*} [AddGroup M] (I : AddSubgroup M) (G : Type*)
    [Group G] [MulAction G M]

/-- Suppose `G` acts on `M` and `I` is a subgroup of `M`.
The inertia subgroup of `I` is the subgroup of `G` whose action is trivial mod `I`. -/
/-
**AddSubgroup.inertia** 是 Mathlib 中的一个定义，位于命名空间 `AddSubgroup`。
形式化陈述：inertia : Subgroup G where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Suppose `G` acts on `M` and `I` is a subgroup of `M`.
The inertia subgroup of `I` is the subgroup of `G` whose action is trivial mod `
I`.
-/
def inertia : Subgroup G where
  carrier := { σ | ∀ x, σ • x - x ∈ I }
  mul_mem' {a b} ha hb x := by simpa [mul_smul] using add_mem (ha (b • x)) (hb x)
  one_mem' := by simp [zero_mem]
  inv_mem' {a} ha x := by simpa using sub_mem_comm_iff.mp (ha (a⁻¹ • x))

variable {I G} in
@[simp]
/-
**AddSubgroup.mem_inertia** 是 Mathlib 中的一个引理，位于命名空间 `AddSubgroup`。
形式化陈述：mem_inertia {σ : G} : σ in I.inertia G ↔ forall x, σ • x - x in I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_inertia {σ : G} : σ ∈ I.inertia G ↔ ∀ x, σ • x - x ∈ I := .rfl

variable {G} in
@[simp]
/-
**AddSubgroup.subgroupOf_inertia** 是 Mathlib 中的一个引理，位于命名空间 `AddSubgroup`。
形式化陈述：subgroupOf_inertia (H : Subgroup G) : (I.inertia G).subgroupOf H = I.inert
ia H
参数：H : Subgroup G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subgroupOf_inertia (H : Subgroup G) : (I.inertia G).subgroupOf H = I.inertia H :=
  rfl

variable {I G} in
/-
**AddSubgroup.coe_mem_inertia** 是 Mathlib 中的一个引理，位于命名空间 `AddSubgroup`。
形式化陈述：coe_mem_inertia {H : Subgroup G} {σ : H} : ↑σ in I.inertia G ↔ σ in I.iner
tia H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma coe_mem_inertia {H : Subgroup G} {σ : H} : ↑σ ∈ I.inertia G ↔ σ ∈ I.inertia H := .rfl

variable {G} in
@[simp]
/-
**AddSubgroup.inertia_map_subtype** 是 Mathlib 中的一个引理，位于命名空间 `AddSubgroup`。
形式化陈述：inertia_map_subtype (H : Subgroup G) : (I.inertia H).map H.subtype = I.ine
rtia G ⊓ H
参数：H : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AddSubgroup.subgroupOf_inertia`：subgroupOf_inertia (H : Subgroup G) : (I
.inertia G).subgroupOf H = I.inertia H
· 使用定理 `Subgroup.subgroupOf_map_subtype`：subgroupOf_map_subtype (H K : Subgroup 
G) : (H.subgroupOf K).map K.subtype = H ⊓ K
-/
lemma inertia_map_subtype (H : Subgroup G) : (I.inertia H).map H.subtype = I.inertia G ⊓ H := by
  rw [← AddSubgroup.subgroupOf_inertia, Subgroup.subgroupOf_map_subtype]

end AddSubgroup

