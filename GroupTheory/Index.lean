/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.GroupWithZero.Subgroup
public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Index of a Subgroup

In this file we define the index of a subgroup, and prove several divisibility properties.
Several theorems proved in this file are known as Lagrange's theorem.

## Main definitions

- `H.index` : the index of `H : Subgroup G` as a natural number,
  and returns 0 if the index is infinite.
- `H.relIndex K` : the relative index of `H : Subgroup G` in `K : Subgroup G` as a natural number,
  and returns 0 if the relative index is infinite.

## Main results

- `card_mul_index` : `Nat.card H * H.index = Nat.card G`
- `index_mul_card` : `H.index * Nat.card H = Nat.card G`
- `index_dvd_card` : `H.index ∣ Nat.card G`
- `relIndex_mul_index` : If `H ≤ K`, then `H.relindex K * K.index = H.index`
- `index_dvd_of_le` : If `H ≤ K`, then `K.index ∣ H.index`
- `relIndex_mul_relIndex` : `relIndex` is multiplicative in towers
- `MulAction.index_stabilizer`: the index of the stabilizer is the cardinality of the orbit
-/

@[expose] public section

assert_not_exists Field

open scoped Pointwise

namespace Subgroup

open Cardinal Function

variable {G G' : Type*} [Group G] [Group G'] (H K L : Subgroup G)

/-- The index of a subgroup as a natural number. Returns `0` if the index is infinite. -/
@[to_additive (attr := wikidata Q1464168) /-- The index of an additive subgroup as a natural number.
Returns 0 if the index is infinite. -/]
/-
**Subgroup.index** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：index : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def index : ℕ :=
  Nat.card (G ⧸ H)

/-- If `H` and `K` are subgroups of a group `G`, then `relIndex H K : ℕ` is the index
of `H ∩ K` in `K`. The function returns `0` if the index is infinite. -/
@[to_additive /-- If `H` and `K` are subgroups of an additive group `G`, then `relIndex H K : ℕ`
is the index of `H ∩ K` in `K`. The function returns `0` if the index is infinite. -/]
/-
**Subgroup.relIndex** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：relIndex : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def relIndex : ℕ :=
  (H.subgroupOf K).index

@[to_additive]
/-
**Subgroup.index_comap_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：index_comap_of_surjective {f : G' ->* G} (hf : Function.Surjective f) : (H
.comap f).index = H.index
参数：hf : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MonoidHom.map_mul`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N) (a b : M), f (a * b) = f a * f b
· 使用定理 `MonoidHom.map_inv`：∀ {α : Type u_2} {β : Type u_3} [inst : Group α] [ins
t_1 : DivisionMonoid β] (f : α →* β) (a : α), f a⁻¹ = (f a)⁻¹
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Quotient.map'`：map'_mk'' (f : α -> β) (h) (x : α) : (Quotient.mk'' x : Q
uotient s₁).map' f h = (Quotient.mk'' (f x) : Quotient s₂)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Quotient.ind'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁ → Prop}
, (∀ (a : α), p (Quotient.mk'' a)) → ∀ (q : Quotient s₁), p q
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Quotient.map'_mk''`：∀ {α : Sort u_1} {β : Sort u_2} {s₁ : Setoid α} {s₂ 
: Setoid β} (f : α → β) (h : ∀ (a b : α), s₁ a b → s₂ (f a) (f b))   (x : α), Qu
otient.m…
-/
theorem index_comap_of_surjective {f : G' →* G} (hf : Function.Surjective f) :
    (H.comap f).index = H.index := by
  have key : ∀ x y : G',
      QuotientGroup.leftRel (H.comap f) x y ↔ QuotientGroup.leftRel H (f x) (f y) := by
    simp only [QuotientGroup.leftRel_apply]
    exact fun x y => iff_of_eq (congr_arg (· ∈ H) (by rw [f.map_mul, f.map_inv]))
  refine Nat.card_congr (Equiv.ofBijective (Quotient.map' f fun x y => (key x y).mp) ⟨?_, ?_⟩)
  · simp_rw [← Quotient.eq''] at key
    refine Quotient.ind' fun x => ?_
    refine Quotient.ind' fun y => ?_
    exact (key x y).mpr
  · refine Quotient.ind' fun x => ?_
    obtain ⟨y, hy⟩ := hf x
    exact ⟨y, (Quotient.map'_mk'' f _ y).trans (congr_arg Quotient.mk'' hy)⟩

@[to_additive]
/-
**Subgroup.index_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：index_comap (f : G' ->* G) : (H.comap f).index = H.relIndex f.range
参数：f : G' ->* G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Subgroup.index_comap_of_surjective`：index_comap_of_surjective {f : G' ->
* G} (hf : Function.Surjective f) : (H.comap f).index = H.index
· 使用定理 `MonoidHom.rangeRestrict_surjective`：rangeRestrict_surjective (f : G ->* 
N) : Function.Surjective f.rangeRestrict
-/
theorem index_comap (f : G' →* G) :
    (H.comap f).index = H.relIndex f.range :=
  Eq.trans (congr_arg index (by rfl))
    ((H.subgroupOf f.range).index_comap_of_surjective f.rangeRestrict_surjective)

@[to_additive]
/-
**Subgroup.relIndex_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：relIndex_comap (f : G' ->* G) (K : Subgroup G') : relIndex (comap f H) K =
 relIndex H (map f K)
参数：f : G' ->* G；K : Subgroup G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.relIndex.eq_1`：∀ {G : Type u_1} [inst : Group G] (H K : Subgrou
p G), H.relIndex K = (H.subgroupOf K).index
· 使用定理 `Subgroup.subgroupOf.eq_1`：∀ {G : Type u_1} [inst : Group G] (H K : Subgr
oup G), H.subgroupOf K = Subgroup.comap K.subtype H
· 使用定理 `Subgroup.comap_comap`：comap_comap (K : Subgroup P) (g : N ->* P) (f : G 
->* N) : (K.comap g).comap f = K.comap (g.comp f)
· 使用定理 `Subgroup.index_comap`：index_comap (f : G' ->* G) : (H.comap f).index = H
.relIndex f.range
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.map_range`：map_range (g : N ->* P) (f : G ->* N) : f.range.map
 g = (g.comp f).range
· 使用定理 `Subgroup.range_subtype`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup 
G), H.subtype.range = H
-/
theorem relIndex_comap (f : G' →* G) (K : Subgroup G') :
    relIndex (comap f H) K = relIndex H (map f K) := by
  rw [relIndex, subgroupOf, comap_comap, index_comap, ← f.map_range, K.range_subtype]

@[to_additive]
/-
**Subgroup.relIndex_map_map_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：relIndex_map_map_of_injective {f : G ->* G'} (H K : Subgroup G) (hf : Func
tion.Injective f) : relIndex (map f H) (map f K) = relIndex H K
参数：H K : Subgroup G；hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.relIndex_comap`：relIndex_comap (f : G' ->* G) (K : Subgroup G')
 : relIndex (comap f H) K = relIndex H (map f K)
· 使用定理 `Subgroup.comap_map_eq_self_of_injective`：comap_map_eq_self_of_injective 
{f : G ->* N} (h : Function.Injective f) (H : Subgroup G) : comap f (map f H) = 
H
-/
theorem relIndex_map_map_of_injective {f : G →* G'} (H K : Subgroup G) (hf : Function.Injective f) :
    relIndex (map f H) (map f K) = relIndex H K := by
  rw [← Subgroup.relIndex_comap, Subgroup.comap_map_eq_self_of_injective hf]

@[to_additive]
/-
**Subgroup.relIndex_map_map** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：relIndex_map_map (f : G ->* G') (H K : Subgroup G) : (map f H).relIndex (m
ap f K) = (H ⊔ f.ker).relIndex (K ⊔ f.ker)
参数：f : G ->* G'；H K : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.comap_map_eq`：comap_map_eq (H : Subgroup G) : comap f (map f H)
 = H ⊔ f.ker
· 使用定理 `Subgroup.relIndex_comap`：relIndex_comap (f : G' ->* G) (K : Subgroup G')
 : relIndex (comap f H) K = relIndex H (map f K)
· 使用定理 `GaloisConnection.l_u_l_eq_l`：∀ {α : Type u} {β : Type v} [inst : Partial
Order α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u →
 ∀ (b : β), l (u …
· 使用定理 `Subgroup.gc_map_comap`：gc_map_comap (f : G ->* N) : GaloisConnection (ma
p f) (comap f)
-/
theorem relIndex_map_map (f : G →* G') (H K : Subgroup G) :
    (map f H).relIndex (map f K) = (H ⊔ f.ker).relIndex (K ⊔ f.ker) := by
  rw [← comap_map_eq, ← comap_map_eq, relIndex_comap, (gc_map_comap f).l_u_l_eq_l]

variable {H K L}

@[to_additive relIndex_mul_index]
/-
**Subgroup.relIndex_mul_index** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：relIndex_mul_index (h : H <= K) : H.relIndex K * K.index = H.index
参数：h : H <= K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem relIndex_mul_index (h : H ≤ K) : H.relIndex K * K.index = H.index := by
  rw [mul_comm]
  simp_rw [relIndex, index, ← Nat.card_prod, Nat.card_congr <| quotientEquivProdOfLE h]

@[to_additive]
/-
**Subgroup.index_dvd_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：index_dvd_of_le (h : H <= K) : K.index ∣ H.index
参数：h : H <= K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_of_mul_left_eq`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b : α} 
(c : α), c * a = b → a ∣ b
· 使用定理 `Subgroup.relIndex_mul_index`：relIndex_mul_index (h : H <= K) : H.relInde
x K * K.index = H.index
-/
theorem index_dvd_of_le (h : H ≤ K) : K.index ∣ H.index :=
  dvd_of_mul_left_eq (H.relIndex K) (relIndex_mul_index h)

@[to_additive]
/-
**Subgroup.relIndex_dvd_index_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：relIndex_dvd_index_of_le (h : H <= K) : H.relIndex K ∣ H.index
参数：h : H <= K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_of_mul_right_eq`：∀ {α : Type u_1} [inst : Semigroup α] {a b : α} (c 
: α), a * c = b → a ∣ b
· 使用定理 `Subgroup.relIndex_mul_index`：relIndex_mul_index (h : H <= K) : H.relInde
x K * K.index = H.index
-/
theorem relIndex_dvd_index_of_le (h : H ≤ K) : H.relIndex K ∣ H.index :=
  dvd_of_mul_right_eq K.index (relIndex_mul_index h)

@[to_additive]
/-
**Subgroup.relIndex_subgroupOf** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：relIndex_subgroupOf (hKL : K <= L) : (H.subgroupOf L).relIndex (K.subgroup
Of L) = H.relIndex K
参数：hKL : K <= L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subgroup.index_comap`：index_comap (f : G' ->* G) : (H.comap f).index = H
.relIndex f.range
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Subgroup.inclusion_range`：∀ {G : Type u_1} [inst : Group G] {H K : Subgr
oup G} (h_le : H ≤ K), (Subgroup.inclusion h_le).range = H.subgroupOf K
-/
theorem relIndex_subgroupOf (hKL : K ≤ L) :
    (H.subgroupOf L).relIndex (K.subgroupOf L) = H.relIndex K :=
  ((index_comap (H.subgroupOf L) (inclusion hKL)).trans (congr_arg _ (inclusion_range hKL))).symm

variable (H K L)

@[to_additive relIndex_mul_relIndex]
/-
**Subgroup.relIndex_mul_relIndex** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：relIndex_mul_relIndex (hHK : H <= K) (hKL : K <= L) : H.relIndex K * K.rel
Index L = H.relIndex L
参数：hHK : H <= K；hKL : K <= L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.relIndex_subgroupOf`：relIndex_subgroupOf (hKL : K <= L) : (H.su
bgroupOf L).relIndex (K.subgroupOf L) = H.relIndex K
· 使用定理 `Subgroup.relIndex_mul_index`：relIndex_mul_index (h : H <= K) : H.relInde
x K * K.index = H.index
-/
theorem relIndex_mul_relIndex (hHK : H ≤ K) (hKL : K ≤ L) :
    H.relIndex K * K.relIndex L = H.relIndex L := by
  rw [← relIndex_subgroupOf hKL]
  exact relIndex_mul_index fun x hx => hHK hx

@[to_additive]
/-
**Subgroup.inf_relIndex_right** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：inf_relIndex_right : (H ⊓ K).relIndex K = H.relIndex K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.relIndex.eq_1`：∀ {G : Type u_1} [inst : Group G] (H K : Subgrou
p G), H.relIndex K = (H.subgroupOf K).index
· 使用定理 `Subgroup.inf_subgroupOf_right`：inf_subgroupOf_right (H K : Subgroup G) :
 (H ⊓ K).subgroupOf K = H.subgroupOf K
-/
theorem inf_relIndex_right : (H ⊓ K).relIndex K = H.relIndex K := by
  rw [relIndex, relIndex, inf_subgroupOf_right]

@[to_additive]
/-
**Subgroup.inf_relIndex_left** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：inf_relIndex_left : (H ⊓ K).relIndex H = K.relIndex H
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `Subgroup.inf_relIndex_right`：inf_relIndex_right : (H ⊓ K).relIndex K = H
.relIndex K
-/
theorem inf_relIndex_left : (H ⊓ K).relIndex H = K.relIndex H := by
  rw [inf_comm, inf_relIndex_right]

@[to_additive relIndex_inf_mul_relIndex]
/-
**Subgroup.relIndex_inf_mul_relIndex** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：relIndex_inf_mul_relIndex : H.relIndex (K ⊓ L) * K.relIndex L = (H ⊓ K).re
lIndex L
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.inf_relIndex_right`：inf_relIndex_right : (H ⊓ K).relIndex K = H
.relIndex K
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)
· 使用定理 `Subgroup.relIndex_mul_relIndex`：relIndex_mul_relIndex (hHK : H <= K) (hK
L : K <= L) : H.relIndex K * K.relIndex L = H.relIndex L
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem relIndex_inf_mul_relIndex : H.relIndex (K ⊓ L) * K.relIndex L = (H ⊓ K).relIndex L := by
  rw [← inf_relIndex_right H (K ⊓ L), ← inf_relIndex_right K L, ← inf_relIndex_right (H ⊓ K) L,
    inf_assoc, relIndex_mul_relIndex (H ⊓ (K ⊓ L)) (K ⊓ L) L inf_le_right inf_le_right]

@[to_additive (attr := simp)]
/-
**Subgroup.relIndex_sup_right** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：relIndex_sup_right [K.Normal] : K.relIndex (H ⊔ K) = K.relIndex H
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Subgroup.normal_subgroupOf`：∀ {G : Type u_1} [inst : Group G] {H N : Sub
group G} [N.Normal], (N.subgroupOf H).Normal
-/
theorem relIndex_sup_right [K.Normal] : K.relIndex (H ⊔ K) = K.relIndex H :=
  Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalQuotient H K).toEquiv.symm

@[to_additive (attr := simp)]
/-
**Subgroup.relIndex_sup_left** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：relIndex_sup_left [K.Normal] : K.relIndex (K ⊔ H) = K.relIndex H
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `Subgroup.relIndex_sup_right`：relIndex_sup_right [K.Normal] : K.relIndex 
(H ⊔ K) = K.relIndex H
-/
theorem relIndex_sup_left [K.Normal] : K.relIndex (K ⊔ H) = K.relIndex H := by
  rw [sup_comm, relIndex_sup_right]

@[to_additive]
/-
**Subgroup.relIndex_dvd_index_of_normal** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：relIndex_dvd_index_of_normal [H.Normal] : H.relIndex K ∣ H.index
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.relIndex_dvd_index_of_le`：relIndex_dvd_index_of_le (h : H <= K)
 : H.relIndex K ∣ H.index
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `Subgroup.relIndex_sup_right`：relIndex_sup_right [K.Normal] : K.relIndex 
(H ⊔ K) = K.relIndex H
-/
theorem relIndex_dvd_index_of_normal [H.Normal] : H.relIndex K ∣ H.index :=
  relIndex_sup_right K H ▸ relIndex_dvd_index_of_le le_sup_right

variable {H K}

@[to_additive]
/-
**Subgroup.relIndex_dvd_of_le_left** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：relIndex_dvd_of_le_left (hHK : H <= K) : K.relIndex L ∣ H.relIndex L
参数：hHK : H <= K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_of_mul_left_eq`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b : α} 
(c : α), c * a = b → a ∣ b
· 使用定理 `Subgroup.relIndex_inf_mul_relIndex`：relIndex_inf_mul_relIndex : H.relInd
ex (K ⊓ L) * K.relIndex L = (H ⊓ K).relIndex L
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
-/
theorem relIndex_dvd_of_le_left (hHK : H ≤ K) : K.relIndex L ∣ H.relIndex L :=
  inf_of_le_left hHK ▸ dvd_of_mul_left_eq _ (relIndex_inf_mul_relIndex _ _ _)

/-- A subgroup has index two if and only if there exists `a` such that for all `b`, exactly one
of `b * a` and `b` belong to `H`. -/
@[to_additive /-- An additive subgroup has index two if and only if there exists `a` such that
for all `b`, exactly one of `b + a` and `b` belong to `H`. -/]
/-
**Subgroup.index_eq_two_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：index_eq_two_iff : H.index = 2 ↔ exists a, forall b, Xor (b * a in H) (b i
n H)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.card_eq_two_iff'`：card_eq_two_iff' (x : α) : Nat.card α = 2 ↔ exists
! y, y != x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_mem_cancel_left`：mul_mem_cancel_left {x y : G} (h : x in H) : x * y 
in H ↔ y in H
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `inv_mem_iff`：inv_mem_iff {S G} [InvolutiveInv G] {_ : SetLike S G} [InvM
emClass S G] {H : S} {x : G} : x⁻¹ in H ↔ x in H
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
-/
theorem index_eq_two_iff : H.index = 2 ↔ ∃ a, ∀ b, Xor (b * a ∈ H) (b ∈ H) := by
  simp only [index, Nat.card_eq_two_iff' ((1 : G) : G ⧸ H), ExistsUnique, inv_mem_iff,
    QuotientGroup.exists_mk, QuotientGroup.forall_mk, Ne, QuotientGroup.eq, mul_one,
    xor_iff_iff_not]
  refine exists_congr fun a =>
    ⟨fun ha b => ⟨fun hba hb => ?_, fun hb => ?_⟩, fun ha => ⟨?_, fun b hb => ?_⟩⟩
  · exact ha.1 ((mul_mem_cancel_left hb).1 hba)
  · exact inv_inv b ▸ ha.2 _ (mt (inv_mem_iff (x := b)).1 hb)
  · rw [← inv_mem_iff (x := a), ← ha, inv_mul_cancel]
    exact one_mem _
  · rwa [ha, inv_mem_iff (x := b)]

/-- A subgroup has index two if and only if there exists `a` such that for all `b`, exactly one
of `a * b` and `b` belong to `H`. -/
@[to_additive /-- An additive subgroup has index two if and only if there exists `a` such that
for all `b`, exactly one of `a + b` and `b` belong to `H`. -/]
/-
**Subgroup.index_eq_two_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：index_eq_two_iff' : H.index = 2 ↔ exists a, forall b, Xor (a * b in H) (b 
in H)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.index_eq_two_iff`：index_eq_two_iff : H.index = 2 ↔ exists a, fo
rall b, Xor (b * a in H) (b in H)
· 使用定理 `Equiv.exists_congr`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} {q : β → 
Prop} (e : α ≃ β),   (∀ (a : α), p a ↔ q (e a)) → ((∃ a, p a) ↔ ∃ b, q b)
· 使用定理 `Equiv.forall_congr`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} {q : β → 
Prop} (e : α ≃ β),   (∀ (a : α), p a ↔ q (e a)) → ((∀ (a : α), p a) ↔ ∀ (b : β),
 q b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.inv_apply`：∀ (G : Type u_14) [inst : InvolutiveInv G], ⇑(Equiv.inv
 G) = Inv.inv
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem index_eq_two_iff' : H.index = 2 ↔ ∃ a, ∀ b, Xor (a * b ∈ H) (b ∈ H) := by
  rw [index_eq_two_iff, (Equiv.inv G).exists_congr]
  refine fun a ↦ (Equiv.inv G).forall_congr fun b ↦ ?_
  simp only [Equiv.inv_apply, inv_mem_iff, ← mul_inv_rev]

/-- A subgroup `H` has index two if and only if there exists `a ∉ H` such that for all `b`, one
of `b * a` and `b` belongs to `H`. -/
@[to_additive /-- An additive subgroup `H` has index two if and only if there exists `a ∉ H` such
that for all `b`, one of `b + a` and `b` belongs to `H`. -/]
/-
**Subgroup.index_eq_two_iff_exists_notMem_and** 是 Mathlib 中的一个引理，位于命名空间 `Subgrou
p`。
形式化陈述：index_eq_two_iff_exists_notMem_and : H.index = 2 ↔ exists a, a ∉ H ∧ foral
l b, (b * a in H) ∨ (b in H)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
-/
lemma index_eq_two_iff_exists_notMem_and :
    H.index = 2 ↔ ∃ a, a ∉ H ∧ ∀ b, (b * a ∈ H) ∨ (b ∈ H) := by
  simp only [index_eq_two_iff, xor_iff_or_and_not_and]
  exact exists_congr fun a ↦ ⟨fun h ↦ ⟨fun ha ↦ ((h a)).2 ⟨mul_mem ha ha, ha⟩, fun b ↦ (h b).1⟩,
    fun h b ↦ ⟨h.2 b, fun h' ↦ h.1 (by simpa using mul_mem (inv_mem h'.2) h'.1)⟩⟩

/-- A subgroup `H` has index two if and only if there exists `a ∉ H` such that for all `b`, one
of `a * b` and `b` belongs to `H`. -/
@[to_additive /-- An additive subgroup has index two if and only if there exists `a ∉ H` such that
for all `b`, one of `a + b` and `b` belongs to `H`. -/]
/-
**Subgroup.index_eq_two_iff_exists_notMem_and'** 是 Mathlib 中的一个引理，位于命名空间 `Subgro
up`。
形式化陈述：index_eq_two_iff_exists_notMem_and' : H.index = 2 ↔ exists a, a ∉ H ∧ fora
ll b, (a * b in H) ∨ (b in H)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
· 使用定理 `InvMemClass.inv_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Inv G} {inst_1 : SetLike S G} [self : InvMemClass S G] {s : S}   {x : G}, x ∈ s 
→ x⁻¹ ∈ s
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
-/
lemma index_eq_two_iff_exists_notMem_and' :
    H.index = 2 ↔ ∃ a, a ∉ H ∧ ∀ b, (a * b ∈ H) ∨ (b ∈ H) := by
  simp only [index_eq_two_iff', xor_iff_or_and_not_and]
  exact exists_congr fun a ↦ ⟨fun h ↦ ⟨fun ha ↦ ((h a)).2 ⟨mul_mem ha ha, ha⟩, fun b ↦ (h b).1⟩,
    fun h b ↦ ⟨h.2 b, fun h' ↦ h.1 (by simpa using mul_mem h'.1 (inv_mem h'.2))⟩⟩

/-- Relative version of `Subgroup.index_eq_two_iff`. -/
@[to_additive /-- Relative version of `AddSubgroup.index_eq_two_iff`. -/]
/-
**Subgroup.relIndex_eq_two_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：relIndex_eq_two_iff : H.relIndex K = 2 ↔ exists a in K, forall b in K, Xor
 (b * a in H) (b in H)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Relative version of `Subgroup.index_eq_two_iff`.
-/
theorem relIndex_eq_two_iff : H.relIndex K = 2 ↔ ∃ a ∈ K, ∀ b ∈ K, Xor (b * a ∈ H) (b ∈ H) := by
  simp [Subgroup.relIndex, Subgroup.index_eq_two_iff, mem_subgroupOf]

/-- Relative version of `Subgroup.index_eq_two_iff'`. -/
@[to_additive /-- Relative version of `AddSubgroup.index_eq_two_iff'`. -/]
/-
**Subgroup.relIindex_eq_two_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：relIindex_eq_two_iff' : H.relIndex K = 2 ↔ exists a in K, forall b in K, X
or (a * b in H) (b in H)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Relative version of `Subgroup.index_eq_two_iff'`.
-/
theorem relIindex_eq_two_iff' : H.relIndex K = 2 ↔ ∃ a ∈ K, ∀ b ∈ K, Xor (a * b ∈ H) (b ∈ H) := by
  simp [Subgroup.relIndex, Subgroup.index_eq_two_iff', mem_subgroupOf]

/-- Relative version of `Subgroup.index_eq_two_iff_exists_notMem_and`. -/
@[to_additive /-- Relative version of `AddSubgroup.index_eq_two_iff_exists_notMem_and`. -/]
/-
**Subgroup.relIndex_eq_two_iff_exists_notMem_and** 是 Mathlib 中的一个引理，位于命名空间 `Subg
roup`。
形式化陈述：relIndex_eq_two_iff_exists_notMem_and : H.relIndex K = 2 ↔ exists a in K, 
a ∉ H ∧ forall b in K, (b * a in H) ∨ (b in H)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.relIndex.eq_1`：∀ {G : Type u_1} [inst : Group G] (H K : Subgrou
p G), H.relIndex K = (H.subgroupOf K).index
· 使用引理 `Subgroup.index_eq_two_iff_exists_notMem_and`：index_eq_two_iff_exists_not
Mem_and : H.index = 2 ↔ exists a, a ∉ H ∧ forall b, (b * a in H) ∨ (b in H)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Relative version of `Subgroup.index_eq_two_iff_exists_notMem_and`.
-/
lemma relIndex_eq_two_iff_exists_notMem_and :
    H.relIndex K = 2 ↔ ∃ a ∈ K, a ∉ H ∧ ∀ b ∈ K, (b * a ∈ H) ∨ (b ∈ H) := by
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff_exists_notMem_and]
  simp only [mem_subgroupOf, coe_mul, Subtype.forall, Subtype.exists, exists_and_left, exists_prop]
  refine exists_congr fun g ↦ ?_
  simp only [and_left_comm]

/-- Relative version of `Subgroup.index_eq_two_iff_exists_notMem_and'`. -/
@[to_additive /-- Relative version of `AddSubgroup.index_eq_two_iff_exists_notMem_and'`. -/]
/-
**Subgroup.relIndex_eq_two_iff_exists_notMem_and'** 是 Mathlib 中的一个引理，位于命名空间 `Sub
group`。
形式化陈述：relIndex_eq_two_iff_exists_notMem_and' : H.relIndex K = 2 ↔ exists a in K,
 a ∉ H ∧ forall b in K, (a * b in H) ∨ (b in H)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.relIndex.eq_1`：∀ {G : Type u_1} [inst : Group G] (H K : Subgrou
p G), H.relIndex K = (H.subgroupOf K).index
· 使用引理 `Subgroup.index_eq_two_iff_exists_notMem_and'`：index_eq_two_iff_exists_no
tMem_and' : H.index = 2 ↔ exists a, a ∉ H ∧ forall b, (a * b in H) ∨ (b in H)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Relative version of `Subgroup.index_eq_two_iff_exists_notMem_and'`.
-/
lemma relIndex_eq_two_iff_exists_notMem_and' :
    H.relIndex K = 2 ↔ ∃ a ∈ K, a ∉ H ∧ ∀ b ∈ K, (a * b ∈ H) ∨ (b ∈ H) := by
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff_exists_notMem_and']
  simp only [mem_subgroupOf, coe_mul, Subtype.forall, Subtype.exists, exists_and_left, exists_prop]
  refine exists_congr fun g ↦ ?_
  simp only [and_left_comm]

@[to_additive]
/-
**Subgroup.mul_mem_iff_of_index_two** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mul_mem_iff_of_index_two (h : H.index = 2) {a b : G} : a * b in H ↔ (a in 
H ↔ b in H)
参数：h : H.index = 2。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_mem_cancel_left`：mul_mem_cancel_left {x y : G} (h : x in H) : x * y 
in H ↔ y in H
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `mul_mem_cancel_right`：mul_mem_cancel_right {x y : G} (h : x in H) : y * 
x in H ↔ y in H
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.index_eq_two_iff`：index_eq_two_iff : H.index = 2 ↔ exists a, fo
rall b, Xor (b * a in H) (b in H)
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Xor.or`：∀ {a b : Prop}, Xor a b → a ∨ b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
-/
theorem mul_mem_iff_of_index_two (h : H.index = 2) {a b : G} : a * b ∈ H ↔ (a ∈ H ↔ b ∈ H) := by
  by_cases ha : a ∈ H; · simp only [ha, true_iff, mul_mem_cancel_left ha]
  by_cases hb : b ∈ H; · simp only [hb, iff_true, mul_mem_cancel_right hb]
  simp only [ha, hb, iff_true]
  rcases index_eq_two_iff.1 h with ⟨c, hc⟩
  refine (hc _).or.resolve_left ?_
  rwa [mul_assoc, mul_mem_cancel_right ((hc _).or.resolve_right hb)]

@[to_additive]
/-
**Subgroup.mul_self_mem_of_index_two** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mul_self_mem_of_index_two (h : H.index = 2) (a : G) : a * a in H
参数：h : H.index = 2；a : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.mul_mem_iff_of_index_two`：mul_mem_iff_of_index_two (h : H.index
 = 2) {a b : G} : a * b in H ↔ (a in H ↔ b in H)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mul_self_mem_of_index_two (h : H.index = 2) (a : G) : a * a ∈ H := by
  rw [mul_mem_iff_of_index_two h]

@[to_additive two_smul_mem_of_index_two]
/-
**Subgroup.sq_mem_of_index_two** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：sq_mem_of_index_two (h : H.index = 2) (a : G) : a ^ 2 in H
参数：h : H.index = 2；a : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.mul_self_mem_of_index_two`：mul_self_mem_of_index_two (h : H.ind
ex = 2) (a : G) : a * a in H
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
-/
theorem sq_mem_of_index_two (h : H.index = 2) (a : G) : a ^ 2 ∈ H :=
  (pow_two a).symm ▸ mul_self_mem_of_index_two h a

variable (H K) {f : G →* G'}

@[to_additive (attr := simp)]
/-
**Subgroup.index_top** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：index_top : (⊤ : Subgroup G).index = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.card_eq_one_iff_unique`：card_eq_one_iff_unique : Nat.card α = 1 ↔ Su
bsingleton α ∧ Nonempty α
· 使用定理 `QuotientGroup.subsingleton_quotient_top`：subsingleton_quotient_top : Sub
singleton (G ⧸ (⊤ : Subgroup G))
-/
theorem index_top : (⊤ : Subgroup G).index = 1 :=
  Nat.card_eq_one_iff_unique.mpr ⟨QuotientGroup.subsingleton_quotient_top, ⟨1⟩⟩

@[to_additive (attr := simp)]
/-
**Subgroup.index_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：index_bot : (⊥ : Subgroup G).index = Nat.card G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
-/
theorem index_bot : (⊥ : Subgroup G).index = Nat.card G :=
  Nat.card_congr QuotientGroup.quotientBot.toEquiv

@[to_additive (attr := simp)]
/-
**Subgroup.relIndex_top_left** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：relIndex_top_left : (⊤ : Subgroup G).relIndex H = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.index_top`：index_top : (⊤ : Subgroup G).index = 1
-/
theorem relIndex_top_left : (⊤ : Subgroup G).relIndex H = 1 :=
  index_top

@[to_additive (attr := simp)]
/-
**Subgroup.relIndex_top_right** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：relIndex_top_right : H.relIndex ⊤ = H.index
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.relIndex_mul_index`：relIndex_mul_index (h : H <= K) : H.relInde
x K * K.index = H.index
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Subgroup.index_top`：index_top : (⊤ : Subgroup G).index = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem relIndex_top_right : H.relIndex ⊤ = H.index := by
  rw [← relIndex_mul_index (show H ≤ ⊤ from le_top), index_top, mul_one]

@[to_additive (attr := simp)]
/-
**Subgroup.relIndex_bot_left** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：relIndex_bot_left : (⊥ : Subgroup G).relIndex H = Nat.card H
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.relIndex.eq_1`：∀ {G : Type u_1} [inst : Group G] (H K : Subgrou
p G), H.relIndex K = (H.subgroupOf K).index
· 使用定理 `Subgroup.bot_subgroupOf`：bot_subgroupOf : (⊥ : Subgroup G).subgroupOf H 
= ⊥
· 使用定理 `Subgroup.index_bot`：index_bot : (⊥ : Subgroup G).index = Nat.card G
-/
theorem relIndex_bot_left : (⊥ : Subgroup G).relIndex H = Nat.card H := by
  rw [relIndex, bot_subgroupOf, index_bot]

@[to_additive (attr := simp)]
/-
**Subgroup.relIndex_bot_right** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：relIndex_bot_right : H.relIndex ⊥ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.relIndex.eq_1`：∀ {G : Type u_1} [inst : Group G] (H K : Subgrou
p G), H.relIndex K = (H.subgroupOf K).index
· 使用定理 `Subgroup.subgroupOf_bot_eq_top`：subgroupOf_bot_eq_top : H.subgroupOf ⊥ =
 ⊤
· 使用定理 `Subgroup.index_top`：index_top : (⊤ : Subgroup G).index = 1
-/
theorem relIndex_bot_right : H.relIndex ⊥ = 1 := by rw [relIndex, subgroupOf_bot_eq_top, index_top]

@[to_additive (attr := simp)]
/-
**Subgroup.relIndex_self** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：relIndex_self : H.relIndex H = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.relIndex.eq_1`：∀ {G : Type u_1} [inst : Group G] (H K : Subgrou
p G), H.relIndex K = (H.subgroupOf K).index
· 使用定理 `Subgroup.subgroupOf_self`：subgroupOf_self : H.subgroupOf H = ⊤
· 使用定理 `Subgroup.index_top`：index_top : (⊤ : Subgroup G).index = 1
-/
theorem relIndex_self : H.relIndex H = 1 := by rw [relIndex, subgroupOf_self, index_top]

@[to_additive]
/-
**Subgroup.index_ker** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：index_ker (f : G ->* G') : f.ker.index = Nat.card f.range
参数：f : G ->* G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.comap_bot`：comap_bot (f : G ->* N) : (⊥ : Subgroup N).comap f 
= f.ker
· 使用定理 `Subgroup.index_comap`：index_comap (f : G' ->* G) : (H.comap f).index = H
.relIndex f.range
· 使用定理 `Subgroup.relIndex_bot_left`：relIndex_bot_left : (⊥ : Subgroup G).relInde
x H = Nat.card H
-/
theorem index_ker (f : G →* G') : f.ker.index = Nat.card f.range := by
  rw [← MonoidHom.comap_bot, index_comap, relIndex_bot_left]

@[to_additive]
/-
**Subgroup.relIndex_ker** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：relIndex_ker (f : G ->* G') : f.ker.relIndex K = Nat.card (K.map f)
参数：f : G ->* G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.comap_bot`：comap_bot (f : G ->* N) : (⊥ : Subgroup N).comap f 
= f.ker
· 使用定理 `Subgroup.relIndex_comap`：relIndex_comap (f : G' ->* G) (K : Subgroup G')
 : relIndex (comap f H) K = relIndex H (map f K)
· 使用定理 `Subgroup.relIndex_bot_left`：relIndex_bot_left : (⊥ : Subgroup G).relInde
x H = Nat.card H
-/
theorem relIndex_ker (f : G →* G') : f.ker.relIndex K = Nat.card (K.map f) := by
  rw [← MonoidHom.comap_bot, relIndex_comap, relIndex_bot_left]

@[to_additive (attr := simp) card_mul_index]
/-
**Subgroup.card_mul_index** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：card_mul_index : Nat.card H * H.index = Nat.card G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.relIndex_bot_left`：relIndex_bot_left : (⊥ : Subgroup G).relInde
x H = Nat.card H
· 使用定理 `Subgroup.index_bot`：index_bot : (⊥ : Subgroup G).index = Nat.card G
· 使用定理 `Subgroup.relIndex_mul_index`：relIndex_mul_index (h : H <= K) : H.relInde
x K * K.index = H.index
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem card_mul_index : Nat.card H * H.index = Nat.card G := by
  rw [← relIndex_bot_left, ← index_bot]
  exact relIndex_mul_index bot_le

@[to_additive]
/-
**Subgroup.card_dvd_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：card_dvd_of_surjective (f : G ->* G') (hf : Function.Surjective f) : Nat.c
ard G' ∣ Nat.card G
参数：f : G ->* G'；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `MonoidHom.normal_ker`：∀ {G : Type u_1} [inst : Group G] {M : Type u_7} [
inst_1 : MulOneClass M] (f : G →* M), f.ker.Normal
· 使用定理 `Dvd.intro_left`：Dvd.intro_left (c : α) (h : c * a = b) : a ∣ b
· 使用定理 `Subgroup.card_mul_index`：card_mul_index : Nat.card H * H.index = Nat.car
d G
-/
theorem card_dvd_of_surjective (f : G →* G') (hf : Function.Surjective f) :
    Nat.card G' ∣ Nat.card G := by
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
  exact Dvd.intro_left (Nat.card f.ker) f.ker.card_mul_index

@[to_additive]
/-
**Subgroup.card_range_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：card_range_dvd (f : G ->* G') : Nat.card f.range ∣ Nat.card G
参数：f : G ->* G'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.card_dvd_of_surjective`：card_dvd_of_surjective (f : G ->* G') (
hf : Function.Surjective f) : Nat.card G' ∣ Nat.card G
· 使用定理 `MonoidHom.rangeRestrict_surjective`：rangeRestrict_surjective (f : G ->* 
N) : Function.Surjective f.rangeRestrict
-/
theorem card_range_dvd (f : G →* G') : Nat.card f.range ∣ Nat.card G :=
  card_dvd_of_surjective f.rangeRestrict f.rangeRestrict_surjective

@[to_additive]
/-
**Subgroup.card_map_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：card_map_dvd (f : G ->* G') : Nat.card (H.map f) ∣ Nat.card H
参数：f : G ->* G'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.card_dvd_of_surjective`：card_dvd_of_surjective (f : G ->* G') (
hf : Function.Surjective f) : Nat.card G' ∣ Nat.card G
· 使用定理 `MonoidHom.subgroupMap_surjective`：subgroupMap_surjective (f : G ->* G') 
(H : Subgroup G) : Function.Surjective (f.subgroupMap H)
-/
theorem card_map_dvd (f : G →* G') : Nat.card (H.map f) ∣ Nat.card H :=
  card_dvd_of_surjective (f.subgroupMap H) (f.subgroupMap_surjective H)

@[to_additive]
/-
**Subgroup.index_map** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：index_map (f : G ->* G') : (H.map f).index = (H ⊔ f.ker).index * f.range.i
ndex
参数：f : G ->* G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.comap_map_eq`：comap_map_eq (H : Subgroup G) : comap f (map f H)
 = H ⊔ f.ker
· 使用定理 `Subgroup.index_comap`：index_comap (f : G' ->* G) : (H.comap f).index = H
.relIndex f.range
· 使用定理 `Subgroup.relIndex_mul_index`：relIndex_mul_index (h : H <= K) : H.relInde
x K * K.index = H.index
· 使用定理 `Subgroup.map_le_range`：map_le_range (H : Subgroup G) : map f H <= f.rang
e
-/
theorem index_map (f : G →* G') :
    (H.map f).index = (H ⊔ f.ker).index * f.range.index := by
  rw [← comap_map_eq, index_comap, relIndex_mul_index (H.map_le_range f)]

@[to_additive]
/-
**Subgroup.index_map_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：index_map_dvd {f : G ->* G'} (hf : Function.Surjective f) : (H.map f).inde
x ∣ H.index
参数：hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.index_map`：index_map (f : G ->* G') : (H.map f).index = (H ⊔ f.
ker).index * f.range.index
· 使用定理 `MonoidHom.range_eq_top_of_surjective`：range_eq_top_of_surjective {N} [Gr
oup N] (f : G ->* N) (hf : Function.Surjective f) : f.range = (⊤ : Subgroup N)
· 使用定理 `Subgroup.index_top`：index_top : (⊤ : Subgroup G).index = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Subgroup.index_dvd_of_le`：index_dvd_of_le (h : H <= K) : K.index ∣ H.ind
ex
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
theorem index_map_dvd {f : G →* G'} (hf : Function.Surjective f) :
    (H.map f).index ∣ H.index := by
  rw [index_map, f.range_eq_top_of_surjective hf, index_top, mul_one]
  exact index_dvd_of_le le_sup_left

@[to_additive]
/-
**Subgroup.dvd_index_map** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：dvd_index_map {f : G ->* G'} (hf : f.ker <= H) : H.index ∣ (H.map f).index
参数：hf : f.ker <= H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.index_map`：index_map (f : G ->* G') : (H.map f).index = (H ⊔ f.
ker).index * f.range.index
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
-/
theorem dvd_index_map {f : G →* G'} (hf : f.ker ≤ H) :
    H.index ∣ (H.map f).index := by
  rw [index_map, sup_of_le_left hf]
  apply dvd_mul_right

@[to_additive]
/-
**Subgroup.index_map_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：index_map_eq (hf1 : Surjective f) (hf2 : f.ker <= H) : (H.map f).index = H
.index
参数：hf1 : Surjective f；hf2 : f.ker <= H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.dvd_antisymm`：∀ {m n : ℕ}, m ∣ n → n ∣ m → m = n
· 使用定理 `Subgroup.index_map_dvd`：index_map_dvd {f : G ->* G'} (hf : Function.Surj
ective f) : (H.map f).index ∣ H.index
· 使用定理 `Subgroup.dvd_index_map`：dvd_index_map {f : G ->* G'} (hf : f.ker <= H) :
 H.index ∣ (H.map f).index
-/
theorem index_map_eq (hf1 : Surjective f) (hf2 : f.ker ≤ H) : (H.map f).index = H.index :=
  Nat.dvd_antisymm (H.index_map_dvd hf1) (H.dvd_index_map hf2)

@[to_additive]
/-
**Subgroup.index_map_of_bijective** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：index_map_of_bijective (hf : Bijective f) (H : Subgroup G) : (H.map f).ind
ex = H.index
参数：hf : Bijective f；H : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.index_map_eq`：index_map_eq (hf1 : Surjective f) (hf2 : f.ker <=
 H) : (H.map f).index = H.index
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.ker_eq_bot`：ker_eq_bot (f : G ->* M) (hf : Function.Injective 
f) : f.ker = ⊥
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
lemma index_map_of_bijective (hf : Bijective f) (H : Subgroup G) : (H.map f).index = H.index :=
  index_map_eq _ hf.2 (by rw [f.ker_eq_bot hf.1]; exact bot_le)

@[to_additive (attr := simp)]
/-
**Subgroup.index_map_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：index_map_equiv (e : G ≃* G') : (map (e : G ->* G') H).index = H.index
参数：e : G ≃* G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.index_map_of_bijective`：index_map_of_bijective (hf : Bijective 
f) (H : Subgroup G) : (H.map f).index = H.index
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `MulEquiv.bijective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst
_1 : Mul N] (e : M ≃* N), Function.Bijective ⇑e
-/
theorem index_map_equiv (e : G ≃* G') : (map (e : G →* G') H).index = H.index :=
  index_map_of_bijective e.bijective H

@[to_additive]
/-
**Subgroup.index_map_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：index_map_of_injective {f : G ->* G'} (hf : Function.Injective f) : (H.map
 f).index = H.index * f.range.index
参数：hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.index_map`：index_map (f : G ->* G') : (H.map f).index = (H ⊔ f.
ker).index * f.range.index
· 使用定理 `MonoidHom.ker_eq_bot`：ker_eq_bot (f : G ->* M) (hf : Function.Injective 
f) : f.ker = ⊥
· 使用定理 `sup_bot_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), a ⊔ ⊥ = a
-/
theorem index_map_of_injective {f : G →* G'} (hf : Function.Injective f) :
    (H.map f).index = H.index * f.range.index := by
  rw [H.index_map, f.ker_eq_bot hf, sup_bot_eq]

@[to_additive]
/-
**Subgroup.index_map_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：index_map_subtype {H : Subgroup G} (K : Subgroup H) : (K.map H.subtype).in
dex = K.index * H.index
参数：K : Subgroup H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.index_map_of_injective`：index_map_of_injective {f : G ->* G'} (
hf : Function.Injective f) : (H.map f).index = H.index * f.range.index
· 使用引理 `Subgroup.subtype_injective`：subtype_injective (s : Subgroup G) : Functio
n.Injective s.subtype
· 使用定理 `Subgroup.range_subtype`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup 
G), H.subtype.range = H
-/
theorem index_map_subtype {H : Subgroup G} (K : Subgroup H) :
    (K.map H.subtype).index = K.index * H.index := by
  rw [K.index_map_of_injective H.subtype_injective, H.range_subtype]

@[to_additive]
/-
**Subgroup.index_eq_card** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：index_eq_card : H.index = Nat.card (G ⧸ H)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem index_eq_card : H.index = Nat.card (G ⧸ H) :=
  rfl

@[to_additive index_mul_card]
/-
**Subgroup.index_mul_card** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：index_mul_card : H.index * Nat.card H = Nat.card G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Subgroup.card_mul_index`：card_mul_index : Nat.card H * H.index = Nat.car
d G
-/
theorem index_mul_card : H.index * Nat.card H = Nat.card G := by
  rw [mul_comm, card_mul_index]

@[to_additive]
/-
**Subgroup.index_dvd_card** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：index_dvd_card : H.index ∣ Nat.card G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.index_mul_card`：index_mul_card : H.index * Nat.card H = Nat.car
d G
-/
theorem index_dvd_card : H.index ∣ Nat.card G :=
  ⟨Nat.card H, H.index_mul_card.symm⟩

@[to_additive]
/-
**Subgroup.relIndex_dvd_card** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：relIndex_dvd_card : H.relIndex K ∣ Nat.card K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.index_dvd_card`：index_dvd_card : H.index ∣ Nat.card G
-/
theorem relIndex_dvd_card : H.relIndex K ∣ Nat.card K :=
  (H.subgroupOf K).index_dvd_card

variable {H K L}

@[to_additive]
/-
**Subgroup.relIndex_eq_zero_of_le_left** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：relIndex_eq_zero_of_le_left (hHK : H <= K) (hKL : K.relIndex L = 0) : H.re
lIndex L = 0
参数：hHK : H <= K；hKL : K.relIndex L = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_of_zero_dvd`：eq_zero_of_zero_dvd (h : 0 ∣ a) : a = 0
· 使用定理 `Subgroup.relIndex_dvd_of_le_left`：relIndex_dvd_of_le_left (hHK : H <= K)
 : K.relIndex L ∣ H.relIndex L
-/
theorem relIndex_eq_zero_of_le_left (hHK : H ≤ K) (hKL : K.relIndex L = 0) : H.relIndex L = 0 :=
  eq_zero_of_zero_dvd (hKL ▸ relIndex_dvd_of_le_left L hHK)

@[to_additive]
/-
**Subgroup.relIndex_eq_zero_of_le_right** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：relIndex_eq_zero_of_le_right (hKL : K <= L) (hHK : H.relIndex K = 0) : H.r
elIndex L = 0
参数：hKL : K <= L；hHK : H.relIndex K = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.card_eq_zero_of_embedding`：card_eq_zero_of_embedding [Nonempty α]
 (f : α ↪ β) (h : Nat.card α = 0) : Nat.card β = 0
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem relIndex_eq_zero_of_le_right (hKL : K ≤ L) (hHK : H.relIndex K = 0) : H.relIndex L = 0 :=
  Finite.card_eq_zero_of_embedding (quotientSubgroupOfEmbeddingOfLE H hKL) hHK

/-- If `J` has finite index in `K`, then the same holds for their comaps under any group hom. -/
@[to_additive /-- If `J` has finite index in `K`, then the same holds for their comaps under any
additive group hom. -/]
/-
**Subgroup.relIndex_comap_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：relIndex_comap_ne_zero (f : G ->* G') {J K : Subgroup G'} (hJK : J.relInde
x K != 0) : (J.comap f).relIndex (K.comap f) != 0
参数：f : G ->* G'；hJK : J.relIndex K != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.relIndex_comap`：relIndex_comap (f : G' ->* G) (K : Subgroup G')
 : relIndex (comap f H) K = relIndex H (map f K)
· 使用定理 `Subgroup.relIndex_eq_zero_of_le_right`：relIndex_eq_zero_of_le_right (hKL
 : K <= L) (hHK : H.relIndex K = 0) : H.relIndex L = 0
· 使用定理 `Subgroup.map_comap_le`：map_comap_le (H : Subgroup N) : map f (comap f H)
 <= H
-/
lemma relIndex_comap_ne_zero (f : G →* G') {J K : Subgroup G'} (hJK : J.relIndex K ≠ 0) :
    (J.comap f).relIndex (K.comap f) ≠ 0 := by
  rw [relIndex_comap]
  exact fun h ↦ hJK <| relIndex_eq_zero_of_le_right (map_comap_le _ _) h

@[to_additive]
/-
**Subgroup.index_eq_zero_of_relIndex_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup
`。
形式化陈述：index_eq_zero_of_relIndex_eq_zero (h : H.relIndex K = 0) : H.index = 0
参数：h : H.relIndex K = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.relIndex_top_right`：relIndex_top_right : H.relIndex ⊤ = H.index
· 使用定理 `Subgroup.relIndex_eq_zero_of_le_right`：relIndex_eq_zero_of_le_right (hKL
 : K <= L) (hHK : H.relIndex K = 0) : H.relIndex L = 0
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem index_eq_zero_of_relIndex_eq_zero (h : H.relIndex K = 0) : H.index = 0 :=
  H.relIndex_top_right.symm.trans (relIndex_eq_zero_of_le_right le_top h)

@[to_additive]
/-
**Subgroup.relIndex_le_of_le_left** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：relIndex_le_of_le_left (hHK : H <= K) (hHL : H.relIndex L != 0) : K.relInd
ex L <= H.relIndex L
参数：hHK : H <= K；hHL : H.relIndex L != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Subgroup.relIndex_dvd_of_le_left`：relIndex_dvd_of_le_left (hHK : H <= K)
 : K.relIndex L ∣ H.relIndex L
-/
theorem relIndex_le_of_le_left (hHK : H ≤ K) (hHL : H.relIndex L ≠ 0) :
    K.relIndex L ≤ H.relIndex L :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hHL) (relIndex_dvd_of_le_left L hHK)

@[to_additive]
/-
**Subgroup.relIndex_le_of_le_right** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：relIndex_le_of_le_right (hKL : K <= L) (hHL : H.relIndex L != 0) : H.relIn
dex K <= H.relIndex L
参数：hKL : K <= L；hHL : H.relIndex L != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.card_le_of_embedding'`：card_le_of_embedding' (f : α ↪ β) (h : Nat
.card β = 0 -> Nat.card α = 0) : Nat.card α <= Nat.card β
-/
theorem relIndex_le_of_le_right (hKL : K ≤ L) (hHL : H.relIndex L ≠ 0) :
    H.relIndex K ≤ H.relIndex L :=
  Finite.card_le_of_embedding' (quotientSubgroupOfEmbeddingOfLE H hKL) fun h => (hHL h).elim

@[to_additive]
/-
**Subgroup.relIndex_ne_zero_trans** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：relIndex_ne_zero_trans (hHK : H.relIndex K != 0) (hKL : K.relIndex L != 0)
 : H.relIndex L != 0
参数：hHK : H.relIndex K != 0；hKL : K.relIndex L != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Nat.instIsDomain`：IsDomain ℕ
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Subgroup.relIndex_eq_zero_of_le_right`：relIndex_eq_zero_of_le_right (hKL
 : K <= L) (hHK : H.relIndex K = 0) : H.relIndex L = 0
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subgroup.relIndex_inf_mul_relIndex`：relIndex_inf_mul_relIndex : H.relInd
ex (K ⊓ L) * K.relIndex L = (H ⊓ K).relIndex L
· 使用定理 `Subgroup.relIndex_eq_zero_of_le_left`：relIndex_eq_zero_of_le_left (hHK :
 H <= K) (hKL : K.relIndex L = 0) : H.relIndex L = 0
-/
theorem relIndex_ne_zero_trans (hHK : H.relIndex K ≠ 0) (hKL : K.relIndex L ≠ 0) :
    H.relIndex L ≠ 0 := fun h =>
  mul_ne_zero (mt (relIndex_eq_zero_of_le_right (show K ⊓ L ≤ K from inf_le_left)) hHK) hKL
    ((relIndex_inf_mul_relIndex H K L).trans (relIndex_eq_zero_of_le_left inf_le_left h))

@[to_additive]
/-
**Subgroup.relIndex_inf_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：relIndex_inf_ne_zero (hH : H.relIndex L != 0) (hK : K.relIndex L != 0) : (
H ⊓ K).relIndex L != 0
参数：hH : H.relIndex L != 0；hK : K.relIndex L != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Subgroup.relIndex_eq_zero_of_le_right`：relIndex_eq_zero_of_le_right (hKL
 : K <= L) (hHK : H.relIndex K = 0) : H.relIndex L = 0
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.inf_relIndex_right`：inf_relIndex_right : (H ⊓ K).relIndex K = H
.relIndex K
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)
· 使用定理 `Subgroup.relIndex_ne_zero_trans`：relIndex_ne_zero_trans (hHK : H.relInde
x K != 0) (hKL : K.relIndex L != 0) : H.relIndex L != 0
-/
theorem relIndex_inf_ne_zero (hH : H.relIndex L ≠ 0) (hK : K.relIndex L ≠ 0) :
    (H ⊓ K).relIndex L ≠ 0 := by
  replace hH : H.relIndex (K ⊓ L) ≠ 0 := mt (relIndex_eq_zero_of_le_right inf_le_right) hH
  rw [← inf_relIndex_right] at hH hK ⊢
  rw [inf_assoc]
  exact relIndex_ne_zero_trans hH hK

@[to_additive]
/-
**Subgroup.index_inf_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：index_inf_ne_zero (hH : H.index != 0) (hK : K.index != 0) : (H ⊓ K).index 
!= 0
参数：hH : H.index != 0；hK : K.index != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.relIndex_top_right`：relIndex_top_right : H.relIndex ⊤ = H.index
· 使用定理 `Subgroup.relIndex_inf_ne_zero`：relIndex_inf_ne_zero (hH : H.relIndex L !
= 0) (hK : K.relIndex L != 0) : (H ⊓ K).relIndex L != 0
-/
theorem index_inf_ne_zero (hH : H.index ≠ 0) (hK : K.index ≠ 0) : (H ⊓ K).index ≠ 0 := by
  rw [← relIndex_top_right] at hH hK ⊢
  exact relIndex_inf_ne_zero hH hK

/-- If `J` has finite index in `K`, then `J ⊓ L` has finite index in `K ⊓ L` for any `L`. -/
@[to_additive /-- If `J` has finite index in `K`, then `J ⊓ L` has finite index in `K ⊓ L` for any
`L`. -/]
/-
**Subgroup.relIndex_inter_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：relIndex_inter_ne_zero {J K : Subgroup G} (hJK : J.relIndex K != 0) (L : S
ubgroup G) : (J ⊓ L).relIndex (K ⊓ L) != 0
参数：hJK : J.relIndex K != 0；L : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.range_subtype`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup 
G), H.subtype.range = H
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `Subgroup.map_comap_eq`：map_comap_eq (H : Subgroup N) : map f (comap f H)
 = f.range ⊓ H
· 使用定理 `Subgroup.relIndex_comap`：relIndex_comap (f : G' ->* G) (K : Subgroup G')
 : relIndex (comap f H) K = relIndex H (map f K)
· 使用定理 `Subgroup.comap_map_eq_self_of_injective`：comap_map_eq_self_of_injective 
{f : G ->* N} (h : Function.Injective f) (H : Subgroup G) : comap f (map f H) = 
H
· 使用引理 `Subgroup.subtype_injective`：subtype_injective (s : Subgroup G) : Functio
n.Injective s.subtype
· 使用引理 `Subgroup.relIndex_comap_ne_zero`：relIndex_comap_ne_zero (f : G ->* G') {
J K : Subgroup G'} (hJK : J.relIndex K != 0) : (J.comap f).relIndex (K.comap f) 
!= 0
-/
lemma relIndex_inter_ne_zero {J K : Subgroup G} (hJK : J.relIndex K ≠ 0) (L : Subgroup G) :
    (J ⊓ L).relIndex (K ⊓ L) ≠ 0 := by
  rw [← range_subtype L, inf_comm, ← map_comap_eq, inf_comm, ← map_comap_eq, ← relIndex_comap,
    comap_map_eq_self_of_injective (subtype_injective L)]
  exact relIndex_comap_ne_zero _ hJK

@[to_additive]
/-
**Subgroup.relIndex_inf_le** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：relIndex_inf_le : (H ⊓ K).relIndex L <= H.relIndex L * K.relIndex L
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.relIndex_eq_zero_of_le_left`：relIndex_eq_zero_of_le_left (hHK :
 H <= K) (hKL : K.relIndex L = 0) : H.relIndex L = 0
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.inf_relIndex_right`：inf_relIndex_right : (H ⊓ K).relIndex K = H
.relIndex K
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)
· 使用定理 `Subgroup.relIndex_mul_relIndex`：relIndex_mul_relIndex (hHK : H <= K) (hK
L : K <= L) : H.relIndex K * K.relIndex L = H.relIndex L
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `Subgroup.relIndex_le_of_le_right`：relIndex_le_of_le_right (hKL : K <= L)
 (hHL : H.relIndex L != 0) : H.relIndex K <= H.relIndex L
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem relIndex_inf_le : (H ⊓ K).relIndex L ≤ H.relIndex L * K.relIndex L := by
  by_cases h : H.relIndex L = 0
  · simp [relIndex_eq_zero_of_le_left inf_le_left h]
  rw [← inf_relIndex_right, inf_assoc, ← relIndex_mul_relIndex _ _ L inf_le_right inf_le_right,
    inf_relIndex_right, inf_relIndex_right]
  grw [relIndex_le_of_le_right inf_le_right h]

@[to_additive]
/-
**Subgroup.index_inf_le** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：index_inf_le : (H ⊓ K).index <= H.index * K.index
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem index_inf_le : (H ⊓ K).index ≤ H.index * K.index := by
  simp_rw [← relIndex_top_right, relIndex_inf_le]

@[to_additive]
/-
**Subgroup.relIndex_iInf_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：relIndex_iInf_ne_zero {ι : Type*} [_hι : Finite ι] {f : ι -> Subgroup G} (
hf : forall i, (f i).relIndex L != 0) : (⨅ i, f i).relIndex L != 0
参数：hf : forall i, (f i).relIndex L != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.prod_ne_zero_iff`：prod_ne_zero_iff : ∏ x in s, f x != 0 ↔ forall 
a in s, f a != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Nat.instIsDomain`：IsDomain ℕ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_pi`：card_pi {β : α -> Type*} [Fintype α] : Nat.card (forall a, 
β a) = ∏ a, Nat.card (β a)
· 使用定理 `Finite.card_eq_zero_of_embedding`：card_eq_zero_of_embedding [Nonempty α]
 (f : α ↪ β) (h : Nat.card α = 0) : Nat.card β = 0
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem relIndex_iInf_ne_zero {ι : Type*} [_hι : Finite ι] {f : ι → Subgroup G}
    (hf : ∀ i, (f i).relIndex L ≠ 0) : (⨅ i, f i).relIndex L ≠ 0 :=
  haveI := Fintype.ofFinite ι
  (Finset.prod_ne_zero_iff.mpr fun i _hi => hf i) ∘
    Nat.card_pi.symm.trans ∘
      Finite.card_eq_zero_of_embedding (quotientiInfSubgroupOfEmbedding f L)

@[to_additive]
/-
**Subgroup.relIndex_iInf_le** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：relIndex_iInf_le {ι : Type*} [Fintype ι] (f : ι -> Subgroup G) : (⨅ i, f i
).relIndex L <= ∏ i, (f i).relIndex L
参数：f : ι -> Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_le_of_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Finite.card_le_of_embedding'`：card_le_of_embedding' (f : α ↪ β) (h : Nat
.card β = 0 -> Nat.card α = 0) : Nat.card α <= Nat.card β
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Finset.prod_eq_zero_iff`：prod_eq_zero_iff : ∏ x in s, f x = 0 ↔ exists a
 in s, f a = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Nat.instIsDomain`：IsDomain ℕ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_pi`：card_pi {β : α -> Type*} [Fintype α] : Nat.card (forall a, 
β a) = ∏ a, Nat.card (β a)
· 使用定理 `Subgroup.relIndex_eq_zero_of_le_left`：relIndex_eq_zero_of_le_left (hHK :
 H <= K) (hKL : K.relIndex L = 0) : H.relIndex L = 0
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
-/
theorem relIndex_iInf_le {ι : Type*} [Fintype ι] (f : ι → Subgroup G) :
    (⨅ i, f i).relIndex L ≤ ∏ i, (f i).relIndex L :=
  le_of_le_of_eq
    (Finite.card_le_of_embedding' (quotientiInfSubgroupOfEmbedding f L) fun h =>
      let ⟨i, _hi, h⟩ := Finset.prod_eq_zero_iff.mp (Nat.card_pi.symm.trans h)
      relIndex_eq_zero_of_le_left (iInf_le f i) h)
    Nat.card_pi

@[to_additive]
/-
**Subgroup.index_iInf_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：index_iInf_ne_zero {ι : Type*} [Finite ι] {f : ι -> Subgroup G} (hf : fora
ll i, (f i).index != 0) : (⨅ i, f i).index != 0
参数：hf : forall i, (f i).index != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.relIndex_iInf_ne_zero`：relIndex_iInf_ne_zero {ι : Type*} [_hι :
 Finite ι] {f : ι -> Subgroup G} (hf : forall i, (f i).relIndex L != 0) : (⨅ i, 
f i).relIndex L != 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem index_iInf_ne_zero {ι : Type*} [Finite ι] {f : ι → Subgroup G}
    (hf : ∀ i, (f i).index ≠ 0) : (⨅ i, f i).index ≠ 0 := by
  simp_rw [← relIndex_top_right] at hf ⊢
  exact relIndex_iInf_ne_zero hf

@[to_additive]
/-
**Subgroup.index_iInf_le** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：index_iInf_le {ι : Type*} [Fintype ι] (f : ι -> Subgroup G) : (⨅ i, f i).i
ndex <= ∏ i, (f i).index
参数：f : ι -> Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem index_iInf_le {ι : Type*} [Fintype ι] (f : ι → Subgroup G) :
    (⨅ i, f i).index ≤ ∏ i, (f i).index := by simp_rw [← relIndex_top_right, relIndex_iInf_le]

@[to_additive (attr := simp) index_eq_one]
/-
**Subgroup.index_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：index_eq_one : H.index = 1 ↔ H = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientGroup.subgroup_eq_top_of_subsingleton`：subgroup_eq_top_of_subsin
gleton (H : Subgroup G) (h : Subsingleton (G ⧸ H)) : H = ⊤
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.card_eq_one_iff_unique`：card_eq_one_iff_unique : Nat.card α = 1 ↔ Su
bsingleton α ∧ Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Subgroup.index_top`：index_top : (⊤ : Subgroup G).index = 1
-/
theorem index_eq_one : H.index = 1 ↔ H = ⊤ :=
  ⟨fun h =>
    QuotientGroup.subgroup_eq_top_of_subsingleton H (Nat.card_eq_one_iff_unique.mp h).1,
    fun h => (congr_arg index h).trans index_top⟩

@[to_additive (attr := simp) relIndex_eq_one]
/-
**Subgroup.relIndex_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：relIndex_eq_one : H.relIndex K = 1 ↔ K <= H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Subgroup.index_eq_one`：index_eq_one : H.index = 1 ↔ H = ⊤
· 使用定理 `Subgroup.subgroupOf_eq_top`：subgroupOf_eq_top {H K : Subgroup G} : H.sub
groupOf K = ⊤ ↔ K <= H
-/
theorem relIndex_eq_one : H.relIndex K = 1 ↔ K ≤ H :=
  index_eq_one.trans subgroupOf_eq_top

@[to_additive (attr := simp) card_eq_one]
/-
**Subgroup.card_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：card_eq_one : Nat.card H = 1 ↔ H = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Subgroup.relIndex_eq_one`：relIndex_eq_one : H.relIndex K = 1 ↔ K <= H
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `Subgroup.relIndex_bot_left`：relIndex_bot_left : (⊥ : Subgroup G).relInde
x H = Nat.card H
-/
theorem card_eq_one : Nat.card H = 1 ↔ H = ⊥ :=
  H.relIndex_bot_left ▸ relIndex_eq_one.trans le_bot_iff

/-- A subgroup has index dividing 2 if and only if there exists `a` such that for all `b`, at least
one of `b * a` and `b` belongs to `H`. -/
@[to_additive /-- An additive subgroup has index dividing 2 if and only if there exists `a` such
that for all `b`, at least one of `b + a` and `b` belongs to `H`. -/]
/-
**Subgroup.index_dvd_two_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：index_dvd_two_iff : H.index ∣ 2 ↔ exists a, forall b, (b * a in H) ∨ (b in
 H) where mp hH
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.le_succ_iff`：∀ {m n : ℕ}, m ≤ n.succ ↔ m ≤ n ∨ m = n.succ
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `two_pos`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialO
rder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_assoc`：∀ {a b c : Prop}, (a ∨ b) ∨ c ↔ a ∨ b ∨ c
· 使用定理 `Nat.le_one_iff_eq_zero_or_eq_one`：∀ {n : ℕ}, n ≤ 1 ↔ n = 0 ∨ n = 1
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.zero_dvd`：∀ {n : ℕ}, 0 ∣ n ↔ n = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subgroup.index_eq_one`：index_eq_one : H.index = 1 ↔ H = ⊤
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `Subgroup.index_eq_two_iff`：index_eq_two_iff : H.index = 2 ↔ exists a, fo
rall b, Xor (b * a in H) (b in H)
· 使用定理 `Xor.or`：∀ {a b : Prop}, Xor a b → a ∨ b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
（共 42 条，此处仅展示前 30 条）
-/
theorem index_dvd_two_iff : H.index ∣ 2 ↔ ∃ a, ∀ b, (b * a ∈ H) ∨ (b ∈ H) where
  mp hH := by
    obtain (hH | hH) : H.index = 1 ∨ H.index = 2 := by
      -- This is just showing that 2 is prime, but we do it "longhand" to avoid making any
      -- dependence on number theory files.
      have := Nat.le_succ_iff.mp (Nat.le_of_dvd two_pos hH)
      rw [Nat.le_one_iff_eq_zero_or_eq_one, or_assoc] at this
      exact this.resolve_left fun h ↦ (two_ne_zero <| Nat.zero_dvd.mp (h ▸ hH)).elim
    · simp [index_eq_one.mp hH]
    · exact match index_eq_two_iff.mp hH with | ⟨a, ha⟩ => ⟨a, fun b ↦ (ha b).or⟩
  mpr := by
    rintro ⟨a, ha⟩
    by_cases ha' : a ∈ H
    · suffices ∀ b, b ∈ H by simp [(eq_top_iff' _).mpr this]
      exact fun b ↦ (ha b).elim (fun h ↦ by simpa using mul_mem h (inv_mem ha')) id
    · refine dvd_of_eq (index_eq_two_iff.mpr
        ⟨a, fun b ↦ (xor_iff_or_and_not_and _ _).mpr ⟨ha b, fun h ↦ ha' ?_⟩⟩)
      simpa using mul_mem (inv_mem h.2) h.1

/-- A subgroup has index dividing 2 if and only if there exists `a` such that for all `b`, at least
one of `a * b` and `b` belongs to `H`. -/
@[to_additive /-- An additive subgroup has index dividing 2 if and only if there exists `a` such
that for all `b`, at least one of `a + b` and `b` belongs to `H`. -/]
/-
**Subgroup.index_dvd_two_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：index_dvd_two_iff' : H.index ∣ 2 ↔ exists a, forall b, (a * b in H) ∨ (b i
n H)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.index_dvd_two_iff`：index_dvd_two_iff : H.index ∣ 2 ↔ exists a, 
forall b, (b * a in H) ∨ (b in H) where mp hH
· 使用定理 `Equiv.exists_congr`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} {q : β → 
Prop} (e : α ≃ β),   (∀ (a : α), p a ↔ q (e a)) → ((∃ a, p a) ↔ ∃ b, q b)
· 使用定理 `Equiv.forall_congr`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} {q : β → 
Prop} (e : α ≃ β),   (∀ (a : α), p a ↔ q (e a)) → ((∀ (a : α), p a) ↔ ∀ (b : β),
 q b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.inv_apply`：∀ (G : Type u_14) [inst : InvolutiveInv G], ⇑(Equiv.inv
 G) = Inv.inv
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem index_dvd_two_iff' : H.index ∣ 2 ↔ ∃ a, ∀ b, (a * b ∈ H) ∨ (b ∈ H) := by
  rw [index_dvd_two_iff, (Equiv.inv G).exists_congr]
  refine fun a ↦ (Equiv.inv G).forall_congr fun b ↦ ?_
  simp only [Equiv.inv_apply, inv_mem_iff, ← mul_inv_rev]

/-- Relative version of `Subgroup.index_dvd_two_iff`. -/
@[to_additive /-- Relative version of `AddSubgroup.index_dvd_two_iff`. -/]
/-
**Subgroup.relIndex_dvd_two_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：relIndex_dvd_two_iff : H.relIndex K ∣ 2 ↔ exists a in K, forall b in K, (b
 * a in H) ∨ (b in H)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Relative version of `Subgroup.index_dvd_two_iff`.
-/
theorem relIndex_dvd_two_iff : H.relIndex K ∣ 2 ↔ ∃ a ∈ K, ∀ b ∈ K, (b * a ∈ H) ∨ (b ∈ H) := by
  simp [Subgroup.relIndex, Subgroup.index_dvd_two_iff, mem_subgroupOf]

/-- Relative version of `Subgroup.index_dvd_two_iff'`. -/
@[to_additive /-- Relative version of `AddSubgroup.index_dvd_two_iff'`. -/]
/-
**Subgroup.relIindex_dvd_two_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：relIindex_dvd_two_iff' : H.relIndex K ∣ 2 ↔ exists a in K, forall b in K, 
(a * b in H) ∨ (b in H)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Relative version of `Subgroup.index_dvd_two_iff'`.
-/
theorem relIindex_dvd_two_iff' : H.relIndex K ∣ 2 ↔ ∃ a ∈ K, ∀ b ∈ K, (a * b ∈ H) ∨ (b ∈ H) := by
  simp [Subgroup.relIndex, Subgroup.index_dvd_two_iff', mem_subgroupOf]

@[to_additive]
/-
**Subgroup.disjoint_of_coprime_natCard** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：disjoint_of_coprime_natCard (h : Nat.card H |>.Coprime <| Nat.card K) : Di
sjoint H K
参数：h : Nat.card H |>.Coprime <| Nat.card K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.card_eq_one`：card_eq_one : Nat.card H = 1 ↔ H = ⊥
· 使用定理 `Nat.eq_one_of_dvd_coprimes`：eq_one_of_dvd_coprimes {a b k : Nat} (h_ab_c
oprime : Coprime a b) (hka : k ∣ a) (hkb : k ∣ b) : k = 1
· 使用定理 `Subgroup.card_dvd_of_le`：card_dvd_of_le {H K : Subgroup α} (hHK : H <= K
) : Nat.card H ∣ Nat.card K
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
lemma disjoint_of_coprime_natCard (h : Nat.card H |>.Coprime <| Nat.card K) : Disjoint H K :=
  disjoint_iff.mpr <| card_eq_one.mp <| Nat.eq_one_of_dvd_coprimes h
    (card_dvd_of_le inf_le_left) (card_dvd_of_le inf_le_right)

@[to_additive (attr := deprecated disjoint_of_coprime_natCard (since := "2026-05-28"))]
/-
**Subgroup.inf_eq_bot_of_coprime** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：inf_eq_bot_of_coprime (h : Nat.Coprime (Nat.card H) (Nat.card K)) : H ⊓ K 
= ⊥
参数：h : Nat.Coprime (Nat.card H) (Nat.card K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用引理 `Subgroup.disjoint_of_coprime_natCard`：disjoint_of_coprime_natCard (h : N
at.card H |>.Coprime <| Nat.card K) : Disjoint H K
-/
lemma inf_eq_bot_of_coprime (h : Nat.Coprime (Nat.card H) (Nat.card K)) : H ⊓ K = ⊥ :=
  disjoint_iff.mp <| disjoint_of_coprime_natCard h

@[to_additive]
/-
**Subgroup.index_ne_zero_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：index_ne_zero_of_finite [hH : Finite (G ⧸ H)] : H.index != 0
参数：G ⧸ H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.index_eq_card`：index_eq_card : H.index = Nat.card (G ⧸ H)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.card_pos`：∀ {α : Type u_1} [Nonempty α] [Finite α], 0 < Nat.card α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem index_ne_zero_of_finite [hH : Finite (G ⧸ H)] : H.index ≠ 0 := by
  cases nonempty_fintype (G ⧸ H)
  rw [index_eq_card]
  exact Nat.card_pos.ne'

/-- Finite index implies finite quotient. -/
@[to_additive (attr := instance_reducible) /-- Finite index implies finite quotient. -/]
/-
**Subgroup.fintypeOfIndexNeZero** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：fintypeOfIndexNeZero (hH : H.index != 0) : Fintype (G ⧸ H)
参数：hH : H.index != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Finite index implies finite quotient.
-/
noncomputable def fintypeOfIndexNeZero (hH : H.index ≠ 0) : Fintype (G ⧸ H) :=
  @Fintype.ofFinite _ (Nat.finite_of_card_ne_zero hH)

@[to_additive]
/-
**Subgroup.index_eq_zero_iff_infinite** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：index_eq_zero_iff_infinite : H.index = 0 ↔ Infinite (G ⧸ H)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma index_eq_zero_iff_infinite : H.index = 0 ↔ Infinite (G ⧸ H) := by
  simp [index_eq_card, Nat.card_eq_zero]

@[to_additive]
/-
**Subgroup.index_ne_zero_iff_finite** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：index_ne_zero_iff_finite : H.index != 0 ↔ Finite (G ⧸ H)
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
lemma index_ne_zero_iff_finite : H.index ≠ 0 ↔ Finite (G ⧸ H) := by
  simp [index_eq_zero_iff_infinite]

@[to_additive one_lt_index_of_ne_top]
/-
**Subgroup.one_lt_index_of_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：one_lt_index_of_ne_top [Finite (G ⧸ H)] (hH : H != ⊤) : 1 < H.index
参数：G ⧸ H；hH : H != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_lt_iff_ne_zero_and_ne_one`：∀ {n : ℕ}, 1 < n ↔ n ≠ 0 ∧ n ≠ 1
· 使用定理 `Subgroup.index_ne_zero_of_finite`：index_ne_zero_of_finite [hH : Finite (
G ⧸ H)] : H.index != 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.index_eq_one`：index_eq_one : H.index = 1 ↔ H = ⊤
-/
theorem one_lt_index_of_ne_top [Finite (G ⧸ H)] (hH : H ≠ ⊤) : 1 < H.index :=
  Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨index_ne_zero_of_finite, mt index_eq_one.mp hH⟩

@[to_additive]
/-
**Subgroup.finite_quotient_of_finite_quotient_of_index_ne_zero** 是 Mathlib 中的一个引
理，位于命名空间 `Subgroup`。
形式化陈述：finite_quotient_of_finite_quotient_of_index_ne_zero {X : Type*} [MulAction
 G X] [Finite <| MulAction.orbitRel.Quotient G X] (hi : H.index != 0) : Finite M
ulAction.orbitRel.Quotient H X
参数：hi : H.index != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
lemma finite_quotient_of_finite_quotient_of_index_ne_zero {X : Type*} [MulAction G X]
    [Finite <| MulAction.orbitRel.Quotient G X] (hi : H.index ≠ 0) :
    Finite <| MulAction.orbitRel.Quotient H X := by
  have := fintypeOfIndexNeZero hi
  exact MulAction.finite_quotient_of_finite_quotient_of_finite_quotient

@[to_additive]
/-
**Subgroup.finite_quotient_of_pretransitive_of_index_ne_zero** 是 Mathlib 中的一个引理，
位于命名空间 `Subgroup`。
形式化陈述：finite_quotient_of_pretransitive_of_index_ne_zero {X : Type*} [MulAction G
 X] [MulAction.IsPretransitive G X] (hi : H.index != 0) : Finite MulAction.orbit
Rel.Quotient H X
参数：hi : H.index != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MulAction.pretransitive_iff_subsingleton_quotient`：pretransitive_iff_sub
singleton_quotient : IsPretransitive G α ↔ Subsingleton (orbitRel.Quotient G α)
· 使用引理 `Subgroup.finite_quotient_of_finite_quotient_of_index_ne_zero`：finite_quo
tient_of_finite_quotient_of_index_ne_zero {X : Type*} [MulAction G X] [Finite <|
 MulAction.orbitRel.Quotient G X] (hi : H.index !=…
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
-/
lemma finite_quotient_of_pretransitive_of_index_ne_zero {X : Type*} [MulAction G X]
    [MulAction.IsPretransitive G X] (hi : H.index ≠ 0) :
    Finite <| MulAction.orbitRel.Quotient H X := by
  have := (MulAction.pretransitive_iff_subsingleton_quotient G X).1 inferInstance
  exact finite_quotient_of_finite_quotient_of_index_ne_zero hi

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/-
**Subgroup.exists_pow_mem_of_index_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：exists_pow_mem_of_index_ne_zero (h : H.index != 0) (a : G) : exists n, 0 <
 n ∧ n <= H.index ∧ a ^ n in H
参数：h : H.index != 0；a : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Fintype.finite`：∀ {α : Type u_4} (_inst : Fintype α), Finite α
· 使用引理 `Nat.card_le_card_of_injective`：card_le_card_of_injective {α : Type u} {β
 : Type v} [Finite β] (f : α -> β) (hf : Injective f) : Nat.card α <= Nat.card β
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_ofFinset`：card_ofFinset {p : Set α} (s : Finset α) (H : for
all x, x in s ↔ x in p) : @Fintype.card p (ofFinset s H) = #s
· 使用定理 `Nat.card_Icc`：∀ (a b : ℕ), (Finset.Icc a b).card = b + 1 - a
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `zpow_add`：zpow_add (a : G) (m n : Int) : a ^ (m + n) = a ^ m * a ^ n
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
（共 32 条，此处仅展示前 30 条）
-/
lemma exists_pow_mem_of_index_ne_zero (h : H.index ≠ 0) (a : G) :
    ∃ n, 0 < n ∧ n ≤ H.index ∧ a ^ n ∈ H := by
  suffices ∃ n₁ n₂, n₁ < n₂ ∧ n₂ ≤ H.index ∧ ((a ^ n₂ : G) : G ⧸ H) = ((a ^ n₁ : G) : G ⧸ H) by
    rcases this with ⟨n₁, n₂, hlt, hle, he⟩
    refine ⟨n₂ - n₁, by lia, by lia, ?_⟩
    rw [eq_comm, QuotientGroup.eq, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add,
        add_comm] at he
    rw [← zpow_natCast]
    convert! he
    lia
  suffices ∃ n₁ n₂, n₁ ≠ n₂ ∧ n₁ ≤ H.index ∧ n₂ ≤ H.index ∧
      ((a ^ n₂ : G) : G ⧸ H) = ((a ^ n₁ : G) : G ⧸ H) by
    rcases this with ⟨n₁, n₂, hne, hle₁, hle₂, he⟩
    rcases hne.lt_or_gt with hlt | hlt
    · exact ⟨n₁, n₂, hlt, hle₂, he⟩
    · exact ⟨n₂, n₁, hlt, hle₁, he.symm⟩
  by_contra hc
  simp_rw [not_exists] at hc
  let f : (Set.Icc 0 H.index) → G ⧸ H := fun n ↦ (a ^ (n : ℕ) : G)
  have hf : Function.Injective f := by
    rintro ⟨n₁, h₁, hle₁⟩ ⟨n₂, h₂, hle₂⟩ he
    have hc' := hc n₁ n₂
    dsimp only [f] at he
    simpa [hle₁, hle₂, he] using hc'
  have := (fintypeOfIndexNeZero h).finite
  have hcard := Nat.card_le_card_of_injective f hf
  simp [← index_eq_card] at hcard

@[to_additive]
/-
**Subgroup.exists_pow_mem_of_relIndex_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Subgrou
p`。
形式化陈述：exists_pow_mem_of_relIndex_ne_zero (h : H.relIndex K != 0) {a : G} (ha : a
 in K) : exists n, 0 < n ∧ n <= H.relIndex K ∧ a ^ n in H ⊓ K
参数：h : H.relIndex K != 0；ha : a in K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.exists_pow_mem_of_index_ne_zero`：exists_pow_mem_of_index_ne_zer
o (h : H.index != 0) (a : G) : exists n, 0 < n ∧ n <= H.index ∧ a ^ n in H
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `pow_mem`：∀ {M : Type u_3} {A : Type u_4} [inst : Monoid M] [inst_1 : Set
Like A M] [SubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), x ^ n ∈ …
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma exists_pow_mem_of_relIndex_ne_zero (h : H.relIndex K ≠ 0) {a : G} (ha : a ∈ K) :
    ∃ n, 0 < n ∧ n ≤ H.relIndex K ∧ a ^ n ∈ H ⊓ K := by
  rcases exists_pow_mem_of_index_ne_zero h ⟨a, ha⟩ with ⟨n, hlt, hle, he⟩
  refine ⟨n, hlt, hle, ?_⟩
  simpa [pow_mem ha, mem_subgroupOf] using he

@[to_additive]
/-
**Subgroup.pow_mem_of_index_ne_zero_of_dvd** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：pow_mem_of_index_ne_zero_of_dvd (h : H.index != 0) (a : G) {n : Nat} (hn :
 forall m, 0 < m -> m <= H.index -> m ∣ n) : a ^ n in H
参数：h : H.index != 0；a : G；hn : forall m, 0 < m -> m <= H.index -> m ∣ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.exists_pow_mem_of_index_ne_zero`：exists_pow_mem_of_index_ne_zer
o (h : H.index != 0) (a : G) : exists n, 0 < n ∧ n <= H.index ∧ a ^ n in H
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `pow_mem`：∀ {M : Type u_3} {A : Type u_4} [inst : Monoid M] [inst_1 : Set
Like A M] [SubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), x ^ n ∈ …
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma pow_mem_of_index_ne_zero_of_dvd (h : H.index ≠ 0) (a : G) {n : ℕ}
    (hn : ∀ m, 0 < m → m ≤ H.index → m ∣ n) : a ^ n ∈ H := by
  rcases exists_pow_mem_of_index_ne_zero h a with ⟨m, hlt, hle, he⟩
  rcases hn m hlt hle with ⟨k, rfl⟩
  rw [pow_mul]
  exact pow_mem he _

@[to_additive]
/-
**Subgroup.pow_mem_of_relIndex_ne_zero_of_dvd** 是 Mathlib 中的一个引理，位于命名空间 `Subgrou
p`。
形式化陈述：pow_mem_of_relIndex_ne_zero_of_dvd (h : H.relIndex K != 0) {a : G} (ha : a
 in K) {n : Nat} (hn : forall m, 0 < m -> m <= H.relIndex K -> m ∣ n) : a ^ n in
 H ⊓ K
参数：h : H.relIndex K != 0；ha : a in K；hn : forall m, 0 < m -> m <= H.relIndex K -
> m ∣ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `pow_mem`：∀ {M : Type u_3} {A : Type u_4} [inst : Monoid M] [inst_1 : Set
Like A M] [SubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), x ^ n ∈ …
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `Subgroup.pow_mem_of_index_ne_zero_of_dvd`：pow_mem_of_index_ne_zero_of_dv
d (h : H.index != 0) (a : G) {n : Nat} (hn : forall m, 0 < m -> m <= H.index -> 
m ∣ n) : a ^ n in H
-/
lemma pow_mem_of_relIndex_ne_zero_of_dvd (h : H.relIndex K ≠ 0) {a : G} (ha : a ∈ K) {n : ℕ}
    (hn : ∀ m, 0 < m → m ≤ H.relIndex K → m ∣ n) : a ^ n ∈ H ⊓ K := by
  convert! pow_mem_of_index_ne_zero_of_dvd h ⟨a, ha⟩ hn
  simp [pow_mem ha, mem_subgroupOf]

@[to_additive (attr := simp) index_prod]
/-
**Subgroup.index_prod** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：index_prod (H : Subgroup G) (K : Subgroup G') : (H.prod K).index = H.index
 * K.index
参数：H : Subgroup G；K : Subgroup G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
-/
lemma index_prod (H : Subgroup G) (K : Subgroup G') : (H.prod K).index = H.index * K.index := by
  simp_rw [index, ← Nat.card_prod]
  exact Nat.card_congr (QuotientGroup.prodEquiv H K)

@[to_additive (attr := simp)]
/-
**Subgroup.index_pi** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：index_pi {ι : Type*} [Fintype ι] (H : ι -> Subgroup G) : (Subgroup.pi Set.
univ H).index = ∏ i, (H i).index
参数：H : ι -> Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用引理 `QuotientGroup.leftRel_pi`：leftRel_pi {ι : Type*} {β : ι -> Type*} [foral
l i, Group (β i)] (s' : forall i, Subgroup (β i)) : leftRel (Subgroup.pi Set.uni
v s') = @piSet…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma index_pi {ι : Type*} [Fintype ι] (H : ι → Subgroup G) :
    (Subgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  simp_rw [index, ← Nat.card_pi]
  refine Nat.card_congr
    ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

@[simp]
/-
**Subgroup.index_toAddSubgroup** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：index_toAddSubgroup : (Subgroup.toAddSubgroup H).index = H.index
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma index_toAddSubgroup : (Subgroup.toAddSubgroup H).index = H.index :=
  rfl

@[simp]
/-
**Subgroup._root_.AddSubgroup.index_toSubgroup** 是 Mathlib 中的一个引理，位于命名空间 `Subgro
up`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.AddSubgroup.index_toSubgroup {G : Type*} [AddGroup G] (H : AddSubgroup G) :
    (AddSubgroup.toSubgroup H).index = H.index :=
  rfl

@[simp]
/-
**Subgroup.relIndex_toAddSubgroup** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：relIndex_toAddSubgroup : (Subgroup.toAddSubgroup H).relIndex (Subgroup.toA
ddSubgroup K) = H.relIndex K
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma relIndex_toAddSubgroup :
    (Subgroup.toAddSubgroup H).relIndex (Subgroup.toAddSubgroup K) = H.relIndex K :=
  rfl

@[simp]
/-
**Subgroup._root_.AddSubgroup.relIndex_toSubgroup** 是 Mathlib 中的一个引理，位于命名空间 `Sub
group`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.AddSubgroup.relIndex_toSubgroup {G : Type*} [AddGroup G] (H K : AddSubgroup G) :
    (AddSubgroup.toSubgroup H).relIndex (AddSubgroup.toSubgroup K) = H.relIndex K :=
  rfl

section FiniteIndex

/-- Typeclass for finite index subgroups. -/
/-
**Subgroup._root_.AddSubgroup.FiniteIndex** 是 Mathlib 中的一个类，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for finite index subgroups.
-/
class _root_.AddSubgroup.FiniteIndex {G : Type*} [AddGroup G] (H : AddSubgroup G) : Prop where
  /-- The additive subgroup has finite index;
  recall that `AddSubgroup.index` returns 0 when the index is infinite. -/
  index_ne_zero : H.index ≠ 0

variable (H) in
/-- Typeclass for finite index subgroups. -/
/-
**Subgroup.FiniteIndex** 是 Mathlib 中的一个归纳类型，位于命名空间 `Subgroup`。
形式化陈述：{G : Type u_1} → [inst : Group G] → Subgroup G → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for finite index subgroups.
-/
@[to_additive] class FiniteIndex : Prop where
  /-- The subgroup has finite index;
  recall that `Subgroup.index` returns 0 when the index is infinite. -/
  index_ne_zero : H.index ≠ 0

/-- Typeclass for a subgroup `H` to have finite index in a subgroup `K`. -/
/-
**Subgroup._root_.AddSubgroup.IsFiniteRelIndex** 是 Mathlib 中的一个类，位于命名空间 `Subgrou
p`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for a subgroup `H` to have finite index in a subgroup `K`.
-/
class _root_.AddSubgroup.IsFiniteRelIndex {G : Type*} [AddGroup G] (H K : AddSubgroup G) :
    Prop where
  protected relIndex_ne_zero : H.relIndex K ≠ 0

variable (H K) in
/-- Typeclass for a subgroup `H` to have finite index in a subgroup `K`. -/
/-
**Subgroup.IsFiniteRelIndex** 是 Mathlib 中的一个归纳类型，位于命名空间 `Subgroup`。
形式化陈述：{G : Type u_1} → [inst : Group G] → Subgroup G → Subgroup G → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for a subgroup `H` to have finite index in a subgroup `K`.
-/
@[to_additive] class IsFiniteRelIndex : Prop where
  protected relIndex_ne_zero : H.relIndex K ≠ 0
/-
**Subgroup.relIndex_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {H K : Subgroup G} [H.IsFiniteRelIndex K
], H.relIndex K ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.IsFiniteRelIndex.relIndex_ne_zero`：∀ {G : Type u_1} {inst : Gro
up G} {H K : Subgroup G} [self : H.IsFiniteRelIndex K], H.relIndex K ≠ 0
-/
@[to_additive] lemma relIndex_ne_zero [H.IsFiniteRelIndex K] : H.relIndex K ≠ 0 :=
  IsFiniteRelIndex.relIndex_ne_zero

@[to_additive]
/-
**Subgroup.IsFiniteRelIndex.to_finiteIndex_subgroupOf** 是 Mathlib 中的一个定理，位于命名空间 
`Subgroup.IsFiniteRelIndex`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {H K : Subgroup G} [H.IsFiniteRelIndex K
], (H.subgroupOf K).FiniteIndex
参数：H.subgroupOf K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.relIndex_ne_zero`：∀ {G : Type u_1} [inst : Group G] {H K : Subg
roup G} [H.IsFiniteRelIndex K], H.relIndex K ≠ 0
-/
instance IsFiniteRelIndex.to_finiteIndex_subgroupOf [H.IsFiniteRelIndex K] :
    (H.subgroupOf K).FiniteIndex where
  index_ne_zero := relIndex_ne_zero

@[to_additive]
/-
**Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Subg
roup`。
形式化陈述：isFiniteRelIndex_iff_relIndex_ne_zero : H.IsFiniteRelIndex K ↔ H.relIndex 
K != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.relIndex_ne_zero`：∀ {G : Type u_1} [inst : Group G] {H K : Subg
roup G} [H.IsFiniteRelIndex K], H.relIndex K ≠ 0
-/
lemma isFiniteRelIndex_iff_relIndex_ne_zero : H.IsFiniteRelIndex K ↔ H.relIndex K ≠ 0 :=
  ⟨fun _ ↦ relIndex_ne_zero, IsFiniteRelIndex.mk⟩

@[to_additive]
/-
**Subgroup.finiteIndex_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：finiteIndex_iff : H.FiniteIndex ↔ H.index != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.FiniteIndex.index_ne_zero`：∀ {G : Type u_1} {inst : Group G} {H
 : Subgroup G} [self : H.FiniteIndex], H.index ≠ 0
-/
theorem finiteIndex_iff : H.FiniteIndex ↔ H.index ≠ 0 :=
  ⟨fun h ↦ h.index_ne_zero, fun h ↦ ⟨h⟩⟩

@[to_additive]
/-
**Subgroup.isFiniteRelIndex_iff_finiteIndex** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`
。
形式化陈述：isFiniteRelIndex_iff_finiteIndex : H.IsFiniteRelIndex K ↔ (H.subgroupOf K)
.FiniteIndex
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero`：isFiniteRelIndex_iff_rel
Index_ne_zero : H.IsFiniteRelIndex K ↔ H.relIndex K != 0
· 使用定理 `Subgroup.finiteIndex_iff`：finiteIndex_iff : H.FiniteIndex ↔ H.index != 0
· 使用定理 `Subgroup.relIndex.eq_1`：∀ {G : Type u_1} [inst : Group G] (H K : Subgrou
p G), H.relIndex K = (H.subgroupOf K).index
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isFiniteRelIndex_iff_finiteIndex :
    H.IsFiniteRelIndex K ↔ (H.subgroupOf K).FiniteIndex := by
  rw [isFiniteRelIndex_iff_relIndex_ne_zero, finiteIndex_iff, relIndex]

@[to_additive]
/-
**Subgroup.not_finiteIndex_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：not_finiteIndex_iff : ¬ H.FiniteIndex ↔ H.index = 0
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
theorem not_finiteIndex_iff : ¬ H.FiniteIndex ↔ H.index = 0 := by
  simp [finiteIndex_iff]

@[simp]
/-
**Subgroup.finiteIndex_toAddSubgroup_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：finiteIndex_toAddSubgroup_iff : H.toAddSubgroup.FiniteIndex ↔ H.FiniteInde
x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem finiteIndex_toAddSubgroup_iff : H.toAddSubgroup.FiniteIndex ↔ H.FiniteIndex := by
  simp [finiteIndex_iff, AddSubgroup.finiteIndex_iff]

@[simp]
/-
**Subgroup._root_.AddSubgroup.finiteIndex_toSubgroup_iff** 是 Mathlib 中的一个定理，位于命名
空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AddSubgroup.finiteIndex_toSubgroup_iff {G : Type*} [AddGroup G] (H : AddSubgroup G) :
    H.toSubgroup.FiniteIndex ↔ H.FiniteIndex := by
  simp [finiteIndex_iff, AddSubgroup.finiteIndex_iff]

@[to_additive (attr := simp)]
/-
**Subgroup.isFiniteRelIndex_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：isFiniteRelIndex_top_iff : H.IsFiniteRelIndex ⊤ ↔ H.FiniteIndex
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.finiteIndex_iff`：finiteIndex_iff : H.FiniteIndex ↔ H.index != 0
· 使用引理 `Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero`：isFiniteRelIndex_iff_rel
Index_ne_zero : H.IsFiniteRelIndex K ↔ H.relIndex K != 0
· 使用定理 `Subgroup.relIndex_top_right`：relIndex_top_right : H.relIndex ⊤ = H.index
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isFiniteRelIndex_top_iff : H.IsFiniteRelIndex ⊤ ↔ H.FiniteIndex := by
  rw [finiteIndex_iff, isFiniteRelIndex_iff_relIndex_ne_zero, relIndex_top_right]

/-- A finite index subgroup has finite quotient. -/
@[to_additive (attr := instance_reducible) /-- A finite index subgroup has finite quotient -/]
/-
**Subgroup.fintypeQuotientOfFiniteIndex** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：fintypeQuotientOfFiniteIndex [FiniteIndex H] : Fintype (G ⧸ H)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.FiniteIndex.index_ne_zero`：∀ {G : Type u_1} {inst : Group G} {H
 : Subgroup G} [self : H.FiniteIndex], H.index ≠ 0

--- 原说明 ---
A finite index subgroup has finite quotient.
-/
noncomputable def fintypeQuotientOfFiniteIndex [FiniteIndex H] : Fintype (G ⧸ H) :=
  fintypeOfIndexNeZero FiniteIndex.index_ne_zero

@[to_additive]
/-
**Subgroup.finite_quotient_of_finiteIndex** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：finite_quotient_of_finiteIndex [FiniteIndex H] : Finite (G ⧸ H)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.finite`：∀ {α : Type u_4} (_inst : Fintype α), Finite α
-/
instance finite_quotient_of_finiteIndex [FiniteIndex H] : Finite (G ⧸ H) :=
  fintypeQuotientOfFiniteIndex.finite

@[to_additive]
/-
**Subgroup.finiteIndex_of_finite_quotient** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：finiteIndex_of_finite_quotient [Finite (G ⧸ H)] : FiniteIndex H
参数：G ⧸ H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.index_ne_zero_of_finite`：index_ne_zero_of_finite [hH : Finite (
G ⧸ H)] : H.index != 0
-/
theorem finiteIndex_of_finite_quotient [Finite (G ⧸ H)] : FiniteIndex H :=
  ⟨index_ne_zero_of_finite⟩

@[to_additive]
/-
**Subgroup.finiteIndex_iff_finite_quotient** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：finiteIndex_iff_finite_quotient : FiniteIndex H ↔ Finite (G ⧸ H)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.finiteIndex_of_finite_quotient`：finiteIndex_of_finite_quotient 
[Finite (G ⧸ H)] : FiniteIndex H
-/
theorem finiteIndex_iff_finite_quotient : FiniteIndex H ↔ Finite (G ⧸ H) :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ finiteIndex_of_finite_quotient⟩

@[to_additive]
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) finiteIndex_of_finite [Finite G] : FiniteIndex H :=
  finiteIndex_of_finite_quotient

@[to_additive]
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [FiniteIndex H] [FiniteIndex K] : FiniteIndex (H.prod K) := by
  simp_all [finiteIndex_iff]

variable (H) in
@[to_additive]
/-
**Subgroup.finite_iff_finite_and_finiteIndex** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup
`。
形式化陈述：finite_iff_finite_and_finiteIndex : Finite G ↔ Finite H ∧ H.FiniteIndex wh
ere mp _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.finiteIndex_of_finite`：∀ {G : Type u_1} [inst : Group G] {H : S
ubgroup G} [Finite G], H.FiniteIndex
· 使用定理 `Nat.finite_of_card_ne_zero`：finite_of_card_ne_zero (h : Nat.card α != 0)
 : Finite α
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Nat.instIsDomain`：IsDomain ℕ
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.card_pos`：∀ {α : Type u_1} [Nonempty α] [Finite α], 0 < Nat.card α
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `Subgroup.FiniteIndex.index_ne_zero`：∀ {G : Type u_1} {inst : Group G} {H
 : Subgroup G} [self : H.FiniteIndex], H.index ≠ 0
· 使用定理 `Subgroup.card_mul_index`：card_mul_index : Nat.card H * H.index = Nat.car
d G
-/
theorem finite_iff_finite_and_finiteIndex : Finite G ↔ Finite H ∧ H.FiniteIndex where
  mp _ := ⟨inferInstance, inferInstance⟩
  mpr := fun ⟨_, _⟩ ↦ Nat.finite_of_card_ne_zero <|
    H.card_mul_index ▸ mul_ne_zero Nat.card_pos.ne' FiniteIndex.index_ne_zero

@[to_additive]
/-
**Subgroup._root_.MonoidHom.finite_iff_finite_ker_range** 是 Mathlib 中的一个定理，位于命名空
间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MonoidHom.finite_iff_finite_ker_range (f : G →* G') :
    Finite G ↔ Finite f.ker ∧ Finite f.range := by
  rw [finite_iff_finite_and_finiteIndex f.ker, ← (QuotientGroup.quotientKerEquivRange f).finite_iff,
    finiteIndex_iff_finite_quotient]

@[to_additive]
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FiniteIndex (⊤ : Subgroup G) :=
  ⟨ne_of_eq_of_ne index_top one_ne_zero⟩

@[to_additive]
/-
**Subgroup.** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [FiniteIndex H] [FiniteIndex K] : FiniteIndex (H ⊓ K) :=
  ⟨index_inf_ne_zero FiniteIndex.index_ne_zero FiniteIndex.index_ne_zero⟩

@[to_additive]
/-
**Subgroup.finiteIndex_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：finiteIndex_iInf {ι : Type*} [Finite ι] {f : ι -> Subgroup G} (hf : forall
 i, (f i).FiniteIndex) : (⨅ i, f i).FiniteIndex
参数：hf : forall i, (f i).FiniteIndex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.index_iInf_ne_zero`：index_iInf_ne_zero {ι : Type*} [Finite ι] {
f : ι -> Subgroup G} (hf : forall i, (f i).index != 0) : (⨅ i, f i).index != 0
· 使用定理 `Subgroup.FiniteIndex.index_ne_zero`：∀ {G : Type u_1} {inst : Group G} {H
 : Subgroup G} [self : H.FiniteIndex], H.index ≠ 0
-/
theorem finiteIndex_iInf {ι : Type*} [Finite ι] {f : ι → Subgroup G}
    (hf : ∀ i, (f i).FiniteIndex) : (⨅ i, f i).FiniteIndex :=
  ⟨index_iInf_ne_zero fun i => (hf i).index_ne_zero⟩

@[to_additive]
/-
**Subgroup.finiteIndex_iInf'** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：finiteIndex_iInf' {ι : Type*} {s : Finset ι} (f : ι -> Subgroup G) (hs : f
orall i in s, (f i).FiniteIndex) : (⨅ i in s, f i).FiniteIndex
参数：f : ι -> Subgroup G；hs : forall i in s, (f i).FiniteIndex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf_subtype'`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {p : ι → Prop} {f : (i : ι) → p i → α},   ⨅ i, ⨅ (h : p i), f i h = ⨅ x, f ↑x 
⋯
· 使用定理 `Subgroup.finiteIndex_iInf`：finiteIndex_iInf {ι : Type*} [Finite ι] {f : 
ι -> Subgroup G} (hf : forall i, (f i).FiniteIndex) : (⨅ i, f i).FiniteIndex
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem finiteIndex_iInf' {ι : Type*} {s : Finset ι}
    (f : ι → Subgroup G) (hs : ∀ i ∈ s, (f i).FiniteIndex) :
    (⨅ i ∈ s, f i).FiniteIndex := by
  rw [iInf_subtype']
  exact finiteIndex_iInf fun ⟨i, hi⟩ => hs i hi

@[to_additive]
/-
**Subgroup.instFiniteIndex_subgroupOf** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：instFiniteIndex_subgroupOf (H K : Subgroup G) [H.FiniteIndex] : (H.subgrou
pOf K).FiniteIndex
参数：H K : Subgroup G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.index_ne_zero_of_finite`：index_ne_zero_of_finite [hH : Finite (
G ⧸ H)] : H.index != 0
· 使用定理 `Subgroup.index_eq_zero_of_relIndex_eq_zero`：index_eq_zero_of_relIndex_eq
_zero (h : H.relIndex K = 0) : H.index = 0
-/
instance instFiniteIndex_subgroupOf (H K : Subgroup G) [H.FiniteIndex] :
    (H.subgroupOf K).FiniteIndex :=
  ⟨fun h => H.index_ne_zero_of_finite <| H.index_eq_zero_of_relIndex_eq_zero h⟩

@[to_additive]
/-
**Subgroup.finiteIndex_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：finiteIndex_of_le [FiniteIndex H] (h : H <= K) : FiniteIndex K
参数：h : H <= K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_zero_of_dvd_ne_zero`：ne_zero_of_dvd_ne_zero {p q : α} (h₁ : q != 0) (
h₂ : p ∣ q) : p != 0
· 使用定理 `Subgroup.FiniteIndex.index_ne_zero`：∀ {G : Type u_1} {inst : Group G} {H
 : Subgroup G} [self : H.FiniteIndex], H.index ≠ 0
· 使用定理 `Subgroup.index_dvd_of_le`：index_dvd_of_le (h : H <= K) : K.index ∣ H.ind
ex
-/
theorem finiteIndex_of_le [FiniteIndex H] (h : H ≤ K) : FiniteIndex K :=
  ⟨ne_zero_of_dvd_ne_zero FiniteIndex.index_ne_zero (index_dvd_of_le h)⟩

@[to_additive]
/-
**Subgroup.isFiniteRelIndex_of_le_left** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：isFiniteRelIndex_of_le_left (L : Subgroup G) [H.IsFiniteRelIndex L] (h : H
 <= K) : K.IsFiniteRelIndex L
参数：L : Subgroup G；h : H <= K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Subgroup.isFiniteRelIndex_iff_finiteIndex`：isFiniteRelIndex_iff_finiteIn
dex : H.IsFiniteRelIndex K ↔ (H.subgroupOf K).FiniteIndex
· 使用定理 `Subgroup.finiteIndex_of_le`：finiteIndex_of_le [FiniteIndex H] (h : H <= 
K) : FiniteIndex K
· 使用引理 `Subgroup.subgroupOf_mono`：subgroupOf_mono {H₁ H₂ : Subgroup G} (H₃ : Sub
group G) (h : H₁ <= H₂) : H₁.subgroupOf H₃ <= H₂.subgroupOf H₃
-/
lemma isFiniteRelIndex_of_le_left (L : Subgroup G) [H.IsFiniteRelIndex L] (h : H ≤ K) :
    K.IsFiniteRelIndex L := by
  rw [isFiniteRelIndex_iff_finiteIndex] at *
  exact finiteIndex_of_le <| subgroupOf_mono L h

@[deprecated (since := "2026-05-09")] alias isFiniteRelIndex_of_le := isFiniteRelIndex_of_le_left
@[deprecated (since := "2026-05-09")] alias
  _root_.AddSubgroup.isFiniteRelIndex_of_le := AddSubgroup.isFiniteRelIndex_of_le_left

variable (H) in
@[to_additive]
/-
**Subgroup.isFiniteRelIndex_of_le_right** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：isFiniteRelIndex_of_le_right (h : K <= L) [H.IsFiniteRelIndex L] : H.IsFin
iteRelIndex K
参数：h : K <= L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero`：isFiniteRelIndex_iff_rel
Index_ne_zero : H.IsFiniteRelIndex K ↔ H.relIndex K != 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Subgroup.relIndex_eq_zero_of_le_right`：relIndex_eq_zero_of_le_right (hKL
 : K <= L) (hHK : H.relIndex K = 0) : H.relIndex L = 0
· 使用定理 `Subgroup.relIndex_ne_zero`：∀ {G : Type u_1} [inst : Group G] {H K : Subg
roup G} [H.IsFiniteRelIndex K], H.relIndex K ≠ 0
-/
lemma isFiniteRelIndex_of_le_right (h : K ≤ L) [H.IsFiniteRelIndex L] :
    H.IsFiniteRelIndex K := by
  rw [isFiniteRelIndex_iff_relIndex_ne_zero]
  exact mt (relIndex_eq_zero_of_le_right h) relIndex_ne_zero

@[to_additive]
/-
**Subgroup.isFiniteRelIndex_of_finiteIndex** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：isFiniteRelIndex_of_finiteIndex [h : H.FiniteIndex] : H.IsFiniteRelIndex K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subgroup.isFiniteRelIndex_of_le_right`：isFiniteRelIndex_of_le_right (h :
 K <= L) [H.IsFiniteRelIndex L] : H.IsFiniteRelIndex K
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Subgroup.isFiniteRelIndex_top_iff`：isFiniteRelIndex_top_iff : H.IsFinite
RelIndex ⊤ ↔ H.FiniteIndex
-/
lemma isFiniteRelIndex_of_finiteIndex [h : H.FiniteIndex] : H.IsFiniteRelIndex K := by
  rw [← isFiniteRelIndex_top_iff] at h
  exact isFiniteRelIndex_of_le_right _ le_top

@[to_additive (attr := gcongr)]
/-
**Subgroup.index_antitone** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：index_antitone (h : H <= K) [H.FiniteIndex] : K.index <= H.index
参数：h : H <= K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Nat.zero_lt_of_ne_zero`：∀ {a : ℕ}, a ≠ 0 → 0 < a
· 使用定理 `Subgroup.FiniteIndex.index_ne_zero`：∀ {G : Type u_1} {inst : Group G} {H
 : Subgroup G} [self : H.FiniteIndex], H.index ≠ 0
· 使用定理 `Subgroup.index_dvd_of_le`：index_dvd_of_le (h : H <= K) : K.index ∣ H.ind
ex
-/
lemma index_antitone (h : H ≤ K) [H.FiniteIndex] : K.index ≤ H.index :=
  Nat.le_of_dvd (Nat.zero_lt_of_ne_zero FiniteIndex.index_ne_zero) (index_dvd_of_le h)

@[to_additive (attr := gcongr)]
/-
**Subgroup.index_strictAnti** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
形式化陈述：index_strictAnti (h : H < K) [H.FiniteIndex] : K.index < H.index
参数：h : H < K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.FiniteIndex.index_ne_zero`：∀ {G : Type u_1} {inst : Group G} {H
 : Subgroup G} [self : H.FiniteIndex], H.index ≠ 0
· 使用定理 `Subgroup.finiteIndex_of_le`：finiteIndex_of_le [FiniteIndex H] (h : H <= 
K) : FiniteIndex K
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用引理 `Subgroup.index_antitone`：index_antitone (h : H <= K) [H.FiniteIndex] : K
.index <= H.index
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.relIndex_mul_index`：relIndex_mul_index (h : H <= K) : H.relInde
x K * K.index = H.index
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `mul_eq_right₀`：mul_eq_right₀ [IsRightCancelMulZero M₀] (hb : b != 0) : a
 * b = b ↔ a = 1
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `Subgroup.relIndex_eq_one`：relIndex_eq_one : H.relIndex K = 1 ↔ K <= H
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
lemma index_strictAnti (h : H < K) [H.FiniteIndex] : K.index < H.index := by
  have h0 : K.index ≠ 0 := (finiteIndex_of_le h.le).index_ne_zero
  apply lt_of_le_of_ne (index_antitone h.le)
  rw [← relIndex_mul_index h.le, Ne, eq_comm, mul_eq_right₀ h0, relIndex_eq_one]
  exact h.not_ge

variable (H K)

@[to_additive]
/-
**Subgroup.finiteIndex_ker** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：finiteIndex_ker {G' : Type*} [Group G'] (f : G ->* G') [Finite f.range] : 
f.ker.FiniteIndex
参数：f : G ->* G'。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.finiteIndex_of_finite_quotient`：finiteIndex_of_finite_quotient 
[Finite (G ⧸ H)] : FiniteIndex H
· 使用定理 `Finite.of_equiv`：Finite.of_equiv (α : Sort*) [h : Finite α] (f : α ≃ β) 
: Finite β
· 使用定理 `MonoidHom.normal_ker`：∀ {G : Type u_1} [inst : Group G] {M : Type u_7} [
inst_1 : MulOneClass M] (f : G →* M), f.ker.Normal
-/
instance finiteIndex_ker {G' : Type*} [Group G'] (f : G →* G') [Finite f.range] :
    f.ker.FiniteIndex :=
  @finiteIndex_of_finite_quotient G _ f.ker
    (Finite.of_equiv f.range (QuotientGroup.quotientKerEquivRange f).symm)
/-
**Subgroup.finiteIndex_normalCore** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：finiteIndex_normalCore [H.FiniteIndex] : H.normalCore.FiniteIndex
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.normalCore_eq_ker`：normalCore_eq_ker : H.normalCore = (MulActio
n.toPermHom G (G ⧸ H)).ker
-/
instance finiteIndex_normalCore [H.FiniteIndex] : H.normalCore.FiniteIndex := by
  rw [normalCore_eq_ker]
  infer_instance
/-
**Subgroup._root_.AddSubgroup.finiteIndex_normalCore** 是 Mathlib 中的一个实例，位于命名空间 `
Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.AddSubgroup.finiteIndex_normalCore {G : Type*} [AddGroup G] (H : AddSubgroup G)
    [h : H.FiniteIndex] : H.normalCore.FiniteIndex := by
  rw [← AddSubgroup.finiteIndex_toSubgroup_iff] at h ⊢
  exact H.toSubgroup.finiteIndex_normalCore

attribute [to_additive existing] finiteIndex_normalCore

@[to_additive]
/-
**Subgroup.index_range** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：index_range {f : G ->* G} [hf : f.ker.FiniteIndex] : f.range.index = Nat.c
ard f.ker
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `mul_left_inj'`：mul_left_inj' (hc : c != 0) : a * c = b * c ↔ a = b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `Subgroup.FiniteIndex.index_ne_zero`：∀ {G : Type u_1} {inst : Group G} {H
 : Subgroup G} [self : H.FiniteIndex], H.index ≠ 0
· 使用定理 `Subgroup.card_mul_index`：card_mul_index : Nat.card H * H.index = Nat.car
d G
· 使用定理 `Subgroup.index_ker`：index_ker (f : G ->* G') : f.ker.index = Nat.card f.
range
· 使用定理 `Subgroup.index_mul_card`：index_mul_card : H.index * Nat.card H = Nat.car
d G
-/
theorem index_range {f : G →* G} [hf : f.ker.FiniteIndex] :
    f.range.index = Nat.card f.ker := by
  rw [← mul_left_inj' hf.index_ne_zero, card_mul_index, index_ker, index_mul_card]

end FiniteIndex

end Subgroup

section Pointwise

open scoped Pointwise

variable {G H : Type*} [Group H] (h : H)

-- NB: `to_additive` does not work to generate the second lemma from the first here, because it
-- would need to additivize `G`, but not `H`.

set_option backward.isDefEq.respectTransparency false in
/-
**Subgroup.relIndex_pointwise_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subgroup.relIndex_pointwise_smul [Group G] [MulDistribMulAction H G] (J K 
: Subgroup G) : (h • J).relIndex (h • K) = J.relIndex K
参数：J K : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.pointwise_smul_def`：pointwise_smul_def {a : α} (S : Subgroup G)
 : a • S = S.map (MulDistribMulAction.toMonoidEnd _ _ a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.relIndex_comap`：relIndex_comap (f : G' ->* G) (K : Subgroup G')
 : relIndex (comap f H) K = relIndex H (map f K)
· 使用定理 `Subgroup.comap_map_eq_self_of_injective`：comap_map_eq_self_of_injective 
{f : G ->* N} (h : Function.Injective f) (H : Subgroup G) : comap f (map f H) = 
H
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulDistribMulAction.toMonoidEnd_apply`：∀ (M : Type u_2) (A : Type u_3) [
inst : Monoid M] [inst_1 : Monoid A] [inst_2 : MulDistribMulAction M A] (r : M),
   (MulDistribMulAction.toM…
· 使用定理 `MulDistribMulAction.toMonoidHom_apply`：∀ {M : Type u_2} (A : Type u_3) [
inst : Monoid M] [inst_1 : Monoid A] [inst_2 : MulDistribMulAction M A] (r : M) 
  (x : A), (MulDistribMulAc…
-/
lemma Subgroup.relIndex_pointwise_smul [Group G] [MulDistribMulAction H G] (J K : Subgroup G) :
    (h • J).relIndex (h • K) = J.relIndex K := by
  rw [pointwise_smul_def K, ← relIndex_comap, pointwise_smul_def,
    comap_map_eq_self_of_injective (by intro a b; simp)]

set_option backward.isDefEq.respectTransparency false in
/-
**AddSubgroup.relIndex_pointwise_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AddSubgroup.relIndex_pointwise_smul [AddGroup G] [DistribMulAction H G] (J
 K : AddSubgroup G) : (h • J).relIndex (h • K) = J.relIndex K
参数：J K : AddSubgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AddSubgroup.pointwise_smul_def`：pointwise_smul_def (S : AddSubgroup A) :
 a • S = S.map (DistribMulAction.toAddMonoidEnd _ _ a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddSubgroup.relIndex_comap`：∀ {G : Type u_1} {G' : Type u_2} [inst : Add
Group G] [inst_1 : AddGroup G'] (H : AddSubgroup G) (f : G' →+ G)   (K : AddSubg
roup G'), (AddSu…
· 使用定理 `AddSubgroup.comap_map_eq_self_of_injective`：∀ {G : Type u_1} [inst : Add
Group G] {N : Type u_5} [inst_1 : AddGroup N] {f : G →+ N},   Function.Injective
 ⇑f → ∀ (H : AddSubgroup G), Add…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DistribMulAction.toAddMonoidEnd_apply`：∀ (M : Type u_1) (A : Type u_7) [
inst : Monoid M] [inst_1 : AddMonoid A] [inst_2 : DistribMulAction M A] (x : M),
   (DistribMulAction.toAddM…
· 使用定理 `DistribSMul.toAddMonoidHom_apply`：∀ {M : Type u_1} (A : Type u_7) [inst 
: AddZeroClass A] [inst_1 : DistribSMul M A] (x : M) (x_1 : A),   (DistribSMul.t
oAddMonoidHom A x) x_1…
-/
lemma AddSubgroup.relIndex_pointwise_smul [AddGroup G] [DistribMulAction H G]
    (J K : AddSubgroup G) : (h • J).relIndex (h • K) = J.relIndex K := by
  rw [pointwise_smul_def K, ← relIndex_comap, pointwise_smul_def,
    comap_map_eq_self_of_injective (by intro a b; simp)]

end Pointwise

namespace MulAction

variable (G : Type*) {X : Type*} [Group G] [MulAction G X] (x : X)

/-
**MulAction.index_stabilizer** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：∀ (G : Type u_1) {X : Type u_2} [inst : Group G] [inst_1 : MulAction G X] 
(x : X),   (MulAction.stabilizer G x).index = (MulAction.orbit G x).ncard
参数：G : Type u_1；x : X；MulAction.stabilizer G x；MulAction.orbit G x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Nat.card_coe_set_eq`：∀ {α : Type u_1} (s : Set α), Nat.card ↑s = s.ncard
-/
@[to_additive] theorem index_stabilizer :
    (stabilizer G x).index = (orbit G x).ncard :=
  (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer G x)).symm.trans
    (Nat.card_coe_set_eq (orbit G x))
/-
**MulAction.index_stabilizer_of_transitive** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`
。
形式化陈述：∀ (G : Type u_1) {X : Type u_2} [inst : Group G] [inst_1 : MulAction G X] 
(x : X) [MulAction.IsPretransitive G X],   (MulAction.stabilizer G x).index = Na
t.card X
参数：G : Type u_1；x : X；MulAction.stabilizer G x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.index_stabilizer`：∀ (G : Type u_1) {X : Type u_2} [inst : Grou
p G] [inst_1 : MulAction G X] (x : X),   (MulAction.stabilizer G x).index = (Mul
Action.orbit G x…
· 使用定理 `MulAction.orbit_eq_univ`：orbit_eq_univ [IsPretransitive M α] (a : α) : o
rbit M a = Set.univ
· 使用定理 `Set.ncard_univ`：∀ (α : Type u_3), Set.univ.ncard = Nat.card α
-/
@[to_additive] theorem index_stabilizer_of_transitive [IsPretransitive G X] :
    (stabilizer G x).index = Nat.card X := by
  rw [index_stabilizer, orbit_eq_univ, Set.ncard_univ]

end MulAction

namespace MonoidHom

@[to_additive AddMonoidHom.surjective_of_card_ker_le_div]
/-
**MonoidHom.surjective_of_card_ker_le_div** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：surjective_of_card_ker_le_div {G M : Type*} [Group G] [Group M] [Finite G]
 [Finite M] (f : G ->* M) (h : Nat.card f.ker <= Nat.card G / Nat.card M) : Func
tion.Surjective f
参数：f : G ->* M；h : Nat.card f.ker <= Nat.card G / Nat.card M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MonoidHom.range_eq_top`：range_eq_top {N} [Group N] {f : G ->* N} : f.ran
ge = (⊤ : Subgroup N) ↔ Function.Surjective f
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
· 使用定理 `Set.eq_of_subset_of_ncard_le`：eq_of_subset_of_ncard_le (h : s subseteq t
) (h' : t.ncard <= s.ncard) (ht : t.Finite
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.coe_top`：coe_top : ((⊤ : Subgroup G) : Set G) = Set.univ
· 使用定理 `Set.ncard_univ`：∀ (α : Type u_3), Set.univ.ncard = Nat.card α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_coe_set_eq`：∀ {α : Type u_1} (s : Set α), Nat.card ↑s = s.ncard
· 使用定理 `SetLike.coe_sort_coe`：coe_sort_coe : ((p : Set B) : Type _) = p
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `MonoidHom.normal_ker`：∀ {G : Type u_1} [inst : Group G] {M : Type u_7} [
inst_1 : MulOneClass M] (f : G →* M), f.ker.Normal
· 使用定理 `Nat.le_of_mul_le_mul_left`：∀ {a b c : ℕ}, c * a ≤ c * b → 0 < c → a ≤ b
· 使用定理 `Nat.mul_le_of_le_div`：∀ (k x y : ℕ), x ≤ y / k → x * k ≤ y
· 使用定理 `Subgroup.card_mul_index`：card_mul_index : Nat.card H * H.index = Nat.car
d G
· 使用定理 `Nat.card_pos`：∀ {α : Type u_1} [Nonempty α] [Finite α], 0 < Nat.card α
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
-/
lemma surjective_of_card_ker_le_div {G M : Type*} [Group G] [Group M] [Finite G] [Finite M]
    (f : G →* M) (h : Nat.card f.ker ≤ Nat.card G / Nat.card M) : Function.Surjective f := by
  refine range_eq_top.1 <| SetLike.ext' <| Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_
  rw [Subgroup.coe_top, Set.ncard_univ, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe,
    ← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  exact Nat.le_of_mul_le_mul_left (f.ker.card_mul_index ▸ Nat.mul_le_of_le_div _ _ _ h) Nat.card_pos

open Finset

variable {G M F : Type*} [Group G] [Fintype G] [Monoid M] [DecidableEq M]
  [FunLike F G M] [MonoidHomClass F G M]

@[to_additive]
/-
**MonoidHom.card_fiber_eq_of_mem_range** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：card_fiber_eq_of_mem_range (f : F) {x y : M} (hx : x in Set.range f) (hy :
 y in Set.range f) : #{g | f g = x} = #{g | f g = y}
参数：f : F；hx : x in Set.range f；hy : y in Set.range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_left_surjective`：mul_left_surjective (a : G) : Surjective (a * ·)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.map_univ_equiv`：map_univ_equiv [Fintype β] (f : β ≃ α) : univ.map
 f.toEmbedding = univ
· 使用定理 `Finset.filter_map`：filter_map {p : β -> Prop} [DecidablePred p] : (s.map
 f).filter p = (s.filter (p ∘ f)).map f
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidHom.coe_toHomUnits`：coe_toHomUnits (f : G ->* M) (g : G) : (f.toHo
mUnits g : M) = f g
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `Units.mul_inv_eq_iff_eq_mul`：mul_inv_eq_iff_eq_mul {a c : α} : a * ↑b⁻¹ 
= c ↔ a = c * b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma card_fiber_eq_of_mem_range (f : F) {x y : M} (hx : x ∈ Set.range f) (hy : y ∈ Set.range f) :
    #{g | f g = x} = #{g | f g = y} := by
  rcases hx with ⟨x, rfl⟩
  rcases hy with ⟨y, rfl⟩
  rcases mul_left_surjective x y with ⟨y, rfl⟩
  conv_lhs =>
    rw [← map_univ_equiv (Equiv.mulRight y⁻¹), filter_map, card_map]
  congr 2 with g
  simp only [Function.comp, Equiv.toEmbedding_apply, Equiv.coe_mulRight, map_mul]
  let f' := MonoidHomClass.toMonoidHom f
  change f' g * f' y⁻¹ = f' x ↔ f' g = f' x * f' y
  rw [← f'.coe_toHomUnits y⁻¹, map_inv, Units.mul_inv_eq_iff_eq_mul, f'.coe_toHomUnits]

end MonoidHom

namespace AddSubgroup
variable {G A : Type*} [Group G] [AddGroup A] [DistribMulAction G A]

@[simp]
/-
**AddSubgroup.index_smul** 是 Mathlib 中的一个引理，位于命名空间 `AddSubgroup`。
形式化陈述：index_smul (a : G) (S : AddSubgroup A) : (a • S).index = S.index
参数：a : G；S : AddSubgroup A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.index_map_of_bijective`：∀ {G : Type u_1} {G' : Type u_2} [in
st : AddGroup G] [inst_1 : AddGroup G'] {f : G →+ G'},   Function.Bijective ⇑f →
 ∀ (H : AddSubgroup G), …
· 使用定理 `MulAction.bijective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Bijective fun x => g • x
-/
lemma index_smul (a : G) (S : AddSubgroup A) : (a • S).index = S.index :=
  index_map_of_bijective (MulAction.bijective _) _

end AddSubgroup

