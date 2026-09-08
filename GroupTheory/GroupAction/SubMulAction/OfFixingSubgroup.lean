/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfStabilizer
public import Mathlib.GroupTheory.GroupAction.Transitive
public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.Tactic.Group

/-!
# SubMulActions on complements of invariant subsets

Given a `MulAction` of `G` on `α` and `s : Set α`,

- `SubMulAction.ofFixingSubgroup` is the action
  of `FixingSubgroup G s` on the complement `sᶜ` of `s`.

- We define equivariant maps that relate various of these `SubMulAction`s
  and permit to manipulate them in a relatively smooth way:

  * `SubMulAction.ofFixingSubgroup_equivariantMap`:
    the identity map from `sᶜ` to `α`, as an equivariant map
    relative to the injection of `FixingSubgroup G s` into `G`.

  * `SubMulAction.fixingSubgroupInsertEquiv M a s`: the
    multiplicative equivalence between `fixingSubgroup M (insert a s)`
    and `fixingSubgroup (stabilizer M a) s`

  * `SubMulAction.ofFixingSubgroup_insert_map`: the equivariant
    map between `SubMulAction.ofFixingSubgroup M (Set.insert a s)`
    and `SubMulAction.ofFixingSubgroup (MulAction.stabilizer M a) s`.

  * `SubMulAction.fixingSubgroupEquivFixingSubgroup`:
    the multiplicative equivalence between `SubMulAction.ofFixingSubgroup M s`
    and `SubMulAction.ofFixingSubgroup M t` induced by `g : M`
    such that `g • t = s`.

  * `SubMulAction.conjMap_ofFixingSubgroup`:
    the equivariant map between `SubMulAction.ofFixingSubgroup M t`
    and `SubMulAction.ofFixingSubgroup M s`
    induced by `g : M` such that `g • t = s`.

  * `SubMulAction.ofFixingSubgroup_of_inclusion`:
    the identity from `SubMulAction.ofFixingSubgroup M s`
    to `SubMulAction.ofFixingSubgroup M t`, when `t ⊆ s`,
    as an equivariant map.

  * `SubMulAction.ofFixingSubgroup_of_singleton`:
    the identity map from `SubMulAction.ofStabilizer M a`
    to `SubMulAction.ofFixingSubgroup M {a}`.

  * `SubMulAction.ofFixingSubgroup_of_eq`:
    the identity from `SubMulAction.ofFixingSubgroup M s`
    to `SubMulAction.ofFixingSubgroup M t`, when `s = t`,
    as an equivariant map.

  * `SubMulAction.ofFixingSubgroup.append`: appends
    an enumeration of `ofFixingSubgroup M s` at the end
    of an enumeration of `s`, as an equivariant map.

-/

@[expose] public section

open scoped Pointwise

open MulAction Function

namespace SubMulAction

variable (M : Type*) {α : Type*} [Group M] [MulAction M α] (s : Set α)

/-- The `SubMulAction` of `fixingSubgroup M s` on the complement of `s`. -/
@[to_additive /-- The `SubAddAction` of `fixingAddSubgroup M s` on the complement of `s`. -/]
/-
**SubMulAction.ofFixingSubgroup** 是 Mathlib 中的一个定义，位于命名空间 `SubMulAction`。
形式化陈述：ofFixingSubgroup : SubMulAction (fixingSubgroup M s) α where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `SubMulAction` of `fixingSubgroup M s` on the complement of `s`.
-/
def ofFixingSubgroup : SubMulAction (fixingSubgroup M s) α where
  carrier := sᶜ
  smul_mem' := fun ⟨c, hc⟩ x ↦ by
    rw [← Subgroup.inv_mem_iff] at hc
    simp only [Set.mem_compl_iff, not_imp_not]
    intro hcx
    rwa [← one_smul M x, ← inv_mul_cancel c, mul_smul, (mem_fixingSubgroup_iff M).mp hc (c • x) hcx]

@[to_additive (attr := simp)]
/-
**SubMulAction.ofFixingSubgroup_carrier** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`
。
形式化陈述：ofFixingSubgroup_carrier : (ofFixingSubgroup M s).carrier = sᶜ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofFixingSubgroup_carrier :
    (ofFixingSubgroup M s).carrier = sᶜ := rfl

variable {s}

@[to_additive]
/-
**SubMulAction.mem_ofFixingSubgroup_iff** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`
。
形式化陈述：mem_ofFixingSubgroup_iff {x : α} : x in ofFixingSubgroup M s ↔ x ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_ofFixingSubgroup_iff {x : α} :
    x ∈ ofFixingSubgroup M s ↔ x ∉ s :=
  Iff.rfl

variable {M}

@[to_additive]
/-
**SubMulAction.not_mem_of_mem_ofFixingSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `SubMul
Action`。
形式化陈述：not_mem_of_mem_ofFixingSubgroup (x : ofFixingSubgroup M s) : ↑x ∉ s
参数：x : ofFixingSubgroup M s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem not_mem_of_mem_ofFixingSubgroup (x : ofFixingSubgroup M s) :
    ↑x ∉ s := x.prop

@[to_additive]
/-
**SubMulAction.disjoint_val_image** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`。
形式化陈述：disjoint_val_image {t : Set (ofFixingSubgroup M s)} : Disjoint s (Subtype.
val '' t)
参数：ofFixingSubgroup M s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.disjoint_iff`：∀ {α : Type u} {s t : Set α}, Disjoint s t ↔ s ∩ t ⊆ ∅
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem disjoint_val_image {t : Set (ofFixingSubgroup M s)} :
    Disjoint s (Subtype.val '' t) := by
  rw [Set.disjoint_iff]
  rintro a ⟨hbs, ⟨b, _, rfl⟩⟩; exact (b.prop hbs).elim

variable (M s) in
/-- The identity map of the `SubMulAction` of the `fixingSubgroup`
into the ambient set, as an equivariant map. -/
@[to_additive
/-- The identity map of the `SubAddAction` of the `fixingAddSubgroup`
into the ambient set, as an equivariant map. -/]
/-
**SubMulAction.ofFixingSubgroup_equivariantMap** 是 Mathlib 中的一个定义，位于命名空间 `SubMul
Action`。
形式化陈述：ofFixingSubgroup_equivariantMap : ofFixingSubgroup M s ->ₑ[(fixingSubgroup
 M s).subtype] α where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ofFixingSubgroup_equivariantMap :
    ofFixingSubgroup M s →ₑ[(fixingSubgroup M s).subtype] α where
  toFun x := x
  map_smul' _ _ := rfl

@[to_additive]
/-
**SubMulAction.ofFixingSubgroup_equivariantMap_injective** 是 Mathlib 中的一个定理，位于命名
空间 `SubMulAction`。
形式化陈述：ofFixingSubgroup_equivariantMap_injective : Injective (ofFixingSubgroup_eq
uivariantMap M s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
-/
theorem ofFixingSubgroup_equivariantMap_injective :
    Injective (ofFixingSubgroup_equivariantMap M s) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  simpa [Subtype.mk.injEq] using! hxy

section Comparisons

section Empty

@[to_additive]
/-
**SubMulAction.ofFixingSubgroupEmpty_equivariantMap_bijective** 是 Mathlib 中的一个定理
，位于命名空间 `SubMulAction`。
形式化陈述：ofFixingSubgroupEmpty_equivariantMap_bijective : Bijective (ofFixingSubgro
up_equivariantMap M (∅ : Set α))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubMulAction.ofFixingSubgroup_equivariantMap_injective`：ofFixingSubgroup
_equivariantMap_injective : Injective (ofFixingSubgroup_equivariantMap M s)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SubMulAction.mem_ofFixingSubgroup_iff`：mem_ofFixingSubgroup_iff {x : α} 
: x in ofFixingSubgroup M s ↔ x ∉ s
· 使用定理 `Set.notMem_empty`：notMem_empty (x : α) : x ∉ (∅ : Set α)
-/
theorem ofFixingSubgroupEmpty_equivariantMap_bijective :
    Bijective (ofFixingSubgroup_equivariantMap M (∅ : Set α)) := by
  refine ⟨ofFixingSubgroup_equivariantMap_injective, fun x ↦ ?_⟩
  exact ⟨⟨x, (mem_ofFixingSubgroup_iff M).mp (Set.notMem_empty x)⟩, rfl⟩

@[to_additive]
/-
**SubMulAction.of_fixingSubgroupEmpty_mapScalars_surjective** 是 Mathlib 中的一个定理，位
于命名空间 `SubMulAction`。
形式化陈述：of_fixingSubgroupEmpty_mapScalars_surjective : Surjective (fixingSubgroup 
M (∅ : Set α)).subtype
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `fixingSubgroup_empty`：fixingSubgroup_empty : fixingSubgroup M (∅ : Set α
) = ⊤
-/
theorem of_fixingSubgroupEmpty_mapScalars_surjective :
    Surjective (fixingSubgroup M (∅ : Set α)).subtype :=
  fun g ↦ ⟨⟨g, by simp⟩, rfl⟩

end Empty

section FixingSubgroupInsert

@[to_additive]
/-
**SubMulAction.mem_fixingSubgroup_insert_iff** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAc
tion`。
形式化陈述：mem_fixingSubgroup_insert_iff {a : α} {s : Set α} {m : M} : m in fixingSub
group M (insert a s) ↔ m • a = a ∧ m in fixingSubgroup M s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
theorem mem_fixingSubgroup_insert_iff {a : α} {s : Set α} {m : M} :
    m ∈ fixingSubgroup M (insert a s) ↔ m • a = a ∧ m ∈ fixingSubgroup M s := by
  simp [mem_fixingSubgroup_iff]

@[to_additive]
/-
**SubMulAction.fixingSubgroup_of_insert** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`
。
形式化陈述：fixingSubgroup_of_insert (a : α) (s : Set (ofStabilizer M a)) : fixingSubg
roup M (insert a ((fun x => x.val) '' s)) = (fixingSubgroup (↥(stabilizer M a)) 
s).map (stabilizer M a).subtype
参数：a : α；s : Set (ofStabilizer M a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
· 使用定理 `SubMulAction.instSMulMemClass`：∀ {R : Type u} {M : Type v} [inst : SMul 
R M], SMulMemClass (SubMulAction R M) R M
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem fixingSubgroup_of_insert (a : α) (s : Set (ofStabilizer M a)) :
    fixingSubgroup M (insert a ((fun x ↦ x.val) '' s)) =
      (fixingSubgroup (↥(stabilizer M a)) s).map (stabilizer M a).subtype := by
  ext m
  simp [mem_fixingSubgroup_iff, mem_ofStabilizer_iff, subgroup_smul_def, and_comm]

@[to_additive]
/-
**SubMulAction.mem_ofFixingSubgroup_insert_iff** 是 Mathlib 中的一个定理，位于命名空间 `SubMul
Action`。
形式化陈述：mem_ofFixingSubgroup_insert_iff {a : α} {s : Set (ofStabilizer M a)} {x : 
α} : x in ofFixingSubgroup M (insert a ((fun x => x.val) '' s)) ↔ exists (hx : x
 in ofStabilizer M a), (⟨x, hx⟩ : ofStabilizer M a) in ofFixingSubgroup (stabili
zer M a) s
参数：ofStabilizer M a。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_ofFixingSubgroup_insert_iff {a : α} {s : Set (ofStabilizer M a)} {x : α} :
    x ∈ ofFixingSubgroup M (insert a ((fun x ↦ x.val) '' s)) ↔
      ∃ (hx : x ∈ ofStabilizer M a),
        (⟨x, hx⟩ : ofStabilizer M a) ∈ ofFixingSubgroup (stabilizer M a) s := by
  grind [mem_ofFixingSubgroup_iff, mem_ofStabilizer_iff]

/-- The natural group isomorphism between fixing subgroups. -/
@[to_additive /-- The natural additive group isomorphism between fixing additive subgroups. -/]
/-
**SubMulAction.fixingSubgroupInsertEquiv** 是 Mathlib 中的一个定义，位于命名空间 `SubMulAction
`。
形式化陈述：fixingSubgroupInsertEquiv (a : α) (s : Set (ofStabilizer M a)) : fixingSub
group M (insert a (Subtype.val '' s)) ≃* fixingSubgroup (stabilizer M a) s where
 toFun m
参数：a : α；s : Set (ofStabilizer M a)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural group isomorphism between fixing subgroups.
-/
def fixingSubgroupInsertEquiv (a : α) (s : Set (ofStabilizer M a)) :
    fixingSubgroup M (insert a (Subtype.val '' s)) ≃* fixingSubgroup (stabilizer M a) s where
  toFun m := ⟨⟨(m : M), (mem_fixingSubgroup_iff M).mp m.prop a (Set.mem_insert _ _)⟩,
      fun ⟨x, hx⟩ => by
        simp only [← SetLike.coe_eq_coe]
        refine (mem_fixingSubgroup_iff M).mp m.prop _ (Set.mem_insert_of_mem a ?_)
        exact ⟨⟨x, (SubMulAction.mem_ofStabilizer_iff  M a).mp x.prop⟩, hx, rfl⟩⟩
  map_mul' _ _ := by simp [← Subtype.coe_inj]
  invFun m := ⟨m, by simp [fixingSubgroup_of_insert]⟩
  left_inv _ := by simp
  right_inv _ := by simp

/-- The identity map of fixing subgroup of stabilizer
into the fixing subgroup of the extended set, as an equivariant map. -/
@[to_additive /-- The identity map of fixing additive subgroup of stabilizer
into the fixing additive subgroup of the extended set, as an equivariant map. -/]
/-
**SubMulAction.ofFixingSubgroup_insert_map** 是 Mathlib 中的一个定义，位于命名空间 `SubMulActi
on`。
形式化陈述：ofFixingSubgroup_insert_map (a : α) (s : Set (ofStabilizer M a)) : ofFixin
gSubgroup M (insert a (Subtype.val '' s)) ->ₑ[fixingSubgroupInsertEquiv a s] ofF
ixingSubgroup (stabilizer M a) s where toFun x
参数：a : α；s : Set (ofStabilizer M a)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ofFixingSubgroup_insert_map (a : α) (s : Set (ofStabilizer M a)) :
    ofFixingSubgroup M (insert a (Subtype.val '' s))
      →ₑ[fixingSubgroupInsertEquiv a s]
        ofFixingSubgroup (stabilizer M a) s where
  toFun x := by
    choose hx hx' using (mem_ofFixingSubgroup_insert_iff.mp x.prop)
    exact ⟨_, hx'⟩
  map_smul' _ _ := rfl

@[to_additive (attr := simp)]
/-
**SubMulAction.ofFixingSubgroup_insert_map_apply** 是 Mathlib 中的一个定理，位于命名空间 `SubM
ulAction`。
形式化陈述：ofFixingSubgroup_insert_map_apply {a : α} {s : Set (ofStabilizer M a)} {x 
: α} (hx : x in ofFixingSubgroup M (insert a (Subtype.val '' s))) : (ofFixingSub
group_insert_map a s) ⟨x, hx⟩ = x
参数：ofStabilizer M a；hx : x in ofFixingSubgroup M (insert a (Subtype.val '' s))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.instIsScalarTowerSubtypeMem`：∀ {G : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : Group G] [inst_1 : SMul α β] [inst_2 : MulAction G α]   [in
st_3 : MulAction G β] [IsS…
-/
theorem ofFixingSubgroup_insert_map_apply {a : α} {s : Set (ofStabilizer M a)}
    {x : α} (hx : x ∈ ofFixingSubgroup M (insert a (Subtype.val '' s))) :
    (ofFixingSubgroup_insert_map a s) ⟨x, hx⟩ = x :=
  rfl

@[to_additive]
/-
**SubMulAction.ofFixingSubgroup_insert_map_bijective** 是 Mathlib 中的一个定理，位于命名空间 `
SubMulAction`。
形式化陈述：ofFixingSubgroup_insert_map_bijective {a : α} {s : Set (ofStabilizer M a)}
 : Bijective (ofFixingSubgroup_insert_map a s)
参数：ofStabilizer M a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.instIsScalarTowerSubtypeMem`：∀ {G : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : Group G] [inst_1 : SMul α β] [inst_2 : MulAction G α]   [in
st_3 : MulAction G β] [IsS…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SubMulAction.mem_ofFixingSubgroup_insert_iff`：mem_ofFixingSubgroup_inser
t_iff {a : α} {s : Set (ofStabilizer M a)} {x : α} : x in ofFixingSubgroup M (in
sert a ((fun x => x.val) '' s)) ↔ …
-/
theorem ofFixingSubgroup_insert_map_bijective {a : α} {s : Set (ofStabilizer M a)} :
    Bijective (ofFixingSubgroup_insert_map a s) := by
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    simpa only [← Subtype.coe_inj, ofFixingSubgroup_insert_map_apply] using h
  · rintro ⟨⟨x, hx1⟩, hx2⟩
    exact ⟨⟨x, mem_ofFixingSubgroup_insert_iff.mpr ⟨hx1, hx2⟩⟩, rfl⟩

end FixingSubgroupInsert

section FixingSubgroupConj

variable {s t : Set α} {g : M}

@[to_additive]
/-
**SubMulAction._root_.Set.conj_mem_fixingSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `Sub
MulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.conj_mem_fixingSubgroup (hg : g • t = s) {k : M} (hk : k ∈ fixingSubgroup M t) :
    MulAut.conj g k ∈ fixingSubgroup M s := by
  simp only [mem_fixingSubgroup_iff] at hk ⊢
  intro y hy
  rw [MulAut.conj_apply, eq_comm, mul_smul, mul_smul, ← inv_smul_eq_iff, eq_comm]
  apply hk
  rw [← Set.mem_smul_set_iff_inv_smul_mem, hg]
  exact hy

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/-
**SubMulAction.fixingSubgroup_map_conj_eq** 是 Mathlib 中的一个定理，位于命名空间 `SubMulActio
n`。
形式化陈述：fixingSubgroup_map_conj_eq (hg : g • t = s) : (fixingSubgroup M t).map (Mu
lAut.conj g).toMonoidHom = fixingSubgroup M s
参数：hg : g • t = s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `Set.conj_mem_fixingSubgroup`：∀ {M : Type u_1} {α : Type u_2} [inst : Gro
up M] [inst_1 : MulAction M α] {s t : Set α} {g : M},   g • t = s → ∀ {k : M}, k
 ∈ fixingSubgroup…
· 使用定理 `inv_smul_eq_iff`：∀ {G : Type u_3} {α : Type u_5} [inst : Group G] [inst_
1 : MulAction G α] {g : G} {a b : α}, g⁻¹ • a = b ↔ a = g • b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Equiv.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun toFun_1 : α 
→ β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : invFun 
= invFun_…
· 使用定理 `MulEquiv.mk.congr_simp`：∀ {M : Type u_9} {N : Type u_10} [inst : Mul M] 
[inst_1 : Mul N] (toEquiv toEquiv_1 : M ≃ N)   (e_toEquiv : toEquiv = toEquiv_1)
 (map_mul' :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `zpow_zero`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G), a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.Group._zpow_trick_one`：_zpow_trick_one {G : Type*} [Group
 G] (a b : G) (m : Int) : a * b * b ^ m = a * b ^ (m + 1)
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fixingSubgroup_map_conj_eq (hg : g • t = s) :
    (fixingSubgroup M t).map (MulAut.conj g).toMonoidHom = fixingSubgroup M s := by
  ext k
  simp only [MulEquiv.toMonoidHom_eq_coe, Subgroup.mem_map, MonoidHom.coe_coe]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact Set.conj_mem_fixingSubgroup hg hn
  · intro hk
    use MulAut.conj g⁻¹ k
    constructor
    · apply Set.conj_mem_fixingSubgroup _ hk
      rw [inv_smul_eq_iff, hg]
    · simp [MulAut.conj]; group

variable (g s) in
/-- The `fixingSubgroup` of `g • s` is the conjugate of the `fixingSubgroup` of `s` by `g`. -/
@[to_additive /-- The `fixingAddSubgroup` of `g +ᵥ s` is the conjugate
of the `fixingAddSubgroup` of `s` by `g`. -/]
/-
**SubMulAction.fixingSubgroup_smul_eq_fixingSubgroup_map_conj** 是 Mathlib 中的一个定理
，位于命名空间 `SubMulAction`。
形式化陈述：fixingSubgroup_smul_eq_fixingSubgroup_map_conj : fixingSubgroup M (g • s) 
= (fixingSubgroup M s).map (MulAut.conj g).toMonoidHom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SubMulAction.fixingSubgroup_map_conj_eq`：fixingSubgroup_map_conj_eq (hg 
: g • t = s) : (fixingSubgroup M t).map (MulAut.conj g).toMonoidHom = fixingSubg
roup M s
-/
theorem fixingSubgroup_smul_eq_fixingSubgroup_map_conj :
    fixingSubgroup M (g • s) = (fixingSubgroup M s).map (MulAut.conj g).toMonoidHom :=
  (fixingSubgroup_map_conj_eq rfl).symm

/-- The equivalence of `fixingSubgroup M t` with `fixingSubgroup M s`
  when `s` is a translate of `t`. -/
@[to_additive
/-- The equivalence of `fixingSubgroup M t` with `fixingSubgroup M s`
  when `s` is a translate of `t`. -/]
/-
**SubMulAction.fixingSubgroupEquivFixingSubgroup** 是 Mathlib 中的一个定义，位于命名空间 `SubM
ulAction`。
形式化陈述：fixingSubgroupEquivFixingSubgroup (hg : g • t = s) : fixingSubgroup M t ≃*
 fixingSubgroup M s
参数：hg : g • t = s。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SubMulAction.fixingSubgroup_map_conj_eq`：fixingSubgroup_map_conj_eq (hg 
: g • t = s) : (fixingSubgroup M t).map (MulAut.conj g).toMonoidHom = fixingSubg
roup M s
-/
def fixingSubgroupEquivFixingSubgroup (hg : g • t = s) :
    fixingSubgroup M t ≃* fixingSubgroup M s :=
  ((MulAut.conj g).subgroupMap (fixingSubgroup M t)).trans
    (MulEquiv.subgroupCongr (fixingSubgroup_map_conj_eq hg))

@[to_additive (attr := simp)]
/-
**SubMulAction.fixingSubgroupEquivFixingSubgroup_coe_apply** 是 Mathlib 中的一个定理，位于
命名空间 `SubMulAction`。
形式化陈述：fixingSubgroupEquivFixingSubgroup_coe_apply (hg : g • t = s) (x : fixingSu
bgroup M t) : (fixingSubgroupEquivFixingSubgroup hg x : M) = MulAut.conj g x
参数：hg : g • t = s；x : fixingSubgroup M t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fixingSubgroupEquivFixingSubgroup_coe_apply (hg : g • t = s) (x : fixingSubgroup M t) :
    (fixingSubgroupEquivFixingSubgroup hg x : M) = MulAut.conj g x := rfl

/-- Conjugation induces an equivariant map between the `SubMulAction` of
the fixing subgroup of a subset and that of a translate. -/
@[to_additive
/-- Conjugation induces an equivariant map between the `SubAddAction` of
the fixing subgroup of a subset and that of a translate. -/]
/-
**SubMulAction.conjMap_ofFixingSubgroup** 是 Mathlib 中的一个定义，位于命名空间 `SubMulAction`
。
形式化陈述：conjMap_ofFixingSubgroup (hg : g • t = s) : ofFixingSubgroup M t ->ₑ[fixin
gSubgroupEquivFixingSubgroup hg] ofFixingSubgroup M s where toFun
参数：hg : g • t = s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def conjMap_ofFixingSubgroup (hg : g • t = s) :
    ofFixingSubgroup M t →ₑ[fixingSubgroupEquivFixingSubgroup hg] ofFixingSubgroup M s where
  toFun := fun ⟨x, hx⟩ =>
    ⟨g • x, by
      intro hgxt; apply hx
      rw [← hg] at hgxt
      exact Set.smul_mem_smul_set_iff.mp hgxt⟩
  map_smul' := fun ⟨m, hm⟩ ⟨x, hx⟩ => by
    simp only [← SetLike.coe_eq_coe, subgroup_smul_def,
      SetLike.val_smul,
      fixingSubgroupEquivFixingSubgroup_coe_apply,
      MulAut.conj_apply, mul_smul, inv_smul_smul]

@[to_additive (attr := simp)]
/-
**SubMulAction.conjMap_ofFixingSubgroup_coe_apply** 是 Mathlib 中的一个定理，位于命名空间 `Sub
MulAction`。
形式化陈述：conjMap_ofFixingSubgroup_coe_apply {hg : g • t = s} (x : ofFixingSubgroup 
M t) : conjMap_ofFixingSubgroup hg x = g • (x : α)
参数：x : ofFixingSubgroup M t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem conjMap_ofFixingSubgroup_coe_apply {hg : g • t = s} (x : ofFixingSubgroup M t) :
    conjMap_ofFixingSubgroup hg x = g • (x : α) := rfl

@[to_additive]
/-
**SubMulAction.conjMap_ofFixingSubgroup_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Sub
MulAction`。
形式化陈述：conjMap_ofFixingSubgroup_bijective {s t : Set α} {g : M} {hst : g • s = t}
 : Bijective (conjMap_ofFixingSubgroup hst)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_smul_eq_iff`：∀ {G : Type u_3} {α : Type u_5} [inst : Group G] [inst_
1 : MulAction G α] {g : G} {a b : α}, g⁻¹ • a = b ↔ a = g • b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem conjMap_ofFixingSubgroup_bijective {s t : Set α} {g : M} {hst : g • s = t} :
    Bijective (conjMap_ofFixingSubgroup hst) := by
  constructor
  · rintro x y hxy
    simpa [← SetLike.coe_eq_coe] using hxy
  · rintro ⟨x, hx⟩
    rw [eq_comm, ← inv_smul_eq_iff] at hst
    use (SubMulAction.conjMap_ofFixingSubgroup hst) ⟨x, hx⟩
    simp [← SetLike.coe_eq_coe]

end FixingSubgroupConj

variable {s t : Set α}

@[to_additive]
/-
**SubMulAction.mem_fixingSubgroup_union_iff** 是 Mathlib 中的一个引理，位于命名空间 `SubMulAct
ion`。
形式化陈述：mem_fixingSubgroup_union_iff {g : M} : g in fixingSubgroup M (s union t) ↔
 g in fixingSubgroup M s ∧ g in fixingSubgroup M t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fixingSubgroup_union`：fixingSubgroup_union {s t : Set α} : fixingSubgrou
p M (s union t) = fixingSubgroup M s ⊓ fixingSubgroup M t
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_fixingSubgroup_union_iff {g : M} :
    g ∈ fixingSubgroup M (s ∪ t) ↔ g ∈ fixingSubgroup M s ∧ g ∈ fixingSubgroup M t := by
  simp [fixingSubgroup_union, Subgroup.mem_inf]

/-- The group morphism from `fixingSubgroup` of a union to the iterated `fixingSubgroup`. -/
@[to_additive
/-- The additive group morphism from `fixingAddSubgroup` of a union
to the iterated `fixingAddSubgroup`. -/]
/-
**SubMulAction.fixingSubgroup_union_to_fixingSubgroup_of_fixingSubgroup** 是 Math
lib 中的一个定义，位于命名空间 `SubMulAction`。
形式化陈述：fixingSubgroup_union_to_fixingSubgroup_of_fixingSubgroup : fixingSubgroup 
M (s union t) ->* fixingSubgroup (fixingSubgroup M s) (Subtype.val ⁻¹' t : Set (
ofFixingSubgroup M s)) where toFun m
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def fixingSubgroup_union_to_fixingSubgroup_of_fixingSubgroup :
    fixingSubgroup M (s ∪ t) →*
      fixingSubgroup (fixingSubgroup M s) (Subtype.val ⁻¹' t : Set (ofFixingSubgroup M s)) where
  toFun m := ⟨⟨m, (mem_fixingSubgroup_union_iff.mp m.prop).1⟩, by
      rintro ⟨⟨x, hx⟩, hx'⟩
      simp only [Set.mem_preimage] at hx'
      simp only [← SetLike.coe_eq_coe, SubMulAction.val_smul_of_tower]
      exact (mem_fixingSubgroup_union_iff.mp m.prop).2 ⟨x, hx'⟩⟩
  map_one' := by simp
  map_mul' _ _ := by simp

variable (M s t) in
/-- The identity between the iterated `SubMulAction`
  of the `fixingSubgroup` and the `SubMulAction` of the `fixingSubgroup`
  of the union, as an equivariant map. -/
@[to_additive /-- The identity between the iterated `SubAddAction`
  of the `fixingAddSubgroup` and the `SubAddAction` of the `fixingAddSubgroup`
  of the union, as an equivariant map. -/]
/-
**SubMulAction.map_ofFixingSubgroupUnion** 是 Mathlib 中的一个定义，位于命名空间 `SubMulAction
`。
形式化陈述：map_ofFixingSubgroupUnion : let ψ : fixingSubgroup M (s union t) -> fixing
Subgroup (fixingSubgroup M s) (Subtype.val ⁻¹' t : Set (ofFixingSubgroup M s))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def map_ofFixingSubgroupUnion :
    let ψ : fixingSubgroup M (s ∪ t) →
      fixingSubgroup (fixingSubgroup M s) (Subtype.val ⁻¹' t : Set (ofFixingSubgroup M s)) :=
      fun m ↦ ⟨⟨m, by
        let hm := m.prop
        simp only [fixingSubgroup_union, Subgroup.mem_inf] at hm
        exact hm.left⟩, by
      let hm := m.prop
      simp only [fixingSubgroup_union, Subgroup.mem_inf] at hm
      rintro ⟨⟨x, hx⟩, hx'⟩
      simp only [Set.mem_preimage] at hx'
      simp only [← SetLike.coe_eq_coe, SubMulAction.val_smul_of_tower]
      exact hm.right ⟨x, hx'⟩⟩
    ofFixingSubgroup M (s ∪ t) →ₑ[ψ]
      ofFixingSubgroup (fixingSubgroup M s) (Subtype.val ⁻¹' t : Set (ofFixingSubgroup M s)) where
  toFun x :=
    ⟨⟨x, fun hx => x.prop (Set.mem_union_left t hx)⟩,
        fun hx => x.prop (by
          apply Set.mem_union_right s
          simpa only [Set.mem_preimage, Subtype.coe_mk] using hx)⟩
  map_smul' := fun ⟨m, hm⟩ ⟨x, hx⟩ => by
    rw [← SetLike.coe_eq_coe, ← SetLike.coe_eq_coe]
    exact subgroup_smul_def ⟨m, hm⟩ x

@[to_additive]
/-
**SubMulAction.map_ofFixingSubgroupUnion_def** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAc
tion`。
形式化陈述：map_ofFixingSubgroupUnion_def (x : SubMulAction.ofFixingSubgroup M (s unio
n t)) : ((SubMulAction.map_ofFixingSubgroupUnion M s t) x : α) = x
参数：x : SubMulAction.ofFixingSubgroup M (s union t)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.instIsScalarTowerSubtypeMem`：∀ {G : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : Group G] [inst_1 : SMul α β] [inst_2 : MulAction G α]   [in
st_3 : MulAction G β] [IsS…
-/
theorem map_ofFixingSubgroupUnion_def (x : SubMulAction.ofFixingSubgroup M (s ∪ t)) :
    ((SubMulAction.map_ofFixingSubgroupUnion M s t) x : α) = x :=
  rfl

@[to_additive]
/-
**SubMulAction.map_ofFixingSubgroupUnion_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Su
bMulAction`。
形式化陈述：map_ofFixingSubgroupUnion_bijective : Bijective (map_ofFixingSubgroupUnion
 M s t)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.instIsScalarTowerSubtypeMem`：∀ {G : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : Group G] [inst_1 : SMul α β] [inst_2 : MulAction G α]   [in
st_3 : MulAction G β] [IsS…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_union`：mem_union (x : α) (a b : Set α) : x in a union b ↔ x in a
 ∨ x in b
-/
theorem map_ofFixingSubgroupUnion_bijective :
    Bijective (map_ofFixingSubgroupUnion M s t) := by
  constructor
  · intro a b h
    simpa only [← SetLike.coe_eq_coe] using! h
  · rintro ⟨⟨a, ha⟩, ha'⟩
    suffices a ∈ ofFixingSubgroup M (s ∪ t) by
      exact ⟨⟨a, this⟩,  rfl⟩
    intro hy
    rcases (Set.mem_union a s t).mp hy with h | h
    · exact ha h
    · apply ha'
      simpa only [Set.mem_preimage]

variable (M) in
/-- The equivariant map on `SubMulAction.ofFixingSubgroup` given a set inclusion. -/
@[to_additive
/-- The equivariant map on `SubAddAction.ofFixingAddSubgroup` given a set inclusion. -/]
/-
**SubMulAction.ofFixingSubgroup_of_inclusion** 是 Mathlib 中的一个定义，位于命名空间 `SubMulAc
tion`。
形式化陈述：ofFixingSubgroup_of_inclusion (hst : t subseteq s) : ofFixingSubgroup M s 
->ₑ[Subgroup.inclusion (fixingSubgroup_antitone M α hst)] ofFixingSubgroup M t w
here toFun y
参数：hst : t subseteq s。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fixingSubgroup_antitone`：fixingSubgroup_antitone : Antitone (fixingSubgr
oup M : Set α -> Subgroup M)
-/
def ofFixingSubgroup_of_inclusion (hst : t ⊆ s) :
    ofFixingSubgroup M s
      →ₑ[Subgroup.inclusion (fixingSubgroup_antitone M α hst)]
        ofFixingSubgroup M t where
  toFun y := ⟨y.val, fun h => y.prop (hst h)⟩
  map_smul' _ _ := rfl

@[to_additive]
/-
**SubMulAction.ofFixingSubgroup_of_inclusion_injective** 是 Mathlib 中的一个引理，位于命名空间
 `SubMulAction`。
形式化陈述：ofFixingSubgroup_of_inclusion_injective {hst : t subseteq s} : Injective (
ofFixingSubgroup_of_inclusion M hst)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fixingSubgroup_antitone`：fixingSubgroup_antitone : Antitone (fixingSubgr
oup M : Set α -> Subgroup M)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.coe_eq_coe`：coe_eq_coe {x y : p} : (x : B) = y ↔ x = y
-/
lemma ofFixingSubgroup_of_inclusion_injective {hst : t ⊆ s} :
    Injective (ofFixingSubgroup_of_inclusion M hst) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  rw [← SetLike.coe_eq_coe] at hxy ⊢
  exact hxy

set_option backward.isDefEq.respectTransparency false in
variable (M) in
/-- The equivariant map between `SubMulAction.ofStabilizer M a`
and `ofFixingSubgroup M {a}`. -/
@[to_additive /-- The equivariant map between `SubAddAction.ofStabilizer M a`
and `ofFixingAddSubgroup M {a}`. -/]
/-
**SubMulAction.ofFixingSubgroup_of_singleton** 是 Mathlib 中的一个定义，位于命名空间 `SubMulAc
tion`。
形式化陈述：ofFixingSubgroup_of_singleton (a : α) : let φ : fixingSubgroup M ({a} : Se
t α) -> stabilizer M a
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ofFixingSubgroup_of_singleton (a : α) :
    let φ : fixingSubgroup M ({a} : Set α) → stabilizer M a := fun ⟨m, hm⟩ =>
      ⟨m, ((mem_fixingSubgroup_iff M).mp hm) a (Set.mem_singleton a)⟩
    ofFixingSubgroup M ({a} : Set α) →ₑ[φ] ofStabilizer M a where
  toFun x := ⟨x, by simp⟩
  map_smul' _ _ := rfl

@[to_additive]
/-
**SubMulAction.ofFixingSubgroup_of_singleton_bijective** 是 Mathlib 中的一个定理，位于命名空间
 `SubMulAction`。
形式化陈述：ofFixingSubgroup_of_singleton_bijective {a : α} : Bijective (ofFixingSubgr
oup_of_singleton M a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_fixingSubgroup_iff`：mem_fixingSubgroup_iff {s : Set α} {m : M} : m i
n fixingSubgroup M s ↔ forall y in s, m • y = y
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
-/
theorem ofFixingSubgroup_of_singleton_bijective {a : α} :
    Bijective (ofFixingSubgroup_of_singleton M a) :=
  ⟨fun _ _ ↦ id, fun x ↦ ⟨x, rfl⟩⟩

variable (M) in
/-- The identity between the `SubMulAction`s of `fixingSubgroup`s
of equal sets, as an equivariant map. -/
@[to_additive /-- The identity between the `SubAddAction`s of `fixingAddSubgroup`s
of equal sets, as an equivariant map. -/]
/-
**SubMulAction.ofFixingSubgroup_of_eq** 是 Mathlib 中的一个定义，位于命名空间 `SubMulAction`。
形式化陈述：ofFixingSubgroup_of_eq (hst : s = t) : let φ : fixingSubgroup M s ≃* fixin
gSubgroup M t
参数：hst : s = t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ofFixingSubgroup_of_eq (hst : s = t) :
    let φ : fixingSubgroup M s ≃* fixingSubgroup M t :=
      MulEquiv.subgroupCongr (congrArg₂ _ rfl hst)
    ofFixingSubgroup M s →ₑ[φ] ofFixingSubgroup M t where
  toFun := fun ⟨x, hx⟩ => ⟨x, by rw [← hst]; exact hx⟩
  map_smul' := fun ⟨m, hm⟩ ⟨x, hx⟩ => rfl

@[to_additive (attr := simp)]
/-
**SubMulAction.ofFixingSubgroup_of_eq_apply** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAct
ion`。
形式化陈述：ofFixingSubgroup_of_eq_apply {hst : s = t} (x : ofFixingSubgroup M s) : ((
ofFixingSubgroup_of_eq M hst x) : α) = x
参数：x : ofFixingSubgroup M s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → γ
) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
-/
theorem ofFixingSubgroup_of_eq_apply {hst : s = t}
    (x : ofFixingSubgroup M s) :
    ((ofFixingSubgroup_of_eq M hst x) : α) = x := rfl

@[to_additive]
/-
**SubMulAction.ofFixingSubgroup_of_eq_bijective** 是 Mathlib 中的一个定理，位于命名空间 `SubMu
lAction`。
形式化陈述：ofFixingSubgroup_of_eq_bijective {hst : s = t} : Bijective (ofFixingSubgro
up_of_eq M hst)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → γ
) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofFixingSubgroup_of_eq_bijective {hst : s = t} :
    Bijective (ofFixingSubgroup_of_eq M hst) :=
  ⟨fun _ _ hxy ↦ by simpa [← SetLike.coe_eq_coe] using hxy,
    fun ⟨x, hxt⟩ ↦ ⟨⟨x, by rwa [hst]⟩, by simp [← SetLike.coe_eq_coe]⟩⟩

end Comparisons

section Construction

open Function.Embedding Fin.Embedding

/-- Append `Fin m ↪ ofFixingSubgroup M s` at the end of an enumeration of `s`. -/
@[to_additive
/-- Append `Fin m ↪ ofFixingSubgroup M s` at the end of an enumeration of `s`. -/]
/-
**SubMulAction.ofFixingSubgroup.append** 是 Mathlib 中的一个定义，位于命名空间 `SubMulAction.o
fFixingSubgroup`。
形式化陈述：{M : Type u_1} →   {α : Type u_2} →     [inst : Group M] →       [inst_1 :
 MulAction M α] →         {s : Set α} → {n : ℕ} → [Finite ↑s] → (Fin n ↪ ↥(SubMu
lAction.ofFixingSubgroup M s)) → Fin (s.ncard + n) ↪ α
参数：Fin n ↪ ↥(SubMulAction.ofFixingSubgroup M s)；s.ncard + n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def ofFixingSubgroup.append
    {n : ℕ} [Finite s] (x : Fin n ↪ ofFixingSubgroup M s) :
    Fin (s.ncard + n) ↪ α := by
  have : Nonempty (Fin (s.ncard) ≃ s) :=
    Finite.card_eq.mp (by simp [Nat.card_coe_set_eq])
  let y := (Classical.choice this).toEmbedding
  apply Fin.Embedding.append (x := y.trans (subtype _)) (y := x.trans (subtype _))
  rw [Set.disjoint_iff_forall_ne]
  rintro _ ⟨j, rfl⟩ _ ⟨i, rfl⟩ H
  apply (x i).prop
  simp only [trans_apply, Function.Embedding.subtype_apply] at H
  simpa [H] using Subtype.coe_prop (y j)

@[to_additive]
/-
**SubMulAction.ofFixingSubgroup.append_left** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAct
ion.ofFixingSubgroup`。
形式化陈述：∀ {M : Type u_1} {α : Type u_2} [inst : Group M] [inst_1 : MulAction M α] 
{s : Set α} {n : ℕ} [inst_2 : Finite ↑s]   (x : Fin n ↪ ↥(SubMulAction.ofFixingS
ubgroup M s)) (i : Fin s.ncard),   have Hs := ⋯;   (SubMulAction.ofFixingSubgrou
p.append x) (Fin.castAdd n i) = ↑((Classical.choice Hs) i)
参数：x : Fin n ↪ ↥(SubMulAction.ofFixingSubgroup M s)；i : Fin s.ncard。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finite.card_eq`：card_eq [Finite α] [Finite β] : Nat.card α = Nat.card β 
↔ Nonempty (α ≃ β)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.append_left`：append_left (u : Fin m -> α) (v : Fin n -> α) (i : Fin 
m) : append u v (Fin.castAdd n i) = u i
· 使用定理 `Function.Embedding.trans_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α ↪ β) (g : β ↪ γ) (a : α), (f.trans g) a = g (f a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofFixingSubgroup.append_left {n : ℕ} [Finite s]
    (x : Fin n ↪ ofFixingSubgroup M s) (i : Fin s.ncard) :
    let Hs : Nonempty (Fin (s.ncard) ≃ s) :=
      Finite.card_eq.mp (by simp [Nat.card_coe_set_eq])
    ofFixingSubgroup.append x (Fin.castAdd n i) = (Classical.choice Hs) i := by
  simp [ofFixingSubgroup.append]

@[to_additive]
/-
**SubMulAction.ofFixingSubgroup.append_right** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAc
tion.ofFixingSubgroup`。
形式化陈述：∀ {M : Type u_1} {α : Type u_2} [inst : Group M] [inst_1 : MulAction M α] 
{s : Set α} {n : ℕ} [inst_2 : Finite ↑s]   (x : Fin n ↪ ↥(SubMulAction.ofFixingS
ubgroup M s)) (i : Fin n),   (SubMulAction.ofFixingSubgroup.append x) (Fin.natAd
d s.ncard i) = ↑(x i)
参数：x : Fin n ↪ ↥(SubMulAction.ofFixingSubgroup M s)；i : Fin n；SubMulAction.ofFix
ingSubgroup.append x；Fin.natAdd s.ncard i；x i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.append_right`：append_right (u : Fin m -> α) (v : Fin n -> α) (i : Fi
n n) : append u v (natAdd m i) = v i
· 使用定理 `Function.Embedding.trans_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α ↪ β) (g : β ↪ γ) (a : α), (f.trans g) a = g (f a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofFixingSubgroup.append_right {n : ℕ} [Finite s]
    (x : Fin n ↪ ofFixingSubgroup M s) (i : Fin n) :
    ofFixingSubgroup.append x (Fin.natAdd s.ncard i) = x i := by
  simp [ofFixingSubgroup.append]

end Construction

section TwoCriteria

open MulAction

/-- A pretransitivity criterion. -/
/-
**SubMulAction.IsPretransitive.isPretransitive_ofFixingSubgroup_inter** 是 Mathli
b 中的一个定理，位于命名空间 `SubMulAction.IsPretransitive`。
形式化陈述：∀ {M : Type u_1} {α : Type u_2} [inst : Group M] [inst_1 : MulAction M α] 
{s : Set α},   MulAction.IsPretransitive ↥(fixingSubgroup M s) ↥(SubMulAction.of
FixingSubgroup M s) →     ∀ {g : M},       s ∪ g • s ≠ ⊤ →         MulAction.IsP
retransitive ↥(fixingSubgroup M (s ∩ g • s)) ↥(SubMulAction.ofFixingSubgroup M (
s ∩ g • s))
参数：fixingSubgroup M s；SubMulAction.ofFixingSubgroup M s；fixingSubgroup M (s ∩ g 
• s)；SubMulAction.ofFixingSubgroup M (s ∩ g • s)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Set.compl_empty_iff`：compl_empty_iff {s : Set α} : sᶜ = ∅ ↔ s = univ
· 使用定理 `Set.top_eq_univ`：top_eq_univ : (⊤ : Set α) = univ
· 使用定理 `Set.compl_inter`：compl_inter (s t : Set α) : (s inter t)ᶜ = sᶜ union tᶜ
· 使用定理 `Set.mem_union_left`：mem_union_left {x : α} {a : Set α} (b : Set α) : x i
n a -> x in a union b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.compl_union`：compl_union (s t : Set α) : (s union t)ᶜ = sᶜ inter tᶜ
· 使用定理 `MulAction.isPretransitive_iff_base`：isPretransitive_iff_base (a : X) : I
sPretransitive G X ↔ forall x : X, exists g : G, g • a = x where mp hG x
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `Set.mem_inter_iff`：mem_inter_iff (x : α) (a b : Set α) : x in a inter b 
↔ x in a ∧ x in b
· 使用定理 `SubMulAction.mem_ofFixingSubgroup_iff`：mem_ofFixingSubgroup_iff {x : α} 
: x in ofFixingSubgroup M s ↔ x ∉ s
· 使用定理 `MulAction.IsPretransitive.exists_smul_eq`：∀ {M : Type u_5} {α : Type u_6
} {inst : SMul M α} [self : MulAction.IsPretransitive M α] (x y : α), ∃ g, g • x
 = y
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_smul_set_iff_inv_smul_mem`：mem_smul_set_iff_inv_smul_mem : x in 
a • A ↔ a⁻¹ • x in A
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `mem_fixingSubgroup_iff`：mem_fixingSubgroup_iff {s : Set α} {m : M} : m i
n fixingSubgroup M s ↔ forall y in s, m • y = y
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用引理 `smul_eq_iff_eq_inv_smul`：smul_eq_iff_eq_inv_smul (g : α) {x y : β} : g •
 x = y ↔ x = g⁻¹ • y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `eq_inv_smul_iff`：∀ {G : Type u_3} {α : Type u_5} [inst : Group G] [inst_
1 : MulAction G α] {g : G} {a b : α}, a = g⁻¹ • b ↔ g • a = b
· 使用引理 `Subgroup.mk_smul`：mk_smul (g : G) (hg : g in S) (a : α) : (⟨g, hg⟩ : S) 
• a = g • a
· 使用定理 `SubMulAction.instSMulMemClass`：∀ {R : Type u} {M : Type v} [inst : SMul 
R M], SMulMemClass (SubMulAction R M) R M
· 使用定理 `SetLike.val_smul`：∀ {S : Type u'} {R : Type u} {M : Type v} [inst : SMul
 R M] [inst_1 : SetLike S M] [hS : SMulMemClass S R M] (s : S)   (r : R) (x : ↥s
), ↑(r…

--- 原说明 ---
A pretransitivity criterion.
-/
theorem IsPretransitive.isPretransitive_ofFixingSubgroup_inter
    (hs : IsPretransitive (fixingSubgroup M s) (ofFixingSubgroup M s))
    {g : M} (ha : s ∪ g • s ≠ ⊤) :
    IsPretransitive (fixingSubgroup M (s ∩ g • s)) (ofFixingSubgroup M (s ∩ g • s)) := by
  rw [Ne, Set.top_eq_univ, ← Set.compl_empty_iff, ← Ne, ← Set.nonempty_iff_ne_empty] at ha
  obtain ⟨a, ha⟩ := ha
  rw [Set.compl_union] at ha
  have ha' : a ∈ (s ∩ g • s)ᶜ := by
    rw [Set.compl_inter]
    exact Set.mem_union_left _ ha.1
  rw [MulAction.isPretransitive_iff_base (⟨a, ha'⟩ : ofFixingSubgroup M (s ∩ g • s))]
  rintro ⟨x, hx⟩
  rw [mem_ofFixingSubgroup_iff, Set.mem_inter_iff, not_and_or] at hx
  rcases hx with hx | hx
  · obtain ⟨⟨k, hk⟩, hkax⟩ := hs.exists_smul_eq ⟨a, ha.1⟩ ⟨x, hx⟩
    use ⟨k, fun ⟨y, hy⟩ ↦ hk ⟨y, hy.1⟩⟩
    rwa [Subtype.ext_iff] at hkax ⊢
  · have hg'x : g⁻¹ • x ∈ ofFixingSubgroup M s := mt Set.mem_smul_set_iff_inv_smul_mem.mpr hx
    have hg'a : g⁻¹ • a ∈ ofFixingSubgroup M s := mt Set.mem_smul_set_iff_inv_smul_mem.mpr ha.2
    obtain ⟨⟨k, hk⟩, hkax⟩ := hs.exists_smul_eq ⟨g⁻¹ • a, hg'a⟩ ⟨g⁻¹ • x, hg'x⟩
    use ⟨g * k * g⁻¹, ?_⟩
    · simp only [← SetLike.coe_eq_coe] at hkax ⊢
      rwa [SetLike.val_smul, Subgroup.mk_smul, eq_inv_smul_iff, smul_smul, smul_smul] at hkax
    · rw [mem_fixingSubgroup_iff] at hk ⊢
      intro y hy
      rw [mul_smul, mul_smul, smul_eq_iff_eq_inv_smul g]
      exact hk _ (Set.mem_smul_set_iff_inv_smul_mem.mp hy.2)

/-- A primitivity criterion -/
/-
**SubMulAction.IsPreprimitive.isPreprimitive_ofFixingSubgroup_inter** 是 Mathlib 
中的一个定理，位于命名空间 `SubMulAction.IsPreprimitive`。
形式化陈述：∀ {M : Type u_1} {α : Type u_2} [inst : Group M] [inst_1 : MulAction M α] 
{s : Set α} [Finite α],   MulAction.IsPreprimitive ↥(fixingSubgroup M s) ↥(SubMu
lAction.ofFixingSubgroup M s) →     ∀ {g : M},       s ∪ g • s ≠ ⊤ →         Mul
Action.IsPreprimitive ↥(fixingSubgroup M (s ∩ g • s)) ↥(SubMulAction.ofFixingSub
group M (s ∩ g • s))
参数：fixingSubgroup M s；SubMulAction.ofFixingSubgroup M s；fixingSubgroup M (s ∩ g 
• s)；SubMulAction.ofFixingSubgroup M (s ∩ g • s)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubMulAction.IsPretransitive.isPretransitive_ofFixingSubgroup_inter`：∀ {
M : Type u_1} {α : Type u_2} [inst : Group M] [inst_1 : MulAction M α] {s : Set 
α},   MulAction.IsPretransitive ↥(fixingSubgroup M s) ↥(S…
· 使用定理 `MulAction.IsPreprimitive.toIsPretransitive`：∀ {G : Type u_1} {X : Type u
_2} {inst : SMul G X} [self : MulAction.IsPreprimitive G X], MulAction.IsPretran
sitive G X
· 使用定理 `MulAction.IsPreprimitive.of_card_lt`：of_card_lt [Finite Y] [IsPretransit
ive H Y] [IsPreprimitive G X] (hf' : Nat.card Y < 2 * (Set.range f).ncard) : IsP
reprimitive H Y
· 使用定理 `fixingSubgroup_antitone`：fixingSubgroup_antitone : Antitone (fixingSubgr
oup M : Set α -> Subgroup M)
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_coe_set_eq`：∀ {α : Type u_1} (s : Set α), Nat.card ↑s = s.ncard
· 使用定理 `Set.ncard_range_of_injective`：ncard_range_of_injective (hf : Function.In
jective f) : (range f).ncard = Nat.card α
· 使用引理 `SubMulAction.ofFixingSubgroup_of_inclusion_injective`：ofFixingSubgroup_o
f_inclusion_injective {hst : t subseteq s} : Injective (ofFixingSubgroup_of_incl
usion M hst)
· 使用定理 `Set.compl_inter`：compl_inter (s t : Set α) : (s inter t)ᶜ = sᶜ union tᶜ
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Set.ncard_union_lt`：ncard_union_lt (hs : s.Finite
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用引理 `Set.disjoint_compl_right_iff_subset`：disjoint_compl_right_iff_subset : D
isjoint s tᶜ ↔ s subseteq t
· 使用定理 `Set.compl_subset_iff_union`：compl_subset_iff_union {s t : Set α} : sᶜ su
bseteq t ↔ s union t = univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.smul_set_compl`：smul_set_compl : a • sᶜ = (a • s)ᶜ
· 使用引理 `Set.ncard_smul_set`：ncard_smul_set (a : G) (s : Set α) : (a • s).ncard =
 s.ncard
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
A primitivity criterion
-/
theorem IsPreprimitive.isPreprimitive_ofFixingSubgroup_inter
    [Finite α]
    (hs : IsPreprimitive (fixingSubgroup M s) (ofFixingSubgroup M s))
    {g : M} (ha : s ∪ g • s ≠ ⊤) :
    IsPreprimitive (fixingSubgroup M (s ∩ g • s)) (ofFixingSubgroup M (s ∩ g • s)) := by
  have := IsPretransitive.isPretransitive_ofFixingSubgroup_inter hs.toIsPretransitive ha
  apply IsPreprimitive.of_card_lt (f := ofFixingSubgroup_of_inclusion M Set.inter_subset_left)
  rw [show Nat.card (ofFixingSubgroup M (s ∩ g • s)) = (s ∩ g • s)ᶜ.ncard from
    Nat.card_coe_set_eq _, Set.ncard_range_of_injective ofFixingSubgroup_of_inclusion_injective,
    show Nat.card (ofFixingSubgroup M s) = sᶜ.ncard from Nat.card_coe_set_eq _, Set.compl_inter]
  refine (Set.ncard_union_lt sᶜ.toFinite (g • s)ᶜ.toFinite ?_).trans_le ?_
  · rwa [Set.disjoint_compl_right_iff_subset, Set.compl_subset_iff_union]
  · rw [← Set.smul_set_compl, Set.ncard_smul_set, two_mul]

end TwoCriteria

end SubMulAction

section Pointwise

open MulAction Set

variable (G : Type*) [Group G] {α : Type*} [MulAction G α]

@[to_additive]
/-
**MulAction.fixingSubgroup_le_stabilizer** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulAction.fixingSubgroup_le_stabilizer (s : Set α) : fixingSubgroup G s <=
 stabilizer G s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.mem_stabilizer_iff`：mem_stabilizer_iff {a : α} {g : G} : g in 
stabilizer G a ↔ g • a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
-/
theorem MulAction.fixingSubgroup_le_stabilizer (s : Set α) :
    fixingSubgroup G s ≤ stabilizer G s := by
  intro k hk
  rw [mem_stabilizer_iff]
  conv_rhs => rw [← Set.image_id s]
  apply Set.image_congr
  simpa only [mem_fixingSubgroup_iff, id] using hk

end Pointwise

