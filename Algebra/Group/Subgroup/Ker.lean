/-
Copyright (c) 2020 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Tactic.ApplyFun

import Mathlib.Algebra.Group.Equiv.Basic

/-!
# Kernel and range of group homomorphisms

We define and prove results about the kernel and range of group homomorphisms.

Special thanks goes to Amelia Livingston and Yury Kudryashov for their help and inspiration.

## Main definitions

Notation used here:

- `G N` are `Group`s

- `x` is an element of type `G`

- `f g : N →* G` are group homomorphisms

Definitions in the file:

* `MonoidHom.range f` : the range of the group homomorphism `f` is a subgroup

* `MonoidHom.ker f` : the kernel of a group homomorphism `f` is the subgroup of elements `x : G`
  such that `f x = 1`

* `MonoidHom.eqLocus f g` : given group homomorphisms `f`, `g`, the elements of `G` such that
  `f x = g x` form a subgroup of `G`

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

namespace MonoidHom

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

open Subgroup

/-- The range of a monoid homomorphism from a group is a subgroup. -/
@[to_additive /-- The range of an `AddMonoidHom` from an `AddGroup` is an `AddSubgroup`. -/]
/-
**MonoidHom.range** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：range (f : G ->* N) : Subgroup N
参数：f : G ->* N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The range of a monoid homomorphism from a group is a subgroup.
-/
def range (f : G →* N) : Subgroup N :=
  Subgroup.copy ((⊤ : Subgroup G).map f) (Set.range f) (by simp)

@[to_additive]
/-
**MonoidHom.subsingleton_coe_range** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：subsingleton_coe_range [Subsingleton G] (f : G ->* N) : (f.range : Set N).
Subsingleton
参数：f : G ->* N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subsingleton_range`：subsingleton_range {α : Sort*} [Subsingleton α] 
(f : α -> β) : (range f).Subsingleton
-/
lemma subsingleton_coe_range [Subsingleton G] (f : G →* N) : (f.range : Set N).Subsingleton :=
  Set.subsingleton_range f

@[to_additive (attr := simp)]
/-
**MonoidHom.coe_range** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：coe_range (f : G ->* N) : (f.range : Set N) = Set.range f
参数：f : G ->* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_range (f : G →* N) : (f.range : Set N) = Set.range f :=
  rfl

@[to_additive (attr := simp)]
/-
**MonoidHom.mem_range** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：mem_range {f : G ->* N} {y : N} : y in f.range ↔ exists x, f x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_range {f : G →* N} {y : N} : y ∈ f.range ↔ ∃ x, f x = y :=
  Iff.rfl

@[to_additive]
/-
**MonoidHom.range_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：range_eq_map (f : G ->* N) : f.range = (⊤ : Subgroup G).map f
参数：f : G ->* N。
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem range_eq_map (f : G →* N) : f.range = (⊤ : Subgroup G).map f := by ext; simp

@[to_additive (attr := simp)]
/-
**MonoidHom.comap_range_self** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：comap_range_self (f : G ->* N) : f.range.comap f = ⊤
参数：f : G ->* N。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem comap_range_self (f : G →* N) : f.range.comap f = ⊤ := by
  ext
  simp

@[to_additive]
/-
**MonoidHom._root_.Subgroup.range_isMulCommutative** 是 Mathlib 中的一个实例，位于命名空间 `Mo
noidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.Subgroup.range_isMulCommutative {G : Type*} [Group G] [IsMulCommutative G]
    {N : Type*} [Group N] (f : G →* N) :
    IsMulCommutative f.range :=
  range_eq_map f ▸ Subgroup.map_isMulCommutative ⊤ f

@[to_additive (attr := simp)]
/-
**MonoidHom.domRestrict_range** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：domRestrict_range (f : G ->* N) : (f.domRestrict K).range = K.map f
参数：f : G ->* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
-/
theorem domRestrict_range (f : G →* N) : (f.domRestrict K).range = K.map f := by
  simp_rw [SetLike.ext_iff, mem_range, mem_map, domRestrict_apply, SetLike.exists,
    exists_prop, forall_const]

@[deprecated (since := "2026-07-19")] alias restrict_range := domRestrict_range
@[deprecated (since := "2026-07-19")]
alias _root_.AddMonoidHom.restrict_range := _root_.AddMonoidHom.domRestrict_range

/-- The canonical surjective group homomorphism `G →* f(G)` induced by a group
homomorphism `G →* N`. -/
@[to_additive
      /-- The canonical surjective `AddGroup` homomorphism `G →+ f(G)` induced by a group
      homomorphism `G →+ N`. -/]
/-
**MonoidHom.rangeRestrict** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：rangeRestrict (f : G ->* N) : G ->* f.range
参数：f : G ->* N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def rangeRestrict (f : G →* N) : G →* f.range :=
  codRestrict f _ fun x => ⟨x, rfl⟩

@[to_additive (attr := simp)]
/-
**MonoidHom.coe_rangeRestrict** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：coe_rangeRestrict (f : G ->* N) (g : G) : (f.rangeRestrict g : N) = f g
参数：f : G ->* N；g : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_rangeRestrict (f : G →* N) (g : G) : (f.rangeRestrict g : N) = f g :=
  rfl

@[to_additive]
/-
**MonoidHom.coe_comp_rangeRestrict** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：coe_comp_rangeRestrict (f : G ->* N) : ((↑) : f.range -> N) ∘ (⇑f.rangeRes
trict : G -> f.range) = f
参数：f : G ->* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp_rangeRestrict (f : G →* N) :
    ((↑) : f.range → N) ∘ (⇑f.rangeRestrict : G → f.range) = f :=
  rfl

@[to_additive]
/-
**MonoidHom.subtype_comp_rangeRestrict** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：subtype_comp_rangeRestrict (f : G ->* N) : f.range.subtype.comp f.rangeRes
trict = f
参数：f : G ->* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `MonoidHom.coe_rangeRestrict`：coe_rangeRestrict (f : G ->* N) (g : G) : (
f.rangeRestrict g : N) = f g
-/
theorem subtype_comp_rangeRestrict (f : G →* N) : f.range.subtype.comp f.rangeRestrict = f :=
  ext <| f.coe_rangeRestrict

@[to_additive]
/-
**MonoidHom.rangeRestrict_surjective** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：rangeRestrict_surjective (f : G ->* N) : Function.Surjective f.rangeRestri
ct
参数：f : G ->* N。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rangeRestrict_surjective (f : G →* N) : Function.Surjective f.rangeRestrict :=
  fun ⟨_, g, rfl⟩ => ⟨g, rfl⟩

@[to_additive (attr := simp)]
/-
**MonoidHom.rangeRestrict_injective_iff** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：rangeRestrict_injective_iff {f : G ->* N} : Injective f.rangeRestrict ↔ In
jective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.injective_codRestrict`：injective_codRestrict {f : ι -> α} {s : Set α
} (h : forall x, f x in s) : Injective (codRestrict f s h) ↔ Injective f
-/
lemma rangeRestrict_injective_iff {f : G →* N} : Injective f.rangeRestrict ↔ Injective f := by
  convert! Set.injective_codRestrict _

@[to_additive]
/-
**MonoidHom.map_range** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：map_range (g : N ->* P) (f : G ->* N) : f.range.map g = (g.comp f).range
参数：g : N ->* P；f : G ->* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.range_eq_map`：range_eq_map (f : G ->* N) : f.range = (⊤ : Subg
roup G).map f
· 使用定理 `Subgroup.map_map`：map_map (g : N ->* P) (f : G ->* N) : (K.map f).map g 
= K.map (g.comp f)
-/
theorem map_range (g : N →* P) (f : G →* N) : f.range.map g = (g.comp f).range := by
  rw [range_eq_map, range_eq_map]; exact (⊤ : Subgroup G).map_map g f

@[to_additive]
/-
**MonoidHom.range_comp** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：range_comp (g : N ->* P) (f : G ->* N) : (g.comp f).range = f.range.map g
参数：g : N ->* P；f : G ->* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.map_range`：map_range (g : N ->* P) (f : G ->* N) : f.range.map
 g = (g.comp f).range
-/
lemma range_comp (g : N →* P) (f : G →* N) : (g.comp f).range = f.range.map g := (map_range ..).symm

@[to_additive]
/-
**MonoidHom.range_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：range_eq_top {N} [Group N] {f : G ->* N} : f.range = (⊤ : Subgroup N) ↔ Fu
nction.Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.coe_range`：coe_range (f : G ->* N) : (f.range : Set N) = Set.r
ange f
· 使用定理 `Subgroup.coe_top`：coe_top : ((⊤ : Subgroup G) : Set G) = Set.univ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Set.range_eq_univ`：range_eq_univ : range f = univ ↔ Surjective f
-/
theorem range_eq_top {N} [Group N] {f : G →* N} :
    f.range = (⊤ : Subgroup N) ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans <| Iff.trans (by rw [coe_range, coe_top]) Set.range_eq_univ

/-- The range of a surjective monoid homomorphism is the whole of the codomain. -/
@[to_additive (attr := simp)
  /-- The range of a surjective `AddMonoid` homomorphism is the whole of the codomain. -/]
/-
**MonoidHom.range_eq_top_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：range_eq_top_of_surjective {N} [Group N] (f : G ->* N) (hf : Function.Surj
ective f) : f.range = (⊤ : Subgroup N)
参数：f : G ->* N；hf : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MonoidHom.range_eq_top`：range_eq_top {N} [Group N] {f : G ->* N} : f.ran
ge = (⊤ : Subgroup N) ↔ Function.Surjective f
-/
theorem range_eq_top_of_surjective {N} [Group N] (f : G →* N) (hf : Function.Surjective f) :
    f.range = (⊤ : Subgroup N) :=
  range_eq_top.2 hf

@[to_additive (attr := simp)]
/-
**MonoidHom.range_one** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：range_one : (1 : G ->* N).range = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `comm`：comm [Std.Symm r] {a b : α} : r a b ↔ r b a
· 使用定理 `IsEquiv.toSymm`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEquiv α r]
, Std.Symm r
-/
theorem range_one : (1 : G →* N).range = ⊥ :=
  SetLike.ext fun x => by simpa using @comm _ (· = ·) _ 1 x

@[to_additive (attr := simp)]
/-
**MonoidHom._root_.Subgroup.range_subtype** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Subgroup.range_subtype (H : Subgroup G) : H.subtype.range = H :=
  SetLike.coe_injective <| (coe_range _).trans <| Subtype.range_coe

@[to_additive]
alias _root_.Subgroup.subtype_range := Subgroup.range_subtype

@[to_additive (attr := simp)]
/-
**MonoidHom._root_.Subgroup.inclusion_range** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Subgroup.inclusion_range {H K : Subgroup G} (h_le : H ≤ K) :
    (inclusion h_le).range = H.subgroupOf K :=
  Subgroup.ext fun g => Set.ext_iff.mp (Set.range_inclusion h_le) g

@[to_additive]
/-
**MonoidHom.subgroupOf_range_eq_of_le** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：subgroupOf_range_eq_of_le {G₁ G₂ : Type*} [Group G₁] [Group G₂] {K : Subgr
oup G₂} (f : G₁ ->* G₂) (h : f.range <= K) : f.range.subgroupOf K = (f.codRestri
ct K fun x => h ⟨x, rfl⟩).range
参数：f : G₁ ->* G₂；h : f.range <= K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonoidHom.codRestrict_apply`：∀ {M : Type u_1} {N : Type u_2} [inst : Mul
OneClass M] [inst_1 : MulOneClass N] {S : Type u_5} [inst_2 : SetLike S N]   [in
st_3 : SubmonoidC…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem subgroupOf_range_eq_of_le {G₁ G₂ : Type*} [Group G₁] [Group G₂] {K : Subgroup G₂}
    (f : G₁ →* G₂) (h : f.range ≤ K) :
    f.range.subgroupOf K = (f.codRestrict K fun x => h ⟨x, rfl⟩).range := by
  ext k
  refine exists_congr ?_
  simp [Subtype.ext_iff]

/-- Computable alternative to `MonoidHom.ofInjective`. -/
@[to_additive /-- Computable alternative to `AddMonoidHom.ofInjective`. -/]
/-
**MonoidHom.ofLeftInverse** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：ofLeftInverse {f : G ->* N} {g : N ->* G} (h : Function.LeftInverse g f) :
 G ≃* f.range
参数：h : Function.LeftInverse g f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Computable alternative to `MonoidHom.ofInjective`.
-/
def ofLeftInverse {f : G →* N} {g : N →* G} (h : Function.LeftInverse g f) : G ≃* f.range :=
  { f.rangeRestrict with
    toFun := f.rangeRestrict
    invFun := g ∘ f.range.subtype
    left_inv := h
    right_inv := by
      rintro ⟨x, y, rfl⟩
      solve_by_elim }

@[to_additive (attr := simp)]
/-
**MonoidHom.ofLeftInverse_apply** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：ofLeftInverse_apply {f : G ->* N} {g : N ->* G} (h : Function.LeftInverse 
g f) (x : G) : ↑(ofLeftInverse h x) = f x
参数：h : Function.LeftInverse g f；x : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofLeftInverse_apply {f : G →* N} {g : N →* G} (h : Function.LeftInverse g f) (x : G) :
    ↑(ofLeftInverse h x) = f x :=
  rfl

@[to_additive (attr := simp)]
/-
**MonoidHom.ofLeftInverse_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：ofLeftInverse_symm_apply {f : G ->* N} {g : N ->* G} (h : Function.LeftInv
erse g f) (x : f.range) : (ofLeftInverse h).symm x = g x
参数：h : Function.LeftInverse g f；x : f.range。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofLeftInverse_symm_apply {f : G →* N} {g : N →* G} (h : Function.LeftInverse g f)
    (x : f.range) : (ofLeftInverse h).symm x = g x :=
  rfl

/-- The range of an injective group homomorphism is isomorphic to its domain. -/
@[to_additive /-- The range of an injective additive group homomorphism is isomorphic to its
domain. -/]
/-
**MonoidHom.ofInjective** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：ofInjective {f : G ->* N} (hf : Function.Injective f) : G ≃* f.range
参数：hf : Function.Injective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def ofInjective {f : G →* N} (hf : Function.Injective f) : G ≃* f.range :=
  MulEquiv.ofBijective (f.codRestrict f.range fun x => ⟨x, rfl⟩)
    ⟨fun _ _ h => hf (Subtype.ext_iff.mp h), by
      rintro ⟨x, y, rfl⟩
      exact ⟨y, rfl⟩⟩

@[to_additive]
/-
**MonoidHom.ofInjective_apply** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：ofInjective_apply {f : G ->* N} (hf : Function.Injective f) {x : G} : ↑(of
Injective hf x) = f x
参数：hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofInjective_apply {f : G →* N} (hf : Function.Injective f) {x : G} :
    ↑(ofInjective hf x) = f x :=
  rfl

@[to_additive (attr := simp)]
/-
**MonoidHom.apply_ofInjective_symm** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：apply_ofInjective_symm {f : G ->* N} (hf : Function.Injective f) (x : f.ra
nge) : f ((ofInjective hf).symm x) = x
参数：hf : Function.Injective f；x : f.range。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `MulEquiv.apply_symm_apply`：apply_symm_apply (e : M ≃* N) (y : N) : e (e.
symm y) = y
-/
theorem apply_ofInjective_symm {f : G →* N} (hf : Function.Injective f) (x : f.range) :
    f ((ofInjective hf).symm x) = x :=
  Subtype.ext_iff.1 <| (ofInjective hf).apply_symm_apply x

@[simp]
/-
**MonoidHom.coe_toAdditive_range** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：coe_toAdditive_range (f : G ->* G') : (MonoidHom.toAdditive f).range = Sub
group.toAddSubgroup f.range
参数：f : G ->* G'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toAdditive_range (f : G →* G') :
    (MonoidHom.toAdditive f).range = Subgroup.toAddSubgroup f.range := rfl

@[simp]
/-
**MonoidHom.coe_toMultiplicative_range** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：coe_toMultiplicative_range {A A' : Type*} [AddGroup A] [AddGroup A'] (f : 
A ->+ A') : (AddMonoidHom.toMultiplicative f).range = AddSubgroup.toSubgroup f.r
ange
参数：f : A ->+ A'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toMultiplicative_range {A A' : Type*} [AddGroup A] [AddGroup A'] (f : A →+ A') :
    (AddMonoidHom.toMultiplicative f).range = AddSubgroup.toSubgroup f.range := rfl

section Ker

variable {M : Type*} [MulOneClass M]

/-- The multiplicative kernel of a monoid homomorphism is the subgroup of elements `x : G` such that
`f x = 1` -/
@[to_additive
      /-- The additive kernel of an `AddMonoid` homomorphism is the `AddSubgroup` of elements
      such that `f x = 0` -/]
/-
**MonoidHom.ker** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：ker (f : G ->* M) : Subgroup G
参数：f : G ->* M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ker (f : G →* M) : Subgroup G :=
  { MonoidHom.mker f with
    inv_mem' := fun {x} (hx : f x = 1) =>
      calc
        f x⁻¹ = f x * f x⁻¹ := by rw [hx, one_mul]
        _ = 1 := by rw [← map_mul, mul_inv_cancel, map_one] }

@[to_additive (attr := simp)]
/-
**MonoidHom.ker_toSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：ker_toSubmonoid (f : G ->* M) : f.ker.toSubmonoid = MonoidHom.mker f
参数：f : G ->* M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ker_toSubmonoid (f : G →* M) : f.ker.toSubmonoid = MonoidHom.mker f := rfl

@[to_additive (attr := simp)]
/-
**MonoidHom.mem_ker** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：mem_ker {f : G ->* M} {x : G} : x in f.ker ↔ f x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_ker {f : G →* M} {x : G} : x ∈ f.ker ↔ f x = 1 :=
  Iff.rfl

@[to_additive]
/-
**MonoidHom.div_mem_ker_iff** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：div_mem_ker_iff (f : G ->* M) {x y : G} : x / y in ker f ↔ f x = f y
参数：f : G ->* M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_mul_cancel`：div_mul_cancel (a b : G) : a / b * b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MonoidHom.mem_ker`：mem_ker {f : G ->* M} {x : G} : x in f.ker ↔ f x = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
theorem div_mem_ker_iff (f : G →* M) {x y : G} : x / y ∈ ker f ↔ f x = f y := by
  constructor <;> intro h
  · rw [← div_mul_cancel x y, map_mul, mem_ker.mp h, one_mul]
  · rw [mem_ker, div_eq_mul_inv, map_mul, h, ← map_mul, mul_inv_cancel, map_one]

@[to_additive]
/-
**MonoidHom.coe_ker** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：coe_ker (f : G ->* M) : (f.ker : Set G) = (f : G -> M) ⁻¹' {1}
参数：f : G ->* M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ker (f : G →* M) : (f.ker : Set G) = (f : G → M) ⁻¹' {1} :=
  rfl

@[to_additive (attr := simp)]
/-
**MonoidHom.ker_toHomUnits** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：ker_toHomUnits {M} [Monoid M] (f : G ->* M) : f.toHomUnits.ker = f.ker
参数：f : G ->* M。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ker_toHomUnits {M} [Monoid M] (f : G →* M) : f.toHomUnits.ker = f.ker := by
  ext x
  simp [mem_ker, Units.ext_iff]

@[to_additive]
/-
**MonoidHom.eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：eq_iff (f : G ->* M) {x y : G} : f x = f y ↔ y⁻¹ * x in f.ker
参数：f : G ->* M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.mem_ker`：mem_ker {f : G ->* M} {x : G} : x in f.ker ↔ f x = 1
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem eq_iff (f : G →* M) {x y : G} : f x = f y ↔ y⁻¹ * x ∈ f.ker := by
  constructor <;> intro h
  · rw [mem_ker, map_mul, h, ← map_mul, inv_mul_cancel, map_one]
  · rw [← one_mul x, ← mul_inv_cancel y, mul_assoc, map_mul, mem_ker.1 h, mul_one]

@[to_additive]
/-
**MonoidHom.decidableMemKer** 是 Mathlib 中的一个实例，位于命名空间 `MonoidHom`。
形式化陈述：decidableMemKer [DecidableEq M] (f : G ->* M) : DecidablePred (· in f.ker)
参数：f : G ->* M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.mem_ker`：mem_ker {f : G ->* M} {x : G} : x in f.ker ↔ f x = 1
-/
instance decidableMemKer [DecidableEq M] (f : G →* M) : DecidablePred (· ∈ f.ker) := fun x =>
  decidable_of_iff (f x = 1) f.mem_ker

@[to_additive]
/-
**MonoidHom.comap_ker** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：comap_ker {P : Type*} [MulOneClass P] (g : N ->* P) (f : G ->* N) : g.ker.
comap f = (g.comp f).ker
参数：g : N ->* P；f : G ->* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_ker {P : Type*} [MulOneClass P] (g : N →* P) (f : G →* N) :
    g.ker.comap f = (g.comp f).ker :=
  rfl

@[to_additive (attr := simp)]
/-
**MonoidHom.comap_bot** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：comap_bot (f : G ->* N) : (⊥ : Subgroup N).comap f = f.ker
参数：f : G ->* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_bot (f : G →* N) : (⊥ : Subgroup N).comap f = f.ker :=
  rfl

@[to_additive]
/-
**MonoidHom.ker_le_comap** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：ker_le_comap (f : G ->* N) (H : Subgroup N) : f.ker <= H.comap f
参数：f : G ->* N；H : Subgroup N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.comap_mono`：comap_mono {f : G ->* N} {K K' : Subgroup N} : K <=
 K' -> comap f K <= comap f K'
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem ker_le_comap (f : G →* N) (H : Subgroup N) : f.ker ≤ H.comap f :=
  comap_mono bot_le

@[to_additive (attr := simp)]
/-
**MonoidHom.ker_domRestrict** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：ker_domRestrict (f : G ->* M) : (f.domRestrict K).ker = f.ker.subgroupOf K
参数：f : G ->* M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
-/
theorem ker_domRestrict (f : G →* M) : (f.domRestrict K).ker = f.ker.subgroupOf K :=
  rfl

@[deprecated (since := "2026-07-19")] alias ker_restrict := ker_domRestrict
@[deprecated (since := "2026-07-19")]
alias _root_.AddMonoidHom.ker_restrict := _root_.AddMonoidHom.ker_domRestrict

@[to_additive (attr := simp)]
/-
**MonoidHom.ker_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：ker_codRestrict {S} [SetLike S N] [SubmonoidClass S N] (f : G ->* N) (s : 
S) (h : forall x, f x in s) : (f.codRestrict s h).ker = f.ker
参数：f : G ->* N；s : S；h : forall x, f x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
theorem ker_codRestrict {S} [SetLike S N] [SubmonoidClass S N] (f : G →* N) (s : S)
    (h : ∀ x, f x ∈ s) : (f.codRestrict s h).ker = f.ker :=
  SetLike.ext fun _x => Subtype.ext_iff

@[to_additive (attr := simp)]
/-
**MonoidHom.ker_rangeRestrict** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：ker_rangeRestrict (f : G ->* N) : ker (rangeRestrict f) = ker f
参数：f : G ->* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ker_codRestrict`：ker_codRestrict {S} [SetLike S N] [SubmonoidC
lass S N] (f : G ->* N) (s : S) (h : forall x, f x in s) : (f.codRestrict s h).k
er = f.ker
-/
theorem ker_rangeRestrict (f : G →* N) : ker (rangeRestrict f) = ker f :=
  ker_codRestrict _ _ _

@[to_additive (attr := simp)]
/-
**MonoidHom.ker_one** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：ker_one : (1 : G ->* M).ker = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `eq_self_iff_true`：∀ {α : Sort u_1} (a : α), a = a ↔ True
-/
theorem ker_one : (1 : G →* M).ker = ⊤ :=
  SetLike.ext fun _x => eq_self_iff_true _

@[to_additive (attr := simp)]
/-
**MonoidHom.ker_id** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：ker_id : (MonoidHom.id G).ker = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ker_id : (MonoidHom.id G).ker = ⊥ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**MonoidHom.ker_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {M : Type u_7} [inst_1 : MulOneClass M] 
{f : G →* M}, f.ker = ⊤ ↔ f = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MonoidHom.ext_iff`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] {f g : M →* N}, f = g ↔ ∀ (x : M), f x = g x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[to_additive] theorem ker_eq_top_iff {f : G →* M} : f.ker = ⊤ ↔ f = 1 := by
  simp [ker, ← top_le_iff, SetLike.le_def, f.ext_iff]
/-
**MonoidHom.range_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：∀ {G : Type u_1} {G' : Type u_2} [inst : Group G] [inst_1 : Group G'] {f :
 G →* G'}, f.range = ⊥ ↔ f = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `MonoidHom.range_eq_map`：range_eq_map (f : G ->* N) : f.range = (⊤ : Subg
roup G).map f
· 使用定理 `Subgroup.map_le_iff_le_comap`：map_le_iff_le_comap {f : G ->* N} {K : Sub
group G} {H : Subgroup N} : K.map f <= H ↔ K <= H.comap f
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `MonoidHom.comap_bot`：comap_bot (f : G ->* N) : (⊥ : Subgroup N).comap f 
= f.ker
· 使用定理 `MonoidHom.ker_eq_top_iff`：∀ {G : Type u_1} [inst : Group G] {M : Type u_
7} [inst_1 : MulOneClass M] {f : G →* M}, f.ker = ⊤ ↔ f = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[to_additive] theorem range_eq_bot_iff {f : G →* G'} : f.range = ⊥ ↔ f = 1 := by
  rw [← le_bot_iff, f.range_eq_map, map_le_iff_le_comap, top_le_iff, comap_bot, ker_eq_top_iff]

@[to_additive]
/-
**MonoidHom.ker_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：ker_eq_bot_iff (f : G ->* M) : f.ker = ⊥ ↔ Function.Injective f
参数：f : G ->* M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `inv_mul_eq_one`：inv_mul_eq_one : a⁻¹ * b = 1 ↔ a = b
· 使用定理 `Subgroup.mem_bot`：mem_bot {x : G} : x in (⊥ : Subgroup G) ↔ x = 1
· 使用定理 `MonoidHom.eq_iff`：eq_iff (f : G ->* M) {x y : G} : f x = f y ↔ y⁻¹ * x i
n f.ker
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.map_one`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N), f 1 = 1
-/
theorem ker_eq_bot_iff (f : G →* M) : f.ker = ⊥ ↔ Function.Injective f :=
  ⟨fun h x y hxy => by rwa [eq_iff, h, mem_bot, inv_mul_eq_one, eq_comm] at hxy, fun h =>
    bot_unique fun _ hx => h (hx.trans f.map_one.symm)⟩

@[to_additive]
/-
**MonoidHom.ker_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：ker_eq_bot (f : G ->* M) (hf : Function.Injective f) : f.ker = ⊥
参数：f : G ->* M；hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MonoidHom.ker_eq_bot_iff`：ker_eq_bot_iff (f : G ->* M) : f.ker = ⊥ ↔ Fun
ction.Injective f
-/
theorem ker_eq_bot (f : G →* M) (hf : Function.Injective f) : f.ker = ⊥ :=
  f.ker_eq_bot_iff.mpr hf

/-- The kernel of a homomorphism composed with an isomorphism is equal to the kernel of
the homomorphism mapped by the inverse isomorphism. -/
@[to_additive (attr := simp)]
/-
**MonoidHom.ker_comp_mulEquiv** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：ker_comp_mulEquiv {P : Type*} [MulOneClass P] (g : N ->* P) (iso : G ≃* N)
 : (g.comp iso).ker = map (iso.symm : N ->* G) g.ker
参数：g : N ->* P；iso : G ≃* N。
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
· 使用定理 `MonoidHom.comap_ker`：comap_ker {P : Type*} [MulOneClass P] (g : N ->* P)
 (f : G ->* N) : g.ker.comap f = (g.comp f).ker
· 使用定理 `Subgroup.comap_equiv_eq_map_symm`：comap_equiv_eq_map_symm (f : N ≃* G) (
K : Subgroup G) : K.comap (G

--- 原说明 ---
The kernel of a homomorphism composed with an isomorphism is equal to the kernel
 of
the homomorphism mapped by the inverse isomorphism.
-/
lemma ker_comp_mulEquiv {P : Type*} [MulOneClass P] (g : N →* P) (iso : G ≃* N) :
    (g.comp iso).ker = map (iso.symm : N →* G) g.ker := by
  rw [← comap_ker, comap_equiv_eq_map_symm]

/-- Composing with an injective homomorphism on the codomain does not change the kernel. -/
@[to_additive]
/-
**MonoidHom.ker_comp_of_injective** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：ker_comp_of_injective {P : Type*} [MulOneClass P] (f : G ->* N) (g : N ->*
 P) (hg : Function.Injective g) : (g.comp f).ker = f.ker
参数：f : G ->* N；g : N ->* P；hg : Function.Injective g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.comap_ker`：comap_ker {P : Type*} [MulOneClass P] (g : N ->* P)
 (f : G ->* N) : g.ker.comap f = (g.comp f).ker
· 使用定理 `MonoidHom.ker_eq_bot`：ker_eq_bot (f : G ->* M) (hf : Function.Injective 
f) : f.ker = ⊥
· 使用定理 `MonoidHom.comap_bot`：comap_bot (f : G ->* N) : (⊥ : Subgroup N).comap f 
= f.ker

--- 原说明 ---
Composing with an injective homomorphism on the codomain does not change the ker
nel.
-/
lemma ker_comp_of_injective {P : Type*} [MulOneClass P] (f : G →* N) (g : N →* P)
    (hg : Function.Injective g) : (g.comp f).ker = f.ker := by
  rw [← comap_ker, g.ker_eq_bot hg, comap_bot]

/-- Composing with an isomorphism on the codomain does not change the kernel. -/
@[to_additive (attr := simp)]
/-
**MonoidHom.ker_mulEquiv_comp** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：ker_mulEquiv_comp {P : Type*} [MulOneClass P] (f : G ->* N) (iso : N ≃* P)
 : ((iso : N ->* P).comp f).ker = f.ker
参数：f : G ->* N；iso : N ≃* P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidHom.ker_comp_of_injective`：ker_comp_of_injective {P : Type*} [MulO
neClass P] (f : G ->* N) (g : N ->* P) (hg : Function.Injective g) : (g.comp f).
ker = f.ker
· 使用定理 `MulEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst
_1 : Mul N] (e : M ≃* N), Function.Injective ⇑e

--- 原说明 ---
Composing with an isomorphism on the codomain does not change the kernel.
-/
lemma ker_mulEquiv_comp {P : Type*} [MulOneClass P] (f : G →* N) (iso : N ≃* P) :
    ((iso : N →* P).comp f).ker = f.ker :=
  ker_comp_of_injective f iso.toMonoidHom iso.injective

@[to_additive (attr := simp)]
/-
**MonoidHom._root_.Subgroup.ker_subtype** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Subgroup.ker_subtype (H : Subgroup G) : H.subtype.ker = ⊥ :=
  H.subtype.ker_eq_bot Subtype.coe_injective

@[to_additive (attr := simp)]
/-
**MonoidHom._root_.Subgroup.ker_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Subgroup.ker_inclusion {H K : Subgroup G} (h : H ≤ K) : (inclusion h).ker = ⊥ :=
  (inclusion h).ker_eq_bot (Set.inclusion_injective h)

@[to_additive ker_prod]
/-
**MonoidHom.ker_prod** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：ker_prod {M N : Type*} [MulOneClass M] [MulOneClass N] (f : G ->* M) (g : 
G ->* N) : (f.prod g).ker = f.ker ⊓ g.ker
参数：f : G ->* M；g : G ->* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Prod.mk_eq_one`：mk_eq_one {x : M} {y : N} : (x, y) = 1 ↔ x = 1 ∧ y = 1
-/
theorem ker_prod {M N : Type*} [MulOneClass M] [MulOneClass N] (f : G →* M) (g : G →* N) :
    (f.prod g).ker = f.ker ⊓ g.ker :=
  SetLike.ext fun _ => Prod.mk_eq_one

@[to_additive]
/-
**MonoidHom.range_le_ker_iff** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：range_le_ker_iff (f : G ->* G') (g : G' ->* M) : f.range <= g.ker ↔ g.comp
 f = 1
参数：f : G ->* G'；g : G' ->* M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem range_le_ker_iff (f : G →* G') (g : G' →* M) : f.range ≤ g.ker ↔ g.comp f = 1 :=
  ⟨fun h => ext fun x => h ⟨x, rfl⟩, by rintro h _ ⟨y, rfl⟩; exact DFunLike.congr_fun h y⟩

@[to_additive]
/-
**MonoidHom.** 是 Mathlib 中的一个实例，位于命名空间 `MonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) normal_ker (f : G →* M) : f.ker.Normal :=
  ⟨fun x hx y => by
    rw [mem_ker, map_mul, map_mul, mem_ker.1 hx, mul_one, map_mul_eq_one f (mul_inv_cancel y)]⟩

@[simp]
/-
**MonoidHom.coe_toAdditive_ker** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：coe_toAdditive_ker (f : G ->* G') : (MonoidHom.toAdditive f).ker = Subgrou
p.toAddSubgroup f.ker
参数：f : G ->* G'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toAdditive_ker (f : G →* G') :
    (MonoidHom.toAdditive f).ker = Subgroup.toAddSubgroup f.ker := rfl

@[simp]
/-
**MonoidHom.coe_toMultiplicative_ker** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：coe_toMultiplicative_ker {A A' : Type*} [AddGroup A] [AddZeroClass A'] (f 
: A ->+ A') : (AddMonoidHom.toMultiplicative f).ker = AddSubgroup.toSubgroup f.k
er
参数：f : A ->+ A'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toMultiplicative_ker {A A' : Type*} [AddGroup A] [AddZeroClass A'] (f : A →+ A') :
    (AddMonoidHom.toMultiplicative f).ker = AddSubgroup.toSubgroup f.ker := rfl

end Ker

section EqLocus

variable {M : Type*} [Monoid M]

/-- The subgroup of elements `x : G` such that `f x = g x` -/
@[to_additive /-- The additive subgroup of elements `x : G` such that `f x = g x` -/]
/-
**MonoidHom.eqLocus** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：eqLocus (f g : G ->* M) : Subgroup G
参数：f g : G ->* M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subgroup of elements `x : G` such that `f x = g x`
-/
def eqLocus (f g : G →* M) : Subgroup G :=
  { eqLocusM f g with inv_mem' := eq_on_inv f g }

@[to_additive (attr := simp)]
/-
**MonoidHom.eqLocus_same** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：eqLocus_same (f : G ->* N) : f.eqLocus f = ⊤
参数：f : G ->* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `eq_self_iff_true`：∀ {α : Sort u_1} (a : α), a = a ↔ True
-/
theorem eqLocus_same (f : G →* N) : f.eqLocus f = ⊤ :=
  SetLike.ext fun _ => eq_self_iff_true _

/-- If two monoid homomorphisms are equal on a set, then they are equal on its subgroup closure. -/
@[to_additive
      /-- If two monoid homomorphisms are equal on a set, then they are equal on its subgroup
      closure. -/]
/-
**MonoidHom.eqOn_closure** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：eqOn_closure {f g : G ->* M} {s : Set G} (h : Set.EqOn f g s) : Set.EqOn f
 g (closure s)
参数：h : Set.EqOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.closure_le`：closure_le : closure k <= K ↔ k subseteq K
-/
theorem eqOn_closure {f g : G →* M} {s : Set G} (h : Set.EqOn f g s) : Set.EqOn f g (closure s) :=
  show closure s ≤ f.eqLocus g from (closure_le _).2 h

@[to_additive]
/-
**MonoidHom.eq_of_eqOn_top** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：eq_of_eqOn_top {f g : G ->* M} (h : Set.EqOn f g (⊤ : Subgroup G)) : f = g
参数：h : Set.EqOn f g (⊤ : Subgroup G)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `trivial`：True
-/
theorem eq_of_eqOn_top {f g : G →* M} (h : Set.EqOn f g (⊤ : Subgroup G)) : f = g :=
  ext fun _x => h trivial

@[to_additive]
/-
**MonoidHom.eq_of_eqOn_dense** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：eq_of_eqOn_dense {s : Set G} (hs : closure s = ⊤) {f g : G ->* M} (h : s.E
qOn f g) : f = g
参数：hs : closure s = ⊤；h : s.EqOn f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.eq_of_eqOn_top`：eq_of_eqOn_top {f g : G ->* M} (h : Set.EqOn f
 g (⊤ : Subgroup G)) : f = g
· 使用定理 `MonoidHom.eqOn_closure`：eqOn_closure {f g : G ->* M} {s : Set G} (h : Se
t.EqOn f g s) : Set.EqOn f g (closure s)
-/
theorem eq_of_eqOn_dense {s : Set G} (hs : closure s = ⊤) {f g : G →* M} (h : s.EqOn f g) : f = g :=
  eq_of_eqOn_top <| hs ▸ eqOn_closure h

end EqLocus

end MonoidHom

namespace Subgroup

variable {N : Type*} [Group N] (H : Subgroup G)

@[to_additive]
/-
**Subgroup.map_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_eq_bot_iff {f : G ->* N} : H.map f = ⊥ ↔ H <= f.ker
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_eq_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOr
der α] [inst_1 : Preorder β] [inst_2 : OrderBot α] {u : α → β} {l : β → α},   Ga
loisConnection …
· 使用定理 `Subgroup.gc_map_comap`：gc_map_comap (f : G ->* N) : GaloisConnection (ma
p f) (comap f)
-/
theorem map_eq_bot_iff {f : G →* N} : H.map f = ⊥ ↔ H ≤ f.ker :=
  (gc_map_comap f).l_eq_bot

@[to_additive]
/-
**Subgroup.map_eq_bot_iff_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_eq_bot_iff_of_injective {f : G ->* N} (hf : Function.Injective f) : H.
map f = ⊥ ↔ H = ⊥
参数：hf : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.map_eq_bot_iff`：map_eq_bot_iff {f : G ->* N} : H.map f = ⊥ ↔ H 
<= f.ker
· 使用定理 `MonoidHom.ker_eq_bot`：ker_eq_bot (f : G ->* M) (hf : Function.Injective 
f) : f.ker = ⊥
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem map_eq_bot_iff_of_injective {f : G →* N} (hf : Function.Injective f) :
    H.map f = ⊥ ↔ H = ⊥ := by rw [map_eq_bot_iff, f.ker_eq_bot hf, le_bot_iff]

@[to_additive (attr := simp)]
/-
**Subgroup.map_ker_self** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_ker_self (f : G ->* N) : f.ker.map f = ⊥
参数：f : G ->* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.map_eq_bot_iff`：map_eq_bot_iff {f : G ->* N} : H.map f = ⊥ ↔ H 
<= f.ker
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem map_ker_self (f : G →* N) : f.ker.map f = ⊥ := by
  rw [map_eq_bot_iff]

open MonoidHom

variable (f : G →* N)

@[to_additive]
/-
**Subgroup.map_le_range** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_le_range (H : Subgroup G) : map f H <= f.range
参数：H : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.map_mono`：map_mono {f : G ->* N} {K K' : Subgroup G} : K <= K' 
-> map f K <= map f K'
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.range_eq_map`：range_eq_map (f : G ->* N) : f.range = (⊤ : Subg
roup G).map f
-/
theorem map_le_range (H : Subgroup G) : map f H ≤ f.range :=
  (range_eq_map f).symm ▸ map_mono le_top

@[to_additive]
/-
**Subgroup.map_subtype_le** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_subtype_le {H : Subgroup G} (K : Subgroup H) : K.map H.subtype <= H
参数：K : Subgroup H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Subgroup.map_le_range`：map_le_range (H : Subgroup G) : map f H <= f.rang
e
· 使用定理 `Subgroup.range_subtype`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup 
G), H.subtype.range = H
-/
theorem map_subtype_le {H : Subgroup G} (K : Subgroup H) : K.map H.subtype ≤ H :=
  (K.map_le_range H.subtype).trans_eq H.range_subtype

@[to_additive]
/-
**Subgroup.ker_le_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：ker_le_comap (H : Subgroup N) : f.ker <= comap f H
参数：H : Subgroup N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.comap_mono`：comap_mono {f : G ->* N} {K K' : Subgroup N} : K <=
 K' -> comap f K <= comap f K'
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `MonoidHom.comap_bot`：comap_bot (f : G ->* N) : (⊥ : Subgroup N).comap f 
= f.ker
-/
theorem ker_le_comap (H : Subgroup N) : f.ker ≤ comap f H :=
  comap_bot f ▸ comap_mono bot_le

@[to_additive]
/-
**Subgroup.map_comap_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_comap_eq (H : Subgroup N) : map f (comap f H) = f.range ⊓ H
参数：H : Subgroup N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.coe_map`：coe_map (f : G ->* N) (K : Subgroup G) : (K.map f : Se
t N) = f '' K
· 使用定理 `Subgroup.coe_comap`：coe_comap (K : Subgroup N) (f : G ->* N) : (K.comap 
f : Set G) = f ⁻¹' K
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Subgroup.coe_inf`：coe_inf (p p' : Subgroup G) : ((p ⊓ p' : Subgroup G) :
 Set G) = (p : Set G) inter p'
· 使用定理 `MonoidHom.coe_range`：coe_range (f : G ->* N) : (f.range : Set N) = Set.r
ange f
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
-/
theorem map_comap_eq (H : Subgroup N) : map f (comap f H) = f.range ⊓ H :=
  SetLike.ext' <| by
    rw [coe_map, coe_comap, Set.image_preimage_eq_inter_range, coe_inf, coe_range, Set.inter_comm]

@[to_additive]
/-
**Subgroup.comap_map_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：comap_map_eq (H : Subgroup G) : comap f (map f H) = H ⊔ f.ker
参数：H : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `Subgroup.mul_mem_sup`：mul_mem_sup {S T : Subgroup G} {x y : G} (hx : x i
n S) (hy : y in T) : x * y in S ⊔ T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `Subgroup.le_comap_map`：le_comap_map (H : Subgroup G) : H <= comap f (map
 f H)
· 使用定理 `Subgroup.ker_le_comap`：ker_le_comap (H : Subgroup N) : f.ker <= comap f 
H
-/
theorem comap_map_eq (H : Subgroup G) : comap f (map f H) = H ⊔ f.ker := by
  refine le_antisymm ?_ (sup_le (le_comap_map _ _) (ker_le_comap _ _))
  intro x hx; simp only [mem_map, mem_comap] at hx
  rcases hx with ⟨y, hy, hy'⟩
  rw [← mul_inv_cancel_left y x]
  exact mul_mem_sup hy (by simp [mem_ker, hy'])

@[to_additive]
/-
**Subgroup.map_comap_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_comap_eq_self {f : G ->* N} {H : Subgroup N} (h : H <= f.range) : map 
f (comap f H) = H
参数：h : H <= f.range。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.map_comap_eq`：map_comap_eq (H : Subgroup N) : map f (comap f H)
 = f.range ⊓ H
· 使用定理 `inf_eq_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= b ↔ b ≤ a
-/
theorem map_comap_eq_self {f : G →* N} {H : Subgroup N} (h : H ≤ f.range) :
    map f (comap f H) = H := by
  rwa [map_comap_eq, inf_eq_right]

@[to_additive]
/-
**Subgroup.map_comap_eq_self_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_comap_eq_self_of_surjective {f : G ->* N} (h : Function.Surjective f) 
(H : Subgroup N) : map f (comap f H) = H
参数：h : Function.Surjective f；H : Subgroup N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.map_comap_eq_self`：map_comap_eq_self {f : G ->* N} {H : Subgrou
p N} (h : H <= f.range) : map f (comap f H) = H
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MonoidHom.range_eq_top`：range_eq_top {N} [Group N] {f : G ->* N} : f.ran
ge = (⊤ : Subgroup N) ↔ Function.Surjective f
-/
theorem map_comap_eq_self_of_surjective {f : G →* N} (h : Function.Surjective f) (H : Subgroup N) :
    map f (comap f H) = H :=
  map_comap_eq_self (range_eq_top.2 h ▸ le_top)

@[to_additive]
/-
**Subgroup.comap_le_comap_of_le_range** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：comap_le_comap_of_le_range {f : G ->* N} {K L : Subgroup N} (hf : K <= f.r
ange) : K.comap f <= L.comap f ↔ K <= L
参数：hf : K <= f.range。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Subgroup.map_comap_eq_self`：map_comap_eq_self {f : G ->* N} {H : Subgrou
p N} (h : H <= f.range) : map f (comap f H) = H
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.map_le_iff_le_comap`：map_le_iff_le_comap {f : G ->* N} {K : Sub
group G} {H : Subgroup N} : K.map f <= H ↔ K <= H.comap f
· 使用定理 `Subgroup.comap_mono`：comap_mono {f : G ->* N} {K K' : Subgroup N} : K <=
 K' -> comap f K <= comap f K'
-/
theorem comap_le_comap_of_le_range {f : G →* N} {K L : Subgroup N} (hf : K ≤ f.range) :
    K.comap f ≤ L.comap f ↔ K ≤ L :=
  ⟨(map_comap_eq_self hf).ge.trans ∘ map_le_iff_le_comap.mpr, comap_mono⟩

@[to_additive]
/-
**Subgroup.comap_le_comap_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：comap_le_comap_of_surjective {f : G ->* N} {K L : Subgroup N} (hf : Functi
on.Surjective f) : K.comap f <= L.comap f ↔ K <= L
参数：hf : Function.Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.comap_le_comap_of_le_range`：comap_le_comap_of_le_range {f : G -
>* N} {K L : Subgroup N} (hf : K <= f.range) : K.comap f <= L.comap f ↔ K <= L
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MonoidHom.range_eq_top`：range_eq_top {N} [Group N] {f : G ->* N} : f.ran
ge = (⊤ : Subgroup N) ↔ Function.Surjective f
-/
theorem comap_le_comap_of_surjective {f : G →* N} {K L : Subgroup N} (hf : Function.Surjective f) :
    K.comap f ≤ L.comap f ↔ K ≤ L :=
  comap_le_comap_of_le_range (range_eq_top.2 hf ▸ le_top)

@[to_additive]
/-
**Subgroup.comap_lt_comap_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：comap_lt_comap_of_surjective {f : G ->* N} {K L : Subgroup N} (hf : Functi
on.Surjective f) : K.comap f < L.comap f ↔ K < L
参数：hf : Function.Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subgroup.comap_le_comap_of_surjective`：comap_le_comap_of_surjective {f :
 G ->* N} {K L : Subgroup N} (hf : Function.Surjective f) : K.comap f <= L.comap
 f ↔ K <= L
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem comap_lt_comap_of_surjective {f : G →* N} {K L : Subgroup N} (hf : Function.Surjective f) :
    K.comap f < L.comap f ↔ K < L := by simp_rw [lt_iff_le_not_ge, comap_le_comap_of_surjective hf]

@[to_additive]
/-
**Subgroup.comap_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：comap_injective {f : G ->* N} (h : Function.Surjective f) : Function.Injec
tive (comap f)
参数：h : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.comap_le_comap_of_surjective`：comap_le_comap_of_surjective {f :
 G ->* N} {K L : Subgroup N} (hf : Function.Surjective f) : K.comap f <= L.comap
 f ↔ K <= L
-/
theorem comap_injective {f : G →* N} (h : Function.Surjective f) : Function.Injective (comap f) :=
  fun K L => by simp only [le_antisymm_iff, comap_le_comap_of_surjective h, imp_self]

@[to_additive (attr := simp)]
/-
**Subgroup.comap_eq_ker** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：comap_eq_ker {f : G ->* N} {H : Subgroup N} : H.comap f = f.ker ↔ Disjoint
 H f.range
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.ge_iff_eq'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (a ≤ b ↔ a = b)
· 使用定理 `Subgroup.ker_le_comap`：ker_le_comap (H : Subgroup N) : f.ker <= comap f 
H
· 使用定理 `Subgroup.map_eq_bot_iff`：map_eq_bot_iff {f : G ->* N} : H.map f = ⊥ ↔ H 
<= f.ker
· 使用定理 `Subgroup.map_comap_eq`：map_comap_eq (H : Subgroup N) : map f (comap f H)
 = f.range ⊓ H
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem comap_eq_ker {f : G →* N} {H : Subgroup N} : H.comap f = f.ker ↔ Disjoint H f.range := by
  rw [← H.ker_le_comap f |>.ge_iff_eq', ← map_eq_bot_iff, map_comap_eq, disjoint_iff, inf_comm]

@[to_additive]
/-
**Subgroup.comap_eq_ker_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：comap_eq_ker_of_surjective {f : G ->* N} (hf : Surjective f) {H : Subgroup
 N} : H.comap f = f.ker ↔ H = ⊥
参数：hf : Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.comap_eq_ker`：comap_eq_ker {f : G ->* N} {H : Subgroup N} : H.c
omap f = f.ker ↔ Disjoint H f.range
· 使用定理 `MonoidHom.range_eq_top_of_surjective`：range_eq_top_of_surjective {N} [Gr
oup N] (f : G ->* N) (hf : Function.Surjective f) : f.range = (⊤ : Subgroup N)
· 使用定理 `disjoint_top`：disjoint_top : Disjoint a ⊤ ↔ a = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem comap_eq_ker_of_surjective {f : G →* N} (hf : Surjective f) {H : Subgroup N} :
    H.comap f = f.ker ↔ H = ⊥ := by
  rw [comap_eq_ker, f.range_eq_top_of_surjective hf, disjoint_top]

@[to_additive]
/-
**Subgroup.comap_map_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：comap_map_eq_self {f : G ->* N} {H : Subgroup G} (h : f.ker <= H) : comap 
f (map f H) = H
参数：h : f.ker <= H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.comap_map_eq`：comap_map_eq (H : Subgroup G) : comap f (map f H)
 = H ⊔ f.ker
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
-/
theorem comap_map_eq_self {f : G →* N} {H : Subgroup G} (h : f.ker ≤ H) :
    comap f (map f H) = H := by
  rwa [comap_map_eq, sup_eq_left]

@[to_additive]
/-
**Subgroup.comap_map_eq_self_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：comap_map_eq_self_of_injective {f : G ->* N} (h : Function.Injective f) (H
 : Subgroup G) : comap f (map f H) = H
参数：h : Function.Injective f；H : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.comap_map_eq_self`：comap_map_eq_self {f : G ->* N} {H : Subgrou
p G} (h : f.ker <= H) : comap f (map f H) = H
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.ker_eq_bot`：ker_eq_bot (f : G ->* M) (hf : Function.Injective 
f) : f.ker = ⊥
-/
theorem comap_map_eq_self_of_injective {f : G →* N} (h : Function.Injective f) (H : Subgroup G) :
    comap f (map f H) = H :=
  comap_map_eq_self ((ker_eq_bot _ h).symm ▸ bot_le)

@[to_additive]
/-
**Subgroup.map_le_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_le_map_iff {f : G ->* N} {H K : Subgroup G} : H.map f <= K.map f ↔ H <
= K ⊔ f.ker
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.map_le_iff_le_comap`：map_le_iff_le_comap {f : G ->* N} {K : Sub
group G} {H : Subgroup N} : K.map f <= H ↔ K <= H.comap f
· 使用定理 `Subgroup.comap_map_eq`：comap_map_eq (H : Subgroup G) : comap f (map f H)
 = H ⊔ f.ker
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem map_le_map_iff {f : G →* N} {H K : Subgroup G} : H.map f ≤ K.map f ↔ H ≤ K ⊔ f.ker := by
  rw [map_le_iff_le_comap, comap_map_eq]

@[to_additive]
/-
**Subgroup.map_le_map_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_le_map_iff' {f : G ->* N} {H K : Subgroup G} : H.map f <= K.map f ↔ H 
⊔ f.ker <= K ⊔ f.ker
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_le_map_iff' {f : G →* N} {H K : Subgroup G} :
    H.map f ≤ K.map f ↔ H ⊔ f.ker ≤ K ⊔ f.ker := by
  simp only [map_le_map_iff, sup_le_iff, le_sup_right, and_true]

@[to_additive]
/-
**Subgroup.map_eq_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_eq_map_iff {f : G ->* N} {H K : Subgroup G} : H.map f = K.map f ↔ H ⊔ 
f.ker = K ⊔ f.ker
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
theorem map_eq_map_iff {f : G →* N} {H K : Subgroup G} :
    H.map f = K.map f ↔ H ⊔ f.ker = K ⊔ f.ker := by simp only [le_antisymm_iff, map_le_map_iff']

@[to_additive]
/-
**Subgroup.map_eq_range_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_eq_range_iff {f : G ->* N} {H : Subgroup G} : H.map f = f.range ↔ Codi
sjoint H f.ker
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.range_eq_map`：range_eq_map (f : G ->* N) : f.range = (⊤ : Subg
roup G).map f
· 使用定理 `Subgroup.map_eq_map_iff`：map_eq_map_iff {f : G ->* N} {H K : Subgroup G}
 : H.map f = K.map f ↔ H ⊔ f.ker = K ⊔ f.ker
· 使用定理 `codisjoint_iff`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : Ord
erTop α] {a b : α}, Codisjoint a b ↔ a ⊔ b = ⊤
· 使用定理 `top_sup_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderTo
p α] (a : α), ⊤ ⊔ a = ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem map_eq_range_iff {f : G →* N} {H : Subgroup G} :
    H.map f = f.range ↔ Codisjoint H f.ker := by
  rw [f.range_eq_map, map_eq_map_iff, codisjoint_iff, top_sup_eq]

@[to_additive]
/-
**Subgroup.map_le_map_iff_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_le_map_iff_of_injective {f : G ->* N} (hf : Function.Injective f) {H K
 : Subgroup G} : H.map f <= K.map f ↔ H <= K
参数：hf : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.map_le_iff_le_comap`：map_le_iff_le_comap {f : G ->* N} {K : Sub
group G} {H : Subgroup N} : K.map f <= H ↔ K <= H.comap f
· 使用定理 `Subgroup.comap_map_eq_self_of_injective`：comap_map_eq_self_of_injective 
{f : G ->* N} (h : Function.Injective f) (H : Subgroup G) : comap f (map f H) = 
H
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem map_le_map_iff_of_injective {f : G →* N} (hf : Function.Injective f) {H K : Subgroup G} :
    H.map f ≤ K.map f ↔ H ≤ K := by rw [map_le_iff_le_comap, comap_map_eq_self_of_injective hf]

@[to_additive (attr := simp)]
/-
**Subgroup.map_subtype_le_map_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_subtype_le_map_subtype {G' : Subgroup G} {H K : Subgroup G'} : H.map G
'.subtype <= K.map G'.subtype ↔ H <= K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.map_le_map_iff_of_injective`：map_le_map_iff_of_injective {f : G
 ->* N} (hf : Function.Injective f) {H K : Subgroup G} : H.map f <= K.map f ↔ H 
<= K
· 使用引理 `Subgroup.subtype_injective`：subtype_injective (s : Subgroup G) : Functio
n.Injective s.subtype
-/
theorem map_subtype_le_map_subtype {G' : Subgroup G} {H K : Subgroup G'} :
    H.map G'.subtype ≤ K.map G'.subtype ↔ H ≤ K :=
  map_le_map_iff_of_injective G'.subtype_injective

set_option backward.isDefEq.respectTransparency false in
/-- Subgroups of the subgroup `H` are considered as subgroups that are less than or equal to
`H`. -/
@[to_additive (attr := simps apply_coe) /-- Additive subgroups of the subgroup `H` are considered as
additive subgroups that are less than or equal to `H`. -/]
/-
**Subgroup.MapSubtype.orderIso** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup.MapSubtype`。
形式化陈述：{G : Type u_1} → [inst : Group G] → (H : Subgroup G) → Subgroup ↥H ≃o { H'
 // H' ≤ H }
参数：H : Subgroup G。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.map_subtype_le`：map_subtype_le {H : Subgroup G} (K : Subgroup H
) : K.map H.subtype <= H
-/
def MapSubtype.orderIso (H : Subgroup G) : Subgroup ↥H ≃o { H' : Subgroup G // H' ≤ H } where
  toFun H' := ⟨H'.map H.subtype, map_subtype_le H'⟩
  invFun sH' := sH'.1.subgroupOf H
  left_inv H' := comap_map_eq_self_of_injective H.subtype_injective H'
  right_inv sH' := Subtype.ext (map_subgroupOf_eq_of_le sH'.2)
  map_rel_iff' := by simp

@[to_additive (attr := simp)]
/-
**Subgroup.MapSubtype.orderIso_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.Ma
pSubtype`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) (sH' : { H' // H' ≤ H }
),   (Subgroup.MapSubtype.orderIso H).symm sH' = (↑sH').subgroupOf H
参数：H : Subgroup G；sH' : { H' // H' ≤ H }；Subgroup.MapSubtype.orderIso H；↑sH'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma MapSubtype.orderIso_symm_apply (H : Subgroup G) (sH' : { H' : Subgroup G // H' ≤ H }) :
    (MapSubtype.orderIso H).symm sH' = sH'.1.subgroupOf H :=
  rfl

@[to_additive]
/-
**Subgroup.** 是 Mathlib 中的一个引理，位于命名空间 `Subgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma «forall» {H : Subgroup G} {P : Subgroup H → Prop} :
    (∀ H' : Subgroup H, P H') ↔ (∀ H' ≤ H, P (H'.subgroupOf H)) := by
  simp [(MapSubtype.orderIso H).forall_congr_left]

@[to_additive]
/-
**Subgroup.map_lt_map_iff_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_lt_map_iff_of_injective {f : G ->* N} (hf : Function.Injective f) {H K
 : Subgroup G} : H.map f < K.map f ↔ H < K
参数：hf : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le'`：lt_iff_lt_of_le_iff_le' {β} [Preorder α] [Preor
der β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) (H' : b <= a ↔ d <= c) : b < a 
↔ d < c
· 使用定理 `Subgroup.map_le_map_iff_of_injective`：map_le_map_iff_of_injective {f : G
 ->* N} (hf : Function.Injective f) {H K : Subgroup G} : H.map f <= K.map f ↔ H 
<= K
-/
theorem map_lt_map_iff_of_injective {f : G →* N} (hf : Function.Injective f) {H K : Subgroup G} :
    H.map f < K.map f ↔ H < K :=
  lt_iff_lt_of_le_iff_le' (map_le_map_iff_of_injective hf) (map_le_map_iff_of_injective hf)

@[to_additive (attr := simp)]
/-
**Subgroup.map_subtype_lt_map_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_subtype_lt_map_subtype {G' : Subgroup G} {H K : Subgroup G'} : H.map G
'.subtype < K.map G'.subtype ↔ H < K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.map_lt_map_iff_of_injective`：map_lt_map_iff_of_injective {f : G
 ->* N} (hf : Function.Injective f) {H K : Subgroup G} : H.map f < K.map f ↔ H <
 K
· 使用引理 `Subgroup.subtype_injective`：subtype_injective (s : Subgroup G) : Functio
n.Injective s.subtype
-/
theorem map_subtype_lt_map_subtype {G' : Subgroup G} {H K : Subgroup G'} :
    H.map G'.subtype < K.map G'.subtype ↔ H < K :=
  map_lt_map_iff_of_injective G'.subtype_injective

@[to_additive]
/-
**Subgroup.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_injective {f : G ->* N} (h : Function.Injective f) : Function.Injectiv
e (map f)
参数：h : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `Subgroup.comap_map_eq_self_of_injective`：comap_map_eq_self_of_injective 
{f : G ->* N} (h : Function.Injective f) (H : Subgroup G) : comap f (map f H) = 
H
-/
theorem map_injective {f : G →* N} (h : Function.Injective f) : Function.Injective (map f) :=
  Function.LeftInverse.injective <| comap_map_eq_self_of_injective h

@[to_additive]
/-
**Subgroup.map_subtype_inj** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_subtype_inj {H : Subgroup G} {K L : Subgroup H} : K.map H.subtype = L.
map H.subtype ↔ K = L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Subgroup.map_injective`：map_injective {f : G ->* N} (h : Function.Inject
ive f) : Function.Injective (map f)
· 使用引理 `Subgroup.subtype_injective`：subtype_injective (s : Subgroup G) : Functio
n.Injective s.subtype
-/
theorem map_subtype_inj {H : Subgroup G} {K L : Subgroup H} :
    K.map H.subtype = L.map H.subtype ↔ K = L :=
  (map_injective H.subtype_injective).eq_iff

/-- Given `f(A) = f(B)`, `ker f ≤ A`, and `ker f ≤ B`, deduce that `A = B`. -/
@[to_additive /-- Given `f(A) = f(B)`, `ker f ≤ A`, and `ker f ≤ B`, deduce that `A = B`. -/]
/-
**Subgroup.map_injective_of_ker_le** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：map_injective_of_ker_le {H K : Subgroup G} (hH : f.ker <= H) (hK : f.ker <
= K) (hf : map f H = map f K) : H = K
参数：hH : f.ker <= H；hK : f.ker <= K；hf : map f H = map f K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `Subgroup.comap_map_eq`：comap_map_eq (H : Subgroup G) : comap f (map f H)
 = H ⊔ f.ker
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Given `f(A) = f(B)`, `ker f ≤ A`, and `ker f ≤ B`, deduce that `A = B`.
-/
theorem map_injective_of_ker_le {H K : Subgroup G} (hH : f.ker ≤ H) (hK : f.ker ≤ K)
    (hf : map f H = map f K) : H = K := by
  apply_fun comap f at hf
  rwa [comap_map_eq, comap_map_eq, sup_of_le_left hH, sup_of_le_left hK] at hf

@[to_additive]
/-
**Subgroup.ker_subgroupMap** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：ker_subgroupMap : (f.subgroupMap H).ker = f.ker.subgroupOf H
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
theorem ker_subgroupMap : (f.subgroupMap H).ker = f.ker.subgroupOf H :=
  ext fun _ ↦ Subtype.ext_iff

@[to_additive]
/-
**Subgroup.closure_preimage_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：closure_preimage_eq_top (s : Set G) : closure ((closure s).subtype ⁻¹' s) 
= ⊤
参数：s : Set G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.closure_closure_coe_preimage`：closure_closure_coe_preimage {k :
 Set G} : closure (((↑) : closure k -> G) ⁻¹' k) = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem closure_preimage_eq_top (s : Set G) : closure ((closure s).subtype ⁻¹' s) = ⊤ := by
  simp

@[to_additive]
/-
**Subgroup.comap_sup_eq_of_le_range** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：comap_sup_eq_of_le_range {H K : Subgroup N} (hH : H <= f.range) (hK : K <=
 f.range) : comap f H ⊔ comap f K = comap f (H ⊔ K)
参数：hH : H <= f.range；hK : K <= f.range。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.map_injective_of_ker_le`：map_injective_of_ker_le {H K : Subgrou
p G} (hH : f.ker <= H) (hK : f.ker <= K) (hf : map f H = map f K) : H = K
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Subgroup.ker_le_comap`：ker_le_comap (H : Subgroup N) : f.ker <= comap f 
H
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.map_comap_eq`：map_comap_eq (H : Subgroup N) : map f (comap f H)
 = f.range ⊓ H
· 使用定理 `Subgroup.map_sup`：map_sup (H K : Subgroup G) (f : G ->* N) : (H ⊔ K).map
 f = H.map f ⊔ K.map f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inf_eq_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= b ↔ b ≤ a
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
-/
theorem comap_sup_eq_of_le_range {H K : Subgroup N} (hH : H ≤ f.range) (hK : K ≤ f.range) :
    comap f H ⊔ comap f K = comap f (H ⊔ K) :=
  map_injective_of_ker_le f ((ker_le_comap f H).trans le_sup_left) (ker_le_comap f (H ⊔ K))
    (by
      rw [map_comap_eq, map_sup, map_comap_eq, map_comap_eq, inf_eq_right.mpr hH,
        inf_eq_right.mpr hK, inf_eq_right.mpr (sup_le hH hK)])

@[to_additive]
/-
**Subgroup.comap_sup_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：comap_sup_eq (H K : Subgroup N) (hf : Function.Surjective f) : comap f H ⊔
 comap f K = comap f (H ⊔ K)
参数：H K : Subgroup N；hf : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.comap_sup_eq_of_le_range`：comap_sup_eq_of_le_range {H K : Subgr
oup N} (hH : H <= f.range) (hK : K <= f.range) : comap f H ⊔ comap f K = comap f
 (H ⊔ K)
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MonoidHom.range_eq_top`：range_eq_top {N} [Group N] {f : G ->* N} : f.ran
ge = (⊤ : Subgroup N) ↔ Function.Surjective f
-/
theorem comap_sup_eq (H K : Subgroup N) (hf : Function.Surjective f) :
    comap f H ⊔ comap f K = comap f (H ⊔ K) :=
  comap_sup_eq_of_le_range f (range_eq_top.2 hf ▸ le_top) (range_eq_top.2 hf ▸ le_top)

@[to_additive]
/-
**Subgroup.subgroupOf_sup** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：subgroupOf_sup {A A' B : Subgroup G} (hA : A <= B) (hA' : A' <= B) : (A ⊔ 
A').subgroupOf B = A.subgroupOf B ⊔ A'.subgroupOf B
参数：hA : A <= B；hA' : A' <= B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.map_injective_of_ker_le`：map_injective_of_ker_le {H K : Subgrou
p G} (hH : f.ker <= H) (hK : f.ker <= K) (hf : map f H = map f K) : H = K
· 使用定理 `Subgroup.ker_le_comap`：ker_le_comap (H : Subgroup N) : f.ker <= comap f 
H
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subgroup.map_comap_eq`：map_comap_eq (H : Subgroup N) : map f (comap f H)
 = f.range ⊓ H
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subgroup.range_subtype`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup 
G), H.subtype.range = H
· 使用定理 `Subgroup.map_sup`：map_sup (H K : Subgroup G) (f : G ->* N) : (H ⊔ K).map
 f = H.map f ⊔ K.map f
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
-/
theorem subgroupOf_sup {A A' B : Subgroup G} (hA : A ≤ B) (hA' : A' ≤ B) :
    (A ⊔ A').subgroupOf B = A.subgroupOf B ⊔ A'.subgroupOf B := by
  refine
    map_injective_of_ker_le B.subtype (ker_le_comap _ _)
      (le_trans (ker_le_comap B.subtype _) le_sup_left) ?_
  simp only [subgroupOf, map_comap_eq, map_sup, range_subtype]
  rw [inf_of_le_right (sup_le hA hA'), inf_of_le_right hA', inf_of_le_right hA]

@[to_additive]
/-
**Subgroup.codisjoint_subgroupOf_sup** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：codisjoint_subgroupOf_sup (H K : Subgroup G) : Codisjoint (H.subgroupOf (H
 ⊔ K)) (K.subgroupOf (H ⊔ K))
参数：H K : Subgroup G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `codisjoint_iff`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : Ord
erTop α] {a b : α}, Codisjoint a b ↔ a ⊔ b = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.subgroupOf_sup`：subgroupOf_sup {A A' B : Subgroup G} (hA : A <=
 B) (hA' : A' <= B) : (A ⊔ A').subgroupOf B = A.subgroupOf B ⊔ A'.subgroupOf B
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `Subgroup.subgroupOf_self`：subgroupOf_self : H.subgroupOf H = ⊤
-/
theorem codisjoint_subgroupOf_sup (H K : Subgroup G) :
    Codisjoint (H.subgroupOf (H ⊔ K)) (K.subgroupOf (H ⊔ K)) := by
  rw [codisjoint_iff, ← subgroupOf_sup, subgroupOf_self]
  exacts [le_sup_left, le_sup_right]

variable {M : Type*} [CommGroup M]

@[to_additive]
/-
**Subgroup.subgroupOf_map_powMonoidHom_eq_range** 是 Mathlib 中的一个引理，位于命名空间 `Subgr
oup`。
形式化陈述：subgroupOf_map_powMonoidHom_eq_range (S : Subgroup M) (n : Nat) : (map (po
wMonoidHom n) S).subgroupOf S = (powMonoidHom n).range
参数：S : Subgroup M；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `pow_mem`：∀ {M : Type u_3} {A : Type u_4} [inst : Monoid M] [inst_1 : Set
Like A M] [SubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), x ^ n ∈ …
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `powMonoidHom_apply`：∀ {α : Type u_1} [inst : CommMonoid α] (n : ℕ) (x : 
α), (powMonoidHom n) x = x ^ n
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
-/
lemma subgroupOf_map_powMonoidHom_eq_range (S : Subgroup M) (n : ℕ) :
    (map (powMonoidHom n) S).subgroupOf S = (powMonoidHom n).range := by
  ext : 1
  simp [mem_subgroupOf]
  grind

end Subgroup

namespace MulEquiv

@[to_additive (attr := simp)]
/-
**MulEquiv.range_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `MulEquiv`。
形式化陈述：range_eq_top (e : G ≃* G') : (e : G ->* G').range = ⊤
参数：e : G ≃* G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `MonoidHom.range_eq_top`：range_eq_top {N} [Group N] {f : G ->* N} : f.ran
ge = (⊤ : Subgroup N) ↔ Function.Surjective f
· 使用定理 `MulEquiv.surjective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [ins
t_1 : Mul N] (e : M ≃* N), Function.Surjective ⇑e
-/
lemma range_eq_top (e : G ≃* G') : (e : G →* G').range = ⊤ :=
  MonoidHom.range_eq_top.mpr e.surjective

variable {M N : Type*} [CommGroup M] [CommGroup N]

open MonoidHom in
@[to_additive]
/-
**MulEquiv.map_range_powMonoidHom** 是 Mathlib 中的一个引理，位于命名空间 `MulEquiv`。
形式化陈述：map_range_powMonoidHom (e : M ≃* N) (n : Nat) : (powMonoidHom (α
参数：e : M ≃* N；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `powMonoidHom_apply`：∀ {α : Type u_1} [inst : CommMonoid α] (n : ℕ) (x : 
α), (powMonoidHom n) x = x ^ n
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MonoidHom.map_range`：map_range (g : N ->* P) (f : G ->* N) : f.range.map
 g = (g.comp f).range
· 使用引理 `MonoidHom.range_comp`：range_comp (g : N ->* P) (f : G ->* N) : (g.comp f
).range = f.range.map g
· 使用引理 `MulEquiv.range_eq_top`：range_eq_top (e : G ≃* G') : (e : G ->* G').range
 = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.range_eq_map`：range_eq_map (f : G ->* N) : f.range = (⊤ : Subg
roup G).map f
-/
lemma map_range_powMonoidHom (e : M ≃* N) (n : ℕ) :
    (powMonoidHom (α := M) n).range.map e = (powMonoidHom (α := N) n).range := by
  have H : (e : M →* N).comp (powMonoidHom n) = (powMonoidHom n).comp e := by ext : 1; simp
  rw [map_range, H, range_comp, e.range_eq_top, ← range_eq_map]

end MulEquiv

