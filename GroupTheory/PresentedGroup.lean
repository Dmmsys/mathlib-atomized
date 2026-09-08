/-
Copyright (c) 2019 Michael Howes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Howes, Newell Jensen
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Coprod.Basic

/-!
# Defining a group given by generators and relations

Given a subset `rels` of relations of the free group on a type `α`, this file constructs the group
given by generators `x : α` and relations `r ∈ rels`.

## Main definitions

* `PresentedGroup rels`: the quotient group of the free group on a type `α` by a subset `rels` of
  relations of the free group on `α`.
* `of`: The canonical map from `α` to a presented group with generators `α`.
* `toGroup f`: the canonical group homomorphism `PresentedGroup rels → G`, given a function
  `f : α → G` from a type `α` to a group `G` which satisfies the relations `rels`.

## Tags

generators, relations, group presentations
-/

@[expose] public section


variable {α β : Type*}

/-- Given a set of relations, `rels`, over a type `α`, `PresentedGroup` constructs the group with
generators `x : α` and relations `rels` as a quotient of `FreeGroup α`. -/
/-
**PresentedGroup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：PresentedGroup (rels : Set (FreeGroup α))
参数：rels : Set (FreeGroup α)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a set of relations, `rels`, over a type `α`, `PresentedGroup` constructs t
he group with
generators `x : α` and relations `rels` as a quotient of `FreeGroup α`.
-/
def PresentedGroup (rels : Set (FreeGroup α)) :=
  FreeGroup α ⧸ Subgroup.normalClosure rels
deriving Group

namespace PresentedGroup

/-- The canonical map from the free group on `α` to a presented group with generators `x : α`,
where `x` is mapped to its equivalence class under the given set of relations `rels` -/
/-
**PresentedGroup.mk** 是 Mathlib 中的一个定义，位于命名空间 `PresentedGroup`。
形式化陈述：mk (rels : Set (FreeGroup α)) : FreeGroup α ->* PresentedGroup rels
参数：rels : Set (FreeGroup α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from the free group on `α` to a presented group with generator
s `x : α`,
where `x` is mapped to its equivalence class under the given set of relations `r
els`
-/
def mk (rels : Set (FreeGroup α)) : FreeGroup α →* PresentedGroup rels :=
  ⟨⟨QuotientGroup.mk, rfl⟩, fun _ _ => rfl⟩
/-
**PresentedGroup.mk_surjective** 是 Mathlib 中的一个定理，位于命名空间 `PresentedGroup`。
形式化陈述：mk_surjective (rels : Set (FreeGroup α)) : Function.Surjective mk rels
参数：rels : Set (FreeGroup α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientGroup.mk_surjective`：mk_surjective : Function.Surjective @mk _ _
 s
-/
theorem mk_surjective (rels : Set (FreeGroup α)) : Function.Surjective <| mk rels :=
  QuotientGroup.mk_surjective

/-- `of` is the canonical map from `α` to a presented group with generators `x : α`. The term `x` is
mapped to the equivalence class of the image of `x` in `FreeGroup α`. -/
/-
**PresentedGroup.of** 是 Mathlib 中的一个定义，位于命名空间 `PresentedGroup`。
形式化陈述：of {rels : Set (FreeGroup α)} (x : α) : PresentedGroup rels
参数：FreeGroup α；x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`of` is the canonical map from `α` to a presented group with generators `x : α`.
 The term `x` is
mapped to the equivalence class of the image of `x` in `FreeGroup α`.
-/
def of {rels : Set (FreeGroup α)} (x : α) : PresentedGroup rels :=
  mk rels (FreeGroup.of x)

open Subgroup in
/--
`FreeGroup α →* FreeGroup β` induces a homomorphism
`PresentedGroup s →* PresentedGroup t` if the image of `s` is contained in `t`.
-/
/-
**PresentedGroup.map** 是 Mathlib 中的一个定义，位于命名空间 `PresentedGroup`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     (f : FreeGroup α →* FreeGroup β) →
       {s : Set (FreeGroup α)} → {t : Set (FreeGroup β)} → Set.MapsTo (⇑f) s t →
 PresentedGroup s →* PresentedGroup t
参数：f : FreeGroup α →* FreeGroup β；FreeGroup α；FreeGroup β；⇑f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`FreeGroup α →* FreeGroup β` induces a homomorphism
`PresentedGroup s →* PresentedGroup t` if the image of `s` is contained in `t`.
-/
protected def map (f : FreeGroup α →* FreeGroup β)
    {s : Set (FreeGroup α)} {t : Set (FreeGroup β)} (hst : s.MapsTo f t) :
    PresentedGroup s →* PresentedGroup t :=
  QuotientGroup.map _ _ f
    ((comap_normalClosure_image_ge s f).trans
    (comap_mono (normalClosure_mono hst.image_subset)))
/-
**PresentedGroup.mk_eq_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `PresentedGroup`。
形式化陈述：mk_eq_one_iff {rels : Set (FreeGroup α)} {x : FreeGroup α} : mk rels x = 1
 ↔ x in Subgroup.normalClosure rels
参数：FreeGroup α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientGroup.eq_one_iff`：eq_one_iff {N : Subgroup G} [N.Normal] (x : G)
 : (x : G ⧸ N) = 1 ↔ x in N
-/
lemma mk_eq_one_iff {rels : Set (FreeGroup α)} {x : FreeGroup α} :
    mk rels x = 1 ↔ x ∈ Subgroup.normalClosure rels :=
  QuotientGroup.eq_one_iff _
/-
**PresentedGroup.one_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `PresentedGroup`。
形式化陈述：one_of_mem {rels : Set (FreeGroup α)} {x : FreeGroup α} (hx : x in rels) :
 mk rels x = 1
参数：FreeGroup α；hx : x in rels。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `PresentedGroup.mk_eq_one_iff`：mk_eq_one_iff {rels : Set (FreeGroup α)} {
x : FreeGroup α} : mk rels x = 1 ↔ x in Subgroup.normalClosure rels
· 使用定理 `Subgroup.subset_normalClosure`：subset_normalClosure : s subseteq normalC
losure s
-/
lemma one_of_mem {rels : Set (FreeGroup α)} {x : FreeGroup α} (hx : x ∈ rels) :
    mk rels x = 1 :=
  mk_eq_one_iff.mpr <| Subgroup.subset_normalClosure hx
/-
**PresentedGroup.mk_eq_mk_of_mul_inv_mem** 是 Mathlib 中的一个引理，位于命名空间 `PresentedGro
up`。
形式化陈述：mk_eq_mk_of_mul_inv_mem {rels : Set (FreeGroup α)} {x y : FreeGroup α} (hx
 : x * y⁻¹ in rels) : mk rels x = mk rels y
参数：FreeGroup α；hx : x * y⁻¹ in rels。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_of_mul_inv_eq_one`：eq_of_mul_inv_eq_one (h : a * b⁻¹ = 1) : a = b
· 使用引理 `PresentedGroup.one_of_mem`：one_of_mem {rels : Set (FreeGroup α)} {x : Fr
eeGroup α} (hx : x in rels) : mk rels x = 1
-/
lemma mk_eq_mk_of_mul_inv_mem {rels : Set (FreeGroup α)} {x y : FreeGroup α}
    (hx : x * y⁻¹ ∈ rels) : mk rels x = mk rels y :=
  eq_of_mul_inv_eq_one <| one_of_mem hx
/-
**PresentedGroup.mk_eq_mk_of_inv_mul_mem** 是 Mathlib 中的一个引理，位于命名空间 `PresentedGro
up`。
形式化陈述：mk_eq_mk_of_inv_mul_mem {rels : Set (FreeGroup α)} {x y : FreeGroup α} (hx
 : x⁻¹ * y in rels) : mk rels x = mk rels y
参数：FreeGroup α；hx : x⁻¹ * y in rels。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_of_inv_mul_eq_one`：eq_of_inv_mul_eq_one (h : a⁻¹ * b = 1) : a = b
· 使用引理 `PresentedGroup.one_of_mem`：one_of_mem {rels : Set (FreeGroup α)} {x : Fr
eeGroup α} (hx : x in rels) : mk rels x = 1
-/
lemma mk_eq_mk_of_inv_mul_mem {rels : Set (FreeGroup α)} {x y : FreeGroup α}
    (hx : x⁻¹ * y ∈ rels) : mk rels x = mk rels y :=
  eq_of_inv_mul_eq_one <| one_of_mem hx

set_option backward.isDefEq.respectTransparency false in
/-- The generators of a presented group generate the presented group. That is, the subgroup closure
of the set of generators equals `⊤`. -/
@[simp]
/-
**PresentedGroup.closure_range_of** 是 Mathlib 中的一个定理，位于命名空间 `PresentedGroup`。
形式化陈述：closure_range_of (rels : Set (FreeGroup α)) : Subgroup.closure (Set.range 
(PresentedGroup.of : α -> PresentedGroup rels)) = ⊤
参数：rels : Set (FreeGroup α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.map_closure`：map_closure (f : G ->* N) (s : Set G) : (closure 
s).map f = closure (f '' s)
· 使用定理 `FreeGroup.closure_range_of`：closure_range_of (α) : Subgroup.closure (Set
.range (FreeGroup.of : α -> FreeGroup α)) = ⊤
· 使用定理 `MonoidHom.range_eq_map`：range_eq_map (f : G ->* N) : f.range = (⊤ : Subg
roup G).map f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MonoidHom.range_eq_top`：range_eq_top {N} [Group N] {f : G ->* N} : f.ran
ge = (⊤ : Subgroup N) ↔ Function.Surjective f
· 使用定理 `QuotientGroup.mk'_surjective`：∀ {G : Type u_1} [inst : Group G] (N : Sub
group G) [nN : N.Normal], Function.Surjective ⇑(QuotientGroup.mk' N)

--- 原说明 ---
The generators of a presented group generate the presented group. That is, the s
ubgroup closure
of the set of generators equals `⊤`.
-/
theorem closure_range_of (rels : Set (FreeGroup α)) :
    Subgroup.closure (Set.range (PresentedGroup.of : α → PresentedGroup rels)) = ⊤ := by
  have : (PresentedGroup.of : α → PresentedGroup rels) = QuotientGroup.mk' _ ∘ FreeGroup.of := rfl
  rw [this, Set.range_comp, ← MonoidHom.map_closure (QuotientGroup.mk' _),
    FreeGroup.closure_range_of, ← MonoidHom.range_eq_map]
  exact MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _)

@[induction_eliminator]
/-
**PresentedGroup.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `PresentedGroup`。
形式化陈述：induction_on {rels : Set (FreeGroup α)} {C : PresentedGroup rels -> Prop} 
(x : PresentedGroup rels) (H : forall z, C (mk rels z)) : C x
参数：FreeGroup α；x : PresentedGroup rels；H : forall z, C (mk rels z)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
-/
theorem induction_on {rels : Set (FreeGroup α)} {C : PresentedGroup rels → Prop}
    (x : PresentedGroup rels) (H : ∀ z, C (mk rels z)) : C x :=
  Quotient.inductionOn' x H
/-
**PresentedGroup.generated_by** 是 Mathlib 中的一个定理，位于命名空间 `PresentedGroup`。
形式化陈述：generated_by (rels : Set (FreeGroup α)) (H : Subgroup (PresentedGroup rels
)) (h : forall j : α, PresentedGroup.of j in H) (x : PresentedGroup rels) : x in
 H
参数：rels : Set (FreeGroup α)；H : Subgroup (PresentedGroup rels)；h : forall j : α,
 PresentedGroup.of j in H；x : PresentedGroup rels。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FreeGroup.induction_on`：∀ {α : Type u} {C : FreeGroup α → Prop} (z : Fre
eGroup α),   C 1 →     (∀ (x : α), C (FreeGroup.of x)) →       (∀ (x : α), C (Fr
eeGroup.of x…
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
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.inv_mem_iff`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G)
 {x : G}, x⁻¹ ∈ H ↔ x ∈ H
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuotientGroup.mk_mul`：mk_mul (a b : G) : ((a * b : G) : Q) = a * b
· 使用定理 `Subgroup.mul_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
y : G}, x ∈ H → y ∈ H → x * y ∈ H
-/
theorem generated_by (rels : Set (FreeGroup α)) (H : Subgroup (PresentedGroup rels))
    (h : ∀ j : α, PresentedGroup.of j ∈ H) (x : PresentedGroup rels) : x ∈ H := by
  obtain ⟨z⟩ := x
  induction z
  · exact one_mem H
  · exact h _
  · exact (Subgroup.inv_mem_iff H).mpr (by assumption)
  rename_i h1 h2
  change QuotientGroup.mk _ ∈ H.carrier
  rw [QuotientGroup.mk_mul]
  exact Subgroup.mul_mem _ h1 h2

section ToGroup

/-
Presented groups satisfy a universal property. If `G` is a group and `f : α → G` is a map such that
the images of `f` satisfy all the given relations, then `f` extends uniquely to a group homomorphism
from `PresentedGroup rels` to `G`.
-/
variable {G : Type*} [Group G] {f : α → G} {rels : Set (FreeGroup α)}

local notation "F" => FreeGroup.lift f

/-
**PresentedGroup.closure_rels_subset_ker** 是 Mathlib 中的一个定理，位于命名空间 `PresentedGro
up`。
形式化陈述：closure_rels_subset_ker (h : forall r in rels, FreeGroup.lift f r = 1) : S
ubgroup.normalClosure rels <= MonoidHom.ker F
参数：h : forall r in rels, FreeGroup.lift f r = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.normalClosure_le_normal`：normalClosure_le_normal {N : Subgroup 
G} [N.Normal] (h : s subseteq N) : normalClosure s <= N
· 使用定理 `MonoidHom.normal_ker`：∀ {G : Type u_1} [inst : Group G] {M : Type u_7} [
inst_1 : MulOneClass M] (f : G →* M), f.ker.Normal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MonoidHom.mem_ker`：mem_ker {f : G ->* M} {x : G} : x in f.ker ↔ f x = 1
-/
theorem closure_rels_subset_ker (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) :
    Subgroup.normalClosure rels ≤ MonoidHom.ker F :=
  Subgroup.normalClosure_le_normal fun x w ↦ MonoidHom.mem_ker.2 (h x w)
/-
**PresentedGroup.to_group_eq_one_of_mem_closure** 是 Mathlib 中的一个定理，位于命名空间 `Prese
ntedGroup`。
形式化陈述：to_group_eq_one_of_mem_closure (h : forall r in rels, FreeGroup.lift f r =
 1) : forall x in Subgroup.normalClosure rels, F x = 1
参数：h : forall r in rels, FreeGroup.lift f r = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MonoidHom.mem_ker`：mem_ker {f : G ->* M} {x : G} : x in f.ker ↔ f x = 1
· 使用定理 `PresentedGroup.closure_rels_subset_ker`：closure_rels_subset_ker (h : for
all r in rels, FreeGroup.lift f r = 1) : Subgroup.normalClosure rels <= MonoidHo
m.ker F
-/
theorem to_group_eq_one_of_mem_closure (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) :
    ∀ x ∈ Subgroup.normalClosure rels, F x = 1 :=
  fun _ w ↦ MonoidHom.mem_ker.1 <| closure_rels_subset_ker h w

/-- The extension of a map `f : α → G` that satisfies the given relations to a group homomorphism
from `PresentedGroup rels → G`. -/
/-
**PresentedGroup.toGroup** 是 Mathlib 中的一个定义，位于命名空间 `PresentedGroup`。
形式化陈述：toGroup (h : forall r in rels, FreeGroup.lift f r = 1) : PresentedGroup re
ls ->* G
参数：h : forall r in rels, FreeGroup.lift f r = 1。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PresentedGroup.to_group_eq_one_of_mem_closure`：to_group_eq_one_of_mem_cl
osure (h : forall r in rels, FreeGroup.lift f r = 1) : forall x in Subgroup.norm
alClosure rels, F x = 1

--- 原说明 ---
The extension of a map `f : α → G` that satisfies the given relations to a group
 homomorphism
from `PresentedGroup rels → G`.
-/
def toGroup (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) : PresentedGroup rels →* G :=
  QuotientGroup.lift (Subgroup.normalClosure rels) F (to_group_eq_one_of_mem_closure h)

@[simp]
/-
**PresentedGroup.toGroup.of** 是 Mathlib 中的一个定理，位于命名空间 `PresentedGroup.toGroup`。
形式化陈述：∀ {α : Type u_1} {G : Type u_3} [inst : Group G] {f : α → G} {rels : Set (
FreeGroup α)}   (h : ∀ r ∈ rels, (FreeGroup.lift f) r = 1) {x : α}, (PresentedGr
oup.toGroup h) (PresentedGroup.of x) = f x
参数：FreeGroup α；h : ∀ r ∈ rels, (FreeGroup.lift f) r = 1；PresentedGroup.toGroup h
；PresentedGroup.of x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FreeGroup.lift_apply_of`：lift_apply_of {x} : lift f (of x) = f x
-/
theorem toGroup.of (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) {x : α} : toGroup h (of x) = f x :=
  FreeGroup.lift_apply_of
/-
**PresentedGroup.toGroup.unique** 是 Mathlib 中的一个定理，位于命名空间 `PresentedGroup.toGrou
p`。
形式化陈述：∀ {α : Type u_1} {G : Type u_3} [inst : Group G] {f : α → G} {rels : Set (
FreeGroup α)}   (h : ∀ r ∈ rels, (FreeGroup.lift f) r = 1) (g : PresentedGroup r
els →* G),   (∀ (x : α), g (PresentedGroup.of x) = f x) → ∀ {x : PresentedGroup 
rels}, g x = (PresentedGroup.toGroup h) x
参数：FreeGroup α；h : ∀ r ∈ rels, (FreeGroup.lift f) r = 1；g : PresentedGroup rels 
→* G；∀ (x : α), g (PresentedGroup.of x) = f x；PresentedGroup.toGroup h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientGroup.induction_on`：induction_on {C : α ⧸ s -> Prop} (x : α ⧸ s)
 (H : forall z, C (QuotientGroup.mk z)) : C x
· 使用定理 `FreeGroup.lift_unique`：lift_unique (g : FreeGroup α ->* β) (hg : forall 
x, g (FreeGroup.of x) = f x) {x} : g x = FreeGroup.lift f x
-/
theorem toGroup.unique (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) (g : PresentedGroup rels →* G)
    (hg : ∀ x : α, g (PresentedGroup.of x) = f x) : ∀ {x}, g x = toGroup h x := by
  intro x
  refine QuotientGroup.induction_on x ?_
  exact fun _ ↦ FreeGroup.lift_unique (g.comp (QuotientGroup.mk' _)) hg

@[ext]
/-
**PresentedGroup.ext** 是 Mathlib 中的一个定理，位于命名空间 `PresentedGroup`。
形式化陈述：ext {φ ψ : PresentedGroup rels ->* G} (hx : forall (x : α), φ (.of x) = ψ 
(.of x)) : φ = ψ
参数：hx : forall (x : α), φ (.of x) = ψ (.of x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientGroup.monoidHom_ext`：monoidHom_ext ⦃f g : G ⧸ N ->* M⦄ (h : f.co
mp (mk' N) = g.comp (mk' N)) : f = g
· 使用引理 `FreeGroup.ext_hom`：ext_hom {M : Type*} [Monoid M] (f g : FreeGroup α ->*
 M) (h : forall a, f (of a) = g (of a)) : f = g
-/
theorem ext {φ ψ : PresentedGroup rels →* G} (hx : ∀ (x : α), φ (.of x) = ψ (.of x)) : φ = ψ := by
  unfold PresentedGroup
  ext
  apply hx

/-- Presented groups of isomorphic types are isomorphic. -/
/-
**PresentedGroup.equivPresentedGroup** 是 Mathlib 中的一个定义，位于命名空间 `PresentedGroup`。
形式化陈述：equivPresentedGroup (rels : Set (FreeGroup α)) (e : α ≃ β) : PresentedGrou
p rels ≃* PresentedGroup (FreeGroup.freeGroupCongr e '' rels)
参数：rels : Set (FreeGroup α)；e : α ≃ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Presented groups of isomorphic types are isomorphic.
-/
def equivPresentedGroup (rels : Set (FreeGroup α)) (e : α ≃ β) :
    PresentedGroup rels ≃* PresentedGroup (FreeGroup.freeGroupCongr e '' rels) :=
  QuotientGroup.congr (Subgroup.normalClosure rels)
    (Subgroup.normalClosure ((FreeGroup.freeGroupCongr e) '' rels)) (FreeGroup.freeGroupCongr e)
    (Subgroup.map_normalClosure rels (FreeGroup.freeGroupCongr e).toMonoidHom
      (FreeGroup.freeGroupCongr e).surjective)
/-
**PresentedGroup.equivPresentedGroup_apply_of** 是 Mathlib 中的一个定理，位于命名空间 `Present
edGroup`。
形式化陈述：equivPresentedGroup_apply_of (x : α) (rels : Set (FreeGroup α)) (e : α ≃ β
) : equivPresentedGroup rels e (PresentedGroup.of x) = PresentedGroup.of (rels
参数：x : α；rels : Set (FreeGroup α)；e : α ≃ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equivPresentedGroup_apply_of (x : α) (rels : Set (FreeGroup α)) (e : α ≃ β) :
    equivPresentedGroup rels e (PresentedGroup.of x) =
      PresentedGroup.of (rels := FreeGroup.freeGroupCongr e '' rels) (e x) := rfl
/-
**PresentedGroup.equivPresentedGroup_symm_apply_of** 是 Mathlib 中的一个定理，位于命名空间 `Pr
esentedGroup`。
形式化陈述：equivPresentedGroup_symm_apply_of (x : β) (rels : Set (FreeGroup α)) (e : 
α ≃ β) : (equivPresentedGroup rels e).symm (PresentedGroup.of x) = PresentedGrou
p.of (rels
参数：x : β；rels : Set (FreeGroup α)；e : α ≃ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equivPresentedGroup_symm_apply_of (x : β) (rels : Set (FreeGroup α)) (e : α ≃ β) :
    (equivPresentedGroup rels e).symm (PresentedGroup.of x) =
      PresentedGroup.of (rels := rels) (e.symm x) := rfl

end ToGroup

/-
**PresentedGroup.** 是 Mathlib 中的一个实例，位于命名空间 `PresentedGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (rels : Set (FreeGroup α)) : Inhabited (PresentedGroup rels) :=
  ⟨1⟩

section Coprod

variable (rels₁ : Set (FreeGroup α)) (rels₂ : Set (FreeGroup β))

/--
The canonical inclusion map from the disjoint union of types to the free product of the relations
-/
/-
**PresentedGroup.toCoprod** 是 Mathlib 中的一个定义，位于命名空间 `PresentedGroup`。
形式化陈述：toCoprod : α oplus β -> Monoid.Coprod (PresentedGroup rels₁) (PresentedGro
up rels₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical inclusion map from the disjoint union of types to the free product
 of the relations
-/
def toCoprod : α ⊕ β → Monoid.Coprod (PresentedGroup rels₁) (PresentedGroup rels₂) :=
  Sum.elim (Monoid.Coprod.inl ∘ .of) (Monoid.Coprod.inr ∘ .of)

@[simp]
/-
**PresentedGroup.lift_toCoprod_inl_eq_inl_mk** 是 Mathlib 中的一个引理，位于命名空间 `Presente
dGroup`。
形式化陈述：lift_toCoprod_inl_eq_inl_mk : (FreeGroup.lift (toCoprod rels₁ rels₂)).comp
 (FreeGroup.map Sum.inl) = Monoid.Coprod.inl.comp (mk rels₁)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FreeGroup.ext_hom`：ext_hom {M : Type*} [Monoid M] (f g : FreeGroup α ->*
 M) (h : forall a, f (of a) = g (of a)) : f = g
-/
lemma lift_toCoprod_inl_eq_inl_mk : (FreeGroup.lift (toCoprod rels₁ rels₂)).comp
    (FreeGroup.map Sum.inl) = Monoid.Coprod.inl.comp (mk rels₁) :=
  FreeGroup.ext_hom _ _ fun _ ↦ rfl

@[simp]
/-
**PresentedGroup.lift_toCoprod_inr_eq_inr_mk** 是 Mathlib 中的一个引理，位于命名空间 `Presente
dGroup`。
形式化陈述：lift_toCoprod_inr_eq_inr_mk : (FreeGroup.lift (toCoprod rels₁ rels₂)).comp
 (FreeGroup.map Sum.inr) = Monoid.Coprod.inr.comp (mk rels₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FreeGroup.ext_hom`：ext_hom {M : Type*} [Monoid M] (f g : FreeGroup α ->*
 M) (h : forall a, f (of a) = g (of a)) : f = g
-/
lemma lift_toCoprod_inr_eq_inr_mk : (FreeGroup.lift (toCoprod rels₁ rels₂)).comp
    (FreeGroup.map Sum.inr) = Monoid.Coprod.inr.comp (mk rels₂) :=
  FreeGroup.ext_hom _ _ fun _ ↦ rfl
/-
**PresentedGroup.lift_toCoprod_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `PresentedGroup`
。
形式化陈述：lift_toCoprod_eq_one (r : FreeGroup (α oplus β)) (hr : r in FreeGroup.map 
Sum.inl '' rels₁ union FreeGroup.map Sum.inr '' rels₂) : FreeGroup.lift (toCopro
d rels₁ rels₂) r = 1
参数：r : FreeGroup (α oplus β)；hr : r in FreeGroup.map Sum.inl '' rels₁ union Free
Group.map Sum.inr '' rels₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PresentedGroup.lift_toCoprod_inl_eq_inl_mk`：lift_toCoprod_inl_eq_inl_mk 
: (FreeGroup.lift (toCoprod rels₁ rels₂)).comp (FreeGroup.map Sum.inl) = Monoid.
Coprod.inl.comp (mk rels₁)
· 使用引理 `PresentedGroup.one_of_mem`：one_of_mem {rels : Set (FreeGroup α)} {x : Fr
eeGroup α} (hx : x in rels) : mk rels x = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `PresentedGroup.lift_toCoprod_inr_eq_inr_mk`：lift_toCoprod_inr_eq_inr_mk 
: (FreeGroup.lift (toCoprod rels₁ rels₂)).comp (FreeGroup.map Sum.inr) = Monoid.
Coprod.inr.comp (mk rels₂)
-/
lemma lift_toCoprod_eq_one (r : FreeGroup (α ⊕ β))
    (hr : r ∈ FreeGroup.map Sum.inl '' rels₁ ∪ FreeGroup.map Sum.inr '' rels₂) :
    FreeGroup.lift (toCoprod rels₁ rels₂) r = 1 := by
  obtain ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ := hr <;> simp [← MonoidHom.comp_apply, one_of_mem hr]

/--
The free product (Coproduct) of presentations is isomorphic to the presentation of the union over
the `FreeGroup (α ⊕ β)`
-/
/-
**PresentedGroup.coprodPresentations** 是 Mathlib 中的一个定义，位于命名空间 `PresentedGroup`。
形式化陈述：coprodPresentations : PresentedGroup (FreeGroup.map Sum.inl '' rels₁ union
 FreeGroup.map Sum.inr '' rels₂) ≃* Monoid.Coprod (PresentedGroup rels₁) (Presen
tedGroup rels₂)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `PresentedGroup.lift_toCoprod_eq_one`：lift_toCoprod_eq_one (r : FreeGroup
 (α oplus β)) (hr : r in FreeGroup.map Sum.inl '' rels₁ union FreeGroup.map Sum.
inr '' rels₂) : FreeGroup…

--- 原说明 ---
The free product (Coproduct) of presentations is isomorphic to the presentation 
of the union over
the `FreeGroup (α ⊕ β)`
-/
def coprodPresentations :
    PresentedGroup (FreeGroup.map Sum.inl '' rels₁ ∪ FreeGroup.map Sum.inr '' rels₂) ≃*
    Monoid.Coprod (PresentedGroup rels₁) (PresentedGroup rels₂) :=
  MonoidHom.toMulEquiv
    (toGroup (lift_toCoprod_eq_one rels₁ rels₂))
    (Monoid.Coprod.lift
      (PresentedGroup.map (FreeGroup.map Sum.inl) fun r hr ↦ .inl ⟨r, hr, rfl⟩)
      (PresentedGroup.map (FreeGroup.map Sum.inr) fun r hr ↦ .inr ⟨r, hr, rfl⟩))
    (ext <| Sum.rec (fun _ ↦ rfl) (fun _ ↦ rfl))
    (Monoid.Coprod.hom_ext (ext fun _ ↦ rfl) (ext fun _ ↦ rfl))
end Coprod
end PresentedGroup

