/-
Copyright (c) 2022 Kyle Miller, Adam Topaz, Rémi Bottinelli, Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Adam Topaz, Rémi Bottinelli, Junyan Xu
-/
module

public import Mathlib.Topology.Category.TopCat.Limits.Konig

/-!
# Cofiltered systems

This file deals with properties of cofiltered (and inverse) systems.

## Main definitions

Given a functor `F : J ⥤ Type v`:

* For `j : J`, `F.eventualRange j` is the intersection of all ranges of morphisms `F.map f`
  where `f` has codomain `j`.
* `F.IsMittagLeffler` states that the functor `F` satisfies the Mittag-Leffler
  condition: the ranges of morphisms `F.map f` (with `f` having codomain `j`) stabilize.
* If `J` is cofiltered `F.toEventualRanges` is the subfunctor of `F` obtained by restriction
  to `F.eventualRange`.
* `F.toPreimages` restricts a functor to preimages of a given set in some `F.obj i`. If `J` is
  cofiltered, then it is Mittag-Leffler if `F` is, see `IsMittagLeffler.toPreimages`.

## Main statements

* `nonempty_sections_of_finite_cofiltered_system` shows that if `J` is cofiltered and each
  `F.obj j` is nonempty and finite, `F.sections` is nonempty.
* `nonempty_sections_of_finite_inverse_system` is a specialization of the above to `J` being a
  directed set (and `F : Jᵒᵖ ⥤ Type v`).
* `isMittagLeffler_of_exists_finite_range` shows that if `J` is cofiltered and for all `j`,
  there exists some `i` and `f : i ⟶ j` such that the range of `F.map f` is finite, then
  `F` is Mittag-Leffler.
* `surjective_toEventualRanges` shows that if `F` is Mittag-Leffler, then `F.toEventualRanges`
  has all morphisms `F.map f` surjective.

## TODO

* Prove [Stacks: Lemma 0597](https://stacks.math.columbia.edu/tag/0597)

## References

* [Stacks: Mittag-Leffler systems](https://stacks.math.columbia.edu/tag/0594)

## Tags

Mittag-Leffler, surjective, eventual range, inverse system,

-/

@[expose] public section


universe u v w

open CategoryTheory CategoryTheory.IsCofiltered Set CategoryTheory.FunctorToTypes

section FiniteKonig

/-- This bootstraps `nonempty_sections_of_finite_inverse_system`. In this version,
the `F` functor is between categories of the same universe, and it is an easy
corollary to `TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system`. -/
/-
**nonempty_sections_of_finite_cofiltered_system.init** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：nonempty_sections_of_finite_cofiltered_system.init {J : Type u} [SmallCate
gory J] [IsCofilteredOrEmpty J] (F : J ⥤ Type u) [hf : forall j, Finite (F.obj j
)] [hne : forall j, Nonempty (F.obj j)] : F.sections.Nonempty
参数：F : J ⥤ Type u；F.obj j；F.obj j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system`：nonempty_limi
tCone_of_compact_t2_cofiltered_system (F : J ⥤ TopCat.{max v u}) [IsCofilteredOr
Empty J] [forall j : J, Nonempty (F.obj j)] [fo…
· 使用定理 `Finite.compactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Finite 
X], CompactSpace X
· 使用定理 `DiscreteTopology.toT2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X]
 [DiscreteTopology X], T2Space X

--- 原说明 ---
This bootstraps `nonempty_sections_of_finite_inverse_system`. In this version,
the `F` functor is between categories of the same universe, and it is an easy
corollary to `TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system`.
-/
theorem nonempty_sections_of_finite_cofiltered_system.init {J : Type u} [SmallCategory J]
    [IsCofilteredOrEmpty J] (F : J ⥤ Type u) [hf : ∀ j, Finite (F.obj j)]
    [hne : ∀ j, Nonempty (F.obj j)] : F.sections.Nonempty := by
  let F' : J ⥤ TopCat := F ⋙ TopCat.discrete
  have : ∀ j, DiscreteTopology (F'.obj j) := fun _ => ⟨rfl⟩
  have : ∀ j, Finite (F'.obj j) := hf
  have : ∀ j, Nonempty (F'.obj j) := hne
  obtain ⟨⟨u, hu⟩⟩ := TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system.{u} F'
  exact ⟨u, hu⟩

/-- The cofiltered limit of nonempty finite types is nonempty.

See `nonempty_sections_of_finite_inverse_system` for a specialization to inverse limits. -/
/-
**nonempty_sections_of_finite_cofiltered_system** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_sections_of_finite_cofiltered_system {J : Type u} [Category.{w} J
] [IsCofilteredOrEmpty J] (F : J ⥤ Type v) [forall j : J, Finite (F.obj j)] [for
all j : J, Nonempty (F.obj j)] : F.sections.Nonempty
参数：F : J ⥤ Type v；F.obj j；F.obj j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_equiv`：Finite.of_equiv (α : Sort*) [h : Finite α] (f : α ≃ β) 
: Finite β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `nonempty_sections_of_finite_cofiltered_system.init`：nonempty_sections_of
_finite_cofiltered_system.init {J : Type u} [SmallCategory J] [IsCofilteredOrEmp
ty J] (F : J ⥤ Type u) [hf : forall j, F…
· 使用定理 `CategoryTheory.IsCofiltered.toIsCofilteredOrEmpty`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} [self : CategoryTheory.IsCofiltered C],   Ca
tegoryTheory.IsCofilteredOrEmpty C
· 使用定理 `CategoryTheory.instIsCofilteredAsSmall`：∀ (C : Type u) [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.IsCofiltered C],   CategoryTheory.IsCof
iltered (CategoryTheory.AsSm…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The cofiltered limit of nonempty finite types is nonempty.

See `nonempty_sections_of_finite_inverse_system` for a specialization to inverse
 limits.
-/
theorem nonempty_sections_of_finite_cofiltered_system {J : Type u} [Category.{w} J]
    [IsCofilteredOrEmpty J] (F : J ⥤ Type v) [∀ j : J, Finite (F.obj j)]
    [∀ j : J, Nonempty (F.obj j)] : F.sections.Nonempty := by
  -- Step 1: lift everything to the `max u v w` universe.
  let J' : Type max w v u := AsSmall.{max w v} J
  let down : J' ⥤ J := AsSmall.down
  let F' : J' ⥤ Type (max u v w) := down ⋙ F ⋙ uliftFunctor.{max u w, v}
  have : ∀ i, Nonempty (F'.obj i) := fun i => ⟨⟨Classical.arbitrary (F.obj (down.obj i))⟩⟩
  have : ∀ i, Finite (F'.obj i) := fun i => Finite.of_equiv (F.obj (down.obj i)) Equiv.ulift.symm
  -- Step 2: apply the bootstrap theorem
  cases isEmpty_or_nonempty J
  · fconstructor <;> apply isEmptyElim
  have : IsCofiltered J := ⟨⟩
  obtain ⟨u, hu⟩ := nonempty_sections_of_finite_cofiltered_system.init F'
  -- Step 3: interpret the results
  use fun j => (u ⟨j⟩).down
  intro j j' f
  have h := @hu (⟨j⟩ : J') (⟨j'⟩ : J') (ULift.up f)
  simp only [F', down, AsSmall.down] at h
  simp_rw [← h]
  rfl

/-- The inverse limit of nonempty finite types is nonempty.

See `nonempty_sections_of_finite_cofiltered_system` for a generalization to cofiltered limits.
That version applies in almost all cases, and the only difference is that this version
allows `J` to be empty.

This may be regarded as a generalization of Kőnig's lemma.
To specialize: given a locally finite connected graph, take `Jᵒᵖ` to be `ℕ` and
`F j` to be length-`j` paths that start from an arbitrary fixed vertex.
Elements of `F.sections` can be read off as infinite rays in the graph. -/
/-
**nonempty_sections_of_finite_inverse_system** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_sections_of_finite_inverse_system {J : Type u} [Preorder J] [IsDi
rectedOrder J] (F : Jᵒᵖ ⥤ Type v) [forall j : Jᵒᵖ, Finite (F.obj j)] [forall j :
 Jᵒᵖ, Nonempty (F.obj j)] : F.sections.Nonempty
参数：F : Jᵒᵖ ⥤ Type v；F.obj j；F.obj j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_sections_of_finite_cofiltered_system`：nonempty_sections_of_fini
te_cofiltered_system {J : Type u} [Category.{w} J] [IsCofilteredOrEmpty J] (F : 
J ⥤ Type v) [forall j : J, Finite (…
· 使用定理 `CategoryTheory.isFilteredOrEmpty_of_directed_le`：∀ (α : Type u) [inst : 
Preorder α] [IsDirectedOrder α], CategoryTheory.IsFilteredOrEmpty α

--- 原说明 ---
The inverse limit of nonempty finite types is nonempty.

See `nonempty_sections_of_finite_cofiltered_system` for a generalization to cofi
ltered limits.
That version applies in almost all cases, and the only difference is that this v
ersion
allows `J` to be empty.

This may be regarded as a generalization of Kőnig's lemma.
To specialize: given a locally finite connected graph, take `Jᵒᵖ` to be `ℕ` and
`F j` to be length-`j` paths that start from an arbitrary fixed vertex.
Elements of `F.sections` can be read off as infinite rays in the graph.
-/
theorem nonempty_sections_of_finite_inverse_system {J : Type u} [Preorder J] [IsDirectedOrder J]
    (F : Jᵒᵖ ⥤ Type v) [∀ j : Jᵒᵖ, Finite (F.obj j)] [∀ j : Jᵒᵖ, Nonempty (F.obj j)] :
    F.sections.Nonempty := nonempty_sections_of_finite_cofiltered_system F

end FiniteKonig

namespace CategoryTheory

namespace Functor

variable {J : Type u} [Category* J] (F : J ⥤ Type v) {i j k : J} (s : Set (F.obj i))

/-- The eventual range of the functor `F : J ⥤ Type v` at index `j : J` is the intersection
of the ranges of all maps `F.map f` with `i : J` and `f : i ⟶ j`. -/
/-
**CategoryTheory.Functor.eventualRange** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：eventualRange (j : J)
参数：j : J。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The eventual range of the functor `F : J ⥤ Type v` at index `j : J` is the inter
section
of the ranges of all maps `F.map f` with `i : J` and `f : i ⟶ j`.
-/
def eventualRange (j : J) :=
  ⋂ (i) (f : i ⟶ j), range (F.map f)
/-
**CategoryTheory.Functor.mem_eventualRange_iff** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：mem_eventualRange_iff {x : F.obj j} : x in F.eventualRange j ↔ forall ⦃i⦄ 
(f : i ⟶ j), x in range (F.map f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_iInter₂`：mem_iInter₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋂ (i) (j), s i j) ↔ forall i j, x in s i j
-/
theorem mem_eventualRange_iff {x : F.obj j} :
    x ∈ F.eventualRange j ↔ ∀ ⦃i⦄ (f : i ⟶ j), x ∈ range (F.map f) :=
  mem_iInter₂

/-- The functor `F : J ⥤ Type v` satisfies the Mittag-Leffler condition if for all `j : J`,
there exists some `i : J` and `f : i ⟶ j` such that for all `k : J` and `g : k ⟶ j`, the range
of `F.map f` is contained in that of `F.map g`;
in other words (see `isMittagLeffler_iff_eventualRange`), the eventual range at `j` is attained
by some `f : i ⟶ j`. -/
/-
**CategoryTheory.Functor.IsMittagLeffler** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：IsMittagLeffler : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `F : J ⥤ Type v` satisfies the Mittag-Leffler condition if for all `
j : J`,
there exists some `i : J` and `f : i ⟶ j` such that for all `k : J` and `g : k ⟶
 j`, the range
of `F.map f` is contained in that of `F.map g`;
in other words (see `isMittagLeffler_iff_eventualRange`), the eventual range at 
`j` is attained
by some `f : i ⟶ j`.
-/
def IsMittagLeffler : Prop :=
  ∀ j : J, ∃ (i : _) (f : i ⟶ j), ∀ ⦃k⦄ (g : k ⟶ j), range (F.map f) ⊆ range (F.map g)
/-
**CategoryTheory.Functor.isMittagLeffler_iff_eventualRange** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Functor`。
形式化陈述：isMittagLeffler_iff_eventualRange : F.IsMittagLeffler ↔ forall j : J, exis
ts (i : _) (f : i ⟶ j), F.eventualRange j = range (F.map f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `exists₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∃ a b, p a b) ↔ ∃ a b, q a b
)
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Set.iInter₂_subset`：iInter₂_subset {s : forall i, κ i -> Set α} (i : ι) 
(j : κ i) : ⋂ (i) (j), s i j subseteq s i j
· 使用定理 `Set.subset_iInter₂`：subset_iInter₂ {s : Set α} {t : forall i, κ i -> Set
 α} (h : forall i j, s subseteq t i j) : s subseteq ⋂ (i) (j), t i j
-/
theorem isMittagLeffler_iff_eventualRange :
    F.IsMittagLeffler ↔ ∀ j : J, ∃ (i : _) (f : i ⟶ j), F.eventualRange j = range (F.map f) :=
  forall_congr' fun _ =>
    exists₂_congr fun _ _ =>
      ⟨fun h => (iInter₂_subset _ _).antisymm <| subset_iInter₂ h, fun h => h ▸ iInter₂_subset⟩
/-
**CategoryTheory.Functor.IsMittagLeffler.subset_image_eventualRange** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.Functor.IsMittagLeffler`。
形式化陈述：∀ {J : Type u} [inst : CategoryTheory.Category.{v_1, u} J] (F : CategoryTh
eory.Functor J (Type v)) {i j : J},   F.IsMittagLeffler →     ∀ (f : j ⟶ i), F.e
ventualRange i ⊆ ⇑(CategoryTheory.ConcreteCategory.hom (F.map f)) '' F.eventualR
ange j
参数：F : CategoryTheory.Functor J (Type v)；f : j ⟶ i；CategoryTheory.ConcreteCatego
ry.hom (F.map f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Functor.isMittagLeffler_iff_eventualRange`：isMittagLeffle
r_iff_eventualRange : F.IsMittagLeffler ↔ forall j : J, exists (i : _) (f : i ⟶ 
j), F.eventualRange j = range (F.map f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.mem_eventualRange_iff`：mem_eventualRange_iff {x :
 F.obj j} : x in F.eventualRange j ↔ forall ⦃i⦄ (f : i ⟶ j), x in range (F.map f
)
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
-/
theorem IsMittagLeffler.subset_image_eventualRange (h : F.IsMittagLeffler) (f : j ⟶ i) :
    F.eventualRange i ⊆ F.map f '' F.eventualRange j := by
  obtain ⟨k, g, hg⟩ := F.isMittagLeffler_iff_eventualRange.1 h j
  rw [hg]; intro x hx
  obtain ⟨x, rfl⟩ := F.mem_eventualRange_iff.1 hx (g ≫ f)
  exact ⟨_, ⟨x, rfl⟩, by rw [map_comp, comp_apply]⟩
/-
**CategoryTheory.Functor.eventualRange_eq_range_precomp** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Functor`。
形式化陈述：eventualRange_eq_range_precomp (f : i ⟶ j) (g : j ⟶ k) (h : F.eventualRang
e k = range (F.map g)) : F.eventualRange k = range (F.map <| f ≫ g)
参数：f : i ⟶ j；g : j ⟶ k；h : F.eventualRange k = range (F.map g)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.iInter₂_subset`：iInter₂_subset {s : forall i, κ i -> Set α} (i : ι) 
(j : κ i) : ⋂ (i) (j), s i j subseteq s i j
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.types_comp`：types_comp {X Y Z : Type u} (f : X ⟶ Y) (g : 
Y ⟶ Z) : ConcreteCategory.hom (f ≫ g) = g ∘ f
· 使用定理 `Set.range_comp_subset_range`：range_comp_subset_range (f : α -> β) (g : β
 -> γ) : range (g ∘ f) subseteq range g
-/
theorem eventualRange_eq_range_precomp (f : i ⟶ j) (g : j ⟶ k)
    (h : F.eventualRange k = range (F.map g)) : F.eventualRange k = range (F.map <| f ≫ g) := by
  apply subset_antisymm
  · apply iInter₂_subset
  · rw [h, F.map_comp, types_comp]
    apply range_comp_subset_range
/-
**CategoryTheory.Functor.isMittagLeffler_of_surjective** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Functor`。
形式化陈述：isMittagLeffler_of_surjective (h : forall ⦃i j : J⦄ (f : i ⟶ j), Function.
Surjective (F.map f)) : F.IsMittagLeffler
参数：h : forall ⦃i j : J⦄ (f : i ⟶ j), Function.Surjective (F.map f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.types_id`：types_id (X : Type u) : (𝟙 X : _ -> _) = id
· 使用定理 `Set.range_id`：range_id : range (@id α) = univ
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem isMittagLeffler_of_surjective (h : ∀ ⦃i j : J⦄ (f : i ⟶ j), Function.Surjective (F.map f)) :
    F.IsMittagLeffler :=
  fun j => ⟨j, 𝟙 j, fun k g => by rw [map_id, types_id, range_id, (h g).range_eq]⟩

/-- The subfunctor of `F` obtained by restricting to the preimages of a set `s ∈ F.obj i`. -/
@[simps]
/-
**CategoryTheory.Functor.toPreimages** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：toPreimages : J ⥤ Type v where obj j
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subfunctor of `F` obtained by restricting to the preimages of a set `s ∈ F.o
bj i`.
-/
def toPreimages : J ⥤ Type v where
  obj j := ⋂ f : j ⟶ i, F.map f ⁻¹' s
  map g := ↾(MapsTo.restrict (F.map g) _ _ fun x h => by
    rw [mem_iInter] at h ⊢
    intro f
    rw [← mem_preimage, preimage_preimage, mem_preimage]
    convert! h (g ≫ f); rw [F.map_comp]; rfl)
/-
**CategoryTheory.Functor.toPreimages_finite** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Functor`。
形式化陈述：toPreimages_finite [forall j, Finite (F.obj j)] : forall j, Finite ((F.toP
reimages s).obj j)
参数：F.obj j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance toPreimages_finite [∀ j, Finite (F.obj j)] : ∀ j, Finite ((F.toPreimages s).obj j) :=
  fun _ => Subtype.finite

variable [IsCofilteredOrEmpty J]
/-
**CategoryTheory.Functor.eventualRange_mapsTo** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Functor`。
形式化陈述：eventualRange_mapsTo (f : j ⟶ i) : (F.eventualRange j).MapsTo (F.map f) (F
.eventualRange i)
参数：f : j ⟶ i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.mem_eventualRange_iff`：mem_eventualRange_iff {x :
 F.obj j} : x in F.eventualRange j ↔ forall ⦃i⦄ (f : i ⟶ j), x in range (F.map f
)
· 使用定理 `CategoryTheory.IsCofiltered.cospan`：cospan {i j j' : C} (f : j ⟶ i) (f' 
: j' ⟶ i) : exists (k : C) (g : k ⟶ j) (g' : k ⟶ j'), g ≫ f = g' ≫ f'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
theorem eventualRange_mapsTo (f : j ⟶ i) :
    (F.eventualRange j).MapsTo (F.map f) (F.eventualRange i) := fun x hx => by
  rw [mem_eventualRange_iff] at hx ⊢
  intro k f'
  obtain ⟨l, g, g', he⟩ := cospan f f'
  obtain ⟨x, rfl⟩ := hx g
  rw [← comp_apply, ← map_comp, he, F.map_comp]
  exact ⟨_, rfl⟩
/-
**CategoryTheory.Functor.IsMittagLeffler.eq_image_eventualRange** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.Functor.IsMittagLeffler`。
形式化陈述：∀ {J : Type u} [inst : CategoryTheory.Category.{v_1, u} J] (F : CategoryTh
eory.Functor J (Type v)) {i j : J}   [CategoryTheory.IsCofilteredOrEmpty J],   F
.IsMittagLeffler →     ∀ (f : j ⟶ i), F.eventualRange i = ⇑(CategoryTheory.Concr
eteCategory.hom (F.map f)) '' F.eventualRange j
参数：F : CategoryTheory.Functor J (Type v)；f : j ⟶ i；CategoryTheory.ConcreteCatego
ry.hom (F.map f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `CategoryTheory.Functor.IsMittagLeffler.subset_image_eventualRange`：∀ {J 
: Type u} [inst : CategoryTheory.Category.{v_1, u} J] (F : CategoryTheory.Functo
r J (Type v)) {i j : J},   F.IsMittagLeffler →     ∀ (f…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mapsTo_iff_image_subset`：mapsTo_iff_image_subset : MapsTo f s t ↔ f 
'' s subseteq t
· 使用定理 `CategoryTheory.Functor.eventualRange_mapsTo`：eventualRange_mapsTo (f : j
 ⟶ i) : (F.eventualRange j).MapsTo (F.map f) (F.eventualRange i)
-/
theorem IsMittagLeffler.eq_image_eventualRange (h : F.IsMittagLeffler) (f : j ⟶ i) :
    F.eventualRange i = F.map f '' F.eventualRange j :=
  (h.subset_image_eventualRange F f).antisymm <| mapsTo_iff_image_subset.1
    (F.eventualRange_mapsTo f)
/-
**CategoryTheory.Functor.eventualRange_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Functor`。
形式化陈述：eventualRange_eq_iff {f : i ⟶ j} : F.eventualRange j = range (F.map f) ↔ f
orall ⦃k⦄ (g : k ⟶ i), range (F.map f) subseteq range (F.map <| g ≫ f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `subset_antisymm_iff`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst 
: PartialOrder α] {a b : α}, a = b ↔ a ⊆ b ∧ b ⊆ a
· 使用定理 `CategoryTheory.Functor.eventualRange.eq_1`：∀ {J : Type u} [inst : Catego
ryTheory.Category.{v_1, u} J] (F : CategoryTheory.Functor J (Type v)) (j : J),  
 F.eventualRange j = ⋂ i, ⋂ f, …
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Set.iInter₂_subset`：iInter₂_subset {s : forall i, κ i -> Set α} (i : ι) 
(j : κ i) : ⋂ (i) (j), s i j subseteq s i j
· 使用定理 `Set.subset_iInter₂_iff`：subset_iInter₂_iff {s : Set α} {t : forall i, κ 
i -> Set α} : (s subseteq ⋂ (i) (j), t i j) ↔ forall i j, s subseteq t i j
· 使用定理 `CategoryTheory.IsCofiltered.cospan`：cospan {i j j' : C} (f : j ⟶ i) (f' 
: j' ⟶ i) : exists (k : C) (g : k ⟶ j) (g' : k ⟶ j'), g ≫ f = g' ≫ f'
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.types_comp`：types_comp {X Y Z : Type u} (f : X ⟶ Y) (g : 
Y ⟶ Z) : ConcreteCategory.hom (f ≫ g) = g ∘ f
· 使用定理 `Set.range_comp_subset_range`：range_comp_subset_range (f : α -> β) (g : β
 -> γ) : range (g ∘ f) subseteq range g
-/
theorem eventualRange_eq_iff {f : i ⟶ j} :
    F.eventualRange j = range (F.map f) ↔
      ∀ ⦃k⦄ (g : k ⟶ i), range (F.map f) ⊆ range (F.map <| g ≫ f) := by
  rw [subset_antisymm_iff, eventualRange, and_iff_right (iInter₂_subset _ _), subset_iInter₂_iff]
  refine ⟨fun h k g => h _ _, fun h j' f' => ?_⟩
  obtain ⟨k, g, g', he⟩ := cospan f f'
  refine (h g).trans ?_
  rw [he, F.map_comp, types_comp]
  apply range_comp_subset_range
/-
**CategoryTheory.Functor.isMittagLeffler_iff_subset_range_comp** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isMittagLeffler_iff_subset_range_comp : F.IsMittagLeffler ↔ forall j : J, 
exists (i : _) (f : i ⟶ j), forall ⦃k⦄ (g : k ⟶ i), range (F.map f) subseteq ran
ge (F.map <| g ≫ f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isMittagLeffler_iff_subset_range_comp : F.IsMittagLeffler ↔ ∀ j : J, ∃ (i : _) (f : i ⟶ j),
    ∀ ⦃k⦄ (g : k ⟶ i), range (F.map f) ⊆ range (F.map <| g ≫ f) := by
  simp_rw [isMittagLeffler_iff_eventualRange, eventualRange_eq_iff]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.IsMittagLeffler.toPreimages** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Functor.IsMittagLeffler`。
形式化陈述：∀ {J : Type u} [inst : CategoryTheory.Category.{v_1, u} J] (F : CategoryTh
eory.Functor J (Type v)) {i : J}   (s : Set (F.obj i)) [CategoryTheory.IsCofilte
redOrEmpty J], F.IsMittagLeffler → (F.toPreimages s).IsMittagLeffler
参数：F : CategoryTheory.Functor J (Type v)；s : Set (F.obj i)；F.toPreimages s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Functor.isMittagLeffler_iff_subset_range_comp`：isMittagLe
ffler_iff_subset_range_comp : F.IsMittagLeffler ↔ forall j : J, exists (i : _) (
f : i ⟶ j), forall ⦃k⦄ (g : k ⟶ i), range (F.map f…
· 使用定理 `CategoryTheory.IsCofilteredOrEmpty.cone_objs`：∀ {C : Type u} {inst : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.IsCofilteredOrEmpty C] (X 
Y : C),   ∃ W x x, True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Functor.isMittagLeffler_iff_eventualRange`：isMittagLeffle
r_iff_eventualRange : F.IsMittagLeffler ↔ forall j : J, exists (i : _) (f : i ⟶ 
j), F.eventualRange j = range (F.map f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.IsMittagLeffler.subset_image_eventualRange`：∀ {J 
: Type u} [inst : CategoryTheory.Category.{v_1, u} J] (F : CategoryTheory.Functo
r J (Type v)) {i j : J},   F.IsMittagLeffler →     ∀ (f…
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
· 使用定理 `CategoryTheory.IsCofilteredOrEmpty.cone_maps`：∀ {C : Type u} {inst : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.IsCofilteredOrEmpty C] ⦃X 
Y : C⦄   (f g : X ⟶ Y), ∃ W h, Cat…
· 使用定理 `CategoryTheory.Functor.mem_eventualRange_iff`：mem_eventualRange_iff {x :
 F.obj j} : x in F.eventualRange j ↔ forall ⦃i⦄ (f : i ⟶ j), x in range (F.map f
)
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
-/
theorem IsMittagLeffler.toPreimages (h : F.IsMittagLeffler) : (F.toPreimages s).IsMittagLeffler :=
  (isMittagLeffler_iff_subset_range_comp _).2 fun j => by
    obtain ⟨j₁, g₁, f₁, -⟩ := IsCofilteredOrEmpty.cone_objs i j
    obtain ⟨j₂, f₂, h₂⟩ := F.isMittagLeffler_iff_eventualRange.1 h j₁
    refine ⟨j₂, f₂ ≫ f₁, fun j₃ f₃ => ?_⟩
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    have : F.map f₂ x ∈ F.eventualRange j₁ := by
      rw [h₂]
      exact ⟨_, rfl⟩
    obtain ⟨y, hy, h₃⟩ := h.subset_image_eventualRange F (f₃ ≫ f₂) this
    refine ⟨⟨y, mem_iInter.2 fun g₂ => ?_⟩, Subtype.ext ?_⟩
    · obtain ⟨j₄, f₄, h₄⟩ := IsCofilteredOrEmpty.cone_maps g₂ ((f₃ ≫ f₂) ≫ g₁)
      obtain ⟨y, rfl⟩ := F.mem_eventualRange_iff.1 hy f₄
      rw [← comp_apply, ← map_comp] at h₃
      rw [mem_preimage, ← comp_apply, ← map_comp, h₄, ← Category.assoc, map_comp, comp_apply, h₃,
        ← comp_apply, ← map_comp]
      apply mem_iInter.1 hx
    · simp only [toPreimages_obj, toPreimages_map, ConcreteCategory.hom_ofHom,
        TypeCat.Fun.coe_mk, MapsTo.val_restrict_apply]
      rw [← Category.assoc, map_comp, comp_apply, h₃, map_comp, comp_apply]
/-
**CategoryTheory.Functor.isMittagLeffler_of_exists_finite_range** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isMittagLeffler_of_exists_finite_range (h : forall j : J, exists (i : _) (
f : i ⟶ j), (range <| F.map f).Finite) : F.IsMittagLeffler
参数：h : forall j : J, exists (i : _) (f : i ⟶ j), (range <| F.map f).Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.has_min`：∀ {α : Type u_4} {r : α → α → Prop}, WellFounded r 
→ ∀ (s : Set α), s.Nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬r x a
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `DirectedOn.is_bot_of_is_min`：∀ {α : Type u_1} [inst : Preorder α] {s : S
et α},   DirectedOn (fun x1 x2 => x2 ≤ x1) s → ∀ {m : α}, m ∈ s → (∀ a ∈ s, a ≤ 
m → m ≤ a) → ∀ a …
· 使用定理 `Directed.directedOn_range`：∀ {α : Type u_1} {ι : Sort u_3} {r : α → α → 
Prop} {f : ι → α}, Directed r f → DirectedOn r (Set.range f)
· 使用定理 `CategoryTheory.Functor.ranges_directed`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.IsCofilteredOrEmpty C]   (F : CategoryT
heory.Functor C (Type u_1)) …
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `eq_of_le_of_not_lt`：eq_of_le_of_not_lt (h₁ : a <= b) (h₂ : ¬a < b) : a =
 b
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_ssubset`：coe_ssubset {s₁ s₂ : Finset α} : (s₁ : Set α) ⊂ s₂ ↔
 s₁ ⊂ s₂
-/
theorem isMittagLeffler_of_exists_finite_range
    (h : ∀ j : J, ∃ (i : _) (f : i ⟶ j), (range <| F.map f).Finite) : F.IsMittagLeffler := by
  intro j
  obtain ⟨i, hi, hf⟩ := h j
  obtain ⟨m, ⟨i, f, hm⟩, hmin⟩ := Finset.wellFoundedLT.wf.has_min
    { s : Finset (F.obj j) | ∃ (i : _) (f : i ⟶ j), ↑s = range (F.map f) }
    ⟨_, i, hi, hf.coe_toFinset⟩
  refine ⟨i, f, fun k g =>
    (F.ranges_directed j).directedOn_range.is_bot_of_is_min ⟨⟨i, f⟩, rfl⟩ ?_ _ ⟨⟨k, g⟩, rfl⟩⟩
  rintro _ ⟨⟨k', g'⟩, rfl⟩ hl
  refine (eq_of_le_of_not_lt hl ?_).ge
  have := hmin _ ⟨k', g', (m.finite_toSet.subset <| hm.substr hl).coe_toFinset⟩
  rwa [← Finset.coe_ssubset, Set.Finite.coe_toFinset, hm] at this

/-- The subfunctor of `F` obtained by restricting to the eventual range at each index. -/
@[simps obj map]
/-
**CategoryTheory.Functor.toEventualRanges** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：toEventualRanges : J ⥤ Type v where obj j
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.eventualRange_mapsTo`：eventualRange_mapsTo (f : j
 ⟶ i) : (F.eventualRange j).MapsTo (F.map f) (F.eventualRange i)

--- 原说明 ---
The subfunctor of `F` obtained by restricting to the eventual range at each inde
x.
-/
def toEventualRanges : J ⥤ Type v where
  obj j := F.eventualRange j
  map f := ↾((F.eventualRange_mapsTo f).restrict _ _ _)
/-
**CategoryTheory.Functor.toEventualRanges_finite** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.Functor`。
形式化陈述：toEventualRanges_finite [forall j, Finite (F.obj j)] : forall j, Finite (F
.toEventualRanges.obj j)
参数：F.obj j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance toEventualRanges_finite [∀ j, Finite (F.obj j)] : ∀ j, Finite (F.toEventualRanges.obj j) :=
  fun _ => Subtype.finite

/-- The sections of the functor `F : J ⥤ Type v` are in bijection with the sections of
`F.toEventualRanges`. -/
/-
**CategoryTheory.Functor.toEventualRangesSectionsEquiv** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Functor`。
形式化陈述：toEventualRangesSectionsEquiv : F.toEventualRanges.sections ≃ F.sections w
here toFun s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sections of the functor `F : J ⥤ Type v` are in bijection with the sections 
of
`F.toEventualRanges`.
-/
def toEventualRangesSectionsEquiv : F.toEventualRanges.sections ≃ F.sections where
  toFun s := ⟨_, fun f => Subtype.coe_inj.2 <| s.prop f⟩
  invFun s :=
    ⟨fun _ => ⟨_, mem_iInter₂.2 fun _ f => ⟨_, s.prop f⟩⟩, fun f => Subtype.ext <| s.prop f⟩

/-- If `F` satisfies the Mittag-Leffler condition, its restriction to eventual ranges is a
surjective functor. -/
/-
**CategoryTheory.Functor.surjective_toEventualRanges** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Functor`。
形式化陈述：surjective_toEventualRanges (h : F.IsMittagLeffler) ⦃i j⦄ (f : i ⟶ j) : Fu
nction.Surjective (F.toEventualRanges.map f)
参数：h : F.IsMittagLeffler；f : i ⟶ j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsMittagLeffler.subset_image_eventualRange`：∀ {J 
: Type u} [inst : CategoryTheory.Category.{v_1, u} J] (F : CategoryTheory.Functo
r J (Type v)) {i j : J},   F.IsMittagLeffler →     ∀ (f…

--- 原说明 ---
If `F` satisfies the Mittag-Leffler condition, its restriction to eventual range
s is a
surjective functor.
-/
theorem surjective_toEventualRanges (h : F.IsMittagLeffler) ⦃i j⦄ (f : i ⟶ j) :
    Function.Surjective (F.toEventualRanges.map f) := fun ⟨x, hx⟩ => by
  obtain ⟨y, hy, rfl⟩ := h.subset_image_eventualRange F f hx
  exact ⟨⟨y, hy⟩, rfl⟩

/-- If `F` is nonempty at each index and Mittag-Leffler, then so is `F.toEventualRanges`. -/
/-
**CategoryTheory.Functor.toEventualRanges_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Functor`。
形式化陈述：toEventualRanges_nonempty (h : F.IsMittagLeffler) [forall j : J, Nonempty 
(F.obj j)] (j : J) : Nonempty (F.toEventualRanges.obj j)
参数：h : F.IsMittagLeffler；F.obj j；j : J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Functor.isMittagLeffler_iff_eventualRange`：isMittagLeffle
r_iff_eventualRange : F.IsMittagLeffler ↔ forall j : J, exists (i : _) (f : i ⟶ 
j), F.eventualRange j = range (F.map f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.toEventualRanges_obj`：∀ {J : Type u} [inst : Cate
goryTheory.Category.{v_1, u} J] (F : CategoryTheory.Functor J (Type v))   [inst_
1 : CategoryTheory.IsCofilteredOr…

--- 原说明 ---
If `F` is nonempty at each index and Mittag-Leffler, then so is `F.toEventualRan
ges`.
-/
theorem toEventualRanges_nonempty (h : F.IsMittagLeffler) [∀ j : J, Nonempty (F.obj j)] (j : J) :
    Nonempty (F.toEventualRanges.obj j) := by
  let ⟨i, f, h⟩ := F.isMittagLeffler_iff_eventualRange.1 h j
  rw [toEventualRanges_obj, h]
  infer_instance

/-- If `F` has all arrows surjective, then it "factors through a poset". -/
/-
**CategoryTheory.Functor.thin_diagram_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Functor`。
形式化陈述：thin_diagram_of_surjective (Fsur : forall ⦃i j : J⦄ (f : i ⟶ j), Function.
Surjective (F.map f)) {i j} (f g : i ⟶ j) : F.map f = F.map g
参数：Fsur : forall ⦃i j : J⦄ (f : i ⟶ j), Function.Surjective (F.map f)；f g : i ⟶ 
j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsCofilteredOrEmpty.cone_maps`：∀ {C : Type u} {inst : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.IsCofilteredOrEmpty C] ⦃X 
Y : C⦄   (f g : X ⟶ Y), ∃ W h, Cat…
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Surjective.injective_comp_right`：∀ {α : Sort u_1} {β : Sort u_2
} {γ : Sort u_3} {f : α → β}, Function.Surjective f → Function.Injective fun g =
> g ∘ f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …

--- 原说明 ---
If `F` has all arrows surjective, then it "factors through a poset".
-/
theorem thin_diagram_of_surjective
    (Fsur : ∀ ⦃i j : J⦄ (f : i ⟶ j), Function.Surjective (F.map f)) {i j}
    (f g : i ⟶ j) : F.map f = F.map g := by
  let ⟨k, φ, hφ⟩ := IsCofilteredOrEmpty.cone_maps f g
  apply ConcreteCategory.ext
  have := congrArg F.map hφ
  simp only [map_comp, ConcreteCategory.ext_iff, DFunLike.ext_iff, comp_apply, ← funext_iff] at this
  simpa using (Fsur φ).injective_comp_right <| this
/-
**CategoryTheory.Functor.toPreimages_nonempty_of_surjective** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Functor`。
形式化陈述：toPreimages_nonempty_of_surjective [hFn : forall j : J, Nonempty (F.obj j)
] (Fsur : forall ⦃i j : J⦄ (f : i ⟶ j), Function.Surjective (F.map f)) (hs : s.N
onempty) (j) : Nonempty ((F.toPreimages s).obj j)
参数：F.obj j；Fsur : forall ⦃i j : J⦄ (f : i ⟶ j), Function.Surjective (F.map f)；hs
 : s.Nonempty；j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.toPreimages_obj`：∀ {J : Type u} [inst : CategoryT
heory.Category.{v_1, u} J] (F : CategoryTheory.Functor J (Type v)) {i : J}   (s 
: Set (F.obj i)) (j : J), (F…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.thin_diagram_of_surjective`：thin_diagram_of_surje
ctive (Fsur : forall ⦃i j : J⦄ (f : i ⟶ j), Function.Surjective (F.map f)) {i j}
 (f g : i ⟶ j) : F.map f = F.map g
-/
theorem toPreimages_nonempty_of_surjective [hFn : ∀ j : J, Nonempty (F.obj j)]
    (Fsur : ∀ ⦃i j : J⦄ (f : i ⟶ j), Function.Surjective (F.map f)) (hs : s.Nonempty) (j) :
    Nonempty ((F.toPreimages s).obj j) := by
  simp only [toPreimages_obj, nonempty_coe_sort, nonempty_iInter, mem_preimage]
  obtain h | ⟨⟨ji⟩⟩ := isEmpty_or_nonempty (j ⟶ i)
  · exact ⟨(hFn j).some, fun ji => h.elim ji⟩
  · obtain ⟨y, ys⟩ := hs
    obtain ⟨x, rfl⟩ := Fsur ji y
    exact ⟨x, fun ji' => (F.thin_diagram_of_surjective Fsur ji' ji).symm ▸ ys⟩
/-
**CategoryTheory.Functor.eval_section_injective_of_eventually_injective** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：eval_section_injective_of_eventually_injective {j} (Finj : forall (i) (f :
 i ⟶ j), Function.Injective (F.map f)) (i) (f : i ⟶ j) : (fun s : F.sections => 
s.val j).Injective
参数：Finj : forall (i) (f : i ⟶ j), Function.Injective (F.map f)；i；f : i ⟶ j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.IsCofilteredOrEmpty.cone_objs`：∀ {C : Type u} {inst : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.IsCofilteredOrEmpty C] (X 
Y : C),   ∃ W x x, True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem eval_section_injective_of_eventually_injective {j}
    (Finj : ∀ (i) (f : i ⟶ j), Function.Injective (F.map f)) (i) (f : i ⟶ j) :
    (fun s : F.sections => s.val j).Injective := by
  refine fun s₀ s₁ h => Subtype.ext <| funext fun k => ?_
  obtain ⟨m, mi, mk, _⟩ := IsCofilteredOrEmpty.cone_objs i k
  dsimp at h
  rw [← s₀.prop (mi ≫ f), ← s₁.prop (mi ≫ f)] at h
  rw [← s₀.prop mk, ← s₁.prop mk]
  exact congr_arg _ (Finj m (mi ≫ f) h)

section FiniteCofilteredSystem

variable [∀ j : J, Nonempty (F.obj j)] [∀ j : J, Finite (F.obj j)]
  (Fsur : ∀ ⦃i j : J⦄ (f : i ⟶ j), Function.Surjective (F.map f))
include Fsur

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.eval_section_surjective_of_surjective** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：eval_section_surjective_of_surjective (i : J) : (fun s : F.sections => s.v
al i).Surjective
参数：i : J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.toPreimages_nonempty_of_surjective`：toPreimages_n
onempty_of_surjective [hFn : forall j : J, Nonempty (F.obj j)] (Fsur : forall ⦃i
 j : J⦄ (f : i ⟶ j), Function.Surjective (F.map…
· 使用定理 `Set.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Set α).Nonem
pty
· 使用定理 `nonempty_sections_of_finite_cofiltered_system`：nonempty_sections_of_fini
te_cofiltered_system {J : Type u} [Category.{w} J] [IsCofilteredOrEmpty J] (F : 
J ⥤ Type v) [forall j : J, Finite (…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
-/
theorem eval_section_surjective_of_surjective (i : J) :
    (fun s : F.sections => s.val i).Surjective := fun x => by
  let s : Set (F.obj i) := {x}
  have := F.toPreimages_nonempty_of_surjective s Fsur (singleton_nonempty x)
  obtain ⟨sec, h⟩ := nonempty_sections_of_finite_cofiltered_system (F.toPreimages s)
  refine ⟨⟨fun j => (sec j).val, fun jk => by simpa [Subtype.ext_iff] using! h jk⟩, ?_⟩
  · have := (sec i).prop
    simp only [mem_iInter, mem_preimage] at this
    have := this (𝟙 i)
    rwa [map_id, id_apply] at this
/-
**CategoryTheory.Functor.eventually_injective** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Functor`。
形式化陈述：eventually_injective [Nonempty J] [Finite F.sections] : exists j, forall (
i) (f : i ⟶ j), Function.Injective (F.map f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_le_of_surjective`：card_le_of_surjective (f : α -> β) (h : F
unction.Surjective f) : card β <= card α
· 使用定理 `CategoryTheory.Functor.eval_section_surjective_of_surjective`：eval_secti
on_surjective_of_surjective (i : J) : (fun s : F.sections => s.val i).Surjective
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fintype.bijective_iff_surjective_and_card`：bijective_iff_surjective_and_
card (f : α -> β) : Bijective f ↔ Surjective f ∧ card α = card β
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sub_le_sub_iff_left`：∀ {n m k : ℕ}, n ≤ k → (k - m ≤ k - n ↔ n ≤ m)
· 使用定理 `Function.argmin_le`：argmin_le (a : α) [Nonempty α] : f (argmin f) <= f a
-/
theorem eventually_injective [Nonempty J] [Finite F.sections] :
    ∃ j, ∀ (i) (f : i ⟶ j), Function.Injective (F.map f) := by
  have : ∀ j, Fintype (F.obj j) := fun j => Fintype.ofFinite (F.obj j)
  have : Fintype F.sections := Fintype.ofFinite F.sections
  have card_le : ∀ j, Fintype.card (F.obj j) ≤ Fintype.card F.sections :=
    fun j => Fintype.card_le_of_surjective _ (F.eval_section_surjective_of_surjective Fsur j)
  let fn j := Fintype.card F.sections - Fintype.card (F.obj j)
  refine ⟨fn.argmin,
    fun i f => ((Fintype.bijective_iff_surjective_and_card _).2
      ⟨Fsur f, le_antisymm ?_ (Fintype.card_le_of_surjective _ <| Fsur f)⟩).1⟩
  rw [← Nat.sub_le_sub_iff_left (card_le i)]
  apply fn.argmin_le

end FiniteCofilteredSystem

end Functor

end CategoryTheory

