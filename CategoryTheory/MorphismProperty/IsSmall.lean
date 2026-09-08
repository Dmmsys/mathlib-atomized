/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.Logic.Small.Basic

/-!
# Small classes of morphisms

A class of morphisms `W : MorphismProperty C` is `w`-small
if the corresponding set in `Set (Arrow C)` is.

-/

public section

universe w t v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace MorphismProperty

variable (W : MorphismProperty C)

/-- A class of morphisms `W : MorphismProperty C` is `w`-small
if the corresponding set in `Set (Arrow C)` is. -/
@[pp_with_univ]
/-
**CategoryTheory.MorphismProperty.IsSmall** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryT
heory.MorphismProperty`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
MorphismProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class of morphisms `W : MorphismProperty C` is `w`-small
if the corresponding set in `Set (Arrow C)` is.
-/
class IsSmall : Prop where
  small_toSet : Small.{w} W.toSet

attribute [instance] IsSmall.small_toSet
/-
**CategoryTheory.MorphismProperty.isSmall_ofHoms** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.MorphismProperty`。
形式化陈述：isSmall_ofHoms {ι : Type t} [Small.{w} ι] {A B : ι -> C} (f : forall i, A 
i ⟶ B i) : IsSmall.{w} (ofHoms f)
参数：f : forall i, A i ⟶ B i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `small_of_surjective`：small_of_surjective {α : Type v} {β : Type w} [Smal
l.{u} α] {f : α -> β} (hf : Function.Surjective f) : Small.{u} β
-/
instance isSmall_ofHoms {ι : Type t} [Small.{w} ι] {A B : ι → C} (f : ∀ i, A i ⟶ B i) :
    IsSmall.{w} (ofHoms f) := by
  let φ (i : ι) : (ofHoms f).toSet := ⟨Arrow.mk (f i), ⟨i⟩⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨⟨_, _, f⟩, ⟨i⟩⟩
    exact ⟨i, rfl⟩
  exact ⟨small_of_surjective hφ⟩
/-
**CategoryTheory.MorphismProperty.isSmall_iff_eq_ofHoms** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.MorphismProperty`。
形式化陈述：isSmall_iff_eq_ofHoms : IsSmall.{w} W ↔ exists (ι : Type w) (A B : ι -> C)
 (f : forall i, A i ⟶ B i), W = ofHoms f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsSmall.small_toSet`：∀ {C : Type u} {ins
t : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.MorphismProperty C}   
[self : CategoryTheory.MorphismProperty.I…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.ofHoms_iff`：ofHoms_iff {ι : Type*} {X Y 
: ι -> C} (f : forall i, X i ⟶ Y i) {A B : C} (g : A ⟶ B) : ofHoms f g ↔ exists 
i, Arrow.mk g = Arrow.mk (f i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Arrow.mk_eq`：mk_eq (f : Arrow T) : Arrow.mk f.hom = f
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.MorphismProperty.arrow_mk_mem_toSet_iff`：arrow_mk_mem_toS
et_iff {X Y : C} (f : X ⟶ Y) : Arrow.mk f in P.toSet ↔ P f
-/
lemma isSmall_iff_eq_ofHoms :
    IsSmall.{w} W ↔ ∃ (ι : Type w) (A B : ι → C) (f : ∀ i, A i ⟶ B i),
      W = ofHoms f := by
  constructor
  · intro
    refine ⟨Shrink.{w} W.toSet, _, _, fun i ↦ ((equivShrink _).symm i).1.hom, ?_⟩
    ext A B f
    rw [ofHoms_iff]
    constructor
    · intro hf
      exact ⟨equivShrink _ ⟨f, hf⟩, by simp⟩
    · rintro ⟨i, hi⟩
      simp only [← W.arrow_mk_mem_toSet_iff, hi, Arrow.mk_eq, Subtype.coe_prop]
  · rintro ⟨_, _, _, _, rfl⟩
    infer_instance
/-
**CategoryTheory.MorphismProperty.isSmall_iSup** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.MorphismProperty`。
形式化陈述：isSmall_iSup {α : Type*} (W : α -> MorphismProperty C) [Small.{w} α] [fora
ll a, IsSmall.{w} (W a)] : IsSmall.{w} (iSup W) where small_toSet
参数：W : α -> MorphismProperty C；W a。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.toSet_iSup`：toSet_iSup {ι : Type*} (W : 
ι -> MorphismProperty C) : (⨆ i, W i).toSet = ⋃ i, (W i).toSet
· 使用定理 `small_of_surjective`：small_of_surjective {α : Type v} {β : Type w} [Smal
l.{u} α] {f : α -> β} (hf : Function.Surjective f) : Small.{u} β
· 使用定理 `CategoryTheory.MorphismProperty.IsSmall.small_toSet`：∀ {C : Type u} {ins
t : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.MorphismProperty C}   
[self : CategoryTheory.MorphismProperty.I…
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
instance isSmall_iSup {α : Type*} (W : α → MorphismProperty C)
    [Small.{w} α] [∀ a, IsSmall.{w} (W a)] :
    IsSmall.{w} (iSup W) where
  small_toSet := by
    rw [toSet_iSup]
    refine small_of_surjective (f := fun (⟨i, f⟩ : Σ i, (W i).toSet) ↦
      ⟨f, by rw [Set.mem_iUnion]; exact ⟨i, f.prop⟩⟩) ?_
    rintro ⟨f, hf⟩
    simp only [Set.mem_iUnion] at hf
    obtain ⟨i, hf⟩ := hf
    exact ⟨⟨i, ⟨_, hf⟩⟩, rfl⟩
/-
**CategoryTheory.MorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Mor
phismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type t} [Small.{w} α] (W : α → MorphismProperty C) [∀ i, IsSmall.{w} (W i)] :
    IsSmall.{w} (⨆ i, W i) := by
  choose α A B f hf using fun i ↦ (isSmall_iff_eq_ofHoms.{w} (W i)).1 inferInstance
  simp only [hf, iSup_ofHoms]
  infer_instance

end MorphismProperty

end CategoryTheory

