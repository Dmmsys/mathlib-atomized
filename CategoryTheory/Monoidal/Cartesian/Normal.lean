/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits

/-!
# Normal subgroup objects

In this file we define normal subgroups of group objects in a cartesian monoidal category as
a predicate on morphisms. A morphism `φ : H ⟶ G` of group objects is normal if it is mono, a
monoid morphism and the conjugation map `(g, h) ↦ g * h * g⁻¹` factors through `φ`.

This is applied in the study of group schemes.

## Main declarations

- `CategoryTheory.IsMonHom.Normal`: The predicate on morphisms to be a normal monoid morphism.
- `CategoryTheory.IsMonHom.normal_iff_normal_monoidHom`: A monoid morphism `H ⟶ G` that is mono
  is normal if and only if for every `X`, the image of `H(X)` in `G(X)` is a normal subgroup.

## References

- In the context of group schemes:
  [Görtz, Wedhorn, Algebraic Geometry II, Definition 27.3][goertz-wedhorn-2]
-/

@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C]

open MonObj GrpObj MonoidalCategory CartesianMonoidalCategory

/-- A morphism `φ : H ⟶ G` of additive group objects is a normal monoid homomorphism if it is a
monoid homomorphism that is mono and such that the conjugation map `(g, h) ↦ g + h - g`
factors through `φ`. -/
/-
**CategoryTheory.IsAddMonHom.Normal** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.
IsAddMonHom`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.CartesianMonoidalCategory C] →       {G H : C} → [Category
Theory.AddGrpObj G] → [CategoryTheory.AddGrpObj H] → (H ⟶ G) → Prop
参数：H ⟶ G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism `φ : H ⟶ G` of additive group objects is a normal monoid homomorphism
 if it is a
monoid homomorphism that is mono and such that the conjugation map `(g, h) ↦ g +
 h - g`
factors through `φ`.
-/
class IsAddMonHom.Normal {G H : C} [AddGrpObj G] [AddGrpObj H] (φ : H ⟶ G) : Prop where
  mono : Mono φ := by infer_instance
  isAddMonHom : IsAddMonHom φ := by infer_instance
  exists_comp_eq_addConj : ∃ ψ : G ⊗ H ⟶ H, ψ ≫ φ = G ◁ φ ≫ AddGrpObj.addConj G

attribute [instance] IsAddMonHom.Normal.mono IsAddMonHom.Normal.isAddMonHom

namespace IsMonHom

variable {G H K : C} [GrpObj G] [GrpObj H] [GrpObj K] {φ : H ⟶ G}

/-- A morphism `φ : H ⟶ G` of group objects is a normal monoid homomorphism if it is a
monoid homomorphism that is mono and such that the conjugation map `(g, h) ↦ g * h * g⁻¹`
factors through `φ`. -/
@[to_additive]
/-
**CategoryTheory.IsMonHom.Normal** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory.IsMonH
om`。
形式化陈述：Normal (φ : H ⟶ G) : Prop where mono : Mono φ
参数：φ : H ⟶ G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism `φ : H ⟶ G` of group objects is a normal monoid homomorphism if it is
 a
monoid homomorphism that is mono and such that the conjugation map `(g, h) ↦ g *
 h * g⁻¹`
factors through `φ`.
-/
class Normal (φ : H ⟶ G) : Prop where
  mono : Mono φ := by infer_instance
  isMonHom : IsMonHom φ := by infer_instance
  exists_comp_eq_conj (φ) : ∃ ψ : G ⊗ H ⟶ H, ψ ≫ φ = G ◁ φ ≫ conj G

attribute [instance] Normal.mono Normal.isMonHom

@[to_additive]
/-
**CategoryTheory.IsMonHom.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.IsMonHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Normal (𝟙 G) where
  exists_comp_eq_conj := by cat_disch

@[to_additive]
/-
**CategoryTheory.IsMonHom.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.IsMonHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Normal η[G] where
  exists_comp_eq_conj := by
    use toUnit _
    simp [conj, comp_mul, comp_inv, toUnit_unique _ (toUnit _), ← Hom.one_def]

@[to_additive]
/-
**CategoryTheory.IsMonHom.isNormalHom_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.IsMonHom`。
形式化陈述：isNormalHom_iff [IsMonHom φ] [Mono φ] : Normal φ ↔ exists ψ : G otimes H ⟶
 H, ψ ≫ φ = G ◁ φ ≫ conj G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsMonHom.Normal.exists_comp_eq_conj`：∀ {C : Type u_1} {in
st : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.CartesianMon
oidalCategory C}   {G H : C} {inst_2 : C…
-/
lemma isNormalHom_iff [IsMonHom φ] [Mono φ] : Normal φ ↔ ∃ ψ : G ⊗ H ⟶ H, ψ ≫ φ = G ◁ φ ≫ conj G :=
  ⟨fun h ↦ h.exists_comp_eq_conj, fun h ↦ ⟨‹_›, ‹_›, h⟩⟩

/-- If `φ` is mono, it is a normal group homomorphism if and only if for all `X` the image of
`H(X)` in `G(X)` is a normal subgroup. -/
@[to_additive /-- If `φ` is mono, it is a normal additive group homomorphism if and only if for all
`X` the image of `H(X)` in `G(X)` is a normal additive subgroup. -/]
/-
**CategoryTheory.IsMonHom.normal_iff_normal_monoidHom** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.IsMonHom`。
形式化陈述：normal_iff_normal_monoidHom [IsMonHom φ] [Mono φ] : Normal φ ↔ forall (X :
 C), (monoidHom φ X).range.Normal
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.IsMonHom.isNormalHom_iff`：isNormalHom_iff [IsMonHom φ] [M
ono φ] : Normal φ ↔ exists ψ : G otimes H ⟶ H, ψ ≫ φ = G ◁ φ ≫ conj G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.IsMonHom.monoidHom_apply`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheory.CartesianMonoidalCategory
 C]   {M N : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.lift_whiskerLeft_assoc`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Carte
sianMonoidalCategory C]   {X Y Z W : C} (f : X ⟶ Y) (…
· 使用定理 `CategoryTheory.GrpObj.lift_conj_eq_mul_mul_inv`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.CartesianMonoidalCateg
ory C] {X G : C}   [inst_2 : Categor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Subgroup.Normal.conj_mem`：∀ {G : Type u_1} [inst : Group G] {H : Subgrou
p G}, H.Normal → ∀ n ∈ H, ∀ (g : G), g * n * g⁻¹ ∈ H
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.MonObj.comp_mul`：∀ {C : Type u_1} [inst : CategoryTheory.
Category.{v, u_1} C] [inst_1 : CategoryTheory.CartesianMonoidalCategory C]   {M 
X Y : C} [inst_2 : C…
· 使用定理 `CategoryTheory.GrpObj.comp_inv`：∀ {C : Type u} [inst : CategoryTheory.Ca
tegory.{v, u} C] [inst_1 : CategoryTheory.CartesianMonoidalCategory C]   {G X Y 
: C} [inst_2 : Categ…
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.FullyFaithful.map_preimage`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.whiskerLeft_fst`：whiskerLeft_fs
t (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ f ≫ fst _ _ = fst _ _
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.whiskerLeft_snd`：whiskerLeft_sn
d (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ f ≫ snd _ _ = snd _ _ ≫ f
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem normal_iff_normal_monoidHom [IsMonHom φ] [Mono φ] :
    Normal φ ↔ ∀ (X : C), (monoidHom φ X).range.Normal := by
  rw [isNormalHom_iff]
  refine ⟨?_, ?_⟩
  · intro ⟨ψ, hψ⟩ X
    constructor
    rintro - ⟨x, rfl⟩ z
    exact ⟨lift z x ≫ ψ, by simp [hψ]⟩
  · intro hnormal
    have (X : C) (g : X ⟶ G) (h : X ⟶ H) : ∃ (h' : X ⟶ H), h' ≫ φ = g * h ≫ φ * g⁻¹ :=
      (hnormal X).conj_mem (h ≫ φ) (by simp) g
    choose h' hh' using this
    refine ⟨Yoneda.fullyFaithful.preimage ?_, ?_⟩
    · refine ⟨fun X ↦ ↾fun x ↦ h' _ (x ≫ fst _ _) (x ≫ snd _ _), fun X Y f ↦ ?_⟩
      ext
      simp [← cancel_mono φ, hh', comp_mul, comp_inv]
    · refine yoneda.map_injective ?_
      ext
      simp [hh', conj, comp_mul, comp_inv]

@[to_additive]
/-
**CategoryTheory.IsMonHom.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.IsMonHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [BraidedCategory C] [IsCommMonObj G] [IsMonHom φ] [Mono φ] :
    Normal φ := by
  simp [isNormalHom_iff, conj_eq_snd_of_isCommMonObj]

@[to_additive]
/-
**CategoryTheory.IsMonHom.Normal.of_isPullback_** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.IsMonHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Normal.of_isPullback_η [IsMonHom φ] {P : C} (p : G ⟶ P) [GrpObj P] [IsMonHom p]
    (h : IsPullback φ (toUnit _) p η) :
    Normal φ where
  mono := h.mono_fst_of_mono
  exists_comp_eq_conj := by
    refine ⟨h.lift (G ◁ φ ≫ conj G) (toUnit _) ?_, ?_⟩
    · simp [conj, comp_mul, inv_comp, mul_comp, h.w, comp_inv, ← Hom.one_def]
    · simp

end CategoryTheory.IsMonHom

