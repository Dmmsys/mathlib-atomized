/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Shift.ShiftSequence
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Algebra.Homology.ExactSequence

/-! # Homological functors

In this file, given a functor `F : C ⥤ A` from a pretriangulated category to
an abelian category, we define the type class `F.IsHomological`, which is the property
that `F` sends distinguished triangles in `C` to exact sequences in `A`.

If `F` has been endowed with `[F.ShiftSequence ℤ]`, then we may think
of the functor `F` as a `H^0`, and then the `H^n` functors are the functors `F.shift n : C ⥤ A`:
we have isomorphisms `(F.shift n).obj X ≅ F.obj (X⟦n⟧)`, but through the choice of this
"shift sequence", the user may provide functors with better definitional properties.

Given a triangle `T` in `C`, we define a connecting homomorphism
`F.homologySequenceδ T n₀ n₁ h : (F.shift n₀).obj T.obj₃ ⟶ (F.shift n₁).obj T.obj₁`
under the assumption `h : n₀ + 1 = n₁`. When `T` is distinguished, this connecting
homomorphism is part of a long exact sequence
`... ⟶ (F.shift n₀).obj T.obj₁ ⟶ (F.shift n₀).obj T.obj₂ ⟶ (F.shift n₀).obj T.obj₃ ⟶ ...`

The exactness of this long exact sequence is given by three lemmas
`F.homologySequence_exact₁`, `F.homologySequence_exact₂` and `F.homologySequence_exact₃`.

If `F` is a homological functor, we define the strictly full triangulated subcategory
`F.homologicalKernel`: it consists of objects `X : C` such that for all `n : ℤ`,
`(F.shift n).obj X` (or `F.obj (X⟦n⟧)`) is zero. We show that a morphism `f` in `C`
belongs to `F.homologicalKernel.trW` (i.e. the cone of `f` is in this kernel) iff
`(F.shift n).map f` is an isomorphism for all `n : ℤ`.

Note: depending on the sources, homological functors are sometimes
called cohomological functors, while certain authors use "cohomological functors"
for "contravariant" functors (i.e. functors `Cᵒᵖ ⥤ A`).

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*][verdier1996]

-/

@[expose] public section

namespace CategoryTheory

open Category Limits Pretriangulated ZeroObject Preadditive

variable {C D A : Type*} [Category* C] [HasShift C ℤ]
  [Category* D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ (n : ℤ), (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]
  [Category* A]

namespace Functor

variable (F : C ⥤ A)

/-- The kernel of a homological functor `F : C ⥤ A` is the strictly full
triangulated subcategory consisting of objects `X` such that
for all `n : ℤ`, `F.obj (X⟦n⟧)` is zero. -/
/-
**CategoryTheory.Functor.homologicalKernel** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：homologicalKernel : ObjectProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel of a homological functor `F : C ⥤ A` is the strictly full
triangulated subcategory consisting of objects `X` such that
for all `n : ℤ`, `F.obj (X⟦n⟧)` is zero.
-/
def homologicalKernel : ObjectProperty C :=
  fun X ↦ ∀ (n : ℤ), IsZero (F.obj (X⟦n⟧))
/-
**CategoryTheory.Functor.mem_homologicalKernel_iff** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Functor`。
形式化陈述：mem_homologicalKernel_iff [F.ShiftSequence Int] (X : C) : F.homologicalKer
nel X ↔ forall (n : Int), IsZero ((F.shift n).obj X)
参数：X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.isZero_iff`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (e : X ≅ Y),   CategoryTheory.Limits.IsZero X ↔ Catego
ryTheory.Limits.IsZ…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_homologicalKernel_iff [F.ShiftSequence ℤ] (X : C) :
    F.homologicalKernel X ↔ ∀ (n : ℤ), IsZero ((F.shift n).obj X) := by
  simp only [← fun (n : ℤ) => Iso.isZero_iff ((F.isoShift n).app X),
    homologicalKernel, comp_obj]

section Pretriangulated

variable [HasZeroObject C] [Preadditive C] [∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive]
  [Pretriangulated C] [Abelian A]

/-- A functor from a pretriangulated category to an abelian category is a homological functor
if it sends distinguished triangles to exact sequences. -/
/-
**CategoryTheory.Functor.IsHomological** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：{C : Type u_1} →   {A : Type u_3} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.HasShift C ℤ] →         [inst_2 : C
ategoryTheory.Category.{v_3, u_3} A] →           CategoryTheory.Functor C A →   
          [inst_3 : CategoryTheory.Limits.HasZeroObject C] →               [inst
_4 : CategoryTheory.Preadditive C] →                 [inst_5 : ∀ (n : ℤ), (Categ
oryTheory.shiftFunctor C n).Additive] →                   [CategoryTheory.Pretri
angulated C] → [CategoryTheory.Abelian A] → Prop
参数：n : ℤ；CategoryTheory.shiftFunctor C n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor from a pretriangulated category to an abelian category is a homologica
l functor
if it sends distinguished triangles to exact sequences.
-/
class IsHomological : Prop extends F.PreservesZeroMorphisms where
  exact (T : Triangle C) (hT : T ∈ distTriang C) :
    ((shortComplexOfDistTriangle T hT).map F).Exact
/-
**CategoryTheory.Functor.map_distinguished_exact** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Functor`。
形式化陈述：map_distinguished_exact [F.IsHomological] (T : Triangle C) (hT : T in dist
Triang C) : ((shortComplexOfDistTriangle T hT).map F).Exact
参数：T : Triangle C；hT : T in distTriang C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsHomological.exact`：∀ {C : Type u_1} {A : Type u
_3} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.HasSh
ift C ℤ}   {inst_2 : CategoryThe…
-/
lemma map_distinguished_exact [F.IsHomological] (T : Triangle C) (hT : T ∈ distTriang C) :
    ((shortComplexOfDistTriangle T hT).map F).Exact :=
  IsHomological.exact _ hT
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (L : C ⥤ D) (F : D ⥤ A) [L.CommShift ℤ] [L.IsTriangulated] [F.IsHomological] :
    (L ⋙ F).IsHomological where
  exact T hT := F.map_distinguished_exact _ (L.map_distinguished T hT)
/-
**CategoryTheory.Functor.IsHomological.mk'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Functor.IsHomological`。
形式化陈述：∀ {C : Type u_1} {A : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1}
 C] [inst_1 : CategoryTheory.HasShift C ℤ]   [inst_2 : CategoryTheory.Category.{
v_3, u_3} A] (F : CategoryTheory.Functor C A)   [inst_3 : CategoryTheory.Limits.
HasZeroObject C] [inst_4 : CategoryTheory.Preadditive C]   [inst_5 : ∀ (n : ℤ), 
(CategoryTheory.shiftFunctor C n).Additive] [inst_6 : CategoryTheory.Pretriangul
ated C]   [inst_7 : CategoryTheory.Abelian A] [inst_8 : F.PreservesZeroMorphisms
],   (∀ (T : CategoryTheory.Pretriangulated.Triangle C) (hT : T ∈ CategoryTheory
.Pretriangulated.distinguishedTriangles),       ∃ T' e, ((CategoryTheory.Pretria
ngulated.shortComplexOfDistTriangle T' ⋯).map F).Exact) →     F.IsHomological
参数：F : CategoryTheory.Functor C A；n : ℤ；CategoryTheory.shiftFunctor C n；∀ (T : C
ategoryTheory.Pretriangulated.Triangle C) (hT : T ∈ CategoryTheory.Pretriangulat
ed.distinguishedTriangles),       ∃ T' e, ((CategoryTheory.Pretriangulated.short
ComplexOfDistTriangle T' ⋯).map F).Exact。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Pretriangulated.isomorphic_distinguished`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZer
oObject C}   {inst_2 : CategoryTheory.HasShif…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.ShortComplex.exact_iff_of_iso`：exact_iff_of_iso (e : S₁ ≅
 S₂) : S₁.Exact ↔ S₂.Exact
-/
lemma IsHomological.mk' [F.PreservesZeroMorphisms]
    (hF : ∀ (T : Pretriangulated.Triangle C) (hT : T ∈ distTriang C),
      ∃ (T' : Pretriangulated.Triangle C) (e : T ≅ T'),
      ((shortComplexOfDistTriangle T' (isomorphic_distinguished _ hT _ e.symm)).map F).Exact) :
    F.IsHomological where
  exact T hT := by
    obtain ⟨T', e, h'⟩ := hF T hT
    exact (ShortComplex.exact_iff_of_iso
      (F.mapShortComplex.mapIso ((shortComplexOfDistTriangleIsoOfIso e hT)))).2 h'
/-
**CategoryTheory.Functor.IsHomological.of_iso** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Functor.IsHomological`。
形式化陈述：∀ {C : Type u_1} {A : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1}
 C] [inst_1 : CategoryTheory.HasShift C ℤ]   [inst_2 : CategoryTheory.Category.{
v_3, u_3} A] [inst_3 : CategoryTheory.Limits.HasZeroObject C]   [inst_4 : Catego
ryTheory.Preadditive C] [inst_5 : ∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).A
dditive]   [inst_6 : CategoryTheory.Pretriangulated C] [inst_7 : CategoryTheory.
Abelian A] {F₁ F₂ : CategoryTheory.Functor C A}   [F₁.IsHomological] (e : F₁ ≅ F
₂), F₂.IsHomological
参数：n : ℤ；CategoryTheory.shiftFunctor C n；e : F₁ ≅ F₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.preservesZeroMorphisms_of_iso`：preservesZeroMorph
isms_of_iso {F₁ F₂ : C ⥤ D} [F₁.PreservesZeroMorphisms] (e : F₁ ≅ F₂) : F₂.Prese
rvesZeroMorphisms where map_zero X Y
· 使用定理 `CategoryTheory.Functor.IsHomological.toPreservesZeroMorphisms`：∀ {C : Ty
pe u_1} {A : Type u_3} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : C
ategoryTheory.HasShift C ℤ}   {inst_2 : CategoryThe…
· 使用引理 `CategoryTheory.ShortComplex.exact_of_iso`：exact_of_iso (e : S₁ ≅ S₂) (h 
: S₁.Exact) : S₂.Exact
· 使用引理 `CategoryTheory.Functor.map_distinguished_exact`：map_distinguished_exact 
[F.IsHomological] (T : Triangle C) (hT : T in distTriang C) : ((shortComplexOfDi
stTriangle T hT).map F).Exact
-/
lemma IsHomological.of_iso {F₁ F₂ : C ⥤ A} [F₁.IsHomological] (e : F₁ ≅ F₂) :
    F₂.IsHomological :=
  have := preservesZeroMorphisms_of_iso e
  ⟨fun T hT => ShortComplex.exact_of_iso (ShortComplex.mapNatIso _ e)
    (F₁.map_distinguished_exact T hT)⟩

section

variable [F.IsHomological]

/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : F.homologicalKernel.IsClosedUnderIsomorphisms where
  of_iso e hX n := (hX n).of_iso ((shiftFunctor C n ⋙ F).mapIso e.symm)
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : F.homologicalKernel.IsTriangulated where
  exists_zero := ⟨0, isZero_zero C,
    fun n ↦ (shiftFunctor C n ⋙ F).map_isZero (isZero_zero C)⟩
  toIsStableUnderShift := ⟨fun a ↦ ⟨fun X hX b ↦
    (hX (a + b)).of_iso (F.mapIso ((shiftFunctorAdd C a b).app X).symm)⟩⟩
  toIsTriangulatedClosed₂ :=
    ObjectProperty.IsTriangulatedClosed₂.mk' (fun T hT h₁ h₃ n ↦
      (F.map_distinguished_exact _
        (Triangle.shift_distinguished T hT n)).isZero_of_both_zeros
          ((h₁ n).eq_of_src _ _) ((h₃ n).eq_of_tgt _ _))

end

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (priority := 100) [F.IsHomological] :
    PreservesLimitsOfShape (Discrete WalkingPair) F := by
  suffices ∀ (X₁ X₂ : C), PreservesLimit (pair X₁ X₂) F from
    ⟨fun {X} => preservesLimit_of_iso_diagram F (diagramIsoPair X).symm⟩
  intro X₁ X₂
  have : HasBinaryBiproduct (F.obj X₁) (F.obj X₂) := HasBinaryBiproducts.has_binary_biproduct _ _
  have : Mono (F.biprodComparison X₁ X₂) := by
    rw [mono_iff_cancel_zero]
    intro Z f hf
    let S := (ShortComplex.mk _ _ (biprod.inl_snd (X := X₁) (Y := X₂))).map F
    have : Mono S.f := by dsimp [S]; infer_instance
    have ex : S.Exact := F.map_distinguished_exact _ (binaryBiproductTriangle_distinguished X₁ X₂)
    obtain ⟨g, rfl⟩ := ex.lift' f (by simpa using! hf =≫ biprod.snd)
    dsimp [S] at hf ⊢
    replace hf := hf =≫ biprod.fst
    simp only [assoc, biprodComparison_fst, zero_comp, ← F.map_comp, biprod.inl_fst,
      F.map_id, comp_id] at hf
    rw [hf, zero_comp]
  have : PreservesBinaryBiproduct X₁ X₂ F := preservesBinaryBiproduct_of_mono_biprodComparison _
  apply Limits.preservesBinaryProduct_of_preservesBinaryBiproduct
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [F.IsHomological] : F.Additive :=
  F.additive_of_preserves_binary_products
/-
**CategoryTheory.Functor.isHomological_of_localization** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Functor`。
形式化陈述：isHomological_of_localization (L : C ⥤ D) [L.CommShift Int] [L.IsTriangula
ted] [L.mapArrow.EssSurj] (F : D ⥤ A) (G : C ⥤ A) (e : L ⋙ F ≅ G) [G.IsHomologic
al] : F.IsHomological
参数：L : C ⥤ D；F : D ⥤ A；G : C ⥤ A；e : L ⋙ F ≅ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_map_zero_object`：preser
vesZeroMorphisms_of_map_zero_object (i : F.obj 0 ≅ 0) : PreservesZeroMorphisms F
 where map_zero X Y
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.Functor.IsTriangulated.instPreservesZeroMorphisms`：∀ {C :
 Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.IsHomological.toPreservesZeroMorphisms`：∀ {C : Ty
pe u_1} {A : Type u_3} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : C
ategoryTheory.HasShift C ℤ}   {inst_2 : CategoryThe…
· 使用定理 `CategoryTheory.Functor.IsHomological.of_iso`：∀ {C : Type u_1} {A : Type 
u_3} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.HasS
hift C ℤ]   [inst_2 : CategoryThe…
· 使用定理 `CategoryTheory.Functor.IsHomological.mk'`：∀ {C : Type u_1} {A : Type u_3
} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.HasShif
t C ℤ]   [inst_2 : CategoryThe…
· 使用定理 `CategoryTheory.Pretriangulated.isomorphic_distinguished`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZer
oObject C}   {inst_2 : CategoryTheory.HasShif…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.distTriang_iff`：distTriang_iff (T : Triangle D) :
 (T in distTriang D) ↔ T in L.essImageDistTriang
· 使用引理 `CategoryTheory.Functor.map_distinguished_exact`：map_distinguished_exact 
[F.IsHomological] (T : Triangle C) (hT : T in distTriang C) : ((shortComplexOfDi
stTriangle T hT).map F).Exact
-/
lemma isHomological_of_localization (L : C ⥤ D)
    [L.CommShift ℤ] [L.IsTriangulated] [L.mapArrow.EssSurj] (F : D ⥤ A)
    (G : C ⥤ A) (e : L ⋙ F ≅ G) [G.IsHomological] :
    F.IsHomological := by
  have : F.PreservesZeroMorphisms := preservesZeroMorphisms_of_map_zero_object
    (F.mapIso L.mapZeroObject.symm ≪≫ e.app _ ≪≫ G.mapZeroObject)
  have : (L ⋙ F).IsHomological := IsHomological.of_iso e.symm
  refine IsHomological.mk' _ (fun T hT => ?_)
  rw [L.distTriang_iff] at hT
  obtain ⟨T₀, e, hT₀⟩ := hT
  exact ⟨L.mapTriangle.obj T₀, e, (L ⋙ F).map_distinguished_exact _ hT₀⟩

end Pretriangulated

section

/-- The connecting homomorphism in the long exact sequence attached to a homological
functor and a distinguished triangle. -/
/-
**CategoryTheory.Functor.homologySequence** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The connecting homomorphism in the long exact sequence attached to a homological
functor and a distinguished triangle.
-/
noncomputable def homologySequenceδ
    [F.ShiftSequence ℤ] (T : Triangle C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (F.shift n₀).obj T.obj₃ ⟶ (F.shift n₁).obj T.obj₁ :=
  F.shiftMap T.mor₃ n₀ n₁ (by rw [add_comm 1, h])

variable {T T'}

@[reassoc]
/-
**CategoryTheory.Functor.homologySequence** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homologySequenceδ_naturality
    [F.ShiftSequence ℤ] (T T' : Triangle C) (φ : T ⟶ T') (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (F.shift n₀).map φ.hom₃ ≫ F.homologySequenceδ T' n₀ n₁ h =
      F.homologySequenceδ T n₀ n₁ h ≫ (F.shift n₁).map φ.hom₁ := by
  dsimp only [homologySequenceδ]
  rw [← shiftMap_comp', ← φ.comm₃, shiftMap_comp]

variable (T)
variable [HasZeroObject C] [Preadditive C] [∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive]
  [Pretriangulated C] [Abelian A] [F.IsHomological]
variable [F.ShiftSequence ℤ] (T T' : Triangle C) (hT : T ∈ distTriang C)
  (hT' : T' ∈ distTriang C) (φ : T ⟶ T') (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)

section
include hT
@[reassoc]
/-
**CategoryTheory.Functor.comp_homologySequence** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_homologySequenceδ :
    (F.shift n₀).map T.mor₂ ≫ F.homologySequenceδ T n₀ n₁ h = 0 := by
  dsimp only [homologySequenceδ]
  rw [← F.shiftMap_comp', comp_distTriang_mor_zero₂₃ _ hT, shiftMap_zero]

@[reassoc]
/-
**CategoryTheory.Functor.homologySequence** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homologySequenceδ_comp :
    F.homologySequenceδ T n₀ n₁ h ≫ (F.shift n₁).map T.mor₁ = 0 := by
  dsimp only [homologySequenceδ]
  rw [← F.shiftMap_comp, comp_distTriang_mor_zero₃₁ _ hT, shiftMap_zero]

@[reassoc]
/-
**CategoryTheory.Functor.homologySequence_comp** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：homologySequence_comp : (F.shift n₀).map T.mor₁ ≫ (F.shift n₀).map T.mor₂ 
= 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Pretriangulated.comp_distTriang_mor_zero₁₂`：comp_distTria
ng_mor_zero₁₂ (T) (H : T in distTriang C) : T.mor₁ ≫ T.mor₂ = 0
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `CategoryTheory.Functor.instPreservesZeroMorphismsShift`：∀ {C : Type u_1}
 {A : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Catego
ryTheory.Category.{v_3, u_3} A] (F : Categor…
· 使用定理 `CategoryTheory.Functor.IsHomological.toPreservesZeroMorphisms`：∀ {C : Ty
pe u_1} {A : Type u_3} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : C
ategoryTheory.HasShift C ℤ}   {inst_2 : CategoryThe…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
-/
lemma homologySequence_comp :
    (F.shift n₀).map T.mor₁ ≫ (F.shift n₀).map T.mor₂ = 0 := by
  rw [← Functor.map_comp, comp_distTriang_mor_zero₁₂ _ hT, Functor.map_zero]

attribute [local simp] smul_smul

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.homologySequence_exact** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homologySequence_exact₂ :
    (ShortComplex.mk _ _ (F.homologySequence_comp T hT n₀)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (F.map_distinguished_exact _
    (Triangle.shift_distinguished _ hT n₀))
  exact ShortComplex.isoMk ((F.isoShift n₀).app _)
    (n₀.negOnePow • ((F.isoShift n₀).app _)) ((F.isoShift n₀).app _)
    (by simp) (by simp)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.homologySequence_exact** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homologySequence_exact₃ :
    (ShortComplex.mk _ _ (F.comp_homologySequenceδ T hT _ _ h)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (F.homologySequence_exact₂ _ (rot_of_distTriang _ hT) n₀)
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    ((F.shiftIso 1 n₀ n₁ (by lia)).app _) (by simp) (by simp [homologySequenceδ, shiftMap])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.homologySequence_exact** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homologySequence_exact₁ :
    (ShortComplex.mk _ _ (F.homologySequenceδ_comp T hT _ _ h)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (F.homologySequence_exact₂ _ (inv_rot_of_distTriang _ hT) n₁)
  refine ShortComplex.isoMk (-((F.shiftIso (-1) n₁ n₀ (by lia)).app _))
    (Iso.refl _) (Iso.refl _) ?_ (by simp)
  dsimp
  simp only [homologySequenceδ, neg_comp, map_neg, comp_id,
    F.shiftIso_hom_app_comp_shiftMap_of_add_eq_zero T.mor₃ (-1) (neg_add_cancel 1) n₀ n₁
      (by lia)]
/-
**CategoryTheory.Functor.homologySequence_epi_shift_map_mor** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homologySequence_epi_shift_map_mor₁_iff :
    Epi ((F.shift n₀).map T.mor₁) ↔ (F.shift n₀).map T.mor₂ = 0 :=
  (F.homologySequence_exact₂ T hT n₀).epi_f_iff
/-
**CategoryTheory.Functor.homologySequence_mono_shift_map_mor** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homologySequence_mono_shift_map_mor₁_iff :
    Mono ((F.shift n₁).map T.mor₁) ↔ F.homologySequenceδ T n₀ n₁ h = 0 :=
  (F.homologySequence_exact₁ T hT n₀ n₁ h).mono_g_iff
/-
**CategoryTheory.Functor.homologySequence_epi_shift_map_mor** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homologySequence_epi_shift_map_mor₂_iff :
    Epi ((F.shift n₀).map T.mor₂) ↔ F.homologySequenceδ T n₀ n₁ h = 0 :=
  (F.homologySequence_exact₃ T hT n₀ n₁ h).epi_f_iff
/-
**CategoryTheory.Functor.homologySequence_mono_shift_map_mor** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homologySequence_mono_shift_map_mor₂_iff :
    Mono ((F.shift n₀).map T.mor₂) ↔ (F.shift n₀).map T.mor₁ = 0 :=
  (F.homologySequence_exact₂ T hT n₀).mono_g_iff
end

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.mem_homologicalKernel_trW_iff** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Functor`。
形式化陈述：mem_homologicalKernel_trW_iff {X Y : C} (f : X ⟶ Y) : F.homologicalKernel.
trW f ↔ forall (n : Int), IsIso ((F.shift n).map f)
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Pretriangulated.distinguished_cocone_triangle`：∀ {C : Typ
e u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.H
asZeroObject C}   {inst_2 : CategoryTheory.HasShif…
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `CategoryTheory.ObjectProperty.trW_iff_of_distinguished`：trW_iff_of_disti
nguished [P.IsClosedUnderIsomorphisms] (T : Triangle C) (hT : T in distTriang C)
 : P.trW T.mor₁ ↔ P T.obj₃
· 使用定理 `CategoryTheory.Functor.instIsClosedUnderIsomorphismsHomologicalKernel`：∀
 {C : Type u_1} {A : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C] [in
st_1 : CategoryTheory.HasShift C ℤ]   [inst_2 : CategoryThe…
· 使用引理 `CategoryTheory.Functor.comp_homologySequenceδ`：comp_homologySequenceδ : 
(F.shift n₀).map T.mor₂ ≫ F.homologySequenceδ T n₀ n₁ h = 0
· 使用定理 `CategoryTheory.ShortComplex.Exact.isZero_X₂_iff`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C] 
  {S : CategoryTheory.ShortComplex C}…
· 使用引理 `CategoryTheory.Functor.homologySequence_exact₃`：homologySequence_exact₃ 
: (ShortComplex.mk _ _ (F.comp_homologySequenceδ T hT _ _ h)).Exact
· 使用引理 `CategoryTheory.Functor.homologySequence_mono_shift_map_mor₁_iff`：homolog
ySequence_mono_shift_map_mor₁_iff : Mono ((F.shift n₁).map T.mor₁) ↔ F.homologyS
equenceδ T n₀ n₁ h = 0
· 使用引理 `CategoryTheory.Functor.homologySequence_epi_shift_map_mor₁_iff`：homology
Sequence_epi_shift_map_mor₁_iff : Epi ((F.shift n₀).map T.mor₁) ↔ (F.shift n₀).m
ap T.mor₂ = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `CategoryTheory.isIso_of_mono_of_epi`：isIso_of_mono_of_epi [Balanced C] {
X Y : C} (f : X ⟶ Y) [Mono f] [Epi f] : IsIso f
· 使用定理 `CategoryTheory.balanced_of_strongMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.StrongMonoCategory C],   Categor
yTheory.Balanced C
· 使用定理 `CategoryTheory.strongMonoCategory_of_regularMonoCategory`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularMonoCateg
ory C],   CategoryTheory.StrongMonoCategory C
· 使用定理 `CategoryTheory.regularMonoCategoryOfNormalMonoCategory`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZ
eroMorphisms C]   [CategoryTheory.IsNormalMo…
· 使用定理 `CategoryTheory.Abelian.toIsNormalMonoCategory`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryThe
ory.IsNormalMonoCategory C
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
-/
lemma mem_homologicalKernel_trW_iff {X Y : C} (f : X ⟶ Y) :
    F.homologicalKernel.trW f ↔ ∀ (n : ℤ), IsIso ((F.shift n).map f) := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  apply (F.homologicalKernel.trW_iff_of_distinguished _ hT).trans
  have h₁ := fun n => (F.homologySequence_exact₃ _ hT n _ rfl).isZero_X₂_iff
  have h₂ := fun n => F.homologySequence_mono_shift_map_mor₁_iff _ hT n _ rfl
  have h₃ := fun n => F.homologySequence_epi_shift_map_mor₁_iff _ hT n
  dsimp at h₁ h₂ h₃ ⊢
  simp only [mem_homologicalKernel_iff, h₁, ← h₂, ← h₃]
  constructor
  · intro h n
    obtain ⟨m, rfl⟩ : ∃ (m : ℤ), n = m + 1 := ⟨n - 1, by simp⟩
    have := (h (m + 1)).1
    have := (h m).2
    apply isIso_of_mono_of_epi
  · intros
    constructor <;> infer_instance

open ComposableArrows

/-- The exact sequence with six terms starting from `(F.shift n₀).obj T.obj₁` until
`(F.shift n₁).obj T.obj₃` when `T` is a distinguished triangle and `F` a homological functor. -/
/-
**CategoryTheory.Functor.homologySequenceComposableArrows** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The exact sequence with six terms starting from `(F.shift n₀).obj T.obj₁` until
`(F.shift n₁).obj T.obj₃` when `T` is a distinguished triangle and `F` a homolog
ical functor.
-/
@[simp] noncomputable def homologySequenceComposableArrows₅ : ComposableArrows A 5 :=
  mk₅ ((F.shift n₀).map T.mor₁) ((F.shift n₀).map T.mor₂)
    (F.homologySequenceδ T n₀ n₁ h) ((F.shift n₁).map T.mor₁) ((F.shift n₁).map T.mor₂)

include hT in
/-
**CategoryTheory.Functor.homologySequenceComposableArrows** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homologySequenceComposableArrows₅_exact :
    (F.homologySequenceComposableArrows₅ T n₀ n₁ h).Exact :=
  exact_of_δ₀ (F.homologySequence_exact₂ T hT n₀).exact_toComposableArrows
    (exact_of_δ₀ (F.homologySequence_exact₃ T hT n₀ n₁ h).exact_toComposableArrows
      (exact_of_δ₀ (F.homologySequence_exact₁ T hT n₀ n₁ h).exact_toComposableArrows
        (F.homologySequence_exact₂ T hT n₁).exact_toComposableArrows))

end

end Functor

end CategoryTheory

