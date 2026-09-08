/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT

/-!
# Induced t-structures

Let `t` be a t-structure on a pretriangulated category `C`.
If `P` is a triangulated subcategory of `C`, we introduce a typeclass
`P.HasInducedTStructure t` which essentially says that up to isomorphisms
`P` is stable by the application of the truncation functors.

In particular, we show that the triangulated subcategory `t.plus`
of `t`-bounded above objects can be endowed with a t-structure `t.onPlus`,
and the same applies to `t.minus` and `t.bounded`.

-/

@[expose] public section

namespace CategoryTheory

open Limits Pretriangulated Triangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  (P : ObjectProperty C) (t : TStructure C)

namespace ObjectProperty

/-- The property that a full subcategory of a pretriangulated category
equipped with a t-structure can be endowed with an induced t-structure. -/
@[mk_iff]
/-
**CategoryTheory.ObjectProperty.HasInducedTStructure** 是 Mathlib 中的一个归纳类型，位于命名空间
 `CategoryTheory.ObjectProperty`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Preadditive C] →       [inst_2 : CategoryTheory.Limits.Has
ZeroObject C] →         [inst_3 : CategoryTheory.HasShift C ℤ] →           [inst
_4 : ∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive] →             [inst_
5 : CategoryTheory.Pretriangulated C] →               (P : CategoryTheory.Object
Property C) →                 CategoryTheory.Triangulated.TStructure C → [P.IsTr
iangulated] → Prop
参数：n : ℤ；CategoryTheory.shiftFunctor C n；P : CategoryTheory.ObjectProperty C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property that a full subcategory of a pretriangulated category
equipped with a t-structure can be endowed with an induced t-structure.
-/
class HasInducedTStructure [P.IsTriangulated] : Prop where
  exists_triangle_zero_one (A : C) (hA : P A) :
    ∃ (X Y : C) (_ : t.IsLE X 0) (_ : t.IsGE Y 1)
      (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧) (_ : Triangle.mk f g h ∈ distTriang C),
    P.isoClosure X ∧ P.isoClosure Y

variable [P.IsTriangulated] [h : P.HasInducedTStructure t]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The t-structure induced on a full subcategory. -/
/-
**CategoryTheory.ObjectProperty.tStructure** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.ObjectProperty`。
形式化陈述：tStructure : TStructure P.FullSubcategory where le n X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsTriangulated.toIsStableUnderShift`：∀ {C 
: Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheo
ry.Limits.HasZeroObject C}   {inst_2 : CategoryTheory.H…

--- 原说明 ---
The t-structure induced on a full subcategory.
-/
noncomputable def tStructure : TStructure P.FullSubcategory where
  le n X := t.le n X.obj
  ge n X := t.ge n X.obj
  le_isClosedUnderIsomorphisms n := ⟨fun {X Y} e hX ↦ (t.le n).prop_of_iso (P.ι.mapIso e) hX⟩
  ge_isClosedUnderIsomorphisms n := ⟨fun {X Y} e hX ↦ (t.ge n).prop_of_iso (P.ι.mapIso e) hX⟩
  le_shift n a n' h X hX := (t.le n').prop_of_iso ((P.ι.commShiftIso a).symm.app X)
      (t.le_shift n a n' h X.obj hX)
  ge_shift n a n' h X hX := (t.ge n').prop_of_iso ((P.ι.commShiftIso a).symm.app X)
    (t.ge_shift n a n' h X.obj hX)
  zero' {X Y} f hX hY := P.ι.map_injective (by
    rw [Functor.map_zero]
    exact t.zero' (P.ι.map f) hX hY)
  le_zero_le X hX := t.le_zero_le _ hX
  ge_one_le X hX := t.ge_one_le _ hX
  exists_triangle_zero_one A := by
    obtain ⟨X, Y, hX, hY, f, g, h, hT, ⟨X', hX', ⟨e⟩⟩, ⟨Y', hY', ⟨e'⟩⟩⟩ :=
      h.exists_triangle_zero_one A.1 A.2
    exact ⟨⟨X', hX'⟩, ⟨Y', hY'⟩, (t.le 0).prop_of_iso e hX.le,
      (t.ge 1).prop_of_iso e' hY.ge,
      P.fullyFaithfulι.preimage (e.inv ≫ f),
      P.fullyFaithfulι.preimage (g ≫ e'.hom),
      P.fullyFaithfulι.preimage (e'.inv ≫ h ≫ e.hom⟦(1 : ℤ)⟧' ≫
          (P.ι.commShiftIso (1 : ℤ)).inv.app ⟨X', hX'⟩),
      isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ e.symm (Iso.refl _) e'.symm)⟩
/-
**CategoryTheory.ObjectProperty.tStructure_isLE_iff** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.ObjectProperty`。
形式化陈述：tStructure_isLE_iff (X : P.FullSubcategory) (n : Int) : (P.tStructure t).I
sLE X n ↔ t.IsLE X.obj n
参数：X : P.FullSubcategory；n : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.instHasZeroObjectFullSubcategoryOfContains
Zero`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheo
ry.ObjectProperty C) [P.ContainsZero],   CategoryTheory.Limits.Has…
· 使用定理 `CategoryTheory.ObjectProperty.IsTriangulated.toContainsZero`：∀ {C : Type
 u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Lim
its.HasZeroObject C}   {inst_2 : CategoryTheory.H…
· 使用定理 `CategoryTheory.ObjectProperty.IsTriangulated.toIsStableUnderShift`：∀ {C 
: Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheo
ry.Limits.HasZeroObject C}   {inst_2 : CategoryTheory.H…
· 使用定理 `CategoryTheory.ObjectProperty.instAdditiveFullSubcategoryShiftFunctor`：∀
 {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (P : CategoryTheor
y.ObjectProperty C) {A : Type u_2}   [inst_1 : AddMonoid A]…
· 使用定理 `CategoryTheory.Triangulated.TStructure.IsLE.le`：∀ {C : Type u_1} {inst :
 CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Preadditive C}  
 {inst_2 : CategoryTheory.Limits.Has…
-/
lemma tStructure_isLE_iff (X : P.FullSubcategory) (n : ℤ) :
    (P.tStructure t).IsLE X n ↔ t.IsLE X.obj n :=
  ⟨fun h => ⟨h.1⟩, fun h => ⟨h.1⟩⟩
/-
**CategoryTheory.ObjectProperty.tStructure_isGE_iff** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.ObjectProperty`。
形式化陈述：tStructure_isGE_iff (X : P.FullSubcategory) (n : Int) : (P.tStructure t).I
sGE X n ↔ t.IsGE X.obj n
参数：X : P.FullSubcategory；n : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.instHasZeroObjectFullSubcategoryOfContains
Zero`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheo
ry.ObjectProperty C) [P.ContainsZero],   CategoryTheory.Limits.Has…
· 使用定理 `CategoryTheory.ObjectProperty.IsTriangulated.toContainsZero`：∀ {C : Type
 u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Lim
its.HasZeroObject C}   {inst_2 : CategoryTheory.H…
· 使用定理 `CategoryTheory.ObjectProperty.IsTriangulated.toIsStableUnderShift`：∀ {C 
: Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheo
ry.Limits.HasZeroObject C}   {inst_2 : CategoryTheory.H…
· 使用定理 `CategoryTheory.ObjectProperty.instAdditiveFullSubcategoryShiftFunctor`：∀
 {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (P : CategoryTheor
y.ObjectProperty C) {A : Type u_2}   [inst_1 : AddMonoid A]…
· 使用定理 `CategoryTheory.Triangulated.TStructure.IsGE.ge`：∀ {C : Type u_1} {inst :
 CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Preadditive C}  
 {inst_2 : CategoryTheory.Limits.Has…
-/
lemma tStructure_isGE_iff (X : P.FullSubcategory) (n : ℤ) :
    (P.tStructure t).IsGE X n ↔ t.IsGE X.obj n :=
  ⟨fun h => ⟨h.1⟩, fun h => ⟨h.1⟩⟩

/-- Constructor for `HasInducedTStructure`. -/
/-
**CategoryTheory.ObjectProperty.HasInducedTStructure.mk'** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.ObjectProperty.HasInducedTStructure`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   [inst_2 : CategoryTheory.Limits.HasZeroObject C] 
[inst_3 : CategoryTheory.HasShift C ℤ]   [inst_4 : ∀ (n : ℤ), (CategoryTheory.sh
iftFunctor C n).Additive] [inst_5 : CategoryTheory.Pretriangulated C]   {P : Cat
egoryTheory.ObjectProperty C} [inst_6 : P.IsTriangulated] {t : CategoryTheory.Tr
iangulated.TStructure C},   (∀ (X : C), P X → ∀ (n : ℤ), P ((t.truncLE n).obj X)
 ∧ P ((t.truncGE n).obj X)) → P.HasInducedTStructure t
参数：n : ℤ；CategoryTheory.shiftFunctor C n；∀ (X : C), P X → ∀ (n : ℤ), P ((t.trunc
LE n).obj X) ∧ P ((t.truncGE n).obj X)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Triangulated.TStructure.instIsLEObjTruncLE`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Pread
ditive C]   [inst_2 : CategoryTheory.Limits.Has…
· 使用定理 `CategoryTheory.Triangulated.TStructure.instIsGEObjTruncGE`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive
 C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用引理 `CategoryTheory.Triangulated.TStructure.triangleLEGE_distinguished`：trian
gleLEGE_distinguished (a b : Int) (h : a + 1 = b) (X : C) : (t.triangleLEGE a b 
h).obj X in distTriang C
· 使用引理 `CategoryTheory.ObjectProperty.le_isoClosure`：le_isoClosure : P <= isoClo
sure P
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Constructor for `HasInducedTStructure`.
-/
lemma HasInducedTStructure.mk' {P : ObjectProperty C} [P.IsTriangulated] {t : TStructure C}
    (h : ∀ (X : C) (_ : P X) (n : ℤ), P ((t.truncLE n).obj X) ∧ P ((t.truncGE n).obj X)) :
    P.HasInducedTStructure t where
  exists_triangle_zero_one X hX :=
    ⟨_, _, inferInstance, inferInstance, _, _, _,
      t.triangleLEGE_distinguished 0 1 (by lia) X,
        P.le_isoClosure _ ((h X hX _).1), P.le_isoClosure _ ((h X hX _).2)⟩

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ObjectProperty.mem_of_hasInductedTStructure** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：mem_of_hasInductedTStructure (P : ObjectProperty C) [P.IsTriangulated] (t 
: TStructure C) [P.IsClosedUnderIsomorphisms] [P.HasInducedTStructure t] (T : Tr
iangle C) (hT : T in distTriang C) (n₀ n₁ : Int) (h : n₀ + 1 = n₁) (h₁ : t.IsLE 
T.obj₁ n₀) (h₂ : P T.obj₂) (h₃ : t.IsGE T.obj₃ n₁) : P T.obj₁ ∧ P T.obj₃
参数：P : ObjectProperty C；t : TStructure C；T : Triangle C；hT : T in distTriang C；n
₀ n₁ : Int；h : n₀ + 1 = n₁；h₁ : t.IsLE T.obj₁ n₀；h₂ : P T.obj₂；h₃ : t.IsGE T.obj
₃ n₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsTriangulated.toIsStableUnderShift`：∀ {C 
: Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheo
ry.Limits.HasZeroObject C}   {inst_2 : CategoryTheory.H…
· 使用定理 `CategoryTheory.ObjectProperty.instHasZeroObjectFullSubcategoryOfContains
Zero`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheo
ry.ObjectProperty C) [P.ContainsZero],   CategoryTheory.Limits.Has…
· 使用定理 `CategoryTheory.ObjectProperty.IsTriangulated.toContainsZero`：∀ {C : Type
 u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Lim
its.HasZeroObject C}   {inst_2 : CategoryTheory.H…
· 使用定理 `CategoryTheory.ObjectProperty.instAdditiveFullSubcategoryShiftFunctor`：∀
 {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (P : CategoryTheor
y.ObjectProperty C) {A : Type u_2}   [inst_1 : AddMonoid A]…
· 使用定理 `CategoryTheory.Triangulated.TStructure.triangle_iso_exists`：∀ {C : Type 
u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditiv
e C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用引理 `CategoryTheory.Functor.map_distinguished`：map_distinguished [F.IsTriangu
lated] (T : Triangle C) (hT : T in distTriang C) : F.mapTriangle.obj T in distTr
iang D
· 使用定理 `CategoryTheory.ObjectProperty.instIsTriangulatedFullSubcategoryι`：∀ {C :
 Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheor
y.Limits.HasZeroObject C]   [inst_2 : CategoryTheory.H…
· 使用引理 `CategoryTheory.Triangulated.TStructure.triangleLEGE_distinguished`：trian
gleLEGE_distinguished (a b : Int) (h : a + 1 = b) (X : C) : (t.triangleLEGE a b 
h).obj X in distTriang C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ObjectProperty.tStructure_isLE_iff`：tStructure_isLE_iff (
X : P.FullSubcategory) (n : Int) : (P.tStructure t).IsLE X n ↔ t.IsLE X.obj n
· 使用定理 `CategoryTheory.Triangulated.TStructure.instIsLEObjTruncLE`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Pread
ditive C]   [inst_2 : CategoryTheory.Limits.Has…
· 使用引理 `CategoryTheory.ObjectProperty.tStructure_isGE_iff`：tStructure_isGE_iff (
X : P.FullSubcategory) (n : Int) : (P.tStructure t).IsGE X n ↔ t.IsGE X.obj n
· 使用定理 `CategoryTheory.Triangulated.TStructure.instIsGEObjTruncGE`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive
 C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.ObjectProperty.prop_iff_of_iso`：prop_iff_of_iso [IsClosed
UnderIsomorphisms P] {X Y : C} (e : X ≅ Y) : P X ↔ P Y
· 使用引理 `CategoryTheory.ObjectProperty.prop_ι_obj`：prop_ι_obj (X) : P (P.ι.obj X)
-/
lemma mem_of_hasInductedTStructure (P : ObjectProperty C) [P.IsTriangulated] (t : TStructure C)
    [P.IsClosedUnderIsomorphisms] [P.HasInducedTStructure t]
    (T : Triangle C) (hT : T ∈ distTriang C)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (h₁ : t.IsLE T.obj₁ n₀) (h₂ : P T.obj₂)
    (h₃ : t.IsGE T.obj₃ n₁) :
    P T.obj₁ ∧ P T.obj₃ := by
  obtain ⟨e, _⟩ := t.triangle_iso_exists hT
    (P.ι.map_distinguished _ ((P.tStructure t).triangleLEGE_distinguished n₀ n₁ h ⟨_, h₂⟩))
    (Iso.refl _) n₀ n₁ inferInstance inferInstance
      (by dsimp; rw [← P.tStructure_isLE_iff]; infer_instance)
      (by dsimp; rw [← P.tStructure_isGE_iff]; infer_instance)
  exact ⟨(P.prop_iff_of_iso (Triangle.π₁.mapIso e)).2 (P.prop_ι_obj _),
    (P.prop_iff_of_iso (Triangle.π₃.mapIso e)).2 (P.prop_ι_obj _)⟩

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P P' : ObjectProperty C) [P.IsTriangulated] [P'.IsTriangulated] (t : TStructure C)
    [P.HasInducedTStructure t] [P'.HasInducedTStructure t]
    [P.IsClosedUnderIsomorphisms] [P'.IsClosedUnderIsomorphisms] :
    (P ⊓ P').HasInducedTStructure t :=
  .mk' (by
    rintro X ⟨hX, hX'⟩ n
    exact
      ⟨⟨(P.mem_of_hasInductedTStructure t _ (t.triangleLEGE_distinguished n _ rfl X) n _ rfl
          (by dsimp; infer_instance) hX (by dsimp; infer_instance)).1,
        (P'.mem_of_hasInductedTStructure t _ (t.triangleLEGE_distinguished n _ rfl X) n _ rfl
          (by dsimp; infer_instance) hX' (by dsimp; infer_instance)).1⟩,
          ⟨(P.mem_of_hasInductedTStructure t _ (t.triangleLEGE_distinguished (n - 1) n (by lia) X)
          (n - 1) n (by lia) (by dsimp; infer_instance) hX (by dsimp; infer_instance)).2,
        (P'.mem_of_hasInductedTStructure t _ (t.triangleLEGE_distinguished (n - 1) n (by lia) X)
          (n - 1) n (by lia) (by dsimp; infer_instance) hX' (by dsimp; infer_instance)).2⟩⟩)

end ObjectProperty

namespace Triangulated.TStructure

variable [IsTriangulated C]

/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : t.plus.HasInducedTStructure t :=
  .mk' (by rintro X ⟨a, _⟩ n; exact ⟨⟨a, inferInstance⟩, ⟨a, inferInstance⟩⟩)
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : t.minus.HasInducedTStructure t :=
  .mk' (by rintro X ⟨a, _⟩ n; exact ⟨⟨a, inferInstance⟩, ⟨a, inferInstance⟩⟩)
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : t.bounded.HasInducedTStructure t := by
  dsimp [bounded]
  infer_instance

/-- The t-structure induced on the full subcategory of `t`-bounded above objects. -/
/-
**CategoryTheory.Triangulated.TStructure.onPlus** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cat
egoryTheory.Triangulated.TStructure`。
形式化陈述：onPlus : TStructure t.plus.FullSubcategory
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Triangulated.TStructure.instIsTriangulatedPlus`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preaddi
tive C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用定理 `CategoryTheory.Triangulated.TStructure.instHasInducedTStructurePlus`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTh
eory.Preadditive C]   [inst_2 : CategoryTheory.Limits.Has…

--- 原说明 ---
The t-structure induced on the full subcategory of `t`-bounded above objects.
-/
noncomputable abbrev onPlus : TStructure t.plus.FullSubcategory := t.plus.tStructure t

/-- The t-structure induced on the full subcategory of `t`-bounded below objects. -/
/-
**CategoryTheory.Triangulated.TStructure.onMinus** 是 Mathlib 中的一个缩写定义，位于命名空间 `Ca
tegoryTheory.Triangulated.TStructure`。
形式化陈述：onMinus : TStructure t.minus.FullSubcategory
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Triangulated.TStructure.instIsTriangulatedMinus`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadd
itive C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用定理 `CategoryTheory.Triangulated.TStructure.instHasInducedTStructureMinus`：∀ 
{C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryT
heory.Preadditive C]   [inst_2 : CategoryTheory.Limits.Has…

--- 原说明 ---
The t-structure induced on the full subcategory of `t`-bounded below objects.
-/
noncomputable abbrev onMinus : TStructure t.minus.FullSubcategory := t.minus.tStructure t

/-- The t-structure induced on the full subcategory of `t`-bounded objects. -/
/-
**CategoryTheory.Triangulated.TStructure.onBounded** 是 Mathlib 中的一个缩写定义，位于命名空间 `
CategoryTheory.Triangulated.TStructure`。
形式化陈述：onBounded : TStructure t.bounded.FullSubcategory
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Triangulated.TStructure.instIsTriangulatedBounded`：∀ {C :
 Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Prea
dditive C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用定理 `CategoryTheory.Triangulated.TStructure.instHasInducedTStructureBounded`：
∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Categor
yTheory.Preadditive C]   [inst_2 : CategoryTheory.Limits.Has…

--- 原说明 ---
The t-structure induced on the full subcategory of `t`-bounded objects.
-/
noncomputable abbrev onBounded : TStructure t.bounded.FullSubcategory := t.bounded.tStructure t

end Triangulated.TStructure

end CategoryTheory

