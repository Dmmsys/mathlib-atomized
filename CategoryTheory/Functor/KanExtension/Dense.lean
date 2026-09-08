/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.DenseAt
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Generator.StrongGenerator

/-!
# Dense functors

A functor `F : C ⥤ D` is dense (`F.IsDense`) if `𝟭 D` is a pointwise
left Kan extension of `F` along itself, i.e. any `Y : D` is the
colimit of all `F.obj X` for all morphisms `F.obj X ⟶ Y` (which
is the condition `F.DenseAt Y`).
When `F` is full, we show that this
is equivalent to saying that the restricted Yoneda functor
`D ⥤ Cᵒᵖ ⥤ Type _` is fully faithful (see the lemma
`Functor.isDense_iff_fullyFaithful_restrictedULiftYoneda`).

We also show that the range of a dense functor is a strong
generator (see `Functor.isStrongGenerator_of_isDense`).

## References

* https://ncatlab.org/nlab/show/dense+subcategory

-/

@[expose] public section

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits Opposite Presheaf ConcreteCategory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {C' : Type u₃} [Category.{v₃} C']

namespace Functor

/-- A functor `F : C ⥤ D` is dense if any `Y : D` is a canonical colimit
relatively to `F`. -/
/-
**CategoryTheory.Functor.IsDense** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.Fun
ctor`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} C] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.F
unctor C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F : C ⥤ D` is dense if any `Y : D` is a canonical colimit
relatively to `F`.
-/
class IsDense (F : C ⥤ D) : Prop where
  isDenseAt (F) (Y : D) : F.isDenseAt Y

/-- This is a choice of structure `F.DenseAt Y` when `F : C ⥤ D`
is dense, and `Y : D`. -/
/-
**CategoryTheory.Functor.denseAt** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Funct
or`。
形式化陈述：denseAt (F : C ⥤ D) [F.IsDense] (Y : D) : F.DenseAt Y
参数：F : C ⥤ D；Y : D。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsDense.isDenseAt`：∀ {C : Type u₁} {D : Type u₂} 
{inst : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category.{v
₂, u₂} D}   (F : CategoryTheor…

--- 原说明 ---
This is a choice of structure `F.DenseAt Y` when `F : C ⥤ D`
is dense, and `Y : D`.
-/
noncomputable def denseAt (F : C ⥤ D) [F.IsDense] (Y : D) : F.DenseAt Y :=
  (IsDense.isDenseAt F Y).some
/-
**CategoryTheory.Functor.isDense_iff_nonempty_isPointwiseLeftKanExtension** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isDense_iff_nonempty_isPointwiseLeftKanExtension (F : C ⥤ D) : F.IsDense ↔
 Nonempty ((LeftExtension.mk _ (rightUnitor F).inv).IsPointwiseLeftKanExtension)
参数：F : C ⥤ D。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isDense_iff_nonempty_isPointwiseLeftKanExtension (F : C ⥤ D) :
    F.IsDense ↔
      Nonempty ((LeftExtension.mk _ (rightUnitor F).inv).IsPointwiseLeftKanExtension) :=
  ⟨fun _ ↦ ⟨fun _ ↦ F.denseAt _⟩, fun ⟨h⟩ ↦ ⟨fun _ ↦ ⟨h _⟩⟩⟩
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) [F.IsDense] : Functor.IsLeftKanExtension (𝟭 D) (Functor.rightUnitor F).inv :=
  ((Functor.isDense_iff_nonempty_isPointwiseLeftKanExtension F).mp ‹_›).some.isLeftKanExtension
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) [F.IsDense] : F.HasPointwiseLeftKanExtension F :=
  fun X ↦ (Functor.IsDense.isDenseAt F X).some.hasPointwiseLeftKanExtensionAt
/-
**CategoryTheory.Functor.IsDense.of_iso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Functor.IsDense`。
形式化陈述：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F G : CategoryTheory.Functor C 
D} (e : F ≅ G) [F.IsDense], G.IsDense
参数：e : F ≅ G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.congr_isDenseAt`：congr_isDenseAt {G : C ⥤ D} (e :
 F ≅ G) : F.isDenseAt = G.isDenseAt
-/
lemma IsDense.of_iso {F G : C ⥤ D} (e : F ≅ G) [F.IsDense] :
    G.IsDense where
  isDenseAt Y := by
    rw [← Functor.congr_isDenseAt e]
    exact ⟨F.denseAt Y⟩
/-
**CategoryTheory.Functor.IsDense.iff_of_iso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Functor.IsDense`。
形式化陈述：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F G : CategoryTheory.Functor C 
D} (e : F ≅ G), F.IsDense ↔ G.IsDense
参数：e : F ≅ G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsDense.of_iso`：∀ {C : Type u₁} {D : Type u₂} [in
st : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   {F G : CategoryThe…
-/
lemma IsDense.iff_of_iso {F G : C ⥤ D} (e : F ≅ G) :
    F.IsDense ↔ G.IsDense :=
  ⟨fun _ ↦ of_iso e, fun _ ↦ of_iso e.symm⟩

variable (F : C ⥤ D)
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (G : C' ⥤ C) [F.IsDense] [G.IsEquivalence] :
    (G ⋙ F).IsDense where
  isDenseAt Y := ⟨(F.denseAt Y).precompOfFinal G⟩
/-
**CategoryTheory.Functor.IsDense.comp_left_iff_of_isEquivalence** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.Functor.IsDense`。
形式化陈述：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {C' : Type u₃} [inst_2 : Categor
yTheory.Category.{v₃, u₃} C'] (F : CategoryTheory.Functor C D)   (G : CategoryTh
eory.Functor C' C) [G.IsEquivalence], (G.comp F).IsDense ↔ F.IsDense
参数：F : CategoryTheory.Functor C D；G : CategoryTheory.Functor C' C；G.comp F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsDense.of_iso`：∀ {C : Type u₁} {D : Type u₂} [in
st : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.instIsDenseCompOfIsEquivalence`：∀ {C : Type u₁} {
D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {C' : Type u₃} [in…
-/
lemma IsDense.comp_left_iff_of_isEquivalence (G : C' ⥤ C) [G.IsEquivalence] :
    (G ⋙ F).IsDense ↔ F.IsDense := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ inferInstance⟩
  let e : G.inv ⋙ G ⋙ F ≅ F := (associator _ _ _).symm ≪≫
    isoWhiskerRight (G.asEquivalence.counitIso) _ ≪≫ F.leftUnitor
  exact of_iso e
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (G : D ⥤ C') [F.IsDense] [G.IsEquivalence] :
    (F ⋙ G).IsDense where
  isDenseAt Y :=
    ⟨ letI e : Y ≅ G.obj (G.inv.obj Y) := G.asEquivalence.counitIso.symm.app Y
      DenseAt.ofIso (F.denseAt (G.inv.obj Y) |>.postcompEquivalence G) e.symm ⟩
/-
**CategoryTheory.Functor.IsDense.comp_right_iff_of_isEquivalence** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Functor.IsDense`。
形式化陈述：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {C' : Type u₃} [inst_2 : Categor
yTheory.Category.{v₃, u₃} C'] (F : CategoryTheory.Functor C D)   (G : CategoryTh
eory.Functor D C') [G.IsEquivalence], (F.comp G).IsDense ↔ F.IsDense
参数：F : CategoryTheory.Functor C D；G : CategoryTheory.Functor D C'；F.comp G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsDense.of_iso`：∀ {C : Type u₁} {D : Type u₂} [in
st : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.instIsDenseCompOfIsEquivalence_1`：∀ {C : Type u₁}
 {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryThe
ory.Category.{v₂, u₂} D]   {C' : Type u₃} [in…
-/
lemma IsDense.comp_right_iff_of_isEquivalence (G : D ⥤ C') [G.IsEquivalence] :
    (F ⋙ G).IsDense ↔ F.IsDense := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ inferInstance⟩
  let e : (F ⋙ G) ⋙ G.inv ≅ F := associator .. ≪≫
    isoWhiskerLeft _ G.asEquivalence.unitIso.symm ≪≫ F.rightUnitor
  exact of_iso e

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.IsDense] : (restrictedULiftYoneda.{w} F).Faithful where
  map_injective h :=
    (F.denseAt _).hom_ext' (fun X p ↦ by
      simpa using! ULift.up_injective (ConcreteCategory.congr_hom (CC := fun X ↦ X)
        (NatTrans.congr_app h (op X)) (ULift.up p)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.IsDense] : (restrictedULiftYoneda.{w} F).Full where
  map_surjective {Y Z} f := by
    let c : Cocone (CostructuredArrow.proj F Y ⋙ F) :=
      { pt := Z
        ι :=
          { app g := ((f.app (op g.left)) (ULift.up g.hom)).down
            naturality g₁ g₂ φ := by
              simpa [uliftFunctor, uliftYoneda,
                restrictedULiftYoneda, ← ULift.down_inj] using
                ((f.naturality_apply φ.left.op) (ULift.up g₂.hom)).symm } }
    refine ⟨(F.denseAt Y).desc c, ?_⟩
    ext ⟨X⟩ ⟨x⟩
    have := (F.denseAt Y).fac c (.mk x)
    dsimp [c] at this
    simpa using ULift.down_injective this

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {F} in
/-
**CategoryTheory.Functor.IsDense.of_fullyFaithful_restrictedULiftYoneda** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.Functor.IsDense`。
形式化陈述：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheory.Functor C D}
 [F.Full] (h : (CategoryTheory.Presheaf.restrictedULiftYoneda F).FullyFaithful),
   F.IsDense
参数：h : (CategoryTheory.Presheaf.restrictedULiftYoneda F).FullyFaithful。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ULift.down_injective`：∀ {α : Type u_1}, Function.Injective ULift.down
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.Cocone.w`：∀ {J : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} C] 
  {F : CategoryTheor…
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Functor.FullyFaithful.map_injective`：map_injective {X Y :
 C} {f g : X ⟶ Y} (h : F.map f = F.map g) : f = g
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.FullyFaithful.map_preimage`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.NatTrans.mk.congr_simp`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   {F G : CategoryThe…
-/
lemma IsDense.of_fullyFaithful_restrictedULiftYoneda [F.Full]
    (h : (restrictedULiftYoneda.{w} F).FullyFaithful) :
    F.IsDense where
  isDenseAt Y := by
    let φ (s : Cocone (CostructuredArrow.proj F Y ⋙ F)) :
        (restrictedULiftYoneda.{w} F).obj Y ⟶ (restrictedULiftYoneda F).obj s.pt :=
      { app := fun ⟨X⟩ ↦ ↾fun ⟨x⟩ ↦ ULift.up (s.ι.app (.mk x))
        naturality := by
          rintro ⟨X₁⟩ ⟨X₂⟩ ⟨f⟩
          ext ⟨x⟩
          let α : CostructuredArrow.mk (F.map f ≫ x) ⟶ CostructuredArrow.mk x :=
            CostructuredArrow.homMk f
          exact ULift.down_injective (s.w α).symm }
    have hφ (s) (j) : (restrictedULiftYoneda F).map j.hom ≫ φ s =
        (restrictedULiftYoneda F).map (s.ι.app j) := by
      ext ⟨X⟩ ⟨x⟩
      let α : .mk (x ≫ j.hom) ⟶ j := CostructuredArrow.homMk (F.preimage x)
      have := s.w α
      dsimp [uliftYoneda, φ, α] at this ⊢
      apply ULift.down_injective
      simpa using this.symm
    exact
      ⟨{desc s := (h.preimage (φ s))
        fac s j := h.map_injective (by simp [hφ])
        uniq s m hm := h.map_injective (by
          ext ⟨_⟩ ⟨_⟩
          simp [φ, ← hm]) }⟩
/-
**CategoryTheory.Functor.isDense_iff_fullyFaithful_restrictedULiftYoneda** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：isDense_iff_fullyFaithful_restrictedULiftYoneda [F.Full] : F.IsDense ↔ Non
empty (restrictedULiftYoneda.{w} F).FullyFaithful
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instFullOppositeTypeRestrictedULiftYonedaOfIsDens
e`：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [in
st_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instFaithfulOppositeTypeRestrictedULiftYonedaOfIs
Dense`：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C]
 [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsDense.of_fullyFaithful_restrictedULiftYoneda`：∀
 {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1
 : CategoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheor…
-/
lemma isDense_iff_fullyFaithful_restrictedULiftYoneda [F.Full] :
    F.IsDense ↔ Nonempty (restrictedULiftYoneda.{w} F).FullyFaithful :=
  ⟨fun _ ↦ ⟨FullyFaithful.ofFullyFaithful _⟩,
    fun ⟨h⟩ ↦ IsDense.of_fullyFaithful_restrictedULiftYoneda h⟩

open ObjectProperty in
/-
**CategoryTheory.Functor.isStrongGenerator_of_isDense** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Functor`。
形式化陈述：isStrongGenerator_of_isDense [F.IsDense] : IsStrongGenerator (.ofObj F.obj
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsStrongGenerator.mk_of_exists_colimitsOfS
hape`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheo
ry.ObjectProperty C},   (∀ (X : C), ∃ J x, P.colimitsOfShape J X) …
· 使用定理 `CategoryTheory.CostructuredArrow.instSmallOfLocallySmall`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   {S : CategoryTheor…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
· 使用定理 `CategoryTheory.Shrink.instLocallySmallShrink`：∀ (C : Type u) [inst : Cat
egoryTheory.Category.{v, u} C] [inst_1 : Small.{w', u} C]   [CategoryTheory.Loca
llySmall.{w, v, u} C], CategoryThe…
· 使用定理 `CategoryTheory.locallySmall_of_essentiallySmall`：∀ (C : Type u) [inst : 
CategoryTheory.Category.{v, u} C] [CategoryTheory.EssentiallySmall.{w, v, u} C],
   CategoryTheory.LocallySmall.{w, v,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Equivalence.trans_functor`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.ShrinkHoms.equivalence_inverse`：∀ (C : Type u) [inst : Ca
tegoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.LocallySmall.{w, v, u} 
C],   (CategoryTheory.ShrinkHoms.eq…
· 使用定理 `CategoryTheory.ShrinkHoms.inverse_obj`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [inst_1 : CategoryTheory.LocallySmall.{w, v, u} C]   (X 
: CategoryTheory.ShrinkHoms…
· 使用定理 `CategoryTheory.CostructuredArrow.proj_obj`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   (S : CategoryTheor…
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma isStrongGenerator_of_isDense [F.IsDense] :
    IsStrongGenerator (.ofObj F.obj) :=
  (IsStrongGenerator.mk_of_exists_colimitsOfShape.{max u₁ u₂ v₁ v₂,
      max u₁ v₁ v₂} (fun Y ↦ ⟨_, _, ⟨{
    ι := _
    diag := _
    isColimit := (IsColimit.whiskerEquivalence (F.denseAt Y)
      ((ShrinkHoms.equivalence _).symm.trans ((Shrink.equivalence _)).symm))
    prop_diag_obj := by simp }⟩⟩))

/-- If `F` is dense, the left Kan extension of `F` along `F` is isomorphic to the identity. -/
/-
**CategoryTheory.Functor.IsDense.leftKanExtensionIso** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Functor.IsDense`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} C] →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (F : Cat
egoryTheory.Functor C D) → [inst_2 : F.IsDense] → F.leftKanExtension F ≅ Categor
yTheory.Functor.id D
参数：F : CategoryTheory.Functor C D。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instIsLeftKanExtensionIdInvRightUnitorOfIsDense`：
∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_
1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…

--- 原说明 ---
If `F` is dense, the left Kan extension of `F` along `F` is isomorphic to the id
entity.
-/
noncomputable def IsDense.leftKanExtensionIso (F : C ⥤ D) [F.IsDense] :
    F.leftKanExtension F ≅ 𝟭 D :=
  Functor.leftKanExtensionUnique _ (F.leftKanExtensionUnit F) _ F.rightUnitor.inv

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.IsDense.leftKanExtensionUnit_leftKanExtensionIso_hom** 
是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Functor.IsDense`。
形式化陈述：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [inst_2 : F.IsDense],   CategoryTheory.CategoryStruct.comp (F.leftKanExtensionU
nit F)       (F.whiskerLeft (CategoryTheory.Functor.IsDense.leftKanExtensionIso 
F).hom) =     F.rightUnitor.inv
参数：F : CategoryTheory.Functor C D；F.leftKanExtensionUnit F；F.whiskerLeft (Catego
ryTheory.Functor.IsDense.leftKanExtensionIso F).hom。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Functor.instHasLeftKanExtension`：∀ {C : Type u_1} {D : Ty
pe u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.instHasPointwiseLeftKanExtensionOfIsDense`：∀ {C :
 Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.leftKanExtensionUnique_hom`：∀ {C : Type u_1} {H :
 Type u_3} {D : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_3, u_3} …
· 使用定理 `CategoryTheory.Functor.instIsLeftKanExtensionIdInvRightUnitorOfIsDense`：
∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_
1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用引理 `CategoryTheory.Functor.descOfIsLeftKanExtension_fac`：descOfIsLeftKanExte
nsion_fac (G : D ⥤ H) (β : F ⟶ L ⋙ G) : α ≫ whiskerLeft L (F'.descOfIsLeftKanExt
ension α G β) = β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsDense.leftKanExtensionUnit_leftKanExtensionIso_hom (F : C ⥤ D) [F.IsDense] :
    F.leftKanExtensionUnit F ≫ F.whiskerLeft (Functor.IsDense.leftKanExtensionIso F).hom =
      F.rightUnitor.inv := by
  simp [Functor.IsDense.leftKanExtensionIso]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.IsDense.leftKanExtensionUnit_leftKanExtensionIso_hom_ap
p** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Functor.IsDense`。
形式化陈述：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [inst_2 : F.IsDense] (X : C),   CategoryTheory.CategoryStruct.comp ((F.leftKanE
xtensionUnit F).app X)       ((CategoryTheory.Functor.IsDense.leftKanExtensionIs
o F).hom.app (F.obj X)) =     F.rightUnitor.inv.app X
参数：F : CategoryTheory.Functor C D；X : C；(F.leftKanExtensionUnit F).app X；(Catego
ryTheory.Functor.IsDense.leftKanExtensionIso F).hom.app (F.obj X)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instHasLeftKanExtension`：∀ {C : Type u_1} {D : Ty
pe u_2} {H : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.instHasPointwiseLeftKanExtensionOfIsDense`：∀ {C :
 Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.IsDense.leftKanExtensionUnit_leftKanExtensionIso_
hom`：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [
inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
-/
lemma IsDense.leftKanExtensionUnit_leftKanExtensionIso_hom_app [F.IsDense] (X : C) :
    (F.leftKanExtensionUnit F).app X ≫ (Functor.IsDense.leftKanExtensionIso F).hom.app (F.obj X) =
      F.rightUnitor.inv.app _ :=
  congr($(Functor.IsDense.leftKanExtensionUnit_leftKanExtensionIso_hom _).app _)

end Functor

/-- `yoneda` is dense: Every `X : Cᵒᵖ ⥤ Type v₁` is the colimit over
`CostructuredArrow.proj yoneda X ⋙ yoneda`. -/
/-
**CategoryTheory.denseAtYoneda** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：denseAtYoneda (X : Cᵒᵖ ⥤ Type v₁) : yoneda.DenseAt X
参数：X : Cᵒᵖ ⥤ Type v₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`yoneda` is dense: Every `X : Cᵒᵖ ⥤ Type v₁` is the colimit over
`CostructuredArrow.proj yoneda X ⋙ yoneda`.
-/
def denseAtYoneda (X : Cᵒᵖ ⥤ Type v₁) : yoneda.DenseAt X :=
  Presheaf.isColimitTautologicalCocone X
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (yoneda (C := C)).IsDense where
  isDenseAt X := ⟨denseAtYoneda X⟩

/-- `uliftYoneda` is dense: Every `X : Cᵒᵖ ⥤ Type max w v₁` is the colimit over
`CostructuredArrow.proj uliftYoneda X ⋙ uliftYoneda`. -/
/-
**CategoryTheory.denseAtUliftYoneda** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：denseAtUliftYoneda (X : Cᵒᵖ ⥤ Type max w v₁) : uliftYoneda.DenseAt X
参数：X : Cᵒᵖ ⥤ Type max w v₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`uliftYoneda` is dense: Every `X : Cᵒᵖ ⥤ Type max w v₁` is the colimit over
`CostructuredArrow.proj uliftYoneda X ⋙ uliftYoneda`.
-/
def denseAtUliftYoneda (X : Cᵒᵖ ⥤ Type max w v₁) : uliftYoneda.DenseAt X :=
  Presheaf.isColimitTautologicalCocone' X
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (uliftYoneda.{w} (C := C)).IsDense where
  isDenseAt X := ⟨denseAtUliftYoneda X⟩

end CategoryTheory

