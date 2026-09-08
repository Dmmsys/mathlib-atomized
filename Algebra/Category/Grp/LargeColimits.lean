/-
Copyright (c) 2025 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Module.CharacterModule
public import Mathlib.Algebra.Group.Equiv.Basic

/-!
# Existence of "big" colimits in the category of additive commutative groups

If `F : J ⥤ AddCommGrpCat.{w}` is a functor, we show that `F` admits a colimit if and only
if `Colimits.Quot F` (the quotient of the direct sum of the commutative groups `F.obj j`
by the relations given by the morphisms in the diagram) is `w`-small.

-/

public section

universe w u v

open CategoryTheory Limits

namespace AddCommGrpCat

variable {J : Type u} [Category.{v} J] {F : J ⥤ AddCommGrpCat.{w}} (c : Cocone F)

open Colimits

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
If `c` is a cocone of `F` such that `Quot.desc F c` is bijective, then `c` is a colimit
cocone of `F`.
-/
/-
**AddCommGrpCat.isColimit_iff_bijective_desc** 是 Mathlib 中的一个引理，位于命名空间 `AddCommG
rpCat`。
形式化陈述：isColimit_iff_bijective_desc [DecidableEq J] : Nonempty (IsColimit c) ↔ Fu
nction.Bijective (Quot.desc F c)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CharacterModule.dual_bijective_iff_bijective`：dual_bijective_iff_bijecti
ve {f : A ->ₗ[R] A'} : Function.Bijective (dual f) ↔ Function.Bijective f
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `AddCommGrpCat.ofHom_injective`：∀ {X Y : Type u} [inst : AddCommGroup X] 
[inst_1 : AddCommGroup Y], Function.Injective fun f => AddCommGrpCat.ofHom f
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `AddCommGrpCat.hom_ext`：∀ {X Y : AddCommGrpCat} {f g : X ⟶ Y}, AddCommGrp
Cat.Hom.hom f = AddCommGrpCat.Hom.hom g → f = g
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `ULift.ext`：ext (x y : ULift α) (h : x.down = y.down) : x = y
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
· 使用定理 `AddCommGrpCat.Colimits.Quot.ι_desc`：∀ {J : Type u} [inst : CategoryTheor
y.Category.{v, u} J] (F : CategoryTheory.Functor J AddCommGrpCat)   (c : Categor
yTheory.Limits.Cocone F)…
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `AddCommGrpCat.Colimits.Quot.map_ι`：∀ {J : Type u} [inst : CategoryTheory
.Category.{v, u} J] (F : CategoryTheory.Functor J AddCommGrpCat)   [inst_1 : Dec
idableEq J] {j j' : J} …
· 使用定理 `AddCommGrpCat.Colimits.Quot.addMonoidHom_ext`：∀ {J : Type u} [inst : Cat
egoryTheory.Category.{v, u} J] (F : CategoryTheory.Functor J AddCommGrpCat)   [i
nst_1 : DecidableEq J] {α : Type u…
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
· 使用定理 `AddEquiv.apply_symm_apply`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M
] [inst_1 : Add N] (e : M ≃+ N) (y : N), e (e.symm y) = y

--- 原说明 ---
If `c` is a cocone of `F` such that `Quot.desc F c` is bijective, then `c` is a 
colimit
cocone of `F`.
-/
lemma isColimit_iff_bijective_desc [DecidableEq J] :
     Nonempty (IsColimit c) ↔ Function.Bijective (Quot.desc F c) := by
  refine ⟨fun ⟨hc⟩ => ?_, fun h ↦ Nonempty.intro (isColimit_of_bijective_desc F c h)⟩
  change Function.Bijective (Quot.desc F c).toIntLinearMap
  rw [← CharacterModule.dual_bijective_iff_bijective]
  refine ⟨fun χ ψ eq ↦ ?_, fun χ ↦ ?_⟩
  · apply AddEquiv.ulift.symm.addMonoidHomCongrRightEquiv.injective
    apply ofHom_injective
    refine hc.hom_ext (fun j ↦ ?_)
    ext x
    erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ← Quot.ι_desc _ c j x]
    exact DFunLike.congr_fun eq (Quot.ι F j x)
  · set c' : Cocone F :=
      { pt := AddCommGrpCat.of (ULift (AddCircle (1 : ℚ)))
        ι :=
          { app j := AddCommGrpCat.ofHom (((@AddEquiv.ulift _ _).symm.toAddMonoidHom.comp χ).comp
                       (Quot.ι F j))
            naturality {j j'} u := by
              ext
              dsimp
              rw [Quot.map_ι F (f := u)] } }
    use AddEquiv.ulift.toAddMonoidHom.comp (hc.desc c').hom
    refine Quot.addMonoidHom_ext _ (fun j x ↦ ?_)
    dsimp
    rw [Quot.ι_desc]
    change AddEquiv.ulift ((c.ι.app j ≫ hc.desc c') x) = _
    rw [hc.fac]
    dsimp [c']
    rw [AddEquiv.apply_symm_apply]

/--
A functor `F : J ⥤ AddCommGrpCat.{w}` has a colimit if and only if `Colimits.Quot F` is
`w`-small.
-/
/-
**AddCommGrpCat.hasColimit_iff_small_quot** 是 Mathlib 中的一个引理，位于命名空间 `AddCommGrpC
at`。
形式化陈述：hasColimit_iff_small_quot [DecidableEq J] : HasColimit F ↔ Small.{w} (Quot
 F)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `AddCommGrpCat.isColimit_iff_bijective_desc`：isColimit_iff_bijective_desc
 [DecidableEq J] : Nonempty (IsColimit c) ↔ Function.Bijective (Quot.desc F c)
· 使用引理 `AddCommGrpCat.hasColimit_of_small_quot`：hasColimit_of_small_quot [Decida
bleEq J] (h : Small.{w} (Quot F)) : HasColimit F

--- 原说明 ---
A functor `F : J ⥤ AddCommGrpCat.{w}` has a colimit if and only if `Colimits.Quo
t F` is
`w`-small.
-/
lemma hasColimit_iff_small_quot [DecidableEq J] : HasColimit F ↔ Small.{w} (Quot F) :=
  ⟨fun _ ↦ Small.mk ⟨_, ⟨(Equiv.ofBijective _ ((isColimit_iff_bijective_desc (colimit.cocone F)).mp
    ⟨colimit.isColimit _⟩))⟩⟩, hasColimit_of_small_quot F⟩

end AddCommGrpCat

