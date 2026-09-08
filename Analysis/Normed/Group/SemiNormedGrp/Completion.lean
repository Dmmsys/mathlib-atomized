/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Johan Commelin
-/
module

public import Mathlib.Analysis.Normed.Group.SemiNormedGrp
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Analysis.Normed.Group.HomCompletion

/-!
# Completions of normed groups

This file contains an API for completions of seminormed groups (basic facts about
objects and morphisms).

## Main definitions

- `SemiNormedGrp.Completion : SemiNormedGrp ⥤ SemiNormedGrp` : the completion of a
  seminormed group (defined as a functor on `SemiNormedGrp` to itself).
- `SemiNormedGrp.Completion.lift (f : V ⟶ W) : (Completion.obj V ⟶ W)` : a normed group hom
  from `V` to complete `W` extends ("lifts") to a seminormed group hom from the completion of
  `V` to `W`.

## Projects

1. Construct the category of complete seminormed groups, say `CompleteSemiNormedGrp`
  and promote the `Completion` functor below to a functor landing in this category.
2. Prove that the functor `Completion : SemiNormedGrp ⥤ CompleteSemiNormedGrp`
  is left adjoint to the forgetful functor.

-/

@[expose] public section

noncomputable section

universe u

open UniformSpace MulOpposite CategoryTheory NormedAddGroupHom


namespace SemiNormedGrp

/-- The completion of a seminormed group, as an endofunctor on `SemiNormedGrp`. -/
@[simps]
/-
**SemiNormedGrp.completion** 是 Mathlib 中的一个定义，位于命名空间 `SemiNormedGrp`。
形式化陈述：completion : SemiNormedGrp.{u} ⥤ SemiNormedGrp.{u} where obj V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The completion of a seminormed group, as an endofunctor on `SemiNormedGrp`.
-/
def completion : SemiNormedGrp.{u} ⥤ SemiNormedGrp.{u} where
  obj V := SemiNormedGrp.of (Completion V)
  map f := SemiNormedGrp.ofHom f.hom.completion
  map_id _ := SemiNormedGrp.hom_ext completion_id
  map_comp f g := SemiNormedGrp.hom_ext (completion_comp f.hom g.hom).symm
/-
**SemiNormedGrp.completion_completeSpace** 是 Mathlib 中的一个实例，位于命名空间 `SemiNormedGr
p`。
形式化陈述：completion_completeSpace {V : SemiNormedGrp} : CompleteSpace (completion.o
bj V)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance completion_completeSpace {V : SemiNormedGrp} : CompleteSpace (completion.obj V) :=
  Completion.completeSpace _

/-- The canonical morphism from a seminormed group `V` to its completion. -/
/-
**SemiNormedGrp.completion.incl** 是 Mathlib 中的一个定义，位于命名空间 `SemiNormedGrp.complet
ion`。
形式化陈述：{V : SemiNormedGrp} → V ⟶ SemiNormedGrp.completion.obj V
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical morphism from a seminormed group `V` to its completion.
-/
def completion.incl {V : SemiNormedGrp} : V ⟶ completion.obj V :=
  ofHom
  { toFun v := (v : Completion V)
    map_add' := Completion.coe_add
    bound' := ⟨1, fun v => by simp⟩ }
/-
**SemiNormedGrp.completion.norm_incl_eq** 是 Mathlib 中的一个定理，位于命名空间 `SemiNormedGrp
.completion`。
形式化陈述：∀ {V : SemiNormedGrp} {v : V.carrier}, ‖(CategoryTheory.ConcreteCategory.h
om SemiNormedGrp.completion.incl) v‖ = ‖v‖
参数：CategoryTheory.ConcreteCategory.hom SemiNormedGrp.completion.incl。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.Completion.norm_coe`：norm_coe {E} [SeminormedAddCommGroup E
] (x : E) : ‖(x : Completion E)‖ = ‖x‖
-/
theorem completion.norm_incl_eq {V : SemiNormedGrp} {v : V} : ‖completion.incl v‖ = ‖v‖ :=
  UniformSpace.Completion.norm_coe _
/-
**SemiNormedGrp.completion.map_normNoninc** 是 Mathlib 中的一个定理，位于命名空间 `SemiNormedG
rp.completion`。
形式化陈述：∀ {V W : SemiNormedGrp} {f : V ⟶ W},   (SemiNormedGrp.Hom.hom f).NormNonin
c → (SemiNormedGrp.Hom.hom (SemiNormedGrp.completion.map f)).NormNoninc
参数：SemiNormedGrp.Hom.hom f；SemiNormedGrp.Hom.hom (SemiNormedGrp.completion.map f
)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one`：normNoninc_iff_
norm_le_one : f.NormNoninc ↔ ‖f‖ <= 1
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `NormedAddGroupHom.norm_completion`：NormedAddGroupHom.norm_completion (f 
: NormedAddGroupHom G H) : ‖f.completion‖ = ‖f‖
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem completion.map_normNoninc {V W : SemiNormedGrp} {f : V ⟶ W} (hf : f.hom.NormNoninc) :
    (completion.map f).hom.NormNoninc :=
  NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.2 <|
    (NormedAddGroupHom.norm_completion f.hom).le.trans <|
      NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.1 hf

variable (V W : SemiNormedGrp)

/-- Given a normed group hom `V ⟶ W`, this defines the associated morphism
from the completion of `V` to the completion of `W`.
The difference from the definition obtained from the functoriality of completion is in that the
map sending a morphism `f` to the associated morphism of completions is itself additive. -/
/-
**SemiNormedGrp.completion.mapHom** 是 Mathlib 中的一个定义，位于命名空间 `SemiNormedGrp.compl
etion`。
形式化陈述：(V W : SemiNormedGrp) → (V ⟶ W) →+ (SemiNormedGrp.completion.obj V ⟶ SemiN
ormedGrp.completion.obj W)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a normed group hom `V ⟶ W`, this defines the associated morphism
from the completion of `V` to the completion of `W`.
The difference from the definition obtained from the functoriality of completion
 is in that the
map sending a morphism `f` to the associated morphism of completions is itself a
dditive.
-/
def completion.mapHom (V W : SemiNormedGrp.{u}) :
     (V ⟶ W) →+ (completion.obj V ⟶ completion.obj W) :=
  @AddMonoidHom.mk' _ _ (_) (_) completion.map fun f g =>
    SemiNormedGrp.hom_ext (f.hom.completion_add g.hom)
/-
**SemiNormedGrp.completion.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `SemiNormedGrp.com
pletion`。
形式化陈述：∀ (V W : SemiNormedGrp), SemiNormedGrp.completion.map 0 = 0
参数：V W : SemiNormedGrp。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_zero`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M
] [inst_1 : AddZero N] (f : M →+ N), f 0 = 0
-/
theorem completion.map_zero (V W : SemiNormedGrp) : completion.map (0 : V ⟶ W) = 0 :=
  (completion.mapHom V W).map_zero
/-
**SemiNormedGrp.** 是 Mathlib 中的一个实例，位于命名空间 `SemiNormedGrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preadditive SemiNormedGrp.{u} where
/-
**SemiNormedGrp.** 是 Mathlib 中的一个实例，位于命名空间 `SemiNormedGrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Functor.Additive completion where
  map_add := SemiNormedGrp.hom_ext <| NormedAddGroupHom.completion_add _ _

/-- Given a normed group hom `f : V → W` with `W` complete, this provides a lift of `f` to
the completion of `V`. The lemmas `lift_unique` and `lift_comp_incl` provide the api for the
universal property of the completion. -/
/-
**SemiNormedGrp.completion.lift** 是 Mathlib 中的一个定义，位于命名空间 `SemiNormedGrp.complet
ion`。
形式化陈述：{V W : SemiNormedGrp} → [CompleteSpace W.carrier] → [T0Space W.carrier] → 
(V ⟶ W) → (SemiNormedGrp.completion.obj V ⟶ W)
参数：V ⟶ W；SemiNormedGrp.completion.obj V ⟶ W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a normed group hom `f : V → W` with `W` complete, this provides a lift of 
`f` to
the completion of `V`. The lemmas `lift_unique` and `lift_comp_incl` provide the
 api for the
universal property of the completion.
-/
def completion.lift {V W : SemiNormedGrp} [CompleteSpace W] [T0Space W] (f : V ⟶ W) :
    completion.obj V ⟶ W :=
  ofHom
  { toFun := f.hom.extension
    map_add' := f.hom.extension.toAddMonoidHom.map_add'
    bound' := f.hom.extension.bound' }
/-
**SemiNormedGrp.completion.lift_comp_incl** 是 Mathlib 中的一个定理，位于命名空间 `SemiNormedG
rp.completion`。
形式化陈述：∀ {V W : SemiNormedGrp} [inst : CompleteSpace W.carrier] [inst_1 : T0Space
 W.carrier] (f : V ⟶ W),   CategoryTheory.CategoryStruct.comp SemiNormedGrp.comp
letion.incl (SemiNormedGrp.completion.lift f) = f
参数：f : V ⟶ W；SemiNormedGrp.completion.lift f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemiNormedGrp.ext`：ext {M N : SemiNormedGrp} {f₁ f₂ : M ⟶ N} (h : forall
 (x : M), f₁ x = f₂ x) : f₁ = f₂
· 使用定理 `NormedAddGroupHom.extension_coe`：NormedAddGroupHom.extension_coe (f : No
rmedAddGroupHom G H) (v : G) : f.extension v = f v
-/
theorem completion.lift_comp_incl {V W : SemiNormedGrp} [CompleteSpace W] [T0Space W]
    (f : V ⟶ W) : completion.incl ≫ completion.lift f = f :=
  ext <| NormedAddGroupHom.extension_coe _
/-
**SemiNormedGrp.completion.lift_unique** 是 Mathlib 中的一个定理，位于命名空间 `SemiNormedGrp.
completion`。
形式化陈述：∀ {V W : SemiNormedGrp} [inst : CompleteSpace W.carrier] [inst_1 : T0Space
 W.carrier] (f : V ⟶ W)   (g : SemiNormedGrp.completion.obj V ⟶ W),   CategoryTh
eory.CategoryStruct.comp SemiNormedGrp.completion.incl g = f → g = SemiNormedGrp
.completion.lift f
参数：f : V ⟶ W；g : SemiNormedGrp.completion.obj V ⟶ W。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemiNormedGrp.hom_ext`：hom_ext {M N : SemiNormedGrp} {f g : M ⟶ N} (hf :
 f.hom = g.hom) : f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedAddGroupHom.extension_unique`：NormedAddGroupHom.extension_unique (
f : NormedAddGroupHom G H) {g : NormedAddGroupHom (Completion G) H} (hg : forall
 v, f v = g v) : f.exten…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SemiNormedGrp.ext_iff`：∀ {M N : SemiNormedGrp} {f₁ f₂ : M ⟶ N},   f₁ = f
₂ ↔ ∀ (x : M.carrier), (CategoryTheory.ConcreteCategory.hom f₁) x = (CategoryThe
ory.Concret…
-/
theorem completion.lift_unique {V W : SemiNormedGrp} [CompleteSpace W] [T0Space W]
    (f : V ⟶ W) (g : completion.obj V ⟶ W) : completion.incl ≫ g = f → g = completion.lift f :=
  fun h => SemiNormedGrp.hom_ext (NormedAddGroupHom.extension_unique _ fun v =>
    ((SemiNormedGrp.ext_iff.1 h) v).symm).symm

end SemiNormedGrp

