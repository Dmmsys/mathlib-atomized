/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc

/-!
# The diagonal object of a morphism.

We provide various API and isomorphisms considering the diagonal object `Δ_{Y/X} := pullback f f`
of a morphism `f : X ⟶ Y`.

-/

@[expose] public section


open CategoryTheory

noncomputable section

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] {X Y Z : C}

namespace pullback

section Diagonal

variable (f : X ⟶ Y) [HasPullback f f]

/-- The diagonal object of a morphism `f : X ⟶ Y` is `Δ_{X/Y} := pullback f f`. -/
/-
**CategoryTheory.Limits.pullback.diagonalObj** 是 Mathlib 中的一个缩写定义，位于命名空间 `Catego
ryTheory.Limits.pullback`。
形式化陈述：diagonalObj : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagonal object of a morphism `f : X ⟶ Y` is `Δ_{X/Y} := pullback f f`.
-/
abbrev diagonalObj : C :=
  pullback f f

/-- The diagonal morphism `X ⟶ Δ_{X/Y}` for a morphism `f : X ⟶ Y`. -/
/-
**CategoryTheory.Limits.pullback.diagonal** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits.pullback`。
形式化陈述：diagonal : X ⟶ diagonalObj f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagonal morphism `X ⟶ Δ_{X/Y}` for a morphism `f : X ⟶ Y`.
-/
def diagonal : X ⟶ diagonalObj f :=
  pullback.lift (𝟙 _) (𝟙 _) rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullback.diagonal_fst** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.pullback`。
形式化陈述：diagonal_fst : diagonal f ≫ pullback.fst _ _ = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.lift_fst`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
-/
theorem diagonal_fst : diagonal f ≫ pullback.fst _ _ = 𝟙 _ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullback.diagonal_snd** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.pullback`。
形式化陈述：diagonal_snd : diagonal f ≫ pullback.snd _ _ = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.lift_snd`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
-/
theorem diagonal_snd : diagonal f ≫ pullback.snd _ _ = 𝟙 _ :=
  pullback.lift_snd _ _ _
/-
**CategoryTheory.Limits.pullback.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limi
ts.pullback`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSplitMono (diagonal f) :=
  ⟨⟨⟨pullback.fst _ _, diagonal_fst f⟩⟩⟩
/-
**CategoryTheory.Limits.pullback.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limi
ts.pullback`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSplitEpi (pullback.fst f f) :=
  ⟨⟨⟨diagonal f, diagonal_fst f⟩⟩⟩
/-
**CategoryTheory.Limits.pullback.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limi
ts.pullback`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSplitEpi (pullback.snd f f) :=
  ⟨⟨⟨diagonal f, diagonal_snd f⟩⟩⟩
/-
**CategoryTheory.Limits.pullback.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limi
ts.pullback`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mono f] : IsIso (diagonal f) := by
  rw [(IsIso.inv_eq_of_inv_hom_id (diagonal_fst f)).symm]
  infer_instance
/-
**CategoryTheory.Limits.pullback.isIso_diagonal_iff** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Limits.pullback`。
形式化陈述：isIso_diagonal_iff : IsIso (diagonal f) ↔ Mono f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.pullback.lift_fst`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_fst`：diagonal_fst : diagonal f ≫
 pullback.fst _ _ = 𝟙 _
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_snd`：diagonal_snd : diagonal f ≫
 pullback.snd _ _ = 𝟙 _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.pullback.lift_snd`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
· 使用定理 `CategoryTheory.Limits.pullback.instIsIsoDiagonalOfMono`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y)   [inst_1 :
 CategoryTheory.Limits.HasPullback f f] [Cat…
-/
lemma isIso_diagonal_iff : IsIso (diagonal f) ↔ Mono f :=
  ⟨fun H ↦ ⟨fun _ _ e ↦ by rw [← lift_fst _ _ e, (cancel_epi (g := fst f f) (h := snd f f)
    (diagonal f)).mp (by simp), lift_snd]⟩, fun _ ↦ inferInstance⟩

/-- The two projections `Δ_{X/Y} ⟶ X` form a kernel pair for `f : X ⟶ Y`. -/
/-
**CategoryTheory.Limits.pullback.diagonal_isKernelPair** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits.pullback`。
形式化陈述：diagonal_isKernelPair : IsKernelPair f (pullback.fst f f) (pullback.snd f 
f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g

--- 原说明 ---
The two projections `Δ_{X/Y} ⟶ X` form a kernel pair for `f : X ⟶ Y`.
-/
theorem diagonal_isKernelPair : IsKernelPair f (pullback.fst f f) (pullback.snd f f) :=
  IsPullback.of_hasPullback f f

end Diagonal

end pullback

section Diagonal

variable [HasPullbacks C]

open pullback

section

variable {U V₁ V₂ : C} (f : X ⟶ Y) (i : U ⟶ Y)
variable (i₁ : V₁ ⟶ pullback f i) (i₂ : V₂ ⟶ pullback f i)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullback_diagonal_map_snd_fst_fst** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Limits`。
形式化陈述：pullback_diagonal_map_snd_fst_fst : (pullback.snd (diagonal f) (map (i₁ ≫ 
snd f i) (i₂ ≫ snd f i) f f (i₁ ≫ fst f i) (i₂ ≫ fst f i) i (by simp [condition]
) (by simp [condition]))) ≫ fst _ _ ≫ i₁ ≫ fst _ _ = pullback.fst _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_fst`：diagonal_fst : diagonal f ≫
 pullback.fst _ _ = 𝟙 _
· 使用定理 `CategoryTheory.Limits.pullback.condition_assoc`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 :
 CategoryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.pullback.lift_fst`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
-/
theorem pullback_diagonal_map_snd_fst_fst :
    (pullback.snd (diagonal f)
      (map (i₁ ≫ snd f i) (i₂ ≫ snd f i) f f (i₁ ≫ fst f i) (i₂ ≫ fst f i) i
        (by simp [condition]) (by simp [condition]))) ≫
      fst _ _ ≫ i₁ ≫ fst _ _ =
      pullback.fst _ _ := by
  conv_rhs => rw [← Category.comp_id (pullback.fst _ _)]
  rw [← diagonal_fst f, pullback.condition_assoc, pullback.lift_fst]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullback_diagonal_map_snd_snd_fst** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Limits`。
形式化陈述：pullback_diagonal_map_snd_snd_fst : (pullback.snd (diagonal f) (map (i₁ ≫ 
snd f i) (i₂ ≫ snd f i) f f (i₁ ≫ fst f i) (i₂ ≫ fst f i) i (by simp [condition]
) (by simp [condition]))) ≫ snd _ _ ≫ i₂ ≫ fst _ _ = pullback.fst _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_snd`：diagonal_snd : diagonal f ≫
 pullback.snd _ _ = 𝟙 _
· 使用定理 `CategoryTheory.Limits.pullback.condition_assoc`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 :
 CategoryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.pullback.lift_snd`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
-/
theorem pullback_diagonal_map_snd_snd_fst :
    (pullback.snd (diagonal f)
      (map (i₁ ≫ snd f i) (i₂ ≫ snd f i) f f (i₁ ≫ fst f i) (i₂ ≫ fst f i) i
        (by simp [condition]) (by simp [condition]))) ≫
      snd _ _ ≫ i₂ ≫ fst _ _ =
      pullback.fst _ _ := by
  conv_rhs => rw [← Category.comp_id (pullback.fst _ _)]
  rw [← diagonal_snd f, pullback.condition_assoc, pullback.lift_snd]

variable [HasPullback i₁ i₂]

/-- The underlying map of `pullbackDiagonalIso` -/
/-
**CategoryTheory.Limits.pullbackDiagonalMapIso.hom** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits.pullbackDiagonalMapIso`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {X 
Y : C} →       [inst_1 : CategoryTheory.Limits.HasPullbacks C] →         {U V₁ V
₂ : C} →           (f : X ⟶ Y) →             (i : U ⟶ Y) →               (i₁ : V
₁ ⟶ CategoryTheory.Limits.pullback f i) →                 (i₂ : V₂ ⟶ CategoryThe
ory.Limits.pullback f i) →                   [inst_2 : CategoryTheory.Limits.Has
Pullback i₁ i₂] →                     CategoryTheory.Limits.pullback (CategoryTh
eory.Limits.pullback.diagonal f)                         (CategoryTheory.Limits.
pullback.map                           (CategoryTheory.CategoryStruct.comp i₁ (C
ategoryTheory.Limits.pullback.snd f i))                           (CategoryTheor
y.CategoryStruct.comp i₂ (CategoryTheory.Limits.pullback.snd f i)) f f          
                 (CategoryTheory.CategoryStruct.comp i₁ (CategoryTheory.Limits.p
ullback.fst f i))                           (CategoryTheory.CategoryStruct.comp 
i₂ (CategoryTheory.Limits.pullback.fst f i)) i ⋯ ⋯) ⟶                       Cate
goryTheory.Limits.pullback i₁ i₂
参数：f : X ⟶ Y；i : U ⟶ Y；i₁ : V₁ ⟶ CategoryTheory.Limits.pullback f i；i₂ : V₂ ⟶ Ca
tegoryTheory.Limits.pullback f i；CategoryTheory.Limits.pullback.diagonal f；Categ
oryTheory.Limits.pullback.map                           (CategoryTheory.Category
Struct.comp i₁ (CategoryTheory.Limits.pullback.snd f i))                        
   (CategoryTheory.CategoryStruct.comp i₂ (CategoryTheory.Limits.pullback.snd f 
i)) f f                           (CategoryTheory.CategoryStruct.comp i₁ (Catego
ryTheory.Limits.pullback.fst f i))                           (CategoryTheory.Cat
egoryStruct.comp i₂ (CategoryTheory.Limits.pullback.fst f i)) i ⋯ ⋯。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying map of `pullbackDiagonalIso`
-/
abbrev pullbackDiagonalMapIso.hom :
    pullback (diagonal f)
        (map (i₁ ≫ snd _ _) (i₂ ≫ snd _ _) f f (i₁ ≫ fst _ _) (i₂ ≫ fst _ _) i
          (by simp only [Category.assoc, condition])
          (by simp only [Category.assoc, condition])) ⟶
      pullback i₁ i₂ :=
  pullback.lift (pullback.snd _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd _ _) (by
  ext
  · simp only [Category.assoc, pullback_diagonal_map_snd_fst_fst,
      pullback_diagonal_map_snd_snd_fst]
  · simp only [Category.assoc, condition])

set_option backward.isDefEq.respectTransparency false in
/-- The underlying inverse of `pullbackDiagonalIso` -/
/-
**CategoryTheory.Limits.pullbackDiagonalMapIso.inv** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits.pullbackDiagonalMapIso`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {X 
Y : C} →       [inst_1 : CategoryTheory.Limits.HasPullbacks C] →         {U V₁ V
₂ : C} →           (f : X ⟶ Y) →             (i : U ⟶ Y) →               (i₁ : V
₁ ⟶ CategoryTheory.Limits.pullback f i) →                 (i₂ : V₂ ⟶ CategoryThe
ory.Limits.pullback f i) →                   [inst_2 : CategoryTheory.Limits.Has
Pullback i₁ i₂] →                     CategoryTheory.Limits.pullback i₁ i₂ ⟶    
                   CategoryTheory.Limits.pullback (CategoryTheory.Limits.pullbac
k.diagonal f)                         (CategoryTheory.Limits.pullback.map       
                    (CategoryTheory.CategoryStruct.comp i₁ (CategoryTheory.Limit
s.pullback.snd f i))                           (CategoryTheory.CategoryStruct.co
mp i₂ (CategoryTheory.Limits.pullback.snd f i)) f f                           (C
ategoryTheory.CategoryStruct.comp i₁ (CategoryTheory.Limits.pullback.fst f i))  
                         (CategoryTheory.CategoryStruct.comp i₂ (CategoryTheory.
Limits.pullback.fst f i)) i ⋯ ⋯)
参数：f : X ⟶ Y；i : U ⟶ Y；i₁ : V₁ ⟶ CategoryTheory.Limits.pullback f i；i₂ : V₂ ⟶ Ca
tegoryTheory.Limits.pullback f i；CategoryTheory.Limits.pullback.diagonal f；Categ
oryTheory.Limits.pullback.map                           (CategoryTheory.Category
Struct.comp i₁ (CategoryTheory.Limits.pullback.snd f i))                        
   (CategoryTheory.CategoryStruct.comp i₂ (CategoryTheory.Limits.pullback.snd f 
i)) f f                           (CategoryTheory.CategoryStruct.comp i₁ (Catego
ryTheory.Limits.pullback.fst f i))                           (CategoryTheory.Cat
egoryStruct.comp i₂ (CategoryTheory.Limits.pullback.fst f i)) i ⋯ ⋯。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying inverse of `pullbackDiagonalIso`
-/
abbrev pullbackDiagonalMapIso.inv : pullback i₁ i₂ ⟶
    pullback (diagonal f)
        (map (i₁ ≫ snd _ _) (i₂ ≫ snd _ _) f f (i₁ ≫ fst _ _) (i₂ ≫ fst _ _) i
          (by simp only [Category.assoc, condition])
          (by simp only [Category.assoc, condition])) :=
    pullback.lift (pullback.fst _ _ ≫ i₁ ≫ pullback.fst _ _)
      (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (pullback.snd _ _) (Category.id_comp _).symm
        (Category.id_comp _).symm) (by
        ext
        · simp only [Category.assoc, diagonal_fst, Category.comp_id, limit.lift_π,
          PullbackCone.mk_π_app, limit.lift_π_assoc, cospan_left]
        · simp only [condition_assoc, Category.assoc, diagonal_snd, Category.comp_id, limit.lift_π,
          PullbackCone.mk_π_app, limit.lift_π_assoc, cospan_right])

set_option backward.isDefEq.respectTransparency false in
/-- This iso witnesses the fact that
given `f : X ⟶ Y`, `i : U ⟶ Y`, and `i₁ : V₁ ⟶ X ×[Y] U`, `i₂ : V₂ ⟶ X ×[Y] U`, the diagram

```
V₁ ×[X ×[Y] U] V₂ ⟶ V₁ ×[U] V₂
        |                 |
        |                 |
        ↓                 ↓
        X         ⟶   X ×[Y] X
```

is a pullback square.
Also see `pullback_fst_map_snd_isPullback`.
-/
/-
**CategoryTheory.Limits.pullbackDiagonalMapIso** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：pullbackDiagonalMapIso : pullback (diagonal f) (map (i₁ ≫ snd _ _) (i₂ ≫ s
nd _ _) f f (i₁ ≫ fst _ _) (i₂ ≫ fst _ _) i (by simp only [Category.assoc, condi
tion]) (by simp only [Category.assoc, condition])) ≅ pullback i₁ i₂ where hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This iso witnesses the fact that
given `f : X ⟶ Y`, `i : U ⟶ Y`, and `i₁ : V₁ ⟶ X ×[Y] U`, `i₂ : V₂ ⟶ X ×[Y] U`, 
the diagram

```
V₁ ×[X ×[Y] U] V₂ ⟶ V₁ ×[U] V₂
        |                 |
        |                 |
        ↓                 ↓
        X         ⟶   X ×[Y] X
```

is a pullback square.
Also see `pullback_fst_map_snd_isPullback`.
-/
def pullbackDiagonalMapIso :
    pullback (diagonal f)
        (map (i₁ ≫ snd _ _) (i₂ ≫ snd _ _) f f (i₁ ≫ fst _ _) (i₂ ≫ fst _ _) i
          (by simp only [Category.assoc, condition])
          (by simp only [Category.assoc, condition])) ≅
      pullback i₁ i₂ where
  hom := pullbackDiagonalMapIso.hom f i i₁ i₂
  inv := pullbackDiagonalMapIso.inv f i i₁ i₂

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackDiagonalMapIso.hom_fst** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits.pullbackDiagonalMapIso`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X Y : C} [
inst_1 : CategoryTheory.Limits.HasPullbacks C]   {U V₁ V₂ : C} (f : X ⟶ Y) (i : 
U ⟶ Y) (i₁ : V₁ ⟶ CategoryTheory.Limits.pullback f i)   (i₂ : V₂ ⟶ CategoryTheor
y.Limits.pullback f i) [inst_2 : CategoryTheory.Limits.HasPullback i₁ i₂],   Cat
egoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullbackDiagonalMapIso f 
i i₁ i₂).hom       (CategoryTheory.Limits.pullback.fst i₁ i₂) =     CategoryTheo
ry.CategoryStruct.comp       (CategoryTheory.Limits.pullback.snd (CategoryTheory
.Limits.pullback.diagonal f)         (CategoryTheory.Limits.pullback.map        
   (CategoryTheory.CategoryStruct.comp i₁ (CategoryTheory.Limits.pullback.snd f 
i))           (CategoryTheory.CategoryStruct.comp i₂ (CategoryTheory.Limits.pull
back.snd f i)) f f           (CategoryTheory.CategoryStruct.comp i₁ (CategoryThe
ory.Limits.pullback.fst f i))           (CategoryTheory.CategoryStruct.comp i₂ (
CategoryTheory.Limits.pullback.fst f i)) i ⋯ ⋯))       (CategoryTheory.Limits.pu
llback.fst         (CategoryTheory.CategoryStruct.comp i₁ (CategoryTheory.Limits
.pullback.snd f i))         (CategoryTheory.CategoryStruct.comp i₂ (CategoryTheo
ry.Limits.pullback.snd f i)))
参数：f : X ⟶ Y；i : U ⟶ Y；i₁ : V₁ ⟶ CategoryTheory.Limits.pullback f i；i₂ : V₂ ⟶ Ca
tegoryTheory.Limits.pullback f i；CategoryTheory.Limits.pullbackDiagonalMapIso f 
i i₁ i₂；CategoryTheory.Limits.pullback.fst i₁ i₂；CategoryTheory.Limits.pullback.
snd (CategoryTheory.Limits.pullback.diagonal f)         (CategoryTheory.Limits.p
ullback.map           (CategoryTheory.CategoryStruct.comp i₁ (CategoryTheory.Lim
its.pullback.snd f i))           (CategoryTheory.CategoryStruct.comp i₂ (Categor
yTheory.Limits.pullback.snd f i)) f f           (CategoryTheory.CategoryStruct.c
omp i₁ (CategoryTheory.Limits.pullback.fst f i))           (CategoryTheory.Categ
oryStruct.comp i₂ (CategoryTheory.Limits.pullback.fst f i)) i ⋯ ⋯)；CategoryTheor
y.Limits.pullback.fst         (CategoryTheory.CategoryStruct.comp i₁ (CategoryTh
eory.Limits.pullback.snd f i))         (CategoryTheory.CategoryStruct.comp i₂ (C
ategoryTheory.Limits.pullback.snd f i))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackDiagonalMapIso.hom_fst :
    (pullbackDiagonalMapIso f i i₁ i₂).hom ≫ pullback.fst _ _ =
      pullback.snd _ _ ≫ pullback.fst _ _ := by
  delta pullbackDiagonalMapIso
  simp only [limit.lift_π, PullbackCone.mk_π_app]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackDiagonalMapIso.hom_snd** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits.pullbackDiagonalMapIso`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X Y : C} [
inst_1 : CategoryTheory.Limits.HasPullbacks C]   {U V₁ V₂ : C} (f : X ⟶ Y) (i : 
U ⟶ Y) (i₁ : V₁ ⟶ CategoryTheory.Limits.pullback f i)   (i₂ : V₂ ⟶ CategoryTheor
y.Limits.pullback f i) [inst_2 : CategoryTheory.Limits.HasPullback i₁ i₂],   Cat
egoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullbackDiagonalMapIso f 
i i₁ i₂).hom       (CategoryTheory.Limits.pullback.snd i₁ i₂) =     CategoryTheo
ry.CategoryStruct.comp       (CategoryTheory.Limits.pullback.snd (CategoryTheory
.Limits.pullback.diagonal f)         (CategoryTheory.Limits.pullback.map        
   (CategoryTheory.CategoryStruct.comp i₁ (CategoryTheory.Limits.pullback.snd f 
i))           (CategoryTheory.CategoryStruct.comp i₂ (CategoryTheory.Limits.pull
back.snd f i)) f f           (CategoryTheory.CategoryStruct.comp i₁ (CategoryThe
ory.Limits.pullback.fst f i))           (CategoryTheory.CategoryStruct.comp i₂ (
CategoryTheory.Limits.pullback.fst f i)) i ⋯ ⋯))       (CategoryTheory.Limits.pu
llback.snd         (CategoryTheory.CategoryStruct.comp i₁ (CategoryTheory.Limits
.pullback.snd f i))         (CategoryTheory.CategoryStruct.comp i₂ (CategoryTheo
ry.Limits.pullback.snd f i)))
参数：f : X ⟶ Y；i : U ⟶ Y；i₁ : V₁ ⟶ CategoryTheory.Limits.pullback f i；i₂ : V₂ ⟶ Ca
tegoryTheory.Limits.pullback f i；CategoryTheory.Limits.pullbackDiagonalMapIso f 
i i₁ i₂；CategoryTheory.Limits.pullback.snd i₁ i₂；CategoryTheory.Limits.pullback.
snd (CategoryTheory.Limits.pullback.diagonal f)         (CategoryTheory.Limits.p
ullback.map           (CategoryTheory.CategoryStruct.comp i₁ (CategoryTheory.Lim
its.pullback.snd f i))           (CategoryTheory.CategoryStruct.comp i₂ (Categor
yTheory.Limits.pullback.snd f i)) f f           (CategoryTheory.CategoryStruct.c
omp i₁ (CategoryTheory.Limits.pullback.fst f i))           (CategoryTheory.Categ
oryStruct.comp i₂ (CategoryTheory.Limits.pullback.fst f i)) i ⋯ ⋯)；CategoryTheor
y.Limits.pullback.snd         (CategoryTheory.CategoryStruct.comp i₁ (CategoryTh
eory.Limits.pullback.snd f i))         (CategoryTheory.CategoryStruct.comp i₂ (C
ategoryTheory.Limits.pullback.snd f i))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackDiagonalMapIso.hom_snd :
    (pullbackDiagonalMapIso f i i₁ i₂).hom ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.snd _ _ := by
  delta pullbackDiagonalMapIso
  simp only [limit.lift_π, PullbackCone.mk_π_app]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackDiagonalMapIso.inv_fst** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits.pullbackDiagonalMapIso`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X Y : C} [
inst_1 : CategoryTheory.Limits.HasPullbacks C]   {U V₁ V₂ : C} (f : X ⟶ Y) (i : 
U ⟶ Y) (i₁ : V₁ ⟶ CategoryTheory.Limits.pullback f i)   (i₂ : V₂ ⟶ CategoryTheor
y.Limits.pullback f i) [inst_2 : CategoryTheory.Limits.HasPullback i₁ i₂],   Cat
egoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullbackDiagonalMapIso f 
i i₁ i₂).inv       (CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pu
llback.diagonal f)         (CategoryTheory.Limits.pullback.map           (Catego
ryTheory.CategoryStruct.comp i₁ (CategoryTheory.Limits.pullback.snd f i))       
    (CategoryTheory.CategoryStruct.comp i₂ (CategoryTheory.Limits.pullback.snd f
 i)) f f           (CategoryTheory.CategoryStruct.comp i₁ (CategoryTheory.Limits
.pullback.fst f i))           (CategoryTheory.CategoryStruct.comp i₂ (CategoryTh
eory.Limits.pullback.fst f i)) i ⋯ ⋯)) =     CategoryTheory.CategoryStruct.comp 
(CategoryTheory.Limits.pullback.fst i₁ i₂)       (CategoryTheory.CategoryStruct.
comp i₁ (CategoryTheory.Limits.pullback.fst f i))
参数：f : X ⟶ Y；i : U ⟶ Y；i₁ : V₁ ⟶ CategoryTheory.Limits.pullback f i；i₂ : V₂ ⟶ Ca
tegoryTheory.Limits.pullback f i；CategoryTheory.Limits.pullbackDiagonalMapIso f 
i i₁ i₂；CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.diago
nal f)         (CategoryTheory.Limits.pullback.map           (CategoryTheory.Cat
egoryStruct.comp i₁ (CategoryTheory.Limits.pullback.snd f i))           (Categor
yTheory.CategoryStruct.comp i₂ (CategoryTheory.Limits.pullback.snd f i)) f f    
       (CategoryTheory.CategoryStruct.comp i₁ (CategoryTheory.Limits.pullback.fs
t f i))           (CategoryTheory.CategoryStruct.comp i₂ (CategoryTheory.Limits.
pullback.fst f i)) i ⋯ ⋯)；CategoryTheory.Limits.pullback.fst i₁ i₂；CategoryTheor
y.CategoryStruct.comp i₁ (CategoryTheory.Limits.pullback.fst f i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackDiagonalMapIso.inv_fst :
    (pullbackDiagonalMapIso f i i₁ i₂).inv ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ i₁ ≫ pullback.fst _ _ := by
  delta pullbackDiagonalMapIso
  simp only [limit.lift_π, PullbackCone.mk_π_app]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackDiagonalMapIso.inv_snd_fst** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Limits.pullbackDiagonalMapIso`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X Y : C} [
inst_1 : CategoryTheory.Limits.HasPullbacks C]   {U V₁ V₂ : C} (f : X ⟶ Y) (i : 
U ⟶ Y) (i₁ : V₁ ⟶ CategoryTheory.Limits.pullback f i)   (i₂ : V₂ ⟶ CategoryTheor
y.Limits.pullback f i) [inst_2 : CategoryTheory.Limits.HasPullback i₁ i₂],   Cat
egoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullbackDiagonalMapIso f 
i i₁ i₂).inv       (CategoryTheory.CategoryStruct.comp         (CategoryTheory.L
imits.pullback.snd (CategoryTheory.Limits.pullback.diagonal f)           (Catego
ryTheory.Limits.pullback.map             (CategoryTheory.CategoryStruct.comp i₁ 
(CategoryTheory.Limits.pullback.snd f i))             (CategoryTheory.CategorySt
ruct.comp i₂ (CategoryTheory.Limits.pullback.snd f i)) f f             (Category
Theory.CategoryStruct.comp i₁ (CategoryTheory.Limits.pullback.fst f i))         
    (CategoryTheory.CategoryStruct.comp i₂ (CategoryTheory.Limits.pullback.fst f
 i)) i ⋯ ⋯))         (CategoryTheory.Limits.pullback.fst           (CategoryTheo
ry.CategoryStruct.comp i₁ (CategoryTheory.Limits.pullback.snd f i))           (C
ategoryTheory.CategoryStruct.comp i₂ (CategoryTheory.Limits.pullback.snd f i))))
 =     CategoryTheory.Limits.pullback.fst i₁ i₂
参数：f : X ⟶ Y；i : U ⟶ Y；i₁ : V₁ ⟶ CategoryTheory.Limits.pullback f i；i₂ : V₂ ⟶ Ca
tegoryTheory.Limits.pullback f i；CategoryTheory.Limits.pullbackDiagonalMapIso f 
i i₁ i₂；CategoryTheory.CategoryStruct.comp         (CategoryTheory.Limits.pullba
ck.snd (CategoryTheory.Limits.pullback.diagonal f)           (CategoryTheory.Lim
its.pullback.map             (CategoryTheory.CategoryStruct.comp i₁ (CategoryThe
ory.Limits.pullback.snd f i))             (CategoryTheory.CategoryStruct.comp i₂
 (CategoryTheory.Limits.pullback.snd f i)) f f             (CategoryTheory.Categ
oryStruct.comp i₁ (CategoryTheory.Limits.pullback.fst f i))             (Categor
yTheory.CategoryStruct.comp i₂ (CategoryTheory.Limits.pullback.fst f i)) i ⋯ ⋯))
         (CategoryTheory.Limits.pullback.fst           (CategoryTheory.CategoryS
truct.comp i₁ (CategoryTheory.Limits.pullback.snd f i))           (CategoryTheor
y.CategoryStruct.comp i₂ (CategoryTheory.Limits.pullback.snd f i)))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackDiagonalMapIso.inv_snd_fst :
    (pullbackDiagonalMapIso f i i₁ i₂).inv ≫ pullback.snd _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ := by
  delta pullbackDiagonalMapIso
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackDiagonalMapIso.inv_snd_snd** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Limits.pullbackDiagonalMapIso`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X Y : C} [
inst_1 : CategoryTheory.Limits.HasPullbacks C]   {U V₁ V₂ : C} (f : X ⟶ Y) (i : 
U ⟶ Y) (i₁ : V₁ ⟶ CategoryTheory.Limits.pullback f i)   (i₂ : V₂ ⟶ CategoryTheor
y.Limits.pullback f i) [inst_2 : CategoryTheory.Limits.HasPullback i₁ i₂],   Cat
egoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullbackDiagonalMapIso f 
i i₁ i₂).inv       (CategoryTheory.CategoryStruct.comp         (CategoryTheory.L
imits.pullback.snd (CategoryTheory.Limits.pullback.diagonal f)           (Catego
ryTheory.Limits.pullback.map             (CategoryTheory.CategoryStruct.comp i₁ 
(CategoryTheory.Limits.pullback.snd f i))             (CategoryTheory.CategorySt
ruct.comp i₂ (CategoryTheory.Limits.pullback.snd f i)) f f             (Category
Theory.CategoryStruct.comp i₁ (CategoryTheory.Limits.pullback.fst f i))         
    (CategoryTheory.CategoryStruct.comp i₂ (CategoryTheory.Limits.pullback.fst f
 i)) i ⋯ ⋯))         (CategoryTheory.Limits.pullback.snd           (CategoryTheo
ry.CategoryStruct.comp i₁ (CategoryTheory.Limits.pullback.snd f i))           (C
ategoryTheory.CategoryStruct.comp i₂ (CategoryTheory.Limits.pullback.snd f i))))
 =     CategoryTheory.Limits.pullback.snd i₁ i₂
参数：f : X ⟶ Y；i : U ⟶ Y；i₁ : V₁ ⟶ CategoryTheory.Limits.pullback f i；i₂ : V₂ ⟶ Ca
tegoryTheory.Limits.pullback f i；CategoryTheory.Limits.pullbackDiagonalMapIso f 
i i₁ i₂；CategoryTheory.CategoryStruct.comp         (CategoryTheory.Limits.pullba
ck.snd (CategoryTheory.Limits.pullback.diagonal f)           (CategoryTheory.Lim
its.pullback.map             (CategoryTheory.CategoryStruct.comp i₁ (CategoryThe
ory.Limits.pullback.snd f i))             (CategoryTheory.CategoryStruct.comp i₂
 (CategoryTheory.Limits.pullback.snd f i)) f f             (CategoryTheory.Categ
oryStruct.comp i₁ (CategoryTheory.Limits.pullback.fst f i))             (Categor
yTheory.CategoryStruct.comp i₂ (CategoryTheory.Limits.pullback.fst f i)) i ⋯ ⋯))
         (CategoryTheory.Limits.pullback.snd           (CategoryTheory.CategoryS
truct.comp i₁ (CategoryTheory.Limits.pullback.snd f i))           (CategoryTheor
y.CategoryStruct.comp i₂ (CategoryTheory.Limits.pullback.snd f i)))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackDiagonalMapIso.inv_snd_snd :
    (pullbackDiagonalMapIso f i i₁ i₂).inv ≫ pullback.snd _ _ ≫ pullback.snd _ _ =
      pullback.snd _ _ := by
  delta pullbackDiagonalMapIso
  simp

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.pullback_fst_map_snd_isPullback** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：pullback_fst_map_snd_isPullback : IsPullback (fst _ _ ≫ i₁ ≫ fst _ _) (map
 i₁ i₂ (i₁ ≫ snd _ _) (i₂ ≫ snd _ _) _ _ _ (Category.id_comp _).symm (Category.i
d_comp _).symm) (diagonal f) (map (i₁ ≫ snd _ _) (i₂ ≫ snd _ _) f f (i₁ ≫ fst _ 
_) (i₂ ≫ fst _ _) i (by simp [condition]) (by simp [condition]))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsPullback.of_iso_pullback`：of_iso_pullback (h : CommSq f
st snd f g) [HasPullback f g] (i : P ≅ pullback f g) (w₁ : i.hom ≫ pullback.fst 
_ _ = fst) (w₂ : i.hom ≫ pullba…
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.pullback.condition_assoc`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 :
 CategoryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_fst`：diagonal_fst : diagonal f ≫
 pullback.fst _ _ = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_snd`：diagonal_snd : diagonal f ≫
 pullback.snd _ _ = 𝟙 _
· 使用定理 `CategoryTheory.Limits.pullbackDiagonalMapIso.inv_fst`：∀ {C : Type u_1} [
inst : CategoryTheory.Category.{v_1, u_1} C] {X Y : C} [inst_1 : CategoryTheory.
Limits.HasPullbacks C]   {U V₁ V₂ : C} (f …
· 使用定理 `CategoryTheory.Limits.pullbackDiagonalMapIso.inv_snd_fst`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X Y : C} [inst_1 : CategoryThe
ory.Limits.HasPullbacks C]   {U V₁ V₂ : C} (f …
· 使用定理 `CategoryTheory.Limits.pullbackDiagonalMapIso.inv_snd_snd`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X Y : C} [inst_1 : CategoryThe
ory.Limits.HasPullbacks C]   {U V₁ V₂ : C} (f …
-/
theorem pullback_fst_map_snd_isPullback :
    IsPullback (fst _ _ ≫ i₁ ≫ fst _ _)
      (map i₁ i₂ (i₁ ≫ snd _ _) (i₂ ≫ snd _ _) _ _ _
        (Category.id_comp _).symm (Category.id_comp _).symm)
      (diagonal f)
      (map (i₁ ≫ snd _ _) (i₂ ≫ snd _ _) f f (i₁ ≫ fst _ _) (i₂ ≫ fst _ _) i (by simp [condition])
        (by simp [condition])) :=
  IsPullback.of_iso_pullback ⟨by ext <;> simp [condition_assoc]⟩
    (pullbackDiagonalMapIso f i i₁ i₂).symm (pullbackDiagonalMapIso.inv_fst f i i₁ i₂)
    (by cat_disch)

end

section

variable {S T : C} (f : X ⟶ T) (g : Y ⟶ T) (i : T ⟶ S)
variable [HasPullback i i] [HasPullback f g] [HasPullback (f ≫ i) (g ≫ i)]
variable
  [HasPullback (diagonal i)
      (pullback.map (f ≫ i) (g ≫ i) i i f g (𝟙 _) (Category.comp_id _) (Category.comp_id _))]

set_option backward.isDefEq.respectTransparency false in
/-- This iso witnesses the fact that
given `f : X ⟶ T`, `g : Y ⟶ T`, and `i : T ⟶ S`, the diagram

```
X ×ₜ Y ⟶ X ×ₛ Y
  |         |
  |         |
  ↓         ↓
  T    ⟶  T ×ₛ T
```

is a pullback square.
Also see `pullback_map_diagonal_isPullback`.
-/
/-
**CategoryTheory.Limits.pullbackDiagonalMapIdIso** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：pullbackDiagonalMapIdIso : pullback (diagonal i) (pullback.map (f ≫ i) (g 
≫ i) i i f g (𝟙 _) (Category.comp_id _) (Category.comp_id _)) ≅ pullback f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This iso witnesses the fact that
given `f : X ⟶ T`, `g : Y ⟶ T`, and `i : T ⟶ S`, the diagram

```
X ×ₜ Y ⟶ X ×ₛ Y
  |         |
  |         |
  ↓         ↓
  T    ⟶  T ×ₛ T
```

is a pullback square.
Also see `pullback_map_diagonal_isPullback`.
-/
def pullbackDiagonalMapIdIso :
    pullback (diagonal i)
        (pullback.map (f ≫ i) (g ≫ i) i i f g (𝟙 _) (Category.comp_id _) (Category.comp_id _)) ≅
      pullback f g := by
  refine ?_ ≪≫
    pullbackDiagonalMapIso i (𝟙 _) (f ≫ inv (pullback.fst _ _)) (g ≫ inv (pullback.fst _ _)) ≪≫ ?_
  · refine @asIso _ _ _ _ (pullback.map _ _ _ _ (𝟙 T) ((pullback.congrHom ?_ ?_).hom) (𝟙 _) ?_ ?_)
      ?_
    · rw [← Category.comp_id (pullback.snd ..), ← condition, Category.assoc, IsIso.inv_hom_id_assoc]
    · rw [← Category.comp_id (pullback.snd ..), ← condition, Category.assoc, IsIso.inv_hom_id_assoc]
    · rw [Category.comp_id, Category.id_comp]
    · ext <;> simp
    · infer_instance
  · refine @asIso _ _ _ _ (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (pullback.fst _ _) ?_ ?_) ?_
    · rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.id_comp]
    · infer_instance

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackDiagonalMapIdIso_hom_fst** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：pullbackDiagonalMapIdIso_hom_fst : (pullbackDiagonalMapIdIso f g i).hom ≫ 
pullback.fst _ _ = pullback.snd _ _ ≫ pullback.fst _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.pullback.congrHom_hom`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z} (h₁ : 
f₁ = f₂)   (h₂ : g₁ = g₂) [inst_1…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.pullback.map.congr_simp`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S)   [i
nst_1 : CategoryTheory.Limits.HasPu…
· 使用定理 `CategoryTheory.asIso.congr_simp`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f f_1 : X ⟶ Y) (e_f : f = f_1)   [inst_1 : Category
Theory.IsIso f], Cate…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Limits.pullbackDiagonalMapIso.hom_fst`：∀ {C : Type u_1} [
inst : CategoryTheory.Category.{v_1, u_1} C] {X Y : C} [inst_1 : CategoryTheory.
Limits.HasPullbacks C]   {U V₁ V₂ : C} (f …
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackDiagonalMapIdIso_hom_fst :
    (pullbackDiagonalMapIdIso f g i).hom ≫ pullback.fst _ _ =
      pullback.snd _ _ ≫ pullback.fst _ _ := by
  delta pullbackDiagonalMapIdIso
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackDiagonalMapIdIso_hom_snd** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：pullbackDiagonalMapIdIso_hom_snd : (pullbackDiagonalMapIdIso f g i).hom ≫ 
pullback.snd _ _ = pullback.snd _ _ ≫ pullback.snd _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.pullback.congrHom_hom`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z} (h₁ : 
f₁ = f₂)   (h₂ : g₁ = g₂) [inst_1…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.pullback.map.congr_simp`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S)   [i
nst_1 : CategoryTheory.Limits.HasPu…
· 使用定理 `CategoryTheory.asIso.congr_simp`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f f_1 : X ⟶ Y) (e_f : f = f_1)   [inst_1 : Category
Theory.IsIso f], Cate…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Limits.pullbackDiagonalMapIso.hom_snd`：∀ {C : Type u_1} [
inst : CategoryTheory.Category.{v_1, u_1} C] {X Y : C} [inst_1 : CategoryTheory.
Limits.HasPullbacks C]   {U V₁ V₂ : C} (f …
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackDiagonalMapIdIso_hom_snd :
    (pullbackDiagonalMapIdIso f g i).hom ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.snd _ _ := by
  delta pullbackDiagonalMapIdIso
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackDiagonalMapIdIso_inv_fst** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：pullbackDiagonalMapIdIso_inv_fst : (pullbackDiagonalMapIdIso f g i).inv ≫ 
pullback.fst _ _ = pullback.fst _ _ ≫ f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_fst`：diagonal_fst : diagonal f ≫
 pullback.fst _ _ = 𝟙 _
· 使用定理 `CategoryTheory.Limits.pullback.condition_assoc`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 :
 CategoryTheory.Limits.HasPullback f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Limits.pullbackDiagonalMapIdIso_hom_fst_assoc`：∀ {C : Typ
e u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X Y : C} [inst_1 : Categor
yTheory.Limits.HasPullbacks C]   {S T : C} (f : X …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackDiagonalMapIdIso_inv_fst :
    (pullbackDiagonalMapIdIso f g i).inv ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f := by
  rw [Iso.inv_comp_eq, ← Category.comp_id (pullback.fst _ _), ← diagonal_fst i,
    pullback.condition_assoc]
  simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackDiagonalMapIdIso_inv_snd_fst** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Limits`。
形式化陈述：pullbackDiagonalMapIdIso_inv_snd_fst : (pullbackDiagonalMapIdIso f g i).in
v ≫ pullback.snd _ _ ≫ pullback.fst _ _ = pullback.fst _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.pullbackDiagonalMapIdIso_hom_fst`：pullbackDiagonal
MapIdIso_hom_fst : (pullbackDiagonalMapIdIso f g i).hom ≫ pullback.fst _ _ = pul
lback.snd _ _ ≫ pullback.fst _ _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackDiagonalMapIdIso_inv_snd_fst :
    (pullbackDiagonalMapIdIso f g i).inv ≫ pullback.snd _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ := by
  rw [Iso.inv_comp_eq]
  simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackDiagonalMapIdIso_inv_snd_snd** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Limits`。
形式化陈述：pullbackDiagonalMapIdIso_inv_snd_snd : (pullbackDiagonalMapIdIso f g i).in
v ≫ pullback.snd _ _ ≫ pullback.snd _ _ = pullback.snd _ _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.pullbackDiagonalMapIdIso_hom_snd`：pullbackDiagonal
MapIdIso_hom_snd : (pullbackDiagonalMapIdIso f g i).hom ≫ pullback.snd _ _ = pul
lback.snd _ _ ≫ pullback.snd _ _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackDiagonalMapIdIso_inv_snd_snd :
    (pullbackDiagonalMapIdIso f g i).inv ≫ pullback.snd _ _ ≫ pullback.snd _ _ =
      pullback.snd _ _ := by
  rw [Iso.inv_comp_eq]
  simp
/-
**CategoryTheory.Limits.pullback.diagonal_comp** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits.pullback`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X Y Z : C}
   [inst_1 : CategoryTheory.Limits.HasPullbacks C] (f : X ⟶ Y) (g : Y ⟶ Z),   Ca
tegoryTheory.Limits.pullback.diagonal (CategoryTheory.CategoryStruct.comp f g) =
     CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullback.diagonal
 f)       (CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.pullbackDia
gonalMapIdIso f f g).inv         (CategoryTheory.Limits.pullback.snd (CategoryTh
eory.Limits.pullback.diagonal g)           (CategoryTheory.Limits.pullback.map (
CategoryTheory.CategoryStruct.comp f g)             (CategoryTheory.CategoryStru
ct.comp f g) g g f f (CategoryTheory.CategoryStruct.id Z) ⋯ ⋯)))
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.comp f g；CategoryTheory.Lim
its.pullback.diagonal f；CategoryTheory.CategoryStruct.comp (CategoryTheory.Limit
s.pullbackDiagonalMapIdIso f f g).inv         (CategoryTheory.Limits.pullback.sn
d (CategoryTheory.Limits.pullback.diagonal g)           (CategoryTheory.Limits.p
ullback.map (CategoryTheory.CategoryStruct.comp f g)             (CategoryTheory
.CategoryStruct.comp f g) g g f f (CategoryTheory.CategoryStruct.id Z) ⋯ ⋯))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_fst`：diagonal_fst : diagonal f ≫
 pullback.fst _ _ = 𝟙 _
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullbackDiagonalMapIdIso_inv_snd_fst`：pullbackDiag
onalMapIdIso_inv_snd_fst : (pullbackDiagonalMapIdIso f g i).inv ≫ pullback.snd _
 _ ≫ pullback.fst _ _ = pullback.fst _ _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_snd`：diagonal_snd : diagonal f ≫
 pullback.snd _ _ = 𝟙 _
· 使用定理 `CategoryTheory.Limits.pullbackDiagonalMapIdIso_inv_snd_snd`：pullbackDiag
onalMapIdIso_inv_snd_snd : (pullbackDiagonalMapIdIso f g i).inv ≫ pullback.snd _
 _ ≫ pullback.snd _ _ = pullback.snd _ _
-/
theorem pullback.diagonal_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    diagonal (f ≫ g) = diagonal f ≫ (pullbackDiagonalMapIdIso f f g).inv ≫ pullback.snd _ _ := by
  ext <;> simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Limits.pullback.comp_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits.pullback`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X Y Z : C}
   [inst_1 : CategoryTheory.Limits.HasPullbacks C] (f : X ⟶ Y) (g : Y ⟶ Z),   Ca
tegoryTheory.CategoryStruct.comp f (CategoryTheory.Limits.pullback.diagonal g) =
     CategoryTheory.CategoryStruct.comp       (CategoryTheory.Limits.pullback.di
agonal (CategoryTheory.CategoryStruct.comp f g))       (CategoryTheory.Limits.pu
llback.map (CategoryTheory.CategoryStruct.comp f g)         (CategoryTheory.Cate
goryStruct.comp f g) g g f f (CategoryTheory.CategoryStruct.id Z) ⋯ ⋯)
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.Limits.pullback.diagonal g；CategoryTheory.
Limits.pullback.diagonal (CategoryTheory.CategoryStruct.comp f g)；CategoryTheory
.Limits.pullback.map (CategoryTheory.CategoryStruct.comp f g)         (CategoryT
heory.CategoryStruct.comp f g) g g f f (CategoryTheory.CategoryStruct.id Z) ⋯ ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_fst`：diagonal_fst : diagonal f ≫
 pullback.fst _ _ = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_fst_assoc`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : Cate
goryTheory.Limits.HasPullback f f] {Z :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_snd`：diagonal_snd : diagonal f ≫
 pullback.snd _ _ = 𝟙 _
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_snd_assoc`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : Cate
goryTheory.Limits.HasPullback f f] {Z :…
-/
lemma pullback.comp_diagonal (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ pullback.diagonal g = pullback.diagonal (f ≫ g) ≫
      pullback.map (f ≫ g) (f ≫ g) g g f f (𝟙 Z) (by simp) (by simp) := by
  ext <;> simp

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.pullback_map_diagonal_isPullback** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：pullback_map_diagonal_isPullback : IsPullback (pullback.fst _ _ ≫ f) (pull
back.map f g (f ≫ i) (g ≫ i) _ _ i (Category.id_comp _).symm (Category.id_comp _
).symm) (diagonal i) (pullback.map (f ≫ i) (g ≫ i) i i f g (𝟙 _) (Category.comp_
id _) (Category.comp_id _))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.IsPullback.of_iso_pullback`：of_iso_pullback (h : CommSq f
st snd f g) [HasPullback f g] (i : P ≅ pullback f g) (w₁ : i.hom ≫ pullback.fst 
_ _ = fst) (w₂ : i.hom ≫ pullba…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_fst`：diagonal_fst : diagonal f ≫
 pullback.fst _ _ = 𝟙 _
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_snd`：diagonal_snd : diagonal f ≫
 pullback.snd _ _ = 𝟙 _
· 使用定理 `CategoryTheory.Limits.pullbackDiagonalMapIdIso_inv_fst`：pullbackDiagonal
MapIdIso_inv_fst : (pullbackDiagonalMapIdIso f g i).inv ≫ pullback.fst _ _ = pul
lback.fst _ _ ≫ f
· 使用定理 `CategoryTheory.Limits.pullbackDiagonalMapIdIso_inv_snd_fst`：pullbackDiag
onalMapIdIso_inv_snd_fst : (pullbackDiagonalMapIdIso f g i).inv ≫ pullback.snd _
 _ ≫ pullback.fst _ _ = pullback.fst _ _
· 使用定理 `CategoryTheory.Limits.pullbackDiagonalMapIdIso_inv_snd_snd`：pullbackDiag
onalMapIdIso_inv_snd_snd : (pullbackDiagonalMapIdIso f g i).inv ≫ pullback.snd _
 _ ≫ pullback.snd _ _ = pullback.snd _ _
-/
theorem pullback_map_diagonal_isPullback :
    IsPullback (pullback.fst _ _ ≫ f)
      (pullback.map f g (f ≫ i) (g ≫ i) _ _ i (Category.id_comp _).symm (Category.id_comp _).symm)
      (diagonal i)
      (pullback.map (f ≫ i) (g ≫ i) i i f g (𝟙 _) (Category.comp_id _) (Category.comp_id _)) := by
  apply IsPullback.of_iso_pullback _ (pullbackDiagonalMapIdIso f g i).symm
  · simp
  · ext <;> simp
  · constructor
    ext <;> simp [condition]

/-- The diagonal object of `X ×[Z] Y ⟶ X` is isomorphic to `Δ_{Y/Z} ×[Z] X`. -/
/-
**CategoryTheory.Limits.diagonalObjPullbackFstIso** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：diagonalObjPullbackFstIso {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : diagonalOb
j (pullback.fst f g) ≅ pullback (pullback.snd _ _ ≫ g : diagonalObj g ⟶ Z) f
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagonal object of `X ×[Z] Y ⟶ X` is isomorphic to `Δ_{Y/Z} ×[Z] X`.
-/
def diagonalObjPullbackFstIso {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    diagonalObj (pullback.fst f g) ≅
      pullback (pullback.snd _ _ ≫ g : diagonalObj g ⟶ Z) f :=
  pullbackRightPullbackFstIso _ _ _ ≪≫
    pullback.congrHom pullback.condition rfl ≪≫
      pullbackAssoc _ _ _ _ ≪≫ pullbackSymmetry _ _ ≪≫ pullback.congrHom pullback.condition rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.diagonalObjPullbackFstIso_hom_fst_fst** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：diagonalObjPullbackFstIso_hom_fst_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) 
: (diagonalObjPullbackFstIso f g).hom ≫ pullback.fst _ _ ≫ pullback.fst _ _ = pu
llback.fst _ _ ≫ pullback.snd _ _
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.pullback.congrHom_hom`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z} (h₁ : 
f₁ = f₂)   (h₂ : g₁ = g₂) [inst_1…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_hom_comp_fst_assoc`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) 
  [inst_1 : CategoryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.pullbackAssoc_hom_snd_fst`：pullbackAssoc_hom_snd_f
st [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄] [HasPullback f₁ ((pullba
ck.fst _ _ : Z₂ ⟶ X₂) ≫ f₂)] : (pullb…
· 使用定理 `CategoryTheory.Limits.pullbackRightPullbackFstIso_hom_fst_assoc`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} (f : X ⟶ Z) (g :
 Y ⟶ Z) (f' : W ⟶ X)   [inst_1 : CategoryTheory.Limit…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem diagonalObjPullbackFstIso_hom_fst_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).hom ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  delta diagonalObjPullbackFstIso
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.diagonalObjPullbackFstIso_hom_fst_snd** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：diagonalObjPullbackFstIso_hom_fst_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) 
: (diagonalObjPullbackFstIso f g).hom ≫ pullback.fst _ _ ≫ pullback.snd _ _ = pu
llback.snd _ _ ≫ pullback.snd _ _
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.pullback.congrHom_hom`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z} (h₁ : 
f₁ = f₂)   (h₂ : g₁ = g₂) [inst_1…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_hom_comp_fst_assoc`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) 
  [inst_1 : CategoryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.pullbackAssoc_hom_snd_snd`：pullbackAssoc_hom_snd_s
nd [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄] [HasPullback f₁ ((pullba
ck.fst _ _ : Z₂ ⟶ X₂) ≫ f₂)] : (pullb…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.pullbackRightPullbackFstIso_hom_snd`：pullbackRight
PullbackFstIso_hom_snd : (pullbackRightPullbackFstIso f g f').hom ≫ pullback.snd
 _ _ = pullback.snd f' (pullback.fst f g) ≫ pul…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem diagonalObjPullbackFstIso_hom_fst_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).hom ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.snd _ _ := by
  delta diagonalObjPullbackFstIso
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.diagonalObjPullbackFstIso_hom_snd** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Limits`。
形式化陈述：diagonalObjPullbackFstIso_hom_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : (d
iagonalObjPullbackFstIso f g).hom ≫ pullback.snd _ _ = pullback.fst _ _ ≫ pullba
ck.fst _ _
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.pullback.congrHom_hom`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z} (h₁ : 
f₁ = f₂)   (h₂ : g₁ = g₂) [inst_1…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_hom_comp_snd`：pullbackSymmetry_ho
m_comp_snd [HasPullback f g] : (pullbackSymmetry f g).hom ≫ pullback.snd g f = p
ullback.fst f g
· 使用定理 `CategoryTheory.Limits.pullbackAssoc_hom_fst`：pullbackAssoc_hom_fst [HasP
ullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄] [HasPullback f₁ ((pullback.fst _
 _ : Z₂ ⟶ X₂) ≫ f₂)] : (pullbackA…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.pullbackRightPullbackFstIso_hom_fst_assoc`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} (f : X ⟶ Z) (g :
 Y ⟶ Z) (f' : W ⟶ X)   [inst_1 : CategoryTheory.Limit…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem diagonalObjPullbackFstIso_hom_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).hom ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ := by
  delta diagonalObjPullbackFstIso
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.diagonalObjPullbackFstIso_inv_fst_fst** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：diagonalObjPullbackFstIso_inv_fst_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) 
: (diagonalObjPullbackFstIso f g).inv ≫ pullback.fst _ _ ≫ pullback.fst _ _ = pu
llback.snd _ _
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.pullback.congrHom_inv`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z} (h₁ : 
f₁ = f₂)   (h₂ : g₁ = g₂) [inst_1…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.hasPullback_symmetry`：hasPullback_symmetry [HasPul
lback f g] : HasPullback g f
· 使用定理 `CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_fst_assoc`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} (f : X ⟶ Z) (g :
 Y ⟶ Z) (f' : W ⟶ X)   [inst_1 : CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.pullbackAssoc_inv_fst_fst`：pullbackAssoc_inv_fst_f
st [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄] [HasPullback f₁ ((pullba
ck.fst _ _ : Z₂ ⟶ X₂) ≫ f₂)] : (pullb…
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_inv_comp_fst`：pullbackSymmetry_in
v_comp_fst [HasPullback f g] : (pullbackSymmetry f g).inv ≫ pullback.fst f g = p
ullback.snd g f
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem diagonalObjPullbackFstIso_inv_fst_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).inv ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      pullback.snd _ _ := by
  delta diagonalObjPullbackFstIso
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.diagonalObjPullbackFstIso_inv_fst_snd** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：diagonalObjPullbackFstIso_inv_fst_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) 
: (diagonalObjPullbackFstIso f g).inv ≫ pullback.fst _ _ ≫ pullback.snd _ _ = pu
llback.fst _ _ ≫ pullback.fst _ _
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.pullback.congrHom_inv`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z} (h₁ : 
f₁ = f₂)   (h₂ : g₁ = g₂) [inst_1…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.hasPullback_symmetry`：hasPullback_symmetry [HasPul
lback f g] : HasPullback g f
· 使用定理 `CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_fst_assoc`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {W X Y Z : C} (f : X ⟶ Z) (g :
 Y ⟶ Z) (f' : W ⟶ X)   [inst_1 : CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.pullbackAssoc_inv_fst_snd`：pullbackAssoc_inv_fst_s
nd [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄] [HasPullback f₁ ((pullba
ck.fst _ _ : Z₂ ⟶ X₂) ≫ f₂)] : (pullb…
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_inv_comp_snd_assoc`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) 
  [inst_1 : CategoryTheory.Limits.HasPullback f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem diagonalObjPullbackFstIso_inv_fst_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).inv ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ := by
  delta diagonalObjPullbackFstIso
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.diagonalObjPullbackFstIso_inv_snd_fst** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：diagonalObjPullbackFstIso_inv_snd_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) 
: (diagonalObjPullbackFstIso f g).inv ≫ pullback.snd _ _ ≫ pullback.fst _ _ = pu
llback.snd _ _
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.pullback.congrHom_inv`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z} (h₁ : 
f₁ = f₂)   (h₂ : g₁ = g₂) [inst_1…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.hasPullback_symmetry`：hasPullback_symmetry [HasPul
lback f g] : HasPullback g f
· 使用定理 `CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_snd_fst`：pullbackR
ightPullbackFstIso_inv_snd_fst : (pullbackRightPullbackFstIso f g f').inv ≫ pull
back.snd _ _ ≫ pullback.fst _ _ = pullback.fst _ _ …
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.pullbackAssoc_inv_fst_fst`：pullbackAssoc_inv_fst_f
st [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄] [HasPullback f₁ ((pullba
ck.fst _ _ : Z₂ ⟶ X₂) ≫ f₂)] : (pullb…
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_inv_comp_fst`：pullbackSymmetry_in
v_comp_fst [HasPullback f g] : (pullbackSymmetry f g).inv ≫ pullback.fst f g = p
ullback.snd g f
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem diagonalObjPullbackFstIso_inv_snd_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).inv ≫ pullback.snd _ _ ≫ pullback.fst _ _ =
      pullback.snd _ _ := by
  delta diagonalObjPullbackFstIso
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.diagonalObjPullbackFstIso_inv_snd_snd** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：diagonalObjPullbackFstIso_inv_snd_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) 
: (diagonalObjPullbackFstIso f g).inv ≫ pullback.snd _ _ ≫ pullback.snd _ _ = pu
llback.fst _ _ ≫ pullback.snd _ _
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.pullback.congrHom_inv`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z} (h₁ : 
f₁ = f₂)   (h₂ : g₁ = g₂) [inst_1…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.hasPullback_symmetry`：hasPullback_symmetry [HasPul
lback f g] : HasPullback g f
· 使用定理 `CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_snd_snd`：pullbackR
ightPullbackFstIso_inv_snd_snd : (pullbackRightPullbackFstIso f g f').inv ≫ pull
back.snd _ _ ≫ pullback.snd _ _ = pullback.snd _ _
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.pullbackAssoc_inv_snd`：pullbackAssoc_inv_snd [HasP
ullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄] [HasPullback f₁ ((pullback.fst _
 _ : Z₂ ⟶ X₂) ≫ f₂)] : (pullbackA…
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_inv_comp_snd_assoc`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) 
  [inst_1 : CategoryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem diagonalObjPullbackFstIso_inv_snd_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).inv ≫ pullback.snd _ _ ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  delta diagonalObjPullbackFstIso
  simp

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.diagonal_pullback_fst** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：diagonal_pullback_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : diagonal (pull
back.fst f g) = (pullbackSymmetry _ _).hom ≫ ((Over.pullback f).map (Over.homMk 
(diagonal g) : Over.mk g ⟶ Over.mk (pullback.snd _ _ ≫ g))).left ≫ (diagonalObjP
ullbackFstIso f g).inv
参数：f : X ⟶ Z；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `CategoryTheory.Limits.hasPullback_symmetry`：hasPullback_symmetry [HasPul
lback f g] : HasPullback g f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_fst`：diagonal_fst : diagonal f ≫
 pullback.fst _ _ = 𝟙 _
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Over.homMk_left`：∀ {T : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} (f : U.left ⟶ V.left) 
  (w : autoParam (Ca…
· 使用定理 `CategoryTheory.Over.pullback_map_left`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.
HasPullbacksAlong f] (g : C…
· 使用定理 `CategoryTheory.Limits.pullback.lift.congr_simp`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1
 : CategoryTheory.Limits.HasPullback…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.diagonalObjPullbackFstIso_inv_fst_fst`：diagonalObj
PullbackFstIso_inv_fst_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : (diagonalObjPul
lbackFstIso f g).inv ≫ pullback.fst _ _ ≫ pullbac…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_hom_comp_snd`：pullbackSymmetry_ho
m_comp_snd [HasPullback f g] : (pullbackSymmetry f g).hom ≫ pullback.snd g f = p
ullback.fst f g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.diagonalObjPullbackFstIso_inv_fst_snd`：diagonalObj
PullbackFstIso_inv_fst_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : (diagonalObjPul
lbackFstIso f g).inv ≫ pullback.fst _ _ ≫ pullbac…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_hom_comp_fst`：pullbackSymmetry_ho
m_comp_fst [HasPullback f g] : (pullbackSymmetry f g).hom ≫ pullback.fst g f = p
ullback.snd f g
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_snd`：diagonal_snd : diagonal f ≫
 pullback.snd _ _ = 𝟙 _
· 使用定理 `CategoryTheory.Limits.diagonalObjPullbackFstIso_inv_snd_fst`：diagonalObj
PullbackFstIso_inv_snd_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : (diagonalObjPul
lbackFstIso f g).inv ≫ pullback.snd _ _ ≫ pullbac…
· 使用定理 `CategoryTheory.Limits.diagonalObjPullbackFstIso_inv_snd_snd`：diagonalObj
PullbackFstIso_inv_snd_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : (diagonalObjPul
lbackFstIso f g).inv ≫ pullback.snd _ _ ≫ pullbac…
-/
theorem diagonal_pullback_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    diagonal (pullback.fst f g) =
      (pullbackSymmetry _ _).hom ≫
        ((Over.pullback f).map
              (Over.homMk (diagonal g) : Over.mk g ⟶ Over.mk (pullback.snd _ _ ≫ g))).left ≫
          (diagonalObjPullbackFstIso f g).inv := by
  ext <;> simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Informally, this is a special case of `pullback_map_diagonal_isPullback` for `T = X`. -/
/-
**CategoryTheory.Limits.pullback_lift_diagonal_isPullback** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Limits`。
形式化陈述：pullback_lift_diagonal_isPullback (g : Y ⟶ X) (f : X ⟶ S) : IsPullback g (
pullback.lift (𝟙 Y) g (by simp)) (diagonal f) (pullback.map (g ≫ f) f f f g (𝟙 X
) (𝟙 S) (by simp) (by simp))
参数：g : Y ⟶ X；f : X ⟶ S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.pullback.congrHom_inv`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z} (h₁ : 
f₁ = f₂)   (h₂ : g₁ = g₂) [inst_1…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.pullback.map_isIso`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S)   [inst_1
 : CategoryTheory.Limits.HasPu…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.IsPullback.of_iso_pullback`：of_iso_pullback (h : CommSq f
st snd f g) [HasPullback f g] (i : P ≅ pullback f g) (w₁ : i.hom ≫ pullback.fst 
_ _ = fst) (w₂ : i.hom ≫ pullba…
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_fst`：diagonal_fst : diagonal f ≫
 pullback.fst _ _ = 𝟙 _
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_snd`：diagonal_snd : diagonal f ≫
 pullback.snd _ _ = 𝟙 _
· 使用定理 `CategoryTheory.Iso.trans_assoc`：trans_assoc {Z' : C} (α : X ≅ Y) (β : Y 
≅ Z) (γ : Z ≅ Z') : (α ≪≫ β) ≪≫ γ = α ≪≫ β ≪≫ γ
· 使用定理 `CategoryTheory.Limits.pullbackDiagonalMapIdIso_inv_fst`：pullbackDiagonal
MapIdIso_inv_fst : (pullbackDiagonalMapIdIso f g i).inv ≫ pullback.fst _ _ = pul
lback.fst _ _ ≫ f
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
· 使用定理 `CategoryTheory.Limits.pullback.map.congr_simp`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S)   [i
nst_1 : CategoryTheory.Limits.HasPu…
· 使用定理 `CategoryTheory.asIso.congr_simp`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f f_1 : X ⟶ Y) (e_f : f = f_1)   [inst_1 : Category
Theory.IsIso f], Cate…
· 使用定理 `CategoryTheory.Limits.pullbackDiagonalMapIdIso_inv_snd_fst`：pullbackDiag
onalMapIdIso_inv_snd_fst : (pullbackDiagonalMapIdIso f g i).inv ≫ pullback.snd _
 _ ≫ pullback.fst _ _ = pullback.fst _ _
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.Limits.pullbackDiagonalMapIdIso_inv_snd_snd`：pullbackDiag
onalMapIdIso_inv_snd_snd : (pullbackDiagonalMapIdIso f g i).inv ≫ pullback.snd _
 _ ≫ pullback.snd _ _ = pullback.snd _ _
· 使用引理 `CategoryTheory.Limits.pullback_inv_fst_snd_of_right_isIso`：pullback_inv_
fst_snd_of_right_isIso : inv (pullback.fst f g) ≫ pullback.snd f g = f ≫ inv g
· 使用定理 `CategoryTheory.IsIso.inv_id`：inv_id : inv (𝟙 X) = 𝟙 X

--- 原说明 ---
Informally, this is a special case of `pullback_map_diagonal_isPullback` for `T 
= X`.
-/
lemma pullback_lift_diagonal_isPullback (g : Y ⟶ X) (f : X ⟶ S) :
    IsPullback g (pullback.lift (𝟙 Y) g (by simp)) (diagonal f)
      (pullback.map (g ≫ f) f f f g (𝟙 X) (𝟙 S) (by simp) (by simp)) := by
  let i : pullback (g ≫ f) f ≅ pullback (g ≫ f) (𝟙 X ≫ f) := congrHom rfl (by simp)
  let e : pullback (diagonal f) (map (g ≫ f) f f f g (𝟙 X) (𝟙 S) (by simp) (by simp)) ≅
      pullback (diagonal f) (map (g ≫ f) (𝟙 X ≫ f) f f g (𝟙 X) (𝟙 S) (by simp) (by simp)) :=
    (asIso (map _ _ _ _ (𝟙 _) i.inv (𝟙 _) (by simp) (by ext <;> simp [i]))).symm
  apply IsPullback.of_iso_pullback _
      (e ≪≫ pullbackDiagonalMapIdIso (T := X) (S := S) g (𝟙 X) f ≪≫ asIso (pullback.fst _ _)).symm
  · simp [e]
  · ext <;> simp [e, i]
  · constructor
    ext <;> simp

end

set_option backward.isDefEq.respectTransparency false in
/-- Given the following diagram with `S ⟶ S'` a monomorphism,

```
    X ⟶ X'
      ↘      ↘
        S ⟶ S'
      ↗      ↗
    Y ⟶ Y'
```

This iso witnesses the fact that

```
      X ×[S] Y ⟶ (X' ×[S'] Y') ×[Y'] Y
          |                  |
          |                  |
          ↓                  ↓
(X' ×[S'] Y') ×[X'] X ⟶ X' ×[S'] Y'
```

is a pullback square. The diagonal map of this square is `pullback.map`.
Also see `pullback_lift_map_is_pullback`.
-/
@[simps]
/-
**CategoryTheory.Limits.pullbackFstFstIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：pullbackFstFstIso {X Y S X' Y' S' : C} (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ 
S') (g' : Y' ⟶ S') (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : S ⟶ S') (e₁ : f ≫ i₃ = i₁ ≫
 f') (e₂ : g ≫ i₃ = i₂ ≫ g') [Mono i₃] : pullback (pullback.fst _ _ : pullback (
pullback.fst _ _ : pullback f' g' ⟶ _) i₁ ⟶ _) (pullback.fst _ _ : pullback (pul
lback.snd _ _ : pullback f' g' ⟶ _) i₂ ⟶ _) ≅ pullback f g where hom
参数：f : X ⟶ S；g : Y ⟶ S；f' : X' ⟶ S'；g' : Y' ⟶ S'；i₁ : X ⟶ X'；i₂ : Y ⟶ Y'；i₃ : S 
⟶ S'；e₁ : f ≫ i₃ = i₁ ≫ f'；e₂ : g ≫ i₃ = i₂ ≫ g'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given the following diagram with `S ⟶ S'` a monomorphism,

```
    X ⟶ X'
      ↘      ↘
        S ⟶ S'
      ↗      ↗
    Y ⟶ Y'
```

This iso witnesses the fact that

```
      X ×[S] Y ⟶ (X' ×[S'] Y') ×[Y'] Y
          |                  |
          |                  |
          ↓                  ↓
(X' ×[S'] Y') ×[X'] X ⟶ X' ×[S'] Y'
```

is a pullback square. The diagonal map of this square is `pullback.map`.
Also see `pullback_lift_map_is_pullback`.
-/
def pullbackFstFstIso {X Y S X' Y' S' : C} (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ S') (g' : Y' ⟶ S')
    (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : S ⟶ S') (e₁ : f ≫ i₃ = i₁ ≫ f') (e₂ : g ≫ i₃ = i₂ ≫ g')
    [Mono i₃] :
    pullback (pullback.fst _ _ : pullback (pullback.fst _ _ : pullback f' g' ⟶ _) i₁ ⟶ _)
        (pullback.fst _ _ : pullback (pullback.snd _ _ : pullback f' g' ⟶ _) i₂ ⟶ _) ≅
      pullback f g where
  hom :=
    pullback.lift (pullback.fst _ _ ≫ pullback.snd _ _) (pullback.snd _ _ ≫ pullback.snd _ _)
      (by
        rw [← cancel_mono i₃, Category.assoc, Category.assoc, Category.assoc, Category.assoc, e₁,
          e₂, ← pullback.condition_assoc, pullback.condition_assoc, pullback.condition,
          pullback.condition_assoc])
  inv :=
    pullback.lift
      (pullback.lift (pullback.map _ _ _ _ _ _ _ e₁ e₂) (pullback.fst _ _) (pullback.lift_fst ..))
      (pullback.lift (pullback.map _ _ _ _ _ _ _ e₁ e₂) (pullback.snd _ _) (pullback.lift_snd ..))
      (by rw [pullback.lift_fst, pullback.lift_fst])
  hom_inv_id := by
    -- We could use `ext` here to immediately descend to the leaf goals,
    -- but it only obscures the structure.
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · apply pullback.hom_ext
        · simp only [Category.assoc, lift_fst, lift_fst_assoc, Category.id_comp]
          rw [condition]
        · simp [Category.assoc, condition]
      · simp only [Category.assoc, lift_snd, lift_fst, Category.id_comp]
    · apply pullback.hom_ext
      · apply pullback.hom_ext
        · simp only [Category.assoc, lift_snd_assoc, lift_fst_assoc, lift_fst, Category.id_comp]
          rw [← condition_assoc, condition]
        · simp only [Category.assoc, lift_snd, lift_fst_assoc, lift_snd_assoc, Category.id_comp]
          rw [condition]
      · simp only [Category.assoc, lift_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, lift_fst, lift_fst_assoc, lift_snd, Category.id_comp]
    · simp only [Category.assoc, lift_snd, lift_snd_assoc, Category.id_comp]
/-
**CategoryTheory.Limits.pullback_map_eq_pullbackFstFstIso_inv** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：pullback_map_eq_pullbackFstFstIso_inv {X Y S X' Y' S' : C} (f : X ⟶ S) (g 
: Y ⟶ S) (f' : X' ⟶ S') (g' : Y' ⟶ S') (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : S ⟶ S')
 (e₁ : f ≫ i₃ = i₁ ≫ f') (e₂ : g ≫ i₃ = i₂ ≫ g') [Mono i₃] : pullback.map f g f'
 g' i₁ i₂ i₃ e₁ e₂ = (pullbackFstFstIso f g f' g' i₁ i₂ i₃ e₁ e₂).inv ≫ pullback
.snd _ _ ≫ pullback.fst _ _
参数：f : X ⟶ S；g : Y ⟶ S；f' : X' ⟶ S'；g' : Y' ⟶ S'；i₁ : X ⟶ X'；i₂ : Y ⟶ Y'；i₃ : S 
⟶ S'；e₁ : f ≫ i₃ = i₁ ≫ f'；e₂ : g ≫ i₃ = i₂ ≫ g'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.pullbackFstFstIso_inv`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasPullbacks
 C]   {X Y S X' Y' S' : C} (f : X…
· 使用定理 `CategoryTheory.Limits.pullback.lift_snd_assoc`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 
: CategoryTheory.Limits.HasPullback…
· 使用定理 `CategoryTheory.Limits.pullback.lift_fst`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullback_map_eq_pullbackFstFstIso_inv {X Y S X' Y' S' : C} (f : X ⟶ S) (g : Y ⟶ S)
    (f' : X' ⟶ S') (g' : Y' ⟶ S') (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : S ⟶ S')
    (e₁ : f ≫ i₃ = i₁ ≫ f') (e₂ : g ≫ i₃ = i₂ ≫ g') [Mono i₃] :
    pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂ =
      (pullbackFstFstIso f g f' g' i₁ i₂ i₃ e₁ e₂).inv ≫ pullback.snd _ _ ≫ pullback.fst _ _ := by
  simp only [pullbackFstFstIso_inv, lift_snd_assoc, lift_fst]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.pullback_lift_map_isPullback** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：pullback_lift_map_isPullback {X Y S X' Y' S' : C} (f : X ⟶ S) (g : Y ⟶ S) 
(f' : X' ⟶ S') (g' : Y' ⟶ S') (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : S ⟶ S') (e₁ : f 
≫ i₃ = i₁ ≫ f') (e₂ : g ≫ i₃ = i₂ ≫ g') [Mono i₃] : IsPullback (pullback.lift (p
ullback.map f g f' g' i₁ i₂ i₃ e₁ e₂) (fst _ _) (lift_fst _ _ _)) (pullback.lift
 (pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂) (snd _ _) (lift_snd _ _ _)) (pullback.f
st _ _) (pullback.fst _ _)
参数：f : X ⟶ S；g : Y ⟶ S；f' : X' ⟶ S'；g' : Y' ⟶ S'；i₁ : X ⟶ X'；i₂ : Y ⟶ Y'；i₃ : S 
⟶ S'；e₁ : f ≫ i₃ = i₁ ≫ f'；e₂ : g ≫ i₃ = i₂ ≫ g'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_iso_pullback`：of_iso_pullback (h : CommSq f
st snd f g) [HasPullback f g] (i : P ≅ pullback f g) (w₁ : i.hom ≫ pullback.fst 
_ _ = fst) (w₂ : i.hom ≫ pullba…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.pullback.lift_fst`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
· 使用定理 `CategoryTheory.Limits.pullback.lift_snd`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.pullbackFstFstIso_inv`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasPullbacks
 C]   {X Y S X' Y' S' : C} (f : X…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullback_lift_map_isPullback {X Y S X' Y' S' : C} (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ S')
    (g' : Y' ⟶ S') (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : S ⟶ S') (e₁ : f ≫ i₃ = i₁ ≫ f')
    (e₂ : g ≫ i₃ = i₂ ≫ g') [Mono i₃] :
    IsPullback (pullback.lift (pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂) (fst _ _) (lift_fst _ _ _))
      (pullback.lift (pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂) (snd _ _) (lift_snd _ _ _))
      (pullback.fst _ _) (pullback.fst _ _) :=
  IsPullback.of_iso_pullback ⟨by rw [lift_fst, lift_fst]⟩
    (pullbackFstFstIso f g f' g' i₁ i₂ i₃ e₁ e₂).symm (by simp) (by simp)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.isPullback_map_snd_snd** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：isPullback_map_snd_snd {X Y Z S : C} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) :
 IsPullback (pullback.map _ _ _ _ (pullback.snd f g) (pullback.snd f h) f pullba
ck.condition pullback.condition) (pullback.fst (pullback.fst f g) (pullback.fst 
f h)) (pullback.fst g h) (pullback.snd f g)
参数：f : X ⟶ S；g : Y ⟶ S；h : Z ⟶ S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition_assoc`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   (t : 
CategoryTheory.Limits.PullbackCone f g) …
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g
· 使用定理 `CategoryTheory.Limits.pullback.lift.congr_simp`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1
 : CategoryTheory.Limits.HasPullback…
-/
lemma isPullback_map_snd_snd {X Y Z S : C} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) :
    IsPullback (pullback.map _ _ _ _ (pullback.snd f g) (pullback.snd f h) f
        pullback.condition pullback.condition)
      (pullback.fst (pullback.fst f g) (pullback.fst f h))
      (pullback.fst g h) (pullback.snd f g) := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro c
    refine pullback.lift c.snd
        (pullback.lift (c.snd ≫ pullback.fst _ _) (c.fst ≫ pullback.snd _ _) ?_) ?_
    · simp [pullback.condition, ← c.condition_assoc]
    · simp
  · intro c
    apply pullback.hom_ext <;> simp [c.condition]
  · intro c
    apply pullback.hom_ext <;> simp
  · intro c m hfst hsnd
    refine pullback.hom_ext (by simpa) ?_
    apply pullback.hom_ext <;> simp [← hsnd, pullback.condition, ← hfst]

end Diagonal

section Codiagonal

namespace pushout

variable {X Y : C} (f : X ⟶ Y) [HasPushout f f]

/-- The codiagonal object of a morphism `f : X ⟶ Y` is `pushout f f`. -/
/-
**CategoryTheory.Limits.pushout.codiagonalObj** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categ
oryTheory.Limits.pushout`。
形式化陈述：codiagonalObj (f : X ⟶ Y) [HasPushout f f] : C
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The codiagonal object of a morphism `f : X ⟶ Y` is `pushout f f`.
-/
noncomputable abbrev codiagonalObj (f : X ⟶ Y) [HasPushout f f] : C :=
  pushout f f

/-- The codiagonal morphism `pushout f f ⟶ Y` for a morphism `f : X ⟶ Y`. -/
/-
**CategoryTheory.Limits.pushout.codiagonal** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.pushout`。
形式化陈述：codiagonal (f : X ⟶ Y) [HasPushout f f] : codiagonalObj f ⟶ Y
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The codiagonal morphism `pushout f f ⟶ Y` for a morphism `f : X ⟶ Y`.
-/
noncomputable def codiagonal (f : X ⟶ Y) [HasPushout f f] : codiagonalObj f ⟶ Y :=
  pushout.desc (𝟙 Y) (𝟙 Y) rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pushout.inl_codiagonal** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits.pushout`。
形式化陈述：inl_codiagonal : pushout.inl _ _ ≫ codiagonal f = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pushout.inl_desc`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPushout …
-/
theorem inl_codiagonal : pushout.inl _ _ ≫ codiagonal f = 𝟙 _ :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pushout.inr_codiagonal** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits.pushout`。
形式化陈述：inr_codiagonal : pushout.inr _ _ ≫ codiagonal f = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pushout.inr_desc`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPushout …
-/
theorem inr_codiagonal : pushout.inr _ _ ≫ codiagonal f = 𝟙 _ :=
  pushout.inr_desc _ _ _

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.pushout.op_codiagonal** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Limits.pushout`。
形式化陈述：op_codiagonal : (pushout.codiagonal f).op = pullback.diagonal f.op ≫ (pull
backIsoOpPushout _ _).hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasPullbackOppositeOpOfHasPushout`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : C} (f : X ⟶ Y) (g : X 
⟶ Z)   [CategoryTheory.Limits.HasPushout f g], Ca…
· 使用定理 `CategoryTheory.Limits.instHasPushoutUnopOfHasPullbackOpposite`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g 
: Y ⟶ Z)   [CategoryTheory.Limits.HasPullback f g],…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.comp_inv_eq`：comp_inv_eq (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : f ≫ α.inv = g ↔ f = g ≫ α.hom
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullbackIsoOpPushout_inv_fst`：pullbackIsoOpPushout
_inv_fst {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] : (pullbackIsoO
pPushout f g).inv ≫ pullback.fst f g = (…
· 使用定理 `CategoryTheory.Limits.pushout.inl_codiagonal`：inl_codiagonal : pushout.i
nl _ _ ≫ codiagonal f = 𝟙 _
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_fst`：diagonal_fst : diagonal f ≫
 pullback.fst _ _ = 𝟙 _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.pullbackIsoOpPushout_inv_snd`：pullbackIsoOpPushout
_inv_snd {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] : (pullbackIsoO
pPushout f g).inv ≫ pullback.snd f g = (…
· 使用定理 `CategoryTheory.Limits.pushout.inr_codiagonal`：inr_codiagonal : pushout.i
nr _ _ ≫ codiagonal f = 𝟙 _
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_snd`：diagonal_snd : diagonal f ≫
 pullback.snd _ _ = 𝟙 _
-/
lemma op_codiagonal :
    (pushout.codiagonal f).op = pullback.diagonal f.op ≫ (pullbackIsoOpPushout _ _).hom := by
  rw [← Iso.comp_inv_eq]
  ext <;> simp [← op_comp]
/-
**CategoryTheory.Limits.pushout.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limit
s.pushout`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSplitEpi (codiagonal f) :=
  ⟨⟨⟨pushout.inl _ _, inl_codiagonal f⟩⟩⟩
/-
**CategoryTheory.Limits.pushout.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limit
s.pushout`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSplitMono (pushout.inl f f) :=
  ⟨⟨⟨codiagonal f, inl_codiagonal f⟩⟩⟩
/-
**CategoryTheory.Limits.pushout.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limit
s.pushout`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSplitMono (pushout.inr f f) :=
  ⟨⟨⟨codiagonal f, inr_codiagonal f⟩⟩⟩
/-
**CategoryTheory.Limits.pushout.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limit
s.pushout`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Epi f] : IsIso (codiagonal f) := by
  rw [(IsIso.inv_eq_of_hom_inv_id (inl_codiagonal f)).symm]
  infer_instance
/-
**CategoryTheory.Limits.pushout.isIso_codiagonal_iff** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Limits.pushout`。
形式化陈述：isIso_codiagonal_iff : IsIso (codiagonal f) ↔ Epi f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.pushout.inl_desc`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPushout …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.pushout.inl_codiagonal`：inl_codiagonal : pushout.i
nl _ _ ≫ codiagonal f = 𝟙 _
· 使用定理 `CategoryTheory.Limits.pushout.inr_codiagonal`：inr_codiagonal : pushout.i
nr _ _ ≫ codiagonal f = 𝟙 _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.pushout.inr_desc`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPushout …
· 使用定理 `CategoryTheory.Limits.pushout.instIsIsoCodiagonalOfEpi`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y)   [inst_1 :
 CategoryTheory.Limits.HasPushout f f] [Cate…
-/
lemma isIso_codiagonal_iff : IsIso (codiagonal f) ↔ Epi f :=
  ⟨fun H ↦ ⟨fun _ _ e ↦ by rw [← inl_desc _ _ e, (cancel_mono (g := inl f f) (h := inr f f)
    (codiagonal f)).mp (by simp), inr_desc]⟩, fun _ ↦ inferInstance⟩

end pushout

variable [HasPushouts C]

set_option backward.isDefEq.respectTransparency false in
/--
Given `f : T ⟶ X`, `g : T ⟶ Y`, and `i : S ⟶ T`, the diagram
```
X ⨿ₛ Y ⟶ X ⨿ₜ Y
  ↑        ↑
  |        |
  |        |
T ⨿ₛ T  ⟶  T
```
is a pushout square.
-/
/-
**CategoryTheory.Limits.isPushout_map_codiagonal** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：isPushout_map_codiagonal {S T : C} (f : T ⟶ X) (g : T ⟶ Y) (i : S ⟶ T) : I
sPushout (pushout.map i i (i ≫ f) (i ≫ g) f g (𝟙 _) (by simp) (by simp)) (pushou
t.codiagonal i) (pushout.map (i ≫ f) (i ≫ g) f g (𝟙 _) (𝟙 _) i (by simp) (by sim
p)) (f ≫ pushout.inl _ _)
参数：f : T ⟶ X；g : T ⟶ Y；i : S ⟶ T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasPushoutComp`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {W X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) (g' : Z ⟶ W)   
[inst_1 : CategoryTheory.Limit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.IsPullback.op_iff`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {X Y Z P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}   {inr
 : Y ⟶ P}, CategoryThe…
· 使用定理 `CategoryTheory.Limits.instHasPushoutUnopOfHasPullbackOpposite`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g 
: Y ⟶ Z)   [CategoryTheory.Limits.HasPullback f g],…
· 使用定理 `CategoryTheory.Limits.instHasPullbackOppositeOpOfHasPushout`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : C} (f : X ⟶ Y) (g : X 
⟶ Z)   [CategoryTheory.Limits.HasPushout f g], Ca…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.Limits.op_pushoutMap`：op_pushoutMap {W X Y Z S T : C} (f₁
 : S ⟶ W) (f₂ : S ⟶ X) [HasPushout f₁ f₂] (g₁ : T ⟶ Y) (g₂ : T ⟶ Z) [HasPushout 
g₁ g₂] (i₁ : W ⟶ Y) (i₂ :…
· 使用引理 `CategoryTheory.Limits.pushout.op_codiagonal`：op_codiagonal : (pushout.co
diagonal f).op = pullback.diagonal f.op ≫ (pullbackIsoOpPushout _ _).hom
· 使用引理 `CategoryTheory.IsPullback.of_iso`：of_iso (h : IsPullback fst snd f g) {P
' X' Y' Z' : C} {fst' : P' ⟶ X'} {snd' : P' ⟶ Y'} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'} 
(e₁ : P ≅ P') (e₂ : X …
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.pullback_map_diagonal_isPullback`：pullback_map_dia
gonal_isPullback : IsPullback (pullback.fst _ _ ≫ f) (pullback.map f g (f ≫ i) (
g ≫ i) _ _ i (Category.id_comp _).symm (Cate…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.pullbackIsoOpPushout_inv_fst_assoc`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : Cᵒᵖ} (f : X ⟶ Z) (g : Y ⟶
 Z)   [inst_1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …

--- 原说明 ---
Given `f : T ⟶ X`, `g : T ⟶ Y`, and `i : S ⟶ T`, the diagram
```
X ⨿ₛ Y ⟶ X ⨿ₜ Y
  ↑        ↑
  |        |
  |        |
T ⨿ₛ T  ⟶  T
```
is a pushout square.
-/
theorem isPushout_map_codiagonal {S T : C} (f : T ⟶ X) (g : T ⟶ Y) (i : S ⟶ T) :
    IsPushout
      (pushout.map i i (i ≫ f) (i ≫ g) f g (𝟙 _) (by simp) (by simp))
      (pushout.codiagonal i)
      (pushout.map (i ≫ f) (i ≫ g) f g (𝟙 _) (𝟙 _) i (by simp) (by simp))
      (f ≫ pushout.inl _ _) := by
  rw [← IsPullback.op_iff]
  simp only [op_pushoutMap, Quiver.Hom.unop_op, op_comp, unop_comp, op_id, pushout.op_codiagonal]
  exact .of_iso (pullback_map_diagonal_isPullback f.op g.op i.op)
    (pullbackIsoOpPushout _ _) (.refl _) (pullbackIsoOpPushout _ _) (pullbackIsoOpPushout _ _)
    (by simp [← Iso.inv_comp_eq]) (by simp) (by simp) (by simp)

end Codiagonal

end CategoryTheory.Limits

