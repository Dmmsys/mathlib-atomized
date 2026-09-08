/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.RepresentationTheory.Rep.Iso
/-!
# Restriction of representations

Given a group homomorphism `f : H →* G`, we have the restriction functor
`resFunctor f : Rep k G ⥤ Rep k H` which sends a `G`-representation `ρ` to the
`H`-representation `ρ.comp f`.

-/

public section

universe t w u v v1 v2

variable {k : Type u} [Semiring k] {G : Type v1} {H : Type v2} [Monoid G] [Monoid H]

open CategoryTheory

namespace Rep

/-- The map induced by a monoid homomorphism `f : H →* G` on morphisms between
`G`-representations. -/
@[expose, implicit_reducible]
/-
**Rep.resMap** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：resMap {X Y : Rep k G} (f : H ->* G) (p : X ⟶ Y) : of (X
参数：f : H ->* G；p : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map induced by a monoid homomorphism `f : H →* G` on morphisms between
`G`-representations.
-/
def resMap {X Y : Rep k G} (f : H →* G) (p : X ⟶ Y) :
    of (X := X.V) (X.ρ.comp f) ⟶ of (X := Y.V) (Y.ρ.comp f) :=
  ofHom ⟨p.hom, fun h ↦ by simpa using p.hom.2 (f h)⟩

/-- The restriction functor `Rep R G ⥤ Rep R H` for a subgroup `H` of `G`. -/
/-
**Rep.resFunctor** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：resFunctor (f : H ->* G) : Rep.{t} k G ⥤ Rep k H where obj A
参数：f : H ->* G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction functor `Rep R G ⥤ Rep R H` for a subgroup `H` of `G`.
-/
abbrev resFunctor (f : H →* G) : Rep.{t} k G ⥤ Rep k H where
  obj A := of (X := A.V) (A.ρ.comp f)
  map f' := resMap f f'

/-- The restriction of `X : Rep k G` associated to a monoid homomorphism `f : H →* G` -/
/-
**Rep.res** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：res (f : H ->* G) (M : Rep k G)
参数：f : H ->* G；M : Rep k G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of `X : Rep k G` associated to a monoid homomorphism `f : H →* G
`
-/
abbrev res (f : H →* G) (M : Rep k G) := (resFunctor f).obj M

variable (f : H →* G) (M : Rep k G)
/-
**Rep.res_id** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：res_id : res (MonoidHom.id G) M = M
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma res_id : res (MonoidHom.id G) M = M := rfl
/-
**Rep.res_obj_** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma res_obj_ρ : (res f M).ρ = (M.ρ.comp f) := rfl
/-
**Rep.coe_res_obj_** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_res_obj_ρ' (h : H) : (res f M).ρ h = M.ρ (f h) := rfl
/-
**Rep.res_obj_V** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：res_obj_V : (res f M).V = M.V
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma res_obj_V : (res f M).V = M.V := rfl

@[simp]
/-
**Rep.resMap_hom_toLinearMap** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：resMap_hom_toLinearMap {M N : Rep k G} (p : M ⟶ N) : (resMap f p).hom.toLi
nearMap = p.hom.toLinearMap
参数：p : M ⟶ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma resMap_hom_toLinearMap {M N : Rep k G} (p : M ⟶ N) :
    (resMap f p).hom.toLinearMap = p.hom.toLinearMap := rfl

@[deprecated (since := "2026-06-26")]
alias res_map_hom_toLinearMap := resMap_hom_toLinearMap

@[simp]
/-
**Rep.resMap_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：resMap_hom_apply {M N : Rep k G} (p : M ⟶ N) (x : M.V) : @DFunLike.coe (Re
presentation.IntertwiningMap (M.ρ.comp f) (N.ρ.comp f)) _ _ _ (resMap f p).hom x
 = p.hom x
参数：p : M ⟶ N；x : M.V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma resMap_hom_apply {M N : Rep k G} (p : M ⟶ N) (x : M.V) :
    @DFunLike.coe (Representation.IntertwiningMap (M.ρ.comp f) (N.ρ.comp f)) _ _ _
      (resMap f p).hom x = p.hom x := rfl

section

/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (resFunctor (k := k) f).Faithful where
  map_injective h := by
    simpa [Rep.hom_ext_iff, Representation.IntertwiningMap.ext_iff] using h

/-- Morphism between `X Y : Rep k G` can be lifted from restrictions associated with `f : H →* G`
  when `f` is surjective. -/
/-
**Rep.liftHomOfSurj** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：liftHomOfSurj {X Y : Rep k G} (hf : Function.Surjective f) (f' : res f X ⟶
 res f Y) : X ⟶ Y
参数：hf : Function.Surjective f；f' : res f X ⟶ res f Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Morphism between `X Y : Rep k G` can be lifted from restrictions associated with
 `f : H →* G`
  when `f` is surjective.
-/
abbrev liftHomOfSurj {X Y : Rep k G} (hf : Function.Surjective f) (f' : res f X ⟶ res f Y) :
    X ⟶ Y := ofHom ⟨f'.hom.toLinearMap, fun g ↦ by obtain ⟨h, rfl⟩ := hf g; simpa using f'.hom.2 h⟩

@[simp]
/-
**Rep.liftHomOfSurj_toLinearMap** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：liftHomOfSurj_toLinearMap {X Y : Rep k G} (hf : Function.Surjective f) (f'
 : res f X ⟶ res f Y) : (liftHomOfSurj f hf f').hom.toLinearMap = f'.hom.toLinea
rMap
参数：hf : Function.Surjective f；f' : res f X ⟶ res f Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma liftHomOfSurj_toLinearMap {X Y : Rep k G} (hf : Function.Surjective f)
    (f' : res f X ⟶ res f Y) : (liftHomOfSurj f hf f').hom.toLinearMap =
      f'.hom.toLinearMap := rfl
/-
**Rep.full_res** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：full_res (hf : (⇑f).Surjective) : (resFunctor (k
参数：hf : (⇑f).Surjective。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rep.hom_ext`：∀ {k : Type u} {G : Type v} [inst : Semiring k] [inst_1 : M
onoid G] {A B : Rep.{w, u, v} k G} {f g : A ⟶ B},   Rep.Hom.hom f = Rep.Hom.hom 
g…
· 使用引理 `Representation.IntertwiningMap.ext`：ext {f g : IntertwiningMap ρ σ} (h :
 f.toLinearMap = g.toLinearMap) : f = g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma full_res (hf : (⇑f).Surjective) : (resFunctor (k := k) f).Full where
  map_surjective {X Y} f' := ⟨liftHomOfSurj f hf f', by ext; simp⟩
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (resFunctor (k := k) f).Additive where
  map_add {_ _} _ _ := by ext : 2; simp [add_hom]
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {k : Type u} [CommSemiring k] : (resFunctor (k := k) f).Linear k where
  map_smul {_ _} _ _ := by ext : 2; simp [smul_hom]

section ShortComplex

open Limits

variable {k : Type u} [Ring k]

/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesLimits (resFunctor.{w} (k := k) f) :=
  have : PreservesLimitsOfSize.{w, w} (resFunctor f ⋙ forget₂ (Rep.{w} k H) (ModuleCat k)) :=
    inferInstanceAs (PreservesLimitsOfSize.{w, w} (forget₂ (Rep.{w} k G) (ModuleCat k)))
  preservesLimits_of_reflects_of_preserves _ (forget₂ (Rep.{w} k H) (ModuleCat k))
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Limits.PreservesColimits (resFunctor.{w} (k := k) f) :=
  have : PreservesColimitsOfSize.{w, w} (resFunctor (k := k) f ⋙
      forget₂ (Rep.{w} k H) (ModuleCat k)) :=
    inferInstanceAs (PreservesColimitsOfSize.{w, w} (forget₂ (Rep.{w} k G) (ModuleCat k)))
  preservesColimits_of_reflects_of_preserves _ (forget₂ (Rep.{w} k H) (ModuleCat k))

/-- An object of `Rep k G` is zero iff its restriction to `H` is zero. -/
/-
**Rep.isZero_res_iff** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：isZero_res_iff (M : Rep k G) : IsZero (res f M) ↔ IsZero M
参数：M : Rep k G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Rep.isZero_iff`：isZero_iff (M : Rep k G) : Limits.IsZero M ↔ Subsingleto
n M.V
· 使用引理 `Rep.res_obj_V`：res_obj_V : (res f M).V = M.V
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
An object of `Rep k G` is zero iff its restriction to `H` is zero.
-/
lemma isZero_res_iff (M : Rep k G) :
    IsZero (res f M) ↔ IsZero M := by
  rw [isZero_iff, isZero_iff, Rep.res_obj_V]

/--
The instances above show that the restriction functor `res φ : Rep R G ⥤ Rep R H`
preserves and reflects exactness. -/
/-
**Rep.res_map_exact** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：res_map_exact {k : Type u} [CommRing k] (S : ShortComplex (Rep.{w} k G)) :
 (S.map (resFunctor f)).Exact ↔ S.Exact
参数：S : ShortComplex (Rep.{w} k G)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `Rep.instAdditiveResFunctor`：∀ {k : Type u} [inst : Semiring k] {G : Type
 v1} {H : Type v2} [inst_1 : Monoid G] [inst_2 : Monoid H] (f : H →* G),   (Rep.
resFunctor f).Ad…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.exact_map_iff_of_faithful`：exact_map_iff_of_
faithful [S.HasHomology] (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.PreservesLeft
HomologyOf S] [F.PreservesRightHomologyOf S…
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesLeftHomologyOf`：∀ {C :
 Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.preservesHomologyOfExact`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `Rep.instPreservesLimitsResFunctor`：∀ {G : Type v1} {H : Type v2} [inst :
 Monoid G] [inst_1 : Monoid H] (f : H →* G) {k : Type u} [inst_2 : Ring k],   Ca
tegoryTheory.Limits.Pre…
· 使用定理 `CategoryTheory.Limits.PreservesColimits.preservesFiniteColimits`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `Rep.instPreservesColimitsResFunctor`：∀ {G : Type v1} {H : Type v2} [inst
 : Monoid G] [inst_1 : Monoid H] (f : H →* G) {k : Type u} [inst_2 : Ring k],   
CategoryTheory.Limits.Pre…
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesRightHomologyOf`：∀ {C 
: Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `Rep.instFaithfulResFunctor`：∀ {k : Type u} [inst : Semiring k] {G : Type
 v1} {H : Type v2} [inst_1 : Monoid G] [inst_2 : Monoid H] (f : H →* G),   (Rep.
resFunctor f).Fa…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The instances above show that the restriction functor `res φ : Rep R G ⥤ Rep R H
`
preserves and reflects exactness.
-/
lemma res_map_exact {k : Type u} [CommRing k]
    (S : ShortComplex (Rep.{w} k G)) :
    (S.map (resFunctor f)).Exact ↔ S.Exact := by
  rw [ShortComplex.exact_map_iff_of_faithful]

set_option backward.isDefEq.respectTransparency.types false in
/-
**Rep.shortExact_res** 是 Mathlib 中的一个引理，位于命名空间 `Rep`。
形式化陈述：shortExact_res {k : Type u} [CommRing k] (φ : H ->* G) {S : ShortComplex (
Rep.{w} k G)} : (S.map (resFunctor φ)).ShortExact ↔ S.ShortExact
参数：φ : H ->* G；Rep.{w} k G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `Rep.instAdditiveResFunctor`：∀ {k : Type u} [inst : Semiring k] {G : Type
 v1} {H : Type v2} [inst_1 : Monoid G] [inst_2 : Monoid H] (f : H →* G),   (Rep.
resFunctor f).Ad…
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.exact`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.mono_f`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.epi_g`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {S : CategoryTheory.Sho…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.exact_map_iff_of_faithful`：exact_map_iff_of_
faithful [S.HasHomology] (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.PreservesLeft
HomologyOf S] [F.PreservesRightHomologyOf S…
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesLeftHomologyOf`：∀ {C :
 Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.preservesHomologyOfExact`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `Rep.instPreservesLimitsResFunctor`：∀ {G : Type v1} {H : Type v2} [inst :
 Monoid G] [inst_1 : Monoid H] (f : H →* G) {k : Type u} [inst_2 : Ring k],   Ca
tegoryTheory.Limits.Pre…
· 使用定理 `CategoryTheory.Limits.PreservesColimits.preservesFiniteColimits`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `Rep.instPreservesColimitsResFunctor`：∀ {G : Type v1} {H : Type v2} [inst
 : Monoid G] [inst_1 : Monoid H] (f : H →* G) {k : Type u} [inst_2 : Ring k],   
CategoryTheory.Limits.Pre…
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesRightHomologyOf`：∀ {C 
: Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `Rep.instFaithfulResFunctor`：∀ {k : Type u} [inst : Semiring k] {G : Type
 v1} {H : Type v2} [inst_1 : Monoid G] [inst_2 : Monoid H] (f : H →* G),   (Rep.
resFunctor f).Fa…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Rep.mono_iff_injective`：mono_iff_injective (f : A ⟶ B) : Mono f ↔ Functi
on.Injective f.hom
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.ShortComplex.map_f`：∀ {C : Type u_1} {D : Type u_2} [inst
 : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_
2, u_2} D] [inst_2 : Ca…
· 使用定理 `Rep.epi_iff_surjective`：epi_iff_surjective (f : A ⟶ B) : Epi f ↔ Functio
n.Surjective f.hom
· 使用定理 `CategoryTheory.ShortComplex.map_g`：∀ {C : Type u_1} {D : Type u_2} [inst
 : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_
2, u_2} D] [inst_2 : Ca…
-/
lemma shortExact_res {k : Type u} [CommRing k] (φ : H →* G) {S : ShortComplex (Rep.{w} k G)} :
    (S.map (resFunctor φ)).ShortExact ↔ S.ShortExact := by
  constructor
  · intro h
    have h₁ := h.1
    have h₂ := h.2
    have h₃ := h.3
    rw [ShortComplex.exact_map_iff_of_faithful] at h₁
    simp only [ShortComplex.map_f, mono_iff_injective, ShortComplex.map_g,
      epi_iff_surjective] at h₂ h₃
    exact {exact := h₁, mono_f := mono_iff_injective _|>.2 h₂, epi_g := epi_iff_surjective _|>.2 h₃}
  · rintro @⟨_, mono_f, epi_g⟩
    exact {
      exact := by rwa [ShortComplex.exact_map_iff_of_faithful]
      mono_f := by simpa [mono_iff_injective] using! mono_f
      epi_g := by simpa [epi_iff_surjective] using! epi_g
    }

end ShortComplex

noncomputable section

variable {G : Type v} [Group G] (A : Rep k G) (S : Subgroup G)
  [S.Normal] [Representation.IsTrivial (A.ρ.comp S.subtype)]

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` which is trivial on `S` factors
through `G ⧸ S`. -/
/-
**Rep.ofQuotient** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：ofQuotient : Rep k (G ⧸ S)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` which is trivial on `S
` factors
through `G ⧸ S`.
-/
abbrev ofQuotient : Rep k (G ⧸ S) := Rep.of (A.ρ.ofQuotient S)

/-- A `G`-representation `A` on which a normal subgroup `S ≤ G` acts trivially induces a
`G ⧸ S`-representation on `A`, and composing this with the quotient map `G → G ⧸ S` gives the
original representation by definition. Useful for typechecking. -/
/-
**Rep.resOfQuotientIso** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：resOfQuotientIso : (res (QuotientGroup.mk' S) (A.ofQuotient S)) ≅ A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `G`-representation `A` on which a normal subgroup `S ≤ G` acts trivially induc
es a
`G ⧸ S`-representation on `A`, and composing this with the quotient map `G → G ⧸
 S` gives the
original representation by definition. Useful for typechecking.
-/
abbrev resOfQuotientIso : (res (QuotientGroup.mk' S) (A.ofQuotient S)) ≅ A := Iso.refl _

end

end

end Rep

