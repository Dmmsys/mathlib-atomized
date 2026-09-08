/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.CategoryTheory.Sites.CompatibleSheafification
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.ShrinkYoneda
/-!

# Locally surjective morphisms

## Main definitions

- `IsLocallySurjective` : A morphism of presheaves valued in a concrete category is locally
  surjective with respect to a Grothendieck topology if every section in the target is locally
  in the set-theoretic image, i.e. the image sheaf coincides with the target.

## Main results

- `Presheaf.isLocallySurjective_toSheafify`: `toSheafify` is locally surjective.
- `Sheaf.isLocallySurjective_iff_epi`: a morphism of sheaves of types is locally
  surjective iff it is epi.

-/

@[expose] public section


universe w v u v' u' w'

open Opposite CategoryTheory CategoryTheory.GrothendieckTopology CategoryTheory.Functor Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

variable {A : Type u'} [Category.{v'} A] {FA : A → A → Type*} {CA : A → Type w'}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w'} A FA]

namespace Presheaf

/-- Given `f : F ⟶ G`, a morphism between presieves, and `s : G.obj (op U)`, this is the sieve
of `U` consisting of the `i : V ⟶ U` such that `s` restricted along `i` is in the image of `f`. -/
@[simps -isSimp]
/-
**CategoryTheory.Presheaf.imageSieve** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.P
resheaf`。
形式化陈述：imageSieve {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : C} (s : ToType (G.obj (op U)))
 : Sieve U where arrows V i
参数：f : F ⟶ G；s : ToType (G.obj (op U))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `f : F ⟶ G`, a morphism between presieves, and `s : G.obj (op U)`, this is
 the sieve
of `U` consisting of the `i : V ⟶ U` such that `s` restricted along `i` is in th
e image of `f`.
-/
def imageSieve {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : C} (s : ToType (G.obj (op U))) : Sieve U where
  arrows V i := ∃ t : ToType (F.obj (op V)), f.app _ t = G.map i.op s
  downward_closed := by
    rintro V W i ⟨t, ht⟩ j
    refine ⟨F.map j.op t, ?_⟩
    rw [op_comp, G.map_comp, ConcreteCategory.comp_apply, ← ht, NatTrans.naturality_apply f]
/-
**CategoryTheory.Presheaf.pullback_imageSieve** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Presheaf`。
形式化陈述：pullback_imageSieve {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : C} (s : ToType (G.obj
 (op U))) {V : C} (g : V ⟶ U) : (imageSieve f s).pullback g = imageSieve f (G.ma
p g.op s)
参数：f : F ⟶ G；s : ToType (G.obj (op U))；g : V ⟶ U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.ext`：∀ {C : Type u₁} [inst : CategoryTheory.Categor
y.{v₁, u₁} C] {X : C} {R S : CategoryTheory.Sieve X},   (∀ ⦃Y : C⦄ (f : Y ⟶ X), 
R.arrows f ↔ S…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Sieve.pullback_apply`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {X Y : C} (h : Y ⟶ X) (S : CategoryTheory.Sieve X) (x :
 C)   (sl : x ⟶ Y), (Cate…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma pullback_imageSieve
    {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : C} (s : ToType (G.obj (op U)))
    {V : C} (g : V ⟶ U) :
    (imageSieve f s).pullback g = imageSieve f (G.map g.op s) := by
  ext W g
  simp [imageSieve]
/-
**CategoryTheory.Presheaf.imageSieve_eq_sieveOfSection** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Presheaf`。
形式化陈述：imageSieve_eq_sieveOfSection {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : C} (s : ToTy
pe (G.obj (op U))) : imageSieve f s = (Subfunctor.range (whiskerRight f (forget 
A))).sieveOfSection s
参数：f : F ⟶ G；s : ToType (G.obj (op U))。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imageSieve_eq_sieveOfSection {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : C}
    (s : ToType (G.obj (op U))) :
    imageSieve f s = (Subfunctor.range (whiskerRight f (forget A))).sieveOfSection s :=
  rfl
/-
**CategoryTheory.Presheaf.imageSieve_whisker_forget** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Presheaf`。
形式化陈述：imageSieve_whisker_forget {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : C} (s : ToType 
(G.obj (op U))) : imageSieve (whiskerRight f (forget A)) s = imageSieve f s
参数：f : F ⟶ G；s : ToType (G.obj (op U))。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem imageSieve_whisker_forget {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : C} (s : ToType (G.obj (op U))) :
    imageSieve (whiskerRight f (forget A)) s = imageSieve f s :=
  rfl
/-
**CategoryTheory.Presheaf.imageSieve_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Presheaf`。
形式化陈述：imageSieve_app {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : C} (s : ToType (F.obj (op 
U))) : imageSieve f (f.app _ s) = ⊤
参数：f : F ⟶ G；s : ToType (F.obj (op U))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.ext`：∀ {C : Type u₁} [inst : CategoryTheory.Categor
y.{v₁, u₁} C] {X : C} {R S : CategoryTheory.Sieve X},   (∀ ⦃Y : C⦄ (f : Y ⟶ X), 
R.arrows f ↔ S…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presheaf.imageSieve_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {A : Type u'} [inst_1 : CategoryTheory.Category.{v', 
u'} A]   {FA : A → A → Type u_…
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `CategoryTheory.NatTrans.naturality_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1
, u_1} D]   {FD : outParam (D …
-/
theorem imageSieve_app {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : C} (s : ToType (F.obj (op U))) :
    imageSieve f (f.app _ s) = ⊤ := by
  ext V i
  simp only [Sieve.top_apply, iff_true, imageSieve_apply]
  exact ⟨F.map i.op s, NatTrans.naturality_apply f i.op s⟩

/-- If a morphism `g : V ⟶ U.unop` belongs to the sieve `imageSieve f s g`, then
this is choice of a preimage of `G.map g.op s` in `F.obj (op V)`, see
`app_localPreimage`. -/
/-
**CategoryTheory.Presheaf.localPreimage** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Presheaf`。
形式化陈述：localPreimage {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : Cᵒᵖ} (s : ToType (G.obj U))
 {V : C} (g : V ⟶ U.unop) (hg : imageSieve f s g) : ToType (F.obj (op V))
参数：f : F ⟶ G；s : ToType (G.obj U)；g : V ⟶ U.unop；hg : imageSieve f s g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a morphism `g : V ⟶ U.unop` belongs to the sieve `imageSieve f s g`, then
this is choice of a preimage of `G.map g.op s` in `F.obj (op V)`, see
`app_localPreimage`.
-/
noncomputable def localPreimage {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : Cᵒᵖ} (s : ToType (G.obj U))
    {V : C} (g : V ⟶ U.unop) (hg : imageSieve f s g) :
    ToType (F.obj (op V)) :=
  hg.choose

@[simp]
/-
**CategoryTheory.Presheaf.app_localPreimage** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Presheaf`。
形式化陈述：app_localPreimage {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : Cᵒᵖ} (s : ToType (G.obj
 U)) {V : C} (g : V ⟶ U.unop) (hg : imageSieve f s g) : f.app _ (localPreimage f
 s g hg) = G.map g.op s
参数：f : F ⟶ G；s : ToType (G.obj U)；g : V ⟶ U.unop；hg : imageSieve f s g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma app_localPreimage {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : Cᵒᵖ} (s : ToType (G.obj U))
    {V : C} (g : V ⟶ U.unop) (hg : imageSieve f s g) :
    f.app _ (localPreimage f s g hg) = G.map g.op s :=
  hg.choose_spec

/-- A morphism of presheaves `f : F ⟶ G` is locally surjective with respect to a Grothendieck
topology if every section of `G` is locally in the image of `f`. -/
/-
**CategoryTheory.Presheaf.IsLocallySurjective** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categ
oryTheory.Presheaf`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     CategoryT
heory.GrothendieckTopology C →       {A : Type u'} →         [inst_1 : CategoryT
heory.Category.{v', u'} A] →           {FA : A → A → Type u_1} →             {CA
 : A → Type w'} →               [inst_2 : (X Y : A) → FunLike (FA X Y) (CA X) (C
A Y)] →                 [CategoryTheory.ConcreteCategory A FA] → {F G : Category
Theory.Functor Cᵒᵖ A} → (F ⟶ G) → Prop
参数：X Y : A；FA X Y；CA X；CA Y；F ⟶ G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of presheaves `f : F ⟶ G` is locally surjective with respect to a Gro
thendieck
topology if every section of `G` is locally in the image of `f`.
-/
class IsLocallySurjective {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) : Prop where
  imageSieve_mem {U : C} (s : ToType (G.obj (op U))) : imageSieve f s ∈ J U
/-
**CategoryTheory.Presheaf.imageSieve_mem** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Presheaf`。
形式化陈述：imageSieve_mem {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) [IsLocallySurjective J f] {U : 
Cᵒᵖ} (s : ToType (G.obj U)) : imageSieve f s in J U.unop
参数：f : F ⟶ G；s : ToType (G.obj U)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presheaf.IsLocallySurjective.imageSieve_mem`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {J : CategoryTheory.GrothendieckTop
ology C} {A : Type u'}   {inst_1 : CategoryTheor…
-/
lemma imageSieve_mem {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) [IsLocallySurjective J f] {U : Cᵒᵖ}
    (s : ToType (G.obj U)) : imageSieve f s ∈ J U.unop :=
  IsLocallySurjective.imageSieve_mem _
/-
**CategoryTheory.Presheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Presheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) [IsLocallySurjective J f] :
    IsLocallySurjective J (whiskerRight f (forget A)) where
  imageSieve_mem s := imageSieve_mem J f s
/-
**CategoryTheory.Presheaf.isLocallySurjective_iff_range_sheafify_eq_top** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：isLocallySurjective_iff_range_sheafify_eq_top {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) 
: IsLocallySurjective J f ↔ (Subfunctor.range (whiskerRight f (forget A))).sheaf
ify J = ⊤
参数：f : F ⟶ G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `CategoryTheory.Presheaf.IsLocallySurjective.imageSieve_mem`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {J : CategoryTheory.GrothendieckTop
ology C} {A : Type u'}   {inst_1 : CategoryTheor…
-/
theorem isLocallySurjective_iff_range_sheafify_eq_top {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) :
    IsLocallySurjective J f ↔ (Subfunctor.range (whiskerRight f (forget A))).sheafify J = ⊤ := by
  simp only [Subfunctor.ext_iff, funext_iff, Set.ext_iff, Subfunctor.top_obj,
    Set.top_eq_univ, Set.mem_univ, iff_true]
  exact ⟨fun H _ => H.imageSieve_mem, fun H => ⟨H _⟩⟩
/-
**CategoryTheory.Presheaf.isLocallySurjective_iff_range_sheafify_eq_top'** 是 Mat
hlib 中的一个定理，位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：isLocallySurjective_iff_range_sheafify_eq_top' {F G : Cᵒᵖ ⥤ Type w} (f : F
 ⟶ G) : IsLocallySurjective J f ↔ (Subfunctor.range f).sheafify J = ⊤
参数：f : F ⟶ G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presheaf.isLocallySurjective_iff_range_sheafify_eq_top`：i
sLocallySurjective_iff_range_sheafify_eq_top {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) : IsLoc
allySurjective J f ↔ (Subfunctor.range (whiskerRight f (for…
-/
theorem isLocallySurjective_iff_range_sheafify_eq_top' {F G : Cᵒᵖ ⥤ Type w} (f : F ⟶ G) :
    IsLocallySurjective J f ↔ (Subfunctor.range f).sheafify J = ⊤ := by
  apply isLocallySurjective_iff_range_sheafify_eq_top
/-
**CategoryTheory.Presheaf.isLocallySurjective_iff_whisker_forget** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：isLocallySurjective_iff_whisker_forget {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) : IsLoc
allySurjective J f ↔ IsLocallySurjective J (whiskerRight f (forget A))
参数：f : F ⟶ G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isLocallySurjective_iff_whisker_forget {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) :
    IsLocallySurjective J f ↔ IsLocallySurjective J (whiskerRight f (forget A)) := by
  simp only [isLocallySurjective_iff_range_sheafify_eq_top]
  rfl
/-
**CategoryTheory.Presheaf.isLocallySurjective_of_surjective** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：isLocallySurjective_of_surjective {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) (H : forall 
U, Function.Surjective (f.app U)) : IsLocallySurjective J f where imageSieve_mem
 {U} s
参数：f : F ⟶ G；H : forall U, Function.Surjective (f.app U)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presheaf.imageSieve_app`：imageSieve_app {F G : Cᵒᵖ ⥤ A} (
f : F ⟶ G) {U : C} (s : ToType (F.obj (op U))) : imageSieve f (f.app _ s) = ⊤
· 使用定理 `CategoryTheory.GrothendieckTopology.top_mem`：top_mem (X : C) : ⊤ in J X
-/
theorem isLocallySurjective_of_surjective {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G)
    (H : ∀ U, Function.Surjective (f.app U)) : IsLocallySurjective J f where
  imageSieve_mem {U} s := by
    obtain ⟨t, rfl⟩ := H _ s
    rw [imageSieve_app]
    exact J.top_mem _
/-
**CategoryTheory.Presheaf.isLocallySurjective_of_iso** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.Presheaf`。
形式化陈述：isLocallySurjective_of_iso {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) [IsIso f] : IsLocal
lySurjective J f
参数：f : F ⟶ G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presheaf.isLocallySurjective_of_surjective`：isLocallySurj
ective_of_surjective {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) (H : forall U, Function.Surject
ive (f.app U)) : IsLocallySurjective J f where …
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.bijective_iff_isIso_ofHom`：bijective_iff_isIso_ofHom {X Y
 : Type u} (f : X -> Y) : Function.Bijective f ↔ IsIso (ofHom f)
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
-/
instance isLocallySurjective_of_iso {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) [IsIso f] :
    IsLocallySurjective J f := by
  apply isLocallySurjective_of_surjective
  intro U
  apply Function.Bijective.surjective
  rw [bijective_iff_isIso_ofHom]
  infer_instance
/-
**CategoryTheory.Presheaf.isLocallySurjective_comp** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.Presheaf`。
形式化陈述：isLocallySurjective_comp {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃
) [IsLocallySurjective J f₁] [IsLocallySurjective J f₂] : IsLocallySurjective J 
(f₁ ≫ f₂) where imageSieve_mem s
参数：f₁ : F₁ ⟶ F₂；f₂ : F₂ ⟶ F₃。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.NatTrans.comp_app`：comp_app {F G H : C ⥤ D} (α : F ⟶ G) (
β : G ⟶ H) (X : C) : (α ≫ β).app X = α.app X ≫ β.app X
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
· 使用定理 `CategoryTheory.NatTrans.naturality_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1
, u_1} D]   {FD : outParam (D …
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `CategoryTheory.GrothendieckTopology.superset_covering`：superset_covering
 (Hss : S <= R) (sjx : S in J X) : R in J X
· 使用定理 `CategoryTheory.GrothendieckTopology.bind_covering`：bind_covering {S : Si
eve X} {R : forall ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f -> Sieve Y} (hS : S in J X) (hR : fo
rall ⦃Y⦄ ⦃f : Y ⟶ X⦄ (H : S f), R H in …
· 使用引理 `CategoryTheory.Presheaf.imageSieve_mem`：imageSieve_mem {F G : Cᵒᵖ ⥤ A} (
f : F ⟶ G) [IsLocallySurjective J f] {U : Cᵒᵖ} (s : ToType (G.obj U)) : imageSie
ve f s in J U.unop
-/
instance isLocallySurjective_comp {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃)
    [IsLocallySurjective J f₁] [IsLocallySurjective J f₂] :
    IsLocallySurjective J (f₁ ≫ f₂) where
  imageSieve_mem s := by
    have : (Sieve.bind (imageSieve f₂ s) fun _ _ h => imageSieve f₁ h.choose) ≤
        imageSieve (f₁ ≫ f₂) s := by
      rintro V i ⟨W, i, j, H, ⟨t', ht'⟩, rfl⟩
      refine ⟨t', ?_⟩
      rw [op_comp, F₃.map_comp, NatTrans.comp_app, ConcreteCategory.comp_apply,
        ConcreteCategory.comp_apply, ht', NatTrans.naturality_apply, H.choose_spec]
    apply J.superset_covering this
    apply J.bind_covering
    · apply imageSieve_mem
    · intros; apply imageSieve_mem
/-
**CategoryTheory.Presheaf.isLocallySurjective_of_isLocallySurjective** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：isLocallySurjective_of_isLocallySurjective {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶
 F₂) (f₂ : F₂ ⟶ F₃) [IsLocallySurjective J (f₁ ≫ f₂)] : IsLocallySurjective J f₂
 where imageSieve_mem {X} x
参数：f₁ : F₁ ⟶ F₂；f₂ : F₂ ⟶ F₃；f₁ ≫ f₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.superset_covering`：superset_covering
 (Hss : S <= R) (sjx : S in J X) : R in J X
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用引理 `CategoryTheory.Presheaf.app_localPreimage`：app_localPreimage {F G : Cᵒᵖ 
⥤ A} (f : F ⟶ G) {U : Cᵒᵖ} (s : ToType (G.obj U)) {V : C} (g : V ⟶ U.unop) (hg :
 imageSieve f s g) : f.app _ (l…
· 使用引理 `CategoryTheory.Presheaf.imageSieve_mem`：imageSieve_mem {F G : Cᵒᵖ ⥤ A} (
f : F ⟶ G) [IsLocallySurjective J f] {U : Cᵒᵖ} (s : ToType (G.obj U)) : imageSie
ve f s in J U.unop
-/
lemma isLocallySurjective_of_isLocallySurjective
    {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃)
    [IsLocallySurjective J (f₁ ≫ f₂)] :
    IsLocallySurjective J f₂ where
  imageSieve_mem {X} x := by
    refine J.superset_covering ?_ (imageSieve_mem J (f₁ ≫ f₂) x)
    intro Y g hg
    exact ⟨f₁.app _ (localPreimage (f₁ ≫ f₂) x g hg),
      by simpa using app_localPreimage (f₁ ≫ f₂) x g hg⟩
/-
**CategoryTheory.Presheaf.isLocallySurjective_of_isLocallySurjective_fac** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：isLocallySurjective_of_isLocallySurjective_fac {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} {f₁ : 
F₁ ⟶ F₂} {f₂ : F₂ ⟶ F₃} {f₃ : F₁ ⟶ F₃} (fac : f₁ ≫ f₂ = f₃) [IsLocallySurjective
 J f₃] : IsLocallySurjective J f₂
参数：fac : f₁ ≫ f₂ = f₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Presheaf.isLocallySurjective_of_isLocallySurjective`：isLo
callySurjective_of_isLocallySurjective {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ :
 F₂ ⟶ F₃) [IsLocallySurjective J (f₁ ≫ f₂)] : IsLocallyS…
-/
lemma isLocallySurjective_of_isLocallySurjective_fac
    {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} {f₁ : F₁ ⟶ F₂} {f₂ : F₂ ⟶ F₃} {f₃ : F₁ ⟶ F₃} (fac : f₁ ≫ f₂ = f₃)
    [IsLocallySurjective J f₃] : IsLocallySurjective J f₂ := by
  subst fac
  exact isLocallySurjective_of_isLocallySurjective J f₁ f₂
/-
**CategoryTheory.Presheaf.isLocallySurjective_iff_of_fac** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Presheaf`。
形式化陈述：isLocallySurjective_iff_of_fac {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} {f₁ : F₁ ⟶ F₂} {f₂ : F
₂ ⟶ F₃} {f₃ : F₁ ⟶ F₃} (fac : f₁ ≫ f₂ = f₃) [IsLocallySurjective J f₁] : IsLocal
lySurjective J f₃ ↔ IsLocallySurjective J f₂
参数：fac : f₁ ≫ f₂ = f₃。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Presheaf.isLocallySurjective_of_isLocallySurjective_fac`：
isLocallySurjective_of_isLocallySurjective_fac {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} {f₁ : F₁ ⟶ F
₂} {f₂ : F₂ ⟶ F₃} {f₃ : F₁ ⟶ F₃} (fac : f₁ ≫ f₂ = f₃) [IsLoc…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isLocallySurjective_iff_of_fac
    {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} {f₁ : F₁ ⟶ F₂} {f₂ : F₂ ⟶ F₃} {f₃ : F₁ ⟶ F₃} (fac : f₁ ≫ f₂ = f₃)
    [IsLocallySurjective J f₁] :
    IsLocallySurjective J f₃ ↔ IsLocallySurjective J f₂ := by
  constructor
  · intro
    exact isLocallySurjective_of_isLocallySurjective_fac J fac
  · intro
    rw [← fac]
    infer_instance
/-
**CategoryTheory.Presheaf.comp_isLocallySurjective_iff** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Presheaf`。
形式化陈述：comp_isLocallySurjective_iff {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ 
⟶ F₃) [IsLocallySurjective J f₁] : IsLocallySurjective J (f₁ ≫ f₂) ↔ IsLocallySu
rjective J f₂
参数：f₁ : F₁ ⟶ F₂；f₂ : F₂ ⟶ F₃。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Presheaf.isLocallySurjective_iff_of_fac`：isLocallySurject
ive_iff_of_fac {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} {f₁ : F₁ ⟶ F₂} {f₂ : F₂ ⟶ F₃} {f₃ : F₁ ⟶ F₃}
 (fac : f₁ ≫ f₂ = f₃) [IsLocallySurjective J…
-/
lemma comp_isLocallySurjective_iff
    {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃)
    [IsLocallySurjective J f₁] :
    IsLocallySurjective J (f₁ ≫ f₂) ↔ IsLocallySurjective J f₂ :=
  isLocallySurjective_iff_of_fac J rfl

variable {J} in
/-
**CategoryTheory.Presheaf.isLocallySurjective_of_le** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Presheaf`。
形式化陈述：isLocallySurjective_of_le {K : GrothendieckTopology C} (hJK : J <= K) {F G
 : Cᵒᵖ ⥤ A} (f : F ⟶ G) (h : IsLocallySurjective J f) : IsLocallySurjective K f 
where imageSieve_mem s
参数：hJK : J <= K；f : F ⟶ G；h : IsLocallySurjective J f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presheaf.IsLocallySurjective.imageSieve_mem`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {J : CategoryTheory.GrothendieckTop
ology C} {A : Type u'}   {inst_1 : CategoryTheor…
-/
lemma isLocallySurjective_of_le {K : GrothendieckTopology C} (hJK : J ≤ K) {F G : Cᵒᵖ ⥤ A}
    (f : F ⟶ G) (h : IsLocallySurjective J f) : IsLocallySurjective K f where
  imageSieve_mem s := by apply hJK; exact h.1 _
/-
**CategoryTheory.Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallyS
urjective** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective {F₁ F₂ F₃ 
: Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃) [IsLocallyInjective J (f₁ ≫ f₂)] [IsLoc
allySurjective J f₁] : IsLocallyInjective J f₂ where equalizerSieve_mem {X} x₁ x
₂ h
参数：f₁ : F₁ ⟶ F₂；f₂ : F₂ ⟶ F₃；f₁ ≫ f₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.intersection_covering`：intersection_
covering (rj : R in J X) (sj : S in J X) : R ⊓ S in J X
· 使用引理 `CategoryTheory.Presheaf.imageSieve_mem`：imageSieve_mem {F G : Cᵒᵖ ⥤ A} (
f : F ⟶ G) [IsLocallySurjective J f] {U : Cᵒᵖ} (s : ToType (G.obj U)) : imageSie
ve f s in J U.unop
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `CategoryTheory.GrothendieckTopology.superset_covering`：superset_covering
 (Hss : S <= R) (sjx : S in J X) : R in J X
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Presheaf.equalizerSieve_apply`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.Category.{
v', u'} D]   {FD : D → D → Type u_…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.NatTrans.naturality_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1
, u_1} D]   {FD : outParam (D …
· 使用引理 `CategoryTheory.Presheaf.app_localPreimage`：app_localPreimage {F G : Cᵒᵖ 
⥤ A} (f : F ⟶ G) {U : Cᵒᵖ} (s : ToType (G.obj U)) {V : C} (g : V ⟶ U.unop) (hg :
 imageSieve f s g) : f.app _ (l…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.GrothendieckTopology.transitive`：transitive (hS : S in J 
X) (R : Sieve X) (h : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> R.pullback f in J Y) : R in
 J X
· 使用定理 `CategoryTheory.Sieve.le_pullback_bind`：le_pullback_bind (S : Presieve X)
 (R : forall ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f -> Sieve Y) (f : Y ⟶ X) (h : S f) : R h <=
 (bind S R).pullback f
· 使用引理 `CategoryTheory.Presheaf.equalizerSieve_mem`：equalizerSieve_mem [IsLocall
yInjective J φ] {X : Cᵒᵖ} (x y : ToType (F₁.obj X)) (h : φ.app X x = φ.app X y) 
: equalizerSieve x y in J X.unop
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
-/
lemma isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective
    {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃)
    [IsLocallyInjective J (f₁ ≫ f₂)] [IsLocallySurjective J f₁] :
    IsLocallyInjective J f₂ where
  equalizerSieve_mem {X} x₁ x₂ h := by
    let S := imageSieve f₁ x₁ ⊓ imageSieve f₁ x₂
    have hS : S ∈ J X.unop := by
      apply J.intersection_covering
      all_goals apply imageSieve_mem
    let T : ∀ ⦃Y : C⦄ (f : Y ⟶ X.unop) (_ : S f), Sieve Y := fun Y f hf =>
      equalizerSieve (localPreimage f₁ x₁ f hf.1) (localPreimage f₁ x₂ f hf.2)
    refine J.superset_covering ?_ (J.transitive hS (Sieve.bind S.1 T) ?_)
    · rintro Y f ⟨Z, a, g, hg, ha, rfl⟩
      simpa using congr_arg (f₁.app _) ha
    · intro Y f hf
      apply J.superset_covering (Sieve.le_pullback_bind _ _ _ hf)
      apply equalizerSieve_mem J (f₁ ≫ f₂)
      dsimp
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, app_localPreimage,
        app_localPreimage, NatTrans.naturality_apply, NatTrans.naturality_apply, h]
/-
**CategoryTheory.Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallyS
urjective_fac** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac {F₁ F₂
 F₃ : Cᵒᵖ ⥤ A} {f₁ : F₁ ⟶ F₂} {f₂ : F₂ ⟶ F₃} (f₃ : F₁ ⟶ F₃) (fac : f₁ ≫ f₂ = f₃)
 [IsLocallyInjective J f₃] [IsLocallySurjective J f₁] : IsLocallyInjective J f₂
参数：f₃ : F₁ ⟶ F₃；fac : f₁ ≫ f₂ = f₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLo
callySurjective`：isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective
 {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃) [IsLocallyInjective J (f₁…
-/
lemma isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac
    {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} {f₁ : F₁ ⟶ F₂} {f₂ : F₂ ⟶ F₃} (f₃ : F₁ ⟶ F₃) (fac : f₁ ≫ f₂ = f₃)
    [IsLocallyInjective J f₃] [IsLocallySurjective J f₁] :
    IsLocallyInjective J f₂ := by
  subst fac
  exact isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective J f₁ f₂
/-
**CategoryTheory.Presheaf.isLocallySurjective_of_isLocallySurjective_of_isLocall
yInjective** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective {F₁ F₂ F₃
 : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃) [IsLocallySurjective J (f₁ ≫ f₂)] [IsL
ocallyInjective J f₂] : IsLocallySurjective J f₁ where imageSieve_mem {X} x
参数：f₁ : F₁ ⟶ F₂；f₂ : F₂ ⟶ F₃；f₁ ≫ f₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.superset_covering`：superset_covering
 (Hss : S <= R) (sjx : S in J X) : R in J X
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.naturality_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1
, u_1} D]   {FD : outParam (D …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.GrothendieckTopology.transitive`：transitive (hS : S in J 
X) (R : Sieve X) (h : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> R.pullback f in J Y) : R in
 J X
· 使用引理 `CategoryTheory.Presheaf.imageSieve_mem`：imageSieve_mem {F G : Cᵒᵖ ⥤ A} (
f : F ⟶ G) [IsLocallySurjective J f] {U : Cᵒᵖ} (s : ToType (G.obj U)) : imageSie
ve f s in J U.unop
· 使用定理 `CategoryTheory.Sieve.le_pullback_bind`：le_pullback_bind (S : Presieve X)
 (R : forall ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f -> Sieve Y) (f : Y ⟶ X) (h : S f) : R h <=
 (bind S R).pullback f
· 使用引理 `CategoryTheory.Presheaf.equalizerSieve_mem`：equalizerSieve_mem [IsLocall
yInjective J φ] {X : Cᵒᵖ} (x y : ToType (F₁.obj X)) (h : φ.app X x = φ.app X y) 
: equalizerSieve x y in J X.unop
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Presheaf.app_localPreimage`：app_localPreimage {F G : Cᵒᵖ 
⥤ A} (f : F ⟶ G) {U : Cᵒᵖ} (s : ToType (G.obj U)) {V : C} (g : V ⟶ U.unop) (hg :
 imageSieve f s g) : f.app _ (l…
· 使用定理 `CategoryTheory.NatTrans.comp_app`：comp_app {F G H : C ⥤ D} (α : F ⟶ G) (
β : G ⟶ H) (X : C) : (α ≫ β).app X = α.app X ≫ β.app X
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
-/
lemma isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective
    {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃)
    [IsLocallySurjective J (f₁ ≫ f₂)] [IsLocallyInjective J f₂] :
    IsLocallySurjective J f₁ where
  imageSieve_mem {X} x := by
    let S := imageSieve (f₁ ≫ f₂) (f₂.app _ x)
    let T : ∀ ⦃Y : C⦄ (f : Y ⟶ X) (_ : S f), Sieve Y := fun Y f hf =>
      equalizerSieve (f₁.app _ (localPreimage (f₁ ≫ f₂) (f₂.app _ x) f hf)) (F₂.map f.op x)
    refine J.superset_covering ?_ (J.transitive (imageSieve_mem J (f₁ ≫ f₂) (f₂.app _ x))
      (Sieve.bind S.1 T) ?_)
    · rintro Y _ ⟨Z, a, g, hg, ha, rfl⟩
      exact ⟨F₁.map a.op (localPreimage (f₁ ≫ f₂) _ _ hg), by simpa using! ha⟩
    · intro Y f hf
      apply J.superset_covering (Sieve.le_pullback_bind _ _ _ hf)
      apply equalizerSieve_mem J f₂
      rw [NatTrans.naturality_apply, ← app_localPreimage (f₁ ≫ f₂) _ _ hf,
        NatTrans.comp_app, ConcreteCategory.comp_apply]
/-
**CategoryTheory.Presheaf.isLocallySurjective_of_isLocallySurjective_of_isLocall
yInjective_fac** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective_fac {F₁ F
₂ F₃ : Cᵒᵖ ⥤ A} {f₁ : F₁ ⟶ F₂} {f₂ : F₂ ⟶ F₃} (f₃ : F₁ ⟶ F₃) (fac : f₁ ≫ f₂ = f₃
) [IsLocallySurjective J f₃] [IsLocallyInjective J f₂] : IsLocallySurjective J f
₁
参数：f₃ : F₁ ⟶ F₃；fac : f₁ ≫ f₂ = f₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Presheaf.isLocallySurjective_of_isLocallySurjective_of_is
LocallyInjective`：isLocallySurjective_of_isLocallySurjective_of_isLocallyInjecti
ve {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃) [IsLocallySurjective J (…
-/
lemma isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective_fac
    {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} {f₁ : F₁ ⟶ F₂} {f₂ : F₂ ⟶ F₃} (f₃ : F₁ ⟶ F₃) (fac : f₁ ≫ f₂ = f₃)
    [IsLocallySurjective J f₃] [IsLocallyInjective J f₂] :
    IsLocallySurjective J f₁ := by
  subst fac
  exact isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective J f₁ f₂
/-
**CategoryTheory.Presheaf.comp_isLocallyInjective_iff** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Presheaf`。
形式化陈述：comp_isLocallyInjective_iff {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶
 F₃) [IsLocallyInjective J f₁] [IsLocallySurjective J f₁] : IsLocallyInjective J
 (f₁ ≫ f₂) ↔ IsLocallyInjective J f₂
参数：f₁ : F₁ ⟶ F₂；f₂ : F₂ ⟶ F₃。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLo
callySurjective`：isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective
 {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃) [IsLocallyInjective J (f₁…
-/
lemma comp_isLocallyInjective_iff
    {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃)
    [IsLocallyInjective J f₁] [IsLocallySurjective J f₁] :
    IsLocallyInjective J (f₁ ≫ f₂) ↔ IsLocallyInjective J f₂ := by
  constructor
  · intro
    exact isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective J f₁ f₂
  · intro
    infer_instance
/-
**CategoryTheory.Presheaf.isLocallySurjective_comp_iff** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Presheaf`。
形式化陈述：isLocallySurjective_comp_iff {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ 
⟶ F₃) [IsLocallyInjective J f₂] [IsLocallySurjective J f₂] : IsLocallySurjective
 J (f₁ ≫ f₂) ↔ IsLocallySurjective J f₁
参数：f₁ : F₁ ⟶ F₂；f₂ : F₂ ⟶ F₃。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Presheaf.isLocallySurjective_of_isLocallySurjective_of_is
LocallyInjective`：isLocallySurjective_of_isLocallySurjective_of_isLocallyInjecti
ve {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃) [IsLocallySurjective J (…
-/
lemma isLocallySurjective_comp_iff
    {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃)
    [IsLocallyInjective J f₂] [IsLocallySurjective J f₂] :
    IsLocallySurjective J (f₁ ≫ f₂) ↔ IsLocallySurjective J f₁ := by
  constructor
  · intro
    exact isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective J f₁ f₂
  · intro
    infer_instance
/-
**CategoryTheory.Presheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Presheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {F₁ F₂ : Cᵒᵖ ⥤ Type w} (f : F₁ ⟶ F₂) :
    IsLocallySurjective J (Subfunctor.toRangeSheafify J f) where
  imageSieve_mem {X} := by
    rintro ⟨s, hs⟩
    refine J.superset_covering ?_ hs
    rintro Y g ⟨t, ht⟩
    exact ⟨t, Subtype.ext ht⟩

/-- The image of `F` in `J.sheafify F` is isomorphic to the sheafification. -/
/-
**CategoryTheory.Presheaf.sheafificationIsoImagePresheaf** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Presheaf`。
形式化陈述：sheafificationIsoImagePresheaf (F : Cᵒᵖ ⥤ Type (max u v)) : J.sheafify F ≅
 ((Subfunctor.range (J.toSheafify F)).sheafify J).toFunctor where hom
参数：F : Cᵒᵖ ⥤ Type (max u v)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of `F` in `J.sheafify F` is isomorphic to the sheafification.
-/
noncomputable def sheafificationIsoImagePresheaf (F : Cᵒᵖ ⥤ Type (max u v)) :
    J.sheafify F ≅ ((Subfunctor.range (J.toSheafify F)).sheafify J).toFunctor where
  hom :=
    J.sheafifyLift (Subfunctor.toRangeSheafify J _)
      ((isSheaf_iff_isSheaf_of_type J _).mpr <|
        Subfunctor.sheafify_isSheaf _ <|
          (isSheaf_iff_isSheaf_of_type J _).mp <| GrothendieckTopology.sheafify_isSheaf J _)
  inv := Subfunctor.ι _
  hom_inv_id :=
    J.sheafify_hom_ext _ _ (J.sheafify_isSheaf _) (by simp [Subfunctor.toRangeSheafify])
  inv_hom_id := by
    rw [← cancel_mono (Subfunctor.ι _), Category.id_comp, Category.assoc]
    refine Eq.trans ?_ (Category.comp_id _)
    congr 1
    exact J.sheafify_hom_ext _ _ (J.sheafify_isSheaf _) (by simp [Subfunctor.toRangeSheafify])

section

open GrothendieckTopology.Plus

/-
**CategoryTheory.Presheaf.isLocallySurjective_toPlus** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.Presheaf`。
形式化陈述：isLocallySurjective_toPlus (P : Cᵒᵖ ⥤ Type (max u v)) : IsLocallySurjectiv
e J (J.toPlus P) where imageSieve_mem x
参数：P : Cᵒᵖ ⥤ Type (max u v)。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfShape`：∀ {J : Type v} [inst : C
ategoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasCo
limitsOfShape J (Type u)
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Types.instIsEquivalenceForgetTypeFun`：(CategoryTheory.for
get (Type u)).IsEquivalence
· 使用定理 `CategoryTheory.GrothendieckTopology.Plus.exists_rep`：exists_rep {X : C} 
{P : Cᵒᵖ ⥤ D} (x : ToType ((J.plusObj P).obj (op X))) : exists (S : J.Cover X) (
y : Meq P S), x = mk y
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`：∀ {J
 : Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.GrothendieckTopology.superset_covering`：superset_covering
 (Hss : S <= R) (sjx : S in J X) : R in J X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GrothendieckTopology.Plus.toPlus_eq_mk`：toPlus_eq_mk {X :
 C} {P : Cᵒᵖ ⥤ D} (x : ToType (P.obj (op X))) : (J.toPlus P).app _ x = mk (Meq.m
k ⊤ x)
· 使用定理 `CategoryTheory.GrothendieckTopology.Plus.res_mk_eq_mk_pullback`：res_mk_e
q_mk_pullback {Y X : C} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x : Meq P S) (f : Y ⟶ X) 
: (J.plusObj P).map f.op (mk x) = mk (x.pullback f)
· 使用定理 `CategoryTheory.GrothendieckTopology.Plus.eq_mk_iff_exists`：eq_mk_iff_exi
sts {X : C} {P : Cᵒᵖ ⥤ D} {S T : J.Cover X} (x : Meq P S) (y : Meq P T) : mk x =
 mk y ↔ exists (W : J.Cover X) (h1 : W ⟶ S) (h2…
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `CategoryTheory.Meq.ext`：ext {X} {P : Cᵒᵖ ⥤ D} {S : J.Cover X} (x y : Meq
 P S) (h : forall I : S.Arrow, x I = y I) : x = y
· 使用定理 `CategoryTheory.Sieve.downward_closed`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.Sieve X) {Y Z : C}   {f
 : Y ⟶ X}, self.arrows f →…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
instance isLocallySurjective_toPlus (P : Cᵒᵖ ⥤ Type (max u v)) :
    IsLocallySurjective J (J.toPlus P) where
  imageSieve_mem x := by
    obtain ⟨S, x, rfl⟩ := exists_rep x
    refine J.superset_covering (fun Y f hf => ⟨x.1 ⟨Y, f, hf⟩, ?_⟩) S.2
    rw [toPlus_eq_mk, res_mk_eq_mk_pullback, eq_mk_iff_exists]
    refine ⟨S.pullback f, homOfLE le_top, 𝟙 _, ?_⟩
    ext ⟨Z, g, hg⟩
    simpa using!
      x.2 { fst.hf := hf, snd.hf := S.1.downward_closed hf g, r.g₁ := g, r.g₂ := 𝟙 Z, .. }

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Presheaf.isLocallySurjective_toSheafify** 是 Mathlib 中的一个实例，位于命名
空间 `CategoryTheory.Presheaf`。
形式化陈述：isLocallySurjective_toSheafify (P : Cᵒᵖ ⥤ Type (max u v)) : IsLocallySurje
ctive J (J.toSheafify P)
参数：P : Cᵒᵖ ⥤ Type (max u v)。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfShape`：∀ {J : Type v} [inst : C
ategoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasCo
limitsOfShape J (Type u)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GrothendieckTopology.plusMap_toPlus`：plusMap_toPlus : J.p
lusMap (J.toPlus P) = J.toPlus (J.plusObj P)
-/
instance isLocallySurjective_toSheafify (P : Cᵒᵖ ⥤ Type (max u v)) :
    IsLocallySurjective J (J.toSheafify P) := by
  dsimp [GrothendieckTopology.toSheafify]
  rw [GrothendieckTopology.plusMap_toPlus]
  infer_instance
/-
**CategoryTheory.Presheaf.isLocallySurjective_toSheafify'** 是 Mathlib 中的一个实例，位于命
名空间 `CategoryTheory.Presheaf`。
形式化陈述：isLocallySurjective_toSheafify' {D : Type*} [Category* D] {FD : D -> D -> 
Type*} {CD : D -> Type (max u v)} [forall X Y, FunLike (FD X Y) (CD X) (CD Y)] [
ConcreteCategory.{max u v} D FD] (P : Cᵒᵖ ⥤ D) [HasWeakSheafify J D] [J.HasSheaf
Compose (forget D)] [J.PreservesSheafification (forget D)] : IsLocallySurjective
 J (toSheafify J P)
参数：max u v；FD X Y；CD X；CD Y；P : Cᵒᵖ ⥤ D；forget D；forget D。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presheaf.isLocallySurjective_iff_whisker_forget`：isLocall
ySurjective_iff_whisker_forget {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) : IsLocallySurjective
 J f ↔ IsLocallySurjective J (whiskerRight f (forget…
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.instHasSheafifyType`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] (J : CategoryTheory.GrothendieckTopology C),   CategoryTheo
ry.HasSheafify J (Type (…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.sheafComposeIso_hom_fac`：sheafComposeIso_hom_fac : toShea
fify J (P ⋙ F) ≫ (sheafifyComposeIso J F P).hom = whiskerRight (toSheafify J P) 
F
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfShape`：∀ {J : Type v} [inst : C
ategoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasCo
limitsOfShape J (Type u)
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Types.instIsEquivalenceForgetTypeFun`：(CategoryTheory.for
get (Type u)).IsEquivalence
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`：∀ {J
 : Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.reflectsIsomorphisms_of_full_and_faithful`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.Types.instFullForgetTypeFun`：(CategoryTheory.forget (Type
 u)).Full
· 使用定理 `CategoryTheory.instFaithfulForget`：∀ (C : Type u_1) [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {FC : outParam (C → C → Type u_2)}   {CC : outParam (C
 → Type w)} [inst_1 : o…
· 使用引理 `CategoryTheory.toSheafify_plusPlusIsoSheafify_hom`：toSheafify_plusPlusIs
oSheafify_hom (P : Cᵒᵖ ⥤ D) : J.toSheafify P ≫ (plusPlusIsoSheafify J D P).hom =
 toSheafify J P
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance isLocallySurjective_toSheafify' {D : Type*} [Category* D] {FD : D → D → Type*}
    {CD : D → Type (max u v)} [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)]
    [ConcreteCategory.{max u v} D FD]
    (P : Cᵒᵖ ⥤ D) [HasWeakSheafify J D] [J.HasSheafCompose (forget D)]
    [J.PreservesSheafification (forget D)] :
    IsLocallySurjective J (toSheafify J P) := by
  rw [isLocallySurjective_iff_whisker_forget,
    ← sheafComposeIso_hom_fac, ← toSheafify_plusPlusIsoSheafify_hom]
  infer_instance

end

end Presheaf

namespace Sheaf

variable {J}
variable {F₁ F₂ F₃ : Sheaf J A} (φ : F₁ ⟶ F₂) (ψ : F₂ ⟶ F₃)

/-- If `φ : F₁ ⟶ F₂` is a morphism of sheaves, this is an abbreviation for
`Presheaf.IsLocallySurjective J φ.val`. -/
/-
**CategoryTheory.Sheaf.IsLocallySurjective** 是 Mathlib 中的一个缩写定义，位于命名空间 `Category
Theory.Sheaf`。
形式化陈述：IsLocallySurjective
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `φ : F₁ ⟶ F₂` is a morphism of sheaves, this is an abbreviation for
`Presheaf.IsLocallySurjective J φ.val`.
-/
abbrev IsLocallySurjective := Presheaf.IsLocallySurjective J φ.hom
/-
**CategoryTheory.Sheaf.isLocallySurjective_sheafToPresheaf_map_iff** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.Sheaf`。
形式化陈述：isLocallySurjective_sheafToPresheaf_map_iff : Presheaf.IsLocallySurjective
 J ((sheafToPresheaf J A).map φ) ↔ IsLocallySurjective φ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isLocallySurjective_sheafToPresheaf_map_iff :
    Presheaf.IsLocallySurjective J ((sheafToPresheaf J A).map φ) ↔ IsLocallySurjective φ := by rfl
/-
**CategoryTheory.Sheaf.isLocallySurjective_comp** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory.Sheaf`。
形式化陈述：isLocallySurjective_comp [IsLocallySurjective φ] [IsLocallySurjective ψ] :
 IsLocallySurjective (φ ≫ ψ)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isLocallySurjective_comp [IsLocallySurjective φ] [IsLocallySurjective ψ] :
    IsLocallySurjective (φ ≫ ψ) :=
  Presheaf.isLocallySurjective_comp J φ.hom ψ.hom
/-
**CategoryTheory.Sheaf.isLocallySurjective_of_iso** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.Sheaf`。
形式化陈述：isLocallySurjective_of_iso [IsIso φ] : IsLocallySurjective φ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isLocallySurjective_of_iso [IsIso φ] : IsLocallySurjective φ := by
  have : IsIso φ.hom := (inferInstance : IsIso ((sheafToPresheaf J A).map φ))
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Sheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {F G : Sheaf J (Type w)} (f : F ⟶ G) :
    IsLocallySurjective (Sheaf.toImage f) := by
  dsimp [Sheaf.toImage]
  infer_instance

variable [J.HasSheafCompose (forget A)]
/-
**CategoryTheory.Sheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsLocallySurjective φ] :
    IsLocallySurjective ((sheafCompose J (forget A)).map φ) :=
  (Presheaf.isLocallySurjective_iff_whisker_forget J φ.hom).1 inferInstance
/-
**CategoryTheory.Sheaf.isLocallySurjective_iff_isIso** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Sheaf`。
形式化陈述：isLocallySurjective_iff_isIso {F G : Sheaf J (Type w)} (f : F ⟶ G) : IsLoc
allySurjective f ↔ IsIso (Sheaf.imageι f)
参数：Type w；f : F ⟶ G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Sheaf.imageι.eq_1`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C}   {F F' : Categor
yTheory.Sheaf J (Type …
· 使用定理 `CategoryTheory.Presheaf.isLocallySurjective_iff_range_sheafify_eq_top'`：
isLocallySurjective_iff_range_sheafify_eq_top' {F G : Cᵒᵖ ⥤ Type w} (f : F ⟶ G) 
: IsLocallySurjective J f ↔ (Subfunctor.range f).sheafify J …
· 使用定理 `CategoryTheory.Subfunctor.eq_top_iff_isIso`：eq_top_iff_isIso : G = ⊤ ↔ I
sIso G.ι
· 使用引理 `CategoryTheory.isIso_iff_of_reflects_iso`：isIso_iff_of_reflects_iso {A B
 : C} (f : A ⟶ B) (F : C ⥤ D) [F.ReflectsIsomorphisms] : IsIso (F.map f) ↔ IsIso
 f
· 使用定理 `CategoryTheory.reflectsIsomorphisms_of_full_and_faithful`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (F : Categor…
-/
theorem isLocallySurjective_iff_isIso {F G : Sheaf J (Type w)} (f : F ⟶ G) :
    IsLocallySurjective f ↔ IsIso (Sheaf.imageι f) := by
  dsimp only [IsLocallySurjective]
  rw [Sheaf.imageι, Presheaf.isLocallySurjective_iff_range_sheafify_eq_top',
    Subfunctor.eq_top_iff_isIso]
  exact isIso_iff_of_reflects_iso (f := Sheaf.imageι f) (F := sheafToPresheaf J (Type w))
/-
**CategoryTheory.Sheaf.epi_of_isLocallySurjective'** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.Sheaf`。
形式化陈述：epi_of_isLocallySurjective' {F₁ F₂ : Sheaf J (Type w)} (φ : F₁ ⟶ F₂) [IsLo
callySurjective φ] : Epi φ where left_cancellation {Z} f₁ f₂ h
参数：Type w；φ : F₁ ⟶ F₂。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.hom_ext`：hom_ext {X Y : P.FullSubcategory}
 {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `CategoryTheory.Presieve.IsSeparatedFor.ext`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)} {X : C
}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.Presieve.IsSheaf.isSeparated`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C}   {P :
 CategoryTheory.Functor Cᵒᵖ (Type…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.isSheaf_iff_isSheaf_of_type`：isSheaf_iff_isSheaf_of_type 
(P : Cᵒᵖ ⥤ Type w) : Presheaf.IsSheaf J P ↔ Presieve.IsSheaf J P
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用引理 `CategoryTheory.Presheaf.imageSieve_mem`：imageSieve_mem {F G : Cᵒᵖ ⥤ A} (
f : F ⟶ G) [IsLocallySurjective J f] {U : Cᵒᵖ} (s : ToType (G.obj U)) : imageSie
ve f s in J U.unop
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g
-/
instance epi_of_isLocallySurjective' {F₁ F₂ : Sheaf J (Type w)} (φ : F₁ ⟶ F₂)
    [IsLocallySurjective φ] : Epi φ where
  left_cancellation {Z} f₁ f₂ h := by
    ext X x
    apply (((isSheaf_iff_isSheaf_of_type _ _).1 Z.2).isSeparated _
      (Presheaf.imageSieve_mem J φ.hom x)).ext
    rintro Y f ⟨s : F₁.obj.obj (op Y), hs : φ.hom.app _ s = F₂.obj.map f.op x⟩
    dsimp
    have h₁ := ConcreteCategory.congr_hom (f₁.hom.naturality f.op) x
    have h₂ := ConcreteCategory.congr_hom (f₂.hom.naturality f.op) x
    dsimp at h₁ h₂
    rw [← h₁, ← h₂, ← hs]
    exact ConcreteCategory.congr_hom (congr_app ((sheafToPresheaf J _).congr_map h) (op Y)) s
/-
**CategoryTheory.Sheaf.epi_of_isLocallySurjective** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.Sheaf`。
形式化陈述：epi_of_isLocallySurjective [IsLocallySurjective φ] : Epi φ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.epi_of_epi_map`：epi_of_epi_map (F : C ⥤ D) [Refle
ctsEpimorphisms F] {X Y : C} {f : X ⟶ Y} (h : Epi (F.map f)) : Epi f
· 使用定理 `CategoryTheory.Functor.reflectsEpimorphisms_of_faithful`：∀ {C : Type u₁}
 [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryThe
ory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.instFaithfulSheafSheafCompose`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} A]   {B : Type u₃} [ins…
· 使用定理 `CategoryTheory.instFaithfulForget`：∀ (C : Type u_1) [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {FC : outParam (C → C → Type u_2)}   {CC : outParam (C
 → Type w)} [inst_1 : o…
· 使用定理 `CategoryTheory.Sheaf.instIsLocallySurjectiveFunMapTypeSheafComposeForget
`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.G
rothendieckTopology C} {A : Type u'}   [inst_1 : CategoryTheor…
-/
instance epi_of_isLocallySurjective [IsLocallySurjective φ] : Epi φ :=
  (sheafCompose J (forget A)).epi_of_epi_map inferInstance
/-
**CategoryTheory.Sheaf.isLocallySurjective_iff_epi** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Sheaf`。
形式化陈述：isLocallySurjective_iff_epi {F G : Sheaf J (Type w)} (φ : F ⟶ G) [HasSheaf
ify J (Type w)] : IsLocallySurjective φ ↔ Epi φ
参数：Type w；φ : F ⟶ G；Type w。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.epi_of_epi_fac`：epi_of_epi_fac {f : X ⟶ Y} {g : Y ⟶ Z} {h
 : X ⟶ Z} [Epi h] (w : f ≫ g = h) : Epi g
· 使用定理 `CategoryTheory.Sheaf.toImage_ι`：∀ {C : Type u} [inst : CategoryTheory.Ca
tegory.{v, u} C] {J : CategoryTheory.GrothendieckTopology C}   {F F' : CategoryT
heory.Sheaf J (Type …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Sheaf.isLocallySurjective_iff_isIso`：isLocallySurjective_
iff_isIso {F G : Sheaf J (Type w)} (f : F ⟶ G) : IsLocallySurjective f ↔ IsIso (
Sheaf.imageι f)
· 使用定理 `CategoryTheory.isIso_of_mono_of_epi`：isIso_of_mono_of_epi [Balanced C] {
X Y : C} (f : X ⟶ Y) [Mono f] [Epi f] : IsIso f
· 使用定理 `CategoryTheory.SheafOfTypes.balanced`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C}   [CategoryTh
eory.HasSheafify J (Type w…
· 使用定理 `CategoryTheory.instMonoSheafTypeImageι`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C}   {F F' : C
ategoryTheory.Sheaf J (Type …
-/
lemma isLocallySurjective_iff_epi {F G : Sheaf J (Type w)} (φ : F ⟶ G)
    [HasSheafify J (Type w)] :
    IsLocallySurjective φ ↔ Epi φ := by
  constructor
  · intro
    infer_instance
  · intro
    have := epi_of_epi_fac (Sheaf.toImage_ι φ)
    rw [isLocallySurjective_iff_isIso φ]
    apply isIso_of_mono_of_epi

end Sheaf

namespace Presieve.FamilyOfElements

variable {R R' : Cᵒᵖ ⥤ Type w} (φ : R ⟶ R') {X : Cᵒᵖ} (r' : R'.obj X)

/-- Given a morphism `φ : R ⟶ R'` of presheaves of types and `r' : R'.obj X`,
this is the family of elements of `R` defined over the sieve `Presheaf.imageSieve φ r'`
which sends a map in this sieve to an arbitrary choice of a preimage of the
restriction of `r'`. -/
/-
**CategoryTheory.Presieve.FamilyOfElements.localPreimage** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Presieve.FamilyOfElements`。
形式化陈述：localPreimage : FamilyOfElements R (Presheaf.imageSieve φ r').arrows
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism `φ : R ⟶ R'` of presheaves of types and `r' : R'.obj X`,
this is the family of elements of `R` defined over the sieve `Presheaf.imageSiev
e φ r'`
which sends a map in this sieve to an arbitrary choice of a preimage of the
restriction of `r'`.
-/
noncomputable def localPreimage :
    FamilyOfElements R (Presheaf.imageSieve φ r').arrows :=
  fun _ f hf => Presheaf.localPreimage φ r' f hf
/-
**CategoryTheory.Presieve.FamilyOfElements.isAmalgamation_map_localPreimage** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Presieve.FamilyOfElements`。
形式化陈述：isAmalgamation_map_localPreimage : ((localPreimage φ r').map φ).IsAmalgama
tion r'
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Presheaf.app_localPreimage`：app_localPreimage {F G : Cᵒᵖ 
⥤ A} (f : F ⟶ G) {U : Cᵒᵖ} (s : ToType (G.obj U)) {V : C} (g : V ⟶ U.unop) (hg :
 imageSieve f s g) : f.app _ (l…
-/
lemma isAmalgamation_map_localPreimage :
    ((localPreimage φ r').map φ).IsAmalgamation r' :=
  fun _ f hf => (Presheaf.app_localPreimage φ r' f hf).symm

end Presieve.FamilyOfElements

namespace Presheaf

variable {S : C} {ι : Type*} [Small.{w} ι] {X : ι → C} (f : ∀ i, X i ⟶ S)

variable [LocallySmall.{w} C]

/-
**CategoryTheory.Presheaf.imageSieve_cofanIsColimitDesc_shrinkYoneda_map** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：imageSieve_cofanIsColimitDesc_shrinkYoneda_map {c : Cofan (fun i => shrink
Yoneda.{w}.obj (X i))} (hc : IsColimit c) {U : C} (g : U ⟶ S) : Presheaf.imageSi
eve (Cofan.IsColimit.desc hc (fun i => shrinkYoneda.{w}.map (f i))) (U
参数：fun i => shrinkYoneda.{w}.obj (X i)；hc : IsColimit c；g : U ⟶ S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.ext`：∀ {C : Type u₁} [inst : CategoryTheory.Categor
y.{v₁, u₁} C] {X : C} {R S : CategoryTheory.Sieve X},   (∀ ⦃Y : C⦄ (f : Y ⟶ X), 
R.arrows f ↔ S…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Sieve.pullback_apply`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {X Y : C} (h : Y ⟶ X) (S : CategoryTheory.Sieve X) (x :
 C)   (sl : x ⟶ Y), (Cate…
· 使用定理 `CategoryTheory.Sieve.generate_apply`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {X : C} (R : CategoryTheory.Presieve X) (Z : C) (f : Z 
⟶ X),   (CategoryTheory.S…
· 使用定理 `CategoryTheory.Limits.Types.jointly_surjective_of_isColimit`：jointly_sur
jective_of_isColimit {F : J ⥤ Type u} {t : Cocone F} (h : IsColimit t) (x : t.pt
) : exists j y, t.ι.app j y = x
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm`：shrink
Yoneda_map_app_shrinkYonedaObjObjEquiv_symm {X X' : C} {Y : Cᵒᵖ} (f : Y.unop ⟶ X
) (g : X ⟶ X') : (shrinkYoneda.map g).app _ (shrinkYon…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
· 使用定理 `CategoryTheory.Limits.Cofan.IsColimit.fac`：∀ {β : Type w} {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {F : β → C} {c : CategoryTheory.Limits.
Cofan F}   (hc : CategoryTheory…
· 使用引理 `CategoryTheory.shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm`：shrink
Yoneda_obj_map_shrinkYonedaObjObjEquiv_symm {X : C} {Y Y' : Cᵒᵖ} (g : Y ⟶ Y') (f
 : Y.unop ⟶ X) : (shrinkYoneda.obj _).map g (shrinkYon…
-/
lemma imageSieve_cofanIsColimitDesc_shrinkYoneda_map
    {c : Cofan (fun i ↦ shrinkYoneda.{w}.obj (X i))} (hc : IsColimit c)
    {U : C} (g : U ⟶ S) :
    Presheaf.imageSieve
      (Cofan.IsColimit.desc hc (fun i ↦ shrinkYoneda.{w}.map (f i))) (U := U)
        (shrinkYonedaObjObjEquiv.symm g) = Sieve.pullback g (Sieve.ofArrows X f) := by
  ext V v
  simp only [Sieve.pullback_apply, Sieve.generate_apply]
  refine ⟨fun hv ↦ ?_, ?_⟩
  · obtain ⟨w, hw⟩ := hv
    obtain ⟨⟨i⟩, a, rfl⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves ((evaluation _ _).obj (op V)) hc) w
    obtain ⟨a : V ⟶ X i, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective a
    refine ⟨_, a, _, ⟨i⟩, shrinkYonedaObjObjEquiv.symm.injective ?_⟩
    rw [← shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm]
    convert! hw using 1
    · exact (ConcreteCategory.congr_hom (NatTrans.congr_app
        ((Cofan.IsColimit.fac hc (fun i ↦ shrinkYoneda.{w}.map (f i))) i) (op V))
          (shrinkYonedaObjObjEquiv.symm a)).symm
    · exact (shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm v.op g).symm
  · rintro ⟨_, a, _, ⟨i⟩, fac⟩
    refine ⟨(c.inj i).app (op V) (shrinkYonedaObjObjEquiv.symm a),
      (ConcreteCategory.congr_hom (NatTrans.congr_app
      ((Cofan.IsColimit.fac hc (fun i ↦ shrinkYoneda.{w}.map (f i))) i) (op V))
        (shrinkYonedaObjObjEquiv.symm a)).trans ?_⟩
    rw [shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm a (f i), fac]
    exact (shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm v.op g).symm

end Presheaf

namespace GrothendieckTopology

/-
**CategoryTheory.GrothendieckTopology.ofArrows_mem_iff_isLocallySurjective_cofan
IsColimitDesc_shrinkYoneda_map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Grothen
dieckTopology`。
形式化陈述：ofArrows_mem_iff_isLocallySurjective_cofanIsColimitDesc_shrinkYoneda_map [
LocallySmall.{w} C] {S : C} {ι : Type*} [Small.{w} ι] {X : ι -> C} (f : forall i
, X i ⟶ S) {c : Cofan (fun i => shrinkYoneda.{w}.obj (X i))} (hc : IsColimit c) 
: Sieve.ofArrows _ f in J S ↔ Presheaf.IsLocallySurjective J (Cofan.IsColimit.de
sc hc (fun i => shrinkYoneda.{w}.map (f i)))
参数：f : forall i, X i ⟶ S；fun i => shrinkYoneda.{w}.obj (X i)；hc : IsColimit c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `CategoryTheory.GrothendieckTopology.pullback_stable`：pullback_stable (f 
: Y ⟶ X) (hS : S in J X) : S.pullback f in J Y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Presheaf.imageSieve_cofanIsColimitDesc_shrinkYoneda_map`：
imageSieve_cofanIsColimitDesc_shrinkYoneda_map {c : Cofan (fun i => shrinkYoneda
.{w}.obj (X i))} (hc : IsColimit c) {U : C} (g : U ⟶ S) : Pr…
· 使用定理 `CategoryTheory.Sieve.pullback_id`：pullback_id : S.pullback (𝟙 _) = S
· 使用引理 `CategoryTheory.Presheaf.imageSieve_mem`：imageSieve_mem {F G : Cᵒᵖ ⥤ A} (
f : F ⟶ G) [IsLocallySurjective J f] {U : Cᵒᵖ} (s : ToType (G.obj U)) : imageSie
ve f s in J U.unop
-/
lemma ofArrows_mem_iff_isLocallySurjective_cofanIsColimitDesc_shrinkYoneda_map
    [LocallySmall.{w} C] {S : C} {ι : Type*} [Small.{w} ι] {X : ι → C}
    (f : ∀ i, X i ⟶ S)
    {c : Cofan (fun i ↦ shrinkYoneda.{w}.obj (X i))} (hc : IsColimit c) :
    Sieve.ofArrows _ f ∈ J S ↔
      Presheaf.IsLocallySurjective J
        (Cofan.IsColimit.desc hc (fun i ↦ shrinkYoneda.{w}.map (f i))) := by
  refine ⟨fun hf ↦ ⟨fun {U u} ↦ ?_⟩, fun hf ↦ ?_⟩
  · obtain ⟨u, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective u
    replace hf := J.pullback_stable u hf
    rwa [← Presheaf.imageSieve_cofanIsColimitDesc_shrinkYoneda_map f hc u] at hf
  · rw [← Sieve.pullback_id (S := Sieve.ofArrows X f),
      ← Presheaf.imageSieve_cofanIsColimitDesc_shrinkYoneda_map f hc (𝟙 S)]
    exact Presheaf.imageSieve_mem J (Cofan.IsColimit.desc hc (fun i ↦ shrinkYoneda.{w}.map (f i)))
      (shrinkYonedaObjObjEquiv.symm (𝟙 S))

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.GrothendieckTopology.ofArrows_mem_iff_isLocallySurjective_cofan
IsColimitDesc_uliftYoneda_map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Grothend
ieckTopology`。
形式化陈述：ofArrows_mem_iff_isLocallySurjective_cofanIsColimitDesc_uliftYoneda_map {S
 : C} {ι : Type*} [Small.{max w v} ι] {X : ι -> C} (f : forall i, X i ⟶ S) {c : 
Cofan (fun i => uliftYoneda.{w}.obj (X i))} (hc : IsColimit c) : Sieve.ofArrows 
_ f in J S ↔ Presheaf.IsLocallySurjective J (Cofan.IsColimit.desc hc (fun i => u
liftYoneda.{w}.map (f i)))
参数：f : forall i, X i ⟶ S；fun i => uliftYoneda.{w}.obj (X i)；hc : IsColimit c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.GrothendieckTopology.ofArrows_mem_iff_isLocallySurjective
_cofanIsColimitDesc_shrinkYoneda_map`：ofArrows_mem_iff_isLocallySurjective_cofan
IsColimitDesc_shrinkYoneda_map [LocallySmall.{w} C] {S : C} {ι : Type*} [Small.{
w} ι] {X : ι -> C}…
· 使用定理 `CategoryTheory.Limits.Cofan.IsColimit.hom_ext`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {I : Type u_1} {F : I → C} {c : CategoryTheory.L
imits.Cofan F}   (hc : CategoryTheo…
· 使用定理 `CategoryTheory.Limits.Cofan.IsColimit.fac_assoc`：∀ {β : Type w} {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {F : β → C} {c : CategoryTheory.L
imits.Cofan F}   (hc : CategoryTheory…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.Cofan.IsColimit.fac`：∀ {β : Type w} {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {F : β → C} {c : CategoryTheory.Limits.
Cofan F}   (hc : CategoryTheory…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Discrete.natIso_inv_app`：∀ {C : Type u₂} [inst : Category
Theory.Category.{v₂, u₂} C] {I : Type u₁}   {F G : CategoryTheory.Functor (Categ
oryTheory.Discrete I) C} (f …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Presheaf.isLocallySurjective_comp_iff`：isLocallySurjectiv
e_comp_iff {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃) [IsLocallyInjectiv
e J f₂] [IsLocallySurjective J f₂] : IsLoc…
· 使用定理 `CategoryTheory.Presheaf.instIsLocallyInjectiveOfIsIsoFunctorOpposite`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [inst_1 : C
ategoryTheory.Category.{v', u'} D]   {FD : D → D → Type u_…
· 使用定理 `CategoryTheory.NatIso.hom_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma ofArrows_mem_iff_isLocallySurjective_cofanIsColimitDesc_uliftYoneda_map
    {S : C} {ι : Type*} [Small.{max w v} ι] {X : ι → C}
    (f : ∀ i, X i ⟶ S)
    {c : Cofan (fun i ↦ uliftYoneda.{w}.obj (X i))} (hc : IsColimit c) :
    Sieve.ofArrows _ f ∈ J S ↔
      Presheaf.IsLocallySurjective J
        (Cofan.IsColimit.desc hc (fun i ↦ uliftYoneda.{w}.map (f i))) := by
  let e : Discrete.functor (fun i ↦ uliftYoneda.{w}.obj (X i)) ≅
      Discrete.functor (fun i ↦ shrinkYoneda.{max w v}.obj (X i)) :=
    Discrete.natIso (fun i ↦ uliftYonedaIsoShrinkYoneda.{w}.app (X i.as))
  let hc' := (IsColimit.precomposeInvEquiv e _).2 hc
  rw [ofArrows_mem_iff_isLocallySurjective_cofanIsColimitDesc_shrinkYoneda_map.{max w v} J f hc']
  have :
      Cofan.IsColimit.desc hc (fun i ↦ uliftYoneda.map (f i)) ≫
        uliftYonedaIsoShrinkYoneda.hom.app _ =
      Cofan.IsColimit.desc hc' (fun i ↦ shrinkYoneda.map (f i)) :=
    Cofan.IsColimit.hom_ext hc _ _ (fun i ↦ by
      rw [Cofan.IsColimit.fac_assoc, NatTrans.naturality,
        ← Cofan.IsColimit.fac hc' (fun i ↦ shrinkYoneda.map (f i)) i]
      simp [Cofan.inj, e])
  rw [← this, Presheaf.isLocallySurjective_comp_iff J]
/-
**CategoryTheory.GrothendieckTopology.ofArrows_mem_iff_isLocallySurjective_sigma
Desc_shrinkYoneda_map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopo
logy`。
形式化陈述：ofArrows_mem_iff_isLocallySurjective_sigmaDesc_shrinkYoneda_map [LocallySm
all.{w} C] {S : C} {ι : Type*} [Small.{w} ι] {X : ι -> C} (f : forall i, X i ⟶ S
) : Sieve.ofArrows _ f in J S ↔ Presheaf.IsLocallySurjective J (Sigma.desc (fun 
i => shrinkYoneda.{w}.map (f i)))
参数：f : forall i, X i ⟶ S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GrothendieckTopology.ofArrows_mem_iff_isLocallySurjective
_cofanIsColimitDesc_shrinkYoneda_map`：ofArrows_mem_iff_isLocallySurjective_cofan
IsColimitDesc_shrinkYoneda_map [LocallySmall.{w} C] {S : C} {ι : Type*} [Small.{
w} ι] {X : ι -> C}…
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
-/
lemma ofArrows_mem_iff_isLocallySurjective_sigmaDesc_shrinkYoneda_map [LocallySmall.{w} C]
    {S : C} {ι : Type*} [Small.{w} ι] {X : ι → C} (f : ∀ i, X i ⟶ S) :
    Sieve.ofArrows _ f ∈ J S ↔
      Presheaf.IsLocallySurjective J (Sigma.desc (fun i ↦ shrinkYoneda.{w}.map (f i))) :=
  ofArrows_mem_iff_isLocallySurjective_cofanIsColimitDesc_shrinkYoneda_map J f
    (coproductIsCoproduct _)
/-
**CategoryTheory.GrothendieckTopology.ofArrows_mem_iff_isLocallySurjective_sigma
Desc_uliftYoneda_map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopol
ogy`。
形式化陈述：ofArrows_mem_iff_isLocallySurjective_sigmaDesc_uliftYoneda_map {S : C} {ι 
: Type*} [Small.{max w v} ι] {X : ι -> C} (f : forall i, X i ⟶ S) : Sieve.ofArro
ws _ f in J S ↔ Presheaf.IsLocallySurjective J (Sigma.desc (fun i => uliftYoneda
.{w}.map (f i)))
参数：f : forall i, X i ⟶ S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GrothendieckTopology.ofArrows_mem_iff_isLocallySurjective
_cofanIsColimitDesc_uliftYoneda_map`：ofArrows_mem_iff_isLocallySurjective_cofanI
sColimitDesc_uliftYoneda_map {S : C} {ι : Type*} [Small.{max w v} ι] {X : ι -> C
} (f : forall i, …
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
-/
lemma ofArrows_mem_iff_isLocallySurjective_sigmaDesc_uliftYoneda_map
    {S : C} {ι : Type*} [Small.{max w v} ι] {X : ι → C} (f : ∀ i, X i ⟶ S) :
    Sieve.ofArrows _ f ∈ J S ↔
      Presheaf.IsLocallySurjective J (Sigma.desc (fun i ↦ uliftYoneda.{w}.map (f i))) :=
  ofArrows_mem_iff_isLocallySurjective_cofanIsColimitDesc_uliftYoneda_map J f
    (coproductIsCoproduct _)

end GrothendieckTopology

end CategoryTheory

