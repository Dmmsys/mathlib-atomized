/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Locally fully faithful functors into sites

## Main results

- `CategoryTheory.Functor.IsLocallyFull`:
  A functor `G : C ⥤ D` is locally full w.r.t. a topology on `D` if for every
  `f : G.obj U ⟶ G.obj V`, the set of `G.map fᵢ : G.obj Wᵢ ⟶ G.obj U` such that `G.map fᵢ ≫ f` is
  in the image of `G` is a coverage of the topology on `D`.
- `CategoryTheory.Functor.IsLocallyFaithful`:
  A functor `G : C ⥤ D` is locally faithful w.r.t. a topology on `D` if for every `f₁ f₂ : U ⟶ V`
  whose images in `D` are equal, the set of `G.map gᵢ : G.obj Wᵢ ⟶ G.obj U` such that
  `gᵢ ≫ f₁ = gᵢ ≫ f₂` is a coverage of the topology on `D`.

## References

* [caramello2020]: Olivia Caramello, *Denseness conditions, morphisms and equivalences of toposes*

-/

@[expose] public section

universe w vC vD uC uD

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D] (G : C ⥤ D)
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)

/--
For a functor `G : C ⥤ D`, and a morphism `f : G.obj U ⟶ G.obj V`,
`Functor.imageSieve G f` is the sieve of `U`
consisting of those arrows whose composition with `f` has a lift in `G`.

This is the image sieve of `f` under `yonedaMap G V` and hence the name.
See `Functor.imageSieve_eq_imageSieve`.
-/
/-
**CategoryTheory.Functor.imageSieve** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fu
nctor`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{vC, uC} C] →     {D : T
ype uD} →       [inst_1 : CategoryTheory.Category.{vD, uD} D] →         (G : Cat
egoryTheory.Functor C D) → {U V : C} → (G.obj U ⟶ G.obj V) → CategoryTheory.Siev
e U
参数：G : CategoryTheory.Functor C D；G.obj U ⟶ G.obj V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a functor `G : C ⥤ D`, and a morphism `f : G.obj U ⟶ G.obj V`,
`Functor.imageSieve G f` is the sieve of `U`
consisting of those arrows whose composition with `f` has a lift in `G`.

This is the image sieve of `f` under `yonedaMap G V` and hence the name.
See `Functor.imageSieve_eq_imageSieve`.
-/
def Functor.imageSieve {U V : C} (f : G.obj U ⟶ G.obj V) : Sieve U where
  arrows _ i := ∃ l, G.map l = G.map i ≫ f
  downward_closed := by
    rintro Y₁ Y₂ i₁ ⟨l, hl⟩ i₂
    exact ⟨i₂ ≫ l, by simp [hl]⟩

@[simp]
/-
**CategoryTheory.Functor.imageSieve_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Functor`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{vC, uC} C] {D : Type uD} 
[inst_1 : CategoryTheory.Category.{vD, uD} D]   (G : CategoryTheory.Functor C D)
 {U V : C} (f : U ⟶ V), G.imageSieve (G.map f) = ⊤
参数：G : CategoryTheory.Functor C D；f : U ⟶ V；G.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.ext`：∀ {C : Type u₁} [inst : CategoryTheory.Categor
y.{v₁, u₁} C] {X : C} {R S : CategoryTheory.Sieve X},   (∀ ⦃Y : C⦄ (f : Y ⟶ X), 
R.arrows f ↔ S…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Functor.imageSieve_map {U V : C} (f : U ⟶ V) : G.imageSieve (G.map f) = ⊤ := by
  ext W g; simpa using ⟨g ≫ f, by simp⟩

/--
For two arrows `f₁ f₂ : U ⟶ V`, the arrows `i` such that `i ≫ f₁ = i ≫ f₂` forms a sieve.
-/
@[simps]
/-
**CategoryTheory.Sieve.equalizer** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sieve
`。
形式化陈述：{C : Type uC} → [inst : CategoryTheory.Category.{vC, uC} C] → {U V : C} → 
(U ⟶ V) → (U ⟶ V) → CategoryTheory.Sieve U
参数：U ⟶ V；U ⟶ V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For two arrows `f₁ f₂ : U ⟶ V`, the arrows `i` such that `i ≫ f₁ = i ≫ f₂` forms
 a sieve.
-/
def Sieve.equalizer {U V : C} (f₁ f₂ : U ⟶ V) : Sieve U where
  arrows _ i := i ≫ f₁ = i ≫ f₂
  downward_closed := by aesop

@[simp]
/-
**CategoryTheory.Sieve.equalizer_self** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Sieve`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{vC, uC} C] {U V : C} (f :
 U ⟶ V),   CategoryTheory.Sieve.equalizer f f = ⊤
参数：f : U ⟶ V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.ext`：∀ {C : Type u₁} [inst : CategoryTheory.Categor
y.{v₁, u₁} C] {X : C} {R S : CategoryTheory.Sieve X},   (∀ ⦃Y : C⦄ (f : Y ⟶ X), 
R.arrows f ↔ S…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Sieve.equalizer_apply`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{vC, uC} C] {U V : C} (f₁ f₂ : U ⟶ V) (x : C) (i : x ⟶ U),   (Cate
goryTheory.Sieve.equalizer…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Sieve.equalizer_self {U V : C} (f : U ⟶ V) : equalizer f f = ⊤ := by ext; simp
/-
**CategoryTheory.Sieve.equalizer_eq_equalizerSieve** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Sieve`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{vC, uC} C] {U V : C} (f₁ 
f₂ : U ⟶ V),   CategoryTheory.Sieve.equalizer f₁ f₂ = CategoryTheory.Presheaf.eq
ualizerSieve f₁ f₂
参数：f₁ f₂ : U ⟶ V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Sieve.equalizer_eq_equalizerSieve {U V : C} (f₁ f₂ : U ⟶ V) :
    Sieve.equalizer f₁ f₂ = Presheaf.equalizerSieve (F := yoneda.obj _) f₁ f₂ := rfl
/-
**CategoryTheory.Functor.imageSieve_eq_imageSieve** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Functor`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{vC, uC} C] {D : Type uD} 
[inst_1 : CategoryTheory.Category.{vC, uD} D]   (G : CategoryTheory.Functor C D)
 {U V : C} (f : G.obj U ⟶ G.obj V),   G.imageSieve f = CategoryTheory.Presheaf.i
mageSieve (CategoryTheory.yonedaMap G V) f
参数：G : CategoryTheory.Functor C D；f : G.obj U ⟶ G.obj V；CategoryTheory.yonedaMap
 G V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Functor.imageSieve_eq_imageSieve {D : Type uD} [Category.{vC} D] (G : C ⥤ D) {U V : C}
    (f : G.obj U ⟶ G.obj V) :
    G.imageSieve f = Presheaf.imageSieve (yonedaMap G V) f := rfl

open Presieve Opposite

namespace Functor

/--
A functor `G : C ⥤ D` is locally full w.r.t. a topology on `D` if for every `f : G.obj U ⟶ G.obj V`,
the set of `G.map fᵢ : G.obj Wᵢ ⟶ G.obj U` such that `G.map fᵢ ≫ f` is
in the image of `G` is a coverage of the topology on `D`.
-/
/-
**CategoryTheory.Functor.IsLocallyFull** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{vC, uC} C] →     {D : T
ype uD} →       [inst_1 : CategoryTheory.Category.{vD, uD} D] →         Category
Theory.Functor C D → CategoryTheory.GrothendieckTopology D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `G : C ⥤ D` is locally full w.r.t. a topology on `D` if for every `f :
 G.obj U ⟶ G.obj V`,
the set of `G.map fᵢ : G.obj Wᵢ ⟶ G.obj U` such that `G.map fᵢ ≫ f` is
in the image of `G` is a coverage of the topology on `D`.
-/
class IsLocallyFull : Prop where
  functorPushforward_imageSieve_mem : ∀ {U V} (f : G.obj U ⟶ G.obj V),
    (G.imageSieve f).functorPushforward G ∈ K _

/--
A functor `G : C ⥤ D` is locally faithful w.r.t. a topology on `D` if for every `f₁ f₂ : U ⟶ V`
whose images in `D` are equal, the set of `G.map gᵢ : G.obj Wᵢ ⟶ G.obj U` such that
`gᵢ ≫ f₁ = gᵢ ≫ f₂` is a coverage of the topology on `D`.
-/
/-
**CategoryTheory.Functor.IsLocallyFaithful** 是 Mathlib 中的一个归纳类型，位于命名空间 `Category
Theory.Functor`。
形式化陈述：{C : Type uC} →   [inst : CategoryTheory.Category.{vC, uC} C] →     {D : T
ype uD} →       [inst_1 : CategoryTheory.Category.{vD, uD} D] →         Category
Theory.Functor C D → CategoryTheory.GrothendieckTopology D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `G : C ⥤ D` is locally faithful w.r.t. a topology on `D` if for every 
`f₁ f₂ : U ⟶ V`
whose images in `D` are equal, the set of `G.map gᵢ : G.obj Wᵢ ⟶ G.obj U` such t
hat
`gᵢ ≫ f₁ = gᵢ ≫ f₂` is a coverage of the topology on `D`.
-/
class IsLocallyFaithful : Prop where
  functorPushforward_equalizer_mem : ∀ {U V : C} (f₁ f₂ : U ⟶ V), G.map f₁ = G.map f₂ →
    (Sieve.equalizer f₁ f₂).functorPushforward G ∈ K _
/-
**CategoryTheory.Functor.functorPushforward_imageSieve_mem** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Functor`。
形式化陈述：functorPushforward_imageSieve_mem [G.IsLocallyFull K] {U V} (f : G.obj U ⟶
 G.obj V) : (G.imageSieve f).functorPushforward G in K _
参数：f : G.obj U ⟶ G.obj V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsLocallyFull.functorPushforward_imageSieve_mem`：
∀ {C : Type uC} {inst : CategoryTheory.Category.{vC, uC} C} {D : Type uD} {inst_
1 : CategoryTheory.Category.{vD, uD} D}   {G : CategoryTheor…
-/
lemma functorPushforward_imageSieve_mem [G.IsLocallyFull K] {U V} (f : G.obj U ⟶ G.obj V) :
    (G.imageSieve f).functorPushforward G ∈ K _ :=
  Functor.IsLocallyFull.functorPushforward_imageSieve_mem _
/-
**CategoryTheory.Functor.functorPushforward_equalizer_mem** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Functor`。
形式化陈述：functorPushforward_equalizer_mem [G.IsLocallyFaithful K] {U V} (f₁ f₂ : U 
⟶ V) (e : G.map f₁ = G.map f₂) : (Sieve.equalizer f₁ f₂).functorPushforward G in
 K _
参数：f₁ f₂ : U ⟶ V；e : G.map f₁ = G.map f₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsLocallyFaithful.functorPushforward_equalizer_me
m`：∀ {C : Type uC} {inst : CategoryTheory.Category.{vC, uC} C} {D : Type uD} {in
st_1 : CategoryTheory.Category.{vD, uD} D}   {G : CategoryTheor…
-/
lemma functorPushforward_equalizer_mem
    [G.IsLocallyFaithful K] {U V} (f₁ f₂ : U ⟶ V) (e : G.map f₁ = G.map f₂) :
      (Sieve.equalizer f₁ f₂).functorPushforward G ∈ K _ :=
  Functor.IsLocallyFaithful.functorPushforward_equalizer_mem _ _ e

variable {K}
variable {A : Type*} [Category* A] (G : C ⥤ D)
/-
**CategoryTheory.Functor.IsLocallyFull.ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Functor.IsLocallyFull`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{vC, uC} C] {D : Type uD} 
[inst_1 : CategoryTheory.Category.{vD, uD} D]   {K : CategoryTheory.Grothendieck
Topology D} (G : CategoryTheory.Functor C D) [G.IsLocallyFull K]   (ℱ : Category
Theory.Sheaf K (Type u_2)) {X Y : C} (i : G.obj X ⟶ G.obj Y) {s t : ℱ.obj.obj (O
pposite.op (G.obj X))},   (∀ ⦃Z : C⦄ (j : Z ⟶ X) (f : Z ⟶ Y),       G.map f = Ca
tegoryTheory.CategoryStruct.comp (G.map j) i →         (CategoryTheory.ConcreteC
ategory.hom (ℱ.obj.map (G.map j).op)) s =           (CategoryTheory.ConcreteCate
gory.hom (ℱ.obj.map (G.map j).op)) t) →     s = t
参数：G : CategoryTheory.Functor C D；ℱ : CategoryTheory.Sheaf K (Type u_2)；i : G.ob
j X ⟶ G.obj Y；Opposite.op (G.obj X)；∀ ⦃Z : C⦄ (j : Z ⟶ X) (f : Z ⟶ Y),       G.m
ap f = CategoryTheory.CategoryStruct.comp (G.map j) i →         (CategoryTheory.
ConcreteCategory.hom (ℱ.obj.map (G.map j).op)) s =           (CategoryTheory.Con
creteCategory.hom (ℱ.obj.map (G.map j).op)) t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.IsSeparatedFor.ext`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)} {X : C
}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.isSeparatedFor`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)}
 {X : C}   {R : CategoryTheory.Presieve…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.isSheaf_iff_isSheaf_of_type`：isSheaf_iff_isSheaf_of_type 
(P : Cᵒᵖ ⥤ Type w) : Presheaf.IsSheaf J P ↔ Presieve.IsSheaf J P
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用引理 `CategoryTheory.Functor.functorPushforward_imageSieve_mem`：functorPushfor
ward_imageSieve_mem [G.IsLocallyFull K] {U V} (f : G.obj U ⟶ G.obj V) : (G.image
Sieve f).functorPushforward G in K _
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsLocallyFull.ext [G.IsLocallyFull K]
    (ℱ : Sheaf K Type*) {X Y : C} (i : G.obj X ⟶ G.obj Y)
    {s t : ℱ.obj.obj (op (G.obj X))}
    (h : ∀ ⦃Z : C⦄ (j : Z ⟶ X) (f : Z ⟶ Y), G.map f = G.map j ≫ i →
      ℱ.1.map (G.map j).op s = ℱ.1.map (G.map j).op t) : s = t := by
  apply (((isSheaf_iff_isSheaf_of_type _ _).1 ℱ.property) _
    (G.functorPushforward_imageSieve_mem K i)).isSeparatedFor.ext
  rintro Z _ ⟨W, iWX, iZW, ⟨iWY, e⟩, rfl⟩
  simp [h iWX iWY e]
/-
**CategoryTheory.Functor.IsLocallyFaithful.ext** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Functor.IsLocallyFaithful`。
形式化陈述：∀ {C : Type uC} [inst : CategoryTheory.Category.{vC, uC} C] {D : Type uD} 
[inst_1 : CategoryTheory.Category.{vD, uD} D]   {K : CategoryTheory.Grothendieck
Topology D} (G : CategoryTheory.Functor C D) [G.IsLocallyFaithful K]   (ℱ : Cate
goryTheory.Sheaf K (Type u_2)) {X Y : C} (i₁ i₂ : X ⟶ Y),   G.map i₁ = G.map i₂ 
→     ∀ {s t : ℱ.obj.obj (Opposite.op (G.obj X))},       (∀ ⦃Z : C⦄ (j : Z ⟶ X),
           CategoryTheory.CategoryStruct.comp j i₁ = CategoryTheory.CategoryStru
ct.comp j i₂ →             (CategoryTheory.ConcreteCategory.hom (ℱ.obj.map (G.ma
p j).op)) s =               (CategoryTheory.ConcreteCategory.hom (ℱ.obj.map (G.m
ap j).op)) t) →         s = t
参数：G : CategoryTheory.Functor C D；ℱ : CategoryTheory.Sheaf K (Type u_2)；i₁ i₂ : 
X ⟶ Y；Opposite.op (G.obj X)；∀ ⦃Z : C⦄ (j : Z ⟶ X),           CategoryTheory.Cate
goryStruct.comp j i₁ = CategoryTheory.CategoryStruct.comp j i₂ →             (Ca
tegoryTheory.ConcreteCategory.hom (ℱ.obj.map (G.map j).op)) s =               (C
ategoryTheory.ConcreteCategory.hom (ℱ.obj.map (G.map j).op)) t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.IsSeparatedFor.ext`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)} {X : C
}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.isSeparatedFor`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)}
 {X : C}   {R : CategoryTheory.Presieve…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.isSheaf_iff_isSheaf_of_type`：isSheaf_iff_isSheaf_of_type 
(P : Cᵒᵖ ⥤ Type w) : Presheaf.IsSheaf J P ↔ Presieve.IsSheaf J P
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用引理 `CategoryTheory.Functor.functorPushforward_equalizer_mem`：functorPushforw
ard_equalizer_mem [G.IsLocallyFaithful K] {U V} (f₁ f₂ : U ⟶ V) (e : G.map f₁ = 
G.map f₂) : (Sieve.equalizer f₁ f₂).functorPu…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsLocallyFaithful.ext [G.IsLocallyFaithful K] (ℱ : Sheaf K Type*)
    {X Y : C} (i₁ i₂ : X ⟶ Y) (e : G.map i₁ = G.map i₂)
    {s t : ℱ.obj.obj (op (G.obj X))}
    (h : ∀ ⦃Z : C⦄ (j : Z ⟶ X), j ≫ i₁ = j ≫ i₂ →
      ℱ.1.map (G.map j).op s = ℱ.1.map (G.map j).op t) : s = t := by
  apply (((isSheaf_iff_isSheaf_of_type _ _).1 ℱ.property) _
    (G.functorPushforward_equalizer_mem K i₁ i₂ e)).isSeparatedFor.ext
  rintro Z _ ⟨W, iWX, iZW, hiWX, rfl⟩
  simp [h iWX hiWX]
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) IsLocallyFull.of_full [G.Full] : G.IsLocallyFull K where
  functorPushforward_imageSieve_mem f := by
    rw [← G.map_preimage f]
    simp only [Functor.imageSieve_map, Sieve.functorPushforward_top, GrothendieckTopology.top_mem]
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) IsLocallyFaithful.of_faithful [G.Faithful] : G.IsLocallyFaithful K where
  functorPushforward_equalizer_mem f₁ f₂ e := by obtain rfl := G.map_injective e; simp

end CategoryTheory.Functor

