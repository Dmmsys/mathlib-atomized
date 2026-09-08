/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Hypercover.One
public import Mathlib.CategoryTheory.Limits.Types.Multiequalizer

/-!

# `1`-hypercovers and (pre)sheaves of types

In this file we provide some API for working with `1`-hypercovers for sheaves of types.

## Main declarations

- `CategoryTheory.PreOneHypercover.IsStronglySheafFor`: A pre-`1`-hypercover `E`
  satisfies the strong sheaf condition for a presheaf of types `F` if
  `F` is a sheaf for the `0`-covering and separated for the `1`-coverings.
- `CategoryTheory.PreOneHypercover.IsStronglySheafFor.amalgamate`: Glue
  a family of compatible sections along `E` if `E` satisfies the strong sheaf condition.
- `CategoryTheory.PreOneHypercover.IsStronglySheafFor.isLimitMultifork`: If `E`
  satisfies the strong sheaf condition for `F`, then the multiequalizer diagram
  for `E` is limiting.

-/

universe w

@[expose] public section

namespace CategoryTheory

open Limits Opposite

variable {C : Type*} [Category* C]

namespace PreZeroHypercover

variable {S : C}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If the pre-`0`-hypercover `E` has pairwise pullbacks, the sections over the multifork
associated to a presheaf of types are equivalent to the compatible families on `E`. -/
@[simps]
/-
**CategoryTheory.PreZeroHypercover.sectionsEquivOfHasPullbacks** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.PreZeroHypercover`。
形式化陈述：sectionsEquivOfHasPullbacks (E : PreZeroHypercover S) [E.HasPullbacks] (F 
: Cᵒᵖ ⥤ Type*) : (E.toPreOneHypercover.multicospanIndex F).sections ≃ Subtype (P
resieve.Arrows.Compatible F E.f) where toFun s
参数：E : PreZeroHypercover S；F : Cᵒᵖ ⥤ Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the pre-`0`-hypercover `E` has pairwise pullbacks, the sections over the mult
ifork
associated to a presheaf of types are equivalent to the compatible families on `
E`.
-/
def sectionsEquivOfHasPullbacks (E : PreZeroHypercover S)
    [E.HasPullbacks] (F : Cᵒᵖ ⥤ Type*) :
    (E.toPreOneHypercover.multicospanIndex F).sections ≃
      Subtype (Presieve.Arrows.Compatible F E.f) where
  toFun s :=
    ⟨s.val, fun i j W gi gj hgij ↦ by
      have heq := s.property ⟨(i, j), ⟨⟩⟩
      dsimp at heq
      rw [← pullback.lift_fst _ _ hgij]
      conv_rhs => rw [← pullback.lift_snd _ _ hgij]
      rw [op_comp, Functor.map_comp, op_comp, Functor.map_comp]
      simp [heq]⟩
  invFun s := ⟨s.val, fun r ↦ s.property _ _ _ _ _ pullback.condition⟩
  left_inv _ := rfl
  right_inv _ := rfl
/-
**CategoryTheory.PreZeroHypercover.isLimit_toPreOneHypercover_type_iff** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.PreZeroHypercover`。
形式化陈述：isLimit_toPreOneHypercover_type_iff (E : PreZeroHypercover.{w} S) [E.HasPu
llbacks] (F : Cᵒᵖ ⥤ Type*) : Nonempty (IsLimit <| E.toPreOneHypercover.multifork
 F) ↔ E.presieve₀.IsSheafFor F
参数：E : PreZeroHypercover.{w} S；F : Cᵒᵖ ⥤ Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Limits.Multifork.isLimit_types_iff`：isLimit_types_iff : N
onempty (IsLimit c) ↔ Function.Bijective c.toSections
· 使用定理 `CategoryTheory.Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible`：
isSheafFor_ofArrows_iff_bijective_toCompabible : IsSheafFor P (ofArrows X π) ↔ F
unction.Bijective (Arrows.toCompatible P π)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Bijective.of_comp_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Bijective f → ∀ (g : γ → α), Function.Bijective 
(f ∘ g) ↔ Function.Bi…
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isLimit_toPreOneHypercover_type_iff (E : PreZeroHypercover.{w} S) [E.HasPullbacks]
    (F : Cᵒᵖ ⥤ Type*) :
    Nonempty (IsLimit <| E.toPreOneHypercover.multifork F) ↔ E.presieve₀.IsSheafFor F := by
  rw [Multifork.isLimit_types_iff, Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible,
    ← Function.Bijective.of_comp_iff' (E.sectionsEquivOfHasPullbacks F).symm.bijective]
  rfl

end PreZeroHypercover

/-
**CategoryTheory.Precoverage.ZeroHypercover.Hom.isSheafFor_iff** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Precoverage.ZeroHypercover.Hom`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasPullbacks C]   {K : CategoryTheory.Precoverage C} [inst_
2 : K.IsStableUnderBaseChange] {S : C}   {F : CategoryTheory.Functor Cᵒᵖ (Type u
_2)} {𝒰 : K.ZeroHypercover S} {𝒱 : K.ZeroHypercover S}   (f : CategoryTheory.Pre
coverage.ZeroHypercover.Hom K 𝒰 𝒱),   CategoryTheory.Presieve.IsSheafFor F (Cate
goryTheory.Presieve.ofArrows 𝒰.X 𝒰.f) →     (∀ {X : C} (f : X ⟶ S),         Cate
goryTheory.Presieve.IsSeparatedFor F           (CategoryTheory.Presieve.ofArrows
 (CategoryTheory.Precoverage.ZeroHypercover.pullback₂ f 𝒰).X             (Catego
ryTheory.Precoverage.ZeroHypercover.pullback₂ f 𝒰).f)) →       CategoryTheory.Pr
esieve.IsSheafFor F (CategoryTheory.Presieve.ofArrows 𝒱.X 𝒱.f)
参数：Type u_2；f : CategoryTheory.Precoverage.ZeroHypercover.Hom K 𝒰 𝒱；CategoryTheo
ry.Presieve.ofArrows 𝒰.X 𝒰.f；∀ {X : C} (f : X ⟶ S),         CategoryTheory.Presi
eve.IsSeparatedFor F           (CategoryTheory.Presieve.ofArrows (CategoryTheory
.Precoverage.ZeroHypercover.pullback₂ f 𝒰).X             (CategoryTheory.Precove
rage.ZeroHypercover.pullback₂ f 𝒰).f)；CategoryTheory.Presieve.ofArrows 𝒱.X 𝒱.f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instHasPullbackFOfHasPullbacks
Presieve₀`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (E
 : CategoryTheory.PreZeroHypercover X) (f : Y ⟶ X)   [E.presieve₀.HasPu…
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instHasPullbacksPresieve₀OfHas
Pullbacks`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (K : Categor
yTheory.Precoverage C) [K.HasPullbacks] {X Y : C}   (E : K.ZeroHypercov…
· 使用定理 `CategoryTheory.Precoverage.instHasPullbacksOfHasPullbacks`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Precoverage C)  
 [CategoryTheory.Limits.HasPullbacks C], J.HasP…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presieve.isSheafFor_iff_generate`：isSheafFor_iff_generate
 (R : Presieve X) : IsSheafFor P R ↔ IsSheafFor P (generate R : Presieve X)
· 使用定理 `CategoryTheory.Presieve.isSheafFor_subsieve_aux`：isSheafFor_subsieve_aux
 (P : Cᵒᵖ ⥤ Type w) {S : Sieve X} {R : Presieve X} (h : (S : Presieve X) <= R) (
hS : IsSheafFor P (S : Presieve X)) (…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Sieve.generate_le_iff`：generate_le_iff (R : Presieve X) (
S : Sieve X) : generate R <= S ↔ R <= S
· 使用定理 `CategoryTheory.Sieve.generate_sieve`：generate_sieve (S : Sieve X) : gene
rate S = S
· 使用引理 `CategoryTheory.Presieve.ofArrows_le_iff`：ofArrows_le_iff {X : C} {ι : Ty
pe*} {Y : ι -> C} {f : forall i, Y i ⟶ X} {R : Presieve X} : Presieve.ofArrows Y
 f <= R ↔ forall i, R (f i)
· 使用定理 `CategoryTheory.PreZeroHypercover.Hom.w₀`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {S : C} {E : CategoryTheory.PreZeroHypercover S}   {F 
: CategoryTheory.PreZeroHyper…
· 使用定理 `CategoryTheory.Sieve.pullbackArrows_comm`：pullbackArrows_comm {X Y : C} 
(f : Y ⟶ X) (R : Presieve X) [R.HasPullbacks f] : Sieve.generate (R.pullbackArro
ws f) = (Sieve.generate R).pul…
· 使用定理 `CategoryTheory.Presieve.isSeparatedFor_iff_generate`：isSeparatedFor_iff_
generate : IsSeparatedFor P R ↔ IsSeparatedFor P (generate R : Presieve X)
· 使用定理 `CategoryTheory.Presieve.instHasPullbacksOfArrowsOfHasPullback`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) {ι : Ty
pe u_1} (Z : ι → C)   (g : (i : ι) → Z i ⟶ X) [∀ (i…
· 使用定理 `CategoryTheory.Presieve.ofArrows_pullback`：ofArrows_pullback {ι : Type*}
 (Z : ι -> C) (g : forall i : ι, Z i ⟶ X) [forall i, HasPullback (g i) f] : (ofA
rrows (fun i => pullback (g i) …
-/
lemma Precoverage.ZeroHypercover.Hom.isSheafFor_iff [Limits.HasPullbacks C] {K : Precoverage C}
    [K.IsStableUnderBaseChange] {S : C} {F : Cᵒᵖ ⥤ Type*} {𝒰 𝒱 : K.ZeroHypercover S}
    (f : 𝒰.Hom K 𝒱) (H₁ : Presieve.IsSheafFor F (.ofArrows _ 𝒰.f))
    (H₂ : ∀ {X : C} (f : X ⟶ S),
      Presieve.IsSeparatedFor F (.ofArrows (𝒰.pullback₂ f).X (𝒰.pullback₂ f).f)) :
    Presieve.IsSheafFor F (.ofArrows 𝒱.X 𝒱.f) := by
  rw [Presieve.isSheafFor_iff_generate]
  apply Presieve.isSheafFor_subsieve_aux (S := .generate (.ofArrows 𝒰.X 𝒰.f))
  · rw [← Sieve.generate_le_iff, Sieve.generate_sieve, Sieve.generate_le_iff,
      Presieve.ofArrows_le_iff]
    intro i
    rw [← f.w₀]
    exact ⟨_, f.h₀ i, 𝒱.f _, ⟨_⟩, rfl⟩
  · rwa [← Presieve.isSheafFor_iff_generate]
  · intro Y f hf
    rw [← Sieve.pullbackArrows_comm, ← Presieve.isSeparatedFor_iff_generate,
      ← Presieve.ofArrows_pullback]
    apply H₂

namespace PreOneHypercover

variable {X : C} {E : PreOneHypercover.{w} X} {F : Cᵒᵖ ⥤ Type*}

/-- A presheaf `F` of types is (strongly) separated for a pre-`1`-hypercover if `F` is separated for
both the `0` and the `1`-components. -/
/-
**CategoryTheory.PreOneHypercover.IsStronglySeparatedFor** 是 Mathlib 中的一个归纳类型，位于
命名空间 `CategoryTheory.PreOneHypercover`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {X 
: C} → CategoryTheory.PreOneHypercover X → CategoryTheory.Functor Cᵒᵖ (Type u_3)
 → Prop
参数：Type u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A presheaf `F` of types is (strongly) separated for a pre-`1`-hypercover if `F` 
is separated for
both the `0` and the `1`-components.
-/
structure IsStronglySeparatedFor {X : C} (E : PreOneHypercover X) (F : Cᵒᵖ ⥤ Type*) : Prop where
  isSeparatedFor_presieve₀ : E.presieve₀.IsSeparatedFor F
  isSeparatedFor_sieve₁ ⦃i j : E.I₀⦄ ⦃W : C⦄ (p₁ : W ⟶ E.X i) (p₂ : W ⟶ E.X j)
    (h : p₁ ≫ E.f i = p₂ ≫ E.f j) :
    (E.sieve₁ p₁ p₂).arrows.IsSeparatedFor F

/--
A presheaf `F` of types is (strongly) a sheaf for a pre-`1`-hypercover if `F` is a sheaf for
both the `0` and the `1`-components.
This implies that the multiequalizer diagram attached to `E` is exact
(see `CategoryTheory.PreOneHypercover.IsStronglySheafFor.isLimitMultifork`).
-/
/-
**CategoryTheory.PreOneHypercover.IsStronglySheafFor** 是 Mathlib 中的一个归纳类型，位于命名空间
 `CategoryTheory.PreOneHypercover`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {X 
: C} → CategoryTheory.PreOneHypercover X → CategoryTheory.Functor Cᵒᵖ (Type u_3)
 → Prop
参数：Type u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A presheaf `F` of types is (strongly) a sheaf for a pre-`1`-hypercover if `F` is
 a sheaf for
both the `0` and the `1`-components.
This implies that the multiequalizer diagram attached to `E` is exact
(see `CategoryTheory.PreOneHypercover.IsStronglySheafFor.isLimitMultifork`).
-/
structure IsStronglySheafFor {X : C} (E : PreOneHypercover X) (F : Cᵒᵖ ⥤ Type*) : Prop where
  isSheafFor_presieve₀ : E.presieve₀.IsSheafFor F
  isSeparatedFor_sieve₁ ⦃i j : E.I₀⦄ ⦃W : C⦄ (p₁ : W ⟶ E.X i) (p₂ : W ⟶ E.X j)
    (h : p₁ ≫ E.f i = p₂ ≫ E.f j) :
    (E.sieve₁ p₁ p₂).arrows.IsSeparatedFor F
/-
**CategoryTheory.PreOneHypercover.IsStronglySheafFor.isStronglySeparatedFor** 是 
Mathlib 中的一个定理，位于命名空间 `CategoryTheory.PreOneHypercover.IsStronglySheafFor`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X : C} {E 
: CategoryTheory.PreOneHypercover X}   {F : CategoryTheory.Functor Cᵒᵖ (Type u_2
)}, E.IsStronglySheafFor F → E.IsStronglySeparatedFor F
参数：Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.isSeparatedFor`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)}
 {X : C}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.PreOneHypercover.IsStronglySheafFor.isSheafFor_presieve₀`
：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X : C} {E : Cat
egoryTheory.PreOneHypercover X}   {F : CategoryTheory.Functor…
· 使用定理 `CategoryTheory.PreOneHypercover.IsStronglySheafFor.isSeparatedFor_sieve₁
`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X : C} {E : Ca
tegoryTheory.PreOneHypercover X}   {F : CategoryTheory.Functor…
-/
lemma IsStronglySheafFor.isStronglySeparatedFor (h : E.IsStronglySheafFor F) :
    E.IsStronglySeparatedFor F where
  isSeparatedFor_presieve₀ := h.isSheafFor_presieve₀.isSeparatedFor
  isSeparatedFor_sieve₁ _ _ _ p₁ p₂ w := h.isSeparatedFor_sieve₁ p₁ p₂ w
/-
**CategoryTheory.PreOneHypercover.IsStronglySeparatedFor.arrowsCompatible** 是 Ma
thlib 中的一个定理，位于命名空间 `CategoryTheory.PreOneHypercover.IsStronglySeparatedFor`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X : C} {E 
: CategoryTheory.PreOneHypercover X}   {F : CategoryTheory.Functor Cᵒᵖ (Type u_2
)},   E.IsStronglySeparatedFor F →     ∀ (x : (i : E.I₀) → F.obj (Opposite.op (E
.X i))),       (∀ ⦃i j : E.I₀⦄ (k : E.I₁ i j),           (CategoryTheory.Concret
eCategory.hom (F.map (E.p₁ k).op)) (x i) =             (CategoryTheory.ConcreteC
ategory.hom (F.map (E.p₂ k).op)) (x j)) →         CategoryTheory.Presieve.Arrows
.Compatible F E.f x
参数：Type u_2；x : (i : E.I₀) → F.obj (Opposite.op (E.X i))；∀ ⦃i j : E.I₀⦄ (k : E.I
₁ i j),           (CategoryTheory.ConcreteCategory.hom (F.map (E.p₁ k).op)) (x i
) =             (CategoryTheory.ConcreteCategory.hom (F.map (E.p₂ k).op)) (x j)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.IsSeparatedFor.ext`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)} {X : C
}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.PreOneHypercover.IsStronglySeparatedFor.isSeparatedFor_si
eve₁`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X : C} {E 
: CategoryTheory.PreOneHypercover X}   {F : CategoryTheory.Functor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsStronglySeparatedFor.arrowsCompatible (h : E.IsStronglySeparatedFor F)
    (x : ∀ i, F.obj (op <| E.X i))
    (hc : ∀ ⦃i j : E.I₀⦄ (k : E.I₁ i j), F.map (E.p₁ k).op (x i) = F.map (E.p₂ k).op (x j)) :
    Presieve.Arrows.Compatible _ E.f x := by
  rintro i₁ i₂ Z g₁ g₂ heq
  refine (h.isSeparatedFor_sieve₁ g₁ g₂ heq).ext fun W f ⟨T, u, h₁, h₂⟩ ↦ ?_
  rw [← comp_apply, ← Functor.map_comp, ← op_comp, h₁]
  conv_rhs => rw [← comp_apply, ← Functor.map_comp, ← op_comp, h₂]
  simp [hc]

/-- Glue sections of a `Type`-valued sheaf over a `1`-hypercover. -/
/-
**CategoryTheory.PreOneHypercover.IsStronglySheafFor.amalgamate** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.PreOneHypercover.IsStronglySheafFor`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {X 
: C} →       {E : CategoryTheory.PreOneHypercover X} →         {F : CategoryTheo
ry.Functor Cᵒᵖ (Type u_2)} →           E.IsStronglySheafFor F →             (x :
 (i : E.I₀) → F.obj (Opposite.op (E.X i))) →               (∀ ⦃i j : E.I₀⦄ (k : 
E.I₁ i j),                   (CategoryTheory.ConcreteCategory.hom (F.map (E.p₁ k
).op)) (x i) =                     (CategoryTheory.ConcreteCategory.hom (F.map (
E.p₂ k).op)) (x j)) →                 F.obj (Opposite.op X)
参数：Type u_2；x : (i : E.I₀) → F.obj (Opposite.op (E.X i))；∀ ⦃i j : E.I₀⦄ (k : E.I
₁ i j),                   (CategoryTheory.ConcreteCategory.hom (F.map (E.p₁ k).o
p)) (x i) =                     (CategoryTheory.ConcreteCategory.hom (F.map (E.p
₂ k).op)) (x j)；Opposite.op X。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.PreOneHypercover.IsStronglySheafFor.isSheafFor_presieve₀`
：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X : C} {E : Cat
egoryTheory.PreOneHypercover X}   {F : CategoryTheory.Functor…

--- 原说明 ---
Glue sections of a `Type`-valued sheaf over a `1`-hypercover.
-/
noncomputable def IsStronglySheafFor.amalgamate (h : E.IsStronglySheafFor F)
    (x : ∀ i, F.obj (op <| E.X i))
    (hc : ∀ ⦃i j : E.I₀⦄ (k : E.I₁ i j), F.map (E.p₁ k).op (x i) = F.map (E.p₂ k).op (x j)) :
    F.obj (op X) :=
  (h.isSheafFor_presieve₀).amalgamate _
    ((h.isStronglySeparatedFor.arrowsCompatible x hc).familyOfElements_compatible)

@[simp]
/-
**CategoryTheory.PreOneHypercover.IsStronglySheafFor.map_amalgamate** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.PreOneHypercover.IsStronglySheafFor`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X : C} {E 
: CategoryTheory.PreOneHypercover X}   {F : CategoryTheory.Functor Cᵒᵖ (Type u_2
)} (h : E.IsStronglySheafFor F)   (x : (i : E.I₀) → F.obj (Opposite.op (E.X i)))
   (hc :     ∀ ⦃i j : E.I₀⦄ (k : E.I₁ i j),       (CategoryTheory.ConcreteCatego
ry.hom (F.map (E.p₁ k).op)) (x i) =         (CategoryTheory.ConcreteCategory.hom
 (F.map (E.p₂ k).op)) (x j))   (i : E.I₀), (CategoryTheory.ConcreteCategory.hom 
(F.map (E.f i).op)) (h.amalgamate x hc) = x i
参数：Type u_2；h : E.IsStronglySheafFor F；x : (i : E.I₀) → F.obj (Opposite.op (E.X 
i))；hc :     ∀ ⦃i j : E.I₀⦄ (k : E.I₁ i j),       (CategoryTheory.ConcreteCatego
ry.hom (F.map (E.p₁ k).op)) (x i) =         (CategoryTheory.ConcreteCategory.hom
 (F.map (E.p₂ k).op)) (x j)；i : E.I₀；CategoryTheory.ConcreteCategory.hom (F.map 
(E.f i).op)；h.amalgamate x hc。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.PreOneHypercover.IsStronglySheafFor.isSheafFor_presieve₀`
：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X : C} {E : Cat
egoryTheory.PreOneHypercover X}   {F : CategoryTheory.Functor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.PreOneHypercover.IsStronglySheafFor.amalgamate.eq_1`：∀ {C
 : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X : C} {E : Category
Theory.PreOneHypercover X}   {F : CategoryTheory.Functor…
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.valid_glue`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)} {X 
Y : C}   {R : CategoryTheory.Presie…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Presieve.Arrows.Compatible.familyOfElements_ofArrows_mk`：
familyOfElements_ofArrows_mk (i : I) : hx.familyOfElements _ (ofArrows.mk i) = x
 i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsStronglySheafFor.map_amalgamate (h : E.IsStronglySheafFor F)
    (x : ∀ i, F.obj (op <| E.X i))
    (hc : ∀ ⦃i j : E.I₀⦄ (k : E.I₁ i j), F.map (E.p₁ k).op (x i) = F.map (E.p₂ k).op (x j))
    (i : E.I₀) :
    F.map (E.f i).op (h.amalgamate x hc) = x i := by
  rw [amalgamate, Presieve.IsSheafFor.valid_glue _ _ _ ⟨i⟩]
  simp

/-- `F` satisfies the (strong) sheaf condition for the pre-`1`-hypercover `E`, then
the multiequalizer diagram attached to `E` is limiting. -/
noncomputable
/-
**CategoryTheory.PreOneHypercover.IsStronglySheafFor.isLimitMultifork** 是 Mathli
b 中的一个定义，位于命名空间 `CategoryTheory.PreOneHypercover.IsStronglySheafFor`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {X 
: C} →       {E : CategoryTheory.PreOneHypercover X} →         {F : CategoryTheo
ry.Functor Cᵒᵖ (Type u_2)} →           E.IsStronglySheafFor F → CategoryTheory.L
imits.IsLimit (E.multifork F)
参数：Type u_2；E.multifork F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsStronglySheafFor.isLimitMultifork (h : E.IsStronglySheafFor F) :
    IsLimit (E.multifork F) := by
  refine Nonempty.some ?_
  rw [Multifork.isLimit_types_iff]
  refine ⟨fun s t hst ↦ ?_, fun s ↦ ?_⟩
  · exact h.isSheafFor_presieve₀.isSeparatedFor.ext fun _ _ ⟨i⟩ ↦ congr($(hst).val i)
  · exact ⟨h.amalgamate s.val fun i j k ↦ s.property ⟨(i, j), k⟩, by
      ext; exact map_amalgamate _ _ _ _⟩
/-
**CategoryTheory.PreOneHypercover.IsStronglySheafFor.isSheafFor_sieve_of_pullbac
k** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.PreOneHypercover.IsStronglySheafFor`
。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X : C} {E 
: CategoryTheory.PreOneHypercover X}   {F : CategoryTheory.Functor Cᵒᵖ (Type u_2
)},   E.IsStronglySheafFor F →     (∀ ⦃Y : C⦄ (f : Y ⟶ X),         CategoryTheor
y.Presieve.IsSeparatedFor F (CategoryTheory.Sieve.pullback f E.sieve₀).arrows) →
       ∀ {S : CategoryTheory.Sieve X},         (∀ (i : E.I₀), CategoryTheory.Pre
sieve.IsSheafFor F (CategoryTheory.Sieve.pullback (E.f i) S).arrows) →          
 (∀ ⦃i j : E.I₀⦄ (k : E.I₁ i j),               CategoryTheory.Presieve.IsSeparat
edFor F                 (CategoryTheory.Sieve.pullback (CategoryTheory.CategoryS
truct.comp (E.p₁ k) (E.f i)) S).arrows) →             CategoryTheory.Presieve.Is
SheafFor F S.arrows
参数：Type u_2；∀ ⦃Y : C⦄ (f : Y ⟶ X),         CategoryTheory.Presieve.IsSeparatedFo
r F (CategoryTheory.Sieve.pullback f E.sieve₀).arrows；∀ (i : E.I₀), CategoryTheo
ry.Presieve.IsSheafFor F (CategoryTheory.Sieve.pullback (E.f i) S).arrows；∀ ⦃i j
 : E.I₀⦄ (k : E.I₁ i j),               CategoryTheory.Presieve.IsSeparatedFor F 
                (CategoryTheory.Sieve.pullback (CategoryTheory.CategoryStruct.co
mp (E.p₁ k) (E.f i)) S).arrows。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.IsSeparatedFor.ext`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)} {X : C
}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.PreOneHypercover.IsStronglySheafFor.isSeparatedFor_sieve₁
`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X : C} {E : Ca
tegoryTheory.PreOneHypercover X}   {F : CategoryTheory.Functor…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Sieve.pullback_apply`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {X Y : C} (h : Y ⟶ X) (S : CategoryTheory.Sieve X) (x :
 C)   (sl : x ⟶ Y), (Cate…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.PreOneHypercover.w`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {S : C} (self : CategoryTheory.PreOneHypercover S)   ⦃i₁ i₂ 
: self.I₀⦄ (j : self.I₁…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Presieve.Arrows.Compatible.exists_familyOfElements`：exist
s_familyOfElements (hx : Compatible P π x) : exists (x' : FamilyOfElements P (of
Arrows X π)), forall (i : I), x' _ (ofArrows.mk i) = x …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Presieve.isSheafFor_arrows_iff`：isSheafFor_arrows_iff : (
ofArrows X π).IsSheafFor P ↔ (forall (x : (i : I) -> P.obj (op (X i))), Arrows.C
ompatible P π x -> exists! t, foral…
· 使用定理 `CategoryTheory.PreOneHypercover.IsStronglySheafFor.isSheafFor_presieve₀`
：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X : C} {E : Cat
egoryTheory.PreOneHypercover X}   {F : CategoryTheory.Functor…
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用定理 `CategoryTheory.Sieve.downward_closed`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.Sieve X) {Y Z : C}   {f
 : Y ⟶ X}, self.arrows f →…
· 使用定理 `CategoryTheory.Presieve.FamilyOfElements.comp_of_compatible`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ
 (Type w)} {X Y : C}   (S : CategoryTheory.Sieve …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `CategoryTheory.Presieve.FamilyOfElements.Compatible.pullback`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒ
ᵖ (Type w)} {X Y : C}   {S : CategoryTheory.Sieve …
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma IsStronglySheafFor.isSheafFor_sieve_of_pullback (h₁ : E.IsStronglySheafFor F)
    (h₂ : ∀ ⦃Y : C⦄ (f : Y ⟶ X), Presieve.IsSeparatedFor F (E.sieve₀.pullback f).arrows)
    {S : Sieve X}
    (H : ∀ (i : E.I₀), Presieve.IsSheafFor F (S.pullback (E.f i)).arrows)
    (H' : ∀ ⦃i j : E.I₀⦄ (k : E.I₁ i j),
      Presieve.IsSeparatedFor F (S.pullback (E.p₁ k ≫ E.f i)).arrows) :
    Presieve.IsSheafFor F S.arrows := by
  intro t ht
  choose s hs huniq using fun i ↦ H i (t.pullback (E.f i)) (ht.pullback (E.f i))
  have hr : Presieve.Arrows.Compatible _ E.f s := by
    intro i j Z gi gj hgij
    refine (h₁.isSeparatedFor_sieve₁ gi gj hgij).ext fun Y f ⟨k, h, hf₁, hf₂⟩ ↦ ?_
    simp only [← comp_apply, ← Functor.map_comp, ← op_comp, hf₁, hf₂]
    simp only [op_comp, Functor.map_comp, comp_apply]
    congr! 1
    refine (H' k).ext fun W p hp ↦ ?_
    simp only [← comp_apply, ← Functor.map_comp, ← op_comp, hs i (p ≫ E.p₁ k) (by simpa),
      hs j (p ≫ E.p₂ k) (by simpa [← E.w])]
    dsimp only [Presieve.FamilyOfElements.pullback]
    congr 1
    simp [E.w]
  obtain ⟨s', hs'⟩ := hr.exists_familyOfElements
  obtain ⟨t', ht', hunique⟩ := (Presieve.isSheafFor_arrows_iff _ _).mp h₁.isSheafFor_presieve₀ _ hr
  refine ⟨t', fun T f hf ↦ (h₂ f).ext fun Z g hg ↦ ?_, fun y hy ↦ ?_⟩
  · obtain ⟨W, w, u, ⟨i⟩, heq⟩ := hg
    rw [← comp_apply, ← Functor.map_comp, ← op_comp]
    have : t (g ≫ f) (by simp [hf]) = t (w ≫ E.f i) (by simp [heq, hf]) := by
      congr 1
      rw [heq]
    simpa [← heq, ht' i, ← t.comp_of_compatible _ ht, this] using! hs i w _
  · refine hunique _ fun i ↦ huniq _ _ fun Z g hg ↦ ?_
    simp [Presieve.FamilyOfElements.pullback, ← hy _ hg]

/--
Being a sheaf for a presieve `R` is local on the target in the following sense: If `E`
is a pre-`1`-hypercover for which `F` is separated and a sheaf for the `0`-components, then to
check that `F` is a sheaf for `R` it suffices to check:

- `F` is a sheaf for the pullbacks of `R` along the maps from the `0`-components.
- `F` is separated for the pullbacks of `R` along the maps from the `1`-components.
-/
/-
**CategoryTheory.PreOneHypercover.IsStronglySheafFor.isSheafFor_of_pullback** 是 
Mathlib 中的一个定理，位于命名空间 `CategoryTheory.PreOneHypercover.IsStronglySheafFor`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X : C} {E 
: CategoryTheory.PreOneHypercover X}   {F : CategoryTheory.Functor Cᵒᵖ (Type u_2
)},   E.IsStronglySheafFor F →     (∀ ⦃Y : C⦄ (f : Y ⟶ X),         CategoryTheor
y.Presieve.IsSeparatedFor F (CategoryTheory.Sieve.pullback f E.sieve₀).arrows) →
       ∀ {R : CategoryTheory.Presieve X},         (∀ (i : E.I₀),             Cat
egoryTheory.Presieve.IsSheafFor F               (CategoryTheory.Sieve.pullback (
E.f i) (CategoryTheory.Sieve.generate R)).arrows) →           (∀ ⦃i j : E.I₀⦄ (k
 : E.I₁ i j),               CategoryTheory.Presieve.IsSeparatedFor F            
     (CategoryTheory.Sieve.pullback (CategoryTheory.CategoryStruct.comp (E.p₁ k)
 (E.f i))                     (CategoryTheory.Sieve.generate R)).arrows) →      
       CategoryTheory.Presieve.IsSheafFor F R
参数：Type u_2；∀ ⦃Y : C⦄ (f : Y ⟶ X),         CategoryTheory.Presieve.IsSeparatedFo
r F (CategoryTheory.Sieve.pullback f E.sieve₀).arrows；∀ (i : E.I₀),             
CategoryTheory.Presieve.IsSheafFor F               (CategoryTheory.Sieve.pullbac
k (E.f i) (CategoryTheory.Sieve.generate R)).arrows；∀ ⦃i j : E.I₀⦄ (k : E.I₁ i j
),               CategoryTheory.Presieve.IsSeparatedFor F                 (Categ
oryTheory.Sieve.pullback (CategoryTheory.CategoryStruct.comp (E.p₁ k) (E.f i))  
                   (CategoryTheory.Sieve.generate R)).arrows。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presieve.isSheafFor_iff_generate`：isSheafFor_iff_generate
 (R : Presieve X) : IsSheafFor P R ↔ IsSheafFor P (generate R : Presieve X)
· 使用定理 `CategoryTheory.PreOneHypercover.IsStronglySheafFor.isSheafFor_sieve_of_p
ullback`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X : C} 
{E : CategoryTheory.PreOneHypercover X}   {F : CategoryTheory.Functor…

--- 原说明 ---
Being a sheaf for a presieve `R` is local on the target in the following sense: 
If `E`
is a pre-`1`-hypercover for which `F` is separated and a sheaf for the `0`-compo
nents, then to
check that `F` is a sheaf for `R` it suffices to check:

- `F` is a sheaf for the pullbacks of `R` along the maps from the `0`-components
.
- `F` is separated for the pullbacks of `R` along the maps from the `1`-componen
ts.
-/
lemma IsStronglySheafFor.isSheafFor_of_pullback (h₁ : E.IsStronglySheafFor F)
    (h₂ : ∀ ⦃Y : C⦄ (f : Y ⟶ X), Presieve.IsSeparatedFor F (E.sieve₀.pullback f).arrows)
    {R : Presieve X}
    (H : ∀ (i : E.I₀), Presieve.IsSheafFor F ((Sieve.generate R).pullback (E.f i)).arrows)
    (H' : ∀ ⦃i j : E.I₀⦄ (k : E.I₁ i j),
      Presieve.IsSeparatedFor F ((Sieve.generate R).pullback (E.p₁ k ≫ E.f i)).arrows) :
    Presieve.IsSheafFor F R := by
  rw [Presieve.isSheafFor_iff_generate]
  exact h₁.isSheafFor_sieve_of_pullback h₂ H H'

end PreOneHypercover

namespace GrothendieckTopology.OneHypercover

variable {J : GrothendieckTopology C} {X : C} {E : OneHypercover.{w} J X} {F : Cᵒᵖ ⥤ Type*}

/-
**CategoryTheory.GrothendieckTopology.OneHypercover.isStronglySeparatedFor** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.OneHypercover`。
形式化陈述：isStronglySeparatedFor (hf : Presieve.IsSeparated J F) : E.IsStronglySepar
atedFor F where isSeparatedFor_presieve₀
参数：hf : Presieve.IsSeparated J F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presieve.isSeparatedFor_iff_generate`：isSeparatedFor_iff_
generate : IsSeparatedFor P R ↔ IsSeparatedFor P (generate R : Presieve X)
· 使用定理 `CategoryTheory.GrothendieckTopology.OneHypercover.mem₀`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopolog
y C} {S : C}   (self : J.OneHypercover S), s…
· 使用定理 `CategoryTheory.GrothendieckTopology.OneHypercover.mem₁`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopolog
y C} {S : C}   (self : J.OneHypercover S) (i…
-/
lemma isStronglySeparatedFor (hf : Presieve.IsSeparated J F) : E.IsStronglySeparatedFor F where
  isSeparatedFor_presieve₀ := by
    rw [Presieve.isSeparatedFor_iff_generate]
    exact hf _ E.mem₀
  isSeparatedFor_sieve₁ i j W p₁ p₂ h := hf _ (E.mem₁ _ _ _ _ h)
/-
**CategoryTheory.GrothendieckTopology.OneHypercover.isStronglySheafFor** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.OneHypercover`。
形式化陈述：isStronglySheafFor (hf : Presieve.IsSheaf J F) : E.IsStronglySheafFor F wh
ere isSheafFor_presieve₀
参数：hf : Presieve.IsSheaf J F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presieve.isSheafFor_iff_generate`：isSheafFor_iff_generate
 (R : Presieve X) : IsSheafFor P R ↔ IsSheafFor P (generate R : Presieve X)
· 使用定理 `CategoryTheory.GrothendieckTopology.OneHypercover.mem₀`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopolog
y C} {S : C}   (self : J.OneHypercover S), s…
· 使用定理 `CategoryTheory.Presieve.IsSheaf.isSeparated`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C}   {P :
 CategoryTheory.Functor Cᵒᵖ (Type…
· 使用定理 `CategoryTheory.GrothendieckTopology.OneHypercover.mem₁`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopolog
y C} {S : C}   (self : J.OneHypercover S) (i…
-/
lemma isStronglySheafFor (hf : Presieve.IsSheaf J F) : E.IsStronglySheafFor F where
  isSheafFor_presieve₀ := by
    rw [Presieve.isSheafFor_iff_generate]
    exact hf _ E.mem₀
  isSeparatedFor_sieve₁ i j W p₁ p₂ h := hf.isSeparated _ (E.mem₁ _ _ _ _ h)

variable (E) in
/-
**CategoryTheory.GrothendieckTopology.OneHypercover.isSheafFor_sieve_of_pullback
** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.OneHypercover`。
形式化陈述：isSheafFor_sieve_of_pullback (hF : Presieve.IsSheaf J F) {S : Sieve X} (h₁
 : forall (i : E.I₀), Presieve.IsSheafFor F (S.pullback (E.f i)).arrows) (h₂ : f
orall ⦃i j : E.I₀⦄ (k : E.I₁ i j), Presieve.IsSeparatedFor F (S.pullback (E.p₁ k
 ≫ E.f i)).arrows) : Presieve.IsSheafFor F S.arrows
参数：hF : Presieve.IsSheaf J F；h₁ : forall (i : E.I₀), Presieve.IsSheafFor F (S.pu
llback (E.f i)).arrows；h₂ : forall ⦃i j : E.I₀⦄ (k : E.I₁ i j), Presieve.IsSepar
atedFor F (S.pullback (E.p₁ k ≫ E.f i)).arrows。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.PreOneHypercover.IsStronglySheafFor.isSheafFor_sieve_of_p
ullback`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X : C} 
{E : CategoryTheory.PreOneHypercover X}   {F : CategoryTheory.Functor…
· 使用引理 `CategoryTheory.GrothendieckTopology.OneHypercover.isStronglySheafFor`：is
StronglySheafFor (hf : Presieve.IsSheaf J F) : E.IsStronglySheafFor F where isSh
eafFor_presieve₀
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.isSeparatedFor`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)}
 {X : C}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.GrothendieckTopology.pullback_stable`：pullback_stable (f 
: Y ⟶ X) (hS : S in J X) : S.pullback f in J Y
· 使用定理 `CategoryTheory.GrothendieckTopology.OneHypercover.mem₀`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopolog
y C} {S : C}   (self : J.OneHypercover S), s…
-/
lemma isSheafFor_sieve_of_pullback (hF : Presieve.IsSheaf J F) {S : Sieve X}
    (h₁ : ∀ (i : E.I₀), Presieve.IsSheafFor F (S.pullback (E.f i)).arrows)
    (h₂ : ∀ ⦃i j : E.I₀⦄ (k : E.I₁ i j),
      Presieve.IsSeparatedFor F (S.pullback (E.p₁ k ≫ E.f i)).arrows) :
    Presieve.IsSheafFor F S.arrows := by
  refine (E.isStronglySheafFor hF).isSheafFor_sieve_of_pullback ?_ h₁ h₂
  intro Y f
  exact (hF _ (J.pullback_stable _ E.mem₀)).isSeparatedFor

/-- If `F` is a `J`-sheaf, then being a sheaf for a presieve `R` is `J`-local on the target, i.e.
it can be checked on the pullbacks from a `1`-hypercover. -/
/-
**CategoryTheory.GrothendieckTopology.OneHypercover.isSheafFor_of_pullback** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology.OneHypercover`。
形式化陈述：isSheafFor_of_pullback (hF : Presieve.IsSheaf J F) {R : Presieve X} (h₁ : 
forall (i : E.I₀), Presieve.IsSheafFor F ((Sieve.generate R).pullback (E.f i)).a
rrows) (h₂ : forall ⦃i j : E.I₀⦄ (k : E.I₁ i j), Presieve.IsSeparatedFor F ((Sie
ve.generate R).pullback (E.p₁ k ≫ E.f i)).arrows) : Presieve.IsSheafFor F R
参数：hF : Presieve.IsSheaf J F；h₁ : forall (i : E.I₀), Presieve.IsSheafFor F ((Sie
ve.generate R).pullback (E.f i)).arrows；h₂ : forall ⦃i j : E.I₀⦄ (k : E.I₁ i j),
 Presieve.IsSeparatedFor F ((Sieve.generate R).pullback (E.p₁ k ≫ E.f i)).arrows
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presieve.isSheafFor_iff_generate`：isSheafFor_iff_generate
 (R : Presieve X) : IsSheafFor P R ↔ IsSheafFor P (generate R : Presieve X)
· 使用引理 `CategoryTheory.GrothendieckTopology.OneHypercover.isSheafFor_sieve_of_pu
llback`：isSheafFor_sieve_of_pullback (hF : Presieve.IsSheaf J F) {S : Sieve X} (
h₁ : forall (i : E.I₀), Presieve.IsSheafFor F (S.pullback (E.f i)).a…

--- 原说明 ---
If `F` is a `J`-sheaf, then being a sheaf for a presieve `R` is `J`-local on the
 target, i.e.
it can be checked on the pullbacks from a `1`-hypercover.
-/
lemma isSheafFor_of_pullback (hF : Presieve.IsSheaf J F) {R : Presieve X}
    (h₁ : ∀ (i : E.I₀), Presieve.IsSheafFor F ((Sieve.generate R).pullback (E.f i)).arrows)
    (h₂ : ∀ ⦃i j : E.I₀⦄ (k : E.I₁ i j),
      Presieve.IsSeparatedFor F ((Sieve.generate R).pullback (E.p₁ k ≫ E.f i)).arrows) :
    Presieve.IsSheafFor F R := by
  rw [Presieve.isSheafFor_iff_generate]
  exact E.isSheafFor_sieve_of_pullback hF h₁ h₂

end CategoryTheory.GrothendieckTopology.OneHypercover

