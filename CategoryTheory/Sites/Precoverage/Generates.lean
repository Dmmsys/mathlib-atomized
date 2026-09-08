/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Closed
public import Mathlib.CategoryTheory.Sites.Coverage
public import Mathlib.CategoryTheory.Sites.Precoverage.Subsheaf
public import Mathlib.Logic.Small.Set

/-!
# Generators of a Grothendieck topology

Let `K` be a precoverage and `J` a Grothendieck topology on a category `C`. We
say `K` generates `J` if for every presheaf `F` on `C`, it is a sheaf for `J` if and only
if it is a sheaf for every covering in `K`.

If `K` generates `J`, then `J` is the smallest Grothendieck topology containing `K`. The converse
only holds if `K` is a coverage or a pretopology.

## Implementation details

For `C : Type u` and `Category.{v} C`, the definition of `Precoverage.Generates` quantifies over
presheafs `Cᵒᵖ ⥤ Type max u v`. We then show that this implies that the condition holds
for all presheafs `Cᵒᵖ ⥤ Type w`.
-/

@[expose] public section

universe t t' w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {A : Type*} [Category* A]
  {K : Precoverage C} {J : GrothendieckTopology C}

namespace Precoverage

/-- A precoverage `K` generates the topology `J` if a presheaf on `C` is a sheaf
for `K` if and only if it is a sheaf for `J`. -/
/-
**CategoryTheory.Precoverage.Generates** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheo
ry.Precoverage`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     CategoryT
heory.Precoverage C → CategoryTheory.GrothendieckTopology C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A precoverage `K` generates the topology `J` if a presheaf on `C` is a sheaf
for `K` if and only if it is a sheaf for `J`.
-/
structure Generates (K : Precoverage C) (J : GrothendieckTopology C) : Prop where
  le_toPrecoverage : K ≤ J.toPrecoverage
  isSheaf_of_forall_max (F : Cᵒᵖ ⥤ Type (max u v)) (H : ∀ ⦃X : C⦄, ∀ R ∈ K X, R.IsSheafFor F) :
    Presieve.IsSheaf J F

variable {K : Precoverage C} {J : GrothendieckTopology C}
/-
**CategoryTheory.Precoverage.Generates.generate_mem** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Precoverage.Generates`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {K : CategoryTheo
ry.Precoverage C}   {J : CategoryTheory.GrothendieckTopology C},   K.Generates J
 → ∀ {X : C} {R : CategoryTheory.Presieve X}, R ∈ K.coverings X → CategoryTheory
.Sieve.generate R ∈ J X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Precoverage.Generates.le_toPrecoverage`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] {K : CategoryTheory.Precoverage C}   {J 
: CategoryTheory.GrothendieckTopology C}, K…
-/
lemma Generates.generate_mem (H : K.Generates J) {X : C} {R : Presieve X} (h : R ∈ K X) :
    .generate R ∈ J X :=
  H.le_toPrecoverage _ h
/-
**CategoryTheory.Precoverage.Generates.isSheaf_of_forall_aux** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Precoverage`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma Generates.isSheaf_of_forall_aux (h : K.Generates J) (F : Cᵒᵖ ⥤ Type w)
    (H : ∀ ⦃X : C⦄, ∀ R ∈ K X, Presieve.IsSheafFor F R)
    [∀ (Z : C), _root_.Small.{max u v} (F.obj (.op Z))] :
    Presieve.IsSheaf J F := by
  intro X S hS
  let F' : Cᵒᵖ ⥤ Type max u v := FunctorToTypes.shrink F
  let e (X : C) : F.obj (.op X) ≃ F'.obj (.op X) := equivShrink _
  have he (X Y : C) (f : X ⟶ Y) (x : F.obj (.op Y)) :
      (e X) (F.map f.op x) = F'.map f.op (e Y x) := by
    simp [e, F']
  rw [Presieve.isSheafFor_iff_of_nat_equiv e he] at ⊢
  refine h.isSheaf_of_forall_max F' (fun X R hR ↦ ?_) _ hS
  rw [← Presieve.isSheafFor_iff_of_nat_equiv e he]
  exact H _ hR

/-- If `K` generates `J`, then any presheaf `Cᵒᵖ ⥤ Type w` that satisfies the sheaf
condition for all `K`-coverings, is a `J`-sheaf. -/
/-
**CategoryTheory.Precoverage.Generates.isSheaf_of_forall** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Precoverage.Generates`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {K : CategoryTheo
ry.Precoverage C}   {J : CategoryTheory.GrothendieckTopology C},   K.Generates J
 →     ∀ (F : CategoryTheory.Functor Cᵒᵖ (Type w)),       (∀ ⦃X : C⦄, ∀ R ∈ K.co
verings X, CategoryTheory.Presieve.IsSheafFor F R) → CategoryTheory.Presieve.IsS
heaf J F
参数：F : CategoryTheory.Functor Cᵒᵖ (Type w)；∀ ⦃X : C⦄, ∀ R ∈ K.coverings X, Categ
oryTheory.Presieve.IsSheafFor F R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isS
heafFor`：isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor : (IsSeparatedF
or P R ∧ forall x : FamilyOfElements P R, x.Compatible -> exists t, x…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `CategoryTheory.Precoverage.small_subsheafify_of_small`：small_subsheafify
_of_small (hF : forall ⦃X : C⦄ (R : Presieve X), R in K X -> Presieve.IsSheafFor
 F R) (𝒮 : forall Z : C, Set (F.obj (.op Z)…
· 使用定理 `CategoryTheory.instSmallHomOfLocallySmall`：∀ (C : Type u) [inst : Catego
ryTheory.Category.{v, u} C] [CategoryTheory.LocallySmall.{w, v, u} C] (X Y : C),
   Small.{w, v} (X ⟶ Y)
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
· 使用定理 `_private.Mathlib.CategoryTheory.Sites.Precoverage.Generates.0.CategoryTh
eory.Precoverage.Generates.isSheaf_of_forall_aux`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {K : CategoryTheory.Precoverage C}   {J : CategoryThe
ory.GrothendieckTopology C},  …
· 使用引理 `CategoryTheory.Precoverage.isSheafFor_subsheafify`：isSheafFor_subsheafif
y (𝒮 : forall Z : C, Set (F.obj (.op Z))) {X : C} {R : Presieve X} (h : R in K X
) (h' : R.IsSheafFor F) : R.IsSheafFor …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.isSeparatedFor`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)}
 {X : C}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.Presieve.FamilyOfElements.IsAmalgamation.of_mono`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P Q : CategoryTheory.Funct
or Cᵒᵖ (Type w)} {X : C}   {R : CategoryTheory.Presie…
· 使用定理 `CategoryTheory.Subfunctor.instMonoFunctorTypeι`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {F : CategoryTheory.Functor C (Type w)}   (G : 
CategoryTheory.Subfunctor F), Catego…
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `CategoryTheory.Presieve.FamilyOfElements.Compatible.of_mono`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P Q : CategoryTheory.Functor C
ᵒᵖ (Type w)} {X : C}   {R : CategoryTheory.Presie…
· 使用定理 `CategoryTheory.Presieve.FamilyOfElements.IsAmalgamation.map`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P Q : CategoryTheory.Functor C
ᵒᵖ (Type w)} {X : C}   {R : CategoryTheory.Presie…

--- 原说明 ---
If `K` generates `J`, then any presheaf `Cᵒᵖ ⥤ Type w` that satisfies the sheaf
condition for all `K`-coverings, is a `J`-sheaf.
-/
lemma Generates.isSheaf_of_forall (h : K.Generates J) (F : Cᵒᵖ ⥤ Type w)
    (H : ∀ ⦃X : C⦄, ∀ R ∈ K X, Presieve.IsSheafFor F R) :
    Presieve.IsSheaf J F := by
  /- By assumption, the statement holds for `w = max u v`. The idea of the proof is
  to construct a suitable `Type max u v` valued subsheaf of `F` for each covering sieve `S` in
  `J` and every family of sections over `S` to check the necessary conditions.
  We explain existence below, uniqueness works similarly. -/
  intro X S hS
  rw [← Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  refine ⟨?_, ?_⟩
  · intro x t₁ t₂ ht₁ ht₂
    let 𝒮 (Z : C) : Set (F.obj (.op Z)) :=
      .range (fun (g : { g : Z ⟶ X | S.arrows g }) ↦ x _ g.2) ∪
      .range (fun (g : Z ⟶ X) ↦ F.map g.op t₁) ∪ .range (fun (g : Z ⟶ X) ↦ F.map g.op t₂)
    let Q : Subfunctor F := K.subsheafify 𝒮
    have (Z : C) : _root_.Small.{max u v} (Q.toFunctor.obj (Opposite.op Z)) :=
      small_subsheafify_of_small H _ inferInstance _
    have hQ : Presieve.IsSheaf J Q.toFunctor :=
      h.isSheaf_of_forall_aux _ fun X R hR ↦ isSheafFor_subsheafify _ hR (H _ hR)
    let x' : S.arrows.FamilyOfElements Q.toFunctor :=
      fun Z g hg ↦ ⟨x g hg, .base <| .inl <| .inl ⟨⟨g, hg⟩, rfl⟩⟩
    have ht₁' : t₁ ∈ Q.obj (.op X) := .base (.inl <| .inr ⟨𝟙 _, by simp⟩)
    have ht₂' : t₂ ∈ Q.obj (.op X) := .base (.inr ⟨𝟙 _, by simp⟩)
    have : (⟨t₁, ht₁'⟩ : Q.obj _) = ⟨t₂, ht₂'⟩ :=
      (hQ _ hS).isSeparatedFor x' ⟨_, ht₁'⟩ ⟨_, ht₂'⟩ (.of_mono Q.ι ht₁) (.of_mono Q.ι ht₂)
    simp_all
  · -- Let `x` be a compatible family of elements over `S`. We need to show it glues.
    intro x hx
    -- Let `𝒮` be the family of subsets consisting of the family of elements `x`.
    let 𝒮 (Z : C) := Set.range (fun (g : { g : Z ⟶ X | S.arrows g }) ↦ x _ g.2)
    /- Let `Q` be the smallest `K`-subsheaf of `K` containing `𝒮`. This is `max u v`-small, because
    `𝒮` is `max u v`-small. -/
    let Q : Subfunctor F := K.subsheafify 𝒮
    have (Z : C) : _root_.Small.{max u v} (Q.toFunctor.obj (Opposite.op Z)) :=
      small_subsheafify_of_small H _ inferInstance _
    have hQ : Presieve.IsSheaf J Q.toFunctor :=
      h.isSheaf_of_forall_aux _ fun X R hR ↦ isSheafFor_subsheafify _ hR (H _ hR)
    /- By assumption, `Q` is a `J`-sheaf, so the family of sections `x` glues and gives rise
    to an amalgamation of `x` in `F`. -/
    obtain ⟨t, ht, _⟩ := hQ _ hS (fun Z g hg ↦ ⟨x g hg, .base ⟨⟨g, hg⟩, rfl⟩⟩) (.of_mono Q.ι hx)
    exact ⟨t.val, ht.map Q.ι⟩

/-- If `K` generates `J`, then any presheaf is a sheaf if and only if it is a sheaf
for all `K`-covers. -/
/-
**CategoryTheory.Precoverage.Generates.isSheaf_type_iff** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Precoverage.Generates`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {K : CategoryTheo
ry.Precoverage C}   {J : CategoryTheory.GrothendieckTopology C},   K.Generates J
 →     ∀ {F : CategoryTheory.Functor Cᵒᵖ (Type w)},       CategoryTheory.Presiev
e.IsSheaf J F ↔ ∀ ⦃X : C⦄, ∀ R ∈ K.coverings X, CategoryTheory.Presieve.IsSheafF
or F R
参数：Type w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presieve.isSheafFor_iff_generate`：isSheafFor_iff_generate
 (R : Presieve X) : IsSheafFor P R ↔ IsSheafFor P (generate R : Presieve X)
· 使用定理 `CategoryTheory.Precoverage.Generates.le_toPrecoverage`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] {K : CategoryTheory.Precoverage C}   {J 
: CategoryTheory.GrothendieckTopology C}, K…
· 使用定理 `CategoryTheory.Precoverage.Generates.isSheaf_of_forall`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {K : CategoryTheory.Precoverage C}   {J
 : CategoryTheory.GrothendieckTopology C},  …

--- 原说明 ---
If `K` generates `J`, then any presheaf is a sheaf if and only if it is a sheaf
for all `K`-covers.
-/
lemma Generates.isSheaf_type_iff (H : K.Generates J) {F : Cᵒᵖ ⥤ Type w} :
    Presieve.IsSheaf J F ↔ ∀ ⦃X : C⦄, ∀ R ∈ K X, Presieve.IsSheafFor F R := by
  refine ⟨fun h X R hR ↦ ?_, fun h ↦ H.isSheaf_of_forall _ h⟩
  rw [Presieve.isSheafFor_iff_generate]
  exact h _ (H.le_toPrecoverage _ hR)

/--
If `K` generates `J`, then `J` is equal to the smallest Grothendieck topology containing `K`.
The converse is false, but holds if `K` is a coverage, see `CategoryTheory.Coverage.generates_iff`.
-/
/-
**CategoryTheory.Precoverage.Generates.toGrothendieck_eq** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Precoverage.Generates`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {K : CategoryTheo
ry.Precoverage C}   {J : CategoryTheory.GrothendieckTopology C}, K.Generates J →
 K.toGrothendieck = J
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Precoverage.toGrothendieck_le_iff_le_toPrecoverage`：toGro
thendieck_le_iff_le_toPrecoverage : K.toGrothendieck <= J ↔ K <= J.toPrecoverage
· 使用定理 `CategoryTheory.Precoverage.Generates.le_toPrecoverage`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] {K : CategoryTheory.Precoverage C}   {J 
: CategoryTheory.GrothendieckTopology C}, K…
· 使用定理 `CategoryTheory.le_topology_of_closedSieves_isSheaf`：le_topology_of_close
dSieves_isSheaf {J₁ J₂ : GrothendieckTopology C} (h : Presieve.IsSheaf J₁ (Funct
or.closedSieves J₂).toFunctor) : J₁ <= J…
· 使用定理 `CategoryTheory.Precoverage.Generates.isSheaf_type_iff`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] {K : CategoryTheory.Precoverage C}   {J 
: CategoryTheory.GrothendieckTopology C},  …
· 使用定理 `CategoryTheory.Presieve.isSheafFor_iff_generate`：isSheafFor_iff_generate
 (R : Presieve X) : IsSheafFor P R ↔ IsSheafFor P (generate R : Presieve X)
· 使用定理 `CategoryTheory.classifier_isSheaf`：classifier_isSheaf : Presieve.IsSheaf
 J₁ (Functor.closedSieves J₁).toFunctor
· 使用引理 `CategoryTheory.Precoverage.generate_mem_toGrothendieck`：generate_mem_toG
rothendieck {X : C} {R : Presieve X} (hR : R in J X) : Sieve.generate R in J.toG
rothendieck X

--- 原说明 ---
If `K` generates `J`, then `J` is equal to the smallest Grothendieck topology co
ntaining `K`.
The converse is false, but holds if `K` is a coverage, see `CategoryTheory.Cover
age.generates_iff`.
-/
lemma Generates.toGrothendieck_eq (H : K.Generates J) : K.toGrothendieck = J := by
  refine le_antisymm ?_ ?_
  · rw [toGrothendieck_le_iff_le_toPrecoverage]
    exact H.le_toPrecoverage
  · apply CategoryTheory.le_topology_of_closedSieves_isSheaf
    rw [H.isSheaf_type_iff]
    intro X R hR
    rw [Presieve.isSheafFor_iff_generate]
    exact classifier_isSheaf K.toGrothendieck _ (K.generate_mem_toGrothendieck hR)
/-
**CategoryTheory.Precoverage.Generates.isSheaf_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Precoverage.Generates`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {A : Type u_1} [i
nst_1 : CategoryTheory.Category.{v_1, u_1} A]   {K : CategoryTheory.Precoverage 
C} {J : CategoryTheory.GrothendieckTopology C},   K.Generates J →     ∀ {F : Cat
egoryTheory.Functor Cᵒᵖ A},       CategoryTheory.Presheaf.IsSheaf J F ↔         
∀ ⦃X : C⦄,           ∀ R ∈ K.coverings X,             ∀ (M : A), CategoryTheory.
Presieve.IsSheafFor (F.comp (CategoryTheory.coyoneda.obj (Opposite.op M))) R
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Generates.isSheaf_iff (H : K.Generates J) {F : Cᵒᵖ ⥤ A} :
    Presheaf.IsSheaf J F ↔ ∀ ⦃X : C⦄, ∀ R ∈ K X, ∀ (M : A),
      Presieve.IsSheafFor (F ⋙ coyoneda.obj (.op M)) R := by
  grind [Presheaf.IsSheaf, H.isSheaf_type_iff]

end Precoverage

/-- If `K` is a coverage, it generates the smallest Grothendieck topology containing `K`. -/
/-
**CategoryTheory.Coverage.generates_toGrothendieck** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Coverage`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (K : CategoryTheo
ry.Coverage C), K.Generates K.toGrothendieck
参数：K : CategoryTheory.Coverage C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Precoverage.toGrothendieck_le_iff_le_toPrecoverage`：toGro
thendieck_le_iff_le_toPrecoverage : K.toGrothendieck <= J ↔ K <= J.toPrecoverage
· 使用定理 `CategoryTheory.Coverage.toGrothendieck_toPrecoverage`：∀ {C : Type u_1} [
inst : CategoryTheory.Category.{v_1, u_1} C] (J : CategoryTheory.Coverage C),   
J.toGrothendieck = J.toGrothendieck
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `CategoryTheory.Presieve.isSheaf_coverage`：isSheaf_coverage (K : Coverage
 C) (P : Cᵒᵖ ⥤ Type*) : Presieve.IsSheaf K.toGrothendieck P ↔ (forall {X : C} (R
 : Presieve X), R in K X -> Pr…

--- 原说明 ---
If `K` is a coverage, it generates the smallest Grothendieck topology containing
 `K`.
-/
lemma Coverage.generates_toGrothendieck (K : Coverage C) : K.Generates K.toGrothendieck where
  le_toPrecoverage := by
    rw [← Precoverage.toGrothendieck_le_iff_le_toPrecoverage, ← toGrothendieck_toPrecoverage]
  isSheaf_of_forall_max F h := by rwa [Presieve.isSheaf_coverage]
/-
**CategoryTheory.Coverage.generates_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Coverage`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheo
ry.GrothendieckTopology C}   {K : CategoryTheory.Coverage C}, K.Generates J ↔ K.
toGrothendieck = J
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Coverage.toGrothendieck_toPrecoverage`：∀ {C : Type u_1} [
inst : CategoryTheory.Category.{v_1, u_1} C] (J : CategoryTheory.Coverage C),   
J.toGrothendieck = J.toGrothendieck
· 使用定理 `CategoryTheory.Precoverage.Generates.toGrothendieck_eq`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {K : CategoryTheory.Precoverage C}   {J
 : CategoryTheory.GrothendieckTopology C}, K…
· 使用定理 `CategoryTheory.Coverage.generates_toGrothendieck`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] (K : CategoryTheory.Coverage C), K.Generates 
K.toGrothendieck
-/
lemma Coverage.generates_iff {K : Coverage C} : K.Generates J ↔ K.toGrothendieck = J := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rw [← Coverage.toGrothendieck_toPrecoverage]
    exact h.toGrothendieck_eq
  · rintro rfl
    exact Coverage.generates_toGrothendieck _

end CategoryTheory

