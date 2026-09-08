/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.IsSheafFor
public import Mathlib.CategoryTheory.Sites.Precoverage

/-!
# Sheafification of subpresheafs for precoverages

Let `K` be a precoverage. In this file we define the `K`-sheafification of a subpresheaf.
More generally, for a family of subsets `𝒮` of sections of a sheaf `F`, we construct
the smallest subsheaf of `F` containing `𝒮`.

## Main declarations

- `CategoryTheory.Precoverage.subsheafify`: `K`-sheafification of family of sets `𝒮` in a presheaf
  `F`. This is only a sheaf if `F` itself is a sheaf.
- `CategoryTheory.Precoverage.small_subsheafify_of_small`: If all the sets in the family `𝒮`
  are small, then the `K`-sheafification is again small.

## TODOs

- Relate `Precoverage.subsheafify K` with `Subfunctor.sheafify` for the Grothendieck topology
  `Precoverage.toGrothendieck K`.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {K : Precoverage C}

namespace Precoverage

variable {F : Cᵒᵖ ⥤ Type w}

/-- Closure of a family of elements of a presheaf under restriction and gluing of
sections over coverings in `K`. -/
/-
**CategoryTheory.Precoverage.SubsheafClosure** 是 Mathlib 中的一个归纳类型，位于命名空间 `Catego
ryTheory.Precoverage`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     CategoryT
heory.Precoverage C →       {F : CategoryTheory.Functor Cᵒᵖ (Type w)} →         
((Z : C) → Set (F.obj (Opposite.op Z))) → (Z : C) → F.obj (Opposite.op Z) → Prop
参数：Type w；(Z : C) → Set (F.obj (Opposite.op Z))；Z : C；Opposite.op Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Closure of a family of elements of a presheaf under restriction and gluing of
sections over coverings in `K`.
-/
inductive SubsheafClosure (K : Precoverage C) {F : Cᵒᵖ ⥤ Type w}
    (𝒮 : ∀ Z : C, Set (F.obj (.op Z))) :
    ∀ Z : C, F.obj (.op Z) → Prop where
  /-- Element of the initial family. -/
  | base {Z : C} {a : F.obj (.op Z)} : a ∈ 𝒮 Z → K.SubsheafClosure 𝒮 Z a
  /-- Restriction of an element in the closure along a morphism. -/
  | restrict {Z W : C} (h : Z ⟶ W) {a : F.obj (.op W)} :
      K.SubsheafClosure 𝒮 W a → K.SubsheafClosure 𝒮 Z (F.map h.op a)
  /-- Gluing of sections in the closure. -/
  | amalgamate {Z : C} {R : Presieve Z} (hR : R ∈ K Z)
      {y : Presieve.FamilyOfElements F R} (hy : y.Compatible)
      (hmem : ∀ ⦃W : C⦄ (r : W ⟶ Z) (hr : R r), K.SubsheafClosure 𝒮 W (y r hr))
      {t : F.obj (.op Z)} (ht : y.IsAmalgamation t) : K.SubsheafClosure 𝒮 Z t

variable (K) in
/-- The `K`-sheafification of a family of sets `𝒮` in `F`: If `F` is
a sheaf for `K`, this is the smallest subsheaf of `F` containing `𝒮`. -/
@[simps]
/-
**CategoryTheory.Precoverage.subsheafify** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Precoverage`。
形式化陈述：subsheafify (𝒮 : forall Z : C, Set (F.obj (.op Z))) : Subfunctor F where o
bj U
参数：𝒮 : forall Z : C, Set (F.obj (.op Z))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `K`-sheafification of a family of sets `𝒮` in `F`: If `F` is
a sheaf for `K`, this is the smallest subsheaf of `F` containing `𝒮`.
-/
def subsheafify (𝒮 : ∀ Z : C, Set (F.obj (.op Z))) : Subfunctor F where
  obj U := { x | K.SubsheafClosure 𝒮 U.unop x }
  map _ _ ht := .restrict _ ht

variable (𝒮 : ∀ Z : C, Set (F.obj (.op Z)))

/-- If `F` is a sheaf for `R` and `R ∈ K X`, then the `K`-sheafification of `𝒮` is a
sheaf for `R`. -/
/-
**CategoryTheory.Precoverage.isSheafFor_subsheafify** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Precoverage`。
形式化陈述：isSheafFor_subsheafify (𝒮 : forall Z : C, Set (F.obj (.op Z))) {X : C} {R 
: Presieve X} (h : R in K X) (h' : R.IsSheafFor F) : R.IsSheafFor (K.subsheafify
 𝒮).toFunctor
参数：𝒮 : forall Z : C, Set (F.obj (.op Z))；h : R in K X；h' : R.IsSheafFor F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isS
heafFor`：isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor : (IsSeparatedF
or P R ∧ forall x : FamilyOfElements P R, x.Compatible -> exists t, x…
· 使用定理 `CategoryTheory.Presieve.IsSeparatedFor.of_mono`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {P Q : CategoryTheory.Functor Cᵒᵖ (Type w)} 
{X : C}   {R : CategoryTheory.Presie…
· 使用定理 `CategoryTheory.Subfunctor.instMonoFunctorTypeι`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {F : CategoryTheory.Functor C (Type w)}   (G : 
CategoryTheory.Subfunctor F), Catego…
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.isSeparatedFor`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)}
 {X : C}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.Presieve.FamilyOfElements.Compatible.map`：∀ {C : Type u₁}
 [inst : CategoryTheory.Category.{v₁, u₁} C] {P Q : CategoryTheory.Functor Cᵒᵖ (
Type w)} {X : C}   {R : CategoryTheory.Presie…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `CategoryTheory.Presieve.FamilyOfElements.IsAmalgamation.of_mono`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {P Q : CategoryTheory.Funct
or Cᵒᵖ (Type w)} {X : C}   {R : CategoryTheory.Presie…

--- 原说明 ---
If `F` is a sheaf for `R` and `R ∈ K X`, then the `K`-sheafification of `𝒮` is a
sheaf for `R`.
-/
lemma isSheafFor_subsheafify (𝒮 : ∀ Z : C, Set (F.obj (.op Z))) {X : C} {R : Presieve X}
    (h : R ∈ K X) (h' : R.IsSheafFor F) :
    R.IsSheafFor (K.subsheafify 𝒮).toFunctor := by
  let G := K.subsheafify 𝒮
  rw [← Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  refine ⟨.of_mono G.ι h'.isSeparatedFor, fun x hx ↦ ?_⟩
  obtain ⟨t, ht, uniq⟩ := h' (x.map G.ι) (hx.map G.ι)
  exact ⟨⟨t, .amalgamate h (hx.map G.ι) (fun _ _ hr ↦ (x _ hr).property) ht⟩, .of_mono _ ht⟩

namespace SmallConstruction

variable (K) in
/-- Upper bound for the sections of `Precoverage.subsheafify`: If for every `X : C`,
the underlying type of `𝒮 X` embeds into `ι X`, the sections of `K.subsheafify 𝒮`
on `X` embed into `Witness K ι X`. -/
/-
**CategoryTheory.Precoverage.SmallConstruction.Witness** 是 Mathlib 中的一个归纳类型，位于命名
空间 `CategoryTheory.Precoverage.SmallConstruction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Upper bound for the sections of `Precoverage.subsheafify`: If for every `X : C`,
the underlying type of `𝒮 X` embeds into `ι X`, the sections of `K.subsheafify 𝒮
`
on `X` embed into `Witness K ι X`.
-/
private inductive Witness (ι : C → Type w) : C → Type max w u v where
  | base (X : C) : ι X → Witness ι X
  | restrict {X Y : C} (f : X ⟶ Y) : Witness ι Y → Witness ι X
  /-- Family of elements over a covering in `K`. Note that it is not necessarily compatible. -/
  | amalgamate {X : C} {R : Presieve X} (hR : R ∈ K X)
      (h : ∀ ⦃W⦄ (r : W ⟶ X), R r → Witness ι W) : Witness ι X

/-- Realization of a term of `Witness K ι X` as a section of `F` over `X`. By
construction, the sections will lie in the subsheaf `K.subsheafify 𝒮`.
This takes values in `Option`, because not every term constructed from
the `Witness.amalgamate` constructor corresponds to a compatible family. -/
private noncomputable
/-
**CategoryTheory.Precoverage.SmallConstruction.Witness.eval** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Precoverage.SmallConstruction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Witness.eval (hF : ∀ ⦃X : C⦄ (R : Presieve X), R ∈ K X → Presieve.IsSheafFor F R)
    (ι : C → Type max u v) (t : ∀ X, ι X → F.obj (.op X)) :
    {X : C} → Witness K ι X → Option (F.obj (.op X))
  | _, .base X i => t _ i
  | _, .restrict f i => do F.map f.op (← eval hF _ t i)
  | _, .amalgamate (R := R) hR h =>
    open scoped Classical in
    let vals := fun W (r : W ⟶ _) (hr : R r) ↦ eval hF _ t (h r hr)
    /- If all elements of the family are evaluatable and the resulting family is compatible, take
    the glued section. Otherwise, return `none`. -/
    if hall : ∀ (W : C) (r : W ⟶ _) (hr : R r), (vals W r hr).isSome then
      let y : R.FamilyOfElements F := fun _ _ hr ↦ (vals _ _ _).get (hall _ _ hr)
      if hy : y.Compatible then some (hF _ hR _ hy).choose else none
    else none

end SmallConstruction

open SmallConstruction in
/-- If `𝒮 Z` is `max u v`-small for every `Z`, then the subsheaf generated by `𝒮 Z` has
`max u v`-small sections. -/
/-
**CategoryTheory.Precoverage.small_subsheafify_of_small** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Precoverage`。
形式化陈述：small_subsheafify_of_small (hF : forall ⦃X : C⦄ (R : Presieve X), R in K X
 -> Presieve.IsSheafFor F R) (𝒮 : forall Z : C, Set (F.obj (.op Z))) (h : forall
 Z, _root_.Small.{max u v} (𝒮 Z)) : FunctorToTypes.Small.{max u v} (K.subsheafif
y 𝒮).toFunctor
参数：hF : forall ⦃X : C⦄ (R : Presieve X), R in K X -> Presieve.IsSheafFor F R；𝒮 :
 forall Z : C, Set (F.obj (.op Z))；h : forall Z, _root_.Small.{max u v} (𝒮 Z)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Option.get.congr_simp`：∀ {α : Type u} (o o_1 : Option α) (e_o : o = o_1)
 (a : o.isSome = true), o.get a = o_1.get ⋯
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `dite.congr_simp`：∀ {α : Sort u} (c : Prop) {h : Decidable c} [h_1 : Deci
dable c] (t t_1 : c → α),   t = t_1 → ∀ (e e_1 : ¬c → α), e = e_1 → dite c t e =
 dite…
· 使用定理 `Exists.choose.congr_simp`：∀ {α : Sort u_1} {p p_1 : α → Prop} (e_p : p =
 p_1) (P : ∃ a, p a), P.choose = ⋯.choose
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Option.some_injective`：some_injective (α : Type*) : Function.Injective (
@some α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.CategoryTheory.Sites.Precoverage.Subsheaf.0.CategoryThe
ory.Precoverage.SmallConstruction.Witness.eval.congr_simp`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {K : CategoryTheory.Precoverage C}   {F : Ca
tegoryTheory.Functor Cᵒᵖ (Type w)}   (h…
· 使用定理 `small_of_injective`：small_of_injective {α : Type v} {β : Type w} [Small.
{u} β] {f : α -> β} (hf : Function.Injective f) : Small.{u} α
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α

--- 原说明 ---
If `𝒮 Z` is `max u v`-small for every `Z`, then the subsheaf generated by `𝒮 Z` 
has
`max u v`-small sections.
-/
lemma small_subsheafify_of_small
    (hF : ∀ ⦃X : C⦄ (R : Presieve X), R ∈ K X → Presieve.IsSheafFor F R)
    (𝒮 : ∀ Z : C, Set (F.obj (.op Z))) (h : ∀ Z, _root_.Small.{max u v} (𝒮 Z)) :
    FunctorToTypes.Small.{max u v} (K.subsheafify 𝒮).toFunctor := by
  rintro ⟨X⟩
  let ι (X : C) := Shrink.{max u v} (𝒮 X)
  let t (X : C) (i : ι X) : F.obj (Opposite.op X) := ((equivShrink _).symm i).val
  have (x : F.obj (.op X)) (hx : K.SubsheafClosure 𝒮 X x) :
      ∃ (i : Witness K ι X), Witness.eval hF _ t i = x := by
    induction hx with
    | base ha => exact ⟨.base _ (equivShrink _ ⟨_, ha⟩), by grind [Witness.eval]⟩
    | restrict f ha ih =>
      obtain ⟨i, hi⟩ := ih
      use .restrict f i
      grind [Witness.eval]
    | amalgamate hR hy hmem ht ih =>
      choose x hx using ih
      exact ⟨.amalgamate hR x, by simp [Witness.eval, hx]; grind⟩
  choose i hi using this
  have : Function.Injective (fun x : { x // K.SubsheafClosure 𝒮 X x } ↦ i x x.prop) := by
    intro x y hxy
    ext
    apply Option.some_injective
    simp [← hi _ x.prop, ← hi _ y.prop, hxy]
  exact small_of_injective this

end Precoverage

end CategoryTheory

