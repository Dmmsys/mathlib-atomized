/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Limits.ColimitLimit
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.CategoryTheory.Products.Bifunctor
public import Mathlib.Data.Countable.Small

/-!
# Filtered colimits commute with finite limits.

We show that for a functor `F : J × K ⥤ Type v`, when `J` is finite and `K` is filtered,
the universal morphism `colimitLimitToLimitColimit F` comparing the
colimit (over `K`) of the limits (over `J`) with the limit of the colimits is an isomorphism.

(In fact, to prove that it is injective only requires that `J` has finitely many objects.)

## References
* Borceux, Handbook of categorical algebra 1, Theorem 2.13.4
* [Stacks: Filtered colimits](https://stacks.math.columbia.edu/tag/002W)
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

-- Various pieces of algebra that have previously been spuriously imported here:
assert_not_exists map_ne_zero MonoidWithZero

universe w v₁ v₂ v u₁ u₂ u

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits.Types
  CategoryTheory.Limits.Types.FilteredColimit CategoryTheory.Functor

namespace CategoryTheory.Limits

section

variable {J : Type u₁} {K : Type u₂} [Category.{v₁} J] [Category.{v₂} K] [Small.{v} K]

/-- `(G ⋙ lim).obj j` = `limit (G.obj j)` definitionally, so this
is just a variant of `limit_ext'`. -/
/-
**CategoryTheory.Limits.comp_lim_obj_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：∀ {J : Type u₁} {K : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} J] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} K]   [inst_2 : Small.{v, u₂} K] {j : 
J} {G : CategoryTheory.Functor J (CategoryTheory.Functor K (Type v))}   (x y : (
G.comp CategoryTheory.Limits.lim).obj j),   (∀ (k : K),       (CategoryTheory.Co
ncreteCategory.hom (CategoryTheory.Limits.limit.π (G.obj j) k)) x =         (Cat
egoryTheory.ConcreteCategory.hom (CategoryTheory.Limits.limit.π (G.obj j) k)) y)
 →     x = y
参数：CategoryTheory.Functor K (Type v)；x y : (G.comp CategoryTheory.Limits.lim).ob
j j；∀ (k : K),       (CategoryTheory.ConcreteCategory.hom (CategoryTheory.Limits
.limit.π (G.obj j) k)) x =         (CategoryTheory.ConcreteCategory.hom (Categor
yTheory.Limits.limit.π (G.obj j) k)) y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Types.hasLimitsOfShape`：∀ {J : Type v} [inst : Cat
egoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasLimi
tsOfShape J (Type u)
· 使用定理 `CategoryTheory.Limits.Types.limit_ext`：limit_ext (x y : limit F) (w : fo
rall j, limit.π F j x = limit.π F j y) : x = y
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
`(G ⋙ lim).obj j` = `limit (G.obj j)` definitionally, so this
is just a variant of `limit_ext'`.
-/
@[ext] lemma comp_lim_obj_ext {j : J} {G : J ⥤ K ⥤ Type v} (x y : (G ⋙ lim).obj j)
    (w : ∀ (k : K), limit.π (G.obj j) k x = limit.π (G.obj j) k y) : x = y :=
  limit_ext _ x y w

variable (F : J × K ⥤ Type v)

open CategoryTheory.Prod

variable [IsFiltered K]

section

/-!
Injectivity doesn't need that we have finitely many morphisms in `J`,
only that there are finitely many objects.
-/

variable [Finite J]

set_option backward.isDefEq.respectTransparency.types false in
/-- This follows the proof from
* Borceux, Handbook of categorical algebra 1, Theorem 2.13.4
-/
/-
**CategoryTheory.Limits.colimitLimitToLimitColimit_injective** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Limits`。
形式化陈述：colimitLimitToLimitColimit_injective : Function.Injective (colimitLimitToL
imitColimit F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `CategoryTheory.Limits.Types.hasLimitsOfShape`：∀ {J : Type v} [inst : Cat
egoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasLimi
tsOfShape J (Type u)
· 使用定理 `Countable.toSmall`：∀ (α : Type v) [Countable α], Small.{w, v} α
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfShape`：∀ {J : Type v} [inst : C
ategoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasCo
limitsOfShape J (Type u)
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.Types.jointly_surjective'`：jointly_surjective' (x 
: colimit F) : exists (j : J) (y : F.obj j), colimit.ι F j y = x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.ι_colimitLimitToLimitColimit_π_apply`：∀ {J : Type 
u₁} {K : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} J] [inst_1 : Category
Theory.Category.{v₂, u₂} K]   {C : Type u} [inst…
· 使用定理 `CategoryTheory.ConcreteCategory.congr_arg`：congr_arg {X Y : C} (f : X ⟶ 
Y) {x x' : ToType X} (h : x = x') : f x = f x'
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CategoryTheory.IsFiltered.toIsFilteredOrEmpty`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFiltered C],   Category
Theory.IsFilteredOrEmpty C
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_union`：mem_union : a in s union t ↔ a in s ∨ a in t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `instSubsingleton`：∀ (p : Prop), Subsingleton p
· 使用定理 `CategoryTheory.IsFiltered.sup_exists`：sup_exists : exists (S : C) (T : f
orall {X : C}, X in O -> (X ⟶ S)), forall {X Y : C} (mX : X in O) (mY : Y in O) 
{f : X ⟶ Y}, (⟨X, Y, mX, m…
· 使用定理 `CategoryTheory.Limits.Types.colimit_sound'`：colimit_sound' {j j' : J} {x
 : F.obj j} {x' : F.obj j'} {j'' : J} (f : j ⟶ j'') (f' : j' ⟶ j'') (w : F.map f
 x = F.map f' x') : colimit.ι F …
· 使用定理 `CategoryTheory.Limits.comp_lim_obj_ext`：∀ {J : Type u₁} {K : Type u₂} [i
nst : CategoryTheory.Category.{v₁, u₁} J] [inst_1 : CategoryTheory.Category.{v₂,
 u₂} K]   [inst_2 : Small.{v…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
This follows the proof from
* Borceux, Handbook of categorical algebra 1, Theorem 2.13.4
-/
theorem colimitLimitToLimitColimit_injective :
    Function.Injective (colimitLimitToLimitColimit F) := by
  classical
    cases nonempty_fintype J
    -- Suppose we have two terms `x y` in the colimit (over `K`) of the limits (over `J`),
    -- and that these have the same image under `colimitLimitToLimitColimit F`.
    intro x y h
    -- These elements of the colimit have representatives somewhere:
    obtain ⟨kx, x, rfl⟩ := jointly_surjective' x
    obtain ⟨ky, y, rfl⟩ := jointly_surjective' y
    dsimp at x y
    -- Since the images of `x` and `y` are equal in a limit, they are equal componentwise
    -- (indexed by `j : J`),
    have h (j : J) :
        (colimit.ι ((curry.obj F).obj j) kx)
          ((limit.π ((curry.obj (swap K J ⋙ F)).obj kx) j) x) =
        (colimit.ι ((curry.obj F).obj j) ky)
          ((limit.π ((curry.obj (swap K J ⋙ F)).obj ky) j) y) := by
      simpa using! ConcreteCategory.congr_arg (limit.π (curry.obj F ⋙ colim) j) h
    -- and they are equations in a filtered colimit,
    -- so for each `j` we have some place `k j` to the right of both `kx` and `ky`
    simp only [colimit_eq_iff] at h
    let k j := (h j).choose
    let f : ∀ j, kx ⟶ k j := fun j => (h j).choose_spec.choose
    let g : ∀ j, ky ⟶ k j := fun j => (h j).choose_spec.choose_spec.choose
    -- where the images of the components of the representatives become equal:
    have w :
      ∀ j, F.map (𝟙 j ×ₘ f j) (limit.π ((curry.obj (swap K J ⋙ F)).obj kx) j x) =
          F.map (𝟙 j ×ₘ g j) (limit.π ((curry.obj (swap K J ⋙ F)).obj ky) j y) :=
      fun j => (h j).choose_spec.choose_spec.choose_spec
    -- We now use that `K` is filtered, picking some point to the right of all these
    -- morphisms `f j` and `g j`.
    let O : Finset K := Finset.univ.image k ∪ {kx, ky}
    have kxO : kx ∈ O := Finset.mem_union.mpr (Or.inr (by simp))
    have kyO : ky ∈ O := Finset.mem_union.mpr (Or.inr (by simp))
    have kjO : ∀ j, k j ∈ O := fun j => Finset.mem_union.mpr (Or.inl (by simp))
    let H : Finset (Σ' (X Y : K) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y) :=
      (Finset.univ.image fun j : J =>
          ⟨kx, k j, kxO, Finset.mem_union.mpr (Or.inl (by simp)), f j⟩) ∪
        Finset.univ.image fun j : J => ⟨ky, k j, kyO, Finset.mem_union.mpr (Or.inl (by simp)), g j⟩
    obtain ⟨S, T, W⟩ := IsFiltered.sup_exists O H
    have fH : ∀ j, (⟨kx, k j, kxO, kjO j, f j⟩ : Σ' (X Y : K) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y) ∈ H :=
      fun j =>
      Finset.mem_union.mpr
        (Or.inl
          (by
            simp only [true_and, Finset.mem_univ,
              Finset.mem_image]
            refine ⟨j, ?_⟩
            simp only))
    have gH :
      ∀ j, (⟨ky, k j, kyO, kjO j, g j⟩ : Σ' (X Y : K) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y) ∈ H :=
      fun j =>
      Finset.mem_union.mpr
        (Or.inr
          (by
            simp only [true_and, Finset.mem_univ,
              Finset.mem_image]
            refine ⟨j, ?_⟩
            simp only))
    -- Our goal is now an equation between equivalence classes of representatives of a colimit,
    -- and so it suffices to show those representative become equal somewhere, in particular at `S`.
    apply colimit_sound' (T kxO) (T kyO)
    -- We can check if two elements of a limit (in `Type`)
    -- are equal by comparing them componentwise.
    ext j
    -- Now it's just a calculation using `W` and `w`.
    simp only [Functor.comp_map]
    rw [← W _ _ (fH j), ← W _ _ (gH j)]
    simpa [-curry_obj_obj_obj] using! congrArg _ (w j)

end

end

section

variable {J : Type u₁} {K : Type u₂} [SmallCategory J] [Category.{v₂} K] [Small.{v} K]

variable [FinCategory J]

variable (F : J × K ⥤ Type v)

open CategoryTheory.Prod

variable [IsFiltered K]

set_option backward.isDefEq.respectTransparency false in
/-- This follows the proof from `Borceux, Handbook of categorical algebra 1, Theorem 2.13.4`
although with different names.
-/
/-
**CategoryTheory.Limits.colimitLimitToLimitColimit_surjective** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：colimitLimitToLimitColimit_surjective : Function.Surjective (colimitLimitT
oLimitColimit F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfShape`：∀ {J : Type v} [inst : C
ategoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasCo
limitsOfShape J (Type u)
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.Types.hasLimitsOfShape`：∀ {J : Type v} [inst : Cat
egoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasLimi
tsOfShape J (Type u)
· 使用定理 `Countable.toSmall`：∀ (α : Type v) [Countable α], Small.{w, v} α
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.Types.jointly_surjective'`：jointly_surjective' (x 
: colimit F) : exists (j : J) (y : F.obj j), colimit.ι F j y = x
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Bifunctor.diagonal'`：diagonal' (F : C × D ⥤ E) (X X' : C)
 (f : X ⟶ X') (Y Y' : D) (g : Y ⟶ Y') : F.map (f ×ₘ 𝟙 Y) ≫ F.map (𝟙 X' ×ₘ g) = F
.map (f ×ₘ g)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.colimit.w_apply`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   (F : CategoryTheory.F…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.Limits.limit.w_apply`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   (F : CategoryTheory.F…
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Limits.ι_colimMap`：∀ {J : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]  
 {F G : CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CategoryTheory.IsFiltered.toIsFilteredOrEmpty`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.IsFiltered C],   Category
Theory.IsFilteredOrEmpty C
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `CategoryTheory.Bifunctor.map_id_comp`：map_id_comp (F : C × D ⥤ E) (W : C
) {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) : F.map (𝟙 W ×ₘ (f ≫ g)) = F.map (𝟙 W ×ₘ f
) ≫ F.map (𝟙 W ×ₘ g)
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
（共 54 条，此处仅展示前 30 条）

--- 原说明 ---
This follows the proof from `Borceux, Handbook of categorical algebra 1, Theorem
 2.13.4`
although with different names.
-/
theorem colimitLimitToLimitColimit_surjective :
    Function.Surjective (colimitLimitToLimitColimit F) := by
  classical
    -- We begin with some element `x` in the limit (over J) over the colimits (over K),
    intro x
    -- This consists of some coherent family of elements in the various colimits,
    -- and so our first task is to pick representatives of these elements.
    have z := fun j => jointly_surjective' (limit.π (curry.obj F ⋙ Limits.colim) j x)
    -- `k : J ⟶ K` records where the representative of the
    -- element in the `j`-th element of `x` lives
    let k : J → K := fun j => (z j).choose
    -- `y j : F.obj (j, k j)` is the representative
    let y : ∀ j, F.obj (j, k j) := fun j => (z j).choose_spec.choose
    -- and we record that these representatives, when mapped back into the relevant colimits,
    -- are actually the components of `x`.
    have e : ∀ j,
        colimit.ι ((curry.obj F).obj j) (k j) (y j) = limit.π (curry.obj F ⋙ Limits.colim) j x :=
      fun j => (z j).choose_spec.choose_spec
    clear_value k y
    -- A little tidying up of things we no longer need.
    clear z
    -- As a first step, we use that `K` is filtered to pick some point `k' : K` above all the `k j`
    let k' : K := IsFiltered.sup (Finset.univ.image k) ∅
    -- and name the morphisms as `g j : k j ⟶ k'`.
    have g : ∀ j, k j ⟶ k' := fun j => IsFiltered.toSup (Finset.univ.image k) ∅ (by simp)
    clear_value k'
    -- Recalling that the components of `x`, which are indexed by `j : J`, are "coherent",
    -- in other words preserved by morphisms in the `J` direction,
    -- we see that for any morphism `f : j ⟶ j'` in `J`,
    -- the images of `y j` and `y j'`, when mapped to `F.obj (j', k')` respectively by
    -- `(f, g j)` and `(𝟙 j', g j')`, both represent the same element in the colimit.
    have w :
      ∀ {j j' : J} (f : j ⟶ j'),
        colimit.ι ((curry.obj F).obj j') k' (F.map (𝟙 j' ×ₘ g j') (y j')) =
          colimit.ι ((curry.obj F).obj j') k' (F.map (f ×ₘ g j) (y j)) := by
      intro j j' f
      nth_rw 2 [← Bifunctor.diagonal']
      simp only [← curry_obj_obj_map, ← curry_obj_obj_obj, comp_apply, colimit.w_apply]
      rw [e, ← limit.w_apply _ f, ← e]
      simp [← comp_apply, -types_comp_apply]
    -- Because `K` is filtered, we can restate this as saying that
    -- for each such `f`, there is some place to the right of `k'`
    -- where these images of `y j` and `y j'` become equal.
    simp_rw [colimit_eq_iff] at w
    -- We take a moment to restate `w` more conveniently.
    let kf : ∀ {j j'} (_ : j ⟶ j'), K := fun f => (w f).choose
    let gf : ∀ {j j'} (f : j ⟶ j'), k' ⟶ kf f := fun f => (w f).choose_spec.choose
    let hf : ∀ {j j'} (f : j ⟶ j'), k' ⟶ kf f := fun f =>
      (w f).choose_spec.choose_spec.choose
    have wf :
      ∀ {j j'} (f : j ⟶ j'),
        F.map (𝟙 j' ×ₘ (g j' ≫ gf f)) (y j') = F.map (f ×ₘ (g j ≫ hf f)) (y j) :=
      fun {j j'} f => by
      have q :
        ((curry.obj F).obj j').map (gf f) (F.map (𝟙 j' ×ₘ g j') (y j')) =
          ((curry.obj F).obj j').map (hf f) (F.map (f ×ₘ g j) (y j)) :=
        (w f).choose_spec.choose_spec.choose_spec
      convert! q using 1
      · simp [← comp_apply, -types_comp_apply]
      · simp [← comp_apply, -types_comp_apply, ← F.map_comp]
    clear_value kf gf hf
    -- and clean up some things that are no longer needed.
    clear w
    -- We're now ready to use the fact that `K` is filtered a second time,
    -- picking some place to the right of all of
    -- the morphisms `gf f : k' ⟶ kh f` and `hf f : k' ⟶ kf f`.
    -- At this point we're relying on there being only finitely morphisms in `J`.
    let O :=
      (Finset.univ.biUnion fun j => Finset.univ.biUnion fun j' => Finset.univ.image
        (@kf j j')) ∪ {k'}
    have kfO : ∀ {j j'} (f : j ⟶ j'), kf f ∈ O := fun {j} {j'} f =>
      Finset.mem_union.mpr
        (Or.inl
          (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j,
            Finset.mem_biUnion.mpr ⟨j', Finset.mem_univ j',
              Finset.mem_image.mpr ⟨f, Finset.mem_univ _, rfl⟩⟩⟩))
    have k'O : k' ∈ O := Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
    let H : Finset (Σ' (X Y : K) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y) :=
      Finset.univ.biUnion fun j : J =>
        Finset.univ.biUnion fun j' : J =>
          Finset.univ.biUnion fun f : j ⟶ j' =>
            {⟨k', kf f, k'O, kfO f, gf f⟩, ⟨k', kf f, k'O, kfO f, hf f⟩}
    obtain ⟨k'', i', s'⟩ := IsFiltered.sup_exists O H
    -- We then restate this slightly more conveniently, as a family of morphism `i f : kf f ⟶ k''`,
    -- satisfying `gf f ≫ i f = hf f' ≫ i f'`.
    let i : ∀ {j j'} (f : j ⟶ j'), kf f ⟶ k'' := fun {j} {j'} f => i' (kfO f)
    have s : ∀ {j₁ j₂ j₃ j₄} (f : j₁ ⟶ j₂) (f' : j₃ ⟶ j₄), gf f ≫ i f = hf f' ≫ i f' := by
      intro j₁ j₂ j₃ j₄ f f'
      rw [s', s']
      · exact k'O
      · exact Finset.mem_biUnion.mpr ⟨j₃, Finset.mem_univ _,
          Finset.mem_biUnion.mpr ⟨j₄, Finset.mem_univ _,
            Finset.mem_biUnion.mpr ⟨f', Finset.mem_univ _, by
              -- This works by `simp`, but has very high variation in heartbeats.
              rw [Finset.mem_insert, PSigma.mk.injEq, heq_eq_eq, PSigma.mk.injEq, heq_eq_eq,
                PSigma.mk.injEq, heq_eq_eq, PSigma.mk.injEq, heq_eq_eq, eq_self, true_and, eq_self,
                true_and, eq_self, true_and, eq_self, true_and, Finset.mem_singleton, eq_self,
                or_true]
              trivial⟩⟩⟩
      · exact Finset.mem_biUnion.mpr ⟨j₁, Finset.mem_univ _,
          Finset.mem_biUnion.mpr ⟨j₂, Finset.mem_univ _,
            Finset.mem_biUnion.mpr ⟨f, Finset.mem_univ _, by
              -- This works by `simp`, but has very high variation in heartbeats.
              rw [Finset.mem_insert, PSigma.mk.injEq, heq_eq_eq, PSigma.mk.injEq, heq_eq_eq,
                PSigma.mk.injEq, heq_eq_eq, PSigma.mk.injEq, heq_eq_eq, eq_self, true_and, eq_self,
                true_and, eq_self, true_and, eq_self, true_and, Finset.mem_singleton, eq_self,
                true_or]
              trivial⟩⟩⟩
    clear_value i
    clear s' i' H kfO k'O O
    -- We're finally ready to construct the pre-image, and verify it really maps to `x`.
    -- ⊢ ∃ a, colimitLimitToLimitColimit F a = x
    fconstructor
    · -- We construct the pre-image (which, recall is meant to be a point
      -- in the colimit (over `K`) of the limits (over `J`)) via a representative at `k''`.
      apply colimit.ι (curry.obj (swap K J ⋙ F) ⋙ Limits.lim) k'' _
      dsimp
      -- This representative is meant to be an element of a limit,
      -- so we need to construct a family of elements in `F.obj (j, k'')` for varying `j`,
      -- then show that are coherent with respect to morphisms in the `j` direction.
      apply Limit.mk
      swap
      · -- We construct the elements as the images of the `y j`.
        exact fun j => F.map (𝟙 j ×ₘ (g j ≫ gf (𝟙 j) ≫ i (𝟙 j))) (y j)
      · -- After which it's just a calculation, using `s` and `wf`, to see they are coherent.
        dsimp
        intro j j' f
        simp only [← comp_apply, ← Functor.map_comp, prod_comp, id_comp, comp_id]
        calc
          F.map (f ×ₘ (g j ≫ gf (𝟙 j) ≫ i (𝟙 j))) (y j) =
              F.map (f ×ₘ (g j ≫ hf f ≫ i f)) (y j) := by
            rw [s (𝟙 j) f]
          _ =
              F.map (𝟙 j' ×ₘ i f) (F.map (f ×ₘ (g j ≫ hf f)) (y j)) := by
            rw [← comp_apply, ← Functor.map_comp, prod_comp, comp_id, assoc]
          _ =
              F.map (𝟙 j' ×ₘ i f) (F.map (𝟙 j' ×ₘ (g j' ≫ gf f)) (y j')) := by
            rw [← wf f]
          _ = F.map (𝟙 j' ×ₘ (g j' ≫ gf f ≫ i f)) (y j') := by
            rw [← comp_apply, ← Functor.map_comp, prod_comp, id_comp, assoc]
          _ = F.map (𝟙 j' ×ₘ (g j' ≫ gf (𝟙 j') ≫ i (𝟙 j'))) (y j') := by
            rw [s f (𝟙 j'), ← s (𝟙 j') (𝟙 j')]
    -- Finally we check that this maps to `x`.
    · -- We can do this componentwise:
      apply limit_ext
      intro j
      -- and as each component is an equation in a colimit, we can verify it by
      -- pointing out the morphism which carries one representative to the other:
      -- `simp? [← comp_apply, -types_comp_apply]` says:
      simp only [comp_obj, colim_obj, lim_obj, Bifunctor.map_id_comp, id_eq, ← comp_apply, assoc,
        ι_colimitLimitToLimitColimit_π, curry_obj_obj_obj, swap_obj]
      generalize_proofs _ _ _ _ h
      dsimp
      rw [← dsimp% e j, dsimp% Limit.π_mk _ _ h]
      dsimp only [comp_obj, colim_obj, ← curry_obj_obj_obj]
      rw [colimit_eq_iff]
      refine ⟨k'', 𝟙 k'', g j ≫ gf (𝟙 j) ≫ i (𝟙 j), ?_⟩
      simp
/-
**CategoryTheory.Limits.colimitLimitToLimitColimit_isIso** 是 Mathlib 中的一个实例，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：colimitLimitToLimitColimit_isIso : IsIso (colimitLimitToLimitColimit F)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Limits.Types.hasLimitsOfShape`：∀ {J : Type v} [inst : Cat
egoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasLimi
tsOfShape J (Type u)
· 使用定理 `Countable.toSmall`：∀ (α : Type v) [Countable α], Small.{w, v} α
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfShape`：∀ {J : Type v} [inst : C
ategoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasCo
limitsOfShape J (Type u)
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.isIso_iff_bijective`：isIso_iff_bijective {X Y : Type u} (
f : X ⟶ Y) : IsIso f ↔ Function.Bijective f
· 使用定理 `CategoryTheory.Limits.colimitLimitToLimitColimit_injective`：colimitLimit
ToLimitColimit_injective : Function.Injective (colimitLimitToLimitColimit F)
· 使用定理 `CategoryTheory.Limits.colimitLimitToLimitColimit_surjective`：colimitLimi
tToLimitColimit_surjective : Function.Surjective (colimitLimitToLimitColimit F)
-/
instance colimitLimitToLimitColimit_isIso : IsIso (colimitLimitToLimitColimit F) :=
  (isIso_iff_bijective _).mpr
    ⟨colimitLimitToLimitColimit_injective F, colimitLimitToLimitColimit_surjective F⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Limits.colimitLimitToLimitColimitCone_iso** 是 Mathlib 中的一个实例，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：colimitLimitToLimitColimitCone_iso (F : J ⥤ K ⥤ Type v) : IsIso (colimitLi
mitToLimitColimitCone F)
参数：F : J ⥤ K ⥤ Type v。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfShape`：∀ {J : Type v} [inst : C
ategoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasCo
limitsOfShape J (Type u)
· 使用定理 `Countable.toSmall`：∀ (α : Type v) [Countable α], Small.{w, v} α
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.Types.hasLimitsOfShape`：∀ {J : Type v} [inst : Cat
egoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasLimi
tsOfShape J (Type u)
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Limits.Cone.cone_iso_of_hom_iso`：cone_iso_of_hom_iso {K :
 J ⥤ C} {c d : Cone K} (f : c ⟶ d) [i : IsIso f.hom] : IsIso f
-/
instance colimitLimitToLimitColimitCone_iso (F : J ⥤ K ⥤ Type v) :
    IsIso (colimitLimitToLimitColimitCone F) := by
  have : IsIso (colimitLimitToLimitColimitCone F).hom := by
    suffices IsIso (colimitLimitToLimitColimit (uncurry.obj F) ≫
        lim.map (whiskerRight (currying.unitIso.app F).inv colim)) by
      apply IsIso.comp_isIso
    infer_instance
  apply Cone.cone_iso_of_hom_iso
/-
**CategoryTheory.Limits.filtered_colim_preservesFiniteLimits_of_types** 是 Mathli
b 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：filtered_colim_preservesFiniteLimits_of_types : PreservesFiniteLimits (col
im : (K ⥤ Type v) ⥤ _)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesFiniteLimits_of_preservesFiniteLimitsOfSi
ze`：preservesFiniteLimits_of_preservesFiniteLimitsOfSize (F : C ⥤ D) (h : forall
 (J : Type w) {𝒥 : SmallCategory J} (_ : @FinCategory J 𝒥), Pres…
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfShape`：∀ {J : Type v} [inst : C
ategoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasCo
limitsOfShape J (Type u)
· 使用定理 `Countable.toSmall`：∀ (α : Type v) [Countable α], Small.{w, v} α
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.Types.hasLimitsOfShape`：∀ {J : Type v} [inst : Cat
egoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasLimi
tsOfShape J (Type u)
-/
noncomputable instance filtered_colim_preservesFiniteLimits_of_types :
    PreservesFiniteLimits (colim : (K ⥤ Type v) ⥤ _) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{v₂}
  intro J _ _
  refine ⟨fun {F} => ⟨fun {c} hc => ⟨IsLimit.ofIsoLimit (limit.isLimit _) ?_⟩⟩⟩
  symm
  trans colim.mapCone (limit.cone F)
  · exact Functor.mapIso _ (hc.uniqueUpToIso (limit.isLimit F))
  · exact asIso (colimitLimitToLimitColimitCone F)

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{v} C FC]

section

variable [HasLimitsOfShape J C] [HasColimitsOfShape K C]
variable [ReflectsLimitsOfShape J (forget C)] [PreservesColimitsOfShape K (forget C)]
variable [PreservesLimitsOfShape J (forget C)]

/-
**CategoryTheory.Limits.filtered_colim_preservesFiniteLimits** 是 Mathlib 中的一个实例，
位于命名空间 `CategoryTheory.Limits`。
形式化陈述：filtered_colim_preservesFiniteLimits : PreservesLimitsOfShape J (colim : (
K ⥤ C) ⥤ _)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_reflects_of_preserves`：p
reservesLimitsOfShape_of_reflects_of_preserves [PreservesLimitsOfShape J (F ⋙ G)
] [ReflectsLimitsOfShape J G] : PreservesLimitsOfShape J F …
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_natIso`：preservesLimitsO
fShape_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesLimitsOfShape J F] : Preser
vesLimitsOfShape J G where preservesLimit {K…
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfShape`：∀ {J : Type v} [inst : C
ategoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasCo
limitsOfShape J (Type u)
· 使用定理 `CategoryTheory.Limits.comp_preservesLimitsOfShape`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.preservesLimitsOfShapeOfPreservesFiniteLimits`：∀ {
C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 :
 CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
-/
noncomputable instance filtered_colim_preservesFiniteLimits :
    PreservesLimitsOfShape J (colim : (K ⥤ C) ⥤ _) :=
  haveI : PreservesLimitsOfShape J ((colim : (K ⥤ C) ⥤ _) ⋙ forget C) :=
    preservesLimitsOfShape_of_natIso (preservesColimitNatIso _).symm
  preservesLimitsOfShape_of_reflects_of_preserves _ (forget C)

end

attribute [local instance] reflectsLimitsOfShape_of_reflectsIsomorphisms

/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [PreservesFiniteLimits (forget C)] [PreservesColimitsOfShape K (forget C)]
    [HasFiniteLimits C] [HasColimitsOfShape K C] [(forget C).ReflectsIsomorphisms] :
    PreservesFiniteLimits (colim : (K ⥤ C) ⥤ _) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{v}
  intro J _ _
  infer_instance

end

section

variable {C : Type u} [Category.{v} C]
variable {J : Type u₁} [Category.{v₁} J]
variable {K : Type u₂} [Category.{v₂} K]
variable [HasLimitsOfShape J C] [HasColimitsOfShape K C]
variable [PreservesLimitsOfShape J (colim : (K ⥤ C) ⥤ _)]

/-- A curried version of the fact that filtered colimits commute with finite limits. -/
/-
**CategoryTheory.Limits.colimitLimitIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits`。
形式化陈述：colimitLimitIso (F : J ⥤ K ⥤ C) : colimit (limit F) ≅ limit (colimit F.fli
p)
参数：F : J ⥤ K ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A curried version of the fact that filtered colimits commute with finite limits.
-/
noncomputable def colimitLimitIso (F : J ⥤ K ⥤ C) : colimit (limit F) ≅ limit (colimit F.flip) :=
  (isLimitOfPreserves colim (limit.isLimit _)).conePointUniqueUpToIso (limit.isLimit _) ≪≫
    HasLimit.isoOfNatIso (colimitFlipIsoCompColim _).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_colimitLimitIso_limit_π (F : J ⥤ K ⥤ C) (a) (b) :
    colimit.ι (limit F) a ≫ (colimitLimitIso F).hom ≫ limit.π (colimit F.flip) b =
      (limit.π F b).app a ≫ (colimit.ι F.flip a).app b := by
  simp [colimitLimitIso]

end

end CategoryTheory.Limits

