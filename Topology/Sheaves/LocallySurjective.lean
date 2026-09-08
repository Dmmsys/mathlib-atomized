/-
Copyright (c) 2022 Sam van Gool and Jake Levinson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam van Gool, Jake Levinson
-/
module

public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.EpiMono

/-!

# Locally surjective maps of presheaves.

Let `X` be a topological space, `ℱ` and `𝒢` presheaves on `X`, `T : ℱ ⟶ 𝒢` a map.

In this file we formulate two notions for what it means for
`T` to be locally surjective:

  1. For each open set `U`, each section `t : 𝒢(U)` is in the image of `T`
     after passing to some open cover of `U`.

  2. For each `x : X`, the map of *stalks* `Tₓ : ℱₓ ⟶ 𝒢ₓ` is surjective.

We prove that these are equivalent.

-/

@[expose] public section


universe v u

noncomputable section

open CategoryTheory

open TopologicalSpace

open Opposite

namespace TopCat.Presheaf

section LocallySurjective

open scoped AlgebraicGeometry

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC] {X : TopCat.{v}}
variable {ℱ 𝒢 : X.Presheaf C}

/-- A map of presheaves `T : ℱ ⟶ 𝒢` is **locally surjective** if for any open set `U`,
section `t` over `U`, and `x ∈ U`, there exists an open set `x ∈ V ⊆ U` and a section `s` over `V`
such that `$T_*(s_V) = t|_V$`.

See `TopCat.Presheaf.isLocallySurjective_iff` below.
-/
/-
**TopCat.Presheaf.IsLocallySurjective** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.Presheaf
`。
形式化陈述：IsLocallySurjective (T : ℱ ⟶ 𝒢)
参数：T : ℱ ⟶ 𝒢。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A map of presheaves `T : ℱ ⟶ 𝒢` is **locally surjective** if for any open set `U
`,
section `t` over `U`, and `x ∈ U`, there exists an open set `x ∈ V ⊆ U` and a se
ction `s` over `V`
such that `$T_*(s_V) = t|_V$`.

See `TopCat.Presheaf.isLocallySurjective_iff` below.
-/
def IsLocallySurjective (T : ℱ ⟶ 𝒢) :=
  CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) T
/-
**TopCat.Presheaf.isLocallySurjective_iff** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Pres
heaf`。
形式化陈述：isLocallySurjective_iff (T : ℱ ⟶ 𝒢) : IsLocallySurjective T ↔ forall (U t)
, forall x in U, exists (V : _) (_ : V <= U), (exists s, (T.app _) s = t |_ V) ∧
 x in V
参数：T : ℱ ⟶ 𝒢。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presheaf.IsLocallySurjective.imageSieve_mem`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {J : CategoryTheory.GrothendieckTop
ology C} {A : Type u'}   {inst_1 : CategoryTheor…
· 使用定理 `CategoryTheory.leOfHom`：leOfHom {x y : X} (h : x ⟶ y) : x <= y
-/
theorem isLocallySurjective_iff (T : ℱ ⟶ 𝒢) :
    IsLocallySurjective T ↔
      ∀ (U t), ∀ x ∈ U, ∃ (V : _) (_ : V ≤ U), (∃ s, (T.app _) s = t |_ V) ∧ x ∈ V := by
  refine ⟨fun h _ t x hx ↦ ?_, fun h => ⟨fun s x hx ↦ ?_⟩⟩
  · obtain ⟨V, i, hi⟩ := h.imageSieve_mem t x hx
    exact ⟨V, leOfHom i, hi⟩
  · obtain ⟨V, Vle, hV⟩ := h _ s x hx
    exact ⟨V, homOfLE Vle, hV⟩

section SurjectiveOnStalks

variable [Limits.HasColimits C] [Limits.PreservesFilteredColimits (forget C)]

set_option backward.isDefEq.respectTransparency false in
/-- An equivalent condition for a map of presheaves to be locally surjective
is for all the induced maps on stalks to be surjective. -/
/-
**TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks** 是 Mathlib 中的一个定理
，位于命名空间 `TopCat.Presheaf`。
形式化陈述：locally_surjective_iff_surjective_on_stalks (T : ℱ ⟶ 𝒢) : IsLocallySurject
ive T ↔ forall x : X, Function.Surjective ((stalkFunctor C x).map T)
参数：T : ℱ ⟶ 𝒢。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.exists_germ_eq`：exists_germ_eq (F : X.Presheaf C) {x : X
} (t : ToType (stalk.{v, u} F x)) : exists (U : Opens X) (m : x in U) (s : ToTyp
e (F.obj (op U))), F…
· 使用定理 `CategoryTheory.Presheaf.IsLocallySurjective.imageSieve_mem`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {J : CategoryTheory.GrothendieckTop
ology C} {A : Type u'}   {inst_1 : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.Presheaf.stalkFunctor_map_germ_apply'`：stalkFunctor_map_germ_appl
y' [ConcreteCategory C FC] {F G : X.Presheaf C} (U : Opens X) (x : X) (hx : x in
 U) (f : F ⟶ G) (s) : DFunLike.coe…
· 使用定理 `TopCat.Presheaf.germ_res_apply`：germ_res_apply (F : X.Presheaf C) {U V :
 Opens X} (i : U ⟶ V) (x : X) (hx : x in U) [ConcreteCategory C FC] (s) : F.germ
 U x hx (F.map i.op …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `TopCat.Presheaf.germ_eq`：germ_eq (F : X.Presheaf C) {U V : Opens X} (x :
 X) (mU : x in U) (mV : x in V) (s : ToType (F.obj (op U))) (t : ToType (F.obj (
op V))) (h : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `TopCat.Presheaf.stalkFunctor_map_germ_apply`：stalkFunctor_map_germ_apply
 [ConcreteCategory C FC] {F G : X.Presheaf C} (U : Opens X) (x : X) (hx : x in U
) (f : F ⟶ G) (s) : (stalkFunctor…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…

--- 原说明 ---
An equivalent condition for a map of presheaves to be locally surjective
is for all the induced maps on stalks to be surjective.
-/
theorem locally_surjective_iff_surjective_on_stalks (T : ℱ ⟶ 𝒢) :
    IsLocallySurjective T ↔ ∀ x : X, Function.Surjective ((stalkFunctor C x).map T) := by
  constructor <;> intro hT
  · /- human proof:
        Let g ∈ Γₛₜ 𝒢 x be a germ. Represent it on an open set U ⊆ X
        as ⟨t, U⟩. By local surjectivity, pass to a smaller open set V
        on which there exists s ∈ Γ_ ℱ V mapping to t |_ V.
        Then the germ of s maps to g -/
    -- Let g ∈ Γₛₜ 𝒢 x be a germ.
    intro x g
    -- Represent it on an open set U ⊆ X as ⟨t, U⟩.
    obtain ⟨U, hxU, t, rfl⟩ := 𝒢.exists_germ_eq g
    -- By local surjectivity, pass to a smaller open set V
    -- on which there exists s ∈ Γ_ ℱ V mapping to t |_ V.
    rcases hT.imageSieve_mem t x hxU with ⟨V, ι, ⟨s, h_eq⟩, hxV⟩
    -- Then the germ of s maps to g.
    use ℱ.germ _ x hxV s
    simp [h_eq, germ_res_apply]
  · /- human proof:
        Let U be an open set, t ∈ Γ ℱ U a section, x ∈ U a point.
        By surjectivity on stalks, the germ of t is the image of
        some germ f ∈ Γₛₜ ℱ x. Represent f on some open set V ⊆ X as ⟨s, V⟩.
        Then there is some possibly smaller open set x ∈ W ⊆ V ∩ U on which
        we have T(s) |_ W = t |_ W. -/
    constructor
    intro U t x hxU
    set t_x := 𝒢.germ _ x hxU t with ht_x
    obtain ⟨s_x, hs_x : ((stalkFunctor C x).map T) s_x = t_x⟩ := hT x t_x
    obtain ⟨V, hxV, s, rfl⟩ := ℱ.exists_germ_eq s_x
    -- rfl : ℱ.germ x s = s_x
    have key_W := 𝒢.germ_eq x hxV hxU (T.app _ s) t <| by
      convert! hs_x using 1
      symm
      convert! stalkFunctor_map_germ_apply _ _ _ _ s
    obtain ⟨W, hxW, hWV, hWU, h_eq⟩ := key_W
    refine ⟨W, hWU, ⟨ℱ.map hWV.op s, ?_⟩, hxW⟩
    convert! h_eq using 1
    simp only [← ConcreteCategory.comp_apply, T.naturality]

end SurjectiveOnStalks

end LocallySurjective

end TopCat.Presheaf

/-
**TopCat.Sheaf.isLocallySurjective_iff_epi** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Pre
sheaf`。
形式化陈述：TopCat.Sheaf.isLocallySurjective_iff_epi {X : TopCat.{v}} {C : Type u} [Ca
tegory.{v} C] {FC : C -> C -> Type*} {CC : C -> Type v} [forall X Y, FunLike (FC
 X Y) (CC X) (CC Y)] [ConcreteCategory C FC] [Balanced (CategoryTheory.Sheaf (Op
ens.grothendieckTopology X) C)] [(Opens.grothendieckTopology X).HasSheafCompose 
(CategoryTheory.forget C)] [HasSheafify (Opens.grothendieckTopology X) C] [(Open
s.grothendieckTopology X).WEqualsLocallyBijective C] [ConcreteCategory.HasFuncto
rialSurjectiveInjectiveFac
参数：FC X Y；CC X；CC Y；CategoryTheory.Sheaf (Opens.grothendieckTopology X) C；Opens.
grothendieckTopology X；CategoryTheory.forget C；Opens.grothendieckTopology X；Open
s.grothendieckTopology X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Sheaf.isLocallySurjective_iff_epi'`：isLocallySurjective_i
ff_epi' : IsLocallySurjective φ ↔ Epi φ
-/
theorem TopCat.Sheaf.isLocallySurjective_iff_epi {X : TopCat.{v}} {C : Type u} [Category.{v} C]
    {FC : C → C → Type*} {CC : C → Type v} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC] [Balanced (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C)]
    [(Opens.grothendieckTopology X).HasSheafCompose (CategoryTheory.forget C)]
    [HasSheafify (Opens.grothendieckTopology X) C]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective C]
    [ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization C]
    {F G : Sheaf C X} (φ : F ⟶ G) :
    TopCat.Presheaf.IsLocallySurjective φ.hom ↔ Epi φ :=
  CategoryTheory.Sheaf.isLocallySurjective_iff_epi' ..
