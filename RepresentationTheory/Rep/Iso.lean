/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RepresentationTheory.Rep.Basic

/-!
# Equivalence between `Rep k G` and `ModuleCat k[G]`

In this file we show that the category of `k`-linear representations of a monoid `G` is
equivalent to the category of modules over the monoid algebra `k[G]`.
-/

@[expose] public section

universe w w' u u' v v'

namespace Rep

open CategoryTheory
open scoped MonoidAlgebra

suppress_compilation

section Group

variable (k G H : Type u) [Group G] [Monoid H] [MulAction G H] [CommRing k] (n : ℕ)

open MonoidalCategory Finsupp Representation.IntertwiningMap

/-- An isomorphism of `k`-linear representations of `G` from `k[Gⁿ⁺¹]` to `k[G] ⊗ₖ k[Gⁿ]` (on
which `G` acts by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`) sending `(g₀, ..., gₙ)` to
`g₀ ⊗ (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ)`. The inverse sends `g₀ ⊗ (g₁, ..., gₙ)` to
`(g₀, g₀g₁, ..., g₀g₁...gₙ)`. -/
/-
**Rep.diagonalSuccIsoTensorTrivial** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：diagonalSuccIsoTensorTrivial : diagonal k G (n + 1) ≅ leftRegular k G otim
es trivial k G k[Fin n -> G]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism of `k`-linear representations of `G` from `k[Gⁿ⁺¹]` to `k[G] ⊗ₖ k
[Gⁿ]` (on
which `G` acts by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`) sending `(g₀, ..., gₙ)` to
`g₀ ⊗ (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ)`. The inverse sends `g₀ ⊗ (g₁, ..., gₙ)` t
o
`(g₀, g₀g₁, ..., g₀g₁...gₙ)`.
-/
abbrev diagonalSuccIsoTensorTrivial :
    diagonal k G (n + 1) ≅ leftRegular k G ⊗ trivial k G k[Fin n → G] :=
  linearizationOfMulActionIso k G (Fin (n + 1) → G) ≪≫ (linearization k G).mapIso
    (Action.diagonalSuccIsoTensorTrivial G n) ≪≫
    (Functor.Monoidal.μIso (linearization k G) _ _).symm ≪≫
    tensorIso (linearizationOfMulActionIso k G G) (linearizationTrivialIso k G (Fin n → G))

/-- Representation isomorphism `k[Gⁿ⁺¹] ≅ (Gⁿ →₀ k[G])`, where the right-hand representation is
defined pointwise by the left regular representation on `k[G]`. The map sends
`single (g₀, ..., gₙ) a ↦ single (g₀⁻¹g₁, ..., gₙ₋₁⁻¹gₙ) (single g₀ a)`. -/
/-
**Rep.diagonalSuccIsoFree** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：diagonalSuccIsoFree : diagonal k G (n + 1) ≅ free k G (Fin n -> G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Representation isomorphism `k[Gⁿ⁺¹] ≅ (Gⁿ →₀ k[G])`, where the right-hand repres
entation is
defined pointwise by the left regular representation on `k[G]`. The map sends
`single (g₀, ..., gₙ) a ↦ single (g₀⁻¹g₁, ..., gₙ₋₁⁻¹gₙ) (single g₀ a)`.
-/
abbrev diagonalSuccIsoFree : diagonal k G (n + 1) ≅ free k G (Fin n → G) :=
  diagonalSuccIsoTensorTrivial k G n ≪≫ leftRegularTensorTrivialIsoFree k G (Fin n → G)

variable (A : Rep k G)

/-- Given a `k`-linear `G`-representation `A`, the set of representation morphisms
`Hom(k[Gⁿ⁺¹], A)` is `k`-linearly isomorphic to the set of functions `Gⁿ → A`. -/
/-
**Rep.diagonalHomEquiv** 是 Mathlib 中的一个缩写定义，位于命名空间 `Rep`。
形式化陈述：diagonalHomEquiv : (Rep.diagonal k G (n + 1) ⟶ A) ≃ₗ[k] (Fin n -> G) -> A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a `k`-linear `G`-representation `A`, the set of representation morphisms
`Hom(k[Gⁿ⁺¹], A)` is `k`-linearly isomorphic to the set of functions `Gⁿ → A`.
-/
abbrev diagonalHomEquiv :
    (Rep.diagonal k G (n + 1) ⟶ A) ≃ₗ[k] (Fin n → G) → A :=
  Linear.homCongr k (diagonalSuccIsoFree k G n) (Iso.refl _) ≪≫ₗ
    freeLiftLEquiv k G (Fin n → G) A

end Group

/-!
### The categorical equivalence `Rep k G ≌ Module.{u} k[G]`.
-/


variable {k : Type u} {G : Type v} [CommRing k] [Monoid G]

open MonoidAlgebra

/-- Auxiliary lemma for `toModuleMonoidAlgebra`. -/
/-
**Rep.to_Module_monoidAlgebra_map_aux** 是 Mathlib 中的一个定理，位于命名空间 `Rep`。
形式化陈述：to_Module_monoidAlgebra_map_aux {k G : Type*} [CommRing k] [Monoid G] (V W
 : Type*) [AddCommGroup V] [AddCommGroup W] [Module k V] [Module k W] (ρ : G ->*
 V ->ₗ[k] V) (σ : G ->* W ->ₗ[k] W) (f : V ->ₗ[k] W) (w : forall g : G, f.comp (
ρ g) = (σ g).comp f) (r : k[G]) (x : V) : f (MonoidAlgebra.lift k (V ->ₗ[k] V) G
 ρ r x) = MonoidAlgebra.lift k (W ->ₗ[k] W) G σ r (f x)
参数：V W : Type*；ρ : G ->* V ->ₗ[k] V；σ : G ->* W ->ₗ[k] W；f : V ->ₗ[k] W；w : fora
ll g : G, f.comp (ρ g) = (σ g).comp f；r : k[G]；x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidAlgebra.induction_on`：induction_on {motive : R[M] -> Prop} (x : R[
M]) (of : forall m, motive (.of R M m)) (add : forall x y : R[M], motive x -> mo
tive y -> motive…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MonoidAlgebra.of_apply`：∀ (R : Type u_8) (M : Type u_9) [inst : Semiring
 R] [inst_1 : MulOneClass M] (a : M),   (MonoidAlgebra.of R M) a = MonoidAlgebra
.single a 1
· 使用定理 `MonoidAlgebra.lift_single`：lift_single (F : M ->* A) (a b) : lift R A M 
F (single a b) = b • F a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…

--- 原说明 ---
Auxiliary lemma for `toModuleMonoidAlgebra`.
-/
theorem to_Module_monoidAlgebra_map_aux {k G : Type*} [CommRing k] [Monoid G] (V W : Type*)
    [AddCommGroup V] [AddCommGroup W] [Module k V] [Module k W] (ρ : G →* V →ₗ[k] V)
    (σ : G →* W →ₗ[k] W) (f : V →ₗ[k] W) (w : ∀ g : G, f.comp (ρ g) = (σ g).comp f)
    (r : k[G]) (x : V) :
    f (MonoidAlgebra.lift k (V →ₗ[k] V) G ρ r x) =
      MonoidAlgebra.lift k (W →ₗ[k] W) G σ r (f x) := by
  apply MonoidAlgebra.induction_on r
  · intro g
    simp only [one_smul, MonoidAlgebra.lift_single, MonoidAlgebra.of_apply]
    exact LinearMap.congr_fun (w g) x
  · intro g h gw hw; simp only [map_add, LinearMap.add_apply, hw, gw]
  · intro r g w
    simp only [map_smul, w, LinearMap.smul_apply]

/-- Auxiliary definition for `toModuleMonoidAlgebra`. -/
/-
**Rep.toModuleMonoidAlgebraMap** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：toModuleMonoidAlgebraMap {V W : Rep.{w} k G} (f : V ⟶ W) : ModuleCat.of k[
G] V.ρ.asModule ⟶ ModuleCat.of k[G] W.ρ.asModule
参数：f : V ⟶ W。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `toModuleMonoidAlgebra`.
-/
def toModuleMonoidAlgebraMap {V W : Rep.{w} k G} (f : V ⟶ W) :
    ModuleCat.of k[G] V.ρ.asModule ⟶ ModuleCat.of k[G] W.ρ.asModule :=
  ModuleCat.ofHom
    { f.hom.toLinearMap with
      map_smul' := fun r x => to_Module_monoidAlgebra_map_aux V.V W.V V.ρ W.ρ
        f.hom.toLinearMap f.hom.2 r x }

/-- Functorially convert a representation of `G` into a module over `k[G]`. -/
/-
**Rep.toModuleMonoidAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：toModuleMonoidAlgebra : Rep.{w} k G ⥤ ModuleCat k[G] where obj V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functorially convert a representation of `G` into a module over `k[G]`.
-/
def toModuleMonoidAlgebra : Rep.{w} k G ⥤ ModuleCat k[G] where
  obj V := ModuleCat.of _ V.ρ.asModule
  map f := toModuleMonoidAlgebraMap f

set_option backward.isDefEq.respectTransparency false in
/-- Functorially convert a module over `k[G]` into a representation of `G`. -/
/-
**Rep.ofModuleMonoidAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：ofModuleMonoidAlgebra : ModuleCat k[G] ⥤ Rep.{w} k G where obj M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functorially convert a module over `k[G]` into a representation of `G`.
-/
def ofModuleMonoidAlgebra : ModuleCat k[G] ⥤ Rep.{w} k G where
  obj M := Rep.of (Representation.ofModule M)
  map f := ofHom {
    __ := f.hom
    map_smul' r x := f.hom.map_smul (algebraMap k _ r) x
    isIntertwining' g := by ext; apply f.hom.map_smul
  }
/-
**Rep.ofModuleMonoidAlgebra_obj_coe** 是 Mathlib 中的一个定理，位于命名空间 `Rep`。
形式化陈述：ofModuleMonoidAlgebra_obj_coe (M : ModuleCat.{w} k[G]) : ofModuleMonoidAlg
ebra.obj M = RestrictScalars k k[G] M
参数：M : ModuleCat.{w} k[G]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofModuleMonoidAlgebra_obj_coe (M : ModuleCat.{w} k[G]) :
    ofModuleMonoidAlgebra.obj M = RestrictScalars k k[G] M :=
  rfl
/-
**Rep.ofModuleMonoidAlgebra_obj_** 是 Mathlib 中的一个定理，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofModuleMonoidAlgebra_obj_ρ (M : ModuleCat.{w} k[G]) :
    (ofModuleMonoidAlgebra.obj M).ρ = Representation.ofModule M :=
  rfl

/-- Auxiliary definition for `equivalenceModuleMonoidAlgebra`. -/
/-
**Rep.counitIsoAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：counitIsoAddEquiv {M : ModuleCat.{w} k[G]} : (ofModuleMonoidAlgebra ⋙ toMo
duleMonoidAlgebra).obj M ≃+ M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `equivalenceModuleMonoidAlgebra`.
-/
def counitIsoAddEquiv {M : ModuleCat.{w} k[G]} :
    (ofModuleMonoidAlgebra ⋙ toModuleMonoidAlgebra).obj M ≃+ M := by
  dsimp [ofModuleMonoidAlgebra, toModuleMonoidAlgebra]
  exact (Representation.ofModule M).asModuleEquiv.toAddEquiv.trans
    (RestrictScalars.addEquiv k k[G] _)

set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for `equivalenceModuleMonoidAlgebra`. -/
/-
**Rep.unitIsoAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：unitIsoAddEquiv {V : Rep.{w} k G} : V ≃+ (toModuleMonoidAlgebra ⋙ ofModule
MonoidAlgebra).obj V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `equivalenceModuleMonoidAlgebra`.
-/
def unitIsoAddEquiv {V : Rep.{w} k G} : V ≃+ (toModuleMonoidAlgebra ⋙
    ofModuleMonoidAlgebra).obj V := by
  dsimp [ofModuleMonoidAlgebra, toModuleMonoidAlgebra]
  exact V.ρ.asModuleEquiv.symm.toAddEquiv.trans (RestrictScalars.addEquiv _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `equivalenceModuleMonoidAlgebra`. -/
/-
**Rep.counitIso** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：counitIso (M : ModuleCat.{w} k[G]) : (ofModuleMonoidAlgebra ⋙ toModuleMono
idAlgebra).obj M ≅ M
参数：M : ModuleCat.{w} k[G]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `equivalenceModuleMonoidAlgebra`.
-/
def counitIso (M : ModuleCat.{w} k[G]) :
    (ofModuleMonoidAlgebra ⋙ toModuleMonoidAlgebra).obj M ≅ M :=
  LinearEquiv.toModuleIso
    { counitIsoAddEquiv with
      map_smul' := fun r x => by
        simp [counitIsoAddEquiv] }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**Rep.unit_iso_comm** 是 Mathlib 中的一个定理，位于命名空间 `Rep`。
形式化陈述：unit_iso_comm (V : Rep.{w} k G) (g : G) (x : V) : unitIsoAddEquiv ((V.ρ g)
.toFun x) = ((ofModuleMonoidAlgebra.obj (toModuleMonoidAlgebra.obj V)).ρ g).toFu
n (unitIsoAddEquiv x)
参数：V : Rep.{w} k G；g : G；x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Representation.asModuleEquiv_symm_map_rho`：asModuleEquiv_symm_map_rho (g
 : G) (x : V) : ρ.asModuleEquiv.symm (ρ g x) = MonoidAlgebra.of k G g • ρ.asModu
leEquiv.symm x
· 使用引理 `Representation.single_smul`：single_smul (t : k) (g : G) (v : ρ.asModule)
 : MonoidAlgebra.single (g : G) t • v = t • ρ g (ρ.asModuleEquiv v)
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Representation.ofModule_asModule_act`：ofModule_asModule_act (g : G) (x :
 RestrictScalars k k[G] ρ.asModule) : ofModule ρ.asModule g x = (RestrictScalars
.addEquiv _ _ _).symm (ρ.a…
· 使用定理 `AddEquiv.apply_symm_apply`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M
] [inst_1 : Add N] (e : M ≃+ N) (y : N), e (e.symm y) = y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem unit_iso_comm (V : Rep.{w} k G) (g : G) (x : V) :
    unitIsoAddEquiv ((V.ρ g).toFun x) = ((ofModuleMonoidAlgebra.obj
      (toModuleMonoidAlgebra.obj V)).ρ g).toFun (unitIsoAddEquiv x) := by
  simp [unitIsoAddEquiv, ofModuleMonoidAlgebra, toModuleMonoidAlgebra]

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `equivalenceModuleMonoidAlgebra`. -/
/-
**Rep.unitIso** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：unitIso (V : Rep.{w} k G) : V ≅ (toModuleMonoidAlgebra ⋙ ofModuleMonoidAlg
ebra).obj V
参数：V : Rep.{w} k G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `equivalenceModuleMonoidAlgebra`.
-/
def unitIso (V : Rep.{w} k G) : V ≅ (toModuleMonoidAlgebra ⋙ ofModuleMonoidAlgebra).obj V :=
  mkIso <| .mk
  { unitIsoAddEquiv (k := k) (G := G) with
    map_smul' r x := show (RestrictScalars.addEquiv _ _ _).symm
      (V.ρ.asModuleEquiv.symm (r • x)) = _ by
      simp only [Representation.asModuleEquiv_symm_map_smul]
      rfl } fun g ↦ by ext; exact unit_iso_comm ..

/-- The categorical equivalence `Rep k G ≌ ModuleCat k[G]`. -/
/-
**Rep.equivalenceModuleMonoidAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `Rep`。
形式化陈述：equivalenceModuleMonoidAlgebra : Rep.{w} k G ≌ ModuleCat k[G] where functo
r
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The categorical equivalence `Rep k G ≌ ModuleCat k[G]`.
-/
def equivalenceModuleMonoidAlgebra : Rep.{w} k G ≌ ModuleCat k[G] where
  functor := toModuleMonoidAlgebra
  inverse := ofModuleMonoidAlgebra
  unitIso := NatIso.ofComponents (fun V => unitIso V) (by cat_disch)
  counitIso := NatIso.ofComponents (fun M => counitIso M) (by cat_disch)
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (toModuleMonoidAlgebra.{w} (k := k) (G := G)).IsEquivalence :=
  (equivalenceModuleMonoidAlgebra (k := k) (G := G)).isEquivalence_functor
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (ofModuleMonoidAlgebra (k := k) (G := G)).IsEquivalence :=
  (equivalenceModuleMonoidAlgebra (k := k) (G := G)).isEquivalence_inverse

-- TODO Verify that the equivalence with `ModuleCat k[G]` is a monoidal functor.

variable {k G : Type u} [CommRing k] [Monoid G] in
/-
**Rep.** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CategoryTheory.EnoughProjectives (Rep.{max w u} k G) :=
  equivalenceModuleMonoidAlgebra.enoughProjectives_iff.2 ModuleCat.enoughProjectives.{max w u}
/-
**Rep.free_projective** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
形式化陈述：free_projective {α : Type (max w u)} : Projective (free k G α)
参数：max w u。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.projective_of_map_projective`：projective_of_ma
p_projective (adj : F ⊣ G) [F.Full] [F.Faithful] (P : C) (hP : Projective (F.obj
 P)) : Projective P where factors f g _
· 使用定理 `ModuleCat.projective_of_free`：projective_of_free {ι : Type w} (b : Basis
 ι R M) : Projective M
-/
instance free_projective {α : Type (max w u)} :
    Projective (free k G α) :=
  equivalenceModuleMonoidAlgebra.toAdjunction.projective_of_map_projective _ <|
    @ModuleCat.projective_of_free _ _
      (ModuleCat.of k[G] (Representation.free k G α).asModule)
      _ (Representation.freeAsModuleBasis k G α)

section

variable {G : Type u} [Group G] {n : ℕ}

/-
**Rep.diagonal_succ_projective** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
形式化陈述：diagonal_succ_projective : Projective (diagonal k G (n + 1))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Projective.of_iso`：of_iso {P Q : C} (i : P ≅ Q) (_ : Proj
ective P) : Projective Q where factors f e _
-/
instance diagonal_succ_projective :
    Projective (diagonal k G (n + 1)) := by
  exact Projective.of_iso (diagonalSuccIsoFree k G n).symm inferInstance
/-
**Rep.leftRegular_projective** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
形式化陈述：leftRegular_projective : Projective (leftRegular k G)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Projective.of_iso`：of_iso {P Q : C} (i : P ≅ Q) (_ : Proj
ective P) : Projective Q where factors f e _
-/
instance leftRegular_projective :
    Projective (leftRegular k G) :=
  Projective.of_iso (diagonalOneIsoLeftRegular k G) inferInstance
/-
**Rep.trivial_projective_of_subsingleton** 是 Mathlib 中的一个实例，位于命名空间 `Rep`。
形式化陈述：trivial_projective_of_subsingleton [Subsingleton G] : Projective (trivial 
k G k)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Projective.of_iso`：of_iso {P Q : C} (i : P ≅ Q) (_ : Proj
ective P) : Projective Q where factors f e _
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
-/
instance trivial_projective_of_subsingleton [Subsingleton G] :
    Projective (trivial k G k) :=
  Projective.of_iso (ofMulActionSubsingletonIsoTrivial _ _ (Fin 1 → G)) diagonal_succ_projective

end

end Rep

