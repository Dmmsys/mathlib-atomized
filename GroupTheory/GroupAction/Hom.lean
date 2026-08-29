/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.Group.Hom.CompTypeclasses
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.Algebra.Ring.Action.Basic

/-!
# Equivariant homomorphisms

## Main definitions

* `MulActionHom φ X Y`, the type of equivariant functions from `X` to `Y`,
  where `φ : M → N` is a map, `M` acting on the type `X` and `N` acting on the type of `Y`.
  `AddActionHom φ X Y` is its additive version.
* `DistribMulActionHom φ A B`,
  the type of equivariant additive monoid homomorphisms from `A` to `B`,
  where `φ : M → N` is a morphism of monoids,
  `M` acting on the additive monoid `A` and `N` acting on the additive monoid of `B`
* `SMulSemiringHom φ R S`, the type of equivariant ring homomorphisms
  from `R` to `S`, where `φ : M → N` is a morphism of monoids,
  `M` acting on the ring `R` and `N` acting on the ring `S`.

The above types have corresponding classes:
* `MulActionHomClass F φ X Y` states that `F` is a type of bundled `X → Y` homs
  which are `φ`-equivariant;
  `AddActionHomClass F φ X Y` is its additive version.
* `DistribMulActionHomClass F φ A B` states that `F` is a type of bundled `A → B` homs
  preserving the additive monoid structure and `φ`-equivariant
* `SMulSemiringHomClass F φ R S` states that `F` is a type of bundled `R → S` homs
  preserving the ring structure and `φ`-equivariant

## Notation

We introduce the following notation to code equivariant maps
(the subscript index `ₑ` is for *equivariant*) :
* `X →ₑ[φ] Y` is `MulActionHom φ X Y` and `AddActionHom φ X Y`
* `A →ₑ+[φ] B` is `DistribMulActionHom φ A B`.
* `R →ₑ+*[φ] S` is `MulSemiringActionHom φ R S`.

When `M = N` and `φ = MonoidHom.id M`, we provide the backward compatible notation :
* `X →[M] Y` is `MulActionHom (@id M) X Y` and `AddActionHom (@id M) X Y`
* `A →+[M] B` is `DistribMulActionHom (MonoidHom.id M) A B`
* `R →+*[M] S` is `MulSemiringActionHom (MonoidHom.id M) R S`

The notation for `MulActionHom` and `AddActionHom` is the same, because it is unlikely
that it could lead to confusion — unless one needs types `M` and `X` with simultaneous
instances of `Mul M`, `Add M`, `SMul M X` and `VAdd M X`…

-/

@[expose] public section

assert_not_exists Submonoid

section MulActionHom

variable {M' : Type*}
variable {M : Type*} {N : Type*} {P : Type*}
variable (φ : M -> N) (ψ : N -> P) (χ : M -> P)
variable (X : Type*) [SMul M X] [SMul M' X]
variable (Y : Type*) [SMul N Y] [SMul M' Y]
variable (Z : Type*) [SMul P Z]

/--
Definition of `AddActionHom` / `AddActionHom` 的定义

English:
structure AddActionHom
  parameters: {M N : Type*} (φ : M -> N) (X : Type*) [VAdd M X] (Y : Type*) [VAdd N Y]
  axioms and operations (2):
    - toFun : X -> Y
    - map_vadd' : forall (m : M) (x : X), toFun (m +ᵥ x) = (φ m) +ᵥ toFun x

中文:
结构 AddActionHom
  参数: {M N : 类型} (φ : M -> N) (X : 类型) [VAdd M X] (Y : 类型) [VAdd N Y]
  公理与运算 (2 个):
    - toFun : X -> Y
    - map_vadd' : 对任意 (m : M) (x : X), toFun (m +ᵥ x) = (φ m) +ᵥ toFun x
-/
structure AddActionHom {M N : Type*} (φ : M -> N) (X : Type*) [VAdd M X] (Y : Type*) [VAdd N Y] where
  /-- The underlying function. -/
  protected toFun : X -> Y
  /-- The proposition that the function commutes with the additive actions. -/
  protected map_vadd' : forall (m : M) (x : X), toFun (m +ᵥ x) = (φ m) +ᵥ toFun x

/-- Equivariant functions :
When `φ : M → N` is a function, and types `X` and `Y` are endowed with actions of `M` and `N`,
a function `f : X → Y` is `φ`-equivariant if `f (m • x) = (φ m) • (f x)`. -/
@[to_additive]
/--
Definition of `MulActionHom` / `MulActionHom` 的定义

English:
structure MulActionHom
  parameters: where
  axioms and operations (2):
    - toFun : X -> Y
    - map_smul' : forall (m : M) (x : X), toFun (m • x) = (φ m) • toFun x

中文:
结构 MulActionHom
  参数: where
  公理与运算 (2 个):
    - toFun : X -> Y
    - map_smul' : 对任意 (m : M) (x : X), toFun (m • x) = (φ m) • toFun x

Depends on / 依赖: MulActionHom, MulActionHomLocal
-/
structure MulActionHom where
  /-- The underlying function. -/
  protected toFun : X -> Y
  /-- The proposition that the function commutes with the actions. -/
  protected map_smul' : forall (m : M) (x : X), toFun (m • x) = (φ m) • toFun x

/-- `φ`-equivariant functions `X → Y`,
where `φ : M → N`, where `M` and `N` act on `X` and `Y` respectively. -/
notation:25 (name := «MulActionHomLocal≺») X " ->ₑ[" φ:25 "] " Y:0 => MulActionHom φ X Y

/-- `M`-equivariant functions `X → Y` with respect to the action of `M`.
This is the same as `X →ₑ[@id M] Y`. -/
notation:25 (name := «MulActionHomIdLocal≺») X " ->[" M:25 "] " Y:0 => MulActionHom (@id M) X Y

/-- `φ`-equivariant functions `X → Y`,
where `φ : M → N`, where `M` and `N` act additively on `X` and `Y` respectively

We use the same notation as for multiplicative actions, as conflicts are unlikely. -/
notation:25 (name := «AddActionHomLocal≺») X " ->ₑ[" φ:25 "] " Y:0 => AddActionHom φ X Y

/-- `M`-equivariant functions `X → Y` with respect to the additive action of `M`.
This is the same as `X →ₑ[@id M] Y`.

We use the same notation as for multiplicative actions, as conflicts are unlikely. -/
notation:25 (name := «AddActionHomIdLocal≺») X " ->[" M:25 "] " Y:0 => AddActionHom (@id M) X Y

/--
Definition of `AddActionSemiHomClass` / `AddActionSemiHomClass` 的定义

English:
class AddActionSemiHomClass
  parameters: (F : Type*)
  axioms and operations (1):
    - map_vaddₛₗ : forall (f : F) (c : M) (x : X), f (c +ᵥ x) = (φ c) +ᵥ (f x)

中文:
类 AddActionSemiHomClass
  参数: (F : 类型)
  公理与运算 (1 个):
    - map_vaddₛₗ : 对任意 (f : F) (c : M) (x : X), f (c +ᵥ x) = (φ c) +ᵥ (f x)
-/
class AddActionSemiHomClass (F : Type*)
    {M N : outParam Type*} (φ : outParam (M -> N))
    (X Y : outParam Type*) [VAdd M X] [VAdd N Y] [FunLike F X Y] : Prop where
  /-- The proposition that the function preserves the action. -/
  map_vaddₛₗ : forall (f : F) (c : M) (x : X), f (c +ᵥ x) = (φ c) +ᵥ (f x)

/-- `MulActionSemiHomClass F φ X Y` states that
  `F` is a type of morphisms which are `φ`-equivariant.

You should extend this class when you extend `MulActionHom`. -/
@[to_additive]
/--
Definition of `MulActionSemiHomClass` / `MulActionSemiHomClass` 的定义

English:
class MulActionSemiHomClass
  parameters: (F : Type*)
  axioms and operations (1):
    - map_smulₛₗ : forall (f : F) (c : M) (x : X), f (c • x) = (φ c) • (f x)

中文:
类 MulActionSemiHomClass
  参数: (F : 类型)
  公理与运算 (1 个):
    - map_smulₛₗ : 对任意 (f : F) (c : M) (x : X), f (c • x) = (φ c) • (f x)
-/
class MulActionSemiHomClass (F : Type*)
    {M N : outParam Type*} (φ : outParam (M -> N))
    (X Y : outParam Type*) [SMul M X] [SMul N Y] [FunLike F X Y] : Prop where
  /-- The proposition that the function preserves the action. -/
  map_smulₛₗ : forall (f : F) (c : M) (x : X), f (c • x) = (φ c) • (f x)

export MulActionSemiHomClass (map_smulₛₗ)
export AddActionSemiHomClass (map_vaddₛₗ)

/-- `MulActionHomClass F M X Y` states that `F` is a type of
morphisms which are equivariant with respect to actions of `M`
This is an abbreviation of `MulActionSemiHomClass`. -/
@[to_additive /-- `MulActionHomClass F M X Y` states that `F` is a type of
morphisms which are equivariant with respect to actions of `M`
This is an abbreviation of `MulActionSemiHomClass`. -/]
/--
Definition of `MulActionHomClass` / `MulActionHomClass` 的定义

English:
abbreviation MulActionHomClass
  signature: (F : Type*) (M : outParam Type*)
  body: MulActionSemiHomClass F (@id M) X Y

中文:
缩写 MulActionHomClass
  签名: (F : 类型) (M : outParam 类型)
  定义体: MulActionSemiHomClass F (@id M) X Y

Depends on / 依赖: MulActionSemiHomClass
-/
abbrev MulActionHomClass (F : Type*) (M : outParam Type*)
    (X Y : outParam Type*) [SMul M X] [SMul M Y] [FunLike F X Y] :=
  MulActionSemiHomClass F (@id M) X Y

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (MulActionHom φ X Y) X Y
  body: MulActionHom.toFun
  coe_injective f g h := by cases f; cases g; congr

@[to_additive (attr := simp)]

中文:
实例 :
  签名: FunLike (MulActionHom φ X Y) X Y
  定义体: MulActionHom.toFun
  coe_injective f g h := by cases f; cases g; congr

@[to_additive (attr := simp)]
-/
@[to_additive] instance : FunLike (MulActionHom φ X Y) X Y where
  coe := MulActionHom.toFun
  coe_injective f g h := by cases f; cases g; congr

@[to_additive (attr := simp)]
/--
theorem `map_smul` / 定理 `map_smul`

English:
theorem map_smul
  statement: {F M X Y : Type*} [SMul M X] [SMul M Y]
  proof: map_smulₛₗ f c x

@[to_additive]

中文:
定理 map_smul
  结论: {F M X Y : 类型} [SMul M X] [SMul M Y]
  证明: map_smulₛₗ f c x

@[to_additive]
-/
theorem map_smul {F M X Y : Type*} [SMul M X] [SMul M Y]
    [FunLike F X Y] [MulActionHomClass F M X Y]
    (f : F) (c : M) (x : X) : f (c • x) = c • f x :=
  map_smulₛₗ f c x

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulActionSemiHomClass (X ->ₑ[φ] Y) φ X Y
  body: MulActionHom.map_smul'

initialize_simps_projections MulActionHom (toFun -> apply)
initialize_simps_projections AddActionHom (toFun -> apply)

中文:
实例 :
  签名: MulActionSemiHomClass (X ->ₑ[φ] Y) φ X Y
  定义体: MulActionHom.map_smul'

initialize_simps_projections MulActionHom (toFun -> apply)
initialize_simps_projections AddActionHom (toFun -> apply)

Depends on / 依赖: MulActionHom, MulActionHom.map_smul, map_smul
-/
instance : MulActionSemiHomClass (X ->ₑ[φ] Y) φ X Y where
  map_smulₛₗ := MulActionHom.map_smul'

initialize_simps_projections MulActionHom (toFun -> apply)
initialize_simps_projections AddActionHom (toFun -> apply)

namespace MulActionHom

variable {φ X Y}
variable {F : Type*} [FunLike F X Y]

/-- Turn an element of a type `F` satisfying `MulActionSemiHomClass F φ X Y`
  into an actual `MulActionHom`.
  This is declared as the default coercion from `F` to `MulActionSemiHom φ X Y`. -/
@[to_additive (attr := coe)
  /-- Turn an element of a type `F` satisfying `AddActionSemiHomClass F φ X Y`
  into an actual `AddActionHom`.
  This is declared as the default coercion from `F` to `AddActionSemiHom φ X Y`. -/]
/--
Definition of `_root_.MulActionSemiHomClass.toMulActionHom` / `_root_.MulActionSemiHomClass.toMulActionHom` 的定义

English:
definition _root_.MulActionSemiHomClass.toMulActionHom
  signature: [MulActionSemiHomClass F φ X Y] (f : F)
  body: DFunLike.coe f
  map_smul' := map_smulₛₗ f

中文:
定义 _root_.MulActionSemiHomClass.toMulActionHom
  签名: [MulActionSemiHomClass F φ X Y] (f : F)
  定义体: DFunLike.coe f
  map_smul' := map_smulₛₗ f

Depends on / 依赖: DFunLike, DFunLike.coe
-/
def _root_.MulActionSemiHomClass.toMulActionHom [MulActionSemiHomClass F φ X Y] (f : F) :
    X ->ₑ[φ] Y where
  toFun := DFunLike.coe f
  map_smul' := map_smulₛₗ f

/-- Any type satisfying `MulActionSemiHomClass` can be cast into `MulActionHom` via
  `MulActionHomSemiClass.toMulActionHom`. -/
@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulActionSemiHomClass
  signature: F φ X Y] : CoeTC F (X ->ₑ[φ] Y)
  body: ⟨MulActionSemiHomClass.toMulActionHom⟩

中文:
实例 [MulActionSemiHomClass
  签名: F φ X Y] : CoeTC F (X ->ₑ[φ] Y)
  定义体: ⟨MulActionSemiHomClass.toMulActionHom⟩

Depends on / 依赖: MulActionSemiHomClass, MulActionSemiHomClass.toMulActionHom, toMulActionHom
-/
instance [MulActionSemiHomClass F φ X Y] : CoeTC F (X ->ₑ[φ] Y) :=
  ⟨MulActionSemiHomClass.toMulActionHom⟩

variable (M' X Y F) in
/-- If Y/X/M forms a scalar tower, any map X → Y preserving X-action also preserves M-action. -/
@[to_additive]
/--
theorem `_root_.IsScalarTower.smulHomClass` / 定理 `_root_.IsScalarTower.smulHomClass`

English:
theorem _root_.IsScalarTower.smulHomClass
  statement: [MulOneClass X] [SMul X Y] [IsScalarTower M' X Y]
  proof: by
    rw [← mul_one (m • x)]; rw [← smul_eq_mul]; rw [map_smul]; rw [smul_assoc]; rw [← map_smul]; rw [smul_eq_mul]; rw [mul_one]; rw [id_eq]

@[to_additive]

中文:
定理 _root_.IsScalarTower.smulHomClass
  结论: [MulOneClass X] [SMul X Y] [IsScalarTower M' X Y]
  证明: by
    rw [← mul_one (m • x)]; rw [← smul_eq_mul]; rw [map_smul]; rw [smul_assoc]; rw [← map_smul]; rw [smul_eq_mul]; rw [mul_one]; rw [id_eq]

@[to_additive]

Depends on / 依赖: id_eq, map_smul, mul_one, smul_assoc, smul_eq_mul
-/
theorem _root_.IsScalarTower.smulHomClass [MulOneClass X] [SMul X Y] [IsScalarTower M' X Y]
    [MulActionHomClass F X X Y] : MulActionHomClass F M' X Y where
  map_smulₛₗ f m x := by
    rw [← mul_one (m • x)]; rw [← smul_eq_mul]; rw [map_smul]; rw [smul_assoc]; rw [← map_smul]; rw [smul_eq_mul]; rw [mul_one]; rw [id_eq]

@[to_additive]
/--
theorem `map_smul` / 定理 `map_smul`

English:
theorem map_smul
  given: (f : X ->[M'] Y) (m : M') (x : X)
  statement: f (m • x) = m • f x
  proof: map_smul f m x

@[to_additive (attr := ext)]

中文:
定理 map_smul
  条件: (f : X ->[M'] Y) (m : M') (x : X)
  结论: f (m • x) = m • f x
  证明: map_smul f m x

@[to_additive (attr := ext)]
-/
protected theorem map_smul (f : X ->[M'] Y) (m : M') (x : X) : f (m • x) = m • f x :=
  map_smul f m x

@[to_additive (attr := ext)]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : X ->ₑ[φ] Y}
  proof: DFunLike.ext f g

@[to_additive]

中文:
定理 ext
  条件: {f g : X ->ₑ[φ] Y}
  证明: DFunLike.ext f g

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : X ->ₑ[φ] Y} :
    (forall x, f x = g x) -> f = g :=
  DFunLike.ext f g

@[to_additive]
/--
theorem `congr_fun` / 定理 `congr_fun`

English:
theorem congr_fun
  given: {f g : X ->ₑ[φ] Y} (h : f = g) (x : X)
  proof: DFunLike.congr_fun h _

中文:
定理 congr_fun
  条件: {f g : X ->ₑ[φ] Y} (h : f = g) (x : X)
  证明: DFunLike.congr_fun h _
-/
protected theorem congr_fun {f g : X ->ₑ[φ] Y} (h : f = g) (x : X) :
    f x = g x :=
  DFunLike.congr_fun h _

/-- Two equal maps on scalars give rise to an equivariant map for identity -/
@[to_additive /-- Two equal maps on scalars give rise to an equivariant map for identity -/]
/--
Definition of `ofEq` / `ofEq` 的定义

English:
definition ofEq
  signature: {φ' : M -> N} (h : φ = φ') (f : X ->ₑ[φ] Y)
  body: f.toFun
  map_smul' m a := h ▸ f.map_smul' m a

@[to_additive (attr := simp)]

中文:
定义 ofEq
  签名: {φ' : M -> N} (h : φ = φ') (f : X ->ₑ[φ] Y)
  定义体: f.toFun
  map_smul' m a := h ▸ f.map_smul' m a

@[to_additive (attr := simp)]

Depends on / 依赖: f.toFun
-/
def ofEq {φ' : M -> N} (h : φ = φ') (f : X ->ₑ[φ] Y) : X ->ₑ[φ'] Y where
  toFun := f.toFun
  map_smul' m a := h ▸ f.map_smul' m a

@[to_additive (attr := simp)]
/--
theorem `ofEq_coe` / 定理 `ofEq_coe`

English:
theorem ofEq_coe
  given: {φ' : M -> N} (h : φ = φ') (f : X ->ₑ[φ] Y)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 ofEq_coe
  条件: {φ' : M -> N} (h : φ = φ') (f : X ->ₑ[φ] Y)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem ofEq_coe {φ' : M -> N} (h : φ = φ') (f : X ->ₑ[φ] Y) :
    (f.ofEq h).toFun = f.toFun := rfl

@[to_additive (attr := simp)]
/--
theorem `ofEq_apply` / 定理 `ofEq_apply`

English:
theorem ofEq_apply
  given: {φ' : M -> N} (h : φ = φ') (f : X ->ₑ[φ] Y) (a : X)
  proof: rfl

中文:
定理 ofEq_apply
  条件: {φ' : M -> N} (h : φ = φ') (f : X ->ₑ[φ] Y) (a : X)
  证明: rfl
-/
theorem ofEq_apply {φ' : M -> N} (h : φ = φ') (f : X ->ₑ[φ] Y) (a : X) :
    (f.ofEq h) a = f a :=
  rfl

/--
lemma `_root_.FaithfulSMul.of_injective` / 引理 `_root_.FaithfulSMul.of_injective`

English:
lemma _root_.FaithfulSMul.of_injective
  proof: eq_of_smul_eq_smul fun m => hf by simp_rw [map_smul, h]

中文:
引理 _root_.FaithfulSMul.of_injective
  证明: eq_of_smul_eq_smul fun m => hf by simp_rw [map_smul, h]

Depends on / 依赖: eq_of_smul_eq_smul, map_smul, simp_rw
-/
lemma _root_.FaithfulSMul.of_injective
    [FaithfulSMul M' X] [MulActionHomClass F M' X Y] (f : F)
    (hf : Function.Injective f) :
    FaithfulSMul M' Y where
eq_of_smul_eq_smul {_ _} h := eq_of_smul_eq_smul fun m => hf by simp_rw [map_smul, h]

variable {ψ χ} (M N)

/-- The identity map as an equivariant map. -/
@[to_additive (attr := instance_reducible) /-- The identity map as an equivariant map. -/]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : X ->[M] X
  body: ⟨fun x => x, fun _ _ => rfl⟩

中文:
定义 id
  签名: : X ->[M] X
  定义体: ⟨fun x => x, fun _ _ => rfl⟩
-/
protected def id : X ->[M] X :=
  ⟨fun x => x, fun _ _ => rfl⟩

variable {M N Z}

@[to_additive (attr := simp)]
/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (x : X)
  proof: rfl

中文:
定理 id_apply
  条件: (x : X)
  证明: rfl
-/
theorem id_apply (x : X) :
    MulActionHom.id M x = x :=
  rfl

end MulActionHom

namespace MulActionHom
open MulActionHom

variable {φ ψ χ X Y Z}

-- attribute [instance] CompTriple.id_comp CompTriple.comp_id

/-- Composition of two equivariant maps. -/
@[to_additive (attr := instance_reducible) /-- Composition of two equivariant maps. -/]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (g : Y ->ₑ[ψ] Z) (f : X ->ₑ[φ] Y) [κ : CompTriple φ ψ χ]
  body: ⟨fun x => g (f x), fun m x =>
    calc
      g (f (m • x)) = g (φ m • f x) := by rw [map_smulₛₗ]
      _ = ψ (φ m) • g (f x) := by rw [map_smulₛₗ]
      _ = (ψ ∘ φ) m • g (f x) := rfl
      _ = χ m • g (f x) := by rw [κ.comp_eq] ⟩

@[to_additive (attr := simp)]

中文:
定义 comp
  签名: (g : Y ->ₑ[ψ] Z) (f : X ->ₑ[φ] Y) [κ : CompTriple φ ψ χ]
  定义体: ⟨fun x => g (f x), fun m x =>
    calc
      g (f (m • x)) = g (φ m • f x) := by rw [map_smulₛₗ]
      _ = ψ (φ m) • g (f x) := by rw [map_smulₛₗ]
      _ = (ψ ∘ φ) m • g (f x) := rfl
      _ = χ m • g (f x) := by rw [κ.comp_eq] ⟩

@[to_additive (attr := simp)]

Depends on / 依赖: comp_eq
-/
def comp (g : Y ->ₑ[ψ] Z) (f : X ->ₑ[φ] Y) [κ : CompTriple φ ψ χ] :
    X ->ₑ[χ] Z :=
  ⟨fun x => g (f x), fun m x =>
    calc
      g (f (m • x)) = g (φ m • f x) := by rw [map_smulₛₗ]
      _ = ψ (φ m) • g (f x) := by rw [map_smulₛₗ]
      _ = (ψ ∘ φ) m • g (f x) := rfl
      _ = χ m • g (f x) := by rw [κ.comp_eq] ⟩

@[to_additive (attr := simp)]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 comp_apply
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem comp_apply
    (g : Y ->ₑ[ψ] Z) (f : X ->ₑ[φ] Y) [CompTriple φ ψ χ] (x : X) :
    g.comp f x = g (f x) := rfl

@[to_additive (attr := simp)]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : X ->ₑ[φ] Y)
  proof: ext fun x => by rw [comp_apply, id_apply]

@[to_additive (attr := simp)]

中文:
定理 id_comp
  条件: (f : X ->ₑ[φ] Y)
  证明: ext fun x => by rw [comp_apply, id_apply]

@[to_additive (attr := simp)]

Depends on / 依赖: comp_apply, id_apply
-/
theorem id_comp (f : X ->ₑ[φ] Y) :
    (MulActionHom.id N).comp f = f :=
  ext fun x => by rw [comp_apply, id_apply]

@[to_additive (attr := simp)]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : X ->ₑ[φ] Y)
  proof: ext fun x => by rw [comp_apply, id_apply]

@[to_additive (attr := simp)]

中文:
定理 comp_id
  条件: (f : X ->ₑ[φ] Y)
  证明: ext fun x => by rw [comp_apply, id_apply]

@[to_additive (attr := simp)]

Depends on / 依赖: comp_apply, id_apply
-/
theorem comp_id (f : X ->ₑ[φ] Y) :
    f.comp (MulActionHom.id M) = f :=
  ext fun x => by rw [comp_apply, id_apply]

@[to_additive (attr := simp)]
/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  statement: {Q T : Type*} [SMul Q T]
  proof: ext fun _ => rfl

中文:
定理 comp_assoc
  结论: {Q T : 类型} [SMul Q T]
  证明: ext fun _ => rfl
-/
theorem comp_assoc {Q T : Type*} [SMul Q T]
    {η : P -> Q} {θ : M -> Q} {ζ : N -> Q}
    (h : Z ->ₑ[η] T) (g : Y ->ₑ[ψ] Z) (f : X ->ₑ[φ] Y)
    [CompTriple φ ψ χ] [CompTriple χ η θ]
    [CompTriple ψ η ζ] [CompTriple φ ζ θ] :
    h.comp (g.comp f) = (h.comp g).comp f :=
  ext fun _ => rfl

variable {φ' : N -> M}
variable {Y₁ : Type*} [SMul M Y₁]

/-- The inverse of a bijective equivariant map is equivariant. -/
@[to_additive (attr := simps) /-- The inverse of a bijective equivariant map is equivariant. -/]
/--
Definition of `inverse` / `inverse` 的定义

English:
definition inverse
  signature: (f : X ->[M] Y₁) (g : Y₁ -> X)
  body: g
  map_smul' m x :=
    calc
      g (m • x) = g (m • f (g x)) := by rw [h₂]
      _ = g (f (m • g x)) := by simp only [map_smul]
      _ = m • g x := by rw [h₁]

中文:
定义 inverse
  签名: (f : X ->[M] Y₁) (g : Y₁ -> X)
  定义体: g
  map_smul' m x :=
    calc
      g (m • x) = g (m • f (g x)) := by rw [h₂]
      _ = g (f (m • g x)) := by simp only [map_smul]
      _ = m • g x := by rw [h₁]
-/
def inverse (f : X ->[M] Y₁) (g : Y₁ -> X)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : Y₁ ->[M] X where
  toFun := g
  map_smul' m x :=
    calc
      g (m • x) = g (m • f (g x)) := by rw [h₂]
      _ = g (f (m • g x)) := by simp only [map_smul]
      _ = m • g x := by rw [h₁]


/-- The inverse of a bijective equivariant map is equivariant. -/
@[to_additive (attr := simps) /-- The inverse of a bijective equivariant map is equivariant. -/]
/--
Definition of `inverse'` / `inverse'` 的定义

English:
definition inverse'
  signature: (f : X ->ₑ[φ] Y) (g : Y -> X) (k : Function.RightInverse φ' φ)
  body: g
  map_smul' m x :=
    calc
      g (m • x) = g (m • f (g x)) := by rw [h₂]
      _ = g ((φ (φ' m)) • f (g x)) := by rw [k]
      _ = g (f (φ' m • g x)) := by rw [map_smulₛₗ]
      _ = φ' m • g x := by rw [h₁]

@[to_additive]

中文:
定义 inverse'
  签名: (f : X ->ₑ[φ] Y) (g : Y -> X) (k : Function.RightInverse φ' φ)
  定义体: g
  map_smul' m x :=
    calc
      g (m • x) = g (m • f (g x)) := by rw [h₂]
      _ = g ((φ (φ' m)) • f (g x)) := by rw [k]
      _ = g (f (φ' m • g x)) := by rw [map_smulₛₗ]
      _ = φ' m • g x := by rw [h₁]

@[to_additive]
-/
def inverse' (f : X ->ₑ[φ] Y) (g : Y -> X) (k : Function.RightInverse φ' φ)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
    Y ->ₑ[φ'] X where
  toFun := g
  map_smul' m x :=
    calc
      g (m • x) = g (m • f (g x)) := by rw [h₂]
      _ = g ((φ (φ' m)) • f (g x)) := by rw [k]
      _ = g (f (φ' m • g x)) := by rw [map_smulₛₗ]
      _ = φ' m • g x := by rw [h₁]

@[to_additive]
/--
lemma `inverse_eq_inverse'` / 引理 `inverse_eq_inverse'`

English:
lemma inverse_eq_inverse'
  statement: (f : X ->[M] Y₁) (g : Y₁ -> X)
  proof: by
  rfl

@[to_additive]

中文:
引理 inverse_eq_inverse'
  结论: (f : X ->[M] Y₁) (g : Y₁ -> X)
  证明: by
  rfl

@[to_additive]
-/
lemma inverse_eq_inverse' (f : X ->[M] Y₁) (g : Y₁ -> X)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
    inverse f g h₁ h₂ = inverse' f g (congrFun rfl) h₁ h₂ := by
  rfl

@[to_additive]
/--
theorem `inverse'_inverse'` / 定理 `inverse'_inverse'`

English:
theorem inverse'_inverse'
  proof: ext fun _ => rfl

@[to_additive]

中文:
定理 inverse'_inverse'
  证明: ext fun _ => rfl

@[to_additive]
-/
theorem inverse'_inverse'
    {f : X ->ₑ[φ] Y} {g : Y -> X}
    {k₁ : Function.LeftInverse φ' φ} {k₂ : Function.RightInverse φ' φ}
    {h₁ : Function.LeftInverse g f} {h₂ : Function.RightInverse g f} :
    inverse' (inverse' f g k₂ h₁ h₂) f k₁ h₂ h₁ = f :=
  ext fun _ => rfl

@[to_additive]
/--
theorem `comp_inverse'` / 定理 `comp_inverse'`

English:
theorem comp_inverse'
  statement: {f : X ->ₑ[φ] Y} {g : Y -> X}
  proof: by
  ext
  simpa using h₁.eq _

@[to_additive]

中文:
定理 comp_inverse'
  结论: {f : X ->ₑ[φ] Y} {g : Y -> X}
  证明: by
  ext
  simpa using h₁.eq _

@[to_additive]

Depends on / 依赖: CompTriple, CompTriple.comp_inv, MulActionHom, MulActionHom.id, comp_inv
-/
theorem comp_inverse' {f : X ->ₑ[φ] Y} {g : Y -> X}
    {k₁ : Function.LeftInverse φ' φ} {k₂ : Function.RightInverse φ' φ}
    {h₁ : Function.LeftInverse g f} {h₂ : Function.RightInverse g f} :
    (inverse' f g k₂ h₁ h₂).comp f (κ := CompTriple.comp_inv k₁) = MulActionHom.id M := by
  ext
  simpa using h₁.eq _

@[to_additive]
/--
theorem `inverse'_comp` / 定理 `inverse'_comp`

English:
theorem inverse'_comp
  statement: {f : X ->ₑ[φ] Y} {g : Y -> X}
  proof: by
  ext
  simpa using h₂.eq _

中文:
定理 inverse'_comp
  结论: {f : X ->ₑ[φ] Y} {g : Y -> X}
  证明: by
  ext
  simpa using h₂.eq _
-/
theorem inverse'_comp {f : X ->ₑ[φ] Y} {g : Y -> X}
    {k₂ : Function.RightInverse φ' φ}
    {h₁ : Function.LeftInverse g f} {h₂ : Function.RightInverse g f} :
    f.comp (inverse' f g k₂ h₁ h₂) (κ := CompTriple.comp_inv k₂) = MulActionHom.id N := by
  ext
  simpa using h₂.eq _

/-- If actions of `M` and `N` on `α` commute,
  then for `c : M`, `(c • · : α → α)` is an `N`-action homomorphism. -/
@[to_additive (attr := simps) /-- If additive actions of `M` and `N` on `α` commute,
  then for `c : M`, `(c • · : α → α)` is an `N`-additive action homomorphism. -/]
/--
Definition of `_root_.SMulCommClass.toMulActionHom` / `_root_.SMulCommClass.toMulActionHom` 的定义

English:
definition _root_.SMulCommClass.toMulActionHom
  signature: {M} (N α : Type*)
  body: (c • ·)
  map_smul' := smul_comm _

中文:
定义 _root_.SMulCommClass.toMulActionHom
  签名: {M} (N α : 类型)
  定义体: (c • ·)
  map_smul' := smul_comm _
-/
def _root_.SMulCommClass.toMulActionHom {M} (N α : Type*)
    [SMul M α] [SMul N α] [SMulCommClass M N α] (c : M) :
    α ->[N] α where
  toFun := (c • ·)
  map_smul' := smul_comm _

end MulActionHom

end MulActionHom

/-- Evaluation at a point as a `MulActionHom`. -/
@[to_additive (attr := simps) /-- Evaluation at a point as an `AddActionHom`. -/]
/--
Definition of `Pi.evalMulActionHom` / `Pi.evalMulActionHom` 的定义

English:
definition Pi.evalMulActionHom
  signature: {ι M : Type*} {X : ι -> Type*} [forall i, SMul M (X i)] (i : ι)
  body: Function.eval i
  map_smul' _ _ := rfl

中文:
定义 Pi.evalMulActionHom
  签名: {ι M : 类型} {X : ι -> 类型} [对任意 i, SMul M (X i)] (i : ι)
  定义体: Function.eval i
  map_smul' _ _ := rfl

Depends on / 依赖: Function, Function.eval
-/
def Pi.evalMulActionHom {ι M : Type*} {X : ι -> Type*} [forall i, SMul M (X i)] (i : ι) :
    (forall i, X i) ->[M] X i where
  toFun := Function.eval i
  map_smul' _ _ := rfl

namespace MulActionHom

section FstSnd

variable {M α β : Type*} [SMul M α] [SMul M β]

variable (M α β) in
/-- `Prod.fst` as a bundled `MulActionHom`. -/
@[to_additive (attr := simps -fullyApplied) /-- `Prod.fst` as a bundled `AddActionHom`. -/]
/--
Definition of `fst` / `fst` 的定义

English:
definition fst
  signature: : α × β ->[M] α where
  body: Prod.fst
  map_smul' _ _ := rfl

中文:
定义 fst
  签名: : α × β ->[M] α where
  定义体: Prod.fst
  map_smul' _ _ := rfl

Depends on / 依赖: Prod.fst
-/
def fst : α × β ->[M] α where
  toFun := Prod.fst
  map_smul' _ _ := rfl

variable (M α β) in
/-- `Prod.snd` as a bundled `MulActionHom`. -/
@[to_additive (attr := simps -fullyApplied) /-- `Prod.snd` as a bundled `AddActionHom`. -/]
/--
Definition of `snd` / `snd` 的定义

English:
definition snd
  signature: : α × β ->[M] β where
  body: Prod.snd
  map_smul' _ _ := rfl

中文:
定义 snd
  签名: : α × β ->[M] β where
  定义体: Prod.snd
  map_smul' _ _ := rfl

Depends on / 依赖: Prod.snd
-/
def snd : α × β ->[M] β where
  toFun := Prod.snd
  map_smul' _ _ := rfl

end FstSnd

variable {M N α β γ δ : Type*} [SMul M α] [SMul M β] [SMul N γ] [SMul N δ] {σ : M -> N}

/-- If `f` and `g` are equivariant maps, then so is `x ↦ (f x, g x)`. -/
@[to_additive (attr := simps -fullyApplied) prod
  /-- If `f` and `g` are equivariant maps, then so is `x ↦ (f x, g x)`. -/]
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (f : α ->ₑ[σ] γ) (g : α ->ₑ[σ] δ)
  body: (f x, g x)
  map_smul' _ _ := Prod.ext (map_smulₛₗ f _ _) (map_smulₛₗ g _ _)

@[to_additive (attr := simp) fst_comp_prod]

中文:
定义 prod
  签名: (f : α ->ₑ[σ] γ) (g : α ->ₑ[σ] δ)
  定义体: (f x, g x)
  map_smul' _ _ := Prod.ext (map_smulₛₗ f _ _) (map_smulₛₗ g _ _)

@[to_additive (attr := simp) fst_comp_prod]
-/
def prod (f : α ->ₑ[σ] γ) (g : α ->ₑ[σ] δ) : α ->ₑ[σ] γ × δ where
  toFun x := (f x, g x)
  map_smul' _ _ := Prod.ext (map_smulₛₗ f _ _) (map_smulₛₗ g _ _)

@[to_additive (attr := simp) fst_comp_prod]
/--
lemma `fst_comp_prod` / 引理 `fst_comp_prod`

English:
lemma fst_comp_prod
  given: (f : α ->ₑ[σ] γ) (g : α ->ₑ[σ] δ)
  statement: (fst _ _ _).comp (prod f g) = f
  proof: rfl

@[to_additive (attr := simp) snd_comp_prod]

中文:
引理 fst_comp_prod
  条件: (f : α ->ₑ[σ] γ) (g : α ->ₑ[σ] δ)
  结论: (fst _ _ _).comp (prod f g) = f
  证明: rfl

@[to_additive (attr := simp) snd_comp_prod]
-/
lemma fst_comp_prod (f : α ->ₑ[σ] γ) (g : α ->ₑ[σ] δ) : (fst _ _ _).comp (prod f g) = f := rfl

@[to_additive (attr := simp) snd_comp_prod]
/--
lemma `snd_comp_prod` / 引理 `snd_comp_prod`

English:
lemma snd_comp_prod
  given: (f : α ->ₑ[σ] γ) (g : α ->ₑ[σ] δ)
  statement: (snd _ _ _).comp (prod f g) = g
  proof: rfl

@[to_additive (attr := simp) prod_fst_snd]

中文:
引理 snd_comp_prod
  条件: (f : α ->ₑ[σ] γ) (g : α ->ₑ[σ] δ)
  结论: (snd _ _ _).comp (prod f g) = g
  证明: rfl

@[to_additive (attr := simp) prod_fst_snd]
-/
lemma snd_comp_prod (f : α ->ₑ[σ] γ) (g : α ->ₑ[σ] δ) : (snd _ _ _).comp (prod f g) = g := rfl

@[to_additive (attr := simp) prod_fst_snd]
/--
lemma `prod_fst_snd` / 引理 `prod_fst_snd`

English:
lemma prod_fst_snd
  statement: prod (fst M α β) (snd M α β) = .id ..
  proof: rfl

中文:
引理 prod_fst_snd
  结论: prod (fst M α β) (snd M α β) = .id ..
  证明: rfl
-/
lemma prod_fst_snd : prod (fst M α β) (snd M α β) = .id .. := rfl

/-- If `f` and `g` are equivariant maps, then so is `(x, y) ↦ (f x, g y)`. -/
@[to_additive (attr := simps -fullyApplied) prodMap
  /-- If `f` and `g` are equivariant maps, then so is `(x, y) ↦ (f x, g y)`. -/]
/--
Definition of `prodMap` / `prodMap` 的定义

English:
definition prodMap
  signature: (f : α ->ₑ[σ] γ) (g : β ->ₑ[σ] δ)
  body: Prod.map f g
  __ := (f.comp (fst ..)).prod (g.comp (snd ..))

中文:
定义 prodMap
  签名: (f : α ->ₑ[σ] γ) (g : β ->ₑ[σ] δ)
  定义体: Prod.map f g
  __ := (f.comp (fst ..)).prod (g.comp (snd ..))

Depends on / 依赖: Prod.map
-/
def prodMap (f : α ->ₑ[σ] γ) (g : β ->ₑ[σ] δ) : α × β ->ₑ[σ] γ × δ where
  toFun := Prod.map f g
  __ := (f.comp (fst ..)).prod (g.comp (snd ..))

end MulActionHom

namespace MulActionHom

variable {R M N X Y : Type*} {σ : M -> N}

attribute [local simp] map_smulₛₗ smul_sub

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: M X] [SMul N Y] [SMul R Y] [SMulCommClass N R Y] :
  body: ⟨h • f, by simp [smul_comm _ h]⟩

@[to_additive (attr := simp, norm_cast)]

中文:
实例 [SMul
  签名: M X] [SMul N Y] [SMul R Y] [SMulCommClass N R Y] :
  定义体: ⟨h • f, by simp [smul_comm _ h]⟩

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: smul_comm
-/
instance [SMul M X] [SMul N Y] [SMul R Y] [SMulCommClass N R Y] :
    SMul R (X ->ₑ[σ] Y) where
  smul h f := ⟨h • f, by simp [smul_comm _ h]⟩

@[to_additive (attr := simp, norm_cast)]
/--
lemma `coe_smul` / 引理 `coe_smul`

English:
lemma coe_smul
  given: [SMul M X] [SMul N Y] [SMul R Y] [SMulCommClass N R Y] (f : X ->ₑ[σ] Y) (r : R)
  proof: rfl

中文:
引理 coe_smul
  条件: [SMul M X] [SMul N Y] [SMul R Y] [SMulCommClass N R Y] (f : X ->ₑ[σ] Y) (r : R)
  证明: rfl
-/
lemma coe_smul [SMul M X] [SMul N Y] [SMul R Y] [SMulCommClass N R Y] (f : X ->ₑ[σ] Y) (r : R) :
    ⇑(r • f) = r • ⇑f := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: M X] [Zero Y] [SMulZeroClass N Y] :
  body: ⟨0, by simp⟩

@[simp, norm_cast]

中文:
实例 [SMul
  签名: M X] [Zero Y] [SMulZeroClass N Y] :
  定义体: ⟨0, by simp⟩

@[simp, norm_cast]
-/
instance [SMul M X] [Zero Y] [SMulZeroClass N Y] :
    Zero (X ->ₑ[σ] Y) where
  zero := ⟨0, by simp⟩

@[simp, norm_cast]
/--
lemma `coe_zero` / 引理 `coe_zero`

English:
lemma coe_zero
  given: [SMul M X] [Zero Y] [SMulZeroClass N Y]
  statement: ⇑(0 : X ->ₑ[σ] Y) = 0
  proof: rfl

中文:
引理 coe_zero
  条件: [SMul M X] [Zero Y] [SMulZeroClass N Y]
  结论: ⇑(0 : X ->ₑ[σ] Y) = 0
  证明: rfl
-/
lemma coe_zero [SMul M X] [Zero Y] [SMulZeroClass N Y] : ⇑(0 : X ->ₑ[σ] Y) = 0 := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: M X] [AddZeroClass Y] [DistribSMul N Y] :
  body: ⟨f + g, by simp [smul_add]⟩
  zero_add _ := ext fun _ => zero_add _
  add_zero _ := ext fun _ => add_zero _

@[simp, norm_cast]

中文:
实例 [SMul
  签名: M X] [AddZeroClass Y] [DistribSMul N Y] :
  定义体: ⟨f + g, by simp [smul_add]⟩
  zero_add _ := ext fun _ => zero_add _
  add_zero _ := ext fun _ => add_zero _

@[simp, norm_cast]

Depends on / 依赖: smul_add
-/
instance [SMul M X] [AddZeroClass Y] [DistribSMul N Y] :
    AddZeroClass (X ->ₑ[σ] Y) where
  add f g := ⟨f + g, by simp [smul_add]⟩
  zero_add _ := ext fun _ => zero_add _
  add_zero _ := ext fun _ => add_zero _

@[simp, norm_cast]
/--
lemma `coe_add` / 引理 `coe_add`

English:
lemma coe_add
  given: [SMul M X] [AddZeroClass Y] [DistribSMul N Y] (f g : X ->ₑ[σ] Y)
  proof: rfl

中文:
引理 coe_add
  条件: [SMul M X] [AddZeroClass Y] [DistribSMul N Y] (f g : X ->ₑ[σ] Y)
  证明: rfl
-/
lemma coe_add [SMul M X] [AddZeroClass Y] [DistribSMul N Y] (f g : X ->ₑ[σ] Y) :
    ⇑(f + g) = ⇑f + ⇑g := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: M X] [AddMonoid Y] [DistribSMul N Y] :
  body: ext fun _ => add_assoc _ _ _
  nsmul_zero f := ext fun x => AddMonoid.nsmul_zero (f x)
  nsmul_succ n f := ext fun x => AddMonoid.nsmul_succ n (f x)

中文:
实例 [SMul
  签名: M X] [AddMonoid Y] [DistribSMul N Y] :
  定义体: ext fun _ => add_assoc _ _ _
  nsmul_zero f := ext fun x => AddMonoid.nsmul_zero (f x)
  nsmul_succ n f := ext fun x => AddMonoid.nsmul_succ n (f x)

Depends on / 依赖: add_assoc
-/
instance [SMul M X] [AddMonoid Y] [DistribSMul N Y] :
    AddMonoid (X ->ₑ[σ] Y) where
  add_assoc _ _ _ := ext fun _ => add_assoc _ _ _
  nsmul_zero f := ext fun x => AddMonoid.nsmul_zero (f x)
  nsmul_succ n f := ext fun x => AddMonoid.nsmul_succ n (f x)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: M X] [AddCommMonoid Y] [DistribSMul N Y] :
  body: ext fun _ => add_comm _ _

@[to_additive]

中文:
实例 [SMul
  签名: M X] [AddCommMonoid Y] [DistribSMul N Y] :
  定义体: ext fun _ => add_comm _ _

@[to_additive]

Depends on / 依赖: add_comm
-/
instance [SMul M X] [AddCommMonoid Y] [DistribSMul N Y] :
    AddCommMonoid (X ->ₑ[σ] Y) where
  add_comm _ _ := ext fun _ => add_comm _ _

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: M X] [SMul N Y] [Monoid R] [MulAction R Y] [SMulCommClass N R Y] :
  body: ext fun _ => one_smul _ _
  mul_smul _ _ _ := ext fun _ => mul_smul _ _ _

中文:
实例 [SMul
  签名: M X] [SMul N Y] [Monoid R] [MulAction R Y] [SMulCommClass N R Y] :
  定义体: ext fun _ => one_smul _ _
  mul_smul _ _ _ := ext fun _ => mul_smul _ _ _

Depends on / 依赖: one_smul
-/
instance [SMul M X] [SMul N Y] [Monoid R] [MulAction R Y] [SMulCommClass N R Y] :
    MulAction R (X ->ₑ[σ] Y) where
  one_smul _ := ext fun _ => one_smul _ _
  mul_smul _ _ _ := ext fun _ => mul_smul _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddZeroClass
  signature: Y] [SMul M X] [DistribSMul N Y] [DistribSMul R Y] [SMulCommClass N R Y] :
  body: ext fun _ => smul_zero y
  smul_add y _ _ := ext fun _ => smul_add y _ _

中文:
实例 [AddZeroClass
  签名: Y] [SMul M X] [DistribSMul N Y] [DistribSMul R Y] [SMulCommClass N R Y] :
  定义体: ext fun _ => smul_zero y
  smul_add y _ _ := ext fun _ => smul_add y _ _

Depends on / 依赖: smul_zero
-/
instance [AddZeroClass Y] [SMul M X] [DistribSMul N Y] [DistribSMul R Y] [SMulCommClass N R Y] :
    DistribSMul R (X ->ₑ[σ] Y) where
  smul_zero y := ext fun _ => smul_zero y
  smul_add y _ _ := ext fun _ => smul_add y _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddMonoid
  signature: Y] [Monoid R] [SMul M X] [DistribSMul N Y]
  body: (inferInstance : MulAction _ _)
  __ := (inferInstance : DistribSMul _ _)

中文:
实例 [AddMonoid
  签名: Y] [Monoid R] [SMul M X] [DistribSMul N Y]
  定义体: (inferInstance : MulAction _ _)
  __ := (inferInstance : DistribSMul _ _)

Depends on / 依赖: MulAction
-/
instance [AddMonoid Y] [Monoid R] [SMul M X] [DistribSMul N Y]
    [DistribMulAction R Y] [SMulCommClass N R Y] :
    DistribMulAction R (X ->ₑ[σ] Y) where
  __ := (inferInstance : MulAction _ _)
  __ := (inferInstance : DistribSMul _ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommMonoid
  signature: Y] [Semiring R] [SMul M X] [DistribSMul N Y]
  body: ext fun _ => add_smul _ _ _
  zero_smul _ := ext fun _ => zero_smul R _

中文:
实例 [AddCommMonoid
  签名: Y] [Semiring R] [SMul M X] [DistribSMul N Y]
  定义体: ext fun _ => add_smul _ _ _
  zero_smul _ := ext fun _ => zero_smul R _

Depends on / 依赖: add_smul
-/
instance [AddCommMonoid Y] [Semiring R] [SMul M X] [DistribSMul N Y]
    [Module R Y] [SMulCommClass N R Y] :
    Module R (X ->ₑ[σ] Y) where
  add_smul _ _ _ := ext fun _ => add_smul _ _ _
  zero_smul _ := ext fun _ => zero_smul R _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: M X] [AddGroup Y] [DistribSMul N Y] : AddGroup (X ->ₑ[σ] Y) where
  body: ⟨f - g, by simp [smul_sub]⟩
  neg f := ⟨-f, by simp⟩
  neg_add_cancel f := ext fun _ => neg_add_cancel _
  sub_eq_add_neg _ _ := ext fun _ => sub_eq_add_neg _ _
  zsmul_zero' f := ext fun x => SubNegMonoid.zsmul_zero' _
  zsmul_neg' _ _ := ext fun x => SubNegMonoid.zsmul_neg' _ _
  zsmul_succ' _ _ :

中文:
实例 [SMul
  签名: M X] [AddGroup Y] [DistribSMul N Y] : AddGroup (X ->ₑ[σ] Y) where
  定义体: ⟨f - g, by simp [smul_sub]⟩
  neg f := ⟨-f, by simp⟩
  neg_add_cancel f := ext fun _ => neg_add_cancel _
  sub_eq_add_neg _ _ := ext fun _ => sub_eq_add_neg _ _
  zsmul_zero' f := ext fun x => SubNegMonoid.zsmul_zero' _
  zsmul_neg' _ _ := ext fun x => SubNegMonoid.zsmul_neg' _ _
  zsmul_succ' _ _ :

Depends on / 依赖: smul_sub
-/
instance [SMul M X] [AddGroup Y] [DistribSMul N Y] : AddGroup (X ->ₑ[σ] Y) where
  sub f g := ⟨f - g, by simp [smul_sub]⟩
  neg f := ⟨-f, by simp⟩
  neg_add_cancel f := ext fun _ => neg_add_cancel _
  sub_eq_add_neg _ _ := ext fun _ => sub_eq_add_neg _ _
  zsmul_zero' f := ext fun x => SubNegMonoid.zsmul_zero' _
  zsmul_neg' _ _ := ext fun x => SubNegMonoid.zsmul_neg' _ _
  zsmul_succ' _ _ := ext fun x => SubNegMonoid.zsmul_succ' _ _

@[simp, norm_cast]
/--
lemma `coe_neg` / 引理 `coe_neg`

English:
lemma coe_neg
  given: [SMul M X] [AddGroup Y] [DistribSMul N Y] (f : X ->ₑ[σ] Y)
  proof: rfl

@[simp, norm_cast]

中文:
引理 coe_neg
  条件: [SMul M X] [AddGroup Y] [DistribSMul N Y] (f : X ->ₑ[σ] Y)
  证明: rfl

@[simp, norm_cast]
-/
lemma coe_neg [SMul M X] [AddGroup Y] [DistribSMul N Y] (f : X ->ₑ[σ] Y) :
    ⇑(-f) = -⇑f := rfl

@[simp, norm_cast]
/--
lemma `coe_sub` / 引理 `coe_sub`

English:
lemma coe_sub
  given: [SMul M X] [AddGroup Y] [DistribSMul N Y] (f g : X ->ₑ[σ] Y)
  proof: rfl

中文:
引理 coe_sub
  条件: [SMul M X] [AddGroup Y] [DistribSMul N Y] (f g : X ->ₑ[σ] Y)
  证明: rfl
-/
lemma coe_sub [SMul M X] [AddGroup Y] [DistribSMul N Y] (f g : X ->ₑ[σ] Y) :
    ⇑(f - g) = ⇑f - ⇑g := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: M X] [AddCommGroup Y] [DistribSMul N Y] : AddCommGroup (X ->ₑ[σ] Y) where

中文:
实例 [SMul
  签名: M X] [AddCommGroup Y] [DistribSMul N Y] : AddCommGroup (X ->ₑ[σ] Y) where
-/
instance [SMul M X] [AddCommGroup Y] [DistribSMul N Y] : AddCommGroup (X ->ₑ[σ] Y) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: M X] [Monoid N] [Monoid Y] [MulDistribMulAction N Y] :
  body: ⟨f * g, by simp⟩
  mul_assoc _ _ _ := ext fun x => mul_assoc _ _ _
  one := ⟨1, by simp⟩
  one_mul _ := ext fun x => one_mul _
  mul_one _ := ext fun x => mul_one _

@[simp, norm_cast]

中文:
实例 [SMul
  签名: M X] [Monoid N] [Monoid Y] [MulDistribMulAction N Y] :
  定义体: ⟨f * g, by simp⟩
  mul_assoc _ _ _ := ext fun x => mul_assoc _ _ _
  one := ⟨1, by simp⟩
  one_mul _ := ext fun x => one_mul _
  mul_one _ := ext fun x => mul_one _

@[simp, norm_cast]
-/
instance [SMul M X] [Monoid N] [Monoid Y] [MulDistribMulAction N Y] :
    Monoid (X ->ₑ[σ] Y) where
  mul f g := ⟨f * g, by simp⟩
  mul_assoc _ _ _ := ext fun x => mul_assoc _ _ _
  one := ⟨1, by simp⟩
  one_mul _ := ext fun x => one_mul _
  mul_one _ := ext fun x => mul_one _

@[simp, norm_cast]
/--
lemma `coe_mul` / 引理 `coe_mul`

English:
lemma coe_mul
  given: [SMul M X] [Monoid N] [Monoid Y] [MulDistribMulAction N Y] (f g : X ->ₑ[σ] Y)
  proof: rfl

@[simp, norm_cast]

中文:
引理 coe_mul
  条件: [SMul M X] [Monoid N] [Monoid Y] [MulDistribMulAction N Y] (f g : X ->ₑ[σ] Y)
  证明: rfl

@[simp, norm_cast]
-/
lemma coe_mul [SMul M X] [Monoid N] [Monoid Y] [MulDistribMulAction N Y] (f g : X ->ₑ[σ] Y) :
    ⇑(f * g) = ⇑f * ⇑g := rfl

@[simp, norm_cast]
/--
lemma `coe_one` / 引理 `coe_one`

English:
lemma coe_one
  given: [SMul M X] [Monoid N] [Monoid Y] [MulDistribMulAction N Y]
  proof: rfl

中文:
引理 coe_one
  条件: [SMul M X] [Monoid N] [Monoid Y] [MulDistribMulAction N Y]
  证明: rfl
-/
lemma coe_one [SMul M X] [Monoid N] [Monoid Y] [MulDistribMulAction N Y] :
    ⇑(1 : X ->ₑ[σ] Y) = 1 := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: M X] [Monoid N] [CommMonoid Y] [MulDistribMulAction N Y] :
  body: ext fun _ => mul_comm _ _

中文:
实例 [SMul
  签名: M X] [Monoid N] [CommMonoid Y] [MulDistribMulAction N Y] :
  定义体: ext fun _ => mul_comm _ _

Depends on / 依赖: mul_comm
-/
instance [SMul M X] [Monoid N] [CommMonoid Y] [MulDistribMulAction N Y] :
    CommMonoid (X ->ₑ[σ] Y) where
  mul_comm _ _ := ext fun _ => mul_comm _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: M X] [Monoid N] [Semiring Y] [MulSemiringAction N Y] :
  body: (inferInstance : Monoid _)
  __ := (inferInstance : AddCommMonoid _)
  zero_mul _ := ext fun x => zero_mul _
  mul_zero _ := ext fun x => mul_zero _
  left_distrib _ _ _ := ext fun x => left_distrib _ _ _
  right_distrib _ _ _ := ext fun x => right_distrib _ _ _

中文:
实例 [SMul
  签名: M X] [Monoid N] [Semiring Y] [MulSemiringAction N Y] :
  定义体: (inferInstance : Monoid _)
  __ := (inferInstance : AddCommMonoid _)
  zero_mul _ := ext fun x => zero_mul _
  mul_zero _ := ext fun x => mul_zero _
  left_distrib _ _ _ := ext fun x => left_distrib _ _ _
  right_distrib _ _ _ := ext fun x => right_distrib _ _ _

Depends on / 依赖: Monoid
-/
instance [SMul M X] [Monoid N] [Semiring Y] [MulSemiringAction N Y] :
    Semiring (X ->ₑ[σ] Y) where
  __ := (inferInstance : Monoid _)
  __ := (inferInstance : AddCommMonoid _)
  zero_mul _ := ext fun x => zero_mul _
  mul_zero _ := ext fun x => mul_zero _
  left_distrib _ _ _ := ext fun x => left_distrib _ _ _
  right_distrib _ _ _ := ext fun x => right_distrib _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: M X] [Monoid N] [CommSemiring Y] [MulSemiringAction N Y] :

中文:
实例 [SMul
  签名: M X] [Monoid N] [CommSemiring Y] [MulSemiringAction N Y] :
-/
instance [SMul M X] [Monoid N] [CommSemiring Y] [MulSemiringAction N Y] :
    CommSemiring (X ->ₑ[σ] Y) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: M X] [Monoid N] [Ring Y] [MulSemiringAction N Y] :

中文:
实例 [SMul
  签名: M X] [Monoid N] [Ring Y] [MulSemiringAction N Y] :
-/
instance [SMul M X] [Monoid N] [Ring Y] [MulSemiringAction N Y] :
    Ring (X ->ₑ[σ] Y) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: M X] [Monoid N] [CommRing Y] [MulSemiringAction N Y] :

中文:
实例 [SMul
  签名: M X] [Monoid N] [CommRing Y] [MulSemiringAction N Y] :
-/
instance [SMul M X] [Monoid N] [CommRing Y] [MulSemiringAction N Y] :
    CommRing (X ->ₑ[σ] Y) where

namespace End

/-- For a monoid `M` acting on a type `X`, the `M`-equivariant functions from `X` to itself
form a monoid under composition. -/
@[to_additive /-- For an additive monoid `M` acting on a type `X`, the `M`-equivariant functions
from `X` to itself form an additive monoid under composition. -/]
local instance [SMul M X] : Monoid (X ->[M] X) where
  mul f g := f.comp g
  mul_assoc _ _ _ := rfl
  one := .id _
  one_mul _ := rfl
  mul_one _ := rfl

/--
theorem `mul_def` / 定理 `mul_def`

English:
theorem mul_def
  given: [SMul M X] {f g : X ->[M] X}
  statement: f * g = f.comp g
  proof: rfl

中文:
定理 mul_def
  条件: [SMul M X] {f g : X ->[M] X}
  结论: f * g = f.comp g
  证明: rfl
-/
@[to_additive (attr := simp)] theorem mul_def [SMul M X] {f g : X ->[M] X} : f * g = f.comp g := rfl

/-- The `M`-equivariant functions from a monoid `M` to itself are exactly
right multiplications by elements of `M`. See also `RingEquiv.moduleEndSelf`. -/
@[to_additive (attr := simps)
/-- The `M`-equivariant functions from an additive monoid `M` to itself are exactly
right additions by elements of `M`. -/]
/--
Definition of `equivMulOpposite` / `equivMulOpposite` 的定义

English:
definition equivMulOpposite
  signature: [Monoid M]
  body: .op (f 1)
  invFun m := .mk (· * m.unop) fun _ _ => mul_assoc ..
  left_inv f := by ext m; change m • f 1 = _; rw [← map_smul, smul_eq_mul, mul_one]
  right_inv := mul_one
map_mul' f g := congr_arg MulOpposite.op by
    dsimp [← smul_eq_mul]; simp_rw [← map_smul, smul_eq_mul, mul_one]; rfl

中文:
定义 equivMulOpposite
  签名: [Monoid M]
  定义体: .op (f 1)
  invFun m := .mk (· * m.unop) fun _ _ => mul_assoc ..
  left_inv f := by ext m; change m • f 1 = _; rw [← map_smul, smul_eq_mul, mul_one]
  right_inv := mul_one
map_mul' f g := congr_arg MulOpposite.op by
    dsimp [← smul_eq_mul]; simp_rw [← map_smul, smul_eq_mul, mul_one]; rfl
-/
def equivMulOpposite [Monoid M] : (M ->[M] M) ≃* Mᵐᵒᵖ where
  toFun f := .op (f 1)
  invFun m := .mk (· * m.unop) fun _ _ => mul_assoc ..
  left_inv f := by ext m; change m • f 1 = _; rw [← map_smul, smul_eq_mul, mul_one]
  right_inv := mul_one
map_mul' f g := congr_arg MulOpposite.op by
    dsimp [← smul_eq_mul]; simp_rw [← map_smul, smul_eq_mul, mul_one]; rfl

/-- The functions from a monoid `M` to itself equivariant with respect to the right `M`-action
are exactly left multiplications by elements of `M`. See also `RingEquiv.moduleEndSelfOp`. -/
@[to_additive (attr := simps)
/-- The functions from an additive monoid `M` to itself equivariant with respect to
the right `M`-action are exactly left additions by elements of `M`. -/]
/--
Definition of `mulOppositeEquiv` / `mulOppositeEquiv` 的定义

English:
definition mulOppositeEquiv
  signature: [Monoid M]
  body: f 1
  invFun m := .mk (m * ·) fun _ _ => (mul_assoc ..).symm
  left_inv f := by ext m; change MulOpposite.op m • f 1 = _; simp [← map_smul]
  right_inv := mul_one
  map_mul' f g := show _ = MulOpposite.op (g 1) • f 1 by simp [← map_smul]

中文:
定义 mulOppositeEquiv
  签名: [Monoid M]
  定义体: f 1
  invFun m := .mk (m * ·) fun _ _ => (mul_assoc ..).symm
  left_inv f := by ext m; change MulOpposite.op m • f 1 = _; simp [← map_smul]
  right_inv := mul_one
  map_mul' f g := show _ = MulOpposite.op (g 1) • f 1 by simp [← map_smul]
-/
def mulOppositeEquiv [Monoid M] : (M ->[Mᵐᵒᵖ] M) ≃* M where
  toFun f := f 1
  invFun m := .mk (m * ·) fun _ _ => (mul_assoc ..).symm
  left_inv f := by ext m; change MulOpposite.op m • f 1 = _; simp [← map_smul]
  right_inv := mul_one
  map_mul' f g := show _ = MulOpposite.op (g 1) • f 1 by simp [← map_smul]

end End

end MulActionHom

section DistribMulAction

variable {M : Type*} [Monoid M]
variable {N : Type*} [Monoid N]
variable {P : Type*} [Monoid P]
variable (φ : M ->* N) (φ' : N ->* M) (ψ : N ->* P) (χ : M ->* P)
variable (A : Type*) [Monoid A] [MulDistribMulAction M A]
variable (B : Type*) [Monoid B] [MulDistribMulAction N B]
variable (B₁ : Type*) [Monoid B₁] [MulDistribMulAction M B₁]
variable (C : Type*) [Monoid C] [MulDistribMulAction P C]

variable (A' : Type*) [Group A'] [MulDistribMulAction M A']
variable (B' : Type*) [Group B'] [MulDistribMulAction N B']

set_option linter.translateOverwrite false in
attribute [to_additive existing (dont_translate := M) DistribMulAction]
  MulDistribMulAction

/--
Definition of `DistribMulActionHom` / `DistribMulActionHom` 的定义

English:
structure DistribMulActionHom
  parameters: (A : Type*) [AddMonoid A] [DistribMulAction M A] (B : Type*)
  extends: A ->ₑ[φ] B, A ->+ B
  (no additional axioms)

中文:
结构 DistribMulActionHom
  参数: (A : 类型) [AddMonoid A] [DistribMulAction M A] (B : 类型)
  继承: A ->ₑ[φ] B, A ->+ B
  (无附加公理)
-/
structure DistribMulActionHom (A : Type*) [AddMonoid A] [DistribMulAction M A] (B : Type*)
    [AddMonoid B] [DistribMulAction N B] extends A ->ₑ[φ] B, A ->+ B

/-- Equivariant monoid homomorphisms. -/
@[to_additive (dont_translate := M N) DistribMulActionHom]
/--
Definition of `MulDistribMulActionHom` / `MulDistribMulActionHom` 的定义

English:
structure MulDistribMulActionHom
  parameters: extends A ->ₑ[φ] B, A ->* B
  extends: A ->ₑ[φ] B, A ->* B
  (no additional axioms)

中文:
结构 MulDistribMulActionHom
  参数: extends A ->ₑ[φ] B, A ->* B
  继承: A ->ₑ[φ] B, A ->* B
  (无附加公理)
-/
structure MulDistribMulActionHom extends A ->ₑ[φ] B, A ->* B

/-- Reinterpret an equivariant additive monoid homomorphism as an additive monoid homomorphism. -/
add_decl_doc DistribMulActionHom.toAddMonoidHom

/-- Reinterpret an equivariant additive monoid homomorphism as an equivariant function. -/
add_decl_doc DistribMulActionHom.toMulActionHom

/-- Reinterpret an equivariant monoid homomorphism as a monoid homomorphism. -/
add_decl_doc MulDistribMulActionHom.toMonoidHom

/-- Reinterpret an equivariant monoid homomorphism as an equivariant function. -/
add_decl_doc MulDistribMulActionHom.toMulActionHom

@[inherit_doc]
notation:25 (name := «DistribMulActionHomLocal≺»)
  A " ->ₑ+[" φ:25 "] " B:0 => DistribMulActionHom φ A B

@[inherit_doc]
notation:25 (name := «DistribMulActionHomIdLocal≺»)
  A " ->+[" M:25 "] " B:0 => DistribMulActionHom (MonoidHom.id M) A B

@[inherit_doc]
notation:25 (name := «MulDistribMulActionHomLocal≺»)
  A " ->ₑ*[" φ:25 "] " B:0 => MulDistribMulActionHom φ A B

@[inherit_doc]
notation:25 (name := «MulDistribMulActionHomIdLocal≺»)
  A " ->*[" M:25 "] " B:0 => MulDistribMulActionHom (MonoidHom.id M) A B

-- QUESTION/TODO : Impose that `φ` is a morphism of monoids?

/--
Definition of `DistribMulActionSemiHomClass` / `DistribMulActionSemiHomClass` 的定义

English:
class DistribMulActionSemiHomClass
  parameters: (F : Type*)
  extends: MulActionSemiHomClass F φ A B, AddMonoidHomClass F A B
  (no additional axioms)

中文:
类 DistribMulActionSemiHomClass
  参数: (F : 类型)
  继承: MulActionSemiHomClass F φ A B, AddMonoidHomClass F A B
  (无附加公理)
-/
class DistribMulActionSemiHomClass (F : Type*)
    {M N : outParam Type*} (φ : outParam (M -> N))
    (A B : outParam Type*)
    [Monoid M] [Monoid N]
    [AddMonoid A] [AddMonoid B] [DistribMulAction M A] [DistribMulAction N B]
    [FunLike F A B] : Prop
    extends MulActionSemiHomClass F φ A B, AddMonoidHomClass F A B

/-- `MulDistribMulActionSemiHomClass F φ A B` states that `F` is a type of morphisms
preserving the monoid structure and equivariant with respect to `φ`.
You should extend this class when you extend `MulDistribMulActionSemiHom`. -/
@[to_additive existing (dont_translate := M N) DistribMulActionSemiHomClass]
/--
Definition of `MulDistribMulActionSemiHomClass` / `MulDistribMulActionSemiHomClass` 的定义

English:
class MulDistribMulActionSemiHomClass
  parameters: (F : Type*)
  extends: MulActionSemiHomClass F φ A B, MonoidHomClass F A B
  (no additional axioms)

中文:
类 MulDistribMulActionSemiHomClass
  参数: (F : 类型)
  继承: MulActionSemiHomClass F φ A B, MonoidHomClass F A B
  (无附加公理)
-/
class MulDistribMulActionSemiHomClass (F : Type*)
    {M N : outParam Type*} (φ : outParam (M -> N))
    (A B : outParam Type*)
    [Monoid M] [Monoid N]
    [Monoid A] [Monoid B] [MulDistribMulAction M A] [MulDistribMulAction N B]
    [FunLike F A B] : Prop
    extends MulActionSemiHomClass F φ A B, MonoidHomClass F A B

/-- `MulDistribMulActionHomClass F M A B` states that `F` is a type of morphisms preserving
the monoid structure and equivariant with respect to the action of `M`.
It is an abbreviation to `MulDistribMulActionHomClass F (MonoidHom.id M) A B`
You should extend this class when you extend `MulDistribMulActionHom`. -/
@[to_additive (dont_translate := M) DistribMulActionHomClass
/-- `DistribMulActionHomClass F M A B` states that `F` is a type of morphisms preserving
the additive monoid structure and equivariant with respect to the action of `M`.
It is an abbreviation to `DistribMulActionHomClass F (MonoidHom.id M) A B`
You should extend this class when you extend `DistribMulActionHom`. -/]
/--
Definition of `MulDistribMulActionHomClass` / `MulDistribMulActionHomClass` 的定义

English:
abbreviation MulDistribMulActionHomClass
  signature: (F : Type*) (M : outParam Type*)
  body: MulDistribMulActionSemiHomClass F (MonoidHom.id M) A B

中文:
缩写 MulDistribMulActionHomClass
  签名: (F : 类型) (M : outParam 类型)
  定义体: MulDistribMulActionSemiHomClass F (MonoidHom.id M) A B

Depends on / 依赖: MonoidHom, MonoidHom.id, MulDistribMulActionSemiHomClass
-/
abbrev MulDistribMulActionHomClass (F : Type*) (M : outParam Type*)
    (A B : outParam Type*) [Monoid M] [Monoid A] [Monoid B]
    [MulDistribMulAction M A] [MulDistribMulAction M B] [FunLike F A B] :=
    MulDistribMulActionSemiHomClass F (MonoidHom.id M) A B

namespace MulDistribMulActionHom

@[to_additive (dont_translate := M N)]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (A ->ₑ*[φ] B) A B
  body: m.toFun
  coe_injective f g h := by
    rcases f with ⟨tF, _, _⟩; rcases g with ⟨tG, _, _⟩
    cases tF; cases tG; congr

@[to_additive (dont_translate := M N)]

中文:
实例 :
  签名: FunLike (A ->ₑ*[φ] B) A B
  定义体: m.toFun
  coe_injective f g h := by
    rcases f with ⟨tF, _, _⟩; rcases g with ⟨tG, _, _⟩
    cases tF; cases tG; congr

@[to_additive (dont_translate := M N)]

Depends on / 依赖: m.toFun
-/
instance : FunLike (A ->ₑ*[φ] B) A B where
  coe m := m.toFun
  coe_injective f g h := by
    rcases f with ⟨tF, _, _⟩; rcases g with ⟨tG, _, _⟩
    cases tF; cases tG; congr

@[to_additive (dont_translate := M N)]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulDistribMulActionSemiHomClass (A ->ₑ*[φ] B) φ A B
  body: m.map_smul'
  map_one := MulDistribMulActionHom.map_one'
  map_mul := MulDistribMulActionHom.map_mul'

中文:
实例 :
  签名: MulDistribMulActionSemiHomClass (A ->ₑ*[φ] B) φ A B
  定义体: m.map_smul'
  map_one := MulDistribMulActionHom.map_one'
  map_mul := MulDistribMulActionHom.map_mul'

Depends on / 依赖: m.map_smul, map_smul
-/
instance : MulDistribMulActionSemiHomClass (A ->ₑ*[φ] B) φ A B where
  map_smulₛₗ m := m.map_smul'
  map_one := MulDistribMulActionHom.map_one'
  map_mul := MulDistribMulActionHom.map_mul'

variable {φ φ' A B B₁}
variable {F : Type*} [FunLike F A B]

/-- Turn an element of a type `F` satisfying `MulDistribMulActionHomClass F M X Y` into an actual
`MulDistribMulActionHom`. This is declared as the default coercion from `F` to
`MulDistribMulActionHom M X Y`. -/
@[to_additive (attr := coe) (dont_translate := M N) toDistribMulActionHom
/-- Turn an element of a type `F` satisfying `DistribMulActionHomClass F M X Y` into an actual
`DistribMulActionHom`. This is declared as the default coercion from `F` to
`DistribMulActionHom M X Y`. -/]
/--
Definition of `_root_.MulDistribMulActionSemiHomClass.toMulDistribMulActionHom` / `_root_.MulDistribMulActionSemiHomClass.toMulDistribMulActionHom` 的定义

English:
definition _root_.MulDistribMulActionSemiHomClass.toMulDistribMulActionHom
  body: { (f : A ->* B), (f : A ->ₑ[φ] B) with }

中文:
定义 _root_.MulDistribMulActionSemiHomClass.toMulDistribMulActionHom
  定义体: { (f : A ->* B), (f : A ->ₑ[φ] B) with }
-/
def _root_.MulDistribMulActionSemiHomClass.toMulDistribMulActionHom
    [MulDistribMulActionSemiHomClass F φ A B]
    (f : F) : A ->ₑ*[φ] B :=
  { (f : A ->* B), (f : A ->ₑ[φ] B) with }

/-- Any type satisfying `MulDistribMulActionSemiHomClass` can be cast into `MulDistribMulActionHom`
via `MulDistribMulActionSemiHomClass.toMulDistribMulActionHom`. -/
@[to_additive (dont_translate := M N)
/-- Any type satisfying `DistribMulActionSemiHomClass` can be cast into `DistribMulActionHom`
via `DistribMulActionSemiHomClass.toDistribMulActionHom`. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulDistribMulActionSemiHomClass
  signature: F φ A B] : CoeTC F (A ->ₑ*[φ] B)
  body: ⟨MulDistribMulActionSemiHomClass.toMulDistribMulActionHom⟩

中文:
实例 [MulDistribMulActionSemiHomClass
  签名: F φ A B] : CoeTC F (A ->ₑ*[φ] B)
  定义体: ⟨MulDistribMulActionSemiHomClass.toMulDistribMulActionHom⟩

Depends on / 依赖: MulDistribMulActionSemiHomClass, MulDistribMulActionSemiHomClass.toMulDistribMulActionHom, toMulDistribMulActionHom
-/
instance [MulDistribMulActionSemiHomClass F φ A B] : CoeTC F (A ->ₑ*[φ] B) :=
  ⟨MulDistribMulActionSemiHomClass.toMulDistribMulActionHom⟩

/-- If `DistribMulAction` of `M` and `N` on `A` commute,
then for each `c : M`, `(c • ·)` is an `N`-action additive homomorphism. -/
@[simps]
/--
Definition of `_root_.SMulCommClass.toDistribMulActionHom` / `_root_.SMulCommClass.toDistribMulActionHom` 的定义

English:
definition _root_.SMulCommClass.toDistribMulActionHom
  signature: {M} (N A : Type*) [Monoid N] [AddMonoid A]
  body: { SMulCommClass.toMulActionHom N A c,
    DistribSMul.toAddMonoidHom _ c with
    toFun := (c • ·) }

@[to_additive (attr := simp) (dont_translate := M N)]

中文:
定义 _root_.SMulCommClass.toDistribMulActionHom
  签名: {M} (N A : 类型) [Monoid N] [AddMonoid A]
  定义体: { SMulCommClass.toMulActionHom N A c,
    DistribSMul.toAddMonoidHom _ c with
    toFun := (c • ·) }

@[to_additive (attr := simp) (dont_translate := M N)]

Depends on / 依赖: DistribSMul, DistribSMul.toAddMonoidHom, SMulCommClass, SMulCommClass.toMulActionHom, toAddMonoidHom, toMulActionHom
-/
def _root_.SMulCommClass.toDistribMulActionHom {M} (N A : Type*) [Monoid N] [AddMonoid A]
    [DistribSMul M A] [DistribMulAction N A] [SMulCommClass M N A] (c : M) : A ->+[N] A :=
  { SMulCommClass.toMulActionHom N A c,
    DistribSMul.toAddMonoidHom _ c with
    toFun := (c • ·) }

@[to_additive (attr := simp) (dont_translate := M N)]
/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: (f : A ->ₑ*[φ] B)
  statement: f.toFun = f
  proof: rfl

@[to_additive (attr := norm_cast) (dont_translate := M N)]

中文:
定理 toFun_eq_coe
  条件: (f : A ->ₑ*[φ] B)
  结论: f.toFun = f
  证明: rfl

@[to_additive (attr := norm_cast) (dont_translate := M N)]
-/
theorem toFun_eq_coe (f : A ->ₑ*[φ] B) : f.toFun = f := rfl

@[to_additive (attr := norm_cast) (dont_translate := M N)]
/--
theorem `coe_fn_coe` / 定理 `coe_fn_coe`

English:
theorem coe_fn_coe
  given: (f : A ->ₑ*[φ] B)
  statement: ⇑(f : A ->* B) = f
  proof: rfl

@[to_additive (attr := norm_cast) (dont_translate := M N)]

中文:
定理 coe_fn_coe
  条件: (f : A ->ₑ*[φ] B)
  结论: ⇑(f : A ->* B) = f
  证明: rfl

@[to_additive (attr := norm_cast) (dont_translate := M N)]
-/
theorem coe_fn_coe (f : A ->ₑ*[φ] B) : ⇑(f : A ->* B) = f :=
  rfl

@[to_additive (attr := norm_cast) (dont_translate := M N)]
/--
theorem `coe_fn_coe'` / 定理 `coe_fn_coe'`

English:
theorem coe_fn_coe'
  given: (f : A ->ₑ*[φ] B)
  statement: ⇑(f : A ->ₑ[φ] B) = f
  proof: rfl

@[to_additive (attr := ext) (dont_translate := M N)]

中文:
定理 coe_fn_coe'
  条件: (f : A ->ₑ*[φ] B)
  结论: ⇑(f : A ->ₑ[φ] B) = f
  证明: rfl

@[to_additive (attr := ext) (dont_translate := M N)]
-/
theorem coe_fn_coe' (f : A ->ₑ*[φ] B) : ⇑(f : A ->ₑ[φ] B) = f :=
  rfl

@[to_additive (attr := ext) (dont_translate := M N)]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : A ->ₑ*[φ] B}
  statement: (forall x, f x = g x) -> f = g
  proof: DFunLike.ext f g

@[to_additive (dont_translate := M N)]

中文:
定理 ext
  条件: {f g : A ->ₑ*[φ] B}
  结论: (对任意 x, f x = g x) -> f = g
  证明: DFunLike.ext f g

@[to_additive (dont_translate := M N)]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : A ->ₑ*[φ] B} : (forall x, f x = g x) -> f = g :=
  DFunLike.ext f g

@[to_additive (dont_translate := M N)]
/--
theorem `congr_fun` / 定理 `congr_fun`

English:
theorem congr_fun
  given: {f g : A ->ₑ*[φ] B} (h : f = g) (x : A)
  statement: f x = g x
  proof: DFunLike.congr_fun h _

@[to_additive (dont_translate := M N)]

中文:
定理 congr_fun
  条件: {f g : A ->ₑ*[φ] B} (h : f = g) (x : A)
  结论: f x = g x
  证明: DFunLike.congr_fun h _

@[to_additive (dont_translate := M N)]
-/
protected theorem congr_fun {f g : A ->ₑ*[φ] B} (h : f = g) (x : A) : f x = g x :=
  DFunLike.congr_fun h _

@[to_additive (dont_translate := M N)]
/--
theorem `toMulActionHom_injective` / 定理 `toMulActionHom_injective`

English:
theorem toMulActionHom_injective
  given: {f g : A ->ₑ*[φ] B} (h : (f : A ->ₑ[φ] B) = (g : A ->ₑ[φ] B))
  proof: by
  ext a
  exact MulActionHom.congr_fun h a

@[to_additive (dont_translate := M N)]

中文:
定理 toMulActionHom_injective
  条件: {f g : A ->ₑ*[φ] B} (h : (f : A ->ₑ[φ] B) = (g : A ->ₑ[φ] B))
  证明: by
  ext a
  exact MulActionHom.congr_fun h a

@[to_additive (dont_translate := M N)]

Depends on / 依赖: MulActionHom, MulActionHom.congr_fun, congr_fun
-/
theorem toMulActionHom_injective {f g : A ->ₑ*[φ] B} (h : (f : A ->ₑ[φ] B) = (g : A ->ₑ[φ] B)) :
    f = g := by
  ext a
  exact MulActionHom.congr_fun h a

@[to_additive (dont_translate := M N)]
/--
theorem `toMonoidHom_injective` / 定理 `toMonoidHom_injective`

English:
theorem toMonoidHom_injective
  given: {f g : A ->ₑ*[φ] B} (h : (f : A ->* B) = (g : A ->* B))
  statement: f = g
  proof: by
  ext a
  exact DFunLike.congr_fun h a

@[to_additive (dont_translate := M N)]

中文:
定理 toMonoidHom_injective
  条件: {f g : A ->ₑ*[φ] B} (h : (f : A ->* B) = (g : A ->* B))
  结论: f = g
  证明: by
  ext a
  exact DFunLike.congr_fun h a

@[to_additive (dont_translate := M N)]

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun
-/
theorem toMonoidHom_injective {f g : A ->ₑ*[φ] B} (h : (f : A ->* B) = (g : A ->* B)) : f = g := by
  ext a
  exact DFunLike.congr_fun h a

@[to_additive (dont_translate := M N)]
/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  given: (f : A ->ₑ*[φ] B)
  statement: f 1 = 1
  proof: map_one f

@[to_additive (dont_translate := M N)]

中文:
定理 map_zero
  条件: (f : A ->ₑ*[φ] B)
  结论: f 1 = 1
  证明: map_one f

@[to_additive (dont_translate := M N)]
-/
protected theorem map_zero (f : A ->ₑ*[φ] B) : f 1 = 1 :=
  map_one f

@[to_additive (dont_translate := M N)]
/--
theorem `map_mul` / 定理 `map_mul`

English:
theorem map_mul
  given: (f : A ->ₑ*[φ] B) (x y : A)
  statement: f (x * y) = f x * f y
  proof: map_mul f x y

@[to_additive (dont_translate := M N)]

中文:
定理 map_mul
  条件: (f : A ->ₑ*[φ] B) (x y : A)
  结论: f (x * y) = f x * f y
  证明: map_mul f x y

@[to_additive (dont_translate := M N)]
-/
protected theorem map_mul (f : A ->ₑ*[φ] B) (x y : A) : f (x * y) = f x * f y :=
  map_mul f x y

@[to_additive (dont_translate := M N)]
/--
theorem `map_inv` / 定理 `map_inv`

English:
theorem map_inv
  given: (f : A' ->ₑ*[φ] B') (x : A')
  statement: f x⁻¹ = (f x)⁻¹
  proof: map_inv f x

@[to_additive (dont_translate := M N)]

中文:
定理 map_inv
  条件: (f : A' ->ₑ*[φ] B') (x : A')
  结论: f x⁻¹ = (f x)⁻¹
  证明: map_inv f x

@[to_additive (dont_translate := M N)]
-/
protected theorem map_inv (f : A' ->ₑ*[φ] B') (x : A') : f x⁻¹ = (f x)⁻¹ :=
  map_inv f x

@[to_additive (dont_translate := M N)]
/--
theorem `map_sub` / 定理 `map_sub`

English:
theorem map_sub
  given: (f : A' ->ₑ*[φ] B') (x y : A')
  statement: f (x / y) = f x / f y
  proof: map_div f x y

@[to_additive (dont_translate := M N)]

中文:
定理 map_sub
  条件: (f : A' ->ₑ*[φ] B') (x y : A')
  结论: f (x / y) = f x / f y
  证明: map_div f x y

@[to_additive (dont_translate := M N)]
-/
protected theorem map_sub (f : A' ->ₑ*[φ] B') (x y : A') : f (x / y) = f x / f y :=
  map_div f x y

@[to_additive (dont_translate := M N)]
/--
theorem `map_smulₑ` / 定理 `map_smulₑ`

English:
theorem map_smulₑ
  given: (f : A ->ₑ*[φ] B) (m : M) (x : A)
  statement: f (m • x) = (φ m) • f x
  proof: map_smulₛₗ f m x

中文:
定理 map_smulₑ
  条件: (f : A ->ₑ*[φ] B) (m : M) (x : A)
  结论: f (m • x) = (φ m) • f x
  证明: map_smulₛₗ f m x
-/
protected theorem map_smulₑ (f : A ->ₑ*[φ] B) (m : M) (x : A) : f (m • x) = (φ m) • f x :=
  map_smulₛₗ f m x

variable (M)

/-- The identity map as an equivariant monoid homomorphism. -/
@[to_additive (dont_translate := M) (attr := instance_reducible)
/-- The identity map as an equivariant additive monoid homomorphism. -/]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : A ->*[M] A
  body: ⟨MulActionHom.id _, rfl, fun _ _ => rfl⟩

@[to_additive (attr := simp) (dont_translate := M)]

中文:
定义 id
  签名: : A ->*[M] A
  定义体: ⟨MulActionHom.id _, rfl, fun _ _ => rfl⟩

@[to_additive (attr := simp) (dont_translate := M)]
-/
protected def id : A ->*[M] A :=
  ⟨MulActionHom.id _, rfl, fun _ _ => rfl⟩

@[to_additive (attr := simp) (dont_translate := M)]
/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (x : A)
  statement: MulDistribMulActionHom.id M x = x
  proof: by
  rfl

中文:
定理 id_apply
  条件: (x : A)
  结论: MulDistribMulActionHom.id M x = x
  证明: by
  rfl
-/
theorem id_apply (x : A) : MulDistribMulActionHom.id M x = x := by
  rfl

variable {M C ψ χ}

/--
Instance `_root_.DistriMulActionHom.instZero` / 实例 `_root_.DistriMulActionHom.instZero`

English:
instance _root_.DistriMulActionHom.instZero
  signature: {A : Type*} [AddMonoid A] [DistribMulAction M A]
  body: ⟨{ (0 : A ->+ B) with map_smul' := fun m _ => by simp }⟩

@[to_additive (dont_translate := M)]

中文:
实例 _root_.DistriMulActionHom.instZero
  签名: {A : 类型} [AddMonoid A] [DistribMulAction M A]
  定义体: ⟨{ (0 : A ->+ B) with map_smul' := fun m _ => by simp }⟩

@[to_additive (dont_translate := M)]

Depends on / 依赖: map_smul
-/
instance _root_.DistriMulActionHom.instZero {A : Type*} [AddMonoid A] [DistribMulAction M A]
    {B : Type*} [AddMonoid B] [DistribMulAction N B] : Zero (A ->ₑ+[φ] B) :=
  ⟨{ (0 : A ->+ B) with map_smul' := fun m _ => by simp }⟩

@[to_additive (dont_translate := M)]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (A ->*[M] A)
  body: ⟨MulDistribMulActionHom.id M⟩

@[simp]

中文:
实例 :
  签名: One (A ->*[M] A)
  定义体: ⟨MulDistribMulActionHom.id M⟩

@[simp]

Depends on / 依赖: MulDistribMulActionHom, MulDistribMulActionHom.id
-/
instance : One (A ->*[M] A) :=
  ⟨MulDistribMulActionHom.id M⟩

@[simp]
/--
theorem `_root_.DistriMulActionHom.coe_zero` / 定理 `_root_.DistriMulActionHom.coe_zero`

English:
theorem _root_.DistriMulActionHom.coe_zero
  statement: {A : Type*} [AddMonoid A] [DistribMulAction M A]
  proof: rfl

@[to_additive (attr := simp) (dont_translate := M)]

中文:
定理 _root_.DistriMulActionHom.coe_zero
  结论: {A : 类型} [AddMonoid A] [DistribMulAction M A]
  证明: rfl

@[to_additive (attr := simp) (dont_translate := M)]
-/
theorem _root_.DistriMulActionHom.coe_zero {A : Type*} [AddMonoid A] [DistribMulAction M A]
    {B : Type*} [AddMonoid B] [DistribMulAction N B] : ⇑(0 : A ->ₑ+[φ] B) = 0 :=
  rfl

@[to_additive (attr := simp) (dont_translate := M)]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ⇑(1 : A ->*[M] A) = id
  proof: rfl

中文:
定理 coe_one
  结论: ⇑(1 : A ->*[M] A) = id
  证明: rfl
-/
theorem coe_one : ⇑(1 : A ->*[M] A) = id :=
  rfl

/--
theorem `_root_.DistriMulActionHom.zero_apply` / 定理 `_root_.DistriMulActionHom.zero_apply`

English:
theorem _root_.DistriMulActionHom.zero_apply
  statement: {A : Type*} [AddMonoid A] [DistribMulAction M A]
  proof: rfl

@[to_additive (dont_translate := M)]

中文:
定理 _root_.DistriMulActionHom.zero_apply
  结论: {A : 类型} [AddMonoid A] [DistribMulAction M A]
  证明: rfl

@[to_additive (dont_translate := M)]
-/
theorem _root_.DistriMulActionHom.zero_apply {A : Type*} [AddMonoid A] [DistribMulAction M A]
    {B : Type*} [AddMonoid B] [DistribMulAction N B] (a : A) : (0 : A ->ₑ+[φ] B) a = 0 :=
  rfl

@[to_additive (dont_translate := M)]
/--
theorem `one_apply` / 定理 `one_apply`

English:
theorem one_apply
  given: (a : A)
  statement: (1 : A ->*[M] A) a = a
  proof: rfl

中文:
定理 one_apply
  条件: (a : A)
  结论: (1 : A ->*[M] A) a = a
  证明: rfl
-/
theorem one_apply (a : A) : (1 : A ->*[M] A) a = a :=
  rfl

instance {A : Type*} [AddMonoid A] [DistribMulAction M A]
    {B : Type*} [AddMonoid B] [DistribMulAction N B] :
    Inhabited (A ->ₑ+[φ] B) :=
  ⟨0⟩

/-- Composition of two equivariant monoid homomorphisms. -/
@[to_additive (dont_translate := M N P) (attr := instance_reducible)
/-- Composition of two equivariant additive monoid homomorphisms. -/]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: [κ : MonoidHom.CompTriple φ ψ χ]
  body: { MulActionHom.comp (g : B ->ₑ[ψ] C) (f : A ->ₑ[φ] B),
    MonoidHom.comp (g : B ->* C) (f : A ->* B) with }

@[to_additive (attr := simp) (dont_translate := M N P)]

中文:
定义 comp
  签名: [κ : MonoidHom.CompTriple φ ψ χ]
  定义体: { MulActionHom.comp (g : B ->ₑ[ψ] C) (f : A ->ₑ[φ] B),
    MonoidHom.comp (g : B ->* C) (f : A ->* B) with }

@[to_additive (attr := simp) (dont_translate := M N P)]

Depends on / 依赖: MonoidHom, MonoidHom.comp, MulActionHom, MulActionHom.comp
-/
def comp [κ : MonoidHom.CompTriple φ ψ χ]
    (g : B ->ₑ*[ψ] C) (f : A ->ₑ*[φ] B) : A ->ₑ*[χ] C :=
  { MulActionHom.comp (g : B ->ₑ[ψ] C) (f : A ->ₑ[φ] B),
    MonoidHom.comp (g : B ->* C) (f : A ->* B) with }

@[to_additive (attr := simp) (dont_translate := M N P)]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (g : B ->ₑ*[ψ] C) (f : A ->ₑ*[φ] B) [MonoidHom.CompTriple φ ψ χ] (x : A)
  proof: rfl

@[to_additive (attr := simp) (dont_translate := M N)]

中文:
定理 comp_apply
  条件: (g : B ->ₑ*[ψ] C) (f : A ->ₑ*[φ] B) [MonoidHom.CompTriple φ ψ χ] (x : A)
  证明: rfl

@[to_additive (attr := simp) (dont_translate := M N)]
-/
theorem comp_apply (g : B ->ₑ*[ψ] C) (f : A ->ₑ*[φ] B) [MonoidHom.CompTriple φ ψ χ] (x : A) :
    g.comp f x = g (f x) := rfl

@[to_additive (attr := simp) (dont_translate := M N)]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : A ->ₑ*[φ] B)
  statement: comp (MulDistribMulActionHom.id N) f = f
  proof: ext fun x => by rw [comp_apply, id_apply]

@[to_additive (attr := simp) (dont_translate := M N)]

中文:
定理 id_comp
  条件: (f : A ->ₑ*[φ] B)
  结论: comp (MulDistribMulActionHom.id N) f = f
  证明: ext fun x => by rw [comp_apply, id_apply]

@[to_additive (attr := simp) (dont_translate := M N)]

Depends on / 依赖: comp_apply, id_apply
-/
theorem id_comp (f : A ->ₑ*[φ] B) : comp (MulDistribMulActionHom.id N) f = f :=
  ext fun x => by rw [comp_apply, id_apply]

@[to_additive (attr := simp) (dont_translate := M N)]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : A ->ₑ*[φ] B)
  statement: f.comp (MulDistribMulActionHom.id M) = f
  proof: ext fun x => by rw [comp_apply, id_apply]

@[to_additive (attr := simp) (dont_translate := M N P Q)]

中文:
定理 comp_id
  条件: (f : A ->ₑ*[φ] B)
  结论: f.comp (MulDistribMulActionHom.id M) = f
  证明: ext fun x => by rw [comp_apply, id_apply]

@[to_additive (attr := simp) (dont_translate := M N P Q)]

Depends on / 依赖: comp_apply, id_apply
-/
theorem comp_id (f : A ->ₑ*[φ] B) : f.comp (MulDistribMulActionHom.id M) = f :=
  ext fun x => by rw [comp_apply, id_apply]

@[to_additive (attr := simp) (dont_translate := M N P Q)]
/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  statement: {Q D : Type*} [Monoid Q] [Monoid D] [MulDistribMulAction Q D]
  proof: ext fun _ => rfl

中文:
定理 comp_assoc
  结论: {Q D : 类型} [Monoid Q] [Monoid D] [MulDistribMulAction Q D]
  证明: ext fun _ => rfl
-/
theorem comp_assoc {Q D : Type*} [Monoid Q] [Monoid D] [MulDistribMulAction Q D]
    {η : P ->* Q} {θ : M ->* Q} {ζ : N ->* Q}
    (h : C ->ₑ*[η] D) (g : B ->ₑ*[ψ] C) (f : A ->ₑ*[φ] B)
    [MonoidHom.CompTriple φ ψ χ] [MonoidHom.CompTriple χ η θ]
    [MonoidHom.CompTriple ψ η ζ] [MonoidHom.CompTriple φ ζ θ] :
    h.comp (g.comp f) = (h.comp g).comp f :=
  ext fun _ => rfl

/-- The inverse of a bijective `MulDistribMulActionHom` is a `MulDistribMulActionHom`. -/
@[to_additive (attr := simp) (dont_translate := M)
/-- The inverse of a bijective `DistribMulActionHom` is a `DistribMulActionHom`. -/]
/--
Definition of `inverse` / `inverse` 的定义

English:
definition inverse
  signature: (f : A ->*[M] B₁) (g : B₁ -> A) (h₁ : Function.LeftInverse g f)
  body: { (f : A ->* B₁).inverse g h₁ h₂, f.toMulActionHom.inverse g h₁ h₂ with toFun := g }

中文:
定义 inverse
  签名: (f : A ->*[M] B₁) (g : B₁ -> A) (h₁ : Function.LeftInverse g f)
  定义体: { (f : A ->* B₁).inverse g h₁ h₂, f.toMulActionHom.inverse g h₁ h₂ with toFun := g }

Depends on / 依赖: f.toMulActionHom.inverse, inverse, toMulActionHom
-/
def inverse (f : A ->*[M] B₁) (g : B₁ -> A) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : B₁ ->*[M] A :=
  { (f : A ->* B₁).inverse g h₁ h₂, f.toMulActionHom.inverse g h₁ h₂ with toFun := g }

end MulDistribMulActionHom

section Semiring

variable (R : Type*) [Semiring R] [MulSemiringAction M R]
variable (S : Type*) [Semiring S] [MulSemiringAction N S]
variable (T : Type*) [Semiring T] [MulSemiringAction P T]

variable {R S N'}
variable [AddMonoid N'] [DistribMulAction S N']

variable {σ : R ->* S}
@[ext]
/--
theorem `DistribMulActionHom.ext_ring` / 定理 `DistribMulActionHom.ext_ring`

English:
theorem DistribMulActionHom.ext_ring
  given: {f g : R ->ₑ+[σ] N'} (h : f 1 = g 1)
  statement: f = g
  proof: by
  ext x
  rw [← mul_one x]; rw [← smul_eq_mul]; rw [f.map_smulₑ]; rw [g.map_smulₑ]; rw [h]

中文:
定理 DistribMulActionHom.ext_ring
  条件: {f g : R ->ₑ+[σ] N'} (h : f 1 = g 1)
  结论: f = g
  证明: by
  ext x
  rw [← mul_one x]; rw [← smul_eq_mul]; rw [f.map_smulₑ]; rw [g.map_smulₑ]; rw [h]

Depends on / 依赖: f.map_smul, g.map_smul, mul_one, smul_eq_mul
-/
theorem DistribMulActionHom.ext_ring {f g : R ->ₑ+[σ] N'} (h : f 1 = g 1) : f = g := by
  ext x
  rw [← mul_one x]; rw [← smul_eq_mul]; rw [f.map_smulₑ]; rw [g.map_smulₑ]; rw [h]

end Semiring


variable (R : Type*) [Semiring R] [MulSemiringAction M R]
variable (R' : Type*) [Ring R'] [MulSemiringAction M R']
variable (S : Type*) [Semiring S] [MulSemiringAction N S]
variable (S' : Type*) [Ring S'] [MulSemiringAction N S']
variable (T : Type*) [Semiring T] [MulSemiringAction P T]

/--
Definition of `MulSemiringActionHom` / `MulSemiringActionHom` 的定义

English:
structure MulSemiringActionHom
  parameters: extends R ->ₑ+[φ] S, R ->+* S
  extends: R ->ₑ+[φ] S, R ->+* S
  (no additional axioms)

中文:
结构 MulSemiringActionHom
  参数: extends R ->ₑ+[φ] S, R ->+* S
  继承: R ->ₑ+[φ] S, R ->+* S
  (无附加公理)
-/
structure MulSemiringActionHom extends R ->ₑ+[φ] S, R ->+* S

/-- Reinterpret an equivariant ring homomorphism as a ring homomorphism. -/
add_decl_doc MulSemiringActionHom.toRingHom

/-- Reinterpret an equivariant ring homomorphism as an equivariant additive monoid homomorphism. -/
add_decl_doc MulSemiringActionHom.toDistribMulActionHom

@[inherit_doc]
notation:25 (name := «MulSemiringActionHomLocal≺»)
  R " ->ₑ+*[" φ:25 "] " S:0 => MulSemiringActionHom φ R S

@[inherit_doc]
notation:25 (name := «MulSemiringActionHomIdLocal≺»)
  R " ->+*[" M:25 "] " S:0 => MulSemiringActionHom (MonoidHom.id M) R S

/--
Definition of `MulSemiringActionSemiHomClass` / `MulSemiringActionSemiHomClass` 的定义

English:
class MulSemiringActionSemiHomClass
  parameters: (F : Type*)
  extends: DistribMulActionSemiHomClass F φ R S, RingHomClass F R S
  (no additional axioms)

中文:
类 MulSemiringActionSemiHomClass
  参数: (F : 类型)
  继承: DistribMulActionSemiHomClass F φ R S, RingHomClass F R S
  (无附加公理)
-/
class MulSemiringActionSemiHomClass (F : Type*)
    {M N : outParam Type*} [Monoid M] [Monoid N]
    (φ : outParam (M -> N))
    (R S : outParam Type*) [Semiring R] [Semiring S]
    [DistribMulAction M R] [DistribMulAction N S] [FunLike F R S] : Prop
    extends DistribMulActionSemiHomClass F φ R S, RingHomClass F R S

/--
Definition of `MulSemiringActionHomClass` / `MulSemiringActionHomClass` 的定义

English:
abbreviation MulSemiringActionHomClass
  body: MulSemiringActionSemiHomClass F (MonoidHom.id M) R S

中文:
缩写 MulSemiringActionHomClass
  定义体: MulSemiringActionSemiHomClass F (MonoidHom.id M) R S

Depends on / 依赖: MonoidHom, MonoidHom.id, MulSemiringActionSemiHomClass
-/
abbrev MulSemiringActionHomClass
    (F : Type*)
    {M : outParam Type*} [Monoid M]
    (R S : outParam Type*) [Semiring R] [Semiring S]
    [DistribMulAction M R] [DistribMulAction M S] [FunLike F R S] :=
  MulSemiringActionSemiHomClass F (MonoidHom.id M) R S

namespace MulSemiringActionHom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (R ->ₑ+*[φ] S) R S
  body: m.toFun
  coe_injective f g h := by
    rcases f with ⟨⟨tF, _, _⟩, _, _⟩; rcases g with ⟨⟨tG, _, _⟩, _, _⟩
    cases tF; cases tG; congr

中文:
实例 :
  签名: FunLike (R ->ₑ+*[φ] S) R S
  定义体: m.toFun
  coe_injective f g h := by
    rcases f with ⟨⟨tF, _, _⟩, _, _⟩; rcases g with ⟨⟨tG, _, _⟩, _, _⟩
    cases tF; cases tG; congr

Depends on / 依赖: m.toFun
-/
instance : FunLike (R ->ₑ+*[φ] S) R S where
  coe m := m.toFun
  coe_injective f g h := by
    rcases f with ⟨⟨tF, _, _⟩, _, _⟩; rcases g with ⟨⟨tG, _, _⟩, _, _⟩
    cases tF; cases tG; congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulSemiringActionSemiHomClass (R ->ₑ+*[φ] S) φ R S
  body: m.map_zero'
  map_add m := m.map_add'
  map_one := MulSemiringActionHom.map_one'
  map_mul := MulSemiringActionHom.map_mul'
  map_smulₛₗ m := m.map_smul'

中文:
实例 :
  签名: MulSemiringActionSemiHomClass (R ->ₑ+*[φ] S) φ R S
  定义体: m.map_zero'
  map_add m := m.map_add'
  map_one := MulSemiringActionHom.map_one'
  map_mul := MulSemiringActionHom.map_mul'
  map_smulₛₗ m := m.map_smul'

Depends on / 依赖: m.map_zero, map_zero
-/
instance : MulSemiringActionSemiHomClass (R ->ₑ+*[φ] S) φ R S where
  map_zero m := m.map_zero'
  map_add m := m.map_add'
  map_one := MulSemiringActionHom.map_one'
  map_mul := MulSemiringActionHom.map_mul'
  map_smulₛₗ m := m.map_smul'

variable {φ R S}
variable {F : Type*} [FunLike F R S]

/-- Turn an element of a type `F` satisfying `MulSemiringActionHomClass F M R S` into an actual
`MulSemiringActionHom`. This is declared as the default coercion from `F` to
`MulSemiringActionHom M X Y`. -/
@[coe]
/--
Definition of `_root_.MulSemiringActionHomClass.toMulSemiringActionHom` / `_root_.MulSemiringActionHomClass.toMulSemiringActionHom` 的定义

English:
definition _root_.MulSemiringActionHomClass.toMulSemiringActionHom
  body: { (f : R ->+* S), (f : R ->ₑ+[φ] S) with }

中文:
定义 _root_.MulSemiringActionHomClass.toMulSemiringActionHom
  定义体: { (f : R ->+* S), (f : R ->ₑ+[φ] S) with }
-/
def _root_.MulSemiringActionHomClass.toMulSemiringActionHom
    [MulSemiringActionSemiHomClass F φ R S]
    (f : F) : R ->ₑ+*[φ] S :=
  { (f : R ->+* S), (f : R ->ₑ+[φ] S) with }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulSemiringActionSemiHomClass
  signature: F φ R S] :
  body: ⟨MulSemiringActionHomClass.toMulSemiringActionHom⟩

@[norm_cast]

中文:
实例 [MulSemiringActionSemiHomClass
  签名: F φ R S] :
  定义体: ⟨MulSemiringActionHomClass.toMulSemiringActionHom⟩

@[norm_cast]

Depends on / 依赖: MulSemiringActionHomClass, MulSemiringActionHomClass.toMulSemiringActionHom, toMulSemiringActionHom
-/
instance [MulSemiringActionSemiHomClass F φ R S] :
    CoeTC F (R ->ₑ+*[φ] S) :=
  ⟨MulSemiringActionHomClass.toMulSemiringActionHom⟩

@[norm_cast]
/--
theorem `coe_fn_coe` / 定理 `coe_fn_coe`

English:
theorem coe_fn_coe
  given: (f : R ->ₑ+*[φ] S)
  statement: ⇑(f : R ->+* S) = f
  proof: rfl

@[norm_cast]

中文:
定理 coe_fn_coe
  条件: (f : R ->ₑ+*[φ] S)
  结论: ⇑(f : R ->+* S) = f
  证明: rfl

@[norm_cast]
-/
theorem coe_fn_coe (f : R ->ₑ+*[φ] S) : ⇑(f : R ->+* S) = f :=
  rfl

@[norm_cast]
/--
theorem `coe_fn_coe'` / 定理 `coe_fn_coe'`

English:
theorem coe_fn_coe'
  given: (f : R ->ₑ+*[φ] S)
  statement: ⇑(f : R ->ₑ+[φ] S) = f
  proof: rfl

@[ext]

中文:
定理 coe_fn_coe'
  条件: (f : R ->ₑ+*[φ] S)
  结论: ⇑(f : R ->ₑ+[φ] S) = f
  证明: rfl

@[ext]
-/
theorem coe_fn_coe' (f : R ->ₑ+*[φ] S) : ⇑(f : R ->ₑ+[φ] S) = f :=
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : R ->ₑ+*[φ] S}
  statement: (forall x, f x = g x) -> f = g
  proof: DFunLike.ext f g

中文:
定理 ext
  条件: {f g : R ->ₑ+*[φ] S}
  结论: (对任意 x, f x = g x) -> f = g
  证明: DFunLike.ext f g

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : R ->ₑ+*[φ] S} : (forall x, f x = g x) -> f = g :=
  DFunLike.ext f g

/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  given: (f : R ->ₑ+*[φ] S)
  statement: f 0 = 0
  proof: map_zero f

中文:
定理 map_zero
  条件: (f : R ->ₑ+*[φ] S)
  结论: f 0 = 0
  证明: map_zero f
-/
protected theorem map_zero (f : R ->ₑ+*[φ] S) : f 0 = 0 :=
  map_zero f

/--
theorem `map_add` / 定理 `map_add`

English:
theorem map_add
  given: (f : R ->ₑ+*[φ] S) (x y : R)
  statement: f (x + y) = f x + f y
  proof: map_add f x y

中文:
定理 map_add
  条件: (f : R ->ₑ+*[φ] S) (x y : R)
  结论: f (x + y) = f x + f y
  证明: map_add f x y
-/
protected theorem map_add (f : R ->ₑ+*[φ] S) (x y : R) : f (x + y) = f x + f y :=
  map_add f x y

/--
theorem `map_neg` / 定理 `map_neg`

English:
theorem map_neg
  given: (f : R' ->ₑ+*[φ] S') (x : R')
  statement: f (-x) = -f x
  proof: map_neg f x

中文:
定理 map_neg
  条件: (f : R' ->ₑ+*[φ] S') (x : R')
  结论: f (-x) = -f x
  证明: map_neg f x
-/
protected theorem map_neg (f : R' ->ₑ+*[φ] S') (x : R') : f (-x) = -f x :=
  map_neg f x

/--
theorem `map_sub` / 定理 `map_sub`

English:
theorem map_sub
  given: (f : R' ->ₑ+*[φ] S') (x y : R')
  statement: f (x - y) = f x - f y
  proof: map_sub f x y

中文:
定理 map_sub
  条件: (f : R' ->ₑ+*[φ] S') (x y : R')
  结论: f (x - y) = f x - f y
  证明: map_sub f x y
-/
protected theorem map_sub (f : R' ->ₑ+*[φ] S') (x y : R') : f (x - y) = f x - f y :=
  map_sub f x y

/--
theorem `map_one` / 定理 `map_one`

English:
theorem map_one
  given: (f : R ->ₑ+*[φ] S)
  statement: f 1 = 1
  proof: map_one f

中文:
定理 map_one
  条件: (f : R ->ₑ+*[φ] S)
  结论: f 1 = 1
  证明: map_one f
-/
protected theorem map_one (f : R ->ₑ+*[φ] S) : f 1 = 1 :=
  map_one f

/--
theorem `map_mul` / 定理 `map_mul`

English:
theorem map_mul
  given: (f : R ->ₑ+*[φ] S) (x y : R)
  statement: f (x * y) = f x * f y
  proof: map_mul f x y

中文:
定理 map_mul
  条件: (f : R ->ₑ+*[φ] S) (x y : R)
  结论: f (x * y) = f x * f y
  证明: map_mul f x y
-/
protected theorem map_mul (f : R ->ₑ+*[φ] S) (x y : R) : f (x * y) = f x * f y :=
  map_mul f x y

/--
theorem `map_smulₛₗ` / 定理 `map_smulₛₗ`

English:
theorem map_smulₛₗ
  given: (f : R ->ₑ+*[φ] S) (m : M) (x : R)
  statement: f (m • x) = φ m • f x
  proof: map_smulₛₗ f m x

中文:
定理 map_smulₛₗ
  条件: (f : R ->ₑ+*[φ] S) (m : M) (x : R)
  结论: f (m • x) = φ m • f x
  证明: map_smulₛₗ f m x
-/
protected theorem map_smulₛₗ (f : R ->ₑ+*[φ] S) (m : M) (x : R) : f (m • x) = φ m • f x :=
  map_smulₛₗ f m x

/--
theorem `map_smul` / 定理 `map_smul`

English:
theorem map_smul
  given: [MulSemiringAction M S] (f : R ->+*[M] S) (m : M) (x : R)
  proof: map_smulₛₗ f m x

中文:
定理 map_smul
  条件: [MulSemiringAction M S] (f : R ->+*[M] S) (m : M) (x : R)
  证明: map_smulₛₗ f m x
-/
protected theorem map_smul [MulSemiringAction M S] (f : R ->+*[M] S) (m : M) (x : R) :
    f (m • x) = m • f x :=
  map_smulₛₗ f m x

end MulSemiringActionHom

namespace MulSemiringActionHom

variable (M) {R}

/-- The identity map as an equivariant ring homomorphism. -/
@[instance_reducible]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : R ->+*[M] R
  body: ⟨DistribMulActionHom.id _, rfl, (fun _ _ => rfl)⟩

@[simp]

中文:
定义 id
  签名: : R ->+*[M] R
  定义体: ⟨DistribMulActionHom.id _, rfl, (fun _ _ => rfl)⟩

@[simp]
-/
protected def id : R ->+*[M] R :=
  ⟨DistribMulActionHom.id _, rfl, (fun _ _ => rfl)⟩

@[simp]
/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (x : R)
  statement: MulSemiringActionHom.id M x = x
  proof: rfl

中文:
定理 id_apply
  条件: (x : R)
  结论: MulSemiringActionHom.id M x = x
  证明: rfl
-/
theorem id_apply (x : R) : MulSemiringActionHom.id M x = x :=
  rfl


end MulSemiringActionHom

namespace MulSemiringActionHom
open MulSemiringActionHom

variable {R S T}

variable {φ φ' ψ χ}

/-- Composition of two equivariant additive ring homomorphisms. -/
@[instance_reducible]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (g : S ->ₑ+*[ψ] T) (f : R ->ₑ+*[φ] S) [κ : MonoidHom.CompTriple φ ψ χ]
  body: { DistribMulActionHom.comp (g : S ->ₑ+[ψ] T) (f : R ->ₑ+[φ] S),
    RingHom.comp (g : S ->+* T) (f : R ->+* S) with }

@[simp]

中文:
定义 comp
  签名: (g : S ->ₑ+*[ψ] T) (f : R ->ₑ+*[φ] S) [κ : MonoidHom.CompTriple φ ψ χ]
  定义体: { DistribMulActionHom.comp (g : S ->ₑ+[ψ] T) (f : R ->ₑ+[φ] S),
    RingHom.comp (g : S ->+* T) (f : R ->+* S) with }

@[simp]

Depends on / 依赖: DistribMulActionHom, DistribMulActionHom.comp, RingHom, RingHom.comp
-/
def comp (g : S ->ₑ+*[ψ] T) (f : R ->ₑ+*[φ] S) [κ : MonoidHom.CompTriple φ ψ χ] : R ->ₑ+*[χ] T :=
  { DistribMulActionHom.comp (g : S ->ₑ+[ψ] T) (f : R ->ₑ+[φ] S),
    RingHom.comp (g : S ->+* T) (f : R ->+* S) with }

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (g : S ->ₑ+*[ψ] T) (f : R ->ₑ+*[φ] S) [MonoidHom.CompTriple φ ψ χ] (x : R)
  proof: rfl

@[simp]

中文:
定理 comp_apply
  条件: (g : S ->ₑ+*[ψ] T) (f : R ->ₑ+*[φ] S) [MonoidHom.CompTriple φ ψ χ] (x : R)
  证明: rfl

@[simp]
-/
theorem comp_apply (g : S ->ₑ+*[ψ] T) (f : R ->ₑ+*[φ] S) [MonoidHom.CompTriple φ ψ χ] (x : R) :
    g.comp f x = g (f x) := rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : R ->ₑ+*[φ] S)
  statement: (MulSemiringActionHom.id N).comp f = f
  proof: ext fun x => by rw [comp_apply, id_apply]

@[simp]

中文:
定理 id_comp
  条件: (f : R ->ₑ+*[φ] S)
  结论: (MulSemiringActionHom.id N).comp f = f
  证明: ext fun x => by rw [comp_apply, id_apply]

@[simp]

Depends on / 依赖: comp_apply, id_apply
-/
theorem id_comp (f : R ->ₑ+*[φ] S) : (MulSemiringActionHom.id N).comp f = f :=
  ext fun x => by rw [comp_apply, id_apply]

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : R ->ₑ+*[φ] S)
  statement: f.comp (MulSemiringActionHom.id M) = f
  proof: ext fun x => by rw [comp_apply, id_apply]

中文:
定理 comp_id
  条件: (f : R ->ₑ+*[φ] S)
  结论: f.comp (MulSemiringActionHom.id M) = f
  证明: ext fun x => by rw [comp_apply, id_apply]

Depends on / 依赖: comp_apply, id_apply
-/
theorem comp_id (f : R ->ₑ+*[φ] S) : f.comp (MulSemiringActionHom.id M) = f :=
  ext fun x => by rw [comp_apply, id_apply]

/-- The inverse of a bijective `MulSemiringActionHom` is a `MulSemiringActionHom`. -/
@[simps]
/--
Definition of `inverse'` / `inverse'` 的定义

English:
definition inverse'
  signature: (f : R ->ₑ+*[φ] S) (g : S -> R) (k : Function.RightInverse φ' φ)
  body: { (f : R ->+ S).inverse g h₁ h₂,
    (f : R ->* S).inverse g h₁ h₂,
    (f : R ->ₑ[φ] S).inverse' g k h₁ h₂ with
    toFun := g }

中文:
定义 inverse'
  签名: (f : R ->ₑ+*[φ] S) (g : S -> R) (k : Function.RightInverse φ' φ)
  定义体: { (f : R ->+ S).inverse g h₁ h₂,
    (f : R ->* S).inverse g h₁ h₂,
    (f : R ->ₑ[φ] S).inverse' g k h₁ h₂ with
    toFun := g }

Depends on / 依赖: inverse
-/
def inverse' (f : R ->ₑ+*[φ] S) (g : S -> R) (k : Function.RightInverse φ' φ)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
    S ->ₑ+*[φ'] R :=
  { (f : R ->+ S).inverse g h₁ h₂,
    (f : R ->* S).inverse g h₁ h₂,
    (f : R ->ₑ[φ] S).inverse' g k h₁ h₂ with
    toFun := g }

/-- The inverse of a bijective `MulSemiringActionHom` is a `MulSemiringActionHom`. -/
@[simps]
/--
Definition of `inverse` / `inverse` 的定义

English:
definition inverse
  signature: {S₁ : Type*} [Semiring S₁] [MulSemiringAction M S₁]
  body: { (f : R ->+ S₁).inverse g h₁ h₂,
    (f : R ->* S₁).inverse g h₁ h₂,
    f.toMulActionHom.inverse g h₁ h₂ with
    toFun := g }

中文:
定义 inverse
  签名: {S₁ : 类型} [Semiring S₁] [MulSemiringAction M S₁]
  定义体: { (f : R ->+ S₁).inverse g h₁ h₂,
    (f : R ->* S₁).inverse g h₁ h₂,
    f.toMulActionHom.inverse g h₁ h₂ with
    toFun := g }

Depends on / 依赖: f.toMulActionHom.inverse, inverse, toMulActionHom
-/
def inverse {S₁ : Type*} [Semiring S₁] [MulSemiringAction M S₁]
    (f : R ->+*[M] S₁) (g : S₁ -> R)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
    S₁ ->+*[M] R :=
  { (f : R ->+ S₁).inverse g h₁ h₂,
    (f : R ->* S₁).inverse g h₁ h₂,
    f.toMulActionHom.inverse g h₁ h₂ with
    toFun := g }

end MulSemiringActionHom

end DistribMulAction

/--
lemma `IsSMulRegular.of_injective` / 引理 `IsSMulRegular.of_injective`

English:
lemma IsSMulRegular.of_injective
  statement: {R M : Type*} [SMul R M]
  proof: fun x y h3 => h1 h2
  (map_smulₛₗ f r x).symm.trans ((congrArg f h3).trans (map_smulₛₗ f r y))

中文:
引理 IsSMulRegular.of_injective
  结论: {R M : 类型} [SMul R M]
  证明: fun x y h3 => h1 h2
  (map_smulₛₗ f r x).symm.trans ((congrArg f h3).trans (map_smulₛₗ f r y))
-/
lemma IsSMulRegular.of_injective {R M : Type*} [SMul R M]
    {N F} [SMul R N] [FunLike F M N] [MulActionHomClass F R M N]
    (f : F) {r : R} (h1 : Function.Injective f) (h2 : IsSMulRegular N r) :
IsSMulRegular M r := fun x y h3 => h1 h2
  (map_smulₛₗ f r x).symm.trans ((congrArg f h3).trans (map_smulₛₗ f r y))
