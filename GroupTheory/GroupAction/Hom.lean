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
variable (φ : M → N) (ψ : N → P) (χ : M → P)
variable (X : Type*) [SMul M X] [SMul M' X]
variable (Y : Type*) [SMul N Y] [SMul M' Y]
variable (Z : Type*) [SMul P Z]

/-- Equivariant functions :
When `φ : M → N` is a function, and types `X` and `Y` are endowed with additive actions
of `M` and `N`, a function `f : X → Y` is `φ`-equivariant if `f (m +ᵥ x) = (φ m) +ᵥ (f x)`. -/
/-
**AddActionHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{M : Type u_8} →   {N : Type u_9} → (M → N) → (X : Type u_10) → [VAdd M X]
 → (Y : Type u_11) → [VAdd N Y] → Type (max u_10 u_11)
参数：M → N；X : Type u_10；Y : Type u_11；max u_10 u_11。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivariant functions :
When `φ : M → N` is a function, and types `X` and `Y` are endowed with additive 
actions
of `M` and `N`, a function `f : X → Y` is `φ`-equivariant if `f (m +ᵥ x) = (φ m)
 +ᵥ (f x)`.
-/
structure AddActionHom {M N : Type*} (φ : M → N) (X : Type*) [VAdd M X] (Y : Type*) [VAdd N Y] where
  /-- The underlying function. -/
  protected toFun : X → Y
  /-- The proposition that the function commutes with the additive actions. -/
  protected map_vadd' : ∀ (m : M) (x : X), toFun (m +ᵥ x) = (φ m) +ᵥ toFun x

/-- Equivariant functions :
When `φ : M → N` is a function, and types `X` and `Y` are endowed with actions of `M` and `N`,
a function `f : X → Y` is `φ`-equivariant if `f (m • x) = (φ m) • (f x)`. -/
@[to_additive]
/-
**MulActionHom** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：MulActionHom where /-- The underlying function. -/ protected toFun : X -> 
Y /-- The proposition that the function commutes with the actions. -/ protected 
map_smul' : forall (m : M) (x : X), toFun (m • x) = (φ m) • toFun x  /-- `φ`-equ
ivariant functions `X → Y`, where `φ : M → N`, where `M` and `N` act on `X` and 
`Y` respectively. -/ notation:25 (name
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivariant functions :
When `φ : M → N` is a function, and types `X` and `Y` are endowed with actions o
f `M` and `N`,
a function `f : X → Y` is `φ`-equivariant if `f (m • x) = (φ m) • (f x)`.
-/
structure MulActionHom where
  /-- The underlying function. -/
  protected toFun : X → Y
  /-- The proposition that the function commutes with the actions. -/
  protected map_smul' : ∀ (m : M) (x : X), toFun (m • x) = (φ m) • toFun x

/-- `φ`-equivariant functions `X → Y`,
where `φ : M → N`, where `M` and `N` act on `X` and `Y` respectively. -/
notation:25 (name := «MulActionHomLocal≺») X " →ₑ[" φ:25 "] " Y:0 => MulActionHom φ X Y

/-- `M`-equivariant functions `X → Y` with respect to the action of `M`.
This is the same as `X →ₑ[@id M] Y`. -/
notation:25 (name := «MulActionHomIdLocal≺») X " →[" M:25 "] " Y:0 => MulActionHom (@id M) X Y

/-- `φ`-equivariant functions `X → Y`,
where `φ : M → N`, where `M` and `N` act additively on `X` and `Y` respectively

We use the same notation as for multiplicative actions, as conflicts are unlikely. -/
notation:25 (name := «AddActionHomLocal≺») X " →ₑ[" φ:25 "] " Y:0 => AddActionHom φ X Y

/-- `M`-equivariant functions `X → Y` with respect to the additive action of `M`.
This is the same as `X →ₑ[@id M] Y`.

We use the same notation as for multiplicative actions, as conflicts are unlikely. -/
notation:25 (name := «AddActionHomIdLocal≺») X " →[" M:25 "] " Y:0 => AddActionHom (@id M) X Y

/-- `AddActionSemiHomClass F φ X Y` states that
  `F` is a type of morphisms which are `φ`-equivariant.

You should extend this class when you extend `AddActionHom`. -/
/-
**AddActionSemiHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_8) →   {M : outParam (Type u_9)} →     {N : outParam (Type u_1
0)} →       outParam (M → N) →         (X : outParam (Type u_11)) → (Y : outPara
m (Type u_12)) → [VAdd M X] → [VAdd N Y] → [FunLike F X Y] → Prop
参数：Type u_11；Type u_12。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AddActionSemiHomClass F φ X Y` states that
  `F` is a type of morphisms which are `φ`-equivariant.

You should extend this class when you extend `AddActionHom`.
-/
class AddActionSemiHomClass (F : Type*)
    {M N : outParam Type*} (φ : outParam (M → N))
    (X Y : outParam Type*) [VAdd M X] [VAdd N Y] [FunLike F X Y] : Prop where
  /-- The proposition that the function preserves the action. -/
  map_vaddₛₗ : ∀ (f : F) (c : M) (x : X), f (c +ᵥ x) = (φ c) +ᵥ (f x)

/-- `MulActionSemiHomClass F φ X Y` states that
  `F` is a type of morphisms which are `φ`-equivariant.

You should extend this class when you extend `MulActionHom`. -/
@[to_additive]
/-
**MulActionSemiHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_8) →   {M : outParam (Type u_9)} →     {N : outParam (Type u_1
0)} →       outParam (M → N) →         (X : outParam (Type u_11)) → (Y : outPara
m (Type u_12)) → [SMul M X] → [SMul N Y] → [FunLike F X Y] → Prop
参数：Type u_11；Type u_12。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MulActionSemiHomClass F φ X Y` states that
  `F` is a type of morphisms which are `φ`-equivariant.

You should extend this class when you extend `MulActionHom`.
-/
class MulActionSemiHomClass (F : Type*)
    {M N : outParam Type*} (φ : outParam (M → N))
    (X Y : outParam Type*) [SMul M X] [SMul N Y] [FunLike F X Y] : Prop where
  /-- The proposition that the function preserves the action. -/
  map_smulₛₗ : ∀ (f : F) (c : M) (x : X), f (c • x) = (φ c) • (f x)

export MulActionSemiHomClass (map_smulₛₗ)
export AddActionSemiHomClass (map_vaddₛₗ)

/-- `MulActionHomClass F M X Y` states that `F` is a type of
morphisms which are equivariant with respect to actions of `M`
This is an abbreviation of `MulActionSemiHomClass`. -/
@[to_additive /-- `MulActionHomClass F M X Y` states that `F` is a type of
morphisms which are equivariant with respect to actions of `M`
This is an abbreviation of `MulActionSemiHomClass`. -/]
/-
**MulActionHomClass** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：MulActionHomClass (F : Type*) (M : outParam Type*) (X Y : outParam Type*) 
[SMul M X] [SMul M Y] [FunLike F X Y]
参数：F : Type*；M : outParam Type*；X Y : outParam Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev MulActionHomClass (F : Type*) (M : outParam Type*)
    (X Y : outParam Type*) [SMul M X] [SMul M Y] [FunLike F X Y] :=
  MulActionSemiHomClass F (@id M) X Y
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance : FunLike (MulActionHom φ X Y) X Y where
  coe := MulActionHom.toFun
  coe_injective f g h := by cases f; cases g; congr

@[to_additive (attr := simp)]
/-
**map_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X Y] [MulActio
nHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
参数：f : F；c : M；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
-/
theorem map_smul {F M X Y : Type*} [SMul M X] [SMul M Y]
    [FunLike F X Y] [MulActionHomClass F M X Y]
    (f : F) (c : M) (x : X) : f (c • x) = c • f x :=
  map_smulₛₗ f c x

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulActionSemiHomClass (X →ₑ[φ] Y) φ X Y where
  map_smulₛₗ := MulActionHom.map_smul'

initialize_simps_projections MulActionHom (toFun → apply)
initialize_simps_projections AddActionHom (toFun → apply)

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
/-
**MulActionHom._root_.MulActionSemiHomClass.toMulActionHom** 是 Mathlib 中的一个定义，位于
命名空间 `MulActionHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def _root_.MulActionSemiHomClass.toMulActionHom [MulActionSemiHomClass F φ X Y] (f : F) :
    X →ₑ[φ] Y where
  toFun := DFunLike.coe f
  map_smul' := map_smulₛₗ f

/-- Any type satisfying `MulActionSemiHomClass` can be cast into `MulActionHom` via
  `MulActionHomSemiClass.toMulActionHom`. -/
@[to_additive]
/-
**MulActionHom.** 是 Mathlib 中的一个实例，位于命名空间 `MulActionHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any type satisfying `MulActionSemiHomClass` can be cast into `MulActionHom` via
  `MulActionHomSemiClass.toMulActionHom`.
-/
instance [MulActionSemiHomClass F φ X Y] : CoeTC F (X →ₑ[φ] Y) :=
  ⟨MulActionSemiHomClass.toMulActionHom⟩

variable (M' X Y F) in
/-- If Y/X/M forms a scalar tower, any map X → Y preserving X-action also preserves M-action. -/
@[to_additive]
/-
**MulActionHom._root_.IsScalarTower.smulHomClass** 是 Mathlib 中的一个定理，位于命名空间 `MulA
ctionHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If Y/X/M forms a scalar tower, any map X → Y preserving X-action also preserves 
M-action.
-/
theorem _root_.IsScalarTower.smulHomClass [MulOneClass X] [SMul X Y] [IsScalarTower M' X Y]
    [MulActionHomClass F X X Y] : MulActionHomClass F M' X Y where
  map_smulₛₗ f m x := by
    rw [← mul_one (m • x), ← smul_eq_mul, map_smul, smul_assoc, ← map_smul,
      smul_eq_mul, mul_one, id_eq]

@[to_additive]
/-
**MulActionHom.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `MulActionHom`。
形式化陈述：∀ {M' : Type u_1} {X : Type u_5} [inst : SMul M' X] {Y : Type u_6} [inst_1
 : SMul M' Y] (f : X →ₑ[id] Y) (m : M')   (x : X), f (m • x) = m • f x
参数：f : X →ₑ[id] Y；m : M'；x : X；m • x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `instMulActionSemiHomClassMulActionHom`：∀ {M : Type u_2} {N : Type u_3} (
φ : M → N) (X : Type u_5) [inst : SMul M X] (Y : Type u_6) [inst_1 : SMul N Y], 
  MulActionSemiHomClass (X …
-/
protected theorem map_smul (f : X →[M'] Y) (m : M') (x : X) : f (m • x) = m • f x :=
  map_smul f m x

@[to_additive (attr := ext)]
/-
**MulActionHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `MulActionHom`。
形式化陈述：ext {f g : X ->ₑ[φ] Y} : (forall x, f x = g x) -> f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : X →ₑ[φ] Y} :
    (∀ x, f x = g x) → f = g :=
  DFunLike.ext f g

@[to_additive]
/-
**MulActionHom.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `MulActionHom`。
形式化陈述：∀ {M : Type u_2} {N : Type u_3} {φ : M → N} {X : Type u_5} [inst : SMul M 
X] {Y : Type u_6} [inst_1 : SMul N Y]   {f g : X →ₑ[φ] Y}, f = g → ∀ (x : X), f 
x = g x
参数：x : X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
protected theorem congr_fun {f g : X →ₑ[φ] Y} (h : f = g) (x : X) :
    f x = g x :=
  DFunLike.congr_fun h _

/-- Two equal maps on scalars give rise to an equivariant map for identity -/
@[to_additive /-- Two equal maps on scalars give rise to an equivariant map for identity -/]
/-
**MulActionHom.ofEq** 是 Mathlib 中的一个定义，位于命名空间 `MulActionHom`。
形式化陈述：ofEq {φ' : M -> N} (h : φ = φ') (f : X ->ₑ[φ] Y) : X ->ₑ[φ'] Y where toFun
参数：h : φ = φ'；f : X ->ₑ[φ] Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two equal maps on scalars give rise to an equivariant map for identity
-/
def ofEq {φ' : M → N} (h : φ = φ') (f : X →ₑ[φ] Y) : X →ₑ[φ'] Y where
  toFun := f.toFun
  map_smul' m a := h ▸ f.map_smul' m a

@[to_additive (attr := simp)]
/-
**MulActionHom.ofEq_coe** 是 Mathlib 中的一个定理，位于命名空间 `MulActionHom`。
形式化陈述：ofEq_coe {φ' : M -> N} (h : φ = φ') (f : X ->ₑ[φ] Y) : (f.ofEq h).toFun = 
f.toFun
参数：h : φ = φ'；f : X ->ₑ[φ] Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofEq_coe {φ' : M → N} (h : φ = φ') (f : X →ₑ[φ] Y) :
    (f.ofEq h).toFun = f.toFun := rfl

@[to_additive (attr := simp)]
/-
**MulActionHom.ofEq_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulActionHom`。
形式化陈述：ofEq_apply {φ' : M -> N} (h : φ = φ') (f : X ->ₑ[φ] Y) (a : X) : (f.ofEq h
) a = f a
参数：h : φ = φ'；f : X ->ₑ[φ] Y；a : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofEq_apply {φ' : M → N} (h : φ = φ') (f : X →ₑ[φ] Y) (a : X) :
    (f.ofEq h) a = f a :=
  rfl
/-
**MulActionHom._root_.FaithfulSMul.of_injective** 是 Mathlib 中的一个引理，位于命名空间 `MulAc
tionHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.FaithfulSMul.of_injective
    [FaithfulSMul M' X] [MulActionHomClass F M' X Y] (f : F)
    (hf : Function.Injective f) :
    FaithfulSMul M' Y where
  eq_of_smul_eq_smul {_ _} h := eq_of_smul_eq_smul fun m ↦ hf <| by simp_rw [map_smul, h]

variable {ψ χ} (M N)

/-- The identity map as an equivariant map. -/
@[to_additive (attr := instance_reducible) /-- The identity map as an equivariant map. -/]
/-
**MulActionHom.id** 是 Mathlib 中的一个定义，位于命名空间 `MulActionHom`。
形式化陈述：(M : Type u_2) → {X : Type u_5} → [inst : SMul M X] → X →ₑ[id] X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity map as an equivariant map.
-/
protected def id : X →[M] X :=
  ⟨fun x ↦ x, fun _ _ => rfl⟩

variable {M N Z}

@[to_additive (attr := simp)]
/-
**MulActionHom.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulActionHom`。
形式化陈述：id_apply (x : X) : MulActionHom.id M x = x
参数：x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**MulActionHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `MulActionHom`。
形式化陈述：comp (g : Y ->ₑ[ψ] Z) (f : X ->ₑ[φ] Y) [κ : CompTriple φ ψ χ] : X ->ₑ[χ] Z
参数：g : Y ->ₑ[ψ] Z；f : X ->ₑ[φ] Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of two equivariant maps.
-/
def comp (g : Y →ₑ[ψ] Z) (f : X →ₑ[φ] Y) [κ : CompTriple φ ψ χ] :
    X →ₑ[χ] Z :=
  ⟨fun x ↦ g (f x), fun m x =>
    calc
      g (f (m • x)) = g (φ m • f x) := by rw [map_smulₛₗ]
      _ = ψ (φ m) • g (f x) := by rw [map_smulₛₗ]
      _ = (ψ ∘ φ) m • g (f x) := rfl
      _ = χ m • g (f x) := by rw [κ.comp_eq] ⟩

@[to_additive (attr := simp)]
/-
**MulActionHom.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulActionHom`。
形式化陈述：comp_apply (g : Y ->ₑ[ψ] Z) (f : X ->ₑ[φ] Y) [CompTriple φ ψ χ] (x : X) : 
g.comp f x = g (f x)
参数：g : Y ->ₑ[ψ] Z；f : X ->ₑ[φ] Y；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply
    (g : Y →ₑ[ψ] Z) (f : X →ₑ[φ] Y) [CompTriple φ ψ χ] (x : X) :
    g.comp f x = g (f x) := rfl

@[to_additive (attr := simp)]
/-
**MulActionHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `MulActionHom`。
形式化陈述：id_comp (f : X ->ₑ[φ] Y) : (MulActionHom.id N).comp f = f
参数：f : X ->ₑ[φ] Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulActionHom.ext`：ext {f g : X ->ₑ[φ] Y} : (forall x, f x = g x) -> f = 
g
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulActionHom.comp_apply`：comp_apply (g : Y ->ₑ[ψ] Z) (f : X ->ₑ[φ] Y) [C
ompTriple φ ψ χ] (x : X) : g.comp f x = g (f x)
· 使用定理 `MulActionHom.id_apply`：id_apply (x : X) : MulActionHom.id M x = x
-/
theorem id_comp (f : X →ₑ[φ] Y) :
    (MulActionHom.id N).comp f = f :=
  ext fun x => by rw [comp_apply, id_apply]

@[to_additive (attr := simp)]
/-
**MulActionHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `MulActionHom`。
形式化陈述：comp_id (f : X ->ₑ[φ] Y) : f.comp (MulActionHom.id M) = f
参数：f : X ->ₑ[φ] Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulActionHom.ext`：ext {f g : X ->ₑ[φ] Y} : (forall x, f x = g x) -> f = 
g
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulActionHom.comp_apply`：comp_apply (g : Y ->ₑ[ψ] Z) (f : X ->ₑ[φ] Y) [C
ompTriple φ ψ χ] (x : X) : g.comp f x = g (f x)
· 使用定理 `MulActionHom.id_apply`：id_apply (x : X) : MulActionHom.id M x = x
-/
theorem comp_id (f : X →ₑ[φ] Y) :
    f.comp (MulActionHom.id M) = f :=
  ext fun x => by rw [comp_apply, id_apply]

@[to_additive (attr := simp)]
/-
**MulActionHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `MulActionHom`。
形式化陈述：comp_assoc {Q T : Type*} [SMul Q T] {η : P -> Q} {θ : M -> Q} {ζ : N -> Q}
 (h : Z ->ₑ[η] T) (g : Y ->ₑ[ψ] Z) (f : X ->ₑ[φ] Y) [CompTriple φ ψ χ] [CompTrip
le χ η θ] [CompTriple ψ η ζ] [CompTriple φ ζ θ] : h.comp (g.comp f) = (h.comp g)
.comp f
参数：h : Z ->ₑ[η] T；g : Y ->ₑ[ψ] Z；f : X ->ₑ[φ] Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulActionHom.ext`：ext {f g : X ->ₑ[φ] Y} : (forall x, f x = g x) -> f = 
g
-/
theorem comp_assoc {Q T : Type*} [SMul Q T]
    {η : P → Q} {θ : M → Q} {ζ : N → Q}
    (h : Z →ₑ[η] T) (g : Y →ₑ[ψ] Z) (f : X →ₑ[φ] Y)
    [CompTriple φ ψ χ] [CompTriple χ η θ]
    [CompTriple ψ η ζ] [CompTriple φ ζ θ] :
    h.comp (g.comp f) = (h.comp g).comp f :=
  ext fun _ => rfl

variable {φ' : N → M}
variable {Y₁ : Type*} [SMul M Y₁]

/-- The inverse of a bijective equivariant map is equivariant. -/
@[to_additive (attr := simps) /-- The inverse of a bijective equivariant map is equivariant. -/]
/-
**MulActionHom.inverse** 是 Mathlib 中的一个定义，位于命名空间 `MulActionHom`。
形式化陈述：inverse (f : X ->[M] Y₁) (g : Y₁ -> X) (h₁ : Function.LeftInverse g f) (h₂
 : Function.RightInverse g f) : Y₁ ->[M] X where toFun
参数：f : X ->[M] Y₁；g : Y₁ -> X；h₁ : Function.LeftInverse g f；h₂ : Function.RightI
nverse g f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of a bijective equivariant map is equivariant.
-/
def inverse (f : X →[M] Y₁) (g : Y₁ → X)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : Y₁ →[M] X where
  toFun := g
  map_smul' m x :=
    calc
      g (m • x) = g (m • f (g x)) := by rw [h₂]
      _ = g (f (m • g x)) := by simp only [map_smul]
      _ = m • g x := by rw [h₁]


/-- The inverse of a bijective equivariant map is equivariant. -/
@[to_additive (attr := simps) /-- The inverse of a bijective equivariant map is equivariant. -/]
/-
**MulActionHom.inverse'** 是 Mathlib 中的一个定义，位于命名空间 `MulActionHom`。
形式化陈述：inverse' (f : X ->ₑ[φ] Y) (g : Y -> X) (k : Function.RightInverse φ' φ) (h
₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : Y ->ₑ[φ'] X whe
re toFun
参数：f : X ->ₑ[φ] Y；g : Y -> X；k : Function.RightInverse φ' φ；h₁ : Function.LeftIn
verse g f；h₂ : Function.RightInverse g f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of a bijective equivariant map is equivariant.
-/
def inverse' (f : X →ₑ[φ] Y) (g : Y → X) (k : Function.RightInverse φ' φ)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
    Y →ₑ[φ'] X where
  toFun := g
  map_smul' m x :=
    calc
      g (m • x) = g (m • f (g x)) := by rw [h₂]
      _ = g ((φ (φ' m)) • f (g x)) := by rw [k]
      _ = g (f (φ' m • g x)) := by rw [map_smulₛₗ]
      _ = φ' m • g x := by rw [h₁]

@[to_additive]
/-
**MulActionHom.inverse_eq_inverse'** 是 Mathlib 中的一个引理，位于命名空间 `MulActionHom`。
形式化陈述：inverse_eq_inverse' (f : X ->[M] Y₁) (g : Y₁ -> X) (h₁ : Function.LeftInve
rse g f) (h₂ : Function.RightInverse g f) : inverse f g h₁ h₂ = inverse' f g (co
ngrFun rfl) h₁ h₂
参数：f : X ->[M] Y₁；g : Y₁ -> X；h₁ : Function.LeftInverse g f；h₂ : Function.RightI
nverse g f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inverse_eq_inverse' (f : X →[M] Y₁) (g : Y₁ → X)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
    inverse f g h₁ h₂ = inverse' f g (congrFun rfl) h₁ h₂ := by
  rfl

@[to_additive]
/-
**MulActionHom.inverse'_inverse'** 是 Mathlib 中的一个定理，位于命名空间 `MulActionHom`。
形式化陈述：∀ {M : Type u_2} {N : Type u_3} {φ : M → N} {X : Type u_5} [inst : SMul M 
X] {Y : Type u_6} [inst_1 : SMul N Y]   {φ' : N → M} {f : X →ₑ[φ] Y} {g : Y → X}
 {k₁ : Function.LeftInverse φ' φ} {k₂ : Function.RightInverse φ' φ}   {h₁ : Func
tion.LeftInverse g ⇑f} {h₂ : Function.RightInverse g ⇑f}, (f.inverse' g k₂ h₁ h₂
).inverse' (⇑f) k₁ h₂ h₁ = f
参数：f.inverse' g k₂ h₁ h₂；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulActionHom.ext`：ext {f g : X ->ₑ[φ] Y} : (forall x, f x = g x) -> f = 
g
-/
theorem inverse'_inverse'
    {f : X →ₑ[φ] Y} {g : Y → X}
    {k₁ : Function.LeftInverse φ' φ} {k₂ : Function.RightInverse φ' φ}
    {h₁ : Function.LeftInverse g f} {h₂ : Function.RightInverse g f} :
    inverse' (inverse' f g k₂ h₁ h₂) f k₁ h₂ h₁ = f :=
  ext fun _ => rfl

@[to_additive]
/-
**MulActionHom.comp_inverse'** 是 Mathlib 中的一个定理，位于命名空间 `MulActionHom`。
形式化陈述：comp_inverse' {f : X ->ₑ[φ] Y} {g : Y -> X} {k₁ : Function.LeftInverse φ' 
φ} {k₂ : Function.RightInverse φ' φ} {h₁ : Function.LeftInverse g f} {h₂ : Funct
ion.RightInverse g f} : (inverse' f g k₂ h₁ h₂).comp f (κ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulActionHom.ext`：ext {f g : X ->ₑ[φ] Y} : (forall x, f x = g x) -> f = 
g
· 使用引理 `CompTriple.comp_inv`：comp_inv {M N : Type*} {φ : M -> N} {ψ : N -> M} (h
 : Function.RightInverse φ ψ) {χ : M -> M} [IsId χ] : CompTriple φ ψ χ where com
p_eq
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulActionHom.inverse'_apply`：∀ {M : Type u_2} {N : Type u_3} {φ : M → N}
 {X : Type u_5} [inst : SMul M X] {Y : Type u_6} [inst_1 : SMul N Y]   {φ' : N →
 M} (f : X →ₑ[φ] …
· 使用定理 `Function.LeftInverse.eq`：∀ {α : Sort u_1} {β : Sort u_2} {g : β → α} {f 
: α → β}, Function.LeftInverse g f → ∀ (x : α), g (f x) = x
-/
theorem comp_inverse' {f : X →ₑ[φ] Y} {g : Y → X}
    {k₁ : Function.LeftInverse φ' φ} {k₂ : Function.RightInverse φ' φ}
    {h₁ : Function.LeftInverse g f} {h₂ : Function.RightInverse g f} :
    (inverse' f g k₂ h₁ h₂).comp f (κ := CompTriple.comp_inv k₁) = MulActionHom.id M := by
  ext
  simpa using h₁.eq _

@[to_additive]
/-
**MulActionHom.inverse'_comp** 是 Mathlib 中的一个定理，位于命名空间 `MulActionHom`。
形式化陈述：∀ {M : Type u_2} {N : Type u_3} {φ : M → N} {X : Type u_5} [inst : SMul M 
X] {Y : Type u_6} [inst_1 : SMul N Y]   {φ' : N → M} {f : X →ₑ[φ] Y} {g : Y → X}
 {k₂ : Function.RightInverse φ' φ} {h₁ : Function.LeftInverse g ⇑f}   {h₂ : Func
tion.RightInverse g ⇑f}, f.comp (f.inverse' g k₂ h₁ h₂) = MulActionHom.id N
参数：f.inverse' g k₂ h₁ h₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulActionHom.ext`：ext {f g : X ->ₑ[φ] Y} : (forall x, f x = g x) -> f = 
g
· 使用引理 `CompTriple.comp_inv`：comp_inv {M N : Type*} {φ : M -> N} {ψ : N -> M} (h
 : Function.RightInverse φ ψ) {χ : M -> M} [IsId χ] : CompTriple φ ψ χ where com
p_eq
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulActionHom.inverse'_apply`：∀ {M : Type u_2} {N : Type u_3} {φ : M → N}
 {X : Type u_5} [inst : SMul M X] {Y : Type u_6} [inst_1 : SMul N Y]   {φ' : N →
 M} (f : X →ₑ[φ] …
· 使用定理 `Function.RightInverse.eq`：∀ {α : Sort u_1} {β : Sort u_2} {g : β → α} {f
 : α → β}, Function.RightInverse g f → ∀ (x : β), f (g x) = x
-/
theorem inverse'_comp {f : X →ₑ[φ] Y} {g : Y → X}
    {k₂ : Function.RightInverse φ' φ}
    {h₁ : Function.LeftInverse g f} {h₂ : Function.RightInverse g f} :
    f.comp (inverse' f g k₂ h₁ h₂) (κ := CompTriple.comp_inv k₂) = MulActionHom.id N := by
  ext
  simpa using h₂.eq _

/-- If actions of `M` and `N` on `α` commute,
  then for `c : M`, `(c • · : α → α)` is an `N`-action homomorphism. -/
@[to_additive (attr := simps) /-- If additive actions of `M` and `N` on `α` commute,
  then for `c : M`, `(c • · : α → α)` is an `N`-additive action homomorphism. -/]
/-
**MulActionHom._root_.SMulCommClass.toMulActionHom** 是 Mathlib 中的一个定义，位于命名空间 `Mu
lActionHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def _root_.SMulCommClass.toMulActionHom {M} (N α : Type*)
    [SMul M α] [SMul N α] [SMulCommClass M N α] (c : M) :
    α →[N] α where
  toFun := (c • ·)
  map_smul' := smul_comm _

end MulActionHom

end MulActionHom

/-- Evaluation at a point as a `MulActionHom`. -/
@[to_additive (attr := simps) /-- Evaluation at a point as an `AddActionHom`. -/]
/-
**Pi.evalMulActionHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Pi.evalMulActionHom {ι M : Type*} {X : ι -> Type*} [forall i, SMul M (X i)
] (i : ι) : (forall i, X i) ->[M] X i where toFun
参数：X i；i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluation at a point as a `MulActionHom`.
-/
def Pi.evalMulActionHom {ι M : Type*} {X : ι → Type*} [∀ i, SMul M (X i)] (i : ι) :
    (∀ i, X i) →[M] X i where
  toFun := Function.eval i
  map_smul' _ _ := rfl

namespace MulActionHom

section FstSnd

variable {M α β : Type*} [SMul M α] [SMul M β]

variable (M α β) in
/-- `Prod.fst` as a bundled `MulActionHom`. -/
@[to_additive (attr := simps -fullyApplied) /-- `Prod.fst` as a bundled `AddActionHom`. -/]
/-
**MulActionHom.fst** 是 Mathlib 中的一个定义，位于命名空间 `MulActionHom`。
形式化陈述：fst : α × β ->[M] α where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Prod.fst` as a bundled `MulActionHom`.
-/
def fst : α × β →[M] α where
  toFun := Prod.fst
  map_smul' _ _ := rfl

variable (M α β) in
/-- `Prod.snd` as a bundled `MulActionHom`. -/
@[to_additive (attr := simps -fullyApplied) /-- `Prod.snd` as a bundled `AddActionHom`. -/]
/-
**MulActionHom.snd** 是 Mathlib 中的一个定义，位于命名空间 `MulActionHom`。
形式化陈述：snd : α × β ->[M] β where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Prod.snd` as a bundled `MulActionHom`.
-/
def snd : α × β →[M] β where
  toFun := Prod.snd
  map_smul' _ _ := rfl

end FstSnd

variable {M N α β γ δ : Type*} [SMul M α] [SMul M β] [SMul N γ] [SMul N δ] {σ : M → N}

/-- If `f` and `g` are equivariant maps, then so is `x ↦ (f x, g x)`. -/
@[to_additive (attr := simps -fullyApplied) prod
  /-- If `f` and `g` are equivariant maps, then so is `x ↦ (f x, g x)`. -/]
/-
**MulActionHom.prod** 是 Mathlib 中的一个定义，位于命名空间 `MulActionHom`。
形式化陈述：prod (f : α ->ₑ[σ] γ) (g : α ->ₑ[σ] δ) : α ->ₑ[σ] γ × δ where toFun x
参数：f : α ->ₑ[σ] γ；g : α ->ₑ[σ] δ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def prod (f : α →ₑ[σ] γ) (g : α →ₑ[σ] δ) : α →ₑ[σ] γ × δ where
  toFun x := (f x, g x)
  map_smul' _ _ := Prod.ext (map_smulₛₗ f _ _) (map_smulₛₗ g _ _)

@[to_additive (attr := simp) fst_comp_prod]
/-
**MulActionHom.fst_comp_prod** 是 Mathlib 中的一个引理，位于命名空间 `MulActionHom`。
形式化陈述：fst_comp_prod (f : α ->ₑ[σ] γ) (g : α ->ₑ[σ] δ) : (fst _ _ _).comp (prod f
 g) = f
参数：f : α ->ₑ[σ] γ；g : α ->ₑ[σ] δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
-/
lemma fst_comp_prod (f : α →ₑ[σ] γ) (g : α →ₑ[σ] δ) : (fst _ _ _).comp (prod f g) = f := rfl

@[to_additive (attr := simp) snd_comp_prod]
/-
**MulActionHom.snd_comp_prod** 是 Mathlib 中的一个引理，位于命名空间 `MulActionHom`。
形式化陈述：snd_comp_prod (f : α ->ₑ[σ] γ) (g : α ->ₑ[σ] δ) : (snd _ _ _).comp (prod f
 g) = g
参数：f : α ->ₑ[σ] γ；g : α ->ₑ[σ] δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
-/
lemma snd_comp_prod (f : α →ₑ[σ] γ) (g : α →ₑ[σ] δ) : (snd _ _ _).comp (prod f g) = g := rfl

@[to_additive (attr := simp) prod_fst_snd]
/-
**MulActionHom.prod_fst_snd** 是 Mathlib 中的一个引理，位于命名空间 `MulActionHom`。
形式化陈述：prod_fst_snd : prod (fst M α β) (snd M α β) = .id ..
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prod_fst_snd : prod (fst M α β) (snd M α β) = .id .. := rfl

/-- If `f` and `g` are equivariant maps, then so is `(x, y) ↦ (f x, g y)`. -/
@[to_additive (attr := simps -fullyApplied) prodMap
  /-- If `f` and `g` are equivariant maps, then so is `(x, y) ↦ (f x, g y)`. -/]
/-
**MulActionHom.prodMap** 是 Mathlib 中的一个定义，位于命名空间 `MulActionHom`。
形式化陈述：prodMap (f : α ->ₑ[σ] γ) (g : β ->ₑ[σ] δ) : α × β ->ₑ[σ] γ × δ where toFun
参数：f : α ->ₑ[σ] γ；g : β ->ₑ[σ] δ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def prodMap (f : α →ₑ[σ] γ) (g : β →ₑ[σ] δ) : α × β →ₑ[σ] γ × δ where
  toFun := Prod.map f g
  __ := (f.comp (fst ..)).prod (g.comp (snd ..))

end MulActionHom

namespace MulActionHom

variable {R M N X Y : Type*} {σ : M → N}

attribute [local simp] map_smulₛₗ smul_sub

@[to_additive]
/-
**MulActionHom.** 是 Mathlib 中的一个实例，位于命名空间 `MulActionHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul M X] [SMul N Y] [SMul R Y] [SMulCommClass N R Y] :
    SMul R (X →ₑ[σ] Y) where
  smul h f := ⟨h • f, by simp [smul_comm _ h]⟩

@[to_additive (attr := simp, norm_cast)]
/-
**MulActionHom.coe_smul** 是 Mathlib 中的一个引理，位于命名空间 `MulActionHom`。
形式化陈述：coe_smul [SMul M X] [SMul N Y] [SMul R Y] [SMulCommClass N R Y] (f : X ->ₑ
[σ] Y) (r : R) : ⇑(r • f) = r • ⇑f
参数：f : X ->ₑ[σ] Y；r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_smul [SMul M X] [SMul N Y] [SMul R Y] [SMulCommClass N R Y] (f : X →ₑ[σ] Y) (r : R) :
    ⇑(r • f) = r • ⇑f := rfl
/-
**MulActionHom.** 是 Mathlib 中的一个实例，位于命名空间 `MulActionHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul M X] [Zero Y] [SMulZeroClass N Y] :
    Zero (X →ₑ[σ] Y) where
  zero := ⟨0, by simp⟩

@[simp, norm_cast]
/-
**MulActionHom.coe_zero** 是 Mathlib 中的一个引理，位于命名空间 `MulActionHom`。
形式化陈述：coe_zero [SMul M X] [Zero Y] [SMulZeroClass N Y] : ⇑(0 : X ->ₑ[σ] Y) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_zero [SMul M X] [Zero Y] [SMulZeroClass N Y] : ⇑(0 : X →ₑ[σ] Y) = 0 := rfl
/-
**MulActionHom.** 是 Mathlib 中的一个实例，位于命名空间 `MulActionHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul M X] [AddZeroClass Y] [DistribSMul N Y] :
    AddZeroClass (X →ₑ[σ] Y) where
  add f g := ⟨f + g, by simp [smul_add]⟩
  zero_add _ := ext fun _ ↦ zero_add _
  add_zero _ := ext fun _ ↦ add_zero _

@[simp, norm_cast]
/-
**MulActionHom.coe_add** 是 Mathlib 中的一个引理，位于命名空间 `MulActionHom`。
形式化陈述：coe_add [SMul M X] [AddZeroClass Y] [DistribSMul N Y] (f g : X ->ₑ[σ] Y) :
 ⇑(f + g) = ⇑f + ⇑g
参数：f g : X ->ₑ[σ] Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_add [SMul M X] [AddZeroClass Y] [DistribSMul N Y] (f g : X →ₑ[σ] Y) :
    ⇑(f + g) = ⇑f + ⇑g := rfl
/-
**MulActionHom.** 是 Mathlib 中的一个实例，位于命名空间 `MulActionHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul M X] [AddMonoid Y] [DistribSMul N Y] :
    AddMonoid (X →ₑ[σ] Y) where
  add_assoc _ _ _ := ext fun _ ↦ add_assoc _ _ _
  nsmul_zero f := ext fun x ↦ AddMonoid.nsmul_zero (f x)
  nsmul_succ n f := ext fun x ↦ AddMonoid.nsmul_succ n (f x)
/-
**MulActionHom.** 是 Mathlib 中的一个实例，位于命名空间 `MulActionHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul M X] [AddCommMonoid Y] [DistribSMul N Y] :
    AddCommMonoid (X →ₑ[σ] Y) where
  add_comm _ _ := ext fun _ ↦ add_comm _ _

@[to_additive]
/-
**MulActionHom.** 是 Mathlib 中的一个实例，位于命名空间 `MulActionHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul M X] [SMul N Y] [Monoid R] [MulAction R Y] [SMulCommClass N R Y] :
    MulAction R (X →ₑ[σ] Y) where
  one_smul _ := ext fun _ ↦ one_smul _ _
  mul_smul _ _ _ := ext fun _ ↦ mul_smul _ _ _
/-
**MulActionHom.** 是 Mathlib 中的一个实例，位于命名空间 `MulActionHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddZeroClass Y] [SMul M X] [DistribSMul N Y] [DistribSMul R Y] [SMulCommClass N R Y] :
    DistribSMul R (X →ₑ[σ] Y) where
  smul_zero y := ext fun _ ↦ smul_zero y
  smul_add y _ _ := ext fun _ ↦ smul_add y _ _
/-
**MulActionHom.** 是 Mathlib 中的一个实例，位于命名空间 `MulActionHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddMonoid Y] [Monoid R] [SMul M X] [DistribSMul N Y]
    [DistribMulAction R Y] [SMulCommClass N R Y] :
    DistribMulAction R (X →ₑ[σ] Y) where
  __ := (inferInstance : MulAction _ _)
  __ := (inferInstance : DistribSMul _ _)
/-
**MulActionHom.** 是 Mathlib 中的一个实例，位于命名空间 `MulActionHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddCommMonoid Y] [Semiring R] [SMul M X] [DistribSMul N Y]
    [Module R Y] [SMulCommClass N R Y] :
    Module R (X →ₑ[σ] Y) where
  add_smul _ _ _ := ext fun _ ↦ add_smul _ _ _
  zero_smul _ := ext fun _ ↦ zero_smul R _
/-
**MulActionHom.** 是 Mathlib 中的一个实例，位于命名空间 `MulActionHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul M X] [AddGroup Y] [DistribSMul N Y] : AddGroup (X →ₑ[σ] Y) where
  sub f g := ⟨f - g, by simp [smul_sub]⟩
  neg f := ⟨-f, by simp⟩
  neg_add_cancel f := ext fun _ ↦ neg_add_cancel _
  sub_eq_add_neg _ _ := ext fun _ ↦ sub_eq_add_neg _ _
  zsmul_zero' f := ext fun x ↦ SubNegMonoid.zsmul_zero' _
  zsmul_neg' _ _ := ext fun x ↦ SubNegMonoid.zsmul_neg' _ _
  zsmul_succ' _ _ := ext fun x ↦ SubNegMonoid.zsmul_succ' _ _

@[simp, norm_cast]
/-
**MulActionHom.coe_neg** 是 Mathlib 中的一个引理，位于命名空间 `MulActionHom`。
形式化陈述：coe_neg [SMul M X] [AddGroup Y] [DistribSMul N Y] (f : X ->ₑ[σ] Y) : ⇑(-f)
 = -⇑f
参数：f : X ->ₑ[σ] Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_neg [SMul M X] [AddGroup Y] [DistribSMul N Y] (f : X →ₑ[σ] Y) :
    ⇑(-f) = -⇑f := rfl

@[simp, norm_cast]
/-
**MulActionHom.coe_sub** 是 Mathlib 中的一个引理，位于命名空间 `MulActionHom`。
形式化陈述：coe_sub [SMul M X] [AddGroup Y] [DistribSMul N Y] (f g : X ->ₑ[σ] Y) : ⇑(f
 - g) = ⇑f - ⇑g
参数：f g : X ->ₑ[σ] Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_sub [SMul M X] [AddGroup Y] [DistribSMul N Y] (f g : X →ₑ[σ] Y) :
    ⇑(f - g) = ⇑f - ⇑g := rfl
/-
**MulActionHom.** 是 Mathlib 中的一个实例，位于命名空间 `MulActionHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul M X] [AddCommGroup Y] [DistribSMul N Y] : AddCommGroup (X →ₑ[σ] Y) where
/-
**MulActionHom.** 是 Mathlib 中的一个实例，位于命名空间 `MulActionHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul M X] [Monoid N] [Monoid Y] [MulDistribMulAction N Y] :
    Monoid (X →ₑ[σ] Y) where
  mul f g := ⟨f * g, by simp⟩
  mul_assoc _ _ _ := ext fun x ↦ mul_assoc _ _ _
  one := ⟨1, by simp⟩
  one_mul _ := ext fun x ↦ one_mul _
  mul_one _ := ext fun x ↦ mul_one _

@[simp, norm_cast]
/-
**MulActionHom.coe_mul** 是 Mathlib 中的一个引理，位于命名空间 `MulActionHom`。
形式化陈述：coe_mul [SMul M X] [Monoid N] [Monoid Y] [MulDistribMulAction N Y] (f g : 
X ->ₑ[σ] Y) : ⇑(f * g) = ⇑f * ⇑g
参数：f g : X ->ₑ[σ] Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_mul [SMul M X] [Monoid N] [Monoid Y] [MulDistribMulAction N Y] (f g : X →ₑ[σ] Y) :
    ⇑(f * g) = ⇑f * ⇑g := rfl

@[simp, norm_cast]
/-
**MulActionHom.coe_one** 是 Mathlib 中的一个引理，位于命名空间 `MulActionHom`。
形式化陈述：coe_one [SMul M X] [Monoid N] [Monoid Y] [MulDistribMulAction N Y] : ⇑(1 :
 X ->ₑ[σ] Y) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_one [SMul M X] [Monoid N] [Monoid Y] [MulDistribMulAction N Y] :
    ⇑(1 : X →ₑ[σ] Y) = 1 := rfl
/-
**MulActionHom.** 是 Mathlib 中的一个实例，位于命名空间 `MulActionHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul M X] [Monoid N] [CommMonoid Y] [MulDistribMulAction N Y] :
    CommMonoid (X →ₑ[σ] Y) where
  mul_comm _ _ := ext fun _ ↦ mul_comm _ _
/-
**MulActionHom.** 是 Mathlib 中的一个实例，位于命名空间 `MulActionHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul M X] [Monoid N] [Semiring Y] [MulSemiringAction N Y] :
    Semiring (X →ₑ[σ] Y) where
  __ := (inferInstance : Monoid _)
  __ := (inferInstance : AddCommMonoid _)
  zero_mul _ := ext fun x ↦ zero_mul _
  mul_zero _ := ext fun x ↦ mul_zero _
  left_distrib _ _ _ := ext fun x ↦ left_distrib _ _ _
  right_distrib _ _ _ := ext fun x ↦ right_distrib _ _ _
/-
**MulActionHom.** 是 Mathlib 中的一个实例，位于命名空间 `MulActionHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul M X] [Monoid N] [CommSemiring Y] [MulSemiringAction N Y] :
    CommSemiring (X →ₑ[σ] Y) where
/-
**MulActionHom.** 是 Mathlib 中的一个实例，位于命名空间 `MulActionHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul M X] [Monoid N] [Ring Y] [MulSemiringAction N Y] :
    Ring (X →ₑ[σ] Y) where
/-
**MulActionHom.** 是 Mathlib 中的一个实例，位于命名空间 `MulActionHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul M X] [Monoid N] [CommRing Y] [MulSemiringAction N Y] :
    CommRing (X →ₑ[σ] Y) where

namespace End

/-- For a monoid `M` acting on a type `X`, the `M`-equivariant functions from `X` to itself
form a monoid under composition. -/
@[to_additive /-- For an additive monoid `M` acting on a type `X`, the `M`-equivariant functions
from `X` to itself form an additive monoid under composition. -/]
local instance [SMul M X] : Monoid (X →[M] X) where
  mul f g := f.comp g
  mul_assoc _ _ _ := rfl
  one := .id _
  one_mul _ := rfl
  mul_one _ := rfl

/-
**MulActionHom.End.mul_def** 是 Mathlib 中的一个定理，位于命名空间 `MulActionHom.End`。
形式化陈述：∀ {M : Type u_2} {X : Type u_4} [inst : SMul M X] {f g : X →ₑ[id] X}, f * 
g = f.comp g
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] theorem mul_def [SMul M X] {f g : X →[M] X} : f * g = f.comp g := rfl

/-- The `M`-equivariant functions from a monoid `M` to itself are exactly
right multiplications by elements of `M`. See also `RingEquiv.moduleEndSelf`. -/
@[to_additive (attr := simps)
/-- The `M`-equivariant functions from an additive monoid `M` to itself are exactly
right additions by elements of `M`. -/]
/-
**MulActionHom.End.equivMulOpposite** 是 Mathlib 中的一个定义，位于命名空间 `MulActionHom.End`
。
形式化陈述：equivMulOpposite [Monoid M] : (M ->[M] M) ≃* Mᵐᵒᵖ where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def equivMulOpposite [Monoid M] : (M →[M] M) ≃* Mᵐᵒᵖ where
  toFun f := .op (f 1)
  invFun m := .mk (· * m.unop) fun _ _ ↦ mul_assoc ..
  left_inv f := by ext m; change m • f 1 = _; rw [← map_smul, smul_eq_mul, mul_one]
  right_inv := mul_one
  map_mul' f g := congr_arg MulOpposite.op <| by
    dsimp [← smul_eq_mul]; simp_rw [← map_smul, smul_eq_mul, mul_one]; rfl

/-- The functions from a monoid `M` to itself equivariant with respect to the right `M`-action
are exactly left multiplications by elements of `M`. See also `RingEquiv.moduleEndSelfOp`. -/
@[to_additive (attr := simps)
/-- The functions from an additive monoid `M` to itself equivariant with respect to
the right `M`-action are exactly left additions by elements of `M`. -/]
/-
**MulActionHom.End.mulOppositeEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MulActionHom.End`
。
形式化陈述：mulOppositeEquiv [Monoid M] : (M ->[Mᵐᵒᵖ] M) ≃* M where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mulOppositeEquiv [Monoid M] : (M →[Mᵐᵒᵖ] M) ≃* M where
  toFun f := f 1
  invFun m := .mk (m * ·) fun _ _ ↦ (mul_assoc ..).symm
  left_inv f := by ext m; change MulOpposite.op m • f 1 = _; simp [← map_smul]
  right_inv := mul_one
  map_mul' f g := show _ = MulOpposite.op (g 1) • f 1 by simp [← map_smul]

end End

end MulActionHom

section DistribMulAction

variable {M : Type*} [Monoid M]
variable {N : Type*} [Monoid N]
variable {P : Type*} [Monoid P]
variable (φ : M →* N) (φ' : N →* M) (ψ : N →* P) (χ : M →* P)
variable (A : Type*) [Monoid A] [MulDistribMulAction M A]
variable (B : Type*) [Monoid B] [MulDistribMulAction N B]
variable (B₁ : Type*) [Monoid B₁] [MulDistribMulAction M B₁]
variable (C : Type*) [Monoid C] [MulDistribMulAction P C]

variable (A' : Type*) [Group A'] [MulDistribMulAction M A']
variable (B' : Type*) [Group B'] [MulDistribMulAction N B']

set_option linter.translateOverwrite false in
attribute [to_additive existing (dont_translate := M) DistribMulAction]
  MulDistribMulAction

/-- Equivariant additive monoid homomorphisms. -/
/-
**DistribMulActionHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{M : Type u_1} →   [inst : Monoid M] →     {N : Type u_2} →       [inst_1 
: Monoid N] →         (M →* N) →           (A : Type u_10) →             [inst_2
 : AddMonoid A] →               [DistribMulAction M A] →                 (B : Ty
pe u_11) → [inst : AddMonoid B] → [DistribMulAction N B] → Type (max u_10 u_11)
参数：M →* N；A : Type u_10；B : Type u_11；max u_10 u_11。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivariant additive monoid homomorphisms.
-/
structure DistribMulActionHom (A : Type*) [AddMonoid A] [DistribMulAction M A] (B : Type*)
    [AddMonoid B] [DistribMulAction N B] extends A →ₑ[φ] B, A →+ B

/-- Equivariant monoid homomorphisms. -/
@[to_additive (dont_translate := M N) DistribMulActionHom]
/-
**MulDistribMulActionHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{M : Type u_1} →   [inst : Monoid M] →     {N : Type u_2} →       [inst_1 
: Monoid N] →         (M →* N) →           (A : Type u_4) →             [inst_2 
: Monoid A] →               [MulDistribMulAction M A] →                 (B : Typ
e u_5) → [inst : Monoid B] → [MulDistribMulAction N B] → Type (max u_4 u_5)
参数：M →* N；A : Type u_4；B : Type u_5；max u_4 u_5。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivariant monoid homomorphisms.
-/
structure MulDistribMulActionHom extends A →ₑ[φ] B, A →* B

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
  A " →ₑ+[" φ:25 "] " B:0 => DistribMulActionHom φ A B

@[inherit_doc]
notation:25 (name := «DistribMulActionHomIdLocal≺»)
  A " →+[" M:25 "] " B:0 => DistribMulActionHom (MonoidHom.id M) A B

@[inherit_doc]
notation:25 (name := «MulDistribMulActionHomLocal≺»)
  A " →ₑ*[" φ:25 "] " B:0 => MulDistribMulActionHom φ A B

@[inherit_doc]
notation:25 (name := «MulDistribMulActionHomIdLocal≺»)
  A " →*[" M:25 "] " B:0 => MulDistribMulActionHom (MonoidHom.id M) A B

-- QUESTION/TODO : Impose that `φ` is a morphism of monoids?

/-- `DistribMulActionSemiHomClass F φ A B` states that `F` is a type of morphisms
preserving the additive monoid structure and equivariant with respect to `φ`.
You should extend this class when you extend `DistribMulActionSemiHom`. -/
/-
**DistribMulActionSemiHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_10) →   {M : outParam (Type u_11)} →     {N : outParam (Type u
_12)} →       outParam (M → N) →         (A : outParam (Type u_13)) →           
(B : outParam (Type u_14)) →             [inst : Monoid M] →               [inst
_1 : Monoid N] →                 [inst_2 : AddMonoid A] →                   [ins
t_3 : AddMonoid B] → [DistribMulAction M A] → [DistribMulAction N B] → [FunLike 
F A B] → Prop
参数：Type u_13；Type u_14。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`DistribMulActionSemiHomClass F φ A B` states that `F` is a type of morphisms
preserving the additive monoid structure and equivariant with respect to `φ`.
You should extend this class when you extend `DistribMulActionSemiHom`.
-/
class DistribMulActionSemiHomClass (F : Type*)
    {M N : outParam Type*} (φ : outParam (M → N))
    (A B : outParam Type*)
    [Monoid M] [Monoid N]
    [AddMonoid A] [AddMonoid B] [DistribMulAction M A] [DistribMulAction N B]
    [FunLike F A B] : Prop
    extends MulActionSemiHomClass F φ A B, AddMonoidHomClass F A B

/-- `MulDistribMulActionSemiHomClass F φ A B` states that `F` is a type of morphisms
preserving the monoid structure and equivariant with respect to `φ`.
You should extend this class when you extend `MulDistribMulActionSemiHom`. -/
@[to_additive existing (dont_translate := M N) DistribMulActionSemiHomClass]
/-
**MulDistribMulActionSemiHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_10) →   {M : outParam (Type u_11)} →     {N : outParam (Type u
_12)} →       outParam (M → N) →         (A : outParam (Type u_13)) →           
(B : outParam (Type u_14)) →             [inst : Monoid M] →               [inst
_1 : Monoid N] →                 [inst_2 : Monoid A] →                   [inst_3
 : Monoid B] → [MulDistribMulAction M A] → [MulDistribMulAction N B] → [FunLike 
F A B] → Prop
参数：Type u_13；Type u_14。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MulDistribMulActionSemiHomClass F φ A B` states that `F` is a type of morphisms
preserving the monoid structure and equivariant with respect to `φ`.
You should extend this class when you extend `MulDistribMulActionSemiHom`.
-/
class MulDistribMulActionSemiHomClass (F : Type*)
    {M N : outParam Type*} (φ : outParam (M → N))
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
/-
**MulDistribMulActionHomClass** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：MulDistribMulActionHomClass (F : Type*) (M : outParam Type*) (A B : outPar
am Type*) [Monoid M] [Monoid A] [Monoid B] [MulDistribMulAction M A] [MulDistrib
MulAction M B] [FunLike F A B]
参数：F : Type*；M : outParam Type*；A B : outParam Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev MulDistribMulActionHomClass (F : Type*) (M : outParam Type*)
    (A B : outParam Type*) [Monoid M] [Monoid A] [Monoid B]
    [MulDistribMulAction M A] [MulDistribMulAction M B] [FunLike F A B] :=
    MulDistribMulActionSemiHomClass F (MonoidHom.id M) A B

namespace MulDistribMulActionHom

@[to_additive (dont_translate := M N)]
/-
**MulDistribMulActionHom.** 是 Mathlib 中的一个实例，位于命名空间 `MulDistribMulActionHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (A →ₑ*[φ] B) A B where
  coe m := m.toFun
  coe_injective f g h := by
    rcases f with ⟨tF, _, _⟩; rcases g with ⟨tG, _, _⟩
    cases tF; cases tG; congr

@[to_additive (dont_translate := M N)]
/-
**MulDistribMulActionHom.** 是 Mathlib 中的一个实例，位于命名空间 `MulDistribMulActionHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulDistribMulActionSemiHomClass (A →ₑ*[φ] B) φ A B where
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
/-
**MulDistribMulActionHom._root_.MulDistribMulActionSemiHomClass.toMulDistribMulA
ctionHom** 是 Mathlib 中的一个定义，位于命名空间 `MulDistribMulActionHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def _root_.MulDistribMulActionSemiHomClass.toMulDistribMulActionHom
    [MulDistribMulActionSemiHomClass F φ A B]
    (f : F) : A →ₑ*[φ] B :=
  { (f : A →* B), (f : A →ₑ[φ] B) with }

/-- Any type satisfying `MulDistribMulActionSemiHomClass` can be cast into `MulDistribMulActionHom`
via `MulDistribMulActionSemiHomClass.toMulDistribMulActionHom`. -/
@[to_additive (dont_translate := M N)
/-- Any type satisfying `DistribMulActionSemiHomClass` can be cast into `DistribMulActionHom`
via `DistribMulActionSemiHomClass.toDistribMulActionHom`. -/]
/-
**MulDistribMulActionHom.** 是 Mathlib 中的一个实例，位于命名空间 `MulDistribMulActionHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MulDistribMulActionSemiHomClass F φ A B] : CoeTC F (A →ₑ*[φ] B) :=
  ⟨MulDistribMulActionSemiHomClass.toMulDistribMulActionHom⟩

/-- If `DistribMulAction` of `M` and `N` on `A` commute,
then for each `c : M`, `(c • ·)` is an `N`-action additive homomorphism. -/
@[simps]
/-
**MulDistribMulActionHom._root_.SMulCommClass.toDistribMulActionHom** 是 Mathlib 
中的一个定义，位于命名空间 `MulDistribMulActionHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `DistribMulAction` of `M` and `N` on `A` commute,
then for each `c : M`, `(c • ·)` is an `N`-action additive homomorphism.
-/
def _root_.SMulCommClass.toDistribMulActionHom {M} (N A : Type*) [Monoid N] [AddMonoid A]
    [DistribSMul M A] [DistribMulAction N A] [SMulCommClass M N A] (c : M) : A →+[N] A :=
  { SMulCommClass.toMulActionHom N A c,
    DistribSMul.toAddMonoidHom _ c with
    toFun := (c • ·) }

@[to_additive (attr := simp) (dont_translate := M N)]
/-
**MulDistribMulActionHom.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `MulDistribMulAc
tionHom`。
形式化陈述：toFun_eq_coe (f : A ->ₑ*[φ] B) : f.toFun = f
参数：f : A ->ₑ*[φ] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe (f : A →ₑ*[φ] B) : f.toFun = f := rfl

@[to_additive (attr := norm_cast) (dont_translate := M N)]
/-
**MulDistribMulActionHom.coe_fn_coe** 是 Mathlib 中的一个定理，位于命名空间 `MulDistribMulActi
onHom`。
形式化陈述：coe_fn_coe (f : A ->ₑ*[φ] B) : ⇑(f : A ->* B) = f
参数：f : A ->ₑ*[φ] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulDistribMulActionSemiHomClass.toMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `MulDistribMulActionHom.instMulDistribMulActionSemiHomClassCoeMonoidHom`：
∀ {M : Type u_1} [inst : Monoid M] {N : Type u_2} [inst_1 : Monoid N] (φ : M →* 
N) (A : Type u_4) [inst_2 : Monoid A]   [inst_3 : MulDistrib…
-/
theorem coe_fn_coe (f : A →ₑ*[φ] B) : ⇑(f : A →* B) = f :=
  rfl

@[to_additive (attr := norm_cast) (dont_translate := M N)]
/-
**MulDistribMulActionHom.coe_fn_coe'** 是 Mathlib 中的一个定理，位于命名空间 `MulDistribMulAct
ionHom`。
形式化陈述：coe_fn_coe' (f : A ->ₑ*[φ] B) : ⇑(f : A ->ₑ[φ] B) = f
参数：f : A ->ₑ*[φ] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulDistribMulActionSemiHomClass.toMulActionSemiHomClass`：∀ {F : Type u_1
0} {M : outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)} 
  {A : outParam (Type u_13)} {B : outParam (T…
· 使用定理 `MulDistribMulActionHom.instMulDistribMulActionSemiHomClassCoeMonoidHom`：
∀ {M : Type u_1} [inst : Monoid M] {N : Type u_2} [inst_1 : Monoid N] (φ : M →* 
N) (A : Type u_4) [inst_2 : Monoid A]   [inst_3 : MulDistrib…
-/
theorem coe_fn_coe' (f : A →ₑ*[φ] B) : ⇑(f : A →ₑ[φ] B) = f :=
  rfl

@[to_additive (attr := ext) (dont_translate := M N)]
/-
**MulDistribMulActionHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `MulDistribMulActionHom`。
形式化陈述：ext {f g : A ->ₑ*[φ] B} : (forall x, f x = g x) -> f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : A →ₑ*[φ] B} : (∀ x, f x = g x) → f = g :=
  DFunLike.ext f g

@[to_additive (dont_translate := M N)]
/-
**MulDistribMulActionHom.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `MulDistribMulActio
nHom`。
形式化陈述：∀ {M : Type u_1} [inst : Monoid M] {N : Type u_2} [inst_1 : Monoid N] {φ :
 M →* N} {A : Type u_4} [inst_2 : Monoid A]   [inst_3 : MulDistribMulAction M A]
 {B : Type u_5} [inst_4 : Monoid B] [inst_5 : MulDistribMulAction N B]   {f g : 
A →ₑ*[φ] B}, f = g → ∀ (x : A), f x = g x
参数：x : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
protected theorem congr_fun {f g : A →ₑ*[φ] B} (h : f = g) (x : A) : f x = g x :=
  DFunLike.congr_fun h _

@[to_additive (dont_translate := M N)]
/-
**MulDistribMulActionHom.toMulActionHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `Mul
DistribMulActionHom`。
形式化陈述：toMulActionHom_injective {f g : A ->ₑ*[φ] B} (h : (f : A ->ₑ[φ] B) = (g : 
A ->ₑ[φ] B)) : f = g
参数：h : (f : A ->ₑ[φ] B) = (g : A ->ₑ[φ] B)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulDistribMulActionSemiHomClass.toMulActionSemiHomClass`：∀ {F : Type u_1
0} {M : outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)} 
  {A : outParam (Type u_13)} {B : outParam (T…
· 使用定理 `MulDistribMulActionHom.instMulDistribMulActionSemiHomClassCoeMonoidHom`：
∀ {M : Type u_1} [inst : Monoid M] {N : Type u_2} [inst_1 : Monoid N] (φ : M →* 
N) (A : Type u_4) [inst_2 : Monoid A]   [inst_3 : MulDistrib…
· 使用定理 `MulDistribMulActionHom.ext`：ext {f g : A ->ₑ*[φ] B} : (forall x, f x = g
 x) -> f = g
· 使用定理 `MulActionHom.congr_fun`：∀ {M : Type u_2} {N : Type u_3} {φ : M → N} {X :
 Type u_5} [inst : SMul M X] {Y : Type u_6} [inst_1 : SMul N Y]   {f g : X →ₑ[φ]
 Y}, f = g →…
-/
theorem toMulActionHom_injective {f g : A →ₑ*[φ] B} (h : (f : A →ₑ[φ] B) = (g : A →ₑ[φ] B)) :
    f = g := by
  ext a
  exact MulActionHom.congr_fun h a

@[to_additive (dont_translate := M N)]
/-
**MulDistribMulActionHom.toMonoidHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `MulDis
tribMulActionHom`。
形式化陈述：toMonoidHom_injective {f g : A ->ₑ*[φ] B} (h : (f : A ->* B) = (g : A ->* 
B)) : f = g
参数：h : (f : A ->* B) = (g : A ->* B)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulDistribMulActionSemiHomClass.toMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `MulDistribMulActionHom.instMulDistribMulActionSemiHomClassCoeMonoidHom`：
∀ {M : Type u_1} [inst : Monoid M] {N : Type u_2} [inst_1 : Monoid N] (φ : M →* 
N) (A : Type u_4) [inst_2 : Monoid A]   [inst_3 : MulDistrib…
· 使用定理 `MulDistribMulActionHom.ext`：ext {f g : A ->ₑ*[φ] B} : (forall x, f x = g
 x) -> f = g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem toMonoidHom_injective {f g : A →ₑ*[φ] B} (h : (f : A →* B) = (g : A →* B)) : f = g := by
  ext a
  exact DFunLike.congr_fun h a

@[to_additive (dont_translate := M N)]
/-
**MulDistribMulActionHom.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `MulDistribMulAction
Hom`。
形式化陈述：∀ {M : Type u_1} [inst : Monoid M] {N : Type u_2} [inst_1 : Monoid N] {φ :
 M →* N} {A : Type u_4} [inst_2 : Monoid A]   [inst_3 : MulDistribMulAction M A]
 {B : Type u_5} [inst_4 : Monoid B] [inst_5 : MulDistribMulAction N B]   (f : A 
→ₑ*[φ] B), f 1 = 1
参数：f : A →ₑ*[φ] B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulDistribMulActionSemiHomClass.toMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `MulDistribMulActionHom.instMulDistribMulActionSemiHomClassCoeMonoidHom`：
∀ {M : Type u_1} [inst : Monoid M] {N : Type u_2} [inst_1 : Monoid N] (φ : M →* 
N) (A : Type u_4) [inst_2 : Monoid A]   [inst_3 : MulDistrib…
-/
protected theorem map_zero (f : A →ₑ*[φ] B) : f 1 = 1 :=
  map_one f

@[to_additive (dont_translate := M N)]
/-
**MulDistribMulActionHom.map_mul** 是 Mathlib 中的一个定理，位于命名空间 `MulDistribMulActionH
om`。
形式化陈述：∀ {M : Type u_1} [inst : Monoid M] {N : Type u_2} [inst_1 : Monoid N] {φ :
 M →* N} {A : Type u_4} [inst_2 : Monoid A]   [inst_3 : MulDistribMulAction M A]
 {B : Type u_5} [inst_4 : Monoid B] [inst_5 : MulDistribMulAction N B]   (f : A 
→ₑ*[φ] B) (x y : A), f (x * y) = f x * f y
参数：f : A →ₑ*[φ] B；x y : A；x * y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulDistribMulActionSemiHomClass.toMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `MulDistribMulActionHom.instMulDistribMulActionSemiHomClassCoeMonoidHom`：
∀ {M : Type u_1} [inst : Monoid M] {N : Type u_2} [inst_1 : Monoid N] (φ : M →* 
N) (A : Type u_4) [inst_2 : Monoid A]   [inst_3 : MulDistrib…
-/
protected theorem map_mul (f : A →ₑ*[φ] B) (x y : A) : f (x * y) = f x * f y :=
  map_mul f x y

@[to_additive (dont_translate := M N)]
/-
**MulDistribMulActionHom.map_inv** 是 Mathlib 中的一个定理，位于命名空间 `MulDistribMulActionH
om`。
形式化陈述：∀ {M : Type u_1} [inst : Monoid M] {N : Type u_2} [inst_1 : Monoid N] {φ :
 M →* N} (A' : Type u_8) [inst_2 : Group A']   [inst_3 : MulDistribMulAction M A
'] (B' : Type u_9) [inst_4 : Group B'] [inst_5 : MulDistribMulAction N B']   (f 
: A' →ₑ*[φ] B') (x : A'), f x⁻¹ = (f x)⁻¹
参数：A' : Type u_8；B' : Type u_9；f : A' →ₑ*[φ] B'；x : A'；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `MulDistribMulActionSemiHomClass.toMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `MulDistribMulActionHom.instMulDistribMulActionSemiHomClassCoeMonoidHom`：
∀ {M : Type u_1} [inst : Monoid M] {N : Type u_2} [inst_1 : Monoid N] (φ : M →* 
N) (A : Type u_4) [inst_2 : Monoid A]   [inst_3 : MulDistrib…
-/
protected theorem map_inv (f : A' →ₑ*[φ] B') (x : A') : f x⁻¹ = (f x)⁻¹ :=
  map_inv f x

@[to_additive (dont_translate := M N)]
/-
**MulDistribMulActionHom.map_sub** 是 Mathlib 中的一个定理，位于命名空间 `MulDistribMulActionH
om`。
形式化陈述：∀ {M : Type u_1} [inst : Monoid M] {N : Type u_2} [inst_1 : Monoid N] {φ :
 M →* N} (A' : Type u_8) [inst_2 : Group A']   [inst_3 : MulDistribMulAction M A
'] (B' : Type u_9) [inst_4 : Group B'] [inst_5 : MulDistribMulAction N B']   (f 
: A' →ₑ*[φ] B') (x y : A'), f (x / y) = f x / f y
参数：A' : Type u_8；B' : Type u_9；f : A' →ₑ*[φ] B'；x y : A'；x / y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_div`：map_div [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) : forall a b, f (a / b) = f a / f b
· 使用定理 `MulDistribMulActionSemiHomClass.toMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `MulDistribMulActionHom.instMulDistribMulActionSemiHomClassCoeMonoidHom`：
∀ {M : Type u_1} [inst : Monoid M] {N : Type u_2} [inst_1 : Monoid N] (φ : M →* 
N) (A : Type u_4) [inst_2 : Monoid A]   [inst_3 : MulDistrib…
-/
protected theorem map_sub (f : A' →ₑ*[φ] B') (x y : A') : f (x / y) = f x / f y :=
  map_div f x y

@[to_additive (dont_translate := M N)]
/-
**MulDistribMulActionHom.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `MulDistribMulAction
Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem map_smulₑ (f : A →ₑ*[φ] B) (m : M) (x : A) : f (m • x) = (φ m) • f x :=
  map_smulₛₗ f m x

variable (M)

/-- The identity map as an equivariant monoid homomorphism. -/
@[to_additive (dont_translate := M) (attr := instance_reducible)
/-- The identity map as an equivariant additive monoid homomorphism. -/]
/-
**MulDistribMulActionHom.id** 是 Mathlib 中的一个定义，位于命名空间 `MulDistribMulActionHom`。
形式化陈述：(M : Type u_1) →   [inst : Monoid M] → {A : Type u_4} → [inst_1 : Monoid A
] → [inst_2 : MulDistribMulAction M A] → A →*[M] A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def id : A →*[M] A :=
  ⟨MulActionHom.id _, rfl, fun _ _ => rfl⟩

@[to_additive (attr := simp) (dont_translate := M)]
/-
**MulDistribMulActionHom.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulDistribMulAction
Hom`。
形式化陈述：id_apply (x : A) : MulDistribMulActionHom.id M x = x
参数：x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (x : A) : MulDistribMulActionHom.id M x = x := by
  rfl

variable {M C ψ χ}
/-
**MulDistribMulActionHom._root_.DistriMulActionHom.instZero** 是 Mathlib 中的一个实例，位
于命名空间 `MulDistribMulActionHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.DistriMulActionHom.instZero {A : Type*} [AddMonoid A] [DistribMulAction M A]
    {B : Type*} [AddMonoid B] [DistribMulAction N B] : Zero (A →ₑ+[φ] B) :=
  ⟨{ (0 : A →+ B) with map_smul' := fun m _ => by simp }⟩

@[to_additive (dont_translate := M)]
/-
**MulDistribMulActionHom.** 是 Mathlib 中的一个实例，位于命名空间 `MulDistribMulActionHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (A →*[M] A) :=
  ⟨MulDistribMulActionHom.id M⟩

@[simp]
/-
**MulDistribMulActionHom._root_.DistriMulActionHom.coe_zero** 是 Mathlib 中的一个定理，位
于命名空间 `MulDistribMulActionHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.DistriMulActionHom.coe_zero {A : Type*} [AddMonoid A] [DistribMulAction M A]
    {B : Type*} [AddMonoid B] [DistribMulAction N B] : ⇑(0 : A →ₑ+[φ] B) = 0 :=
  rfl

@[to_additive (attr := simp) (dont_translate := M)]
/-
**MulDistribMulActionHom.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `MulDistribMulActionH
om`。
形式化陈述：coe_one : ⇑(1 : A ->*[M] A) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ⇑(1 : A →*[M] A) = id :=
  rfl
/-
**MulDistribMulActionHom._root_.DistriMulActionHom.zero_apply** 是 Mathlib 中的一个定理
，位于命名空间 `MulDistribMulActionHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.DistriMulActionHom.zero_apply {A : Type*} [AddMonoid A] [DistribMulAction M A]
    {B : Type*} [AddMonoid B] [DistribMulAction N B] (a : A) : (0 : A →ₑ+[φ] B) a = 0 :=
  rfl

@[to_additive (dont_translate := M)]
/-
**MulDistribMulActionHom.one_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulDistribMulActio
nHom`。
形式化陈述：one_apply (a : A) : (1 : A ->*[M] A) a = a
参数：a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_apply (a : A) : (1 : A →*[M] A) a = a :=
  rfl
/-
**MulDistribMulActionHom.** 是 Mathlib 中的一个实例，位于命名空间 `MulDistribMulActionHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A : Type*} [AddMonoid A] [DistribMulAction M A]
    {B : Type*} [AddMonoid B] [DistribMulAction N B] :
    Inhabited (A →ₑ+[φ] B) :=
  ⟨0⟩

/-- Composition of two equivariant monoid homomorphisms. -/
@[to_additive (dont_translate := M N P) (attr := instance_reducible)
/-- Composition of two equivariant additive monoid homomorphisms. -/]
/-
**MulDistribMulActionHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `MulDistribMulActionHom`
。
形式化陈述：comp [κ : MonoidHom.CompTriple φ ψ χ] (g : B ->ₑ*[ψ] C) (f : A ->ₑ*[φ] B) 
: A ->ₑ*[χ] C
参数：g : B ->ₑ*[ψ] C；f : A ->ₑ*[φ] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def comp [κ : MonoidHom.CompTriple φ ψ χ]
    (g : B →ₑ*[ψ] C) (f : A →ₑ*[φ] B) : A →ₑ*[χ] C :=
  { MulActionHom.comp (g : B →ₑ[ψ] C) (f : A →ₑ[φ] B),
    MonoidHom.comp (g : B →* C) (f : A →* B) with }

@[to_additive (attr := simp) (dont_translate := M N P)]
/-
**MulDistribMulActionHom.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulDistribMulActi
onHom`。
形式化陈述：comp_apply (g : B ->ₑ*[ψ] C) (f : A ->ₑ*[φ] B) [MonoidHom.CompTriple φ ψ χ
] (x : A) : g.comp f x = g (f x)
参数：g : B ->ₑ*[ψ] C；f : A ->ₑ*[φ] B；x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (g : B →ₑ*[ψ] C) (f : A →ₑ*[φ] B) [MonoidHom.CompTriple φ ψ χ] (x : A) :
    g.comp f x = g (f x) := rfl

@[to_additive (attr := simp) (dont_translate := M N)]
/-
**MulDistribMulActionHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `MulDistribMulActionH
om`。
形式化陈述：id_comp (f : A ->ₑ*[φ] B) : comp (MulDistribMulActionHom.id N) f = f
参数：f : A ->ₑ*[φ] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulDistribMulActionHom.ext`：ext {f g : A ->ₑ*[φ] B} : (forall x, f x = g
 x) -> f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulDistribMulActionHom.comp_apply`：comp_apply (g : B ->ₑ*[ψ] C) (f : A -
>ₑ*[φ] B) [MonoidHom.CompTriple φ ψ χ] (x : A) : g.comp f x = g (f x)
· 使用定理 `MulDistribMulActionHom.id_apply`：id_apply (x : A) : MulDistribMulActionH
om.id M x = x
-/
theorem id_comp (f : A →ₑ*[φ] B) : comp (MulDistribMulActionHom.id N) f = f :=
  ext fun x => by rw [comp_apply, id_apply]

@[to_additive (attr := simp) (dont_translate := M N)]
/-
**MulDistribMulActionHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `MulDistribMulActionH
om`。
形式化陈述：comp_id (f : A ->ₑ*[φ] B) : f.comp (MulDistribMulActionHom.id M) = f
参数：f : A ->ₑ*[φ] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulDistribMulActionHom.ext`：ext {f g : A ->ₑ*[φ] B} : (forall x, f x = g
 x) -> f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulDistribMulActionHom.comp_apply`：comp_apply (g : B ->ₑ*[ψ] C) (f : A -
>ₑ*[φ] B) [MonoidHom.CompTriple φ ψ χ] (x : A) : g.comp f x = g (f x)
· 使用定理 `MulDistribMulActionHom.id_apply`：id_apply (x : A) : MulDistribMulActionH
om.id M x = x
-/
theorem comp_id (f : A →ₑ*[φ] B) : f.comp (MulDistribMulActionHom.id M) = f :=
  ext fun x => by rw [comp_apply, id_apply]

@[to_additive (attr := simp) (dont_translate := M N P Q)]
/-
**MulDistribMulActionHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `MulDistribMulActi
onHom`。
形式化陈述：comp_assoc {Q D : Type*} [Monoid Q] [Monoid D] [MulDistribMulAction Q D] {
η : P ->* Q} {θ : M ->* Q} {ζ : N ->* Q} (h : C ->ₑ*[η] D) (g : B ->ₑ*[ψ] C) (f 
: A ->ₑ*[φ] B) [MonoidHom.CompTriple φ ψ χ] [MonoidHom.CompTriple χ η θ] [Monoid
Hom.CompTriple ψ η ζ] [MonoidHom.CompTriple φ ζ θ] : h.comp (g.comp f) = (h.comp
 g).comp f
参数：h : C ->ₑ*[η] D；g : B ->ₑ*[ψ] C；f : A ->ₑ*[φ] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulDistribMulActionHom.ext`：ext {f g : A ->ₑ*[φ] B} : (forall x, f x = g
 x) -> f = g
-/
theorem comp_assoc {Q D : Type*} [Monoid Q] [Monoid D] [MulDistribMulAction Q D]
    {η : P →* Q} {θ : M →* Q} {ζ : N →* Q}
    (h : C →ₑ*[η] D) (g : B →ₑ*[ψ] C) (f : A →ₑ*[φ] B)
    [MonoidHom.CompTriple φ ψ χ] [MonoidHom.CompTriple χ η θ]
    [MonoidHom.CompTriple ψ η ζ] [MonoidHom.CompTriple φ ζ θ] :
    h.comp (g.comp f) = (h.comp g).comp f :=
  ext fun _ => rfl

/-- The inverse of a bijective `MulDistribMulActionHom` is a `MulDistribMulActionHom`. -/
@[to_additive (attr := simp) (dont_translate := M)
/-- The inverse of a bijective `DistribMulActionHom` is a `DistribMulActionHom`. -/]
/-
**MulDistribMulActionHom.inverse** 是 Mathlib 中的一个定义，位于命名空间 `MulDistribMulActionH
om`。
形式化陈述：inverse (f : A ->*[M] B₁) (g : B₁ -> A) (h₁ : Function.LeftInverse g f) (h
₂ : Function.RightInverse g f) : B₁ ->*[M] A
参数：f : A ->*[M] B₁；g : B₁ -> A；h₁ : Function.LeftInverse g f；h₂ : Function.Right
Inverse g f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def inverse (f : A →*[M] B₁) (g : B₁ → A) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : B₁ →*[M] A :=
  { (f : A →* B₁).inverse g h₁ h₂, f.toMulActionHom.inverse g h₁ h₂ with toFun := g }

end MulDistribMulActionHom

section Semiring

variable (R : Type*) [Semiring R] [MulSemiringAction M R]
variable (S : Type*) [Semiring S] [MulSemiringAction N S]
variable (T : Type*) [Semiring T] [MulSemiringAction P T]

variable {R S N'}
variable [AddMonoid N'] [DistribMulAction S N']

variable {σ : R →* S}
@[ext]
/-
**DistribMulActionHom.ext_ring** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DistribMulActionHom.ext_ring {f g : R ->ₑ+[σ] N'} (h : f 1 = g 1) : f = g
参数：h : f 1 = g 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DistribMulActionHom.ext`：∀ {M : Type u_1} [inst : Monoid M] {N : Type u_
2} [inst_1 : Monoid N] {φ : M →* N} {A : Type u_4} [inst_2 : AddMonoid A]   [ins
t_3 : Distrib…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `DistribMulActionHom.map_smulₑ`：∀ {M : Type u_1} [inst : Monoid M] {N : T
ype u_2} [inst_1 : Monoid N] {φ : M →* N} {A : Type u_4} [inst_2 : AddMonoid A] 
  [inst_3 : Distrib…
-/
theorem DistribMulActionHom.ext_ring {f g : R →ₑ+[σ] N'} (h : f 1 = g 1) : f = g := by
  ext x
  rw [← mul_one x, ← smul_eq_mul, f.map_smulₑ, g.map_smulₑ, h]

end Semiring


variable (R : Type*) [Semiring R] [MulSemiringAction M R]
variable (R' : Type*) [Ring R'] [MulSemiringAction M R']
variable (S : Type*) [Semiring S] [MulSemiringAction N S]
variable (S' : Type*) [Ring S'] [MulSemiringAction N S']
variable (T : Type*) [Semiring T] [MulSemiringAction P T]

/-- Equivariant ring homomorphisms. -/
/-
**MulSemiringActionHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{M : Type u_1} →   [inst : Monoid M] →     {N : Type u_2} →       [inst_1 
: Monoid N] →         (M →* N) →           (R : Type u_10) →             [inst_2
 : Semiring R] →               [MulSemiringAction M R] →                 (S : Ty
pe u_12) → [inst : Semiring S] → [MulSemiringAction N S] → Type (max u_10 u_12)
参数：M →* N；R : Type u_10；S : Type u_12；max u_10 u_12。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivariant ring homomorphisms.
-/
structure MulSemiringActionHom extends R →ₑ+[φ] S, R →+* S

/-- Reinterpret an equivariant ring homomorphism as a ring homomorphism. -/
add_decl_doc MulSemiringActionHom.toRingHom

/-- Reinterpret an equivariant ring homomorphism as an equivariant additive monoid homomorphism. -/
add_decl_doc MulSemiringActionHom.toDistribMulActionHom

@[inherit_doc]
notation:25 (name := «MulSemiringActionHomLocal≺»)
  R " →ₑ+*[" φ:25 "] " S:0 => MulSemiringActionHom φ R S

@[inherit_doc]
notation:25 (name := «MulSemiringActionHomIdLocal≺»)
  R " →+*[" M:25 "] " S:0 => MulSemiringActionHom (MonoidHom.id M) R S

/-- `MulSemiringActionHomClass F φ R S` states that `F` is a type of morphisms preserving
the ring structure and equivariant with respect to `φ`.

You should extend this class when you extend `MulSemiringActionHom`. -/
/-
**MulSemiringActionSemiHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_15) →   {M : outParam (Type u_16)} →     {N : outParam (Type u
_17)} →       [inst : Monoid M] →         [inst_1 : Monoid N] →           outPar
am (M → N) →             (R : outParam (Type u_18)) →               (S : outPara
m (Type u_19)) →                 [inst_2 : Semiring R] →                   [inst
_3 : Semiring S] → [DistribMulAction M R] → [DistribMulAction N S] → [FunLike F 
R S] → Prop
参数：Type u_18；Type u_19。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MulSemiringActionHomClass F φ R S` states that `F` is a type of morphisms prese
rving
the ring structure and equivariant with respect to `φ`.

You should extend this class when you extend `MulSemiringActionHom`.
-/
class MulSemiringActionSemiHomClass (F : Type*)
    {M N : outParam Type*} [Monoid M] [Monoid N]
    (φ : outParam (M → N))
    (R S : outParam Type*) [Semiring R] [Semiring S]
    [DistribMulAction M R] [DistribMulAction N S] [FunLike F R S] : Prop
    extends DistribMulActionSemiHomClass F φ R S, RingHomClass F R S

/-- `MulSemiringActionHomClass F M R S` states that `F` is a type of morphisms preserving
the ring structure and equivariant with respect to a `DistribMulAction` of `M` on `R` and `S`.
-/
/-
**MulSemiringActionHomClass** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：MulSemiringActionHomClass (F : Type*) {M : outParam Type*} [Monoid M] (R S
 : outParam Type*) [Semiring R] [Semiring S] [DistribMulAction M R] [DistribMulA
ction M S] [FunLike F R S]
参数：F : Type*；R S : outParam Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MulSemiringActionHomClass F M R S` states that `F` is a type of morphisms prese
rving
the ring structure and equivariant with respect to a `DistribMulAction` of `M` o
n `R` and `S`.
-/
abbrev MulSemiringActionHomClass
    (F : Type*)
    {M : outParam Type*} [Monoid M]
    (R S : outParam Type*) [Semiring R] [Semiring S]
    [DistribMulAction M R] [DistribMulAction M S] [FunLike F R S] :=
  MulSemiringActionSemiHomClass F (MonoidHom.id M) R S

namespace MulSemiringActionHom

/-
**MulSemiringActionHom.** 是 Mathlib 中的一个实例，位于命名空间 `MulSemiringActionHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (R →ₑ+*[φ] S) R S where
  coe m := m.toFun
  coe_injective f g h := by
    rcases f with ⟨⟨tF, _, _⟩, _, _⟩; rcases g with ⟨⟨tG, _, _⟩, _, _⟩
    cases tF; cases tG; congr
/-
**MulSemiringActionHom.** 是 Mathlib 中的一个实例，位于命名空间 `MulSemiringActionHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulSemiringActionSemiHomClass (R →ₑ+*[φ] S) φ R S where
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
/-
**MulSemiringActionHom._root_.MulSemiringActionHomClass.toMulSemiringActionHom**
 是 Mathlib 中的一个定义，位于命名空间 `MulSemiringActionHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn an element of a type `F` satisfying `MulSemiringActionHomClass F M R S` int
o an actual
`MulSemiringActionHom`. This is declared as the default coercion from `F` to
`MulSemiringActionHom M X Y`.
-/
def _root_.MulSemiringActionHomClass.toMulSemiringActionHom
    [MulSemiringActionSemiHomClass F φ R S]
    (f : F) : R →ₑ+*[φ] S :=
  { (f : R →+* S), (f : R →ₑ+[φ] S) with }

/-- Any type satisfying `MulSemiringActionHomClass` can be cast into `MulSemiringActionHom` via
  `MulSemiringActionHomClass.toMulSemiringActionHom`. -/
/-
**MulSemiringActionHom.** 是 Mathlib 中的一个实例，位于命名空间 `MulSemiringActionHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any type satisfying `MulSemiringActionHomClass` can be cast into `MulSemiringAct
ionHom` via
  `MulSemiringActionHomClass.toMulSemiringActionHom`.
-/
instance [MulSemiringActionSemiHomClass F φ R S] :
    CoeTC F (R →ₑ+*[φ] S) :=
  ⟨MulSemiringActionHomClass.toMulSemiringActionHom⟩

@[norm_cast]
/-
**MulSemiringActionHom.coe_fn_coe** 是 Mathlib 中的一个定理，位于命名空间 `MulSemiringActionHo
m`。
形式化陈述：coe_fn_coe (f : R ->ₑ+*[φ] S) : ⇑(f : R ->+* S) = f
参数：f : R ->ₑ+*[φ] S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulSemiringActionSemiHomClass.toRingHomClass`：∀ {F : Type u_15} {M : out
Param (Type u_16)} {N : outParam (Type u_17)} [inst : Monoid M] [inst_1 : Monoid
 N]   (φ : outParam (M → N)) {R : …
· 使用定理 `MulSemiringActionHom.instMulSemiringActionSemiHomClassCoeMonoidHom`：∀ {M
 : Type u_1} [inst : Monoid M] {N : Type u_2} [inst_1 : Monoid N] (φ : M →* N) (
R : Type u_10) [inst_2 : Semiring R]   [inst_3 : MulSemi…
-/
theorem coe_fn_coe (f : R →ₑ+*[φ] S) : ⇑(f : R →+* S) = f :=
  rfl

@[norm_cast]
/-
**MulSemiringActionHom.coe_fn_coe'** 是 Mathlib 中的一个定理，位于命名空间 `MulSemiringActionH
om`。
形式化陈述：coe_fn_coe' (f : R ->ₑ+*[φ] S) : ⇑(f : R ->ₑ+[φ] S) = f
参数：f : R ->ₑ+*[φ] S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulSemiringActionSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Typ
e u_15} {M : outParam (Type u_16)} {N : outParam (Type u_17)} {inst : Monoid M} 
{inst_1 : Monoid N}   {φ : outParam (M → N)} {R : …
· 使用定理 `MulSemiringActionHom.instMulSemiringActionSemiHomClassCoeMonoidHom`：∀ {M
 : Type u_1} [inst : Monoid M] {N : Type u_2} [inst_1 : Monoid N] (φ : M →* N) (
R : Type u_10) [inst_2 : Semiring R]   [inst_3 : MulSemi…
-/
theorem coe_fn_coe' (f : R →ₑ+*[φ] S) : ⇑(f : R →ₑ+[φ] S) = f :=
  rfl

@[ext]
/-
**MulSemiringActionHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `MulSemiringActionHom`。
形式化陈述：ext {f g : R ->ₑ+*[φ] S} : (forall x, f x = g x) -> f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : R →ₑ+*[φ] S} : (∀ x, f x = g x) → f = g :=
  DFunLike.ext f g
/-
**MulSemiringActionHom.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `MulSemiringActionHom`
。
形式化陈述：∀ {M : Type u_1} [inst : Monoid M] {N : Type u_2} [inst_1 : Monoid N] {φ :
 M →* N} {R : Type u_10} [inst_2 : Semiring R]   [inst_3 : MulSemiringAction M R
] {S : Type u_12} [inst_4 : Semiring S] [inst_5 : MulSemiringAction N S]   (f : 
R →ₑ+*[φ] S), f 0 = 0
参数：f : R →ₑ+*[φ] S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulSemiringActionSemiHomClass.toRingHomClass`：∀ {F : Type u_15} {M : out
Param (Type u_16)} {N : outParam (Type u_17)} [inst : Monoid M] [inst_1 : Monoid
 N]   (φ : outParam (M → N)) {R : …
· 使用定理 `MulSemiringActionHom.instMulSemiringActionSemiHomClassCoeMonoidHom`：∀ {M
 : Type u_1} [inst : Monoid M] {N : Type u_2} [inst_1 : Monoid N] (φ : M →* N) (
R : Type u_10) [inst_2 : Semiring R]   [inst_3 : MulSemi…
-/
protected theorem map_zero (f : R →ₑ+*[φ] S) : f 0 = 0 :=
  map_zero f
/-
**MulSemiringActionHom.map_add** 是 Mathlib 中的一个定理，位于命名空间 `MulSemiringActionHom`。
形式化陈述：∀ {M : Type u_1} [inst : Monoid M] {N : Type u_2} [inst_1 : Monoid N] {φ :
 M →* N} {R : Type u_10} [inst_2 : Semiring R]   [inst_3 : MulSemiringAction M R
] {S : Type u_12} [inst_4 : Semiring S] [inst_5 : MulSemiringAction N S]   (f : 
R →ₑ+*[φ] S) (x y : R), f (x + y) = f x + f y
参数：f : R →ₑ+*[φ] S；x y : R；x + y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `MulSemiringActionSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Typ
e u_15} {M : outParam (Type u_16)} {N : outParam (Type u_17)} {inst : Monoid M} 
{inst_1 : Monoid N}   {φ : outParam (M → N)} {R : …
· 使用定理 `MulSemiringActionHom.instMulSemiringActionSemiHomClassCoeMonoidHom`：∀ {M
 : Type u_1} [inst : Monoid M] {N : Type u_2} [inst_1 : Monoid N] (φ : M →* N) (
R : Type u_10) [inst_2 : Semiring R]   [inst_3 : MulSemi…
-/
protected theorem map_add (f : R →ₑ+*[φ] S) (x y : R) : f (x + y) = f x + f y :=
  map_add f x y
/-
**MulSemiringActionHom.map_neg** 是 Mathlib 中的一个定理，位于命名空间 `MulSemiringActionHom`。
形式化陈述：∀ {M : Type u_1} [inst : Monoid M] {N : Type u_2} [inst_1 : Monoid N] {φ :
 M →* N} (R' : Type u_11) [inst_2 : Ring R']   [inst_3 : MulSemiringAction M R']
 (S' : Type u_13) [inst_4 : Ring S'] [inst_5 : MulSemiringAction N S']   (f : R'
 →ₑ+*[φ] S') (x : R'), f (-x) = -f x
参数：R' : Type u_11；S' : Type u_13；f : R' →ₑ+*[φ] S'；x : R'；-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `MulSemiringActionSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Typ
e u_15} {M : outParam (Type u_16)} {N : outParam (Type u_17)} {inst : Monoid M} 
{inst_1 : Monoid N}   {φ : outParam (M → N)} {R : …
· 使用定理 `MulSemiringActionHom.instMulSemiringActionSemiHomClassCoeMonoidHom`：∀ {M
 : Type u_1} [inst : Monoid M] {N : Type u_2} [inst_1 : Monoid N] (φ : M →* N) (
R : Type u_10) [inst_2 : Semiring R]   [inst_3 : MulSemi…
-/
protected theorem map_neg (f : R' →ₑ+*[φ] S') (x : R') : f (-x) = -f x :=
  map_neg f x
/-
**MulSemiringActionHom.map_sub** 是 Mathlib 中的一个定理，位于命名空间 `MulSemiringActionHom`。
形式化陈述：∀ {M : Type u_1} [inst : Monoid M] {N : Type u_2} [inst_1 : Monoid N] {φ :
 M →* N} (R' : Type u_11) [inst_2 : Ring R']   [inst_3 : MulSemiringAction M R']
 (S' : Type u_13) [inst_4 : Ring S'] [inst_5 : MulSemiringAction N S']   (f : R'
 →ₑ+*[φ] S') (x y : R'), f (x - y) = f x - f y
参数：R' : Type u_11；S' : Type u_13；f : R' →ₑ+*[φ] S'；x y : R'；x - y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `MulSemiringActionSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Typ
e u_15} {M : outParam (Type u_16)} {N : outParam (Type u_17)} {inst : Monoid M} 
{inst_1 : Monoid N}   {φ : outParam (M → N)} {R : …
· 使用定理 `MulSemiringActionHom.instMulSemiringActionSemiHomClassCoeMonoidHom`：∀ {M
 : Type u_1} [inst : Monoid M] {N : Type u_2} [inst_1 : Monoid N] (φ : M →* N) (
R : Type u_10) [inst_2 : Semiring R]   [inst_3 : MulSemi…
-/
protected theorem map_sub (f : R' →ₑ+*[φ] S') (x y : R') : f (x - y) = f x - f y :=
  map_sub f x y
/-
**MulSemiringActionHom.map_one** 是 Mathlib 中的一个定理，位于命名空间 `MulSemiringActionHom`。
形式化陈述：∀ {M : Type u_1} [inst : Monoid M] {N : Type u_2} [inst_1 : Monoid N] {φ :
 M →* N} {R : Type u_10} [inst_2 : Semiring R]   [inst_3 : MulSemiringAction M R
] {S : Type u_12} [inst_4 : Semiring S] [inst_5 : MulSemiringAction N S]   (f : 
R →ₑ+*[φ] S), f 1 = 1
参数：f : R →ₑ+*[φ] S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulSemiringActionSemiHomClass.toRingHomClass`：∀ {F : Type u_15} {M : out
Param (Type u_16)} {N : outParam (Type u_17)} [inst : Monoid M] [inst_1 : Monoid
 N]   (φ : outParam (M → N)) {R : …
· 使用定理 `MulSemiringActionHom.instMulSemiringActionSemiHomClassCoeMonoidHom`：∀ {M
 : Type u_1} [inst : Monoid M] {N : Type u_2} [inst_1 : Monoid N] (φ : M →* N) (
R : Type u_10) [inst_2 : Semiring R]   [inst_3 : MulSemi…
-/
protected theorem map_one (f : R →ₑ+*[φ] S) : f 1 = 1 :=
  map_one f
/-
**MulSemiringActionHom.map_mul** 是 Mathlib 中的一个定理，位于命名空间 `MulSemiringActionHom`。
形式化陈述：∀ {M : Type u_1} [inst : Monoid M] {N : Type u_2} [inst_1 : Monoid N] {φ :
 M →* N} {R : Type u_10} [inst_2 : Semiring R]   [inst_3 : MulSemiringAction M R
] {S : Type u_12} [inst_4 : Semiring S] [inst_5 : MulSemiringAction N S]   (f : 
R →ₑ+*[φ] S) (x y : R), f (x * y) = f x * f y
参数：f : R →ₑ+*[φ] S；x y : R；x * y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `MulSemiringActionSemiHomClass.toRingHomClass`：∀ {F : Type u_15} {M : out
Param (Type u_16)} {N : outParam (Type u_17)} [inst : Monoid M] [inst_1 : Monoid
 N]   (φ : outParam (M → N)) {R : …
· 使用定理 `MulSemiringActionHom.instMulSemiringActionSemiHomClassCoeMonoidHom`：∀ {M
 : Type u_1} [inst : Monoid M] {N : Type u_2} [inst_1 : Monoid N] (φ : M →* N) (
R : Type u_10) [inst_2 : Semiring R]   [inst_3 : MulSemi…
-/
protected theorem map_mul (f : R →ₑ+*[φ] S) (x y : R) : f (x * y) = f x * f y :=
  map_mul f x y
/-
**MulSemiringActionHom.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `MulSemiringActionHom`
。
形式化陈述：∀ {M : Type u_1} [inst : Monoid M] {R : Type u_10} [inst_1 : Semiring R] [
inst_2 : MulSemiringAction M R]   {S : Type u_12} [inst_3 : Semiring S] [inst_4 
: MulSemiringAction M S] (f : R →+*[M] S) (m : M) (x : R),   f (m • x) = m • f x
参数：f : R →+*[M] S；m : M；x : R；m • x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `DistribMulActionSemiHomClass.toMulActionSemiHomClass`：∀ {F : Type u_10} 
{M : outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {
A : outParam (Type u_13)} {B : outParam (T…
· 使用定理 `MulSemiringActionSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Typ
e u_15} {M : outParam (Type u_16)} {N : outParam (Type u_17)} {inst : Monoid M} 
{inst_1 : Monoid N}   {φ : outParam (M → N)} {R : …
· 使用定理 `MulSemiringActionHom.instMulSemiringActionSemiHomClassCoeMonoidHom`：∀ {M
 : Type u_1} [inst : Monoid M] {N : Type u_2} [inst_1 : Monoid N] (φ : M →* N) (
R : Type u_10) [inst_2 : Semiring R]   [inst_3 : MulSemi…
-/
protected theorem map_smulₛₗ (f : R →ₑ+*[φ] S) (m : M) (x : R) : f (m • x) = φ m • f x :=
  map_smulₛₗ f m x
/-
**MulSemiringActionHom.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `MulSemiringActionHom`
。
形式化陈述：∀ {M : Type u_1} [inst : Monoid M] {R : Type u_10} [inst_1 : Semiring R] [
inst_2 : MulSemiringAction M R]   {S : Type u_12} [inst_3 : Semiring S] [inst_4 
: MulSemiringAction M S] (f : R →+*[M] S) (m : M) (x : R),   f (m • x) = m • f x
参数：f : R →+*[M] S；m : M；x : R；m • x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `DistribMulActionSemiHomClass.toMulActionSemiHomClass`：∀ {F : Type u_10} 
{M : outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {
A : outParam (Type u_13)} {B : outParam (T…
· 使用定理 `MulSemiringActionSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Typ
e u_15} {M : outParam (Type u_16)} {N : outParam (Type u_17)} {inst : Monoid M} 
{inst_1 : Monoid N}   {φ : outParam (M → N)} {R : …
· 使用定理 `MulSemiringActionHom.instMulSemiringActionSemiHomClassCoeMonoidHom`：∀ {M
 : Type u_1} [inst : Monoid M] {N : Type u_2} [inst_1 : Monoid N] (φ : M →* N) (
R : Type u_10) [inst_2 : Semiring R]   [inst_3 : MulSemi…
-/
protected theorem map_smul [MulSemiringAction M S] (f : R →+*[M] S) (m : M) (x : R) :
    f (m • x) = m • f x :=
  map_smulₛₗ f m x

end MulSemiringActionHom

namespace MulSemiringActionHom

variable (M) {R}

/-- The identity map as an equivariant ring homomorphism. -/
@[instance_reducible]
/-
**MulSemiringActionHom.id** 是 Mathlib 中的一个定义，位于命名空间 `MulSemiringActionHom`。
形式化陈述：(M : Type u_1) →   [inst : Monoid M] → {R : Type u_10} → [inst_1 : Semirin
g R] → [inst_2 : MulSemiringAction M R] → R →+*[M] R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity map as an equivariant ring homomorphism.
-/
protected def id : R →+*[M] R :=
  ⟨DistribMulActionHom.id _, rfl, (fun _ _ => rfl)⟩

@[simp]
/-
**MulSemiringActionHom.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulSemiringActionHom`
。
形式化陈述：id_apply (x : R) : MulSemiringActionHom.id M x = x
参数：x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**MulSemiringActionHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `MulSemiringActionHom`。
形式化陈述：comp (g : S ->ₑ+*[ψ] T) (f : R ->ₑ+*[φ] S) [κ : MonoidHom.CompTriple φ ψ χ
] : R ->ₑ+*[χ] T
参数：g : S ->ₑ+*[ψ] T；f : R ->ₑ+*[φ] S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of two equivariant additive ring homomorphisms.
-/
def comp (g : S →ₑ+*[ψ] T) (f : R →ₑ+*[φ] S) [κ : MonoidHom.CompTriple φ ψ χ] : R →ₑ+*[χ] T :=
  { DistribMulActionHom.comp (g : S →ₑ+[ψ] T) (f : R →ₑ+[φ] S),
    RingHom.comp (g : S →+* T) (f : R →+* S) with }

@[simp]
/-
**MulSemiringActionHom.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulSemiringActionHo
m`。
形式化陈述：comp_apply (g : S ->ₑ+*[ψ] T) (f : R ->ₑ+*[φ] S) [MonoidHom.CompTriple φ ψ
 χ] (x : R) : g.comp f x = g (f x)
参数：g : S ->ₑ+*[ψ] T；f : R ->ₑ+*[φ] S；x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (g : S →ₑ+*[ψ] T) (f : R →ₑ+*[φ] S) [MonoidHom.CompTriple φ ψ χ] (x : R) :
    g.comp f x = g (f x) := rfl

@[simp]
/-
**MulSemiringActionHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `MulSemiringActionHom`。
形式化陈述：id_comp (f : R ->ₑ+*[φ] S) : (MulSemiringActionHom.id N).comp f = f
参数：f : R ->ₑ+*[φ] S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulSemiringActionHom.ext`：ext {f g : R ->ₑ+*[φ] S} : (forall x, f x = g 
x) -> f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulSemiringActionHom.comp_apply`：comp_apply (g : S ->ₑ+*[ψ] T) (f : R ->
ₑ+*[φ] S) [MonoidHom.CompTriple φ ψ χ] (x : R) : g.comp f x = g (f x)
· 使用定理 `MulSemiringActionHom.id_apply`：id_apply (x : R) : MulSemiringActionHom.i
d M x = x
-/
theorem id_comp (f : R →ₑ+*[φ] S) : (MulSemiringActionHom.id N).comp f = f :=
  ext fun x => by rw [comp_apply, id_apply]

@[simp]
/-
**MulSemiringActionHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `MulSemiringActionHom`。
形式化陈述：comp_id (f : R ->ₑ+*[φ] S) : f.comp (MulSemiringActionHom.id M) = f
参数：f : R ->ₑ+*[φ] S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulSemiringActionHom.ext`：ext {f g : R ->ₑ+*[φ] S} : (forall x, f x = g 
x) -> f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulSemiringActionHom.comp_apply`：comp_apply (g : S ->ₑ+*[ψ] T) (f : R ->
ₑ+*[φ] S) [MonoidHom.CompTriple φ ψ χ] (x : R) : g.comp f x = g (f x)
· 使用定理 `MulSemiringActionHom.id_apply`：id_apply (x : R) : MulSemiringActionHom.i
d M x = x
-/
theorem comp_id (f : R →ₑ+*[φ] S) : f.comp (MulSemiringActionHom.id M) = f :=
  ext fun x => by rw [comp_apply, id_apply]

/-- The inverse of a bijective `MulSemiringActionHom` is a `MulSemiringActionHom`. -/
@[simps]
/-
**MulSemiringActionHom.inverse'** 是 Mathlib 中的一个定义，位于命名空间 `MulSemiringActionHom`
。
形式化陈述：inverse' (f : R ->ₑ+*[φ] S) (g : S -> R) (k : Function.RightInverse φ' φ) 
(h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : S ->ₑ+*[φ'] R
参数：f : R ->ₑ+*[φ] S；g : S -> R；k : Function.RightInverse φ' φ；h₁ : Function.Left
Inverse g f；h₂ : Function.RightInverse g f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of a bijective `MulSemiringActionHom` is a `MulSemiringActionHom`.
-/
def inverse' (f : R →ₑ+*[φ] S) (g : S → R) (k : Function.RightInverse φ' φ)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
    S →ₑ+*[φ'] R :=
  { (f : R →+ S).inverse g h₁ h₂,
    (f : R →* S).inverse g h₁ h₂,
    (f : R →ₑ[φ] S).inverse' g k h₁ h₂ with
    toFun := g }

/-- The inverse of a bijective `MulSemiringActionHom` is a `MulSemiringActionHom`. -/
@[simps]
/-
**MulSemiringActionHom.inverse** 是 Mathlib 中的一个定义，位于命名空间 `MulSemiringActionHom`。
形式化陈述：inverse {S₁ : Type*} [Semiring S₁] [MulSemiringAction M S₁] (f : R ->+*[M]
 S₁) (g : S₁ -> R) (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g
 f) : S₁ ->+*[M] R
参数：f : R ->+*[M] S₁；g : S₁ -> R；h₁ : Function.LeftInverse g f；h₂ : Function.Righ
tInverse g f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of a bijective `MulSemiringActionHom` is a `MulSemiringActionHom`.
-/
def inverse {S₁ : Type*} [Semiring S₁] [MulSemiringAction M S₁]
    (f : R →+*[M] S₁) (g : S₁ → R)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
    S₁ →+*[M] R :=
  { (f : R →+ S₁).inverse g h₁ h₂,
    (f : R →* S₁).inverse g h₁ h₂,
    f.toMulActionHom.inverse g h₁ h₂ with
    toFun := g }

end MulSemiringActionHom

end DistribMulAction

/-
**IsSMulRegular.of_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSMulRegular.of_injective {R M : Type*} [SMul R M] {N F} [SMul R N] [FunL
ike F M N] [MulActionHomClass F R M N] (f : F) {r : R} (h1 : Function.Injective 
f) (h2 : IsSMulRegular N r) : IsSMulRegular M r
参数：f : F；h1 : Function.Injective f；h2 : IsSMulRegular N r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma IsSMulRegular.of_injective {R M : Type*} [SMul R M]
    {N F} [SMul R N] [FunLike F M N] [MulActionHomClass F R M N]
    (f : F) {r : R} (h1 : Function.Injective f) (h2 : IsSMulRegular N r) :
    IsSMulRegular M r := fun x y h3 => h1 <| h2 <|
  (map_smulₛₗ f r x).symm.trans ((congrArg f h3).trans (map_smulₛₗ f r y))
