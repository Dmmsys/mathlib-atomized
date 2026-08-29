/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Group.Units.Equiv

/-!
# Characters from additive to multiplicative monoids

Let `A` be an additive monoid, and `M` a multiplicative one. An *additive character* of `A` with
values in `M` is simply a map `A → M` which intertwines the addition operation on `A` with the
multiplicative operation on `M`.

We define these objects, using the namespace `AddChar`, and show that if `A` is a commutative group
under addition, then the additive characters are also a group (written multiplicatively). Note that
we do not need `M` to be a group here.

We also include some constructions specific to the case when `A = R` is a ring; then we define
`mulShift ψ r`, where `ψ : AddChar R M` and `r : R`, to be the character defined by
`x ↦ ψ (r * x)`.

For more refined results of a number-theoretic nature (primitive characters, Gauss sums, etc)
see `Mathlib/NumberTheory/LegendreSymbol/AddCharacter.lean`.

## Implementation notes

Due to their role as the dual of an additive group, additive characters must themselves be an
additive group. This contrasts to their pointwise operations which make them a multiplicative group.
We simply define both the additive and multiplicative group structures and prove them equal.

For more information on this design decision, see the following zulip thread:
https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Additive.20characters

## Tags

additive character
-/

@[expose] public section

/-!
### Definitions related to and results on additive characters
-/

open Function Multiplicative
open Finset hiding card
open Fintype (card)

section AddCharDef

-- The domain of our additive characters
variable (A : Type*) [AddMonoid A]

-- The target
variable (M : Type*) [Monoid M]

/--
Definition of `AddChar` / `AddChar` 的定义

English:
structure AddChar
  parameters: where
  axioms and operations (3):
    - toFun : A -> M
    - map_zero_eq_one' : toFun 0 = 1
    - map_add_eq_mul' : forall a b : A, toFun (a + b) = toFun a * toFun b

中文:
结构 AddChar
  参数: where
  公理与运算 (3 个):
    - toFun : A -> M
    - map_zero_eq_one' : toFun 0 = 1
    - map_add_eq_mul' : 对任意 a b : A, toFun (a + b) = toFun a * toFun b
-/
structure AddChar where
  /-- The underlying function.

  Do not use this function directly. Instead use the coercion coming from the `FunLike`
  instance. -/
  toFun : A -> M
  /-- The function maps `0` to `1`.

  Do not use this directly. Instead use `AddChar.map_zero_eq_one`. -/
  map_zero_eq_one' : toFun 0 = 1
  /-- The function maps addition in `A` to multiplication in `M`.

  Do not use this directly. Instead use `AddChar.map_add_eq_mul`. -/
  map_add_eq_mul' : forall a b : A, toFun (a + b) = toFun a * toFun b

end AddCharDef

namespace AddChar

section Basic
-- results which don't require commutativity or inverses

variable {A B M N : Type*} [AddMonoid A] [AddMonoid B] [Monoid M] [Monoid N] {ψ : AddChar A M}

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (AddChar A M) A M where
  body: AddChar.toFun
  coe_injective φ ψ h := by cases φ; cases ψ; congr

initialize_simps_projections AddChar (toFun -> apply) -- needs to come after FunLike instance

中文:
实例 instFunLike
  签名: : FunLike (AddChar A M) A M where
  定义体: AddChar.toFun
  coe_injective φ ψ h := by cases φ; cases ψ; congr

initialize_simps_projections AddChar (toFun -> apply) -- needs to come after FunLike instance

Depends on / 依赖: AddChar, AddChar.toFun
-/
instance instFunLike : FunLike (AddChar A M) A M where
  coe := AddChar.toFun
  coe_injective φ ψ h := by cases φ; cases ψ; congr

initialize_simps_projections AddChar (toFun -> apply) -- needs to come after FunLike instance

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: (f g : AddChar A M) (h : forall x : A, f x = g x)
  statement: f = g
  proof: DFunLike.ext f g h

中文:
引理 ext
  条件: (f g : AddChar A M) (h : 对任意 x : A, f x = g x)
  结论: f = g
  证明: DFunLike.ext f g h
-/
@[ext] lemma ext (f g : AddChar A M) (h : forall x : A, f x = g x) : f = g :=
  DFunLike.ext f g h

/--
lemma `coe_mk` / 引理 `coe_mk`

English:
lemma coe_mk
  statement: (f : A -> M)
  proof: by
  rfl

中文:
引理 coe_mk
  结论: (f : A -> M)
  证明: by
  rfl
-/
@[simp] lemma coe_mk (f : A -> M)
    (map_zero_eq_one' : f 0 = 1) (map_add_eq_mul' : forall a b : A, f (a + b) = f a * f b) :
    AddChar.mk f map_zero_eq_one' map_add_eq_mul' = f := by
  rfl

/--
lemma `map_zero_eq_one` / 引理 `map_zero_eq_one`

English:
lemma map_zero_eq_one
  given: (ψ : AddChar A M)
  statement: ψ 0 = 1
  proof: ψ.map_zero_eq_one'

中文:
引理 map_zero_eq_one
  条件: (ψ : AddChar A M)
  结论: ψ 0 = 1
  证明: ψ.map_zero_eq_one'
-/
@[simp] lemma map_zero_eq_one (ψ : AddChar A M) : ψ 0 = 1 := ψ.map_zero_eq_one'

/--
lemma `map_add_eq_mul` / 引理 `map_add_eq_mul`

English:
lemma map_add_eq_mul
  given: (ψ : AddChar A M) (x y : A)
  statement: ψ (x + y) = ψ x * ψ y
  proof: ψ.map_add_eq_mul' x y

中文:
引理 map_add_eq_mul
  条件: (ψ : AddChar A M) (x y : A)
  结论: ψ (x + y) = ψ x * ψ y
  证明: ψ.map_add_eq_mul' x y

Depends on / 依赖: map_add_eq_mul
-/
lemma map_add_eq_mul (ψ : AddChar A M) (x y : A) : ψ (x + y) = ψ x * ψ y := ψ.map_add_eq_mul' x y

/--
Definition of `toMonoidHom` / `toMonoidHom` 的定义

English:
definition toMonoidHom
  signature: (φ : AddChar A M)
  body: φ.toFun
  map_one' := φ.map_zero_eq_one'
  map_mul' := φ.map_add_eq_mul'

中文:
定义 toMonoidHom
  签名: (φ : AddChar A M)
  定义体: φ.toFun
  map_one' := φ.map_zero_eq_one'
  map_mul' := φ.map_add_eq_mul'
-/
def toMonoidHom (φ : AddChar A M) : Multiplicative A ->* M where
  toFun := φ.toFun
  map_one' := φ.map_zero_eq_one'
  map_mul' := φ.map_add_eq_mul'

-- this instance was a bad idea and conflicted with `instFunLike` above

/--
lemma `toMonoidHom_apply` / 引理 `toMonoidHom_apply`

English:
lemma toMonoidHom_apply
  given: (ψ : AddChar A M) (a : Multiplicative A)
  proof: rfl

中文:
引理 toMonoidHom_apply
  条件: (ψ : AddChar A M) (a : Multiplicative A)
  证明: rfl
-/
@[simp] lemma toMonoidHom_apply (ψ : AddChar A M) (a : Multiplicative A) :
    ψ.toMonoidHom a = ψ a.toAdd :=
  rfl

/--
lemma `map_nsmul_eq_pow` / 引理 `map_nsmul_eq_pow`

English:
lemma map_nsmul_eq_pow
  given: (ψ : AddChar A M) (n : Nat) (x : A)
  statement: ψ (n • x) = ψ x ^ n
  proof: ψ.toMonoidHom.map_pow x n

中文:
引理 map_nsmul_eq_pow
  条件: (ψ : AddChar A M) (n : 自然数) (x : A)
  结论: ψ (n • x) = ψ x ^ n
  证明: ψ.toMonoidHom.map_pow x n

Depends on / 依赖: map_pow, toMonoidHom, toMonoidHom.map_pow
-/
lemma map_nsmul_eq_pow (ψ : AddChar A M) (n : Nat) (x : A) : ψ (n • x) = ψ x ^ n :=
  ψ.toMonoidHom.map_pow x n

/--
Definition of `toMonoidHomEquiv` / `toMonoidHomEquiv` 的定义

English:
definition toMonoidHomEquiv
  signature: : AddChar A M ≃ (Multiplicative A ->* M) where
  body: φ.toMonoidHom
  invFun f :=
  { toFun := f.toFun
    map_zero_eq_one' := f.map_one'
    map_add_eq_mul' := f.map_mul' }

中文:
定义 toMonoidHomEquiv
  签名: : AddChar A M ≃ (Multiplicative A ->* M) where
  定义体: φ.toMonoidHom
  invFun f :=
  { toFun := f.toFun
    map_zero_eq_one' := f.map_one'
    map_add_eq_mul' := f.map_mul' }

Depends on / 依赖: toMonoidHom
-/
def toMonoidHomEquiv : AddChar A M ≃ (Multiplicative A ->* M) where
  toFun φ := φ.toMonoidHom
  invFun f :=
  { toFun := f.toFun
    map_zero_eq_one' := f.map_one'
    map_add_eq_mul' := f.map_mul' }

/--
lemma `coe_toMonoidHomEquiv` / 引理 `coe_toMonoidHomEquiv`

English:
lemma coe_toMonoidHomEquiv
  given: (ψ : AddChar A M)
  proof: rfl

中文:
引理 coe_toMonoidHomEquiv
  条件: (ψ : AddChar A M)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_toMonoidHomEquiv (ψ : AddChar A M) :
    ⇑(toMonoidHomEquiv ψ) = ψ ∘ Multiplicative.toAdd := rfl

/--
lemma `coe_toMonoidHomEquiv_symm` / 引理 `coe_toMonoidHomEquiv_symm`

English:
lemma coe_toMonoidHomEquiv_symm
  given: (ψ : Multiplicative A ->* M)
  proof: rfl

中文:
引理 coe_toMonoidHomEquiv_symm
  条件: (ψ : Multiplicative A ->* M)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_toMonoidHomEquiv_symm (ψ : Multiplicative A ->* M) :
    ⇑(toMonoidHomEquiv.symm ψ) = ψ ∘ Multiplicative.ofAdd := rfl

/--
lemma `toMonoidHomEquiv_apply` / 引理 `toMonoidHomEquiv_apply`

English:
lemma toMonoidHomEquiv_apply
  given: (ψ : AddChar A M) (a : Multiplicative A)
  proof: rfl

中文:
引理 toMonoidHomEquiv_apply
  条件: (ψ : AddChar A M) (a : Multiplicative A)
  证明: rfl
-/
@[simp] lemma toMonoidHomEquiv_apply (ψ : AddChar A M) (a : Multiplicative A) :
    toMonoidHomEquiv ψ a = ψ a.toAdd := rfl

/--
lemma `toMonoidHomEquiv_symm_apply` / 引理 `toMonoidHomEquiv_symm_apply`

English:
lemma toMonoidHomEquiv_symm_apply
  given: (ψ : Multiplicative A ->* M) (a : A)
  proof: rfl

中文:
引理 toMonoidHomEquiv_symm_apply
  条件: (ψ : Multiplicative A ->* M) (a : A)
  证明: rfl
-/
@[simp] lemma toMonoidHomEquiv_symm_apply (ψ : Multiplicative A ->* M) (a : A) :
    toMonoidHomEquiv.symm ψ a = ψ (Multiplicative.ofAdd a) := rfl

/--
Definition of `toAddMonoidHom` / `toAddMonoidHom` 的定义

English:
definition toAddMonoidHom
  signature: (φ : AddChar A M)
  body: φ.toFun
  map_zero' := φ.map_zero_eq_one'
  map_add' := φ.map_add_eq_mul'

中文:
定义 toAddMonoidHom
  签名: (φ : AddChar A M)
  定义体: φ.toFun
  map_zero' := φ.map_zero_eq_one'
  map_add' := φ.map_add_eq_mul'
-/
def toAddMonoidHom (φ : AddChar A M) : A ->+ Additive M where
  toFun := φ.toFun
  map_zero' := φ.map_zero_eq_one'
  map_add' := φ.map_add_eq_mul'

/--
lemma `coe_toAddMonoidHom` / 引理 `coe_toAddMonoidHom`

English:
lemma coe_toAddMonoidHom
  given: (ψ : AddChar A M)
  statement: ⇑ψ.toAddMonoidHom = Additive.ofMul ∘ ψ
  proof: rfl

中文:
引理 coe_toAddMonoidHom
  条件: (ψ : AddChar A M)
  结论: ⇑ψ.toAddMonoidHom = Additive.ofMul ∘ ψ
  证明: rfl
-/
@[simp] lemma coe_toAddMonoidHom (ψ : AddChar A M) : ⇑ψ.toAddMonoidHom = Additive.ofMul ∘ ψ := rfl

/--
lemma `toAddMonoidHom_apply` / 引理 `toAddMonoidHom_apply`

English:
lemma toAddMonoidHom_apply
  given: (ψ : AddChar A M) (a : A)
  proof: rfl

中文:
引理 toAddMonoidHom_apply
  条件: (ψ : AddChar A M) (a : A)
  证明: rfl
-/
@[simp] lemma toAddMonoidHom_apply (ψ : AddChar A M) (a : A) :
    ψ.toAddMonoidHom a = Additive.ofMul (ψ a) := rfl

/--
Definition of `toAddMonoidHomEquiv` / `toAddMonoidHomEquiv` 的定义

English:
definition toAddMonoidHomEquiv
  signature: : AddChar A M ≃ (A ->+ Additive M) where
  body: φ.toAddMonoidHom
  invFun f :=
  { toFun := f.toFun
    map_zero_eq_one' := f.map_zero'
    map_add_eq_mul' := f.map_add' }

@[simp, norm_cast]

中文:
定义 toAddMonoidHomEquiv
  签名: : AddChar A M ≃ (A ->+ Additive M) where
  定义体: φ.toAddMonoidHom
  invFun f :=
  { toFun := f.toFun
    map_zero_eq_one' := f.map_zero'
    map_add_eq_mul' := f.map_add' }

@[simp, norm_cast]

Depends on / 依赖: toAddMonoidHom
-/
def toAddMonoidHomEquiv : AddChar A M ≃ (A ->+ Additive M) where
  toFun φ := φ.toAddMonoidHom
  invFun f :=
  { toFun := f.toFun
    map_zero_eq_one' := f.map_zero'
    map_add_eq_mul' := f.map_add' }

@[simp, norm_cast]
/--
lemma `coe_toAddMonoidHomEquiv` / 引理 `coe_toAddMonoidHomEquiv`

English:
lemma coe_toAddMonoidHomEquiv
  given: (ψ : AddChar A M)
  proof: rfl

中文:
引理 coe_toAddMonoidHomEquiv
  条件: (ψ : AddChar A M)
  证明: rfl
-/
lemma coe_toAddMonoidHomEquiv (ψ : AddChar A M) :
    ⇑(toAddMonoidHomEquiv ψ) = Additive.ofMul ∘ ψ := rfl

/--
lemma `coe_toAddMonoidHomEquiv_symm` / 引理 `coe_toAddMonoidHomEquiv_symm`

English:
lemma coe_toAddMonoidHomEquiv_symm
  given: (ψ : A ->+ Additive M)
  proof: rfl

中文:
引理 coe_toAddMonoidHomEquiv_symm
  条件: (ψ : A ->+ Additive M)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_toAddMonoidHomEquiv_symm (ψ : A ->+ Additive M) :
    ⇑(toAddMonoidHomEquiv.symm ψ) = Additive.toMul ∘ ψ := rfl

/--
lemma `toAddMonoidHomEquiv_apply` / 引理 `toAddMonoidHomEquiv_apply`

English:
lemma toAddMonoidHomEquiv_apply
  given: (ψ : AddChar A M) (a : A)
  proof: rfl

中文:
引理 toAddMonoidHomEquiv_apply
  条件: (ψ : AddChar A M) (a : A)
  证明: rfl
-/
@[simp] lemma toAddMonoidHomEquiv_apply (ψ : AddChar A M) (a : A) :
    toAddMonoidHomEquiv ψ a = Additive.ofMul (ψ a) := rfl

/--
lemma `toAddMonoidHomEquiv_symm_apply` / 引理 `toAddMonoidHomEquiv_symm_apply`

English:
lemma toAddMonoidHomEquiv_symm_apply
  given: (ψ : A ->+ Additive M) (a : A)
  proof: rfl

中文:
引理 toAddMonoidHomEquiv_symm_apply
  条件: (ψ : A ->+ Additive M) (a : A)
  证明: rfl
-/
@[simp] lemma toAddMonoidHomEquiv_symm_apply (ψ : A ->+ Additive M) (a : A) :
    toAddMonoidHomEquiv.symm ψ a = (ψ a).toMul := rfl

/--
Instance `instOne` / 实例 `instOne`

English:
instance instOne
  signature: : One (AddChar A M)
  body: toMonoidHomEquiv.one

中文:
实例 instOne
  签名: : One (AddChar A M)
  定义体: toMonoidHomEquiv.one

Depends on / 依赖: toMonoidHomEquiv, toMonoidHomEquiv.one
-/
instance instOne : One (AddChar A M) := toMonoidHomEquiv.one

/--
Instance `instZero` / 实例 `instZero`

English:
instance instZero
  signature: : Zero (AddChar A M)
  body: ⟨1⟩

中文:
实例 instZero
  签名: : Zero (AddChar A M)
  定义体: ⟨1⟩
-/
instance instZero : Zero (AddChar A M) := ⟨1⟩

/--
lemma `coe_one` / 引理 `coe_one`

English:
lemma coe_one
  statement: ⇑(1 : AddChar A M) = 1
  proof: rfl

中文:
引理 coe_one
  结论: ⇑(1 : AddChar A M) = 1
  证明: rfl
-/
@[simp, norm_cast] lemma coe_one : ⇑(1 : AddChar A M) = 1 := rfl
/--
lemma `coe_zero` / 引理 `coe_zero`

English:
lemma coe_zero
  statement: ⇑(0 : AddChar A M) = 1
  proof: rfl

中文:
引理 coe_zero
  结论: ⇑(0 : AddChar A M) = 1
  证明: rfl
-/
@[simp, norm_cast] lemma coe_zero : ⇑(0 : AddChar A M) = 1 := rfl
/--
lemma `one_apply` / 引理 `one_apply`

English:
lemma one_apply
  given: (a : A)
  statement: (1 : AddChar A M) a = 1
  proof: rfl

中文:
引理 one_apply
  条件: (a : A)
  结论: (1 : AddChar A M) a = 1
  证明: rfl
-/
@[simp] lemma one_apply (a : A) : (1 : AddChar A M) a = 1 := rfl
/--
lemma `zero_apply` / 引理 `zero_apply`

English:
lemma zero_apply
  given: (a : A)
  statement: (0 : AddChar A M) a = 1
  proof: rfl

中文:
引理 zero_apply
  条件: (a : A)
  结论: (0 : AddChar A M) a = 1
  证明: rfl
-/
@[simp] lemma zero_apply (a : A) : (0 : AddChar A M) a = 1 := rfl

/--
lemma `one_eq_zero` / 引理 `one_eq_zero`

English:
lemma one_eq_zero
  statement: (1 : AddChar A M) = (0 : AddChar A M)
  proof: rfl

中文:
引理 one_eq_zero
  结论: (1 : AddChar A M) = (0 : AddChar A M)
  证明: rfl
-/
lemma one_eq_zero : (1 : AddChar A M) = (0 : AddChar A M) := rfl

/--
lemma `coe_eq_one` / 引理 `coe_eq_one`

English:
lemma coe_eq_one
  statement: ⇑ψ = 1 ↔ ψ = 0
  proof: by rw [← coe_zero, DFunLike.coe_fn_eq]

中文:
引理 coe_eq_one
  结论: ⇑ψ = 1 ↔ ψ = 0
  证明: by rw [← coe_zero, DFunLike.coe_fn_eq]
-/
@[simp, norm_cast] lemma coe_eq_one : ⇑ψ = 1 ↔ ψ = 0 := by rw [← coe_zero, DFunLike.coe_fn_eq]

/--
lemma `toMonoidHomEquiv_zero` / 引理 `toMonoidHomEquiv_zero`

English:
lemma toMonoidHomEquiv_zero
  statement: toMonoidHomEquiv (0 : AddChar A M) = 1
  proof: rfl

中文:
引理 toMonoidHomEquiv_zero
  结论: toMonoidHomEquiv (0 : AddChar A M) = 1
  证明: rfl
-/
@[simp] lemma toMonoidHomEquiv_zero : toMonoidHomEquiv (0 : AddChar A M) = 1 := rfl
/--
lemma `toMonoidHomEquiv_symm_one` / 引理 `toMonoidHomEquiv_symm_one`

English:
lemma toMonoidHomEquiv_symm_one
  proof: rfl

中文:
引理 toMonoidHomEquiv_symm_one
  证明: rfl
-/
@[simp] lemma toMonoidHomEquiv_symm_one :
    toMonoidHomEquiv.symm (1 : Multiplicative A ->* M) = 0 := rfl

/--
lemma `toAddMonoidHomEquiv_zero` / 引理 `toAddMonoidHomEquiv_zero`

English:
lemma toAddMonoidHomEquiv_zero
  statement: toAddMonoidHomEquiv (0 : AddChar A M) = 0
  proof: rfl

中文:
引理 toAddMonoidHomEquiv_zero
  结论: toAddMonoidHomEquiv (0 : AddChar A M) = 0
  证明: rfl
-/
@[simp] lemma toAddMonoidHomEquiv_zero : toAddMonoidHomEquiv (0 : AddChar A M) = 0 := rfl
/--
lemma `toAddMonoidHomEquiv_symm_zero` / 引理 `toAddMonoidHomEquiv_symm_zero`

English:
lemma toAddMonoidHomEquiv_symm_zero
  proof: rfl

中文:
引理 toAddMonoidHomEquiv_symm_zero
  证明: rfl
-/
@[simp] lemma toAddMonoidHomEquiv_symm_zero :
    toAddMonoidHomEquiv.symm (0 : A ->+ Additive M) = 0 := rfl

/--
Instance `instInhabited` / 实例 `instInhabited`

English:
instance instInhabited
  signature: : Inhabited (AddChar A M)
  body: ⟨1⟩

中文:
实例 instInhabited
  签名: : Inhabited (AddChar A M)
  定义体: ⟨1⟩
-/
instance instInhabited : Inhabited (AddChar A M) := ⟨1⟩

/--
Definition of `_root_.MonoidHom.compAddChar` / `_root_.MonoidHom.compAddChar` 的定义

English:
definition _root_.MonoidHom.compAddChar
  signature: {N : Type*} [Monoid N] (f : M ->* N) (φ : AddChar A M)
  body: toMonoidHomEquiv.symm (f.comp φ.toMonoidHom)

@[simp, norm_cast]

中文:
定义 _root_.MonoidHom.compAddChar
  签名: {N : 类型} [Monoid N] (f : M ->* N) (φ : AddChar A M)
  定义体: toMonoidHomEquiv.symm (f.comp φ.toMonoidHom)

@[simp, norm_cast]

Depends on / 依赖: f.comp, toMonoidHom, toMonoidHomEquiv, toMonoidHomEquiv.symm
-/
def _root_.MonoidHom.compAddChar {N : Type*} [Monoid N] (f : M ->* N) (φ : AddChar A M) :
    AddChar A N := toMonoidHomEquiv.symm (f.comp φ.toMonoidHom)

@[simp, norm_cast]
/--
lemma `_root_.MonoidHom.coe_compAddChar` / 引理 `_root_.MonoidHom.coe_compAddChar`

English:
lemma _root_.MonoidHom.coe_compAddChar
  given: {N : Type*} [Monoid N] (f : M ->* N) (φ : AddChar A M)
  proof: rfl

@[simp, norm_cast]

中文:
引理 _root_.MonoidHom.coe_compAddChar
  条件: {N : 类型} [Monoid N] (f : M ->* N) (φ : AddChar A M)
  证明: rfl

@[simp, norm_cast]
-/
lemma _root_.MonoidHom.coe_compAddChar {N : Type*} [Monoid N] (f : M ->* N) (φ : AddChar A M) :
    f.compAddChar φ = f ∘ φ :=
  rfl

@[simp, norm_cast]
/--
lemma `_root_.MonoidHom.compAddChar_apply` / 引理 `_root_.MonoidHom.compAddChar_apply`

English:
lemma _root_.MonoidHom.compAddChar_apply
  given: (f : M ->* N) (φ : AddChar A M)
  statement: f.compAddChar φ = f ∘ φ
  proof: rfl

中文:
引理 _root_.MonoidHom.compAddChar_apply
  条件: (f : M ->* N) (φ : AddChar A M)
  结论: f.compAddChar φ = f ∘ φ
  证明: rfl
-/
lemma _root_.MonoidHom.compAddChar_apply (f : M ->* N) (φ : AddChar A M) : f.compAddChar φ = f ∘ φ :=
  rfl

/--
lemma `_root_.MonoidHom.compAddChar_injective_left` / 引理 `_root_.MonoidHom.compAddChar_injective_left`

English:
lemma _root_.MonoidHom.compAddChar_injective_left
  given: (ψ : AddChar A M) (hψ : Surjective ψ)
  proof: by
  rintro f g h; rw [DFunLike.ext'_iff] at h ⊢; exact hψ.injective_comp_right h

中文:
引理 _root_.MonoidHom.compAddChar_injective_left
  条件: (ψ : AddChar A M) (hψ : Surjective ψ)
  证明: by
  rintro f g h; rw [DFunLike.ext'_iff] at h ⊢; exact hψ.injective_comp_right h

Depends on / 依赖: DFunLike, DFunLike.ext, _iff, injective_comp_right
-/
lemma _root_.MonoidHom.compAddChar_injective_left (ψ : AddChar A M) (hψ : Surjective ψ) :
    Injective fun f : M ->* N => f.compAddChar ψ := by
  rintro f g h; rw [DFunLike.ext'_iff] at h ⊢; exact hψ.injective_comp_right h

/--
lemma `_root_.MonoidHom.compAddChar_injective_right` / 引理 `_root_.MonoidHom.compAddChar_injective_right`

English:
lemma _root_.MonoidHom.compAddChar_injective_right
  given: (f : M ->* N) (hf : Injective f)
  proof: by
  rintro ψ χ h; rw [DFunLike.ext'_iff] at h ⊢; exact hf.comp_left h

中文:
引理 _root_.MonoidHom.compAddChar_injective_right
  条件: (f : M ->* N) (hf : Injective f)
  证明: by
  rintro ψ χ h; rw [DFunLike.ext'_iff] at h ⊢; exact hf.comp_left h

Depends on / 依赖: DFunLike, DFunLike.ext, _iff, comp_left, hf.comp_left
-/
lemma _root_.MonoidHom.compAddChar_injective_right (f : M ->* N) (hf : Injective f) :
    Injective fun ψ : AddChar B M => f.compAddChar ψ := by
  rintro ψ χ h; rw [DFunLike.ext'_iff] at h ⊢; exact hf.comp_left h

/--
Definition of `compAddMonoidHom` / `compAddMonoidHom` 的定义

English:
definition compAddMonoidHom
  signature: (φ : AddChar B M) (f : A ->+ B)
  body: toAddMonoidHomEquiv.symm (φ.toAddMonoidHom.comp f)

@[simp, norm_cast]

中文:
定义 compAddMonoidHom
  签名: (φ : AddChar B M) (f : A ->+ B)
  定义体: toAddMonoidHomEquiv.symm (φ.toAddMonoidHom.comp f)

@[simp, norm_cast]

Depends on / 依赖: toAddMonoidHom, toAddMonoidHom.comp, toAddMonoidHomEquiv, toAddMonoidHomEquiv.symm
-/
def compAddMonoidHom (φ : AddChar B M) (f : A ->+ B) : AddChar A M :=
  toAddMonoidHomEquiv.symm (φ.toAddMonoidHom.comp f)

@[simp, norm_cast]
/--
lemma `coe_compAddMonoidHom` / 引理 `coe_compAddMonoidHom`

English:
lemma coe_compAddMonoidHom
  given: (φ : AddChar B M) (f : A ->+ B)
  statement: φ.compAddMonoidHom f = φ ∘ f
  proof: rfl

中文:
引理 coe_compAddMonoidHom
  条件: (φ : AddChar B M) (f : A ->+ B)
  结论: φ.compAddMonoidHom f = φ ∘ f
  证明: rfl
-/
lemma coe_compAddMonoidHom (φ : AddChar B M) (f : A ->+ B) : φ.compAddMonoidHom f = φ ∘ f := rfl

/--
lemma `compAddMonoidHom_apply` / 引理 `compAddMonoidHom_apply`

English:
lemma compAddMonoidHom_apply
  statement: (ψ : AddChar B M) (f : A ->+ B)
  proof: rfl

中文:
引理 compAddMonoidHom_apply
  结论: (ψ : AddChar B M) (f : A ->+ B)
  证明: rfl
-/
@[simp] lemma compAddMonoidHom_apply (ψ : AddChar B M) (f : A ->+ B)
    (a : A) : ψ.compAddMonoidHom f a = ψ (f a) := rfl

/--
lemma `compAddMonoidHom_injective_left` / 引理 `compAddMonoidHom_injective_left`

English:
lemma compAddMonoidHom_injective_left
  given: (f : A ->+ B) (hf : Surjective f)
  proof: by
  rintro ψ χ h; rw [DFunLike.ext'_iff] at h ⊢; exact hf.injective_comp_right h

中文:
引理 compAddMonoidHom_injective_left
  条件: (f : A ->+ B) (hf : Surjective f)
  证明: by
  rintro ψ χ h; rw [DFunLike.ext'_iff] at h ⊢; exact hf.injective_comp_right h

Depends on / 依赖: DFunLike, DFunLike.ext, _iff, hf.injective_comp_right, injective_comp_right
-/
lemma compAddMonoidHom_injective_left (f : A ->+ B) (hf : Surjective f) :
    Injective fun ψ : AddChar B M => ψ.compAddMonoidHom f := by
  rintro ψ χ h; rw [DFunLike.ext'_iff] at h ⊢; exact hf.injective_comp_right h

/--
lemma `compAddMonoidHom_injective_right` / 引理 `compAddMonoidHom_injective_right`

English:
lemma compAddMonoidHom_injective_right
  given: (ψ : AddChar B M) (hψ : Injective ψ)
  proof: by
  rintro f g h
  rw [DFunLike.ext'_iff] at h ⊢; exact hψ.comp_left h

中文:
引理 compAddMonoidHom_injective_right
  条件: (ψ : AddChar B M) (hψ : Injective ψ)
  证明: by
  rintro f g h
  rw [DFunLike.ext'_iff] at h ⊢; exact hψ.comp_left h

Depends on / 依赖: DFunLike, DFunLike.ext, _iff, comp_left
-/
lemma compAddMonoidHom_injective_right (ψ : AddChar B M) (hψ : Injective ψ) :
    Injective fun f : A ->+ B => ψ.compAddMonoidHom f := by
  rintro f g h
  rw [DFunLike.ext'_iff] at h ⊢; exact hψ.comp_left h

/--
lemma `eq_one_iff` / 引理 `eq_one_iff`

English:
lemma eq_one_iff
  statement: ψ = 1 ↔ forall x, ψ x = 1
  proof: DFunLike.ext_iff

中文:
引理 eq_one_iff
  结论: ψ = 1 ↔ 对任意 x, ψ x = 1
  证明: DFunLike.ext_iff

Depends on / 依赖: DFunLike, DFunLike.ext_iff, ext_iff
-/
lemma eq_one_iff : ψ = 1 ↔ forall x, ψ x = 1 := DFunLike.ext_iff
/--
lemma `eq_zero_iff` / 引理 `eq_zero_iff`

English:
lemma eq_zero_iff
  statement: ψ = 0 ↔ forall x, ψ x = 1
  proof: DFunLike.ext_iff

中文:
引理 eq_zero_iff
  结论: ψ = 0 ↔ 对任意 x, ψ x = 1
  证明: DFunLike.ext_iff

Depends on / 依赖: DFunLike, DFunLike.ext_iff, ext_iff
-/
lemma eq_zero_iff : ψ = 0 ↔ forall x, ψ x = 1 := DFunLike.ext_iff
/--
lemma `ne_one_iff` / 引理 `ne_one_iff`

English:
lemma ne_one_iff
  statement: ψ != 1 ↔ exists x, ψ x != 1
  proof: DFunLike.ne_iff

中文:
引理 ne_one_iff
  结论: ψ != 1 ↔ 存在 x, ψ x != 1
  证明: DFunLike.ne_iff

Depends on / 依赖: DFunLike, DFunLike.ne_iff, ne_iff
-/
lemma ne_one_iff : ψ != 1 ↔ exists x, ψ x != 1 := DFunLike.ne_iff
/--
lemma `ne_zero_iff` / 引理 `ne_zero_iff`

English:
lemma ne_zero_iff
  statement: ψ != 0 ↔ exists x, ψ x != 1
  proof: DFunLike.ne_iff

中文:
引理 ne_zero_iff
  结论: ψ != 0 ↔ 存在 x, ψ x != 1
  证明: DFunLike.ne_iff

Depends on / 依赖: DFunLike, DFunLike.ne_iff, ne_iff
-/
lemma ne_zero_iff : ψ != 0 ↔ exists x, ψ x != 1 := DFunLike.ne_iff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecidableEq (AddChar A M)
  body: Classical.decEq _

中文:
实例 :
  签名: DecidableEq (AddChar A M)
  定义体: Classical.decEq _

Depends on / 依赖: Classical, Classical.decEq
-/
noncomputable instance : DecidableEq (AddChar A M) := Classical.decEq _

end Basic

section toCommMonoid

variable {ι A M : Type*} [AddMonoid A] [CommMonoid M]

/--
Instance `instCommMonoid` / 实例 `instCommMonoid`

English:
instance instCommMonoid
  signature: : CommMonoid (AddChar A M)
  body: fast_instance% toMonoidHomEquiv.commMonoid

中文:
实例 instCommMonoid
  签名: : CommMonoid (AddChar A M)
  定义体: fast_instance% toMonoidHomEquiv.commMonoid

Depends on / 依赖: commMonoid, fast_instance, toMonoidHomEquiv, toMonoidHomEquiv.commMonoid
-/
instance instCommMonoid : CommMonoid (AddChar A M) :=
  fast_instance% toMonoidHomEquiv.commMonoid

/--
Instance `instAddCommMonoid` / 实例 `instAddCommMonoid`

English:
instance instAddCommMonoid
  signature: : AddCommMonoid (AddChar A M)
  body: inferInstanceAs (AddCommMonoid (Additive (AddChar A M)))

中文:
实例 instAddCommMonoid
  签名: : AddCommMonoid (AddChar A M)
  定义体: inferInstanceAs (AddCommMonoid (Additive (AddChar A M)))

Depends on / 依赖: AddChar, AddCommMonoid, Additive
-/
instance instAddCommMonoid : AddCommMonoid (AddChar A M) :=
  inferInstanceAs (AddCommMonoid (Additive (AddChar A M)))

/--
lemma `coe_mul` / 引理 `coe_mul`

English:
lemma coe_mul
  given: (ψ χ : AddChar A M)
  statement: ⇑(ψ * χ) = ψ * χ
  proof: rfl

中文:
引理 coe_mul
  条件: (ψ χ : AddChar A M)
  结论: ⇑(ψ * χ) = ψ * χ
  证明: rfl
-/
@[simp, norm_cast] lemma coe_mul (ψ χ : AddChar A M) : ⇑(ψ * χ) = ψ * χ := rfl
/--
lemma `coe_add` / 引理 `coe_add`

English:
lemma coe_add
  given: (ψ χ : AddChar A M)
  statement: ⇑(ψ + χ) = ψ * χ
  proof: rfl

中文:
引理 coe_add
  条件: (ψ χ : AddChar A M)
  结论: ⇑(ψ + χ) = ψ * χ
  证明: rfl
-/
@[simp, norm_cast] lemma coe_add (ψ χ : AddChar A M) : ⇑(ψ + χ) = ψ * χ := rfl
/--
lemma `coe_pow` / 引理 `coe_pow`

English:
lemma coe_pow
  given: (ψ : AddChar A M) (n : Nat)
  statement: ⇑(ψ ^ n) = ψ ^ n
  proof: rfl

中文:
引理 coe_pow
  条件: (ψ : AddChar A M) (n : 自然数)
  结论: ⇑(ψ ^ n) = ψ ^ n
  证明: rfl
-/
@[simp, norm_cast] lemma coe_pow (ψ : AddChar A M) (n : Nat) : ⇑(ψ ^ n) = ψ ^ n := rfl
/--
lemma `coe_nsmul` / 引理 `coe_nsmul`

English:
lemma coe_nsmul
  given: (n : Nat) (ψ : AddChar A M)
  statement: ⇑(n • ψ) = ψ ^ n
  proof: rfl

@[simp, norm_cast]

中文:
引理 coe_nsmul
  条件: (n : 自然数) (ψ : AddChar A M)
  结论: ⇑(n • ψ) = ψ ^ n
  证明: rfl

@[simp, norm_cast]
-/
@[simp, norm_cast] lemma coe_nsmul (n : Nat) (ψ : AddChar A M) : ⇑(n • ψ) = ψ ^ n := rfl

@[simp, norm_cast]
/--
lemma `coe_prod` / 引理 `coe_prod`

English:
lemma coe_prod
  given: (s : Finset ι) (ψ : ι -> AddChar A M)
  statement: ∏ i in s, ψ i = ∏ i in s, ⇑(ψ i)
  proof: by
  induction s using Finset.cons_induction <;> simp [*]

@[simp, norm_cast]

中文:
引理 coe_prod
  条件: (s : Finset ι) (ψ : ι -> AddChar A M)
  结论: ∏ i in s, ψ i = ∏ i in s, ⇑(ψ i)
  证明: by
  induction s using Finset.cons_induction <;> simp [*]

@[simp, norm_cast]

Depends on / 依赖: Finset, Finset.cons_induction, cons_induction
-/
lemma coe_prod (s : Finset ι) (ψ : ι -> AddChar A M) : ∏ i in s, ψ i = ∏ i in s, ⇑(ψ i) := by
  induction s using Finset.cons_induction <;> simp [*]

@[simp, norm_cast]
/--
lemma `coe_sum` / 引理 `coe_sum`

English:
lemma coe_sum
  given: (s : Finset ι) (ψ : ι -> AddChar A M)
  statement: ∑ i in s, ψ i = ∏ i in s, ⇑(ψ i)
  proof: by
  induction s using Finset.cons_induction <;> simp [*]

中文:
引理 coe_sum
  条件: (s : Finset ι) (ψ : ι -> AddChar A M)
  结论: ∑ i in s, ψ i = ∏ i in s, ⇑(ψ i)
  证明: by
  induction s using Finset.cons_induction <;> simp [*]

Depends on / 依赖: Finset, Finset.cons_induction, cons_induction
-/
lemma coe_sum (s : Finset ι) (ψ : ι -> AddChar A M) : ∑ i in s, ψ i = ∏ i in s, ⇑(ψ i) := by
  induction s using Finset.cons_induction <;> simp [*]

/--
lemma `mul_apply` / 引理 `mul_apply`

English:
lemma mul_apply
  given: (ψ φ : AddChar A M) (a : A)
  statement: (ψ * φ) a = ψ a * φ a
  proof: rfl

中文:
引理 mul_apply
  条件: (ψ φ : AddChar A M) (a : A)
  结论: (ψ * φ) a = ψ a * φ a
  证明: rfl
-/
@[simp] lemma mul_apply (ψ φ : AddChar A M) (a : A) : (ψ * φ) a = ψ a * φ a := rfl
/--
lemma `add_apply` / 引理 `add_apply`

English:
lemma add_apply
  given: (ψ φ : AddChar A M) (a : A)
  statement: (ψ + φ) a = ψ a * φ a
  proof: rfl

中文:
引理 add_apply
  条件: (ψ φ : AddChar A M) (a : A)
  结论: (ψ + φ) a = ψ a * φ a
  证明: rfl
-/
@[simp] lemma add_apply (ψ φ : AddChar A M) (a : A) : (ψ + φ) a = ψ a * φ a := rfl
/--
lemma `pow_apply` / 引理 `pow_apply`

English:
lemma pow_apply
  given: (ψ : AddChar A M) (n : Nat) (a : A)
  statement: (ψ ^ n) a = (ψ a) ^ n
  proof: rfl

中文:
引理 pow_apply
  条件: (ψ : AddChar A M) (n : 自然数) (a : A)
  结论: (ψ ^ n) a = (ψ a) ^ n
  证明: rfl
-/
@[simp] lemma pow_apply (ψ : AddChar A M) (n : Nat) (a : A) : (ψ ^ n) a = (ψ a) ^ n := rfl
/--
lemma `nsmul_apply` / 引理 `nsmul_apply`

English:
lemma nsmul_apply
  given: (ψ : AddChar A M) (n : Nat) (a : A)
  statement: (n • ψ) a = (ψ a) ^ n
  proof: rfl

中文:
引理 nsmul_apply
  条件: (ψ : AddChar A M) (n : 自然数) (a : A)
  结论: (n • ψ) a = (ψ a) ^ n
  证明: rfl
-/
@[simp] lemma nsmul_apply (ψ : AddChar A M) (n : Nat) (a : A) : (n • ψ) a = (ψ a) ^ n := rfl

/--
lemma `prod_apply` / 引理 `prod_apply`

English:
lemma prod_apply
  given: (s : Finset ι) (ψ : ι -> AddChar A M) (a : A)
  proof: by rw [coe_prod, Finset.prod_apply]

中文:
引理 prod_apply
  条件: (s : Finset ι) (ψ : ι -> AddChar A M) (a : A)
  证明: by rw [coe_prod, Finset.prod_apply]

Depends on / 依赖: Finset, Finset.prod_apply, coe_prod, prod_apply
-/
lemma prod_apply (s : Finset ι) (ψ : ι -> AddChar A M) (a : A) :
    (∏ i in s, ψ i) a = ∏ i in s, ψ i a := by rw [coe_prod, Finset.prod_apply]

/--
lemma `sum_apply` / 引理 `sum_apply`

English:
lemma sum_apply
  given: (s : Finset ι) (ψ : ι -> AddChar A M) (a : A)
  proof: by rw [coe_sum, Finset.prod_apply]

中文:
引理 sum_apply
  条件: (s : Finset ι) (ψ : ι -> AddChar A M) (a : A)
  证明: by rw [coe_sum, Finset.prod_apply]

Depends on / 依赖: Finset, Finset.prod_apply, coe_sum, prod_apply
-/
lemma sum_apply (s : Finset ι) (ψ : ι -> AddChar A M) (a : A) :
    (∑ i in s, ψ i) a = ∏ i in s, ψ i a := by rw [coe_sum, Finset.prod_apply]

/--
lemma `mul_eq_add` / 引理 `mul_eq_add`

English:
lemma mul_eq_add
  given: (ψ χ : AddChar A M)
  statement: ψ * χ = ψ + χ
  proof: rfl

中文:
引理 mul_eq_add
  条件: (ψ χ : AddChar A M)
  结论: ψ * χ = ψ + χ
  证明: rfl
-/
lemma mul_eq_add (ψ χ : AddChar A M) : ψ * χ = ψ + χ := rfl
/--
lemma `pow_eq_nsmul` / 引理 `pow_eq_nsmul`

English:
lemma pow_eq_nsmul
  given: (ψ : AddChar A M) (n : Nat)
  statement: ψ ^ n = n • ψ
  proof: rfl

中文:
引理 pow_eq_nsmul
  条件: (ψ : AddChar A M) (n : 自然数)
  结论: ψ ^ n = n • ψ
  证明: rfl
-/
lemma pow_eq_nsmul (ψ : AddChar A M) (n : Nat) : ψ ^ n = n • ψ := rfl
/--
lemma `prod_eq_sum` / 引理 `prod_eq_sum`

English:
lemma prod_eq_sum
  given: (s : Finset ι) (ψ : ι -> AddChar A M)
  statement: ∏ i in s, ψ i = ∑ i in s, ψ i
  proof: rfl

中文:
引理 prod_eq_sum
  条件: (s : Finset ι) (ψ : ι -> AddChar A M)
  结论: ∏ i in s, ψ i = ∑ i in s, ψ i
  证明: rfl
-/
lemma prod_eq_sum (s : Finset ι) (ψ : ι -> AddChar A M) : ∏ i in s, ψ i = ∑ i in s, ψ i := rfl

/--
lemma `toMonoidHomEquiv_add` / 引理 `toMonoidHomEquiv_add`

English:
lemma toMonoidHomEquiv_add
  given: (ψ φ : AddChar A M)
  proof: rfl

中文:
引理 toMonoidHomEquiv_add
  条件: (ψ φ : AddChar A M)
  证明: rfl
-/
@[simp] lemma toMonoidHomEquiv_add (ψ φ : AddChar A M) :
    toMonoidHomEquiv (ψ + φ) = toMonoidHomEquiv ψ * toMonoidHomEquiv φ := rfl
/--
lemma `toMonoidHomEquiv_symm_mul` / 引理 `toMonoidHomEquiv_symm_mul`

English:
lemma toMonoidHomEquiv_symm_mul
  given: (ψ φ : Multiplicative A ->* M)
  proof: rfl

中文:
引理 toMonoidHomEquiv_symm_mul
  条件: (ψ φ : Multiplicative A ->* M)
  证明: rfl
-/
@[simp] lemma toMonoidHomEquiv_symm_mul (ψ φ : Multiplicative A ->* M) :
    toMonoidHomEquiv.symm (ψ * φ) = toMonoidHomEquiv.symm ψ + toMonoidHomEquiv.symm φ := rfl

/--
Definition of `toMonoidHomMulEquiv` / `toMonoidHomMulEquiv` 的定义

English:
definition toMonoidHomMulEquiv
  signature: : AddChar A M ≃* (Multiplicative A ->* M)
  body: { toMonoidHomEquiv with map_mul' := fun φ ψ => by rfl }

中文:
定义 toMonoidHomMulEquiv
  签名: : AddChar A M ≃* (Multiplicative A ->* M)
  定义体: { toMonoidHomEquiv with map_mul' := fun φ ψ => by rfl }

Depends on / 依赖: map_mul, toMonoidHomEquiv
-/
def toMonoidHomMulEquiv : AddChar A M ≃* (Multiplicative A ->* M) :=
  { toMonoidHomEquiv with map_mul' := fun φ ψ => by rfl }

/--
Definition of `toAddMonoidAddEquiv` / `toAddMonoidAddEquiv` 的定义

English:
definition toAddMonoidAddEquiv
  signature: : Additive (AddChar A M) ≃+ (A ->+ Additive M)
  body: { toAddMonoidHomEquiv with map_add' := fun φ ψ => by rfl }

中文:
定义 toAddMonoidAddEquiv
  签名: : Additive (AddChar A M) ≃+ (A ->+ Additive M)
  定义体: { toAddMonoidHomEquiv with map_add' := fun φ ψ => by rfl }

Depends on / 依赖: map_add, toAddMonoidHomEquiv
-/
def toAddMonoidAddEquiv : Additive (AddChar A M) ≃+ (A ->+ Additive M) :=
  { toAddMonoidHomEquiv with map_add' := fun φ ψ => by rfl }

/--
Definition of `doubleDualEmb` / `doubleDualEmb` 的定义

English:
definition doubleDualEmb
  signature: : A ->+ AddChar (AddChar A M) M where
  body: { toFun := fun ψ => ψ a
               map_zero_eq_one' := by simp
               map_add_eq_mul' := by simp }
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp [map_add_eq_mul]

中文:
定义 doubleDualEmb
  签名: : A ->+ AddChar (AddChar A M) M where
  定义体: { toFun := fun ψ => ψ a
               map_zero_eq_one' := by simp
               map_add_eq_mul' := by simp }
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp [map_add_eq_mul]
-/
def doubleDualEmb : A ->+ AddChar (AddChar A M) M where
  toFun a := { toFun := fun ψ => ψ a
               map_zero_eq_one' := by simp
               map_add_eq_mul' := by simp }
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp [map_add_eq_mul]

/--
lemma `doubleDualEmb_apply` / 引理 `doubleDualEmb_apply`

English:
lemma doubleDualEmb_apply
  given: (a : A) (ψ : AddChar A M)
  statement: doubleDualEmb a ψ = ψ a
  proof: rfl

中文:
引理 doubleDualEmb_apply
  条件: (a : A) (ψ : AddChar A M)
  结论: doubleDualEmb a ψ = ψ a
  证明: rfl
-/
@[simp] lemma doubleDualEmb_apply (a : A) (ψ : AddChar A M) : doubleDualEmb a ψ = ψ a := rfl

end toCommMonoid

section CommSemiring
variable {A R : Type*} [AddGroup A] [Fintype A] [CommSemiring R] [IsDomain R]
  {ψ : AddChar A R}

/--
lemma `sum_eq_ite` / 引理 `sum_eq_ite`

English:
lemma sum_eq_ite
  given: (ψ : AddChar A R) [Decidable (ψ = 0)]
  proof: by
  split_ifs with h
  · simp [h]
  obtain ⟨x, hx⟩ := ne_one_iff.1 h
  refine eq_zero_of_mul_eq_self_left hx ?_
  rw [Finset.mul_sum]
  exact Fintype.sum_equiv (Equiv.addLeft x) _ _ fun y => (map_add_eq_mul ..).symm

中文:
引理 sum_eq_ite
  条件: (ψ : AddChar A R) [Decidable (ψ = 0)]
  证明: by
  split_ifs with h
  · simp [h]
  obtain ⟨x, hx⟩ := ne_one_iff.1 h
  refine eq_zero_of_mul_eq_self_left hx ?_
  rw [Finset.mul_sum]
  exact Fintype.sum_equiv (Equiv.addLeft x) _ _ fun y => (map_add_eq_mul ..).symm

Depends on / 依赖: Equiv.addLeft, Finset, Finset.mul_sum, Fintype, Fintype.sum_equiv, addLeft, eq_zero_of_mul_eq_self_left, map_add_eq_mul, mul_sum, ne_one_iff, split_ifs, sum_equiv
-/
lemma sum_eq_ite (ψ : AddChar A R) [Decidable (ψ = 0)] :
    ∑ a, ψ a = if ψ = 0 then ↑(card A) else 0 := by
  split_ifs with h
  · simp [h]
  obtain ⟨x, hx⟩ := ne_one_iff.1 h
  refine eq_zero_of_mul_eq_self_left hx ?_
  rw [Finset.mul_sum]
  exact Fintype.sum_equiv (Equiv.addLeft x) _ _ fun y => (map_add_eq_mul ..).symm

variable [CharZero R]

/--
lemma `sum_eq_zero_iff_ne_zero` / 引理 `sum_eq_zero_iff_ne_zero`

English:
lemma sum_eq_zero_iff_ne_zero
  statement: ∑ x, ψ x = 0 ↔ ψ != 0
  proof: by
  rw [sum_eq_ite]; rw [Ne.ite_eq_right_iff]; exact Nat.cast_ne_zero.2 Fintype.card_ne_zero

中文:
引理 sum_eq_zero_iff_ne_zero
  结论: ∑ x, ψ x = 0 ↔ ψ != 0
  证明: by
  rw [sum_eq_ite]; rw [Ne.ite_eq_right_iff]; exact Nat.cast_ne_zero.2 Fintype.card_ne_zero

Depends on / 依赖: Fintype, Fintype.card_ne_zero, Nat.cast_ne_zero, Ne.ite_eq_right_iff, card_ne_zero, cast_ne_zero, ite_eq_right_iff, sum_eq_ite
-/
lemma sum_eq_zero_iff_ne_zero : ∑ x, ψ x = 0 ↔ ψ != 0 := by
  rw [sum_eq_ite]; rw [Ne.ite_eq_right_iff]; exact Nat.cast_ne_zero.2 Fintype.card_ne_zero

/--
lemma `sum_ne_zero_iff_eq_zero` / 引理 `sum_ne_zero_iff_eq_zero`

English:
lemma sum_ne_zero_iff_eq_zero
  statement: ∑ x, ψ x != 0 ↔ ψ = 0
  proof: sum_eq_zero_iff_ne_zero.not_left

中文:
引理 sum_ne_zero_iff_eq_zero
  结论: ∑ x, ψ x != 0 ↔ ψ = 0
  证明: sum_eq_zero_iff_ne_zero.not_left

Depends on / 依赖: not_left, sum_eq_zero_iff_ne_zero, sum_eq_zero_iff_ne_zero.not_left
-/
lemma sum_ne_zero_iff_eq_zero : ∑ x, ψ x != 0 ↔ ψ = 0 := sum_eq_zero_iff_ne_zero.not_left

end CommSemiring

/-!
## Additive characters of additive abelian groups
-/
section fromAddCommGroup

variable {A M : Type*} [AddCommGroup A] [CommMonoid M]

/--
Instance `instCommGroup` / 实例 `instCommGroup`

English:
instance instCommGroup
  signature: : CommGroup (AddChar A M) where
  body: ψ.compAddMonoidHom negAddMonoidHom
  inv_mul_cancel ψ := by ext1 x; simp [negAddMonoidHom, ← map_add_eq_mul]

中文:
实例 instCommGroup
  签名: : CommGroup (AddChar A M) where
  定义体: ψ.compAddMonoidHom negAddMonoidHom
  inv_mul_cancel ψ := by ext1 x; simp [negAddMonoidHom, ← map_add_eq_mul]

Depends on / 依赖: compAddMonoidHom, negAddMonoidHom
-/
instance instCommGroup : CommGroup (AddChar A M) where
  inv ψ := ψ.compAddMonoidHom negAddMonoidHom
  inv_mul_cancel ψ := by ext1 x; simp [negAddMonoidHom, ← map_add_eq_mul]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (AddChar A M)
  body: inferInstanceAs AddCommGroup (Additive (AddChar A M))

中文:
实例 :
  签名: AddCommGroup (AddChar A M)
  定义体: inferInstanceAs AddCommGroup (Additive (AddChar A M))

Depends on / 依赖: AddChar, AddCommGroup, Additive
-/
instance : AddCommGroup (AddChar A M) := inferInstanceAs AddCommGroup (Additive (AddChar A M))

/--
lemma `inv_apply` / 引理 `inv_apply`

English:
lemma inv_apply
  given: (ψ : AddChar A M) (a : A)
  statement: ψ⁻¹ a = ψ (-a)
  proof: rfl

中文:
引理 inv_apply
  条件: (ψ : AddChar A M) (a : A)
  结论: ψ⁻¹ a = ψ (-a)
  证明: rfl
-/
@[simp] lemma inv_apply (ψ : AddChar A M) (a : A) : ψ⁻¹ a = ψ (-a) := rfl
/--
lemma `neg_apply` / 引理 `neg_apply`

English:
lemma neg_apply
  given: (ψ : AddChar A M) (a : A)
  statement: (-ψ) a = ψ (-a)
  proof: rfl

中文:
引理 neg_apply
  条件: (ψ : AddChar A M) (a : A)
  结论: (-ψ) a = ψ (-a)
  证明: rfl
-/
@[simp] lemma neg_apply (ψ : AddChar A M) (a : A) : (-ψ) a = ψ (-a) := rfl
/--
lemma `div_apply` / 引理 `div_apply`

English:
lemma div_apply
  given: (ψ χ : AddChar A M) (a : A)
  statement: (ψ / χ) a = ψ a * χ (-a)
  proof: rfl

中文:
引理 div_apply
  条件: (ψ χ : AddChar A M) (a : A)
  结论: (ψ / χ) a = ψ a * χ (-a)
  证明: rfl
-/
lemma div_apply (ψ χ : AddChar A M) (a : A) : (ψ / χ) a = ψ a * χ (-a) := rfl
/--
lemma `sub_apply` / 引理 `sub_apply`

English:
lemma sub_apply
  given: (ψ χ : AddChar A M) (a : A)
  statement: (ψ - χ) a = ψ a * χ (-a)
  proof: rfl

中文:
引理 sub_apply
  条件: (ψ χ : AddChar A M) (a : A)
  结论: (ψ - χ) a = ψ a * χ (-a)
  证明: rfl
-/
lemma sub_apply (ψ χ : AddChar A M) (a : A) : (ψ - χ) a = ψ a * χ (-a) := rfl

end fromAddCommGroup

section fromAddGrouptoCommMonoid

/--
lemma `val_isUnit` / 引理 `val_isUnit`

English:
lemma val_isUnit
  given: {A M} [AddGroup A] [Monoid M] (φ : AddChar A M) (a : A)
  statement: IsUnit (φ a)
  proof: IsUnit.map φ.toMonoidHom Group.isUnit (Multiplicative.ofAdd a)

中文:
引理 val_isUnit
  条件: {A M} [AddGroup A] [Monoid M] (φ : AddChar A M) (a : A)
  结论: IsUnit (φ a)
  证明: IsUnit.map φ.toMonoidHom Group.isUnit (Multiplicative.ofAdd a)

Depends on / 依赖: Group.isUnit, IsUnit, IsUnit.map, Multiplicative, Multiplicative.ofAdd, isUnit, toMonoidHom
-/
lemma val_isUnit {A M} [AddGroup A] [Monoid M] (φ : AddChar A M) (a : A) : IsUnit (φ a) :=
IsUnit.map φ.toMonoidHom Group.isUnit (Multiplicative.ofAdd a)

end fromAddGrouptoCommMonoid

section fromAddGrouptoDivisionMonoid

variable {A M : Type*} [AddGroup A] [DivisionMonoid M]

/--
lemma `map_neg_eq_inv` / 引理 `map_neg_eq_inv`

English:
lemma map_neg_eq_inv
  given: (ψ : AddChar A M) (a : A)
  statement: ψ (-a) = (ψ a)⁻¹
  proof: by
  apply eq_inv_of_mul_eq_one_left
  simp only [← map_add_eq_mul, neg_add_cancel, map_zero_eq_one]

中文:
引理 map_neg_eq_inv
  条件: (ψ : AddChar A M) (a : A)
  结论: ψ (-a) = (ψ a)⁻¹
  证明: by
  apply eq_inv_of_mul_eq_one_left
  simp only [← map_add_eq_mul, neg_add_cancel, map_zero_eq_one]

Depends on / 依赖: eq_inv_of_mul_eq_one_left, map_add_eq_mul, map_zero_eq_one, neg_add_cancel
-/
lemma map_neg_eq_inv (ψ : AddChar A M) (a : A) : ψ (-a) = (ψ a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  simp only [← map_add_eq_mul, neg_add_cancel, map_zero_eq_one]

/--
lemma `map_zsmul_eq_zpow` / 引理 `map_zsmul_eq_zpow`

English:
lemma map_zsmul_eq_zpow
  given: (ψ : AddChar A M) (n : Int) (a : A)
  statement: ψ (n • a) = (ψ a) ^ n
  proof: ψ.toMonoidHom.map_zpow a n

中文:
引理 map_zsmul_eq_zpow
  条件: (ψ : AddChar A M) (n : 整数) (a : A)
  结论: ψ (n • a) = (ψ a) ^ n
  证明: ψ.toMonoidHom.map_zpow a n

Depends on / 依赖: map_zpow, toMonoidHom, toMonoidHom.map_zpow
-/
lemma map_zsmul_eq_zpow (ψ : AddChar A M) (n : Int) (a : A) : ψ (n • a) = (ψ a) ^ n :=
  ψ.toMonoidHom.map_zpow a n

end fromAddGrouptoDivisionMonoid

section fromAddCommGrouptoDivisionCommMonoid
variable {A M : Type*} [AddCommGroup A] [DivisionCommMonoid M]

/--
lemma `inv_apply'` / 引理 `inv_apply'`

English:
lemma inv_apply'
  given: (ψ : AddChar A M) (a : A)
  statement: ψ⁻¹ a = (ψ a)⁻¹
  proof: by rw [inv_apply, map_neg_eq_inv]

中文:
引理 inv_apply'
  条件: (ψ : AddChar A M) (a : A)
  结论: ψ⁻¹ a = (ψ a)⁻¹
  证明: by rw [inv_apply, map_neg_eq_inv]

Depends on / 依赖: inv_apply, map_neg_eq_inv
-/
lemma inv_apply' (ψ : AddChar A M) (a : A) : ψ⁻¹ a = (ψ a)⁻¹ := by rw [inv_apply, map_neg_eq_inv]
/--
lemma `neg_apply'` / 引理 `neg_apply'`

English:
lemma neg_apply'
  given: (ψ : AddChar A M) (a : A)
  statement: (-ψ) a = (ψ a)⁻¹
  proof: map_neg_eq_inv _ _

中文:
引理 neg_apply'
  条件: (ψ : AddChar A M) (a : A)
  结论: (-ψ) a = (ψ a)⁻¹
  证明: map_neg_eq_inv _ _

Depends on / 依赖: map_neg_eq_inv
-/
lemma neg_apply' (ψ : AddChar A M) (a : A) : (-ψ) a = (ψ a)⁻¹ := map_neg_eq_inv _ _

/--
lemma `div_apply'` / 引理 `div_apply'`

English:
lemma div_apply'
  given: (ψ χ : AddChar A M) (a : A)
  statement: (ψ / χ) a = ψ a / χ a
  proof: by
  rw [div_apply]; rw [map_neg_eq_inv]; rw [div_eq_mul_inv]

中文:
引理 div_apply'
  条件: (ψ χ : AddChar A M) (a : A)
  结论: (ψ / χ) a = ψ a / χ a
  证明: by
  rw [div_apply]; rw [map_neg_eq_inv]; rw [div_eq_mul_inv]

Depends on / 依赖: div_apply, div_eq_mul_inv, map_neg_eq_inv
-/
lemma div_apply' (ψ χ : AddChar A M) (a : A) : (ψ / χ) a = ψ a / χ a := by
  rw [div_apply]; rw [map_neg_eq_inv]; rw [div_eq_mul_inv]

/--
lemma `sub_apply'` / 引理 `sub_apply'`

English:
lemma sub_apply'
  given: (ψ χ : AddChar A M) (a : A)
  statement: (ψ - χ) a = ψ a / χ a
  proof: by
  rw [sub_apply]; rw [map_neg_eq_inv]; rw [div_eq_mul_inv]

中文:
引理 sub_apply'
  条件: (ψ χ : AddChar A M) (a : A)
  结论: (ψ - χ) a = ψ a / χ a
  证明: by
  rw [sub_apply]; rw [map_neg_eq_inv]; rw [div_eq_mul_inv]

Depends on / 依赖: div_eq_mul_inv, map_neg_eq_inv, sub_apply
-/
lemma sub_apply' (ψ χ : AddChar A M) (a : A) : (ψ - χ) a = ψ a / χ a := by
  rw [sub_apply]; rw [map_neg_eq_inv]; rw [div_eq_mul_inv]

/--
lemma `zsmul_apply` / 引理 `zsmul_apply`

English:
lemma zsmul_apply
  given: (n : Int) (ψ : AddChar A M) (a : A)
  statement: (n • ψ) a = ψ a ^ n
  proof: by
  cases n <;> simp [-neg_apply, neg_apply']

中文:
引理 zsmul_apply
  条件: (n : 整数) (ψ : AddChar A M) (a : A)
  结论: (n • ψ) a = ψ a ^ n
  证明: by
  cases n <;> simp [-neg_apply, neg_apply']
-/
@[simp] lemma zsmul_apply (n : Int) (ψ : AddChar A M) (a : A) : (n • ψ) a = ψ a ^ n := by
  cases n <;> simp [-neg_apply, neg_apply']

/--
lemma `zpow_apply` / 引理 `zpow_apply`

English:
lemma zpow_apply
  given: (ψ : AddChar A M) (n : Int) (a : A)
  statement: (ψ ^ n) a = ψ a ^ n
  proof: zsmul_apply ..

中文:
引理 zpow_apply
  条件: (ψ : AddChar A M) (n : 整数) (a : A)
  结论: (ψ ^ n) a = ψ a ^ n
  证明: zsmul_apply ..
-/
@[simp] lemma zpow_apply (ψ : AddChar A M) (n : Int) (a : A) : (ψ ^ n) a = ψ a ^ n := zsmul_apply ..

/--
lemma `map_sub_eq_div` / 引理 `map_sub_eq_div`

English:
lemma map_sub_eq_div
  given: (ψ : AddChar A M) (a b : A)
  statement: ψ (a - b) = ψ a / ψ b
  proof: ψ.toMonoidHom.map_div _ _

中文:
引理 map_sub_eq_div
  条件: (ψ : AddChar A M) (a b : A)
  结论: ψ (a - b) = ψ a / ψ b
  证明: ψ.toMonoidHom.map_div _ _

Depends on / 依赖: map_div, toMonoidHom, toMonoidHom.map_div
-/
lemma map_sub_eq_div (ψ : AddChar A M) (a b : A) : ψ (a - b) = ψ a / ψ b :=
  ψ.toMonoidHom.map_div _ _

/--
lemma `injective_iff` / 引理 `injective_iff`

English:
lemma injective_iff
  given: {ψ : AddChar A M}
  statement: Injective ψ ↔ forall ⦃x⦄, ψ x = 1 -> x = 0
  proof: ψ.toMonoidHom.ker_eq_bot_iff.symm.trans eq_bot_iff

中文:
引理 injective_iff
  条件: {ψ : AddChar A M}
  结论: Injective ψ ↔ 对任意 ⦃x⦄, ψ x = 1 -> x = 0
  证明: ψ.toMonoidHom.ker_eq_bot_iff.symm.trans eq_bot_iff

Depends on / 依赖: eq_bot_iff, ker_eq_bot_iff, toMonoidHom, toMonoidHom.ker_eq_bot_iff.symm.trans
-/
lemma injective_iff {ψ : AddChar A M} : Injective ψ ↔ forall ⦃x⦄, ψ x = 1 -> x = 0 :=
  ψ.toMonoidHom.ker_eq_bot_iff.symm.trans eq_bot_iff

end fromAddCommGrouptoDivisionCommMonoid

section MonoidWithZero
variable {A M₀ : Type*} [AddGroup A] [MonoidWithZero M₀] [Nontrivial M₀]

/--
lemma `coe_ne_zero` / 引理 `coe_ne_zero`

English:
lemma coe_ne_zero
  given: (ψ : AddChar A M₀)
  statement: (ψ : A -> M₀) != 0
  proof: ne_iff.2 ⟨0, fun h => by simpa only [h, Pi.zero_apply, zero_ne_one] using map_zero_eq_one ψ⟩

中文:
引理 coe_ne_zero
  条件: (ψ : AddChar A M₀)
  结论: (ψ : A -> M₀) != 0
  证明: ne_iff.2 ⟨0, fun h => by simpa only [h, Pi.zero_apply, zero_ne_one] using map_zero_eq_one ψ⟩
-/
@[simp] lemma coe_ne_zero (ψ : AddChar A M₀) : (ψ : A -> M₀) != 0 :=
  ne_iff.2 ⟨0, fun h => by simpa only [h, Pi.zero_apply, zero_ne_one] using map_zero_eq_one ψ⟩

end MonoidWithZero

/-!
## Additive characters of rings
-/
section Ring

-- The domain and target of our additive characters. Now we restrict to a ring in the domain.
variable {R M : Type*} [Ring R] [CommMonoid M]

/--
Definition of `mulShift` / `mulShift` 的定义

English:
definition mulShift
  signature: (ψ : AddChar R M) (r : R)
  body: ψ.compAddMonoidHom (AddMonoidHom.mulLeft r)

中文:
定义 mulShift
  签名: (ψ : AddChar R M) (r : R)
  定义体: ψ.compAddMonoidHom (AddMonoidHom.mulLeft r)

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mulLeft, compAddMonoidHom, mulLeft
-/
def mulShift (ψ : AddChar R M) (r : R) : AddChar R M :=
  ψ.compAddMonoidHom (AddMonoidHom.mulLeft r)

/--
lemma `mulShift_apply` / 引理 `mulShift_apply`

English:
lemma mulShift_apply
  given: {ψ : AddChar R M} {r : R} {x : R}
  statement: mulShift ψ r x = ψ (r * x)
  proof: rfl

中文:
引理 mulShift_apply
  条件: {ψ : AddChar R M} {r : R} {x : R}
  结论: mulShift ψ r x = ψ (r * x)
  证明: rfl
-/
@[simp] lemma mulShift_apply {ψ : AddChar R M} {r : R} {x : R} : mulShift ψ r x = ψ (r * x) :=
  rfl

/--
theorem `inv_mulShift` / 定理 `inv_mulShift`

English:
theorem inv_mulShift
  given: (ψ : AddChar R M)
  statement: ψ⁻¹ = mulShift ψ (-1)
  proof: by
  ext
  rw [inv_apply]; rw [mulShift_apply]; rw [neg_mul]; rw [one_mul]

中文:
定理 inv_mulShift
  条件: (ψ : AddChar R M)
  结论: ψ⁻¹ = mulShift ψ (-1)
  证明: by
  ext
  rw [inv_apply]; rw [mulShift_apply]; rw [neg_mul]; rw [one_mul]

Depends on / 依赖: inv_apply, mulShift_apply, neg_mul, one_mul
-/
theorem inv_mulShift (ψ : AddChar R M) : ψ⁻¹ = mulShift ψ (-1) := by
  ext
  rw [inv_apply]; rw [mulShift_apply]; rw [neg_mul]; rw [one_mul]

/--
theorem `mulShift_spec'` / 定理 `mulShift_spec'`

English:
theorem mulShift_spec'
  given: (ψ : AddChar R M) (n : Nat) (x : R)
  statement: mulShift ψ n x = ψ x ^ n
  proof: by
  rw [mulShift_apply]; rw [← nsmul_eq_mul]; rw [map_nsmul_eq_pow]

中文:
定理 mulShift_spec'
  条件: (ψ : AddChar R M) (n : 自然数) (x : R)
  结论: mulShift ψ n x = ψ x ^ n
  证明: by
  rw [mulShift_apply]; rw [← nsmul_eq_mul]; rw [map_nsmul_eq_pow]

Depends on / 依赖: map_nsmul_eq_pow, mulShift_apply, nsmul_eq_mul
-/
theorem mulShift_spec' (ψ : AddChar R M) (n : Nat) (x : R) : mulShift ψ n x = ψ x ^ n := by
  rw [mulShift_apply]; rw [← nsmul_eq_mul]; rw [map_nsmul_eq_pow]

/--
theorem `pow_mulShift` / 定理 `pow_mulShift`

English:
theorem pow_mulShift
  given: (ψ : AddChar R M) (n : Nat)
  statement: ψ ^ n = mulShift ψ n
  proof: by
  ext x
  rw [pow_apply]; rw [← mulShift_spec']

中文:
定理 pow_mulShift
  条件: (ψ : AddChar R M) (n : 自然数)
  结论: ψ ^ n = mulShift ψ n
  证明: by
  ext x
  rw [pow_apply]; rw [← mulShift_spec']

Depends on / 依赖: mulShift_spec, pow_apply
-/
theorem pow_mulShift (ψ : AddChar R M) (n : Nat) : ψ ^ n = mulShift ψ n := by
  ext x
  rw [pow_apply]; rw [← mulShift_spec']

/--
theorem `mulShift_mul` / 定理 `mulShift_mul`

English:
theorem mulShift_mul
  given: (ψ : AddChar R M) (r s : R)
  proof: by
  ext
  rw [mulShift_apply]; rw [right_distrib]; rw [map_add_eq_mul]; norm_cast

中文:
定理 mulShift_mul
  条件: (ψ : AddChar R M) (r s : R)
  证明: by
  ext
  rw [mulShift_apply]; rw [right_distrib]; rw [map_add_eq_mul]; norm_cast

Depends on / 依赖: map_add_eq_mul, mulShift_apply, right_distrib
-/
theorem mulShift_mul (ψ : AddChar R M) (r s : R) :
    mulShift ψ r * mulShift ψ s = mulShift ψ (r + s) := by
  ext
  rw [mulShift_apply]; rw [right_distrib]; rw [map_add_eq_mul]; norm_cast

/--
lemma `mulShift_mulShift` / 引理 `mulShift_mulShift`

English:
lemma mulShift_mulShift
  given: (ψ : AddChar R M) (r s : R)
  proof: by
  ext
  simp only [mulShift_apply, mul_assoc]

中文:
引理 mulShift_mulShift
  条件: (ψ : AddChar R M) (r s : R)
  证明: by
  ext
  simp only [mulShift_apply, mul_assoc]

Depends on / 依赖: mulShift_apply, mul_assoc
-/
lemma mulShift_mulShift (ψ : AddChar R M) (r s : R) :
    mulShift (mulShift ψ r) s = mulShift ψ (r * s) := by
  ext
  simp only [mulShift_apply, mul_assoc]

/-- `mulShift ψ 0` is the trivial character. -/
@[simp]
/--
theorem `mulShift_zero` / 定理 `mulShift_zero`

English:
theorem mulShift_zero
  given: (ψ : AddChar R M)
  statement: mulShift ψ 0 = 1
  proof: by
  ext; rw [mulShift_apply, zero_mul, map_zero_eq_one, one_apply]

@[simp]

中文:
定理 mulShift_zero
  条件: (ψ : AddChar R M)
  结论: mulShift ψ 0 = 1
  证明: by
  ext; rw [mulShift_apply, zero_mul, map_zero_eq_one, one_apply]

@[simp]

Depends on / 依赖: map_zero_eq_one, mulShift_apply, one_apply, zero_mul
-/
theorem mulShift_zero (ψ : AddChar R M) : mulShift ψ 0 = 1 := by
  ext; rw [mulShift_apply, zero_mul, map_zero_eq_one, one_apply]

@[simp]
/--
lemma `mulShift_one` / 引理 `mulShift_one`

English:
lemma mulShift_one
  given: (ψ : AddChar R M)
  statement: mulShift ψ 1 = ψ
  proof: by
  ext; rw [mulShift_apply, one_mul]

中文:
引理 mulShift_one
  条件: (ψ : AddChar R M)
  结论: mulShift ψ 1 = ψ
  证明: by
  ext; rw [mulShift_apply, one_mul]

Depends on / 依赖: mulShift_apply, one_mul
-/
lemma mulShift_one (ψ : AddChar R M) : mulShift ψ 1 = ψ := by
  ext; rw [mulShift_apply, one_mul]

/--
lemma `mulShift_unit_eq_one_iff` / 引理 `mulShift_unit_eq_one_iff`

English:
lemma mulShift_unit_eq_one_iff
  given: (ψ : AddChar R M) {u : R} (hu : IsUnit u)
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · ext1 y
    rw [show y = u * (hu.unit⁻¹ * y) by rw [← mul_assoc]; rw [IsUnit.mul_val_inv]; rw [one_mul]]
    simpa only [mulShift_apply] using! DFunLike.ext_iff.mp h (hu.unit⁻¹ * y)
  · solve_by_elim

中文:
引理 mulShift_unit_eq_one_iff
  条件: (ψ : AddChar R M) {u : R} (hu : IsUnit u)
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · ext1 y
    rw [show y = u * (hu.unit⁻¹ * y) by rw [← mul_assoc]; rw [IsUnit.mul_val_inv]; rw [one_mul]]
    simpa only [mulShift_apply] using! DFunLike.ext_iff.mp h (hu.unit⁻¹ * y)
  · solve_by_elim

Depends on / 依赖: DFunLike, DFunLike.ext_iff.mp, IsUnit, IsUnit.mul_val_inv, ext_iff, hu.unit, mulShift_apply, mul_assoc, mul_val_inv, one_mul, solve_by_elim
-/
lemma mulShift_unit_eq_one_iff (ψ : AddChar R M) {u : R} (hu : IsUnit u) :
    ψ.mulShift u = 1 ↔ ψ = 1 := by
  refine ⟨fun h => ?_, ?_⟩
  · ext1 y
    rw [show y = u * (hu.unit⁻¹ * y) by rw [← mul_assoc]; rw [IsUnit.mul_val_inv]; rw [one_mul]]
    simpa only [mulShift_apply] using! DFunLike.ext_iff.mp h (hu.unit⁻¹ * y)
  · solve_by_elim

end Ring

end AddChar
