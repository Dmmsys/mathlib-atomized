/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Tactic.Spread

/-!
# Additive and multiplicative equivalences associated to `Multiplicative` and `Additive`.
-/

@[expose] public section

assert_not_exists Finite Fintype

variable {ι G H : Type*}

/-- Reinterpret `G ≃+ H` as `Multiplicative G ≃* Multiplicative H`. -/
@[simps]
/-
**AddEquiv.toMultiplicative** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddEquiv.toMultiplicative [AddZeroClass G] [AddZeroClass H] : G ≃+ H ≃ (Mu
ltiplicative G ≃* Multiplicative H) where toFun f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Reinterpret `G ≃+ H` as `Multiplicative G ≃* Multiplicative H`.
-/
def AddEquiv.toMultiplicative [AddZeroClass G] [AddZeroClass H] :
    G ≃+ H ≃ (Multiplicative G ≃* Multiplicative H) where
  toFun f :=
  { toFun := AddMonoidHom.toMultiplicative f.toAddMonoidHom
    invFun := AddMonoidHom.toMultiplicative f.symm.toAddMonoidHom
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_mul' := map_add f }
  invFun f :=
  { toFun := AddMonoidHom.toMultiplicative.symm f.toMonoidHom
    invFun := AddMonoidHom.toMultiplicative.symm f.symm.toMonoidHom
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_add' := map_mul f }

/-- Reinterpret `G ≃* H` as `Additive G ≃+ Additive H`. -/
@[simps]
/-
**MulEquiv.toAdditive** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulEquiv.toAdditive [MulOneClass G] [MulOneClass H] : G ≃* H ≃ (Additive G
 ≃+ Additive H) where toFun f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Reinterpret `G ≃* H` as `Additive G ≃+ Additive H`.
-/
def MulEquiv.toAdditive [MulOneClass G] [MulOneClass H] :
    G ≃* H ≃ (Additive G ≃+ Additive H) where
  toFun f :=
  { toFun := MonoidHom.toAdditive f.toMonoidHom
    invFun := MonoidHom.toAdditive f.symm.toMonoidHom
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_add' := map_mul f }
  invFun f :=
  { toFun := MonoidHom.toAdditive.symm f.toAddMonoidHom
    invFun := MonoidHom.toAdditive.symm f.symm.toAddMonoidHom
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_mul' := map_add f }

/-- Reinterpret `Additive G ≃+ H` as `G ≃* Multiplicative H`. -/
@[simps]
/-
**AddEquiv.toMultiplicativeRight** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddEquiv.toMultiplicativeRight [MulOneClass G] [AddZeroClass H] : Additive
 G ≃+ H ≃ (G ≃* Multiplicative H) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret `Additive G ≃+ H` as `G ≃* Multiplicative H`.
-/
def AddEquiv.toMultiplicativeRight [MulOneClass G] [AddZeroClass H] :
    Additive G ≃+ H ≃ (G ≃* Multiplicative H) where
  toFun f :=
  { toFun := f.toAddMonoidHom.toMultiplicativeRight
    invFun := f.symm.toAddMonoidHom.toMultiplicativeLeft
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_mul' := map_add f }
  invFun f :=
  { toFun := f.toMonoidHom.toAdditiveLeft
    invFun := f.symm.toMonoidHom.toAdditiveRight
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_add' := map_mul f }

/-- Reinterpret `G ≃* Multiplicative H` as `Additive G ≃+ H`. -/
/-
**MulEquiv.toAdditiveLeft** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：MulEquiv.toAdditiveLeft [MulOneClass G] [AddZeroClass H] : G ≃* Multiplica
tive H ≃ (Additive G ≃+ H)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Reinterpret `G ≃* Multiplicative H` as `Additive G ≃+ H`.
-/
abbrev MulEquiv.toAdditiveLeft [MulOneClass G] [AddZeroClass H] :
    G ≃* Multiplicative H ≃ (Additive G ≃+ H) :=
  AddEquiv.toMultiplicativeRight.symm

/-- Reinterpret `G ≃+ Additive H` as `Multiplicative G ≃* H`. -/
@[simps]
/-
**AddEquiv.toMultiplicativeLeft** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddEquiv.toMultiplicativeLeft [AddZeroClass G] [MulOneClass H] : G ≃+ Addi
tive H ≃ (Multiplicative G ≃* H) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret `G ≃+ Additive H` as `Multiplicative G ≃* H`.
-/
def AddEquiv.toMultiplicativeLeft [AddZeroClass G] [MulOneClass H] :
    G ≃+ Additive H ≃ (Multiplicative G ≃* H) where
  toFun f :=
  { toFun := f.toAddMonoidHom.toMultiplicativeLeft
    invFun := f.symm.toAddMonoidHom.toMultiplicativeRight
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_mul' := map_add f }
  invFun f :=
  { toFun := f.toMonoidHom.toAdditiveRight
    invFun := f.symm.toMonoidHom.toAdditiveLeft
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_add' := map_mul f }

/-- Reinterpret `Multiplicative G ≃* H` as `G ≃+ Additive H` as. -/
/-
**MulEquiv.toAdditiveRight** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：MulEquiv.toAdditiveRight [AddZeroClass G] [MulOneClass H] : Multiplicative
 G ≃* H ≃ (G ≃+ Additive H)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Reinterpret `Multiplicative G ≃* H` as `G ≃+ Additive H` as.
-/
abbrev MulEquiv.toAdditiveRight [AddZeroClass G] [MulOneClass H] :
    Multiplicative G ≃* H ≃ (G ≃+ Additive H) :=
  AddEquiv.toMultiplicativeLeft.symm

/-- The multiplicative version of an additivized monoid is mul-equivalent to itself. -/
@[simps! apply symm_apply]
/-
**MulEquiv.toMultiplicative_toAdditive** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulEquiv.toMultiplicative_toAdditive [MulOneClass G] : Multiplicative (Add
itive G) ≃* G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplicative version of an additivized monoid is mul-equivalent to itself.
-/
def MulEquiv.toMultiplicative_toAdditive [MulOneClass G] :
    Multiplicative (Additive G) ≃* G :=
  AddEquiv.toMultiplicativeLeft <| MulEquiv.toAdditive (.refl _)

/-- The additive version of a multiplicativized additive monoid is add-equivalent to itself. -/
@[simps! apply symm_apply]
/-
**AddEquiv.toAdditive_toMultiplicative** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddEquiv.toAdditive_toMultiplicative [AddZeroClass G] : Additive (Multipli
cative G) ≃+ G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive version of a multiplicativized additive monoid is add-equivalent to
 itself.
-/
def AddEquiv.toAdditive_toMultiplicative [AddZeroClass G] :
    Additive (Multiplicative G) ≃+ G :=
  MulEquiv.toAdditiveLeft <| AddEquiv.toMultiplicative (.refl _)

/-- Multiplicative equivalence between multiplicative endomorphisms of a `MulOneClass` `M`
and additive endomorphisms of `Additive M`. -/
/-
**monoidEndToAdditive** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：(M : Type u_4) → [inst : MulOneClass M] → Monoid.End M ≃* AddMonoid.End (A
dditive M)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplicative equivalence between multiplicative endomorphisms of a `MulOneClas
s` `M`
and additive endomorphisms of `Additive M`.
-/
@[simps!] def monoidEndToAdditive (M : Type*) [MulOneClass M] :
    Monoid.End M ≃* AddMonoid.End (Additive M) :=
  { MonoidHom.toAdditive with
    map_mul' := fun _ _ => rfl }

/-- Multiplicative equivalence between additive endomorphisms of an `AddZeroClass` `A`
and multiplicative endomorphisms of `Multiplicative A`. -/
/-
**addMonoidEndToMultiplicative** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：(A : Type u_4) → [inst : AddZeroClass A] → AddMonoid.End A ≃* Monoid.End (
Multiplicative A)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplicative equivalence between additive endomorphisms of an `AddZeroClass` `
A`
and multiplicative endomorphisms of `Multiplicative A`.
-/
@[simps!] def addMonoidEndToMultiplicative (A : Type*) [AddZeroClass A] :
    AddMonoid.End A ≃* Monoid.End (Multiplicative A) :=
  { AddMonoidHom.toMultiplicative with
    map_mul' := fun _ _ => rfl }

/-- `Multiplicative (∀ i : ι, K i)` is equivalent to `∀ i : ι, Multiplicative (K i)`. -/
@[simps]
/-
**MulEquiv.piMultiplicative** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulEquiv.piMultiplicative (K : ι -> Type*) [forall i, Add (K i)] : Multipl
icative (forall i : ι, K i) ≃* (forall i : ι, Multiplicative (K i)) where toFun 
x
参数：K : ι -> Type*；K i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Multiplicative (∀ i : ι, K i)` is equivalent to `∀ i : ι, Multiplicative (K i)`
.
-/
def MulEquiv.piMultiplicative (K : ι → Type*) [∀ i, Add (K i)] :
    Multiplicative (∀ i : ι, K i) ≃* (∀ i : ι, Multiplicative (K i)) where
  toFun x := fun i ↦ Multiplicative.ofAdd <| x.toAdd i
  invFun x := Multiplicative.ofAdd fun i ↦ (x i).toAdd
  map_mul' _ _ := rfl

variable (ι) (G) in
/-- `Multiplicative (ι → G)` is equivalent to `ι → Multiplicative G`. -/
/-
**MulEquiv.funMultiplicative** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：MulEquiv.funMultiplicative [Add G] : Multiplicative (ι -> G) ≃* (ι -> Mult
iplicative G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Multiplicative (ι → G)` is equivalent to `ι → Multiplicative G`.
-/
abbrev MulEquiv.funMultiplicative [Add G] :
    Multiplicative (ι → G) ≃* (ι → Multiplicative G) :=
  MulEquiv.piMultiplicative fun _ ↦ G

/-- `Additive (∀ i : ι, K i)` is equivalent to `∀ i : ι, Additive (K i)`. -/
@[simps]
/-
**AddEquiv.piAdditive** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddEquiv.piAdditive (K : ι -> Type*) [forall i, Mul (K i)] : Additive (for
all i : ι, K i) ≃+ (forall i : ι, Additive (K i)) where toFun x
参数：K : ι -> Type*；K i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Additive (∀ i : ι, K i)` is equivalent to `∀ i : ι, Additive (K i)`.
-/
def AddEquiv.piAdditive (K : ι → Type*) [∀ i, Mul (K i)] :
    Additive (∀ i : ι, K i) ≃+ (∀ i : ι, Additive (K i)) where
  toFun x := fun i ↦ Additive.ofMul <| x.toMul i
  invFun x := Additive.ofMul fun i ↦ (x i).toMul
  map_add' _ _ := rfl

variable (ι) (G) in
/-- `Additive (ι → G)` is equivalent to `ι → Additive G`. -/
/-
**AddEquiv.funAdditive** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：AddEquiv.funAdditive [Mul G] : Additive (ι -> G) ≃+ (ι -> Additive G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Additive (ι → G)` is equivalent to `ι → Additive G`.
-/
abbrev AddEquiv.funAdditive [Mul G] :
    Additive (ι → G) ≃+ (ι → Additive G) :=
  AddEquiv.piAdditive fun _ ↦ G

section

variable (G) (H)

/-- `Additive (Multiplicative G)` is just `G`. -/
@[simps!]
/-
**AddEquiv.additiveMultiplicative** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddEquiv.additiveMultiplicative [AddZeroClass G] : Additive (Multiplicativ
e G) ≃+ G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Additive (Multiplicative G)` is just `G`.
-/
def AddEquiv.additiveMultiplicative [AddZeroClass G] : Additive (Multiplicative G) ≃+ G :=
  MulEquiv.toAdditiveLeft (MulEquiv.refl (Multiplicative G))

/-- `Multiplicative (Additive H)` is just `H`. -/
@[simps!]
/-
**MulEquiv.multiplicativeAdditive** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulEquiv.multiplicativeAdditive [MulOneClass H] : Multiplicative (Additive
 H) ≃* H
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Multiplicative (Additive H)` is just `H`.
-/
def MulEquiv.multiplicativeAdditive [MulOneClass H] : Multiplicative (Additive H) ≃* H :=
  AddEquiv.toMultiplicativeLeft (AddEquiv.refl (Additive H))

/-- `Multiplicative (G × H)` is equivalent to `Multiplicative G × Multiplicative H`. -/
@[simps]
/-
**MulEquiv.prodMultiplicative** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulEquiv.prodMultiplicative [Add G] [Add H] : Multiplicative (G × H) ≃* Mu
ltiplicative G × Multiplicative H where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Multiplicative (G × H)` is equivalent to `Multiplicative G × Multiplicative H`.
-/
def MulEquiv.prodMultiplicative [Add G] [Add H] :
    Multiplicative (G × H) ≃* Multiplicative G × Multiplicative H where
  toFun x := (Multiplicative.ofAdd x.toAdd.1,
    Multiplicative.ofAdd x.toAdd.2)
  invFun := fun (x, y) ↦ Multiplicative.ofAdd (x.toAdd, y.toAdd)
  map_mul' _ _ := rfl

/-- `Additive (G × H)` is equivalent to `Additive G × Additive H`. -/
@[simps]
/-
**AddEquiv.prodAdditive** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddEquiv.prodAdditive [Mul G] [Mul H] : Additive (G × H) ≃+ Additive G × A
dditive H where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Additive (G × H)` is equivalent to `Additive G × Additive H`.
-/
def AddEquiv.prodAdditive [Mul G] [Mul H] :
    Additive (G × H) ≃+ Additive G × Additive H where
  toFun x := (Additive.ofMul x.toMul.1,
    Additive.ofMul x.toMul.2)
  invFun := fun (x, y) ↦ Additive.ofMul (x.toMul, y.toMul)
  map_add' _ _ := rfl

end

section End

variable {M : Type*}

/-- `Monoid.End M` is equivalent to `AddMonoid.End (Additive M)`. -/
@[simps! apply]
/-
**MulEquiv.Monoid.End** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulEquiv.Monoid.End [Monoid M] : Monoid.End M ≃* AddMonoid.End (Additive M
) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Monoid.End M` is equivalent to `AddMonoid.End (Additive M)`.
-/
def MulEquiv.Monoid.End [Monoid M] : Monoid.End M ≃* AddMonoid.End (Additive M) where
  __ := MonoidHom.toAdditive
  map_mul' := fun _ _ ↦ rfl

/-- `AddMonoid.End M` is equivalent to `Monoid.End (Multiplicative M)`. -/
@[simps! apply]
/-
**MulEquiv.AddMonoid.End** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulEquiv.AddMonoid.End [AddMonoid M] : AddMonoid.End M ≃* _root_.Monoid.En
d (Multiplicative M) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AddMonoid.End M` is equivalent to `Monoid.End (Multiplicative M)`.
-/
def MulEquiv.AddMonoid.End [AddMonoid M] :
    AddMonoid.End M ≃* _root_.Monoid.End (Multiplicative M) where
  __ := AddMonoidHom.toMultiplicative
  map_mul' := fun _ _ ↦ rfl

end End

