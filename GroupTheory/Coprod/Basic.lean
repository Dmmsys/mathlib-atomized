/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Submonoid.Membership
public import Mathlib.GroupTheory.Congruence.Basic

/-!
# Coproduct (free product) of two monoids or groups

In this file we define `Monoid.Coprod M N` (notation: `M ∗ N`)
to be the coproduct (a.k.a. free product) of two monoids.
The same type is used for the coproduct of two monoids and for the coproduct of two groups.

The coproduct `M ∗ N` has the following universal property:
for any monoid `P` and homomorphisms `f : M →* P`, `g : N →* P`,
there exists a unique homomorphism `fg : M ∗ N →* P`
such that `fg ∘ Monoid.Coprod.inl = f` and `fg ∘ Monoid.Coprod.inr = g`,
where `Monoid.Coprod.inl : M →* M ∗ N`
and `Monoid.Coprod.inr : N →* M ∗ N` are canonical embeddings.
This homomorphism `fg` is given by `Monoid.Coprod.lift f g`.

We also define some homomorphisms and isomorphisms about `M ∗ N`,
and provide additive versions of all definitions and theorems.

## Main definitions

### Types

* `Monoid.Coprod M N` (a.k.a. `M ∗ N`):
  the free product (a.k.a. coproduct) of two monoids `M` and `N`.
* `AddMonoid.Coprod M N` (no notation): the additive version of `Monoid.Coprod`.

In other sections, we only list multiplicative definitions.

### Instances

* `MulOneClass`, `Monoid`, and `Group` structures on the coproduct `M ∗ N`.

### Monoid homomorphisms

* `Monoid.Coprod.mk`: the projection `FreeMonoid (M ⊕ N) →* M ∗ N`.

* `Monoid.Coprod.inl`, `Monoid.Coprod.inr`: canonical embeddings `M →* M ∗ N` and `N →* M ∗ N`.

* `Monoid.Coprod.lift`: construct a monoid homomorphism `M ∗ N →* P`
  from homomorphisms `M →* P` and `N →* P`; see also `Monoid.Coprod.liftEquiv`.

* `Monoid.Coprod.clift`: a constructor for homomorphisms `M ∗ N →* P`
  that allows the user to control the computational behavior.

* `Monoid.Coprod.map`: combine two homomorphisms `f : M →* N` and `g : M' →* N'`
  into `M ∗ M' →* N ∗ N'`.

* `Monoid.Coprod.swap`: the natural homomorphism `M ∗ N →* N ∗ M`.

* `Monoid.Coprod.fst`, `Monoid.Coprod.snd`, and `Monoid.Coprod.toProd`:
  natural projections `M ∗ N →* M`, `M ∗ N →* N`, and `M ∗ N →* M × N`.

### Monoid isomorphisms

* `MulEquiv.coprodCongr`: a `MulEquiv` version of `Monoid.Coprod.map`.
* `MulEquiv.coprodComm`: a `MulEquiv` version of `Monoid.Coprod.swap`.
* `MulEquiv.coprodAssoc`: associativity of the coproduct.
* `MulEquiv.coprodPUnit`, `MulEquiv.punitCoprod`:
  free product by `PUnit` on the left or on the right is isomorphic to the original monoid.

## Main results

The universal property of the coproduct
is given by the definition `Monoid.Coprod.lift` and the lemma `Monoid.Coprod.lift_unique`.

We also prove a slightly more general extensionality lemma `Monoid.Coprod.hom_ext`
for homomorphisms `M ∗ N →* P` and prove lots of basic lemmas like `Monoid.Coprod.fst_comp_inl`.

## Implementation details

The definition of the coproduct of an indexed family of monoids is formalized in `Monoid.CoprodI`.
While mathematically `M ∗ N` is a particular case
of the coproduct of an indexed family of monoids,
it is easier to build API from scratch instead of using something like

```
def Monoid.Coprod M N := Monoid.CoprodI ![M, N]
```

or

```
def Monoid.Coprod M N := Monoid.CoprodI (fun b : Bool => cond b M N)
```

There are several reasons to build an API from scratch.

- API about `Con` makes it easy to define the required type and prove the universal property,
  so there is little overhead compared to transferring API from `Monoid.CoprodI`.
- If `M` and `N` live in different universes, then the definition has to add `ULift`s;
  this makes it harder to transfer API and definitions.
- As of now, we have no way
  to automatically build an instance of `(k : Fin 2) → Monoid (![M, N] k)`
  from `[Monoid M]` and `[Monoid N]`,
  not even speaking about more advanced typeclass assumptions that involve both `M` and `N`.
- Using a list of `M ⊕ N` instead of, e.g., a list of `Σ k : Fin 2, ![M, N] k`
  as the underlying type makes it possible to write computationally effective code
  (though this point is not tested yet).

## TODO

- Prove `Monoid.CoprodI (f : Fin 2 → Type*) ≃* f 0 ∗ f 1` and
  `Monoid.CoprodI (f : Bool → Type*) ≃* f false ∗ f true`.

## Tags

group, monoid, coproduct, free product
-/

@[expose] public section

assert_not_exists MonoidWithZero

open FreeMonoid Function List Set

namespace Monoid

/-- The minimal congruence relation `c` on `FreeMonoid (M ⊕ N)`
such that `FreeMonoid.of ∘ Sum.inl` and `FreeMonoid.of ∘ Sum.inr` are monoid homomorphisms
to the quotient by `c`. -/
@[to_additive /-- The minimal additive congruence relation `c` on `FreeAddMonoid (M ⊕ N)`
such that `FreeAddMonoid.of ∘ Sum.inl` and `FreeAddMonoid.of ∘ Sum.inr`
are additive monoid homomorphisms to the quotient by `c`. -/]
/-
**Monoid.coprodCon** 是 Mathlib 中的一个定义，位于命名空间 `Monoid`。
形式化陈述：coprodCon (M N : Type*) [MulOneClass M] [MulOneClass N] : Con (FreeMonoid 
(M oplus N))
参数：M N : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def coprodCon (M N : Type*) [MulOneClass M] [MulOneClass N] : Con (FreeMonoid (M ⊕ N)) :=
  sInf {c |
    (∀ x y : M, c (of (Sum.inl (x * y))) (of (Sum.inl x) * of (Sum.inl y)))
    ∧ (∀ x y : N, c (of (Sum.inr (x * y))) (of (Sum.inr x) * of (Sum.inr y)))
    ∧ c (of <| Sum.inl 1) 1 ∧ c (of <| Sum.inr 1) 1}

/-- Coproduct of two monoids or groups. -/
@[to_additive /-- Coproduct of two additive monoids or groups. -/]
/-
**Monoid.Coprod** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Monoid.Coprod M N
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coproduct of two monoids or groups.
-/
def Coprod (M N : Type*) [MulOneClass M] [MulOneClass N] := (coprodCon M N).Quotient

namespace Coprod

@[inherit_doc]
scoped infix:30 " ∗ " => Coprod

section MulOneClass

variable {M N M' N' P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass M'] [MulOneClass N']
  [MulOneClass P]

/-
**Monoid.Coprod.** 是 Mathlib 中的一个实例，位于命名空间 `Monoid.Coprod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] protected instance : MulOneClass (M ∗ N) :=
  inferInstanceAs <| MulOneClass (coprodCon M N).Quotient

/-- The natural projection `FreeMonoid (M ⊕ N) →* M ∗ N`. -/
@[to_additive /-- The natural projection `FreeAddMonoid (M ⊕ N) →+ AddMonoid.Coprod M N`. -/]
/-
**Monoid.Coprod.mk** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.Coprod`。
形式化陈述：mk : FreeMonoid (M oplus N) ->* M ∗ N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural projection `FreeMonoid (M ⊕ N) →* M ∗ N`.
-/
def mk : FreeMonoid (M ⊕ N) →* M ∗ N := Con.mk' _

@[to_additive (attr := simp)]
/-
**Monoid.Coprod.con_ker_mk** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：con_ker_mk : Con.ker mk = coprodCon M N
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Con.mk'_ker`：∀ {M : Type u_1} [inst : MulOneClass M] (c : Con M), Con.ke
r c.mk' = c
-/
theorem con_ker_mk : Con.ker mk = coprodCon M N := Con.mk'_ker _

@[to_additive]
/-
**Monoid.Coprod.mk_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：mk_surjective : Surjective (@mk M N _ _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.mk_surjective`：Quot.mk_surjective {r : α -> α -> Prop} : Function.S
urjective (Quot.mk r)
-/
theorem mk_surjective : Surjective (@mk M N _ _) := Quot.mk_surjective

@[to_additive (attr := simp)]
/-
**Monoid.Coprod.mrange_mk** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：mrange_mk : MonoidHom.mrange (@mk M N _ _) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Con.mrange_mk'`：mrange_mk' : MonoidHom.mrange c.mk' = ⊤
-/
theorem mrange_mk : MonoidHom.mrange (@mk M N _ _) = ⊤ := Con.mrange_mk'

@[to_additive]
/-
**Monoid.Coprod.mk_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：mk_eq_mk {w₁ w₂ : FreeMonoid (M oplus N)} : mk w₁ = mk w₂ ↔ coprodCon M N 
w₁ w₂
参数：M oplus N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Con.eq`：∀ {M : Type u_1} [inst : Mul M] (c : Con M) {a b : M}, ↑a = ↑b ↔
 c a b
-/
theorem mk_eq_mk {w₁ w₂ : FreeMonoid (M ⊕ N)} : mk w₁ = mk w₂ ↔ coprodCon M N w₁ w₂ := Con.eq _

/-- The natural embedding `M →* M ∗ N`. -/
@[to_additive /-- The natural embedding `M →+ AddMonoid.Coprod M N`. -/]
/-
**Monoid.Coprod.inl** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.Coprod`。
形式化陈述：inl : M ->* M ∗ N where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural embedding `M →* M ∗ N`.
-/
def inl : M →* M ∗ N where
  toFun := fun x => mk (of (.inl x))
  map_one' := mk_eq_mk.2 fun _c hc => hc.2.2.1
  map_mul' := fun x y => mk_eq_mk.2 fun _c hc => hc.1 x y

/-- The natural embedding `N →* M ∗ N`. -/
@[to_additive /-- The natural embedding `N →+ AddMonoid.Coprod M N`. -/]
/-
**Monoid.Coprod.inr** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.Coprod`。
形式化陈述：inr : N ->* M ∗ N where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural embedding `N →* M ∗ N`.
-/
def inr : N →* M ∗ N where
  toFun := fun x => mk (of (.inr x))
  map_one' := mk_eq_mk.2 fun _c hc => hc.2.2.2
  map_mul' := fun x y => mk_eq_mk.2 fun _c hc => hc.2.1 x y

@[to_additive (attr := simp)]
/-
**Monoid.Coprod.mk_of_inl** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：mk_of_inl (x : M) : (mk (of (.inl x)) : M ∗ N) = inl x
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_of_inl (x : M) : (mk (of (.inl x)) : M ∗ N) = inl x := rfl

@[to_additive (attr := simp)]
/-
**Monoid.Coprod.mk_of_inr** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：mk_of_inr (x : N) : (mk (of (.inr x)) : M ∗ N) = inr x
参数：x : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_of_inr (x : N) : (mk (of (.inr x)) : M ∗ N) = inr x := rfl

@[to_additive (attr := elab_as_elim)]
/-
**Monoid.Coprod.induction_on'** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：induction_on' {motive : M ∗ N -> Prop} (m : M ∗ N) (one : motive 1) (inl_m
ul : forall m x, motive x -> motive (inl m * x)) (inr_mul : forall n x, motive x
 -> motive (inr n * x)) : motive m
参数：m : M ∗ N；one : motive 1；inl_mul : forall m x, motive x -> motive (inl m * x)
；inr_mul : forall n x, motive x -> motive (inr n * x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.Coprod.mk_surjective`：mk_surjective : Surjective (@mk M N _ _)
· 使用定理 `FreeMonoid.inductionOn'`：∀ {α : Type u_1} {motive : FreeMonoid α → Prop}
 (a : FreeMonoid α),   motive 1 → (∀ (b : α) (a : FreeMonoid α), motive a → moti
ve (FreeMonoi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem induction_on' {motive : M ∗ N → Prop} (m : M ∗ N)
    (one : motive 1)
    (inl_mul : ∀ m x, motive x → motive (inl m * x))
    (inr_mul : ∀ n x, motive x → motive (inr n * x)) : motive m := by
  rcases mk_surjective m with ⟨x, rfl⟩
  induction x using FreeMonoid.inductionOn' with
  | one => exact one
  | of_mul x xs ih =>
    cases x with
    | inl m => simpa using inl_mul m _ ih
    | inr n => simpa using inr_mul n _ ih

@[to_additive (attr := elab_as_elim)]
/-
**Monoid.Coprod.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：induction_on {motive : M ∗ N -> Prop} (m : M ∗ N) (inl : forall m, motive 
(inl m)) (inr : forall n, motive (inr n)) (mul : forall x y, motive x -> motive 
y -> motive (x * y)) : motive m
参数：m : M ∗ N；inl : forall m, motive (inl m)；inr : forall n, motive (inr n)；mul :
 forall x y, motive x -> motive y -> motive (x * y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.Coprod.induction_on'`：induction_on' {motive : M ∗ N -> Prop} (m :
 M ∗ N) (one : motive 1) (inl_mul : forall m x, motive x -> motive (inl m * x)) 
(inr_mul : forall…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
theorem induction_on {motive : M ∗ N → Prop} (m : M ∗ N)
    (inl : ∀ m, motive (inl m)) (inr : ∀ n, motive (inr n))
    (mul : ∀ x y, motive x → motive y → motive (x * y)) : motive m :=
  induction_on' m (by simpa using inl 1) (fun _ _ ↦ mul _ _ (inl _)) fun _ _ ↦ mul _ _ (inr _)

/-- Lift a monoid homomorphism `FreeMonoid (M ⊕ N) →* P` satisfying additional properties to
`M ∗ N →* P`. In many cases, `Coprod.lift` is more convenient.

Compared to `Coprod.lift`,
this definition allows a user to provide a custom computational behavior.
Also, it only needs `MulOneClass` assumptions while `Coprod.lift` needs a `Monoid` structure.
-/
@[to_additive /-- Lift an additive monoid homomorphism `FreeAddMonoid (M ⊕ N) →+ P` satisfying
additional properties to `AddMonoid.Coprod M N →+ P`.

Compared to `AddMonoid.Coprod.lift`,
this definition allows a user to provide a custom computational behavior.
Also, it only needs `AddZeroClass` assumptions
while `AddMonoid.Coprod.lift` needs an `AddMonoid` structure. -/]
/-
**Monoid.Coprod.clift** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.Coprod`。
形式化陈述：clift (f : FreeMonoid (M oplus N) ->* P) (hM₁ : f (of (.inl 1)) = 1) (hN₁ 
: f (of (.inr 1)) = 1) (hM : forall x y, f (of (.inl (x * y))) = f (of (.inl x) 
* of (.inl y))) (hN : forall x y, f (of (.inr (x * y))) = f (of (.inr x) * of (.
inr y))) : M ∗ N ->* P
参数：f : FreeMonoid (M oplus N) ->* P；hM₁ : f (of (.inl 1)) = 1；hN₁ : f (of (.inr 
1)) = 1；hM : forall x y, f (of (.inl (x * y))) = f (of (.inl x) * of (.inl y))；h
N : forall x y, f (of (.inr (x * y))) = f (of (.inr x) * of (.inr y))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def clift (f : FreeMonoid (M ⊕ N) →* P)
    (hM₁ : f (of (.inl 1)) = 1) (hN₁ : f (of (.inr 1)) = 1)
    (hM : ∀ x y, f (of (.inl (x * y))) = f (of (.inl x) * of (.inl y)))
    (hN : ∀ x y, f (of (.inr (x * y))) = f (of (.inr x) * of (.inr y))) :
    M ∗ N →* P :=
  Con.lift _ f <| sInf_le ⟨hM, hN, hM₁.trans (map_one f).symm, hN₁.trans (map_one f).symm⟩

@[to_additive (attr := simp)]
/-
**Monoid.Coprod.clift_apply_inl** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：clift_apply_inl (f : FreeMonoid (M oplus N) ->* P) (hM₁ hN₁ hM hN) (x : M)
 : clift f hM₁ hN₁ hM hN (inl x) = f (of (.inl x))
参数：f : FreeMonoid (M oplus N) ->* P；hM₁ hN₁ hM hN；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem clift_apply_inl (f : FreeMonoid (M ⊕ N) →* P) (hM₁ hN₁ hM hN) (x : M) :
    clift f hM₁ hN₁ hM hN (inl x) = f (of (.inl x)) :=
  rfl

@[to_additive (attr := simp)]
/-
**Monoid.Coprod.clift_apply_inr** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：clift_apply_inr (f : FreeMonoid (M oplus N) ->* P) (hM₁ hN₁ hM hN) (x : N)
 : clift f hM₁ hN₁ hM hN (inr x) = f (of (.inr x))
参数：f : FreeMonoid (M oplus N) ->* P；hM₁ hN₁ hM hN；x : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem clift_apply_inr (f : FreeMonoid (M ⊕ N) →* P) (hM₁ hN₁ hM hN) (x : N) :
    clift f hM₁ hN₁ hM hN (inr x) = f (of (.inr x)) :=
  rfl

@[to_additive (attr := simp)]
/-
**Monoid.Coprod.clift_apply_mk** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：clift_apply_mk (f : FreeMonoid (M oplus N) ->* P) (hM₁ hN₁ hM hN w) : clif
t f hM₁ hN₁ hM hN (mk w) = f w
参数：f : FreeMonoid (M oplus N) ->* P；hM₁ hN₁ hM hN w。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem clift_apply_mk (f : FreeMonoid (M ⊕ N) →* P) (hM₁ hN₁ hM hN w) :
    clift f hM₁ hN₁ hM hN (mk w) = f w :=
  rfl

@[to_additive (attr := simp)]
/-
**Monoid.Coprod.clift_comp_mk** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：clift_comp_mk (f : FreeMonoid (M oplus N) ->* P) (hM₁ hN₁ hM hN) : (clift 
f hM₁ hN₁ hM hN).comp mk = f
参数：f : FreeMonoid (M oplus N) ->* P；hM₁ hN₁ hM hN。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem clift_comp_mk (f : FreeMonoid (M ⊕ N) →* P) (hM₁ hN₁ hM hN) :
    (clift f hM₁ hN₁ hM hN).comp mk = f :=
  DFunLike.ext' rfl

@[to_additive (attr := simp)]
/-
**Monoid.Coprod.mclosure_range_inl_union_inr** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.C
oprod`。
形式化陈述：mclosure_range_inl_union_inr : Submonoid.closure (range (inl : M ->* M ∗ N
) union range (inr : N ->* M ∗ N)) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monoid.Coprod.mrange_mk`：mrange_mk : MonoidHom.mrange (@mk M N _ _) = ⊤
· 使用定理 `MonoidHom.mrange_eq_map`：mrange_eq_map (f : F) : mrange f = (⊤ : Submono
id M).map f
· 使用定理 `FreeMonoid.closure_range_of`：closure_range_of : closure (Set.range <| @o
f α) = ⊤
· 使用定理 `MonoidHom.map_mclosure`：map_mclosure (f : F) (s : Set M) : (closure s).m
ap f = closure (f '' s)
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Sum.range_eq`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α ⊕ β 
→ γ),   Set.range f = Set.range (f ∘ Sum.inl) ∪ Set.range (f ∘ Sum.inr)
-/
theorem mclosure_range_inl_union_inr :
    Submonoid.closure (range (inl : M →* M ∗ N) ∪ range (inr : N →* M ∗ N)) = ⊤ := by
  rw [← mrange_mk, MonoidHom.mrange_eq_map, ← closure_range_of, MonoidHom.map_mclosure,
    ← range_comp, Sum.range_eq]; rfl
/-
**Monoid.Coprod.mrange_inl_sup_mrange_inr** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Copr
od`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} [inst : MulOneClass M] [inst_1 : MulOneCla
ss N],   MonoidHom.mrange Monoid.Coprod.inl ⊔ MonoidHom.mrange Monoid.Coprod.inr
 = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monoid.Coprod.mclosure_range_inl_union_inr`：mclosure_range_inl_union_inr
 : Submonoid.closure (range (inl : M ->* M ∗ N) union range (inr : N ->* M ∗ N))
 = ⊤
· 使用定理 `Submonoid.closure_union`：closure_union (s t : Set M) : closure (s union 
t) = closure s ⊔ closure t
· 使用定理 `MonoidHom.coe_mrange`：coe_mrange (f : F) : (mrange f : Set N) = Set.rang
e f
· 使用定理 `Submonoid.closure_eq`：closure_eq : closure (S : Set M) = S
-/
@[to_additive (attr := simp)] theorem mrange_inl_sup_mrange_inr :
    MonoidHom.mrange (inl : M →* M ∗ N) ⊔ MonoidHom.mrange (inr : N →* M ∗ N) = ⊤ := by
  rw [← mclosure_range_inl_union_inr, Submonoid.closure_union, ← MonoidHom.coe_mrange,
    ← MonoidHom.coe_mrange, Submonoid.closure_eq, Submonoid.closure_eq]

@[to_additive]
/-
**Monoid.Coprod.codisjoint_mrange_inl_mrange_inr** 是 Mathlib 中的一个定理，位于命名空间 `Mono
id.Coprod`。
形式化陈述：codisjoint_mrange_inl_mrange_inr : Codisjoint (MonoidHom.mrange (inl : M -
>* M ∗ N)) (MonoidHom.mrange inr)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `codisjoint_iff`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : Ord
erTop α] {a b : α}, Codisjoint a b ↔ a ⊔ b = ⊤
· 使用定理 `Monoid.Coprod.mrange_inl_sup_mrange_inr`：∀ {M : Type u_1} {N : Type u_2}
 [inst : MulOneClass M] [inst_1 : MulOneClass N],   MonoidHom.mrange Monoid.Copr
od.inl ⊔ MonoidHom.mrange Mon…
-/
theorem codisjoint_mrange_inl_mrange_inr :
    Codisjoint (MonoidHom.mrange (inl : M →* M ∗ N)) (MonoidHom.mrange inr) :=
  codisjoint_iff.2 mrange_inl_sup_mrange_inr
/-
**Monoid.Coprod.mrange_eq** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} {P : Type u_5} [inst : MulOneClass M] [ins
t_1 : MulOneClass N] [inst_2 : MulOneClass P]   (f : Monoid.Coprod M N →* P),   
MonoidHom.mrange f = MonoidHom.mrange (f.comp Monoid.Coprod.inl) ⊔ MonoidHom.mra
nge (f.comp Monoid.Coprod.inr)
参数：f : Monoid.Coprod M N →* P；f.comp Monoid.Coprod.inl；f.comp Monoid.Coprod.inr。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.mrange_eq_map`：mrange_eq_map (f : F) : mrange f = (⊤ : Submono
id M).map f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monoid.Coprod.mrange_inl_sup_mrange_inr`：∀ {M : Type u_1} {N : Type u_2}
 [inst : MulOneClass M] [inst_1 : MulOneClass N],   MonoidHom.mrange Monoid.Copr
od.inl ⊔ MonoidHom.mrange Mon…
· 使用定理 `Submonoid.map_sup`：map_sup (S T : Submonoid M) (f : F) : (S ⊔ T).map f =
 S.map f ⊔ T.map f
· 使用定理 `MonoidHom.map_mrange`：map_mrange (g : N ->* P) (f : M ->* N) : (mrange f
).map g = mrange (comp g f)
-/
@[to_additive] theorem mrange_eq (f : M ∗ N →* P) :
    MonoidHom.mrange f = MonoidHom.mrange (f.comp inl) ⊔ MonoidHom.mrange (f.comp inr) := by
  rw [MonoidHom.mrange_eq_map, ← mrange_inl_sup_mrange_inr, Submonoid.map_sup, MonoidHom.map_mrange,
    MonoidHom.map_mrange]

/-- Extensionality lemma for monoid homomorphisms `M ∗ N →* P`.
If two homomorphisms agree on the ranges of `Monoid.Coprod.inl` and `Monoid.Coprod.inr`,
then they are equal. -/
@[to_additive (attr := ext 1100)
  /-- Extensionality lemma for additive monoid homomorphisms `AddMonoid.Coprod M N →+ P`.
  If two homomorphisms agree on the ranges of `AddMonoid.Coprod.inl` and `AddMonoid.Coprod.inr`,
  then they are equal. -/]
/-
**Monoid.Coprod.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：hom_ext {f g : M ∗ N ->* P} (h₁ : f.comp inl = g.comp inl) (h₂ : f.comp in
r = g.comp inr) : f = g
参数：h₁ : f.comp inl = g.comp inl；h₂ : f.comp inr = g.comp inr。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.eq_of_eqOn_denseM`：eq_of_eqOn_denseM {s : Set M} (hs : closure
 s = ⊤) {f g : M ->* N} (h : s.EqOn f g) : f = g
· 使用定理 `Monoid.Coprod.mclosure_range_inl_union_inr`：mclosure_range_inl_union_inr
 : Submonoid.closure (range (inl : M ->* M ∗ N) union range (inr : N ->* M ∗ N))
 = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eqOn_union`：eqOn_union : EqOn f₁ f₂ (s₁ union s₂) ↔ EqOn f₁ f₂ s₁ ∧ 
EqOn f₁ f₂ s₂
· 使用定理 `Set.eqOn_range`：eqOn_range {ι : Sort*} {f : ι -> α} {g₁ g₂ : α -> β} : E
qOn g₁ g₂ (range f) ↔ g₁ ∘ f = g₂ ∘ f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext'_iff`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [i
 : DFunLike F α β] {f g : F}, f = g ↔ ⇑f = ⇑g
-/
theorem hom_ext {f g : M ∗ N →* P} (h₁ : f.comp inl = g.comp inl) (h₂ : f.comp inr = g.comp inr) :
    f = g :=
  MonoidHom.eq_of_eqOn_denseM mclosure_range_inl_union_inr <| eqOn_union.2
    ⟨eqOn_range.2 <| DFunLike.ext'_iff.1 h₁, eqOn_range.2 <| DFunLike.ext'_iff.1 h₂⟩

@[to_additive (attr := simp)]
/-
**Monoid.Coprod.clift_mk** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：clift_mk : clift (mk : FreeMonoid (M oplus N) ->* M ∗ N) (map_one inl) (ma
p_one inr) (map_mul inl) (map_mul inr) = .id _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.Coprod.hom_ext`：hom_ext {f g : M ∗ N ->* P} (h₁ : f.comp inl = g.
comp inl) (h₂ : f.comp inr = g.comp inr) : f = g
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
theorem clift_mk :
    clift (mk : FreeMonoid (M ⊕ N) →* M ∗ N) (map_one inl) (map_one inr) (map_mul inl)
      (map_mul inr) = .id _ :=
  hom_ext rfl rfl

/-- Map `M ∗ N` to `M' ∗ N'` by applying `Sum.map f g` to each element of the underlying list. -/
@[to_additive /-- Map `AddMonoid.Coprod M N` to `AddMonoid.Coprod M' N'`
by applying `Sum.map f g` to each element of the underlying list. -/]
/-
**Monoid.Coprod.map** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.Coprod`。
形式化陈述：map (f : M ->* M') (g : N ->* N') : M ∗ N ->* M' ∗ N'
参数：f : M ->* M'；g : N ->* N'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def map (f : M →* M') (g : N →* N') : M ∗ N →* M' ∗ N' :=
  clift (mk.comp <| FreeMonoid.map <| Sum.map f g)
    (by simp only [MonoidHom.comp_apply, map_of, Sum.map_inl, map_one, mk_of_inl])
    (by simp only [MonoidHom.comp_apply, map_of, Sum.map_inr, map_one, mk_of_inr])
    (fun x y => by simp only [MonoidHom.comp_apply, map_of, Sum.map_inl, map_mul, mk_of_inl])
    fun x y => by simp only [MonoidHom.comp_apply, map_of, Sum.map_inr, map_mul, mk_of_inr]

@[to_additive (attr := simp)]
/-
**Monoid.Coprod.map_mk_ofList** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：map_mk_ofList (f : M ->* M') (g : N ->* N') (l : List (M oplus N)) : map f
 g (mk (ofList l)) = mk (ofList (l.map (Sum.map f g)))
参数：f : M ->* M'；g : N ->* N'；l : List (M oplus N)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_mk_ofList (f : M →* M') (g : N →* N') (l : List (M ⊕ N)) :
    map f g (mk (ofList l)) = mk (ofList (l.map (Sum.map f g))) :=
  rfl

@[to_additive (attr := simp)]
/-
**Monoid.Coprod.map_apply_inl** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：map_apply_inl (f : M ->* M') (g : N ->* N') (x : M) : map f g (inl x) = in
l (f x)
参数：f : M ->* M'；g : N ->* N'；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_apply_inl (f : M →* M') (g : N →* N') (x : M) : map f g (inl x) = inl (f x) := rfl

@[to_additive (attr := simp)]
/-
**Monoid.Coprod.map_apply_inr** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：map_apply_inr (f : M ->* M') (g : N ->* N') (x : N) : map f g (inr x) = in
r (g x)
参数：f : M ->* M'；g : N ->* N'；x : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_apply_inr (f : M →* M') (g : N →* N') (x : N) : map f g (inr x) = inr (g x) := rfl

@[to_additive (attr := simp)]
/-
**Monoid.Coprod.map_comp_inl** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：map_comp_inl (f : M ->* M') (g : N ->* N') : (map f g).comp inl = inl.comp
 f
参数：f : M ->* M'；g : N ->* N'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_comp_inl (f : M →* M') (g : N →* N') : (map f g).comp inl = inl.comp f := rfl

@[to_additive (attr := simp)]
/-
**Monoid.Coprod.map_comp_inr** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：map_comp_inr (f : M ->* M') (g : N ->* N') : (map f g).comp inr = inr.comp
 g
参数：f : M ->* M'；g : N ->* N'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_comp_inr (f : M →* M') (g : N →* N') : (map f g).comp inr = inr.comp g := rfl

@[to_additive (attr := simp)]
/-
**Monoid.Coprod.map_id_id** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：map_id_id : map (.id M) (.id N) = .id (M ∗ N)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.Coprod.hom_ext`：hom_ext {f g : M ∗ N ->* P} (h₁ : f.comp inl = g.
comp inl) (h₂ : f.comp inr = g.comp inr) : f = g
-/
theorem map_id_id : map (.id M) (.id N) = .id (M ∗ N) := hom_ext rfl rfl

@[to_additive]
/-
**Monoid.Coprod.map_comp_map** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：map_comp_map {M'' N''} [MulOneClass M''] [MulOneClass N''] (f' : M' ->* M'
') (g' : N' ->* N'') (f : M ->* M') (g : N ->* N') : (map f' g').comp (map f g) 
= map (f'.comp f) (g'.comp g)
参数：f' : M' ->* M''；g' : N' ->* N''；f : M ->* M'；g : N ->* N'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.Coprod.hom_ext`：hom_ext {f g : M ∗ N ->* P} (h₁ : f.comp inl = g.
comp inl) (h₂ : f.comp inr = g.comp inr) : f = g
-/
theorem map_comp_map {M'' N''} [MulOneClass M''] [MulOneClass N''] (f' : M' →* M'') (g' : N' →* N'')
    (f : M →* M') (g : N →* N') : (map f' g').comp (map f g) = map (f'.comp f) (g'.comp g) :=
  hom_ext rfl rfl

@[to_additive]
/-
**Monoid.Coprod.map_map** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：map_map {M'' N''} [MulOneClass M''] [MulOneClass N''] (f' : M' ->* M'') (g
' : N' ->* N'') (f : M ->* M') (g : N ->* N') (x : M ∗ N) : map f' g' (map f g x
) = map (f'.comp f) (g'.comp g) x
参数：f' : M' ->* M''；g' : N' ->* N''；f : M ->* M'；g : N ->* N'；x : M ∗ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Monoid.Coprod.map_comp_map`：map_comp_map {M'' N''} [MulOneClass M''] [Mu
lOneClass N''] (f' : M' ->* M'') (g' : N' ->* N'') (f : M ->* M') (g : N ->* N')
 : (map f' g').c…
-/
theorem map_map {M'' N''} [MulOneClass M''] [MulOneClass N''] (f' : M' →* M'') (g' : N' →* N'')
    (f : M →* M') (g : N →* N') (x : M ∗ N) :
    map f' g' (map f g x) = map (f'.comp f) (g'.comp g) x :=
  DFunLike.congr_fun (map_comp_map f' g' f g) x

variable (M N)

/-- Map `M ∗ N` to `N ∗ M` by applying `Sum.swap` to each element of the underlying list.

See also `MulEquiv.coprodComm` for a `MulEquiv` version. -/
@[to_additive /-- Map `AddMonoid.Coprod M N` to `AddMonoid.Coprod N M`
  by applying `Sum.swap` to each element of the underlying list.

See also `AddEquiv.coprodComm` for an `AddEquiv` version. -/]
/-
**Monoid.Coprod.swap** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.Coprod`。
形式化陈述：swap : M ∗ N ->* N ∗ M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def swap : M ∗ N →* N ∗ M :=
  clift (mk.comp <| FreeMonoid.map Sum.swap)
    (by simp only [MonoidHom.comp_apply, map_of, Sum.swap_inl, mk_of_inr, map_one])
    (by simp only [MonoidHom.comp_apply, map_of, Sum.swap_inr, mk_of_inl, map_one])
    (fun x y => by simp only [MonoidHom.comp_apply, map_of, Sum.swap_inl, mk_of_inr, map_mul])
    (fun x y => by simp only [MonoidHom.comp_apply, map_of, Sum.swap_inr, mk_of_inl, map_mul])

@[to_additive (attr := simp)]
/-
**Monoid.Coprod.swap_comp_swap** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：swap_comp_swap : (swap M N).comp (swap N M) = .id _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.Coprod.hom_ext`：hom_ext {f g : M ∗ N ->* P} (h₁ : f.comp inl = g.
comp inl) (h₂ : f.comp inr = g.comp inr) : f = g
-/
theorem swap_comp_swap : (swap M N).comp (swap N M) = .id _ := hom_ext rfl rfl

variable {M N}

@[to_additive (attr := simp)]
/-
**Monoid.Coprod.swap_swap** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：swap_swap (x : M ∗ N) : swap N M (swap M N x) = x
参数：x : M ∗ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Monoid.Coprod.swap_comp_swap`：swap_comp_swap : (swap M N).comp (swap N M
) = .id _
-/
theorem swap_swap (x : M ∗ N) : swap N M (swap M N x) = x :=
  DFunLike.congr_fun (swap_comp_swap _ _) x

@[to_additive]
/-
**Monoid.Coprod.swap_comp_map** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：swap_comp_map (f : M ->* M') (g : N ->* N') : (swap M' N').comp (map f g) 
= (map g f).comp (swap M N)
参数：f : M ->* M'；g : N ->* N'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.Coprod.hom_ext`：hom_ext {f g : M ∗ N ->* P} (h₁ : f.comp inl = g.
comp inl) (h₂ : f.comp inr = g.comp inr) : f = g
-/
theorem swap_comp_map (f : M →* M') (g : N →* N') :
    (swap M' N').comp (map f g) = (map g f).comp (swap M N) :=
  hom_ext rfl rfl

@[to_additive]
/-
**Monoid.Coprod.swap_map** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：swap_map (f : M ->* M') (g : N ->* N') (x : M ∗ N) : swap M' N' (map f g x
) = map g f (swap M N x)
参数：f : M ->* M'；g : N ->* N'；x : M ∗ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Monoid.Coprod.swap_comp_map`：swap_comp_map (f : M ->* M') (g : N ->* N')
 : (swap M' N').comp (map f g) = (map g f).comp (swap M N)
-/
theorem swap_map (f : M →* M') (g : N →* N') (x : M ∗ N) :
    swap M' N' (map f g x) = map g f (swap M N x) :=
  DFunLike.congr_fun (swap_comp_map f g) x
/-
**Monoid.Coprod.swap_comp_inl** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} [inst : MulOneClass M] [inst_1 : MulOneCla
ss N],   (Monoid.Coprod.swap M N).comp Monoid.Coprod.inl = Monoid.Coprod.inr
参数：Monoid.Coprod.swap M N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] theorem swap_comp_inl : (swap M N).comp inl = inr := rfl
/-
**Monoid.Coprod.swap_inl** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} [inst : MulOneClass M] [inst_1 : MulOneCla
ss N] (x : M),   (Monoid.Coprod.swap M N) (Monoid.Coprod.inl x) = Monoid.Coprod.
inr x
参数：x : M；Monoid.Coprod.swap M N；Monoid.Coprod.inl x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] theorem swap_inl (x : M) : swap M N (inl x) = inr x := rfl
/-
**Monoid.Coprod.swap_comp_inr** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} [inst : MulOneClass M] [inst_1 : MulOneCla
ss N],   (Monoid.Coprod.swap M N).comp Monoid.Coprod.inr = Monoid.Coprod.inl
参数：Monoid.Coprod.swap M N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] theorem swap_comp_inr : (swap M N).comp inr = inl := rfl
/-
**Monoid.Coprod.swap_inr** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} [inst : MulOneClass M] [inst_1 : MulOneCla
ss N] (x : N),   (Monoid.Coprod.swap M N) (Monoid.Coprod.inr x) = Monoid.Coprod.
inl x
参数：x : N；Monoid.Coprod.swap M N；Monoid.Coprod.inr x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] theorem swap_inr (x : N) : swap M N (inr x) = inl x := rfl

@[to_additive]
/-
**Monoid.Coprod.swap_injective** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：swap_injective : Injective (swap M N)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `Monoid.Coprod.swap_swap`：swap_swap (x : M ∗ N) : swap N M (swap M N x) =
 x
-/
theorem swap_injective : Injective (swap M N) := LeftInverse.injective swap_swap

@[to_additive (attr := simp)]
/-
**Monoid.Coprod.swap_inj** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：swap_inj {x y : M ∗ N} : swap M N x = swap M N y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Monoid.Coprod.swap_injective`：swap_injective : Injective (swap M N)
-/
theorem swap_inj {x y : M ∗ N} : swap M N x = swap M N y ↔ x = y := swap_injective.eq_iff

@[to_additive (attr := simp)]
/-
**Monoid.Coprod.swap_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：swap_eq_one {x : M ∗ N} : swap M N x = 1 ↔ x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Monoid.Coprod.swap_injective`：swap_injective : Injective (swap M N)
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
theorem swap_eq_one {x : M ∗ N} : swap M N x = 1 ↔ x = 1 := swap_injective.eq_iff' (map_one _)

@[to_additive]
/-
**Monoid.Coprod.swap_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：swap_surjective : Surjective (swap M N)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.LeftInverse f g → Function.Surjective f
· 使用定理 `Monoid.Coprod.swap_swap`：swap_swap (x : M ∗ N) : swap N M (swap M N x) =
 x
-/
theorem swap_surjective : Surjective (swap M N) := LeftInverse.surjective swap_swap

@[to_additive]
/-
**Monoid.Coprod.swap_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：swap_bijective : Bijective (swap M N)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.Coprod.swap_injective`：swap_injective : Injective (swap M N)
· 使用定理 `Monoid.Coprod.swap_surjective`：swap_surjective : Surjective (swap M N)
-/
theorem swap_bijective : Bijective (swap M N) := ⟨swap_injective, swap_surjective⟩

@[to_additive (attr := simp)]
/-
**Monoid.Coprod.mker_swap** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：mker_swap : MonoidHom.mker (swap M N) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T
· 使用定理 `Monoid.Coprod.swap_eq_one`：swap_eq_one {x : M ∗ N} : swap M N x = 1 ↔ x 
= 1
-/
theorem mker_swap : MonoidHom.mker (swap M N) = ⊥ := Submonoid.ext fun _ ↦ swap_eq_one

@[to_additive (attr := simp)]
/-
**Monoid.Coprod.mrange_swap** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：mrange_swap : MonoidHom.mrange (swap M N) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.mrange_eq_top_of_surjective`：mrange_eq_top_of_surjective (f : 
F) (hf : Function.Surjective f) : mrange f = (⊤ : Submonoid N)
· 使用定理 `Monoid.Coprod.swap_surjective`：swap_surjective : Surjective (swap M N)
-/
theorem mrange_swap : MonoidHom.mrange (swap M N) = ⊤ :=
  MonoidHom.mrange_eq_top_of_surjective _ swap_surjective

end MulOneClass

section Lift

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [Monoid P]

/-- Lift a pair of monoid homomorphisms `f : M →* P`, `g : N →* P`
to a monoid homomorphism `M ∗ N →* P`.

See also `Coprod.clift` for a version that allows custom computational behavior
and works for a `MulOneClass` codomain.
-/
@[to_additive /-- Lift a pair of additive monoid homomorphisms `f : M →+ P`, `g : N →+ P`
to an additive monoid homomorphism `AddMonoid.Coprod M N →+ P`.

See also `AddMonoid.Coprod.clift` for a version that allows custom computational behavior
and works for an `AddZeroClass` codomain. -/]
/-
**Monoid.Coprod.lift** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.Coprod`。
形式化陈述：lift (f : M ->* P) (g : N ->* P) : (M ∗ N) ->* P
参数：f : M ->* P；g : N ->* P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def lift (f : M →* P) (g : N →* P) : (M ∗ N) →* P :=
  clift (FreeMonoid.lift <| Sum.elim f g) (map_one f) (map_one g) (map_mul f) (map_mul g)

@[to_additive (attr := simp)]
/-
**Monoid.Coprod.lift_apply_mk** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：lift_apply_mk (f : M ->* P) (g : N ->* P) (x : FreeMonoid (M oplus N)) : l
ift f g (mk x) = FreeMonoid.lift (Sum.elim f g) x
参数：f : M ->* P；g : N ->* P；x : FreeMonoid (M oplus N)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_apply_mk (f : M →* P) (g : N →* P) (x : FreeMonoid (M ⊕ N)) :
    lift f g (mk x) = FreeMonoid.lift (Sum.elim f g) x :=
  rfl

@[to_additive (attr := simp)]
/-
**Monoid.Coprod.lift_apply_inl** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：lift_apply_inl (f : M ->* P) (g : N ->* P) (x : M) : lift f g (inl x) = f 
x
参数：f : M ->* P；g : N ->* P；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_apply_inl (f : M →* P) (g : N →* P) (x : M) : lift f g (inl x) = f x :=
  rfl

@[to_additive]
/-
**Monoid.Coprod.lift_unique** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：lift_unique {f : M ->* P} {g : N ->* P} {fg : M ∗ N ->* P} (h₁ : fg.comp i
nl = f) (h₂ : fg.comp inr = g) : fg = lift f g
参数：h₁ : fg.comp inl = f；h₂ : fg.comp inr = g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.Coprod.hom_ext`：hom_ext {f g : M ∗ N ->* P} (h₁ : f.comp inl = g.
comp inl) (h₂ : f.comp inr = g.comp inr) : f = g
-/
theorem lift_unique {f : M →* P} {g : N →* P} {fg : M ∗ N →* P} (h₁ : fg.comp inl = f)
    (h₂ : fg.comp inr = g) : fg = lift f g :=
  hom_ext h₁ h₂

@[to_additive (attr := simp)]
/-
**Monoid.Coprod.lift_comp_inl** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：lift_comp_inl (f : M ->* P) (g : N ->* P) : (lift f g).comp inl = f
参数：f : M ->* P；g : N ->* P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_comp_inl (f : M →* P) (g : N →* P) : (lift f g).comp inl = f := rfl

@[to_additive (attr := simp)]
/-
**Monoid.Coprod.lift_apply_inr** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：lift_apply_inr (f : M ->* P) (g : N ->* P) (x : N) : lift f g (inr x) = g 
x
参数：f : M ->* P；g : N ->* P；x : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_apply_inr (f : M →* P) (g : N →* P) (x : N) : lift f g (inr x) = g x :=
  rfl

@[to_additive (attr := simp)]
/-
**Monoid.Coprod.lift_comp_inr** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：lift_comp_inr (f : M ->* P) (g : N ->* P) : (lift f g).comp inr = g
参数：f : M ->* P；g : N ->* P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_comp_inr (f : M →* P) (g : N →* P) : (lift f g).comp inr = g := rfl

@[to_additive (attr := simp)]
/-
**Monoid.Coprod.lift_comp_swap** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：lift_comp_swap (f : M ->* P) (g : N ->* P) : (lift f g).comp (swap N M) = 
lift g f
参数：f : M ->* P；g : N ->* P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.Coprod.hom_ext`：hom_ext {f g : M ∗ N ->* P} (h₁ : f.comp inl = g.
comp inl) (h₂ : f.comp inr = g.comp inr) : f = g
-/
theorem lift_comp_swap (f : M →* P) (g : N →* P) : (lift f g).comp (swap N M) = lift g f :=
  hom_ext rfl rfl

@[to_additive (attr := simp)]
/-
**Monoid.Coprod.lift_swap** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：lift_swap (f : M ->* P) (g : N ->* P) (x : N ∗ M) : lift f g (swap N M x) 
= lift g f x
参数：f : M ->* P；g : N ->* P；x : N ∗ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Monoid.Coprod.lift_comp_swap`：lift_comp_swap (f : M ->* P) (g : N ->* P)
 : (lift f g).comp (swap N M) = lift g f
-/
theorem lift_swap (f : M →* P) (g : N →* P) (x : N ∗ M) : lift f g (swap N M x) = lift g f x :=
  DFunLike.congr_fun (lift_comp_swap f g) x

@[to_additive]
/-
**Monoid.Coprod.comp_lift** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：comp_lift {P' : Type*} [Monoid P'] (f : P ->* P') (g₁ : M ->* P) (g₂ : N -
>* P) : f.comp (lift g₁ g₂) = lift (f.comp g₁) (f.comp g₂)
参数：f : P ->* P'；g₁ : M ->* P；g₂ : N ->* P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.Coprod.hom_ext`：hom_ext {f g : M ∗ N ->* P} (h₁ : f.comp inl = g.
comp inl) (h₂ : f.comp inr = g.comp inr) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.comp_assoc`：MonoidHom.comp_assoc {Q : Type*} [MulOne M] [MulOn
e N] [MulOne P] [MulOne Q] (f : M ->* N) (g : N ->* P) (h : P ->* Q) : (h.comp g
).comp f =…
· 使用定理 `Monoid.Coprod.lift_comp_inl`：lift_comp_inl (f : M ->* P) (g : N ->* P) :
 (lift f g).comp inl = f
· 使用定理 `Monoid.Coprod.lift_comp_inr`：lift_comp_inr (f : M ->* P) (g : N ->* P) :
 (lift f g).comp inr = g
-/
theorem comp_lift {P' : Type*} [Monoid P'] (f : P →* P') (g₁ : M →* P) (g₂ : N →* P) :
    f.comp (lift g₁ g₂) = lift (f.comp g₁) (f.comp g₂) :=
  hom_ext (by rw [MonoidHom.comp_assoc, lift_comp_inl, lift_comp_inl]) <| by
    rw [MonoidHom.comp_assoc, lift_comp_inr, lift_comp_inr]

/-- `Coprod.lift` as an equivalence. -/
@[to_additive /-- `AddMonoid.Coprod.lift` as an equivalence. -/]
/-
**Monoid.Coprod.liftEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.Coprod`。
形式化陈述：liftEquiv : (M ->* P) × (N ->* P) ≃ (M ∗ N ->* P) where toFun fg
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Coprod.lift` as an equivalence.
-/
def liftEquiv : (M →* P) × (N →* P) ≃ (M ∗ N →* P) where
  toFun fg := lift fg.1 fg.2
  invFun f := (f.comp inl, f.comp inr)
  right_inv _ := Eq.symm <| lift_unique rfl rfl

@[to_additive (attr := simp)]
/-
**Monoid.Coprod.mrange_lift** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：mrange_lift (f : M ->* P) (g : N ->* P) : MonoidHom.mrange (lift f g) = Mo
noidHom.mrange f ⊔ MonoidHom.mrange g
参数：f : M ->* P；g : N ->* P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.Coprod.mrange_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_5} 
[inst : MulOneClass M] [inst_1 : MulOneClass N] [inst_2 : MulOneClass P]   (f : 
Monoid.Coprod…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mrange_lift (f : M →* P) (g : N →* P) :
    MonoidHom.mrange (lift f g) = MonoidHom.mrange f ⊔ MonoidHom.mrange g := by
  simp [mrange_eq]

end Lift

section ToProd

variable {M N : Type*} [Monoid M] [Monoid N]

/-
**Monoid.Coprod.** 是 Mathlib 中的一个实例，位于命名空间 `Monoid.Coprod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance : Monoid (M ∗ N) :=
  { mul_assoc := (Con.monoid _).mul_assoc
    one_mul := (Con.monoid _).one_mul
    mul_one := (Con.monoid _).mul_one }

/-- The natural projection `M ∗ N →* M`. -/
@[to_additive /-- The natural projection `AddMonoid.Coprod M N →+ M`. -/]
/-
**Monoid.Coprod.fst** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.Coprod`。
形式化陈述：fst : M ∗ N ->* M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural projection `M ∗ N →* M`.
-/
def fst : M ∗ N →* M := lift (.id M) 1

/-- The natural projection `M ∗ N →* N`. -/
@[to_additive /-- The natural projection `AddMonoid.Coprod M N →+ N`. -/]
/-
**Monoid.Coprod.snd** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.Coprod`。
形式化陈述：snd : M ∗ N ->* N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural projection `M ∗ N →* N`.
-/
def snd : M ∗ N →* N := lift 1 (.id N)

/-- The natural projection `M ∗ N →* M × N`. -/
@[to_additive toProd /-- The natural projection `AddMonoid.Coprod M N →+ M × N`. -/]
/-
**Monoid.Coprod.toProd** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.Coprod`。
形式化陈述：toProd : M ∗ N ->* M × N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural projection `M ∗ N →* M × N`.
-/
def toProd : M ∗ N →* M × N := lift (.inl _ _) (.inr _ _)
/-
**Monoid.Coprod.fst_comp_inl** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} [inst : Monoid M] [inst_1 : Monoid N],   M
onoid.Coprod.fst.comp Monoid.Coprod.inl = MonoidHom.id M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] theorem fst_comp_inl : (fst : M ∗ N →* M).comp inl = .id _ := rfl
/-
**Monoid.Coprod.fst_apply_inl** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} [inst : Monoid M] [inst_1 : Monoid N] (x :
 M),   Monoid.Coprod.fst (Monoid.Coprod.inl x) = x
参数：x : M；Monoid.Coprod.inl x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] theorem fst_apply_inl (x : M) : fst (inl x : M ∗ N) = x := rfl
/-
**Monoid.Coprod.fst_comp_inr** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} [inst : Monoid M] [inst_1 : Monoid N], Mon
oid.Coprod.fst.comp Monoid.Coprod.inr = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] theorem fst_comp_inr : (fst : M ∗ N →* M).comp inr = 1 := rfl
/-
**Monoid.Coprod.fst_apply_inr** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} [inst : Monoid M] [inst_1 : Monoid N] (x :
 N),   Monoid.Coprod.fst (Monoid.Coprod.inr x) = 1
参数：x : N；Monoid.Coprod.inr x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] theorem fst_apply_inr (x : N) : fst (inr x : M ∗ N) = 1 := rfl
/-
**Monoid.Coprod.snd_comp_inl** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} [inst : Monoid M] [inst_1 : Monoid N], Mon
oid.Coprod.snd.comp Monoid.Coprod.inl = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] theorem snd_comp_inl : (snd : M ∗ N →* N).comp inl = 1 := rfl
/-
**Monoid.Coprod.snd_apply_inl** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} [inst : Monoid M] [inst_1 : Monoid N] (x :
 M),   Monoid.Coprod.snd (Monoid.Coprod.inl x) = 1
参数：x : M；Monoid.Coprod.inl x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] theorem snd_apply_inl (x : M) : snd (inl x : M ∗ N) = 1 := rfl
/-
**Monoid.Coprod.snd_comp_inr** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} [inst : Monoid M] [inst_1 : Monoid N],   M
onoid.Coprod.snd.comp Monoid.Coprod.inr = MonoidHom.id N
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] theorem snd_comp_inr : (snd : M ∗ N →* N).comp inr = .id _ := rfl
/-
**Monoid.Coprod.snd_apply_inr** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} [inst : Monoid M] [inst_1 : Monoid N] (x :
 N),   Monoid.Coprod.snd (Monoid.Coprod.inr x) = x
参数：x : N；Monoid.Coprod.inr x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] theorem snd_apply_inr (x : N) : snd (inr x : M ∗ N) = x := rfl

@[to_additive (attr := simp) toProd_comp_inl]
/-
**Monoid.Coprod.toProd_comp_inl** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：toProd_comp_inl : (toProd : M ∗ N ->* M × N).comp inl = .inl _ _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toProd_comp_inl : (toProd : M ∗ N →* M × N).comp inl = .inl _ _ := rfl

@[to_additive (attr := simp) toProd_comp_inr]
/-
**Monoid.Coprod.toProd_comp_inr** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：toProd_comp_inr : (toProd : M ∗ N ->* M × N).comp inr = .inr _ _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toProd_comp_inr : (toProd : M ∗ N →* M × N).comp inr = .inr _ _ := rfl

@[to_additive (attr := simp) toProd_apply_inl]
/-
**Monoid.Coprod.toProd_apply_inl** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：toProd_apply_inl (x : M) : toProd (inl x : M ∗ N) = (x, 1)
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toProd_apply_inl (x : M) : toProd (inl x : M ∗ N) = (x, 1) := rfl

@[to_additive (attr := simp) toProd_apply_inr]
/-
**Monoid.Coprod.toProd_apply_inr** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：toProd_apply_inr (x : N) : toProd (inr x : M ∗ N) = (1, x)
参数：x : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toProd_apply_inr (x : N) : toProd (inr x : M ∗ N) = (1, x) := rfl

@[to_additive (attr := simp) fst_prod_snd]
/-
**Monoid.Coprod.fst_prod_snd** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：fst_prod_snd : (fst : M ∗ N ->* M).prod snd = toProd
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.Coprod.hom_ext`：hom_ext {f g : M ∗ N ->* P} (h₁ : f.comp inl = g.
comp inl) (h₂ : f.comp inr = g.comp inr) : f = g
-/
theorem fst_prod_snd : (fst : M ∗ N →* M).prod snd = toProd := by ext1 <;> rfl

@[to_additive (attr := simp) prod_mk_fst_snd]
/-
**Monoid.Coprod.prod_mk_fst_snd** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：prod_mk_fst_snd (x : M ∗ N) : (fst x, snd x) = toProd x
参数：x : M ∗ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monoid.Coprod.fst_prod_snd`：fst_prod_snd : (fst : M ∗ N ->* M).prod snd 
= toProd
· 使用定理 `MonoidHom.prod_apply`：prod_apply (f : M ->* N) (g : M ->* P) (x) : f.pro
d g x = (f x, g x)
-/
theorem prod_mk_fst_snd (x : M ∗ N) : (fst x, snd x) = toProd x := by
  rw [← fst_prod_snd, MonoidHom.prod_apply]

@[to_additive (attr := simp) fst_comp_toProd]
/-
**Monoid.Coprod.fst_comp_toProd** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：fst_comp_toProd : (MonoidHom.fst M N).comp toProd = fst
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monoid.Coprod.fst_prod_snd`：fst_prod_snd : (fst : M ∗ N ->* M).prod snd 
= toProd
· 使用定理 `MonoidHom.fst_comp_prod`：fst_comp_prod (f : M ->* N) (g : M ->* P) : (fs
t N P).comp (f.prod g) = f
-/
theorem fst_comp_toProd : (MonoidHom.fst M N).comp toProd = fst := by
  rw [← fst_prod_snd, MonoidHom.fst_comp_prod]

@[to_additive (attr := simp) fst_toProd]
/-
**Monoid.Coprod.fst_toProd** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：fst_toProd (x : M ∗ N) : (toProd x).1 = fst x
参数：x : M ∗ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monoid.Coprod.fst_comp_toProd`：fst_comp_toProd : (MonoidHom.fst M N).com
p toProd = fst
-/
theorem fst_toProd (x : M ∗ N) : (toProd x).1 = fst x := by
  rw [← fst_comp_toProd]; rfl

@[to_additive (attr := simp) snd_comp_toProd]
/-
**Monoid.Coprod.snd_comp_toProd** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：snd_comp_toProd : (MonoidHom.snd M N).comp toProd = snd
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monoid.Coprod.fst_prod_snd`：fst_prod_snd : (fst : M ∗ N ->* M).prod snd 
= toProd
· 使用定理 `MonoidHom.snd_comp_prod`：snd_comp_prod (f : M ->* N) (g : M ->* P) : (sn
d N P).comp (f.prod g) = g
-/
theorem snd_comp_toProd : (MonoidHom.snd M N).comp toProd = snd := by
  rw [← fst_prod_snd, MonoidHom.snd_comp_prod]

@[to_additive (attr := simp) snd_toProd]
/-
**Monoid.Coprod.snd_toProd** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：snd_toProd (x : M ∗ N) : (toProd x).2 = snd x
参数：x : M ∗ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monoid.Coprod.snd_comp_toProd`：snd_comp_toProd : (MonoidHom.snd M N).com
p toProd = snd
-/
theorem snd_toProd (x : M ∗ N) : (toProd x).2 = snd x := by
  rw [← snd_comp_toProd]; rfl

@[to_additive (attr := simp)]
/-
**Monoid.Coprod.fst_comp_swap** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：fst_comp_swap : fst.comp (swap M N) = snd
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.Coprod.lift_comp_swap`：lift_comp_swap (f : M ->* P) (g : N ->* P)
 : (lift f g).comp (swap N M) = lift g f
-/
theorem fst_comp_swap : fst.comp (swap M N) = snd := lift_comp_swap _ _

@[to_additive (attr := simp)]
/-
**Monoid.Coprod.fst_swap** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：fst_swap (x : M ∗ N) : fst (swap M N x) = snd x
参数：x : M ∗ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.Coprod.lift_swap`：lift_swap (f : M ->* P) (g : N ->* P) (x : N ∗ 
M) : lift f g (swap N M x) = lift g f x
-/
theorem fst_swap (x : M ∗ N) : fst (swap M N x) = snd x := lift_swap _ _ _

@[to_additive (attr := simp)]
/-
**Monoid.Coprod.snd_comp_swap** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：snd_comp_swap : snd.comp (swap M N) = fst
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.Coprod.lift_comp_swap`：lift_comp_swap (f : M ->* P) (g : N ->* P)
 : (lift f g).comp (swap N M) = lift g f
-/
theorem snd_comp_swap : snd.comp (swap M N) = fst := lift_comp_swap _ _

@[to_additive (attr := simp)]
/-
**Monoid.Coprod.snd_swap** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：snd_swap (x : M ∗ N) : snd (swap M N x) = fst x
参数：x : M ∗ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.Coprod.lift_swap`：lift_swap (f : M ->* P) (g : N ->* P) (x : N ∗ 
M) : lift f g (swap N M x) = lift g f x
-/
theorem snd_swap (x : M ∗ N) : snd (swap M N x) = fst x := lift_swap _ _ _

@[to_additive (attr := simp)]
/-
**Monoid.Coprod.lift_inr_inl** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：lift_inr_inl : lift (inr : M ->* N ∗ M) inl = swap M N
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.Coprod.hom_ext`：hom_ext {f g : M ∗ N ->* P} (h₁ : f.comp inl = g.
comp inl) (h₂ : f.comp inr = g.comp inr) : f = g
-/
theorem lift_inr_inl : lift (inr : M →* N ∗ M) inl = swap M N := hom_ext rfl rfl

@[to_additive (attr := simp)]
/-
**Monoid.Coprod.lift_inl_inr** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：lift_inl_inr : lift (inl : M ->* M ∗ N) inr = .id _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.Coprod.hom_ext`：hom_ext {f g : M ∗ N ->* P} (h₁ : f.comp inl = g.
comp inl) (h₂ : f.comp inr = g.comp inr) : f = g
-/
theorem lift_inl_inr : lift (inl : M →* M ∗ N) inr = .id _ := hom_ext rfl rfl

@[to_additive]
/-
**Monoid.Coprod.inl_injective** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：inl_injective : Injective (inl : M ->* M ∗ N)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `Monoid.Coprod.fst_apply_inl`：∀ {M : Type u_1} {N : Type u_2} [inst : Mon
oid M] [inst_1 : Monoid N] (x : M),   Monoid.Coprod.fst (Monoid.Coprod.inl x) = 
x
-/
theorem inl_injective : Injective (inl : M →* M ∗ N) := LeftInverse.injective fst_apply_inl

@[to_additive]
/-
**Monoid.Coprod.inr_injective** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：inr_injective : Injective (inr : N ->* M ∗ N)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `Monoid.Coprod.snd_apply_inr`：∀ {M : Type u_1} {N : Type u_2} [inst : Mon
oid M] [inst_1 : Monoid N] (x : N),   Monoid.Coprod.snd (Monoid.Coprod.inr x) = 
x
-/
theorem inr_injective : Injective (inr : N →* M ∗ N) := LeftInverse.injective snd_apply_inr

@[to_additive]
/-
**Monoid.Coprod.fst_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：fst_surjective : Surjective (fst : M ∗ N ->* M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.LeftInverse f g → Function.Surjective f
· 使用定理 `Monoid.Coprod.fst_apply_inl`：∀ {M : Type u_1} {N : Type u_2} [inst : Mon
oid M] [inst_1 : Monoid N] (x : M),   Monoid.Coprod.fst (Monoid.Coprod.inl x) = 
x
-/
theorem fst_surjective : Surjective (fst : M ∗ N →* M) := LeftInverse.surjective fst_apply_inl

@[to_additive]
/-
**Monoid.Coprod.snd_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：snd_surjective : Surjective (snd : M ∗ N ->* N)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.LeftInverse f g → Function.Surjective f
· 使用定理 `Monoid.Coprod.snd_apply_inr`：∀ {M : Type u_1} {N : Type u_2} [inst : Mon
oid M] [inst_1 : Monoid N] (x : N),   Monoid.Coprod.snd (Monoid.Coprod.inr x) = 
x
-/
theorem snd_surjective : Surjective (snd : M ∗ N →* N) := LeftInverse.surjective snd_apply_inr

@[to_additive toProd_surjective]
/-
**Monoid.Coprod.toProd_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：toProd_surjective : Surjective (toProd : M ∗ N ->* M × N)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Monoid.Coprod.toProd_apply_inl`：toProd_apply_inl (x : M) : toProd (inl x
 : M ∗ N) = (x, 1)
· 使用定理 `Monoid.Coprod.toProd_apply_inr`：toProd_apply_inr (x : N) : toProd (inr x
 : M ∗ N) = (1, x)
· 使用定理 `Prod.fst_mul_snd`：fst_mul_snd [MulOneClass M] [MulOneClass N] (p : M × N
) : (p.fst, 1) * (1, p.snd) = p
-/
theorem toProd_surjective : Surjective (toProd : M ∗ N →* M × N) := fun x =>
  ⟨inl x.1 * inr x.2, by rw [map_mul, toProd_apply_inl, toProd_apply_inr, Prod.fst_mul_snd]⟩

end ToProd

section Group

variable {G H : Type*} [Group G] [Group H]

@[to_additive]
/-
**Monoid.Coprod.mk_of_inv_mul** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：∀ {G : Type u_1} {H : Type u_2} [inst : Group G] [inst_1 : Group H] (x : G
 ⊕ H),   Monoid.Coprod.mk (FreeMonoid.of (Sum.map Inv.inv Inv.inv x)) * Monoid.C
oprod.mk (FreeMonoid.of x) = 1
参数：x : G ⊕ H；FreeMonoid.of (Sum.map Inv.inv Inv.inv x)；FreeMonoid.of x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_mul_eq_one`：map_mul_eq_one [MonoidHomClass F M N] (f : F) {a b : M} 
(h : a * b = 1) : f a * f b = 1
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
-/
theorem mk_of_inv_mul : ∀ x : G ⊕ H, mk (of (x.map Inv.inv Inv.inv)) * mk (of x) = 1
  | Sum.inl _ => map_mul_eq_one inl (inv_mul_cancel _)
  | Sum.inr _ => map_mul_eq_one inr (inv_mul_cancel _)

@[to_additive]
/-
**Monoid.Coprod.con_inv_mul_cancel** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：con_inv_mul_cancel (x : FreeMonoid (G oplus H)) : coprodCon G H (ofList (x
.toList.map (Sum.map Inv.inv Inv.inv)).reverse * x) 1
参数：x : FreeMonoid (G oplus H)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monoid.Coprod.mk_eq_mk`：mk_eq_mk {w₁ w₂ : FreeMonoid (M oplus N)} : mk w
₁ = mk w₂ ↔ coprodCon M N w₁ w₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `FreeMonoid.inductionOn'`：∀ {α : Type u_1} {motive : FreeMonoid α → Prop}
 (a : FreeMonoid α),   motive 1 → (∀ (b : α) (a : FreeMonoid α), motive a → moti
ve (FreeMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Monoid.Coprod.mk_of_inv_mul`：∀ {G : Type u_1} {H : Type u_2} [inst : Gro
up G] [inst_1 : Group H] (x : G ⊕ H),   Monoid.Coprod.mk (FreeMonoid.of (Sum.map
 Inv.inv Inv.inv …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem con_inv_mul_cancel (x : FreeMonoid (G ⊕ H)) :
    coprodCon G H (ofList (x.toList.map (Sum.map Inv.inv Inv.inv)).reverse * x) 1 := by
  rw [← mk_eq_mk, map_mul, map_one]
  induction x using FreeMonoid.inductionOn' with
  | one => simp
  | of_mul x xs ihx =>
    simp only [toList_of_mul, map_cons, reverse_cons, ofList_append, map_mul, ofList_singleton]
    rwa [mul_assoc, ← mul_assoc (mk (of _)), mk_of_inv_mul, one_mul]

@[to_additive]
/-
**Monoid.Coprod.** 是 Mathlib 中的一个实例，位于命名空间 `Monoid.Coprod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inv (G ∗ H) where
  inv := Quotient.map' (fun w => ofList (w.toList.map (Sum.map Inv.inv Inv.inv)).reverse) fun _ _ ↦
    (coprodCon G H).map_of_mul_left_rel_one _ con_inv_mul_cancel

@[to_additive]
/-
**Monoid.Coprod.inv_def** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：inv_def (w : FreeMonoid (G oplus H)) : (mk w)⁻¹ = mk (ofList (w.toList.map
 (Sum.map Inv.inv Inv.inv)).reverse)
参数：w : FreeMonoid (G oplus H)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_def (w : FreeMonoid (G ⊕ H)) :
    (mk w)⁻¹ = mk (ofList (w.toList.map (Sum.map Inv.inv Inv.inv)).reverse) :=
  rfl

@[to_additive]
/-
**Monoid.Coprod.** 是 Mathlib 中的一个实例，位于命名空间 `Monoid.Coprod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Group (G ∗ H) where
  inv_mul_cancel := mk_surjective.forall.2 fun x => mk_eq_mk.2 (con_inv_mul_cancel x)

@[to_additive (attr := simp)]
/-
**Monoid.Coprod.closure_range_inl_union_inr** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Co
prod`。
形式化陈述：closure_range_inl_union_inr : Subgroup.closure (range (inl : G ->* G ∗ H) 
union range inr) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.closure_eq_top_of_mclosure_eq_top`：closure_eq_top_of_mclosure_e
q_top {S : Set G} (h : Submonoid.closure S = ⊤) : closure S = ⊤
· 使用定理 `Monoid.Coprod.mclosure_range_inl_union_inr`：mclosure_range_inl_union_inr
 : Submonoid.closure (range (inl : M ->* M ∗ N) union range (inr : N ->* M ∗ N))
 = ⊤
-/
theorem closure_range_inl_union_inr :
    Subgroup.closure (range (inl : G →* G ∗ H) ∪ range inr) = ⊤ :=
  Subgroup.closure_eq_top_of_mclosure_eq_top mclosure_range_inl_union_inr
/-
**Monoid.Coprod.range_inl_sup_range_inr** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod
`。
形式化陈述：∀ {G : Type u_1} {H : Type u_2} [inst : Group G] [inst_1 : Group H],   Mon
oid.Coprod.inl.range ⊔ Monoid.Coprod.inr.range = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monoid.Coprod.closure_range_inl_union_inr`：closure_range_inl_union_inr :
 Subgroup.closure (range (inl : G ->* G ∗ H) union range inr) = ⊤
· 使用定理 `Subgroup.closure_union`：closure_union (s t : Set G) : closure (s union t
) = closure s ⊔ closure t
· 使用定理 `MonoidHom.coe_range`：coe_range (f : G ->* N) : (f.range : Set N) = Set.r
ange f
· 使用定理 `Subgroup.closure_eq`：closure_eq : closure (K : Set G) = K
-/
@[to_additive (attr := simp)] theorem range_inl_sup_range_inr :
    MonoidHom.range (inl : G →* G ∗ H) ⊔ MonoidHom.range inr = ⊤ := by
  rw [← closure_range_inl_union_inr, Subgroup.closure_union, ← MonoidHom.coe_range,
    ← MonoidHom.coe_range, Subgroup.closure_eq, Subgroup.closure_eq]

@[to_additive]
/-
**Monoid.Coprod.codisjoint_range_inl_range_inr** 是 Mathlib 中的一个定理，位于命名空间 `Monoid
.Coprod`。
形式化陈述：codisjoint_range_inl_range_inr : Codisjoint (MonoidHom.range (inl : G ->* 
G ∗ H)) (MonoidHom.range inr)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `codisjoint_iff`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : Ord
erTop α] {a b : α}, Codisjoint a b ↔ a ⊔ b = ⊤
· 使用定理 `Monoid.Coprod.range_inl_sup_range_inr`：∀ {G : Type u_1} {H : Type u_2} [
inst : Group G] [inst_1 : Group H],   Monoid.Coprod.inl.range ⊔ Monoid.Coprod.in
r.range = ⊤
-/
theorem codisjoint_range_inl_range_inr :
    Codisjoint (MonoidHom.range (inl : G →* G ∗ H)) (MonoidHom.range inr) :=
  codisjoint_iff.2 range_inl_sup_range_inr
/-
**Monoid.Coprod.range_swap** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：∀ {G : Type u_1} {H : Type u_2} [inst : Group G] [inst_1 : Group H], (Mono
id.Coprod.swap G H).range = ⊤
参数：Monoid.Coprod.swap G H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MonoidHom.range_eq_top`：range_eq_top {N} [Group N] {f : G ->* N} : f.ran
ge = (⊤ : Subgroup N) ↔ Function.Surjective f
· 使用定理 `Monoid.Coprod.swap_surjective`：swap_surjective : Surjective (swap M N)
-/
@[to_additive (attr := simp)] theorem range_swap : MonoidHom.range (swap G H) = ⊤ :=
  MonoidHom.range_eq_top.2 swap_surjective

variable {K : Type*} [Group K]
/-
**Monoid.Coprod.range_eq** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：∀ {G : Type u_1} {H : Type u_2} [inst : Group G] [inst_1 : Group H] {K : T
ype u_3} [inst_2 : Group K]   (f : Monoid.Coprod G H →* K), f.range = (f.comp Mo
noid.Coprod.inl).range ⊔ (f.comp Monoid.Coprod.inr).range
参数：f : Monoid.Coprod G H →* K；f.comp Monoid.Coprod.inl；f.comp Monoid.Coprod.inr。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.range_eq_map`：range_eq_map (f : G ->* N) : f.range = (⊤ : Subg
roup G).map f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monoid.Coprod.range_inl_sup_range_inr`：∀ {G : Type u_1} {H : Type u_2} [
inst : Group G] [inst_1 : Group H],   Monoid.Coprod.inl.range ⊔ Monoid.Coprod.in
r.range = ⊤
· 使用定理 `Subgroup.map_sup`：map_sup (H K : Subgroup G) (f : G ->* N) : (H ⊔ K).map
 f = H.map f ⊔ K.map f
· 使用定理 `MonoidHom.map_range`：map_range (g : N ->* P) (f : G ->* N) : f.range.map
 g = (g.comp f).range
-/
@[to_additive] theorem range_eq (f : G ∗ H →* K) :
    MonoidHom.range f = MonoidHom.range (f.comp inl) ⊔ MonoidHom.range (f.comp inr) := by
  rw [MonoidHom.range_eq_map, ← range_inl_sup_range_inr, Subgroup.map_sup, MonoidHom.map_range,
    MonoidHom.map_range]
/-
**Monoid.Coprod.range_lift** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Coprod`。
形式化陈述：∀ {G : Type u_1} {H : Type u_2} [inst : Group G] [inst_1 : Group H] {K : T
ype u_3} [inst_2 : Group K] (f : G →* K)   (g : H →* K), (Monoid.Coprod.lift f g
).range = f.range ⊔ g.range
参数：f : G →* K；g : H →* K；Monoid.Coprod.lift f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.Coprod.range_eq`：∀ {G : Type u_1} {H : Type u_2} [inst : Group G]
 [inst_1 : Group H] {K : Type u_3} [inst_2 : Group K]   (f : Monoid.Coprod G H →
* K), f.rang…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[to_additive (attr := simp)] theorem range_lift (f : G →* K) (g : H →* K) :
    MonoidHom.range (lift f g) = MonoidHom.range f ⊔ MonoidHom.range g := by
  simp [range_eq]

end Group

end Monoid.Coprod

open Monoid Coprod

namespace MulEquiv

section MulOneClass

variable {M N M' N' : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass M']
  [MulOneClass N']

/-- Lift two monoid equivalences `e : M ≃* N` and `e' : M' ≃* N'` to a monoid equivalence
`(M ∗ M') ≃* (N ∗ N')`. -/
@[to_additive (attr := simps! -fullyApplied) /-- Lift two additive monoid
equivalences `e : M ≃+ N` and `e' : M' ≃+ N'` to an additive monoid equivalence
`(AddMonoid.Coprod M M') ≃+ (AddMonoid.Coprod N N')`. -/]
/-
**MulEquiv.coprodCongr** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：{M : Type u_1} →   {N : Type u_2} →     {M' : Type u_3} →       {N' : Type
 u_4} →         [inst : MulOneClass M] →           [inst_1 : MulOneClass N] →   
          [inst_2 : MulOneClass M'] →               [inst_3 : MulOneClass N'] → 
M ≃* N → M' ≃* N' → Monoid.Coprod M M' ≃* Monoid.Coprod N N'
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def coprodCongr (e : M ≃* N) (e' : M' ≃* N') : (M ∗ M') ≃* (N ∗ N') :=
  (Coprod.map (e : M →* N) (e' : M' →* N')).toMulEquiv (Coprod.map e.symm e'.symm)
    (by ext <;> simp) (by ext <;> simp)

variable (M N)

/-- A `MulEquiv` version of `Coprod.swap`. -/
@[to_additive (attr := simps! -fullyApplied)
  /-- An `AddEquiv` version of `AddMonoid.Coprod.swap`. -/]
/-
**MulEquiv.coprodComm** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：(M : Type u_1) →   (N : Type u_2) → [inst : MulOneClass M] → [inst_1 : Mul
OneClass N] → Monoid.Coprod M N ≃* Monoid.Coprod N M
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.Coprod.swap_comp_swap`：swap_comp_swap : (swap M N).comp (swap N M
) = .id _
-/
def coprodComm : M ∗ N ≃* N ∗ M :=
  (Coprod.swap _ _).toMulEquiv (Coprod.swap _ _) (Coprod.swap_comp_swap _ _)
    (Coprod.swap_comp_swap _ _)

end MulOneClass

variable (M N P : Type*) [Monoid M] [Monoid N] [Monoid P]

/-- A multiplicative equivalence between `(M ∗ N) ∗ P` and `M ∗ (N ∗ P)`. -/
@[to_additive /-- An additive equivalence between `AddMonoid.Coprod (AddMonoid.Coprod M N) P` and
`AddMonoid.Coprod M (AddMonoid.Coprod N P)`. -/]
/-
**MulEquiv.coprodAssoc** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：(M : Type u_1) →   (N : Type u_2) →     (P : Type u_3) →       [inst : Mon
oid M] →         [inst_1 : Monoid N] →           [inst_2 : Monoid P] → Monoid.Co
prod (Monoid.Coprod M N) P ≃* Monoid.Coprod M (Monoid.Coprod N P)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def coprodAssoc : (M ∗ N) ∗ P ≃* M ∗ (N ∗ P) :=
  MonoidHom.toMulEquiv
    (Coprod.lift (Coprod.map (.id M) inl) (inr.comp inr))
    (Coprod.lift (inl.comp inl) (Coprod.map inr (.id P)))
    (by ext <;> rfl) (by ext <;> rfl)

variable {M N P}

@[to_additive (attr := simp)]
/-
**MulEquiv.coprodAssoc_apply_inl_inl** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} [inst : Monoid M] [inst_1 :
 Monoid N] [inst_2 : Monoid P] (x : M),   (MulEquiv.coprodAssoc M N P) (Monoid.C
oprod.inl (Monoid.Coprod.inl x)) = Monoid.Coprod.inl x
参数：x : M；MulEquiv.coprodAssoc M N P；Monoid.Coprod.inl (Monoid.Coprod.inl x)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coprodAssoc_apply_inl_inl (x : M) : coprodAssoc M N P (inl (inl x)) = inl x := rfl

@[to_additive (attr := simp)]
/-
**MulEquiv.coprodAssoc_apply_inl_inr** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} [inst : Monoid M] [inst_1 :
 Monoid N] [inst_2 : Monoid P] (x : N),   (MulEquiv.coprodAssoc M N P) (Monoid.C
oprod.inl (Monoid.Coprod.inr x)) = Monoid.Coprod.inr (Monoid.Coprod.inl x)
参数：x : N；MulEquiv.coprodAssoc M N P；Monoid.Coprod.inl (Monoid.Coprod.inr x)；Mono
id.Coprod.inl x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coprodAssoc_apply_inl_inr (x : N) : coprodAssoc M N P (inl (inr x)) = inr (inl x) := rfl

@[to_additive (attr := simp)]
/-
**MulEquiv.coprodAssoc_apply_inr** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} [inst : Monoid M] [inst_1 :
 Monoid N] [inst_2 : Monoid P] (x : P),   (MulEquiv.coprodAssoc M N P) (Monoid.C
oprod.inr x) = Monoid.Coprod.inr (Monoid.Coprod.inr x)
参数：x : P；MulEquiv.coprodAssoc M N P；Monoid.Coprod.inr x；Monoid.Coprod.inr x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coprodAssoc_apply_inr (x : P) : coprodAssoc M N P (inr x) = inr (inr x) := rfl

@[to_additive (attr := simp)]
/-
**MulEquiv.coprodAssoc_symm_apply_inl** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} [inst : Monoid M] [inst_1 :
 Monoid N] [inst_2 : Monoid P] (x : M),   (MulEquiv.coprodAssoc M N P).symm (Mon
oid.Coprod.inl x) = Monoid.Coprod.inl (Monoid.Coprod.inl x)
参数：x : M；MulEquiv.coprodAssoc M N P；Monoid.Coprod.inl x；Monoid.Coprod.inl x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coprodAssoc_symm_apply_inl (x : M) : (coprodAssoc M N P).symm (inl x) = inl (inl x) :=
  rfl

@[to_additive (attr := simp)]
/-
**MulEquiv.coprodAssoc_symm_apply_inr_inl** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} [inst : Monoid M] [inst_1 :
 Monoid N] [inst_2 : Monoid P] (x : N),   (MulEquiv.coprodAssoc M N P).symm (Mon
oid.Coprod.inr (Monoid.Coprod.inl x)) = Monoid.Coprod.inl (Monoid.Coprod.inr x)
参数：x : N；MulEquiv.coprodAssoc M N P；Monoid.Coprod.inr (Monoid.Coprod.inl x)；Mono
id.Coprod.inr x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coprodAssoc_symm_apply_inr_inl (x : N) :
    (coprodAssoc M N P).symm (inr (inl x)) = inl (inr x) :=
  rfl

@[to_additive (attr := simp)]
/-
**MulEquiv.coprodAssoc_symm_apply_inr_inr** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} [inst : Monoid M] [inst_1 :
 Monoid N] [inst_2 : Monoid P] (x : P),   (MulEquiv.coprodAssoc M N P).symm (Mon
oid.Coprod.inr (Monoid.Coprod.inr x)) = Monoid.Coprod.inr x
参数：x : P；MulEquiv.coprodAssoc M N P；Monoid.Coprod.inr (Monoid.Coprod.inr x)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coprodAssoc_symm_apply_inr_inr (x : P) :
    (coprodAssoc M N P).symm (inr (inr x)) = inr x :=
  rfl

variable (M)

/-- Isomorphism between `M ∗ PUnit` and `M`. -/
@[to_additive (attr := simps! -fullyApplied)
  /-- Isomorphism between `AddMonoid.Coprod M PUnit` and `M`. -/]
/-
**MulEquiv.coprodPUnit** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：(M : Type u_1) → [inst : Monoid M] → Monoid.Coprod M PUnit.{u_4 + 1} ≃* M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def coprodPUnit : M ∗ PUnit ≃* M :=
  MonoidHom.toMulEquiv fst inl (hom_ext rfl <| Subsingleton.elim _ _) fst_comp_inl

/-- Isomorphism between `PUnit ∗ M` and `M`. -/
@[to_additive (attr := simps! -fullyApplied)
  /-- Isomorphism between `AddMonoid.Coprod PUnit M` and `M`. -/]
/-
**MulEquiv.punitCoprod** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：(M : Type u_1) → [inst : Monoid M] → Monoid.Coprod PUnit.{u_4 + 1} M ≃* M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def punitCoprod : PUnit ∗ M ≃* M :=
  MonoidHom.toMulEquiv snd inr (hom_ext (Subsingleton.elim _ _) rfl) snd_comp_inr

end MulEquiv

