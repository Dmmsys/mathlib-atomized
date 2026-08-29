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
/--
Definition of `coprodCon` / `coprodCon` 的定义

English:
definition coprodCon
  signature: (M N : Type*) [MulOneClass M] [MulOneClass N]
  body: sInf {c |
    (forall x y : M, c (of (Sum.inl (x * y))) (of (Sum.inl x) * of (Sum.inl y)))
    ∧ (forall x y : N, c (of (Sum.inr (x * y))) (of (Sum.inr x) * of (Sum.inr y)))
    ∧ c (of <| Sum.inl 1) 1 ∧ c (of <| Sum.inr 1) 1}

中文:
定义 coprodCon
  签名: (M N : 类型) [MulOne类 M] [MulOne类 N]
  定义体: sInf {c |
    (forall x y : M, c (of (Sum.inl (x * y))) (of (Sum.inl x) * of (Sum.inl y)))
    ∧ (forall x y : N, c (of (Sum.inr (x * y))) (of (Sum.inr x) * of (Sum.inr y)))
    ∧ c (of <| Sum.inl 1) 1 ∧ c (of <| Sum.inr 1) 1}

Depends on / 依赖: Sum.inl, Sum.inr
-/
def coprodCon (M N : Type*) [MulOneClass M] [MulOneClass N] : Con (FreeMonoid (M oplus N)) :=
  sInf {c |
    (forall x y : M, c (of (Sum.inl (x * y))) (of (Sum.inl x) * of (Sum.inl y)))
    ∧ (forall x y : N, c (of (Sum.inr (x * y))) (of (Sum.inr x) * of (Sum.inr y)))
    ∧ c (of <| Sum.inl 1) 1 ∧ c (of <| Sum.inr 1) 1}

/-- Coproduct of two monoids or groups. -/
@[to_additive /-- Coproduct of two additive monoids or groups. -/]
/--
Definition of `Coprod` / `Coprod` 的定义

English:
definition Coprod
  signature: (M N : Type*) [MulOneClass M] [MulOneClass N]
  body: (coprodCon M N).Quotient

中文:
定义 Coprod
  签名: (M N : 类型) [MulOne类 M] [MulOne类 N]
  定义体: (coprodCon M N).Quotient

Depends on / 依赖: B.toMatrix, _toLin, toMatrix
-/
def Coprod (M N : Type*) [MulOneClass M] [MulOneClass N] := (coprodCon M N).Quotient

namespace Coprod

@[inherit_doc]
scoped infix:30 " ∗ " => Coprod

section MulOneClass

variable {M N M' N' P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass M'] [MulOneClass N']
  [MulOneClass P]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulOneClass (M ∗ N)
  body: inferInstanceAs MulOneClass (coprodCon M N).Quotient

中文:
实例 :
  签名: MulOne类 (M ∗ N)
  定义体: inferInstanceAs MulOneClass (coprodCon M N).Quotient

Depends on / 依赖: LinearMap, LinearMap.toMatrix, injective
-/
@[to_additive] protected instance : MulOneClass (M ∗ N) :=
inferInstanceAs MulOneClass (coprodCon M N).Quotient

/-- The natural projection `FreeMonoid (M ⊕ N) →* M ∗ N`. -/
@[to_additive /-- The natural projection `FreeAddMonoid (M ⊕ N) →+ AddMonoid.Coprod M N`. -/]
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: : FreeMonoid (M oplus N) ->* M ∗ N
  body: Con.mk' _

@[to_additive (attr := simp)]

中文:
定义 mk
  签名: : 自由幺半群 (M oplus N) ->* M ∗ N
  定义体: Con.mk' _

@[to_additive (attr := simp)]

Depends on / 依赖: Con.mk
-/
def mk : FreeMonoid (M oplus N) ->* M ∗ N := Con.mk' _

@[to_additive (attr := simp)]
/--
theorem `con_ker_mk` / 定理 `con_ker_mk`

English:
theorem con_ker_mk
  statement: Con.ker mk = coprodCon M N
  proof: Con.mk'_ker _

@[to_additive]

中文:
定理 con_ker_mk
  结论: Con.ker mk = coprodCon M N
  证明: Con.mk'_ker _

@[to_additive]

Depends on / 依赖: Con.mk, _ker
-/
theorem con_ker_mk : Con.ker mk = coprodCon M N := Con.mk'_ker _

@[to_additive]
/--
theorem `mk_surjective` / 定理 `mk_surjective`

English:
theorem mk_surjective
  statement: Surjective (@mk M N _ _)
  proof: Quot.mk_surjective

@[to_additive (attr := simp)]

中文:
定理 mk_surjective
  结论: 满射 (@mk M N _ _)
  证明: Quot.mk_surjective

@[to_additive (attr := simp)]

Depends on / 依赖: Quot.mk_surjective, mk_surjective
-/
theorem mk_surjective : Surjective (@mk M N _ _) := Quot.mk_surjective

@[to_additive (attr := simp)]
/--
theorem `mrange_mk` / 定理 `mrange_mk`

English:
theorem mrange_mk
  statement: MonoidHom.mrange (@mk M N _ _) = ⊤
  proof: Con.mrange_mk'

@[to_additive]

中文:
定理 mrange_mk
  结论: 幺半群态射.mrange (@mk M N _ _) = ⊤
  证明: Con.mrange_mk'

@[to_additive]

Depends on / 依赖: Con.mrange_mk, mrange_mk
-/
theorem mrange_mk : MonoidHom.mrange (@mk M N _ _) = ⊤ := Con.mrange_mk'

@[to_additive]
/--
theorem `mk_eq_mk` / 定理 `mk_eq_mk`

English:
theorem mk_eq_mk
  given: {w₁ w₂ : FreeMonoid (M oplus N)}
  statement: mk w₁ = mk w₂ ↔ coprodCon M N w₁ w₂
  proof: Con.eq _

中文:
定理 mk_eq_mk
  条件: {w₁ w₂ : 自由幺半群 (M oplus N)}
  结论: mk w₁ = mk w₂ ↔ coprodCon M N w₁ w₂
  证明: Con.eq _

Depends on / 依赖: Con.eq
-/
theorem mk_eq_mk {w₁ w₂ : FreeMonoid (M oplus N)} : mk w₁ = mk w₂ ↔ coprodCon M N w₁ w₂ := Con.eq _

/-- The natural embedding `M →* M ∗ N`. -/
@[to_additive /-- The natural embedding `M →+ AddMonoid.Coprod M N`. -/]
/--
Definition of `inl` / `inl` 的定义

English:
definition inl
  signature: : M ->* M ∗ N where
  body: fun x => mk (of (.inl x))
  map_one' := mk_eq_mk.2 fun _c hc => hc.2.2.1
  map_mul' := fun x y => mk_eq_mk.2 fun _c hc => hc.1 x y

中文:
定义 inl
  签名: : M ->* M ∗ N where
  定义体: fun x => mk (of (.inl x))
  map_one' := mk_eq_mk.2 fun _c hc => hc.2.2.1
  map_mul' := fun x y => mk_eq_mk.2 fun _c hc => hc.1 x y
-/
def inl : M ->* M ∗ N where
  toFun := fun x => mk (of (.inl x))
  map_one' := mk_eq_mk.2 fun _c hc => hc.2.2.1
  map_mul' := fun x y => mk_eq_mk.2 fun _c hc => hc.1 x y

/-- The natural embedding `N →* M ∗ N`. -/
@[to_additive /-- The natural embedding `N →+ AddMonoid.Coprod M N`. -/]
/--
Definition of `inr` / `inr` 的定义

English:
definition inr
  signature: : N ->* M ∗ N where
  body: fun x => mk (of (.inr x))
  map_one' := mk_eq_mk.2 fun _c hc => hc.2.2.2
  map_mul' := fun x y => mk_eq_mk.2 fun _c hc => hc.2.1 x y

@[to_additive (attr := simp)]

中文:
定义 inr
  签名: : N ->* M ∗ N where
  定义体: fun x => mk (of (.inr x))
  map_one' := mk_eq_mk.2 fun _c hc => hc.2.2.2
  map_mul' := fun x y => mk_eq_mk.2 fun _c hc => hc.2.1 x y

@[to_additive (attr := simp)]
-/
def inr : N ->* M ∗ N where
  toFun := fun x => mk (of (.inr x))
  map_one' := mk_eq_mk.2 fun _c hc => hc.2.2.2
  map_mul' := fun x y => mk_eq_mk.2 fun _c hc => hc.2.1 x y

@[to_additive (attr := simp)]
/--
theorem `mk_of_inl` / 定理 `mk_of_inl`

English:
theorem mk_of_inl
  given: (x : M)
  statement: (mk (of (.inl x)) : M ∗ N) = inl x
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 mk_of_inl
  条件: (x : M)
  结论: (mk (of (.inl x)) : M ∗ N) = inl x
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem mk_of_inl (x : M) : (mk (of (.inl x)) : M ∗ N) = inl x := rfl

@[to_additive (attr := simp)]
/--
theorem `mk_of_inr` / 定理 `mk_of_inr`

English:
theorem mk_of_inr
  given: (x : N)
  statement: (mk (of (.inr x)) : M ∗ N) = inr x
  proof: rfl

@[to_additive (attr := elab_as_elim)]

中文:
定理 mk_of_inr
  条件: (x : N)
  结论: (mk (of (.inr x)) : M ∗ N) = inr x
  证明: rfl

@[to_additive (attr := elab_as_elim)]
-/
theorem mk_of_inr (x : N) : (mk (of (.inr x)) : M ∗ N) = inr x := rfl

@[to_additive (attr := elab_as_elim)]
/--
theorem `induction_on'` / 定理 `induction_on'`

English:
theorem induction_on'
  statement: {motive : M ∗ N -> Prop} (m : M ∗ N)
  proof: by
  rcases mk_surjective m with ⟨x, rfl⟩
  induction x using FreeMonoid.inductionOn' with
  | one => exact one
  | of_mul x xs ih =>
    cases x with
    | inl m => simpa using inl_mul m _ ih
    | inr n => simpa using inr_mul n _ ih

@[to_additive (attr := elab_as_elim)]

中文:
定理 induction_on'
  结论: {motive : M ∗ N -> 命题} (m : M ∗ N)
  证明: by
  rcases mk_surjective m with ⟨x, rfl⟩
  induction x using FreeMonoid.inductionOn' with
  | one => exact one
  | of_mul x xs ih =>
    cases x with
    | inl m => simpa using inl_mul m _ ih
    | inr n => simpa using inr_mul n _ ih

@[to_additive (attr := elab_as_elim)]

Depends on / 依赖: FreeMonoid, FreeMonoid.inductionOn, inductionOn, inl_mul, inr_mul, mk_surjective, of_mul
-/
theorem induction_on' {motive : M ∗ N -> Prop} (m : M ∗ N)
    (one : motive 1)
    (inl_mul : forall m x, motive x -> motive (inl m * x))
    (inr_mul : forall n x, motive x -> motive (inr n * x)) : motive m := by
  rcases mk_surjective m with ⟨x, rfl⟩
  induction x using FreeMonoid.inductionOn' with
  | one => exact one
  | of_mul x xs ih =>
    cases x with
    | inl m => simpa using inl_mul m _ ih
    | inr n => simpa using inr_mul n _ ih

@[to_additive (attr := elab_as_elim)]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  statement: {motive : M ∗ N -> Prop} (m : M ∗ N)
  proof: induction_on' m (by simpa using inl 1) (fun _ _ => mul _ _ (inl _)) fun _ _ => mul _ _ (inr _)

中文:
定理 induction_on
  结论: {motive : M ∗ N -> 命题} (m : M ∗ N)
  证明: induction_on' m (by simpa using inl 1) (fun _ _ => mul _ _ (inl _)) fun _ _ => mul _ _ (inr _)

Depends on / 依赖: induction_on
-/
theorem induction_on {motive : M ∗ N -> Prop} (m : M ∗ N)
    (inl : forall m, motive (inl m)) (inr : forall n, motive (inr n))
    (mul : forall x y, motive x -> motive y -> motive (x * y)) : motive m :=
  induction_on' m (by simpa using inl 1) (fun _ _ => mul _ _ (inl _)) fun _ _ => mul _ _ (inr _)

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
/--
Definition of `clift` / `clift` 的定义

English:
definition clift
  signature: (f : FreeMonoid (M oplus N) ->* P)
  body: Con.lift _ f sInf_le ⟨hM, hN, hM₁.trans (map_one f).symm, hN₁.trans (map_one f).symm⟩

@[to_additive (attr := simp)]

中文:
定义 clift
  签名: (f : 自由幺半群 (M oplus N) ->* P)
  定义体: Con.lift _ f sInf_le ⟨hM, hN, hM₁.trans (map_one f).symm, hN₁.trans (map_one f).symm⟩

@[to_additive (attr := simp)]

Depends on / 依赖: Con.lift, map_one, sInf_le
-/
def clift (f : FreeMonoid (M oplus N) ->* P)
    (hM₁ : f (of (.inl 1)) = 1) (hN₁ : f (of (.inr 1)) = 1)
    (hM : forall x y, f (of (.inl (x * y))) = f (of (.inl x) * of (.inl y)))
    (hN : forall x y, f (of (.inr (x * y))) = f (of (.inr x) * of (.inr y))) :
    M ∗ N ->* P :=
Con.lift _ f sInf_le ⟨hM, hN, hM₁.trans (map_one f).symm, hN₁.trans (map_one f).symm⟩

@[to_additive (attr := simp)]
/--
theorem `clift_apply_inl` / 定理 `clift_apply_inl`

English:
theorem clift_apply_inl
  given: (f : FreeMonoid (M oplus N) ->* P) (hM₁ hN₁ hM hN) (x : M)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 clift_apply_inl
  条件: (f : 自由幺半群 (M oplus N) ->* P) (hM₁ hN₁ hM hN) (x : M)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem clift_apply_inl (f : FreeMonoid (M oplus N) ->* P) (hM₁ hN₁ hM hN) (x : M) :
    clift f hM₁ hN₁ hM hN (inl x) = f (of (.inl x)) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `clift_apply_inr` / 定理 `clift_apply_inr`

English:
theorem clift_apply_inr
  given: (f : FreeMonoid (M oplus N) ->* P) (hM₁ hN₁ hM hN) (x : N)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 clift_apply_inr
  条件: (f : 自由幺半群 (M oplus N) ->* P) (hM₁ hN₁ hM hN) (x : N)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem clift_apply_inr (f : FreeMonoid (M oplus N) ->* P) (hM₁ hN₁ hM hN) (x : N) :
    clift f hM₁ hN₁ hM hN (inr x) = f (of (.inr x)) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `clift_apply_mk` / 定理 `clift_apply_mk`

English:
theorem clift_apply_mk
  given: (f : FreeMonoid (M oplus N) ->* P) (hM₁ hN₁ hM hN w)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 clift_apply_mk
  条件: (f : 自由幺半群 (M oplus N) ->* P) (hM₁ hN₁ hM hN w)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem clift_apply_mk (f : FreeMonoid (M oplus N) ->* P) (hM₁ hN₁ hM hN w) :
    clift f hM₁ hN₁ hM hN (mk w) = f w :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `clift_comp_mk` / 定理 `clift_comp_mk`

English:
theorem clift_comp_mk
  given: (f : FreeMonoid (M oplus N) ->* P) (hM₁ hN₁ hM hN)
  proof: DFunLike.ext' rfl

@[to_additive (attr := simp)]

中文:
定理 clift_comp_mk
  条件: (f : 自由幺半群 (M oplus N) ->* P) (hM₁ hN₁ hM hN)
  证明: DFunLike.ext' rfl

@[to_additive (attr := simp)]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem clift_comp_mk (f : FreeMonoid (M oplus N) ->* P) (hM₁ hN₁ hM hN) :
    (clift f hM₁ hN₁ hM hN).comp mk = f :=
  DFunLike.ext' rfl

@[to_additive (attr := simp)]
/--
theorem `mclosure_range_inl_union_inr` / 定理 `mclosure_range_inl_union_inr`

English:
theorem mclosure_range_inl_union_inr
  proof: by
  rw [← mrange_mk]; rw [MonoidHom.mrange_eq_map]; rw [← closure_range_of]; rw [MonoidHom.map_mclosure]; rw [← range_comp]; rw [Sum.range_eq]; rfl

中文:
定理 mclosure_range_inl_union_inr
  证明: by
  rw [← mrange_mk]; rw [MonoidHom.mrange_eq_map]; rw [← closure_range_of]; rw [MonoidHom.map_mclosure]; rw [← range_comp]; rw [Sum.range_eq]; rfl

Depends on / 依赖: MonoidHom, MonoidHom.map_mclosure, MonoidHom.mrange_eq_map, Sum.range_eq, closure_range_of, map_mclosure, mrange_eq_map, mrange_mk, range_comp, range_eq
-/
theorem mclosure_range_inl_union_inr :
    Submonoid.closure (range (inl : M ->* M ∗ N) union range (inr : N ->* M ∗ N)) = ⊤ := by
  rw [← mrange_mk]; rw [MonoidHom.mrange_eq_map]; rw [← closure_range_of]; rw [MonoidHom.map_mclosure]; rw [← range_comp]; rw [Sum.range_eq]; rfl

/--
theorem `mrange_inl_sup_mrange_inr` / 定理 `mrange_inl_sup_mrange_inr`

English:
theorem mrange_inl_sup_mrange_inr
  proof: by
  rw [← mclosure_range_inl_union_inr]; rw [Submonoid.closure_union]; rw [← MonoidHom.coe_mrange]; rw [← MonoidHom.coe_mrange]; rw [Submonoid.closure_eq]; rw [Submonoid.closure_eq]

@[to_additive]

中文:
定理 mrange_inl_sup_mrange_inr
  证明: by
  rw [← mclosure_range_inl_union_inr]; rw [Submonoid.closure_union]; rw [← MonoidHom.coe_mrange]; rw [← MonoidHom.coe_mrange]; rw [Submonoid.closure_eq]; rw [Submonoid.closure_eq]

@[to_additive]
-/
@[to_additive (attr := simp)] theorem mrange_inl_sup_mrange_inr :
    MonoidHom.mrange (inl : M ->* M ∗ N) ⊔ MonoidHom.mrange (inr : N ->* M ∗ N) = ⊤ := by
  rw [← mclosure_range_inl_union_inr]; rw [Submonoid.closure_union]; rw [← MonoidHom.coe_mrange]; rw [← MonoidHom.coe_mrange]; rw [Submonoid.closure_eq]; rw [Submonoid.closure_eq]

@[to_additive]
/--
theorem `codisjoint_mrange_inl_mrange_inr` / 定理 `codisjoint_mrange_inl_mrange_inr`

English:
theorem codisjoint_mrange_inl_mrange_inr
  proof: codisjoint_iff.2 mrange_inl_sup_mrange_inr

中文:
定理 codisjoint_mrange_inl_mrange_inr
  证明: codisjoint_iff.2 mrange_inl_sup_mrange_inr

Depends on / 依赖: codisjoint_iff, mrange_inl_sup_mrange_inr
-/
theorem codisjoint_mrange_inl_mrange_inr :
    Codisjoint (MonoidHom.mrange (inl : M ->* M ∗ N)) (MonoidHom.mrange inr) :=
  codisjoint_iff.2 mrange_inl_sup_mrange_inr

/--
theorem `mrange_eq` / 定理 `mrange_eq`

English:
theorem mrange_eq
  given: (f : M ∗ N ->* P)
  proof: by
  rw [MonoidHom.mrange_eq_map]; rw [← mrange_inl_sup_mrange_inr]; rw [Submonoid.map_sup]; rw [MonoidHom.map_mrange]; rw [MonoidHom.map_mrange]

中文:
定理 mrange_eq
  条件: (f : M ∗ N ->* P)
  证明: by
  rw [MonoidHom.mrange_eq_map]; rw [← mrange_inl_sup_mrange_inr]; rw [Submonoid.map_sup]; rw [MonoidHom.map_mrange]; rw [MonoidHom.map_mrange]
-/
@[to_additive] theorem mrange_eq (f : M ∗ N ->* P) :
    MonoidHom.mrange f = MonoidHom.mrange (f.comp inl) ⊔ MonoidHom.mrange (f.comp inr) := by
  rw [MonoidHom.mrange_eq_map]; rw [← mrange_inl_sup_mrange_inr]; rw [Submonoid.map_sup]; rw [MonoidHom.map_mrange]; rw [MonoidHom.map_mrange]

/-- Extensionality lemma for monoid homomorphisms `M ∗ N →* P`.
If two homomorphisms agree on the ranges of `Monoid.Coprod.inl` and `Monoid.Coprod.inr`,
then they are equal. -/
@[to_additive (attr := ext 1100)
  /-- Extensionality lemma for additive monoid homomorphisms `AddMonoid.Coprod M N →+ P`.
  If two homomorphisms agree on the ranges of `AddMonoid.Coprod.inl` and `AddMonoid.Coprod.inr`,
  then they are equal. -/]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  given: {f g : M ∗ N ->* P} (h₁ : f.comp inl = g.comp inl) (h₂ : f.comp inr = g.comp inr)
  proof: MonoidHom.eq_of_eqOn_denseM mclosure_range_inl_union_inr eqOn_union.2
⟨eqOn_range.2 DFunLike.ext'_iff.1 h₁, eqOn_range.2 DFunLike.ext'_iff.1 h₂⟩

@[to_additive (attr := simp)]

中文:
定理 hom_ext
  条件: {f g : M ∗ N ->* P} (h₁ : f.comp inl = g.comp inl) (h₂ : f.comp inr = g.comp inr)
  证明: MonoidHom.eq_of_eqOn_denseM mclosure_range_inl_union_inr eqOn_union.2
⟨eqOn_range.2 DFunLike.ext'_iff.1 h₁, eqOn_range.2 DFunLike.ext'_iff.1 h₂⟩

@[to_additive (attr := simp)]

Depends on / 依赖: DFunLike, DFunLike.ext, MonoidHom, MonoidHom.eq_of_eqOn_denseM, _iff, eqOn_range, eqOn_union, eq_of_eqOn_denseM, mclosure_range_inl_union_inr
-/
theorem hom_ext {f g : M ∗ N ->* P} (h₁ : f.comp inl = g.comp inl) (h₂ : f.comp inr = g.comp inr) :
    f = g :=
MonoidHom.eq_of_eqOn_denseM mclosure_range_inl_union_inr eqOn_union.2
⟨eqOn_range.2 DFunLike.ext'_iff.1 h₁, eqOn_range.2 DFunLike.ext'_iff.1 h₂⟩

@[to_additive (attr := simp)]
/--
theorem `clift_mk` / 定理 `clift_mk`

English:
theorem clift_mk
  proof: hom_ext rfl rfl

中文:
定理 clift_mk
  证明: hom_ext rfl rfl

Depends on / 依赖: hom_ext
-/
theorem clift_mk :
    clift (mk : FreeMonoid (M oplus N) ->* M ∗ N) (map_one inl) (map_one inr) (map_mul inl)
      (map_mul inr) = .id _ :=
  hom_ext rfl rfl

/-- Map `M ∗ N` to `M' ∗ N'` by applying `Sum.map f g` to each element of the underlying list. -/
@[to_additive /-- Map `AddMonoid.Coprod M N` to `AddMonoid.Coprod M' N'`
by applying `Sum.map f g` to each element of the underlying list. -/]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : M ->* M') (g : N ->* N')
  body: clift (mk.comp <| FreeMonoid.map <| Sum.map f g)
    (by simp only [MonoidHom.comp_apply, map_of, Sum.map_inl, map_one, mk_of_inl])
    (by simp only [MonoidHom.comp_apply, map_of, Sum.map_inr, map_one, mk_of_inr])
    (fun x y => by simp only [MonoidHom.comp_apply, map_of, Sum.map_inl, map_mul, mk_of_inl])
    fun x y => by simp only [MonoidHom.comp_apply, map_of, Sum.map_inr, map_mul, mk_of_inr]

@[to_additive (attr := simp)]

中文:
定义 map
  签名: (f : M ->* M') (g : N ->* N')
  定义体: clift (mk.comp <| FreeMonoid.map <| Sum.map f g)
    (by simp only [MonoidHom.comp_apply, map_of, Sum.map_inl, map_one, mk_of_inl])
    (by simp only [MonoidHom.comp_apply, map_of, Sum.map_inr, map_one, mk_of_inr])
    (fun x y => by simp only [MonoidHom.comp_apply, map_of, Sum.map_inl, map_mul, mk_of_inl])
    fun x y => by simp only [MonoidHom.comp_apply, map_of, Sum.map_inr, map_mul, mk_of_inr]

@[to_additive (attr := simp)]

Depends on / 依赖: FreeMonoid, FreeMonoid.map, MonoidHom, MonoidHom.comp_apply, Sum.map, Sum.map_inl, Sum.map_inr, comp_apply, map_inl, map_inr, map_mul, map_of, map_one, mk.comp, mk_of_inl, mk_of_inr
-/
def map (f : M ->* M') (g : N ->* N') : M ∗ N ->* M' ∗ N' :=
  clift (mk.comp <| FreeMonoid.map <| Sum.map f g)
    (by simp only [MonoidHom.comp_apply, map_of, Sum.map_inl, map_one, mk_of_inl])
    (by simp only [MonoidHom.comp_apply, map_of, Sum.map_inr, map_one, mk_of_inr])
    (fun x y => by simp only [MonoidHom.comp_apply, map_of, Sum.map_inl, map_mul, mk_of_inl])
    fun x y => by simp only [MonoidHom.comp_apply, map_of, Sum.map_inr, map_mul, mk_of_inr]

@[to_additive (attr := simp)]
/--
theorem `map_mk_ofList` / 定理 `map_mk_ofList`

English:
theorem map_mk_ofList
  given: (f : M ->* M') (g : N ->* N') (l : List (M oplus N))
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 map_mk_ofList
  条件: (f : M ->* M') (g : N ->* N') (l : 列表 (M oplus N))
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem map_mk_ofList (f : M ->* M') (g : N ->* N') (l : List (M oplus N)) :
    map f g (mk (ofList l)) = mk (ofList (l.map (Sum.map f g))) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `map_apply_inl` / 定理 `map_apply_inl`

English:
theorem map_apply_inl
  given: (f : M ->* M') (g : N ->* N') (x : M)
  statement: map f g (inl x) = inl (f x)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 map_apply_inl
  条件: (f : M ->* M') (g : N ->* N') (x : M)
  结论: map f g (inl x) = inl (f x)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem map_apply_inl (f : M ->* M') (g : N ->* N') (x : M) : map f g (inl x) = inl (f x) := rfl

@[to_additive (attr := simp)]
/--
theorem `map_apply_inr` / 定理 `map_apply_inr`

English:
theorem map_apply_inr
  given: (f : M ->* M') (g : N ->* N') (x : N)
  statement: map f g (inr x) = inr (g x)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 map_apply_inr
  条件: (f : M ->* M') (g : N ->* N') (x : N)
  结论: map f g (inr x) = inr (g x)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem map_apply_inr (f : M ->* M') (g : N ->* N') (x : N) : map f g (inr x) = inr (g x) := rfl

@[to_additive (attr := simp)]
/--
theorem `map_comp_inl` / 定理 `map_comp_inl`

English:
theorem map_comp_inl
  given: (f : M ->* M') (g : N ->* N')
  statement: (map f g).comp inl = inl.comp f
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 map_comp_inl
  条件: (f : M ->* M') (g : N ->* N')
  结论: (map f g).comp inl = inl.comp f
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem map_comp_inl (f : M ->* M') (g : N ->* N') : (map f g).comp inl = inl.comp f := rfl

@[to_additive (attr := simp)]
/--
theorem `map_comp_inr` / 定理 `map_comp_inr`

English:
theorem map_comp_inr
  given: (f : M ->* M') (g : N ->* N')
  statement: (map f g).comp inr = inr.comp g
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 map_comp_inr
  条件: (f : M ->* M') (g : N ->* N')
  结论: (map f g).comp inr = inr.comp g
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem map_comp_inr (f : M ->* M') (g : N ->* N') : (map f g).comp inr = inr.comp g := rfl

@[to_additive (attr := simp)]
/--
theorem `map_id_id` / 定理 `map_id_id`

English:
theorem map_id_id
  statement: map (.id M) (.id N) = .id (M ∗ N)
  proof: hom_ext rfl rfl

@[to_additive]

中文:
定理 map_id_id
  结论: map (.id M) (.id N) = .id (M ∗ N)
  证明: hom_ext rfl rfl

@[to_additive]

Depends on / 依赖: hom_ext
-/
theorem map_id_id : map (.id M) (.id N) = .id (M ∗ N) := hom_ext rfl rfl

@[to_additive]
/--
theorem `map_comp_map` / 定理 `map_comp_map`

English:
theorem map_comp_map
  statement: {M'' N''} [MulOneClass M''] [MulOneClass N''] (f' : M' ->* M'') (g' : N' ->* N'')
  proof: hom_ext rfl rfl

@[to_additive]

中文:
定理 map_comp_map
  结论: {M'' N''} [MulOne类 M''] [MulOne类 N''] (f' : M' ->* M'') (g' : N' ->* N'')
  证明: hom_ext rfl rfl

@[to_additive]

Depends on / 依赖: hom_ext
-/
theorem map_comp_map {M'' N''} [MulOneClass M''] [MulOneClass N''] (f' : M' ->* M'') (g' : N' ->* N'')
    (f : M ->* M') (g : N ->* N') : (map f' g').comp (map f g) = map (f'.comp f) (g'.comp g) :=
  hom_ext rfl rfl

@[to_additive]
/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  statement: {M'' N''} [MulOneClass M''] [MulOneClass N''] (f' : M' ->* M'') (g' : N' ->* N'')
  proof: DFunLike.congr_fun (map_comp_map f' g' f g) x

中文:
定理 map_map
  结论: {M'' N''} [MulOne类 M''] [MulOne类 N''] (f' : M' ->* M'') (g' : N' ->* N'')
  证明: DFunLike.congr_fun (map_comp_map f' g' f g) x

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, map_comp_map
-/
theorem map_map {M'' N''} [MulOneClass M''] [MulOneClass N''] (f' : M' ->* M'') (g' : N' ->* N'')
    (f : M ->* M') (g : N ->* N') (x : M ∗ N) :
    map f' g' (map f g x) = map (f'.comp f) (g'.comp g) x :=
  DFunLike.congr_fun (map_comp_map f' g' f g) x

variable (M N)

/-- Map `M ∗ N` to `N ∗ M` by applying `Sum.swap` to each element of the underlying list.

See also `MulEquiv.coprodComm` for a `MulEquiv` version. -/
@[to_additive /-- Map `AddMonoid.Coprod M N` to `AddMonoid.Coprod N M`
  by applying `Sum.swap` to each element of the underlying list.

See also `AddEquiv.coprodComm` for an `AddEquiv` version. -/]
/--
Definition of `swap` / `swap` 的定义

English:
definition swap
  signature: : M ∗ N ->* N ∗ M
  body: clift (mk.comp <| FreeMonoid.map Sum.swap)
    (by simp only [MonoidHom.comp_apply, map_of, Sum.swap_inl, mk_of_inr, map_one])
    (by simp only [MonoidHom.comp_apply, map_of, Sum.swap_inr, mk_of_inl, map_one])
    (fun x y => by simp only [MonoidHom.comp_apply, map_of, Sum.swap_inl, mk_of_inr, map_mul])
    (fun x y => by simp only [MonoidHom.comp_apply, map_of, Sum.swap_inr, mk_of_inl, map_mul])

@[to_additive (attr := simp)]

中文:
定义 swap
  签名: : M ∗ N ->* N ∗ M
  定义体: clift (mk.comp <| FreeMonoid.map Sum.swap)
    (by simp only [MonoidHom.comp_apply, map_of, Sum.swap_inl, mk_of_inr, map_one])
    (by simp only [MonoidHom.comp_apply, map_of, Sum.swap_inr, mk_of_inl, map_one])
    (fun x y => by simp only [MonoidHom.comp_apply, map_of, Sum.swap_inl, mk_of_inr, map_mul])
    (fun x y => by simp only [MonoidHom.comp_apply, map_of, Sum.swap_inr, mk_of_inl, map_mul])

@[to_additive (attr := simp)]

Depends on / 依赖: FreeMonoid, FreeMonoid.map, MonoidHom, MonoidHom.comp_apply, Sum.swap, Sum.swap_inl, Sum.swap_inr, comp_apply, map_mul, map_of, map_one, mk.comp, mk_of_inl, mk_of_inr, swap_inl, swap_inr
-/
def swap : M ∗ N ->* N ∗ M :=
  clift (mk.comp <| FreeMonoid.map Sum.swap)
    (by simp only [MonoidHom.comp_apply, map_of, Sum.swap_inl, mk_of_inr, map_one])
    (by simp only [MonoidHom.comp_apply, map_of, Sum.swap_inr, mk_of_inl, map_one])
    (fun x y => by simp only [MonoidHom.comp_apply, map_of, Sum.swap_inl, mk_of_inr, map_mul])
    (fun x y => by simp only [MonoidHom.comp_apply, map_of, Sum.swap_inr, mk_of_inl, map_mul])

@[to_additive (attr := simp)]
/--
theorem `swap_comp_swap` / 定理 `swap_comp_swap`

English:
theorem swap_comp_swap
  statement: (swap M N).comp (swap N M) = .id _
  proof: hom_ext rfl rfl

中文:
定理 swap_comp_swap
  结论: (swap M N).comp (swap N M) = .id _
  证明: hom_ext rfl rfl

Depends on / 依赖: hom_ext
-/
theorem swap_comp_swap : (swap M N).comp (swap N M) = .id _ := hom_ext rfl rfl

variable {M N}

@[to_additive (attr := simp)]
/--
theorem `swap_swap` / 定理 `swap_swap`

English:
theorem swap_swap
  given: (x : M ∗ N)
  statement: swap N M (swap M N x) = x
  proof: DFunLike.congr_fun (swap_comp_swap _ _) x

@[to_additive]

中文:
定理 swap_swap
  条件: (x : M ∗ N)
  结论: swap N M (swap M N x) = x
  证明: DFunLike.congr_fun (swap_comp_swap _ _) x

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, swap_comp_swap
-/
theorem swap_swap (x : M ∗ N) : swap N M (swap M N x) = x :=
  DFunLike.congr_fun (swap_comp_swap _ _) x

@[to_additive]
/--
theorem `swap_comp_map` / 定理 `swap_comp_map`

English:
theorem swap_comp_map
  given: (f : M ->* M') (g : N ->* N')
  proof: hom_ext rfl rfl

@[to_additive]

中文:
定理 swap_comp_map
  条件: (f : M ->* M') (g : N ->* N')
  证明: hom_ext rfl rfl

@[to_additive]

Depends on / 依赖: hom_ext
-/
theorem swap_comp_map (f : M ->* M') (g : N ->* N') :
    (swap M' N').comp (map f g) = (map g f).comp (swap M N) :=
  hom_ext rfl rfl

@[to_additive]
/--
theorem `swap_map` / 定理 `swap_map`

English:
theorem swap_map
  given: (f : M ->* M') (g : N ->* N') (x : M ∗ N)
  proof: DFunLike.congr_fun (swap_comp_map f g) x

中文:
定理 swap_map
  条件: (f : M ->* M') (g : N ->* N') (x : M ∗ N)
  证明: DFunLike.congr_fun (swap_comp_map f g) x

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, swap_comp_map
-/
theorem swap_map (f : M ->* M') (g : N ->* N') (x : M ∗ N) :
    swap M' N' (map f g x) = map g f (swap M N x) :=
  DFunLike.congr_fun (swap_comp_map f g) x

/--
theorem `swap_comp_inl` / 定理 `swap_comp_inl`

English:
theorem swap_comp_inl
  statement: (swap M N).comp inl = inr
  proof: rfl

中文:
定理 swap_comp_inl
  结论: (swap M N).comp inl = inr
  证明: rfl
-/
@[to_additive (attr := simp)] theorem swap_comp_inl : (swap M N).comp inl = inr := rfl
/--
theorem `swap_inl` / 定理 `swap_inl`

English:
theorem swap_inl
  given: (x : M)
  statement: swap M N (inl x) = inr x
  proof: rfl

中文:
定理 swap_inl
  条件: (x : M)
  结论: swap M N (inl x) = inr x
  证明: rfl
-/
@[to_additive (attr := simp)] theorem swap_inl (x : M) : swap M N (inl x) = inr x := rfl
/--
theorem `swap_comp_inr` / 定理 `swap_comp_inr`

English:
theorem swap_comp_inr
  statement: (swap M N).comp inr = inl
  proof: rfl

中文:
定理 swap_comp_inr
  结论: (swap M N).comp inr = inl
  证明: rfl
-/
@[to_additive (attr := simp)] theorem swap_comp_inr : (swap M N).comp inr = inl := rfl
/--
theorem `swap_inr` / 定理 `swap_inr`

English:
theorem swap_inr
  given: (x : N)
  statement: swap M N (inr x) = inl x
  proof: rfl

@[to_additive]

中文:
定理 swap_inr
  条件: (x : N)
  结论: swap M N (inr x) = inl x
  证明: rfl

@[to_additive]
-/
@[to_additive (attr := simp)] theorem swap_inr (x : N) : swap M N (inr x) = inl x := rfl

@[to_additive]
/--
theorem `swap_injective` / 定理 `swap_injective`

English:
theorem swap_injective
  statement: Injective (swap M N)
  proof: LeftInverse.injective swap_swap

@[to_additive (attr := simp)]

中文:
定理 swap_injective
  结论: 单射 (swap M N)
  证明: LeftInverse.injective swap_swap

@[to_additive (attr := simp)]

Depends on / 依赖: LeftInverse, LeftInverse.injective, injective, swap_swap
-/
theorem swap_injective : Injective (swap M N) := LeftInverse.injective swap_swap

@[to_additive (attr := simp)]
/--
theorem `swap_inj` / 定理 `swap_inj`

English:
theorem swap_inj
  given: {x y : M ∗ N}
  statement: swap M N x = swap M N y ↔ x = y
  proof: swap_injective.eq_iff

@[to_additive (attr := simp)]

中文:
定理 swap_inj
  条件: {x y : M ∗ N}
  结论: swap M N x = swap M N y ↔ x = y
  证明: swap_injective.eq_iff

@[to_additive (attr := simp)]

Depends on / 依赖: eq_iff, swap_injective, swap_injective.eq_iff
-/
theorem swap_inj {x y : M ∗ N} : swap M N x = swap M N y ↔ x = y := swap_injective.eq_iff

@[to_additive (attr := simp)]
/--
theorem `swap_eq_one` / 定理 `swap_eq_one`

English:
theorem swap_eq_one
  given: {x : M ∗ N}
  statement: swap M N x = 1 ↔ x = 1
  proof: swap_injective.eq_iff' (map_one _)

@[to_additive]

中文:
定理 swap_eq_one
  条件: {x : M ∗ N}
  结论: swap M N x = 1 ↔ x = 1
  证明: swap_injective.eq_iff' (map_one _)

@[to_additive]

Depends on / 依赖: eq_iff, map_one, swap_injective, swap_injective.eq_iff
-/
theorem swap_eq_one {x : M ∗ N} : swap M N x = 1 ↔ x = 1 := swap_injective.eq_iff' (map_one _)

@[to_additive]
/--
theorem `swap_surjective` / 定理 `swap_surjective`

English:
theorem swap_surjective
  statement: Surjective (swap M N)
  proof: LeftInverse.surjective swap_swap

@[to_additive]

中文:
定理 swap_surjective
  结论: 满射 (swap M N)
  证明: LeftInverse.surjective swap_swap

@[to_additive]

Depends on / 依赖: LeftInverse, LeftInverse.surjective, surjective, swap_swap
-/
theorem swap_surjective : Surjective (swap M N) := LeftInverse.surjective swap_swap

@[to_additive]
/--
theorem `swap_bijective` / 定理 `swap_bijective`

English:
theorem swap_bijective
  statement: Bijective (swap M N)
  proof: ⟨swap_injective, swap_surjective⟩

@[to_additive (attr := simp)]

中文:
定理 swap_bijective
  结论: 双射 (swap M N)
  证明: ⟨swap_injective, swap_surjective⟩

@[to_additive (attr := simp)]

Depends on / 依赖: swap_injective, swap_surjective
-/
theorem swap_bijective : Bijective (swap M N) := ⟨swap_injective, swap_surjective⟩

@[to_additive (attr := simp)]
/--
theorem `mker_swap` / 定理 `mker_swap`

English:
theorem mker_swap
  statement: MonoidHom.mker (swap M N) = ⊥
  proof: Submonoid.ext fun _ => swap_eq_one

@[to_additive (attr := simp)]

中文:
定理 mker_swap
  结论: 幺半群态射.mker (swap M N) = ⊥
  证明: Submonoid.ext fun _ => swap_eq_one

@[to_additive (attr := simp)]

Depends on / 依赖: Submonoid, Submonoid.ext, swap_eq_one
-/
theorem mker_swap : MonoidHom.mker (swap M N) = ⊥ := Submonoid.ext fun _ => swap_eq_one

@[to_additive (attr := simp)]
/--
theorem `mrange_swap` / 定理 `mrange_swap`

English:
theorem mrange_swap
  statement: MonoidHom.mrange (swap M N) = ⊤
  proof: MonoidHom.mrange_eq_top_of_surjective _ swap_surjective

中文:
定理 mrange_swap
  结论: 幺半群态射.mrange (swap M N) = ⊤
  证明: MonoidHom.mrange_eq_top_of_surjective _ swap_surjective

Depends on / 依赖: MonoidHom, MonoidHom.mrange_eq_top_of_surjective, mrange_eq_top_of_surjective, swap_surjective
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
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (f : M ->* P) (g : N ->* P)
  body: clift (FreeMonoid.lift <| Sum.elim f g) (map_one f) (map_one g) (map_mul f) (map_mul g)

@[to_additive (attr := simp)]

中文:
定义 lift
  签名: (f : M ->* P) (g : N ->* P)
  定义体: clift (FreeMonoid.lift <| Sum.elim f g) (map_one f) (map_one g) (map_mul f) (map_mul g)

@[to_additive (attr := simp)]

Depends on / 依赖: FreeMonoid, FreeMonoid.lift, Sum.elim, map_mul, map_one
-/
def lift (f : M ->* P) (g : N ->* P) : (M ∗ N) ->* P :=
  clift (FreeMonoid.lift <| Sum.elim f g) (map_one f) (map_one g) (map_mul f) (map_mul g)

@[to_additive (attr := simp)]
/--
theorem `lift_apply_mk` / 定理 `lift_apply_mk`

English:
theorem lift_apply_mk
  given: (f : M ->* P) (g : N ->* P) (x : FreeMonoid (M oplus N))
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 lift_apply_mk
  条件: (f : M ->* P) (g : N ->* P) (x : 自由幺半群 (M oplus N))
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem lift_apply_mk (f : M ->* P) (g : N ->* P) (x : FreeMonoid (M oplus N)) :
    lift f g (mk x) = FreeMonoid.lift (Sum.elim f g) x :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `lift_apply_inl` / 定理 `lift_apply_inl`

English:
theorem lift_apply_inl
  given: (f : M ->* P) (g : N ->* P) (x : M)
  statement: lift f g (inl x) = f x
  proof: rfl

@[to_additive]

中文:
定理 lift_apply_inl
  条件: (f : M ->* P) (g : N ->* P) (x : M)
  结论: lift f g (inl x) = f x
  证明: rfl

@[to_additive]
-/
theorem lift_apply_inl (f : M ->* P) (g : N ->* P) (x : M) : lift f g (inl x) = f x :=
  rfl

@[to_additive]
/--
theorem `lift_unique` / 定理 `lift_unique`

English:
theorem lift_unique
  statement: {f : M ->* P} {g : N ->* P} {fg : M ∗ N ->* P} (h₁ : fg.comp inl = f)
  proof: hom_ext h₁ h₂

@[to_additive (attr := simp)]

中文:
定理 lift_unique
  结论: {f : M ->* P} {g : N ->* P} {fg : M ∗ N ->* P} (h₁ : fg.comp inl = f)
  证明: hom_ext h₁ h₂

@[to_additive (attr := simp)]

Depends on / 依赖: hom_ext
-/
theorem lift_unique {f : M ->* P} {g : N ->* P} {fg : M ∗ N ->* P} (h₁ : fg.comp inl = f)
    (h₂ : fg.comp inr = g) : fg = lift f g :=
  hom_ext h₁ h₂

@[to_additive (attr := simp)]
/--
theorem `lift_comp_inl` / 定理 `lift_comp_inl`

English:
theorem lift_comp_inl
  given: (f : M ->* P) (g : N ->* P)
  statement: (lift f g).comp inl = f
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 lift_comp_inl
  条件: (f : M ->* P) (g : N ->* P)
  结论: (lift f g).comp inl = f
  证明: rfl

@[to_additive (attr := simp)]

Depends on / 依赖: SeparatingLeft
-/
theorem lift_comp_inl (f : M ->* P) (g : N ->* P) : (lift f g).comp inl = f := rfl

@[to_additive (attr := simp)]
/--
theorem `lift_apply_inr` / 定理 `lift_apply_inr`

English:
theorem lift_apply_inr
  given: (f : M ->* P) (g : N ->* P) (x : N)
  statement: lift f g (inr x) = g x
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 lift_apply_inr
  条件: (f : M ->* P) (g : N ->* P) (x : N)
  结论: lift f g (inr x) = g x
  证明: rfl

@[to_additive (attr := simp)]

Depends on / 依赖: SeparatingRight
-/
theorem lift_apply_inr (f : M ->* P) (g : N ->* P) (x : N) : lift f g (inr x) = g x :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `lift_comp_inr` / 定理 `lift_comp_inr`

English:
theorem lift_comp_inr
  given: (f : M ->* P) (g : N ->* P)
  statement: (lift f g).comp inr = g
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 lift_comp_inr
  条件: (f : M ->* P) (g : N ->* P)
  结论: (lift f g).comp inr = g
  证明: rfl

@[to_additive (attr := simp)]

Depends on / 依赖: Nondegenerate
-/
theorem lift_comp_inr (f : M ->* P) (g : N ->* P) : (lift f g).comp inr = g := rfl

@[to_additive (attr := simp)]
/--
theorem `lift_comp_swap` / 定理 `lift_comp_swap`

English:
theorem lift_comp_swap
  given: (f : M ->* P) (g : N ->* P)
  statement: (lift f g).comp (swap N M) = lift g f
  proof: hom_ext rfl rfl

@[to_additive (attr := simp)]

中文:
定理 lift_comp_swap
  条件: (f : M ->* P) (g : N ->* P)
  结论: (lift f g).comp (swap N M) = lift g f
  证明: hom_ext rfl rfl

@[to_additive (attr := simp)]

Depends on / 依赖: hom_ext
-/
theorem lift_comp_swap (f : M ->* P) (g : N ->* P) : (lift f g).comp (swap N M) = lift g f :=
  hom_ext rfl rfl

@[to_additive (attr := simp)]
/--
theorem `lift_swap` / 定理 `lift_swap`

English:
theorem lift_swap
  given: (f : M ->* P) (g : N ->* P) (x : N ∗ M)
  statement: lift f g (swap N M x) = lift g f x
  proof: DFunLike.congr_fun (lift_comp_swap f g) x

@[to_additive]

中文:
定理 lift_swap
  条件: (f : M ->* P) (g : N ->* P) (x : N ∗ M)
  结论: lift f g (swap N M x) = lift g f x
  证明: DFunLike.congr_fun (lift_comp_swap f g) x

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, lift_comp_swap
-/
theorem lift_swap (f : M ->* P) (g : N ->* P) (x : N ∗ M) : lift f g (swap N M x) = lift g f x :=
  DFunLike.congr_fun (lift_comp_swap f g) x

@[to_additive]
/--
theorem `comp_lift` / 定理 `comp_lift`

English:
theorem comp_lift
  given: {P' : Type*} [Monoid P'] (f : P ->* P') (g₁ : M ->* P) (g₂ : N ->* P)
  proof: hom_ext (by rw [MonoidHom.comp_assoc, lift_comp_inl, lift_comp_inl]) by
    rw [MonoidHom.comp_assoc]; rw [lift_comp_inr]; rw [lift_comp_inr]

中文:
定理 comp_lift
  条件: {P' : 类型} [幺半群 P'] (f : P ->* P') (g₁ : M ->* P) (g₂ : N ->* P)
  证明: hom_ext (by rw [MonoidHom.comp_assoc, lift_comp_inl, lift_comp_inl]) by
    rw [MonoidHom.comp_assoc]; rw [lift_comp_inr]; rw [lift_comp_inr]

Depends on / 依赖: MonoidHom, MonoidHom.comp_assoc, comp_assoc, hom_ext, lift_comp_inl, lift_comp_inr
-/
theorem comp_lift {P' : Type*} [Monoid P'] (f : P ->* P') (g₁ : M ->* P) (g₂ : N ->* P) :
    f.comp (lift g₁ g₂) = lift (f.comp g₁) (f.comp g₂) :=
hom_ext (by rw [MonoidHom.comp_assoc, lift_comp_inl, lift_comp_inl]) by
    rw [MonoidHom.comp_assoc]; rw [lift_comp_inr]; rw [lift_comp_inr]

/-- `Coprod.lift` as an equivalence. -/
@[to_additive /-- `AddMonoid.Coprod.lift` as an equivalence. -/]
/--
Definition of `liftEquiv` / `liftEquiv` 的定义

English:
definition liftEquiv
  signature: : (M ->* P) × (N ->* P) ≃ (M ∗ N ->* P) where
  body: lift fg.1 fg.2
  invFun f := (f.comp inl, f.comp inr)
right_inv _ := Eq.symm lift_unique rfl rfl

@[to_additive (attr := simp)]

中文:
定义 liftEquiv
  签名: : (M ->* P) × (N ->* P) ≃ (M ∗ N ->* P) where
  定义体: lift fg.1 fg.2
  invFun f := (f.comp inl, f.comp inr)
right_inv _ := Eq.symm lift_unique rfl rfl

@[to_additive (attr := simp)]
-/
def liftEquiv : (M ->* P) × (N ->* P) ≃ (M ∗ N ->* P) where
  toFun fg := lift fg.1 fg.2
  invFun f := (f.comp inl, f.comp inr)
right_inv _ := Eq.symm lift_unique rfl rfl

@[to_additive (attr := simp)]
/--
theorem `mrange_lift` / 定理 `mrange_lift`

English:
theorem mrange_lift
  given: (f : M ->* P) (g : N ->* P)
  proof: by
  simp [mrange_eq]

中文:
定理 mrange_lift
  条件: (f : M ->* P) (g : N ->* P)
  证明: by
  simp [mrange_eq]

Depends on / 依赖: mrange_eq
-/
theorem mrange_lift (f : M ->* P) (g : N ->* P) :
    MonoidHom.mrange (lift f g) = MonoidHom.mrange f ⊔ MonoidHom.mrange g := by
  simp [mrange_eq]

end Lift

section ToProd

variable {M N : Type*} [Monoid M] [Monoid N]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monoid (M ∗ N)
  body: { mul_assoc := (Con.monoid _).mul_assoc
    one_mul := (Con.monoid _).one_mul
    mul_one := (Con.monoid _).mul_one }

中文:
实例 :
  签名: 幺半群 (M ∗ N)
  定义体: { mul_assoc := (Con.monoid _).mul_assoc
    one_mul := (Con.monoid _).one_mul
    mul_one := (Con.monoid _).mul_one }
-/
@[to_additive] instance : Monoid (M ∗ N) :=
  { mul_assoc := (Con.monoid _).mul_assoc
    one_mul := (Con.monoid _).one_mul
    mul_one := (Con.monoid _).mul_one }

/-- The natural projection `M ∗ N →* M`. -/
@[to_additive /-- The natural projection `AddMonoid.Coprod M N →+ M`. -/]
/--
Definition of `fst` / `fst` 的定义

English:
definition fst
  signature: : M ∗ N ->* M
  body: lift (.id M) 1

中文:
定义 fst
  签名: : M ∗ N ->* M
  定义体: lift (.id M) 1
-/
def fst : M ∗ N ->* M := lift (.id M) 1

/-- The natural projection `M ∗ N →* N`. -/
@[to_additive /-- The natural projection `AddMonoid.Coprod M N →+ N`. -/]
/--
Definition of `snd` / `snd` 的定义

English:
definition snd
  signature: : M ∗ N ->* N
  body: lift 1 (.id N)

中文:
定义 snd
  签名: : M ∗ N ->* N
  定义体: lift 1 (.id N)
-/
def snd : M ∗ N ->* N := lift 1 (.id N)

/-- The natural projection `M ∗ N →* M × N`. -/
@[to_additive toProd /-- The natural projection `AddMonoid.Coprod M N →+ M × N`. -/]
/--
Definition of `toProd` / `toProd` 的定义

English:
definition toProd
  signature: : M ∗ N ->* M × N
  body: lift (.inl _ _) (.inr _ _)

中文:
定义 toProd
  签名: : M ∗ N ->* M × N
  定义体: lift (.inl _ _) (.inr _ _)
-/
def toProd : M ∗ N ->* M × N := lift (.inl _ _) (.inr _ _)

/--
theorem `fst_comp_inl` / 定理 `fst_comp_inl`

English:
theorem fst_comp_inl
  statement: (fst : M ∗ N ->* M).comp inl = .id _
  proof: rfl

中文:
定理 fst_comp_inl
  结论: (fst : M ∗ N ->* M).comp inl = .id _
  证明: rfl
-/
@[to_additive (attr := simp)] theorem fst_comp_inl : (fst : M ∗ N ->* M).comp inl = .id _ := rfl
/--
theorem `fst_apply_inl` / 定理 `fst_apply_inl`

English:
theorem fst_apply_inl
  given: (x : M)
  statement: fst (inl x : M ∗ N) = x
  proof: rfl

中文:
定理 fst_apply_inl
  条件: (x : M)
  结论: fst (inl x : M ∗ N) = x
  证明: rfl
-/
@[to_additive (attr := simp)] theorem fst_apply_inl (x : M) : fst (inl x : M ∗ N) = x := rfl
/--
theorem `fst_comp_inr` / 定理 `fst_comp_inr`

English:
theorem fst_comp_inr
  statement: (fst : M ∗ N ->* M).comp inr = 1
  proof: rfl

中文:
定理 fst_comp_inr
  结论: (fst : M ∗ N ->* M).comp inr = 1
  证明: rfl
-/
@[to_additive (attr := simp)] theorem fst_comp_inr : (fst : M ∗ N ->* M).comp inr = 1 := rfl
/--
theorem `fst_apply_inr` / 定理 `fst_apply_inr`

English:
theorem fst_apply_inr
  given: (x : N)
  statement: fst (inr x : M ∗ N) = 1
  proof: rfl

中文:
定理 fst_apply_inr
  条件: (x : N)
  结论: fst (inr x : M ∗ N) = 1
  证明: rfl
-/
@[to_additive (attr := simp)] theorem fst_apply_inr (x : N) : fst (inr x : M ∗ N) = 1 := rfl
/--
theorem `snd_comp_inl` / 定理 `snd_comp_inl`

English:
theorem snd_comp_inl
  statement: (snd : M ∗ N ->* N).comp inl = 1
  proof: rfl

中文:
定理 snd_comp_inl
  结论: (snd : M ∗ N ->* N).comp inl = 1
  证明: rfl
-/
@[to_additive (attr := simp)] theorem snd_comp_inl : (snd : M ∗ N ->* N).comp inl = 1 := rfl
/--
theorem `snd_apply_inl` / 定理 `snd_apply_inl`

English:
theorem snd_apply_inl
  given: (x : M)
  statement: snd (inl x : M ∗ N) = 1
  proof: rfl

中文:
定理 snd_apply_inl
  条件: (x : M)
  结论: snd (inl x : M ∗ N) = 1
  证明: rfl
-/
@[to_additive (attr := simp)] theorem snd_apply_inl (x : M) : snd (inl x : M ∗ N) = 1 := rfl
/--
theorem `snd_comp_inr` / 定理 `snd_comp_inr`

English:
theorem snd_comp_inr
  statement: (snd : M ∗ N ->* N).comp inr = .id _
  proof: rfl

中文:
定理 snd_comp_inr
  结论: (snd : M ∗ N ->* N).comp inr = .id _
  证明: rfl
-/
@[to_additive (attr := simp)] theorem snd_comp_inr : (snd : M ∗ N ->* N).comp inr = .id _ := rfl
/--
theorem `snd_apply_inr` / 定理 `snd_apply_inr`

English:
theorem snd_apply_inr
  given: (x : N)
  statement: snd (inr x : M ∗ N) = x
  proof: rfl

@[to_additive (attr := simp) toProd_comp_inl]

中文:
定理 snd_apply_inr
  条件: (x : N)
  结论: snd (inr x : M ∗ N) = x
  证明: rfl

@[to_additive (attr := simp) toProd_comp_inl]
-/
@[to_additive (attr := simp)] theorem snd_apply_inr (x : N) : snd (inr x : M ∗ N) = x := rfl

@[to_additive (attr := simp) toProd_comp_inl]
/--
theorem `toProd_comp_inl` / 定理 `toProd_comp_inl`

English:
theorem toProd_comp_inl
  statement: (toProd : M ∗ N ->* M × N).comp inl = .inl _ _
  proof: rfl

@[to_additive (attr := simp) toProd_comp_inr]

中文:
定理 toProd_comp_inl
  结论: (toProd : M ∗ N ->* M × N).comp inl = .inl _ _
  证明: rfl

@[to_additive (attr := simp) toProd_comp_inr]
-/
theorem toProd_comp_inl : (toProd : M ∗ N ->* M × N).comp inl = .inl _ _ := rfl

@[to_additive (attr := simp) toProd_comp_inr]
/--
theorem `toProd_comp_inr` / 定理 `toProd_comp_inr`

English:
theorem toProd_comp_inr
  statement: (toProd : M ∗ N ->* M × N).comp inr = .inr _ _
  proof: rfl

@[to_additive (attr := simp) toProd_apply_inl]

中文:
定理 toProd_comp_inr
  结论: (toProd : M ∗ N ->* M × N).comp inr = .inr _ _
  证明: rfl

@[to_additive (attr := simp) toProd_apply_inl]
-/
theorem toProd_comp_inr : (toProd : M ∗ N ->* M × N).comp inr = .inr _ _ := rfl

@[to_additive (attr := simp) toProd_apply_inl]
/--
theorem `toProd_apply_inl` / 定理 `toProd_apply_inl`

English:
theorem toProd_apply_inl
  given: (x : M)
  statement: toProd (inl x : M ∗ N) = (x, 1)
  proof: rfl

@[to_additive (attr := simp) toProd_apply_inr]

中文:
定理 toProd_apply_inl
  条件: (x : M)
  结论: toProd (inl x : M ∗ N) = (x, 1)
  证明: rfl

@[to_additive (attr := simp) toProd_apply_inr]
-/
theorem toProd_apply_inl (x : M) : toProd (inl x : M ∗ N) = (x, 1) := rfl

@[to_additive (attr := simp) toProd_apply_inr]
/--
theorem `toProd_apply_inr` / 定理 `toProd_apply_inr`

English:
theorem toProd_apply_inr
  given: (x : N)
  statement: toProd (inr x : M ∗ N) = (1, x)
  proof: rfl

@[to_additive (attr := simp) fst_prod_snd]

中文:
定理 toProd_apply_inr
  条件: (x : N)
  结论: toProd (inr x : M ∗ N) = (1, x)
  证明: rfl

@[to_additive (attr := simp) fst_prod_snd]
-/
theorem toProd_apply_inr (x : N) : toProd (inr x : M ∗ N) = (1, x) := rfl

@[to_additive (attr := simp) fst_prod_snd]
/--
theorem `fst_prod_snd` / 定理 `fst_prod_snd`

English:
theorem fst_prod_snd
  statement: (fst : M ∗ N ->* M).prod snd = toProd
  proof: by ext1 <;> rfl

@[to_additive (attr := simp) prod_mk_fst_snd]

中文:
定理 fst_prod_snd
  结论: (fst : M ∗ N ->* M).乘积 snd = toProd
  证明: by ext1 <;> rfl

@[to_additive (attr := simp) prod_mk_fst_snd]
-/
theorem fst_prod_snd : (fst : M ∗ N ->* M).prod snd = toProd := by ext1 <;> rfl

@[to_additive (attr := simp) prod_mk_fst_snd]
/--
theorem `prod_mk_fst_snd` / 定理 `prod_mk_fst_snd`

English:
theorem prod_mk_fst_snd
  given: (x : M ∗ N)
  statement: (fst x, snd x) = toProd x
  proof: by
  rw [← fst_prod_snd]; rw [MonoidHom.prod_apply]

@[to_additive (attr := simp) fst_comp_toProd]

中文:
定理 prod_mk_fst_snd
  条件: (x : M ∗ N)
  结论: (fst x, snd x) = toProd x
  证明: by
  rw [← fst_prod_snd]; rw [MonoidHom.prod_apply]

@[to_additive (attr := simp) fst_comp_toProd]

Depends on / 依赖: MonoidHom, MonoidHom.prod_apply, fst_prod_snd, prod_apply
-/
theorem prod_mk_fst_snd (x : M ∗ N) : (fst x, snd x) = toProd x := by
  rw [← fst_prod_snd]; rw [MonoidHom.prod_apply]

@[to_additive (attr := simp) fst_comp_toProd]
/--
theorem `fst_comp_toProd` / 定理 `fst_comp_toProd`

English:
theorem fst_comp_toProd
  statement: (MonoidHom.fst M N).comp toProd = fst
  proof: by
  rw [← fst_prod_snd]; rw [MonoidHom.fst_comp_prod]

@[to_additive (attr := simp) fst_toProd]

中文:
定理 fst_comp_toProd
  结论: (幺半群态射.fst M N).comp toProd = fst
  证明: by
  rw [← fst_prod_snd]; rw [MonoidHom.fst_comp_prod]

@[to_additive (attr := simp) fst_toProd]

Depends on / 依赖: MonoidHom, MonoidHom.fst_comp_prod, fst_comp_prod, fst_prod_snd
-/
theorem fst_comp_toProd : (MonoidHom.fst M N).comp toProd = fst := by
  rw [← fst_prod_snd]; rw [MonoidHom.fst_comp_prod]

@[to_additive (attr := simp) fst_toProd]
/--
theorem `fst_toProd` / 定理 `fst_toProd`

English:
theorem fst_toProd
  given: (x : M ∗ N)
  statement: (toProd x).1 = fst x
  proof: by
  rw [← fst_comp_toProd]; rfl

@[to_additive (attr := simp) snd_comp_toProd]

中文:
定理 fst_toProd
  条件: (x : M ∗ N)
  结论: (toProd x).1 = fst x
  证明: by
  rw [← fst_comp_toProd]; rfl

@[to_additive (attr := simp) snd_comp_toProd]

Depends on / 依赖: fst_comp_toProd
-/
theorem fst_toProd (x : M ∗ N) : (toProd x).1 = fst x := by
  rw [← fst_comp_toProd]; rfl

@[to_additive (attr := simp) snd_comp_toProd]
/--
theorem `snd_comp_toProd` / 定理 `snd_comp_toProd`

English:
theorem snd_comp_toProd
  statement: (MonoidHom.snd M N).comp toProd = snd
  proof: by
  rw [← fst_prod_snd]; rw [MonoidHom.snd_comp_prod]

@[to_additive (attr := simp) snd_toProd]

中文:
定理 snd_comp_toProd
  结论: (幺半群态射.snd M N).comp toProd = snd
  证明: by
  rw [← fst_prod_snd]; rw [MonoidHom.snd_comp_prod]

@[to_additive (attr := simp) snd_toProd]

Depends on / 依赖: MonoidHom, MonoidHom.snd_comp_prod, fst_prod_snd, snd_comp_prod
-/
theorem snd_comp_toProd : (MonoidHom.snd M N).comp toProd = snd := by
  rw [← fst_prod_snd]; rw [MonoidHom.snd_comp_prod]

@[to_additive (attr := simp) snd_toProd]
/--
theorem `snd_toProd` / 定理 `snd_toProd`

English:
theorem snd_toProd
  given: (x : M ∗ N)
  statement: (toProd x).2 = snd x
  proof: by
  rw [← snd_comp_toProd]; rfl

@[to_additive (attr := simp)]

中文:
定理 snd_toProd
  条件: (x : M ∗ N)
  结论: (toProd x).2 = snd x
  证明: by
  rw [← snd_comp_toProd]; rfl

@[to_additive (attr := simp)]

Depends on / 依赖: snd_comp_toProd
-/
theorem snd_toProd (x : M ∗ N) : (toProd x).2 = snd x := by
  rw [← snd_comp_toProd]; rfl

@[to_additive (attr := simp)]
/--
theorem `fst_comp_swap` / 定理 `fst_comp_swap`

English:
theorem fst_comp_swap
  statement: fst.comp (swap M N) = snd
  proof: lift_comp_swap _ _

@[to_additive (attr := simp)]

中文:
定理 fst_comp_swap
  结论: fst.comp (swap M N) = snd
  证明: lift_comp_swap _ _

@[to_additive (attr := simp)]

Depends on / 依赖: lift_comp_swap
-/
theorem fst_comp_swap : fst.comp (swap M N) = snd := lift_comp_swap _ _

@[to_additive (attr := simp)]
/--
theorem `fst_swap` / 定理 `fst_swap`

English:
theorem fst_swap
  given: (x : M ∗ N)
  statement: fst (swap M N x) = snd x
  proof: lift_swap _ _ _

@[to_additive (attr := simp)]

中文:
定理 fst_swap
  条件: (x : M ∗ N)
  结论: fst (swap M N x) = snd x
  证明: lift_swap _ _ _

@[to_additive (attr := simp)]

Depends on / 依赖: lift_swap
-/
theorem fst_swap (x : M ∗ N) : fst (swap M N x) = snd x := lift_swap _ _ _

@[to_additive (attr := simp)]
/--
theorem `snd_comp_swap` / 定理 `snd_comp_swap`

English:
theorem snd_comp_swap
  statement: snd.comp (swap M N) = fst
  proof: lift_comp_swap _ _

@[to_additive (attr := simp)]

中文:
定理 snd_comp_swap
  结论: snd.comp (swap M N) = fst
  证明: lift_comp_swap _ _

@[to_additive (attr := simp)]

Depends on / 依赖: lift_comp_swap
-/
theorem snd_comp_swap : snd.comp (swap M N) = fst := lift_comp_swap _ _

@[to_additive (attr := simp)]
/--
theorem `snd_swap` / 定理 `snd_swap`

English:
theorem snd_swap
  given: (x : M ∗ N)
  statement: snd (swap M N x) = fst x
  proof: lift_swap _ _ _

@[to_additive (attr := simp)]

中文:
定理 snd_swap
  条件: (x : M ∗ N)
  结论: snd (swap M N x) = fst x
  证明: lift_swap _ _ _

@[to_additive (attr := simp)]

Depends on / 依赖: lift_swap
-/
theorem snd_swap (x : M ∗ N) : snd (swap M N x) = fst x := lift_swap _ _ _

@[to_additive (attr := simp)]
/--
theorem `lift_inr_inl` / 定理 `lift_inr_inl`

English:
theorem lift_inr_inl
  statement: lift (inr : M ->* N ∗ M) inl = swap M N
  proof: hom_ext rfl rfl

@[to_additive (attr := simp)]

中文:
定理 lift_inr_inl
  结论: lift (inr : M ->* N ∗ M) inl = swap M N
  证明: hom_ext rfl rfl

@[to_additive (attr := simp)]

Depends on / 依赖: hom_ext
-/
theorem lift_inr_inl : lift (inr : M ->* N ∗ M) inl = swap M N := hom_ext rfl rfl

@[to_additive (attr := simp)]
/--
theorem `lift_inl_inr` / 定理 `lift_inl_inr`

English:
theorem lift_inl_inr
  statement: lift (inl : M ->* M ∗ N) inr = .id _
  proof: hom_ext rfl rfl

@[to_additive]

中文:
定理 lift_inl_inr
  结论: lift (inl : M ->* M ∗ N) inr = .id _
  证明: hom_ext rfl rfl

@[to_additive]

Depends on / 依赖: hom_ext
-/
theorem lift_inl_inr : lift (inl : M ->* M ∗ N) inr = .id _ := hom_ext rfl rfl

@[to_additive]
/--
theorem `inl_injective` / 定理 `inl_injective`

English:
theorem inl_injective
  statement: Injective (inl : M ->* M ∗ N)
  proof: LeftInverse.injective fst_apply_inl

@[to_additive]

中文:
定理 inl_injective
  结论: 单射 (inl : M ->* M ∗ N)
  证明: LeftInverse.injective fst_apply_inl

@[to_additive]

Depends on / 依赖: LeftInverse, LeftInverse.injective, fst_apply_inl, injective
-/
theorem inl_injective : Injective (inl : M ->* M ∗ N) := LeftInverse.injective fst_apply_inl

@[to_additive]
/--
theorem `inr_injective` / 定理 `inr_injective`

English:
theorem inr_injective
  statement: Injective (inr : N ->* M ∗ N)
  proof: LeftInverse.injective snd_apply_inr

@[to_additive]

中文:
定理 inr_injective
  结论: 单射 (inr : N ->* M ∗ N)
  证明: LeftInverse.injective snd_apply_inr

@[to_additive]

Depends on / 依赖: LeftInverse, LeftInverse.injective, injective, snd_apply_inr
-/
theorem inr_injective : Injective (inr : N ->* M ∗ N) := LeftInverse.injective snd_apply_inr

@[to_additive]
/--
theorem `fst_surjective` / 定理 `fst_surjective`

English:
theorem fst_surjective
  statement: Surjective (fst : M ∗ N ->* M)
  proof: LeftInverse.surjective fst_apply_inl

@[to_additive]

中文:
定理 fst_surjective
  结论: 满射 (fst : M ∗ N ->* M)
  证明: LeftInverse.surjective fst_apply_inl

@[to_additive]

Depends on / 依赖: LeftInverse, LeftInverse.surjective, fst_apply_inl, surjective
-/
theorem fst_surjective : Surjective (fst : M ∗ N ->* M) := LeftInverse.surjective fst_apply_inl

@[to_additive]
/--
theorem `snd_surjective` / 定理 `snd_surjective`

English:
theorem snd_surjective
  statement: Surjective (snd : M ∗ N ->* N)
  proof: LeftInverse.surjective snd_apply_inr

@[to_additive toProd_surjective]

中文:
定理 snd_surjective
  结论: 满射 (snd : M ∗ N ->* N)
  证明: LeftInverse.surjective snd_apply_inr

@[to_additive toProd_surjective]

Depends on / 依赖: LeftInverse, LeftInverse.surjective, snd_apply_inr, surjective
-/
theorem snd_surjective : Surjective (snd : M ∗ N ->* N) := LeftInverse.surjective snd_apply_inr

@[to_additive toProd_surjective]
/--
theorem `toProd_surjective` / 定理 `toProd_surjective`

English:
theorem toProd_surjective
  statement: Surjective (toProd : M ∗ N ->* M × N)
  proof: fun x =>
  ⟨inl x.1 * inr x.2, by rw [map_mul, toProd_apply_inl, toProd_apply_inr, Prod.fst_mul_snd]⟩

中文:
定理 toProd_surjective
  结论: 满射 (toProd : M ∗ N ->* M × N)
  证明: fun x =>
  ⟨inl x.1 * inr x.2, by rw [map_mul, toProd_apply_inl, toProd_apply_inr, Prod.fst_mul_snd]⟩
-/
theorem toProd_surjective : Surjective (toProd : M ∗ N ->* M × N) := fun x =>
  ⟨inl x.1 * inr x.2, by rw [map_mul, toProd_apply_inl, toProd_apply_inr, Prod.fst_mul_snd]⟩

end ToProd

section Group

variable {G H : Type*} [Group G] [Group H]

@[to_additive]
/--
theorem `mk_of_inv_mul` / 定理 `mk_of_inv_mul`

English:
theorem mk_of_inv_mul
  statement: forall x : G oplus H, mk (of (x.map Inv.inv Inv.inv)) * mk (of x) = 1

中文:
定理 mk_of_inv_mul
  结论: 对任意 x : G oplus H, mk (of (x.map 取逆.inv 取逆.inv)) * mk (of x) = 1
-/
theorem mk_of_inv_mul : forall x : G oplus H, mk (of (x.map Inv.inv Inv.inv)) * mk (of x) = 1
  | Sum.inl _ => map_mul_eq_one inl (inv_mul_cancel _)
  | Sum.inr _ => map_mul_eq_one inr (inv_mul_cancel _)

@[to_additive]
/--
theorem `con_inv_mul_cancel` / 定理 `con_inv_mul_cancel`

English:
theorem con_inv_mul_cancel
  given: (x : FreeMonoid (G oplus H))
  proof: by
  rw [← mk_eq_mk]; rw [map_mul]; rw [map_one]
  induction x using FreeMonoid.inductionOn' with
  | one => simp
  | of_mul x xs ihx =>
    simp only [toList_of_mul, map_cons, reverse_cons, ofList_append, map_mul, ofList_singleton]
    rwa [mul_assoc, ← mul_assoc (mk (of _)), mk_of_inv_mul, one_mul]

@[to_additive]

中文:
定理 con_inv_mul_cancel
  条件: (x : 自由幺半群 (G oplus H))
  证明: by
  rw [← mk_eq_mk]; rw [map_mul]; rw [map_one]
  induction x using FreeMonoid.inductionOn' with
  | one => simp
  | of_mul x xs ihx =>
    simp only [toList_of_mul, map_cons, reverse_cons, ofList_append, map_mul, ofList_singleton]
    rwa [mul_assoc, ← mul_assoc (mk (of _)), mk_of_inv_mul, one_mul]

@[to_additive]

Depends on / 依赖: FreeMonoid, FreeMonoid.inductionOn, inductionOn, map_cons, map_mul, map_one, mk_eq_mk, mk_of_inv_mul, mul_assoc, ofList_append, ofList_singleton, of_mul, one_mul, reverse_cons, toList_of_mul
-/
theorem con_inv_mul_cancel (x : FreeMonoid (G oplus H)) :
    coprodCon G H (ofList (x.toList.map (Sum.map Inv.inv Inv.inv)).reverse * x) 1 := by
  rw [← mk_eq_mk]; rw [map_mul]; rw [map_one]
  induction x using FreeMonoid.inductionOn' with
  | one => simp
  | of_mul x xs ihx =>
    simp only [toList_of_mul, map_cons, reverse_cons, ofList_append, map_mul, ofList_singleton]
    rwa [mul_assoc, ← mul_assoc (mk (of _)), mk_of_inv_mul, one_mul]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inv (G ∗ H)
  body: Quotient.map' (fun w => ofList (w.toList.map (Sum.map Inv.inv Inv.inv)).reverse) fun _ _ =>
    (coprodCon G H).map_of_mul_left_rel_one _ con_inv_mul_cancel

@[to_additive]

中文:
实例 :
  签名: 取逆 (G ∗ H)
  定义体: Quotient.map' (fun w => ofList (w.toList.map (Sum.map Inv.inv Inv.inv)).reverse) fun _ _ =>
    (coprodCon G H).map_of_mul_left_rel_one _ con_inv_mul_cancel

@[to_additive]

Depends on / 依赖: Inv.inv, Quotient, Quotient.map, Sum.map, ofList, reverse, toList, w.toList.map
-/
instance : Inv (G ∗ H) where
  inv := Quotient.map' (fun w => ofList (w.toList.map (Sum.map Inv.inv Inv.inv)).reverse) fun _ _ =>
    (coprodCon G H).map_of_mul_left_rel_one _ con_inv_mul_cancel

@[to_additive]
/--
theorem `inv_def` / 定理 `inv_def`

English:
theorem inv_def
  given: (w : FreeMonoid (G oplus H))
  proof: rfl

@[to_additive]

中文:
定理 inv_def
  条件: (w : 自由幺半群 (G oplus H))
  证明: rfl

@[to_additive]
-/
theorem inv_def (w : FreeMonoid (G oplus H)) :
    (mk w)⁻¹ = mk (ofList (w.toList.map (Sum.map Inv.inv Inv.inv)).reverse) :=
  rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Group (G ∗ H)
  body: mk_surjective.forall.2 fun x => mk_eq_mk.2 (con_inv_mul_cancel x)

@[to_additive (attr := simp)]

中文:
实例 :
  签名: 群 (G ∗ H)
  定义体: mk_surjective.forall.2 fun x => mk_eq_mk.2 (con_inv_mul_cancel x)

@[to_additive (attr := simp)]

Depends on / 依赖: con_inv_mul_cancel, mk_eq_mk, mk_surjective, mk_surjective.forall
-/
instance : Group (G ∗ H) where
  inv_mul_cancel := mk_surjective.forall.2 fun x => mk_eq_mk.2 (con_inv_mul_cancel x)

@[to_additive (attr := simp)]
/--
theorem `closure_range_inl_union_inr` / 定理 `closure_range_inl_union_inr`

English:
theorem closure_range_inl_union_inr
  proof: Subgroup.closure_eq_top_of_mclosure_eq_top mclosure_range_inl_union_inr

中文:
定理 closure_range_inl_union_inr
  证明: Subgroup.closure_eq_top_of_mclosure_eq_top mclosure_range_inl_union_inr

Depends on / 依赖: Subgroup, Subgroup.closure_eq_top_of_mclosure_eq_top, closure_eq_top_of_mclosure_eq_top, mclosure_range_inl_union_inr
-/
theorem closure_range_inl_union_inr :
    Subgroup.closure (range (inl : G ->* G ∗ H) union range inr) = ⊤ :=
  Subgroup.closure_eq_top_of_mclosure_eq_top mclosure_range_inl_union_inr

/--
theorem `range_inl_sup_range_inr` / 定理 `range_inl_sup_range_inr`

English:
theorem range_inl_sup_range_inr
  proof: by
  rw [← closure_range_inl_union_inr]; rw [Subgroup.closure_union]; rw [← MonoidHom.coe_range]; rw [← MonoidHom.coe_range]; rw [Subgroup.closure_eq]; rw [Subgroup.closure_eq]

@[to_additive]

中文:
定理 range_inl_sup_range_inr
  证明: by
  rw [← closure_range_inl_union_inr]; rw [Subgroup.closure_union]; rw [← MonoidHom.coe_range]; rw [← MonoidHom.coe_range]; rw [Subgroup.closure_eq]; rw [Subgroup.closure_eq]

@[to_additive]
-/
@[to_additive (attr := simp)] theorem range_inl_sup_range_inr :
    MonoidHom.range (inl : G ->* G ∗ H) ⊔ MonoidHom.range inr = ⊤ := by
  rw [← closure_range_inl_union_inr]; rw [Subgroup.closure_union]; rw [← MonoidHom.coe_range]; rw [← MonoidHom.coe_range]; rw [Subgroup.closure_eq]; rw [Subgroup.closure_eq]

@[to_additive]
/--
theorem `codisjoint_range_inl_range_inr` / 定理 `codisjoint_range_inl_range_inr`

English:
theorem codisjoint_range_inl_range_inr
  proof: codisjoint_iff.2 range_inl_sup_range_inr

中文:
定理 codisjoint_range_inl_range_inr
  证明: codisjoint_iff.2 range_inl_sup_range_inr

Depends on / 依赖: codisjoint_iff, range_inl_sup_range_inr
-/
theorem codisjoint_range_inl_range_inr :
    Codisjoint (MonoidHom.range (inl : G ->* G ∗ H)) (MonoidHom.range inr) :=
  codisjoint_iff.2 range_inl_sup_range_inr

/--
theorem `range_swap` / 定理 `range_swap`

English:
theorem range_swap
  statement: MonoidHom.range (swap G H) = ⊤
  proof: MonoidHom.range_eq_top.2 swap_surjective

中文:
定理 range_swap
  结论: 幺半群态射.range (swap G H) = ⊤
  证明: MonoidHom.range_eq_top.2 swap_surjective
-/
@[to_additive (attr := simp)] theorem range_swap : MonoidHom.range (swap G H) = ⊤ :=
  MonoidHom.range_eq_top.2 swap_surjective

variable {K : Type*} [Group K]

/--
theorem `range_eq` / 定理 `range_eq`

English:
theorem range_eq
  given: (f : G ∗ H ->* K)
  proof: by
  rw [MonoidHom.range_eq_map]; rw [← range_inl_sup_range_inr]; rw [Subgroup.map_sup]; rw [MonoidHom.map_range]; rw [MonoidHom.map_range]

中文:
定理 range_eq
  条件: (f : G ∗ H ->* K)
  证明: by
  rw [MonoidHom.range_eq_map]; rw [← range_inl_sup_range_inr]; rw [Subgroup.map_sup]; rw [MonoidHom.map_range]; rw [MonoidHom.map_range]
-/
@[to_additive] theorem range_eq (f : G ∗ H ->* K) :
    MonoidHom.range f = MonoidHom.range (f.comp inl) ⊔ MonoidHom.range (f.comp inr) := by
  rw [MonoidHom.range_eq_map]; rw [← range_inl_sup_range_inr]; rw [Subgroup.map_sup]; rw [MonoidHom.map_range]; rw [MonoidHom.map_range]

/--
theorem `range_lift` / 定理 `range_lift`

English:
theorem range_lift
  given: (f : G ->* K) (g : H ->* K)
  proof: by
  simp [range_eq]

中文:
定理 range_lift
  条件: (f : G ->* K) (g : H ->* K)
  证明: by
  simp [range_eq]
-/
@[to_additive (attr := simp)] theorem range_lift (f : G ->* K) (g : H ->* K) :
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
/--
Definition of `coprodCongr` / `coprodCongr` 的定义

English:
definition coprodCongr
  signature: (e : M ≃* N) (e' : M' ≃* N')
  body: (Coprod.map (e : M ->* N) (e' : M' ->* N')).toMulEquiv (Coprod.map e.symm e'.symm)
    (by ext <;> simp) (by ext <;> simp)

中文:
定义 coprodCongr
  签名: (e : M ≃* N) (e' : M' ≃* N')
  定义体: (Coprod.map (e : M ->* N) (e' : M' ->* N')).toMulEquiv (Coprod.map e.symm e'.symm)
    (by ext <;> simp) (by ext <;> simp)

Depends on / 依赖: Coprod, Coprod.map, e.symm, toMulEquiv
-/
def coprodCongr (e : M ≃* N) (e' : M' ≃* N') : (M ∗ M') ≃* (N ∗ N') :=
  (Coprod.map (e : M ->* N) (e' : M' ->* N')).toMulEquiv (Coprod.map e.symm e'.symm)
    (by ext <;> simp) (by ext <;> simp)

variable (M N)

/-- A `MulEquiv` version of `Coprod.swap`. -/
@[to_additive (attr := simps! -fullyApplied)
  /-- An `AddEquiv` version of `AddMonoid.Coprod.swap`. -/]
/--
Definition of `coprodComm` / `coprodComm` 的定义

English:
definition coprodComm
  signature: : M ∗ N ≃* N ∗ M
  body: (Coprod.swap _ _).toMulEquiv (Coprod.swap _ _) (Coprod.swap_comp_swap _ _)
    (Coprod.swap_comp_swap _ _)

中文:
定义 coprodComm
  签名: : M ∗ N ≃* N ∗ M
  定义体: (Coprod.swap _ _).toMulEquiv (Coprod.swap _ _) (Coprod.swap_comp_swap _ _)
    (Coprod.swap_comp_swap _ _)

Depends on / 依赖: Coprod, Coprod.swap, Coprod.swap_comp_swap, LinearEquiv, LinearEquiv.ofLinearMap, LinearEquiv.toLinearMap_injective, Matrix, Matrix.toLin, _mul, _one, coe_mul, coe_one, inv_mul_cancel, map_mul, map_one, mul_inv_cancel, ofLinearMap, swap_comp_swap, toLinearMap_injective, toMulEquiv
-/
def coprodComm : M ∗ N ≃* N ∗ M :=
  (Coprod.swap _ _).toMulEquiv (Coprod.swap _ _) (Coprod.swap_comp_swap _ _)
    (Coprod.swap_comp_swap _ _)

end MulOneClass

variable (M N P : Type*) [Monoid M] [Monoid N] [Monoid P]

/-- A multiplicative equivalence between `(M ∗ N) ∗ P` and `M ∗ (N ∗ P)`. -/
@[to_additive /-- An additive equivalence between `AddMonoid.Coprod (AddMonoid.Coprod M N) P` and
`AddMonoid.Coprod M (AddMonoid.Coprod N P)`. -/]
/--
Definition of `coprodAssoc` / `coprodAssoc` 的定义

English:
definition coprodAssoc
  signature: : (M ∗ N) ∗ P ≃* M ∗ (N ∗ P)
  body: MonoidHom.toMulEquiv
    (Coprod.lift (Coprod.map (.id M) inl) (inr.comp inr))
    (Coprod.lift (inl.comp inl) (Coprod.map inr (.id P)))
    (by ext <;> rfl) (by ext <;> rfl)

中文:
定义 coprodAssoc
  签名: : (M ∗ N) ∗ P ≃* M ∗ (N ∗ P)
  定义体: MonoidHom.toMulEquiv
    (Coprod.lift (Coprod.map (.id M) inl) (inr.comp inr))
    (Coprod.lift (inl.comp inl) (Coprod.map inr (.id P)))
    (by ext <;> rfl) (by ext <;> rfl)

Depends on / 依赖: Coprod, Coprod.lift, Coprod.map, MonoidHom, MonoidHom.toMulEquiv, inl.comp, inr.comp, toMulEquiv
-/
def coprodAssoc : (M ∗ N) ∗ P ≃* M ∗ (N ∗ P) :=
  MonoidHom.toMulEquiv
    (Coprod.lift (Coprod.map (.id M) inl) (inr.comp inr))
    (Coprod.lift (inl.comp inl) (Coprod.map inr (.id P)))
    (by ext <;> rfl) (by ext <;> rfl)

variable {M N P}

@[to_additive (attr := simp)]
/--
theorem `coprodAssoc_apply_inl_inl` / 定理 `coprodAssoc_apply_inl_inl`

English:
theorem coprodAssoc_apply_inl_inl
  given: (x : M)
  statement: coprodAssoc M N P (inl (inl x)) = inl x
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coprodAssoc_apply_inl_inl
  条件: (x : M)
  结论: coprodAssoc M N P (inl (inl x)) = inl x
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coprodAssoc_apply_inl_inl (x : M) : coprodAssoc M N P (inl (inl x)) = inl x := rfl

@[to_additive (attr := simp)]
/--
theorem `coprodAssoc_apply_inl_inr` / 定理 `coprodAssoc_apply_inl_inr`

English:
theorem coprodAssoc_apply_inl_inr
  given: (x : N)
  statement: coprodAssoc M N P (inl (inr x)) = inr (inl x)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coprodAssoc_apply_inl_inr
  条件: (x : N)
  结论: coprodAssoc M N P (inl (inr x)) = inr (inl x)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coprodAssoc_apply_inl_inr (x : N) : coprodAssoc M N P (inl (inr x)) = inr (inl x) := rfl

@[to_additive (attr := simp)]
/--
theorem `coprodAssoc_apply_inr` / 定理 `coprodAssoc_apply_inr`

English:
theorem coprodAssoc_apply_inr
  given: (x : P)
  statement: coprodAssoc M N P (inr x) = inr (inr x)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coprodAssoc_apply_inr
  条件: (x : P)
  结论: coprodAssoc M N P (inr x) = inr (inr x)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coprodAssoc_apply_inr (x : P) : coprodAssoc M N P (inr x) = inr (inr x) := rfl

@[to_additive (attr := simp)]
/--
theorem `coprodAssoc_symm_apply_inl` / 定理 `coprodAssoc_symm_apply_inl`

English:
theorem coprodAssoc_symm_apply_inl
  given: (x : M)
  statement: (coprodAssoc M N P).symm (inl x) = inl (inl x)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coprodAssoc_symm_apply_inl
  条件: (x : M)
  结论: (coprodAssoc M N P).symm (inl x) = inl (inl x)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coprodAssoc_symm_apply_inl (x : M) : (coprodAssoc M N P).symm (inl x) = inl (inl x) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `coprodAssoc_symm_apply_inr_inl` / 定理 `coprodAssoc_symm_apply_inr_inl`

English:
theorem coprodAssoc_symm_apply_inr_inl
  given: (x : N)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 coprodAssoc_symm_apply_inr_inl
  条件: (x : N)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem coprodAssoc_symm_apply_inr_inl (x : N) :
    (coprodAssoc M N P).symm (inr (inl x)) = inl (inr x) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `coprodAssoc_symm_apply_inr_inr` / 定理 `coprodAssoc_symm_apply_inr_inr`

English:
theorem coprodAssoc_symm_apply_inr_inr
  given: (x : P)
  proof: rfl

中文:
定理 coprodAssoc_symm_apply_inr_inr
  条件: (x : P)
  证明: rfl
-/
theorem coprodAssoc_symm_apply_inr_inr (x : P) :
    (coprodAssoc M N P).symm (inr (inr x)) = inr x :=
  rfl

variable (M)

/-- Isomorphism between `M ∗ PUnit` and `M`. -/
@[to_additive (attr := simps! -fullyApplied)
  /-- Isomorphism between `AddMonoid.Coprod M PUnit` and `M`. -/]
/--
Definition of `coprodPUnit` / `coprodPUnit` 的定义

English:
definition coprodPUnit
  signature: : M ∗ PUnit ≃* M
  body: MonoidHom.toMulEquiv fst inl (hom_ext rfl <| Subsingleton.elim _ _) fst_comp_inl

中文:
定义 coprodPUnit
  签名: : M ∗ 命题单元 ≃* M
  定义体: MonoidHom.toMulEquiv fst inl (hom_ext rfl <| Subsingleton.elim _ _) fst_comp_inl

Depends on / 依赖: MonoidHom, MonoidHom.toMulEquiv, Subsingleton, Subsingleton.elim, fst_comp_inl, hom_ext, toMulEquiv
-/
def coprodPUnit : M ∗ PUnit ≃* M :=
  MonoidHom.toMulEquiv fst inl (hom_ext rfl <| Subsingleton.elim _ _) fst_comp_inl

/-- Isomorphism between `PUnit ∗ M` and `M`. -/
@[to_additive (attr := simps! -fullyApplied)
  /-- Isomorphism between `AddMonoid.Coprod PUnit M` and `M`. -/]
/--
Definition of `punitCoprod` / `punitCoprod` 的定义

English:
definition punitCoprod
  signature: : PUnit ∗ M ≃* M
  body: MonoidHom.toMulEquiv snd inr (hom_ext (Subsingleton.elim _ _) rfl) snd_comp_inr

中文:
定义 punitCoprod
  签名: : 命题单元 ∗ M ≃* M
  定义体: MonoidHom.toMulEquiv snd inr (hom_ext (Subsingleton.elim _ _) rfl) snd_comp_inr

Depends on / 依赖: MonoidHom, MonoidHom.toMulEquiv, Subsingleton, Subsingleton.elim, hom_ext, snd_comp_inr, toMulEquiv
-/
def punitCoprod : PUnit ∗ M ≃* M :=
  MonoidHom.toMulEquiv snd inr (hom_ext (Subsingleton.elim _ _) rfl) snd_comp_inr

end MulEquiv
