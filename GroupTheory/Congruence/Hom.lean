/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.GroupTheory.Congruence.Defs

/-!
# Congruence relations and homomorphisms

This file contains elementary definitions involving congruence relations and morphisms.

## Main definitions

* `Con.ker`: the kernel of a monoid homomorphism as a congruence relation
* `Con.mk'`: the map from a monoid to its quotient by a congruence relation
* `Con.lift`: the homomorphism on the quotient given that the congruence is in the kernel
* `Con.map`: homomorphism from a smaller to a larger quotient

## Tags

congruence, congruence relation, quotient, quotient by congruence relation, monoid,
quotient monoid
-/

@[expose] public section


variable (M : Type*) {N : Type*} {P : Type*}

open Function Setoid

variable {M}

namespace Con

section Mul
variable {F} [Mul M] [Mul N] [Mul P] [FunLike F M N] [MulHomClass F M N]

/-- The natural homomorphism from a magma to its quotient by a congruence relation. -/
@[to_additive (attr := simps) /-- The natural homomorphism from an additive magma to its quotient by
an additive congruence relation. -/]
/--
Definition of `mkMulHom` / `mkMulHom` 的定义

English:
definition mkMulHom
  signature: (c : Con M)
  body: (↑)
  map_mul' _ _ := rfl

中文:
定义 mkMulHom
  签名: (c : Con M)
  定义体: (↑)
  map_mul' _ _ := rfl
-/
def mkMulHom (c : Con M) : MulHom M c.Quotient where
  toFun := (↑)
  map_mul' _ _ := rfl

/-- The kernel of a multiplicative homomorphism as a congruence relation. -/
@[to_additive /-- The kernel of an additive homomorphism as an additive congruence relation. -/]
/--
Definition of `ker` / `ker` 的定义

English:
definition ker
  signature: (f : F)
  body: Setoid.ker f
  mul' h1 h2 := by
    dsimp +instances [Setoid.ker, onFun] at *
    rw [map_mul]; rw [h1]; rw [h2]; rw [map_mul]

@[to_additive (attr := norm_cast)]

中文:
定义 ker
  签名: (f : F)
  定义体: Setoid.ker f
  mul' h1 h2 := by
    dsimp +instances [Setoid.ker, onFun] at *
    rw [map_mul]; rw [h1]; rw [h2]; rw [map_mul]

@[to_additive (attr := norm_cast)]

Depends on / 依赖: Setoid, Setoid.ker
-/
def ker (f : F) : Con M where
  toSetoid := Setoid.ker f
  mul' h1 h2 := by
    dsimp +instances [Setoid.ker, onFun] at *
    rw [map_mul]; rw [h1]; rw [h2]; rw [map_mul]

@[to_additive (attr := norm_cast)]
/--
theorem `ker_coeMulHom` / 定理 `ker_coeMulHom`

English:
theorem ker_coeMulHom
  given: (f : F)
  statement: ker (f : MulHom M N) = ker f
  proof: rfl

中文:
定理 ker_coeMulHom
  条件: (f : F)
  结论: ker (f : 乘法半群态射 M N) = ker f
  证明: rfl
-/
theorem ker_coeMulHom (f : F) : ker (f : MulHom M N) = ker f := rfl

/-- The definition of the congruence relation defined by a monoid homomorphism's kernel. -/
@[to_additive (attr := simp) /-- The definition of the additive congruence relation defined by an
`AddMonoid` homomorphism's kernel. -/]
/--
theorem `ker_rel` / 定理 `ker_rel`

English:
theorem ker_rel
  given: (f : F) {x y}
  statement: ker f x y ↔ f x = f y
  proof: Iff.rfl

@[to_additive (attr := simp) /-- The kernel of the quotient map induced by an additive congruence
relation `c` equals `c`. -/]

中文:
定理 ker_rel
  条件: (f : F) {x y}
  结论: ker f x y ↔ f x = f y
  证明: Iff.rfl

@[to_additive (attr := simp) /-- The kernel of the quotient map induced by an additive congruence
relation `c` equals `c`. -/]

Depends on / 依赖: Iff.rfl
-/
theorem ker_rel (f : F) {x y} : ker f x y ↔ f x = f y :=
  Iff.rfl

@[to_additive (attr := simp) /-- The kernel of the quotient map induced by an additive congruence
relation `c` equals `c`. -/]
/--
theorem `ker_mkMulHom_eq` / 定理 `ker_mkMulHom_eq`

English:
theorem ker_mkMulHom_eq
  given: (c : Con M)
  statement: ker (mkMulHom c) = c
  proof: ext fun _ _ => Quotient.eq''

中文:
定理 ker_mkMulHom_eq
  条件: (c : Con M)
  结论: ker (mkMulHom c) = c
  证明: ext fun _ _ => Quotient.eq''

Depends on / 依赖: Quotient, Quotient.eq
-/
theorem ker_mkMulHom_eq (c : Con M) : ker (mkMulHom c) = c :=
  ext fun _ _ => Quotient.eq''

/-- Given a function `f`, the smallest congruence relation containing the binary relation on `f`'s
image defined by '`x ≈ y` iff the elements of `f⁻¹(x)` are related to the elements of `f⁻¹(y)`
by a congruence relation `c`.' -/
@[to_additive /-- Given a function `f`, the smallest additive congruence relation containing the
binary relation on `f`'s image defined by '`x ≈ y` iff the elements of `f⁻¹(x)` are related to the
elements of `f⁻¹(y)` by an additive congruence relation `c`.' -/]
/--
Definition of `mapGen` / `mapGen` 的定义

English:
definition mapGen
  signature: {c : Con M} (f : M -> N)
  body: conGen Relation.Map c f f

中文:
定义 mapGen
  签名: {c : Con M} (f : M -> N)
  定义体: conGen Relation.Map c f f

Depends on / 依赖: Relation, Relation.Map, conGen
-/
def mapGen {c : Con M} (f : M -> N) : Con N :=
conGen Relation.Map c f f

/-- Given a surjective multiplicative-preserving function `f` whose kernel is contained in a
congruence relation `c`, the congruence relation on `f`'s codomain defined by '`x ≈ y` iff the
elements of `f⁻¹(x)` are related to the elements of `f⁻¹(y)` by `c`.' -/
@[to_additive /-- Given a surjective addition-preserving function `f` whose kernel is contained in
an additive congruence relation `c`, the additive congruence relation on `f`'s codomain defined
by '`x ≈ y` iff the elements of `f⁻¹(x)` are related to the elements of `f⁻¹(y)` by `c`.' -/]
/--
Definition of `mapOfSurjective` / `mapOfSurjective` 的定义

English:
definition mapOfSurjective
  signature: {c : Con M} (f : F) (h : ker f <= c) (hf : Surjective f)
  body: c.toSetoid.mapOfSurjective f h hf
  mul' h₁ h₂ := by
    rcases h₁ with ⟨a, b, h1, rfl, rfl⟩
    rcases h₂ with ⟨p, q, h2, rfl, rfl⟩
    exact ⟨a * p, b * q, c.mul h1 h2, map_mul f _ _, map_mul f _ _⟩

中文:
定义 mapOfSurjective
  签名: {c : Con M} (f : F) (h : ker f <= c) (hf : 满射 f)
  定义体: c.toSetoid.mapOfSurjective f h hf
  mul' h₁ h₂ := by
    rcases h₁ with ⟨a, b, h1, rfl, rfl⟩
    rcases h₂ with ⟨p, q, h2, rfl, rfl⟩
    exact ⟨a * p, b * q, c.mul h1 h2, map_mul f _ _, map_mul f _ _⟩

Depends on / 依赖: c.toSetoid.mapOfSurjective, mapOfSurjective, toSetoid
-/
def mapOfSurjective {c : Con M} (f : F) (h : ker f <= c) (hf : Surjective f) : Con N where
  __ := c.toSetoid.mapOfSurjective f h hf
  mul' h₁ h₂ := by
    rcases h₁ with ⟨a, b, h1, rfl, rfl⟩
    rcases h₂ with ⟨p, q, h2, rfl, rfl⟩
    exact ⟨a * p, b * q, c.mul h1 h2, map_mul f _ _, map_mul f _ _⟩

/-- A specialization of 'the smallest congruence relation containing a congruence relation `c`
equals `c`'. -/
@[to_additive /-- A specialization of 'the smallest additive congruence relation containing
an additive congruence relation `c` equals `c`'. -/]
/--
theorem `mapOfSurjective_eq_mapGen` / 定理 `mapOfSurjective_eq_mapGen`

English:
theorem mapOfSurjective_eq_mapGen
  given: {c : Con M} {f : F} (h : ker f <= c) (hf : Surjective f)
  proof: by
  rw [← conGen_of_con (c.mapOfSurjective f h hf)]; rfl

中文:
定理 mapOfSurjective_eq_mapGen
  条件: {c : Con M} {f : F} (h : ker f <= c) (hf : 满射 f)
  证明: by
  rw [← conGen_of_con (c.mapOfSurjective f h hf)]; rfl

Depends on / 依赖: c.mapOfSurjective, conGen_of_con, mapOfSurjective
-/
theorem mapOfSurjective_eq_mapGen {c : Con M} {f : F} (h : ker f <= c) (hf : Surjective f) :
    c.mapGen f = c.mapOfSurjective f h hf := by
  rw [← conGen_of_con (c.mapOfSurjective f h hf)]; rfl

/-- Given a congruence relation `c` on a type `M` with a multiplication, the order-preserving
bijection between the set of congruence relations containing `c` and the congruence relations
on the quotient of `M` by `c`. -/
@[to_additive /-- Given an additive congruence relation `c` on a type `M` with an addition,
the order-preserving bijection between the set of additive congruence relations containing `c` and
the additive congruence relations on the quotient of `M` by `c`. -/]
/--
Definition of `correspondence` / `correspondence` 的定义

English:
definition correspondence
  signature: {c : Con M}
  body: d.1.mapOfSurjective (mkMulHom c) (by rw [Con.ker_mkMulHom_eq]; exact d.2)
      Quotient.mk_surjective
  invFun d :=
    ⟨comap ((↑) : M -> c.Quotient) (fun _ _ => rfl) d, fun x y h =>
      show d x y by rw [c.eq.2 h]; exact d.refl _⟩
  left_inv d :=
Subtype.ext_iff.2
      ext fun x y =>
        ⟨

中文:
定义 correspondence
  签名: {c : Con M}
  定义体: d.1.mapOfSurjective (mkMulHom c) (by rw [Con.ker_mkMulHom_eq]; exact d.2)
      Quotient.mk_surjective
  invFun d :=
    ⟨comap ((↑) : M -> c.Quotient) (fun _ _ => rfl) d, fun x y h =>
      show d x y by rw [c.eq.2 h]; exact d.refl _⟩
  left_inv d :=
Subtype.ext_iff.2
      ext fun x y =>
        ⟨

Depends on / 依赖: Con.ext, Con.induction_on, Con.ker_mkMulHom_eq, IsStablyFiniteRing, Matrix, Matrix.mul_smul, Quotient, Quotient.mk_surjective, Subtype, Subtype.ext_iff, add_add_add_comm, add_assoc, add_smul, c.Quotient, c.eq, d.refl, detp_mul, detp_neg_one_one, detp_one_one, detp_smul_adjp
-/
def correspondence {c : Con M} : { d // c <= d } ≃o Con c.Quotient where
  toFun d :=
d.1.mapOfSurjective (mkMulHom c) (by rw [Con.ker_mkMulHom_eq]; exact d.2)
      Quotient.mk_surjective
  invFun d :=
    ⟨comap ((↑) : M -> c.Quotient) (fun _ _ => rfl) d, fun x y h =>
      show d x y by rw [c.eq.2 h]; exact d.refl _⟩
  left_inv d :=
Subtype.ext_iff.2
      ext fun x y =>
        ⟨fun ⟨a, b, H, hx, hy⟩ =>
d.1.trans (d.1.symm <| d.2 <| c.eq.1 hx) d.1.trans H d.2 c.eq.1 hy,
          fun h => ⟨_, _, h, rfl, rfl⟩⟩
  right_inv d :=
    Con.ext fun x y => by
      refine ⟨?_, Con.induction_on₂ x y fun w z h => ⟨w, z, h, rfl, rfl⟩⟩
      rintro ⟨a, b, H, rfl, rfl⟩
      exact H
  map_rel_iff' {s t} := by
    constructor
    · intro h x y hs
      rcases h ⟨x, y, hs, rfl, rfl⟩ with ⟨a, b, ht, hx, hy⟩
      exact t.1.trans (t.1.symm <| t.2 <| c.eq.1 hx) (t.1.trans ht (t.2 <| c.eq.1 hy))
    · exact Relation.map_mono

end Mul

section MulOneClass

variable [MulOneClass M] [MulOneClass N] [MulOneClass P] {c : Con M}

variable (c)

/-- The natural homomorphism from a monoid to its quotient by a congruence relation. -/
@[to_additive /-- The natural homomorphism from an `AddMonoid` to its quotient by an additive
congruence relation. -/]
/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: : M ->* c.Quotient where
  body: mkMulHom c
  map_one' := rfl

中文:
定义 mk'
  签名: : M ->* c.商 where
  定义体: mkMulHom c
  map_one' := rfl

Depends on / 依赖: mkMulHom
-/
def mk' : M ->* c.Quotient where
  __ := mkMulHom c
  map_one' := rfl

variable (x y : M)

/-- The kernel of the natural homomorphism from a monoid to its quotient by a congruence
relation `c` equals `c`. -/
@[to_additive (attr := simp) /-- The kernel of the natural homomorphism from an `AddMonoid` to its
quotient by an additive congruence relation `c` equals `c`. -/]
/--
theorem `mk'_ker` / 定理 `mk'_ker`

English:
theorem mk'_ker
  statement: ker c.mk' = c
  proof: ext fun _ _ => c.eq

中文:
定理 mk'_ker
  结论: ker c.mk' = c
  证明: ext fun _ _ => c.eq

Depends on / 依赖: Finset, Finset.smul_sum, Finset.sum_congr, Matrix, Matrix.toLinearMap, ite_smul, mem_univ, one_smul, reduceIte, simp_rw, smul_sum, sum_congr, sum_ite_eq, zero_smul
-/
theorem mk'_ker : ker c.mk' = c :=
  ext fun _ _ => c.eq

variable {c}

/-- The natural homomorphism from a monoid to its quotient by a congruence relation is
surjective. -/
@[to_additive /-- The natural homomorphism from an `AddMonoid` to its quotient by a congruence
relation is surjective. -/]
/--
theorem `mk'_surjective` / 定理 `mk'_surjective`

English:
theorem mk'_surjective
  statement: Surjective c.mk'
  proof: Quotient.mk''_surjective

@[to_additive (attr := simp)]

中文:
定理 mk'_surjective
  结论: 满射 c.mk'
  证明: Quotient.mk''_surjective

@[to_additive (attr := simp)]
-/
theorem mk'_surjective : Surjective c.mk' :=
  Quotient.mk''_surjective

@[to_additive (attr := simp)]
/--
theorem `coe_mk'` / 定理 `coe_mk'`

English:
theorem coe_mk'
  statement: (c.mk' : M -> c.Quotient) = ((↑) : M -> c.Quotient)
  proof: rfl

@[to_additive]

中文:
定理 coe_mk'
  结论: (c.mk' : M -> c.商) = ((↑) : M -> c.商)
  证明: rfl

@[to_additive]
-/
theorem coe_mk' : (c.mk' : M -> c.Quotient) = ((↑) : M -> c.Quotient) :=
  rfl

@[to_additive]
/--
theorem `ker_apply` / 定理 `ker_apply`

English:
theorem ker_apply
  given: {f : M ->* P} {x y}
  statement: ker f x y ↔ f x = f y
  proof: Iff.rfl

中文:
定理 ker_apply
  条件: {f : M ->* P} {x y}
  结论: ker f x y ↔ f x = f y
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem ker_apply {f : M ->* P} {x y} : ker f x y ↔ f x = f y := Iff.rfl

/-- Given a monoid homomorphism `f : N → M` and a congruence relation `c` on `M`, the congruence
relation induced on `N` by `f` equals the kernel of `c`'s quotient homomorphism composed with
`f`. -/
@[to_additive /-- Given an `AddMonoid` homomorphism `f : N → M` and an additive congruence relation
`c` on `M`, the additive congruence relation induced on `N` by `f` equals the kernel of `c`'s
quotient homomorphism composed with `f`. -/]
/--
theorem `comap_eq` / 定理 `comap_eq`

English:
theorem comap_eq
  given: {f : N ->* M}
  statement: comap f f.map_mul c = ker (c.mk'.comp f)
  proof: ext fun x y => show c _ _ ↔ c.mk' _ = c.mk' _ by rw [← c.eq]; rfl

中文:
定理 comap_eq
  条件: {f : N ->* M}
  结论: comap f f.map_mul c = ker (c.mk'.comp f)
  证明: ext fun x y => show c _ _ ↔ c.mk' _ = c.mk' _ by rw [← c.eq]; rfl

Depends on / 依赖: c.eq, c.mk
-/
theorem comap_eq {f : N ->* M} : comap f f.map_mul c = ker (c.mk'.comp f) :=
  ext fun x y => show c _ _ ↔ c.mk' _ = c.mk' _ by rw [← c.eq]; rfl

variable (c) (f : M ->* P)

set_option backward.isDefEq.respectTransparency false in
/-- The homomorphism on the quotient of a monoid by a congruence relation `c` induced by a
homomorphism constant on `c`'s equivalence classes. -/
@[to_additive /-- The homomorphism on the quotient of an `AddMonoid` by an additive congruence
relation `c` induced by a homomorphism constant on `c`'s equivalence classes. -/]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (H : c <= ker f)
  body: (Con.liftOn x f) fun _ _ h => H h
  map_one' := by rw [← f.map_one]; rfl
  map_mul' x y := Con.induction_on₂ x y fun m n => by
    dsimp only [← coe_mul, Con.liftOn_coe]
    rw [map_mul]

中文:
定义 lift
  签名: (H : c <= ker f)
  定义体: (Con.liftOn x f) fun _ _ h => H h
  map_one' := by rw [← f.map_one]; rfl
  map_mul' x y := Con.induction_on₂ x y fun m n => by
    dsimp only [← coe_mul, Con.liftOn_coe]
    rw [map_mul]

Depends on / 依赖: Con.liftOn, liftOn
-/
def lift (H : c <= ker f) : c.Quotient ->* P where
  toFun x := (Con.liftOn x f) fun _ _ h => H h
  map_one' := by rw [← f.map_one]; rfl
  map_mul' x y := Con.induction_on₂ x y fun m n => by
    dsimp only [← coe_mul, Con.liftOn_coe]
    rw [map_mul]

variable {c f}

/-- The diagram describing the universal property for quotients of monoids commutes. -/
@[to_additive /-- The diagram describing the universal property for quotients of `AddMonoid`s
commutes. -/]
/--
theorem `lift_mk'` / 定理 `lift_mk'`

English:
theorem lift_mk'
  given: (H : c <= ker f) (x)
  statement: c.lift f H (c.mk' x) = f x
  proof: rfl

中文:
定理 lift_mk'
  条件: (H : c <= ker f) (x)
  结论: c.lift f H (c.mk' x) = f x
  证明: rfl
-/
theorem lift_mk' (H : c <= ker f) (x) : c.lift f H (c.mk' x) = f x :=
  rfl

/-- The diagram describing the universal property for quotients of monoids commutes. -/
@[to_additive (attr := simp) /-- The diagram describing the universal property for quotients of
`AddMonoid`s commutes. -/]
/--
theorem `lift_coe` / 定理 `lift_coe`

English:
theorem lift_coe
  given: (H : c <= ker f) (x : M)
  statement: c.lift f H x = f x
  proof: rfl

中文:
定理 lift_coe
  条件: (H : c <= ker f) (x : M)
  结论: c.lift f H x = f x
  证明: rfl
-/
theorem lift_coe (H : c <= ker f) (x : M) : c.lift f H x = f x :=
  rfl

/-- The diagram describing the universal property for quotients of monoids commutes. -/
@[to_additive (attr := simp) /-- The diagram describing the universal property for quotients of
`AddMonoid`s commutes. -/]
/--
theorem `lift_comp_mk'` / 定理 `lift_comp_mk'`

English:
theorem lift_comp_mk'
  given: (H : c <= ker f)
  statement: (c.lift f H).comp c.mk' = f
  proof: by ext; rfl

中文:
定理 lift_comp_mk'
  条件: (H : c <= ker f)
  结论: (c.lift f H).comp c.mk' = f
  证明: by ext; rfl

Depends on / 依赖: LinearMap, LinearMap.toMatrix
-/
theorem lift_comp_mk' (H : c <= ker f) : (c.lift f H).comp c.mk' = f := by ext; rfl

/-- Given a homomorphism `f` from the quotient of a monoid by a congruence relation, `f` equals the
homomorphism on the quotient induced by `f` composed with the natural map from the monoid to
the quotient. -/
@[to_additive (attr := simp) /-- Given a homomorphism `f` from the quotient of an `AddMonoid` by an
additive congruence relation, `f` equals the homomorphism on the quotient induced by `f` composed
with the natural map from the `AddMonoid` to the quotient. -/]
/--
theorem `lift_apply_mk'` / 定理 `lift_apply_mk'`

English:
theorem lift_apply_mk'
  given: (f : c.Quotient ->* P)
  proof: by
  ext x; rcases x with ⟨⟩; rfl

中文:
定理 lift_apply_mk'
  条件: (f : c.商 ->* P)
  证明: by
  ext x; rcases x with ⟨⟩; rfl
-/
theorem lift_apply_mk' (f : c.Quotient ->* P) :
    (c.lift (f.comp c.mk') fun x y h => show f ↑x = f ↑y by rw [c.eq.2 h]) = f := by
  ext x; rcases x with ⟨⟩; rfl

/-- Homomorphisms on the quotient of a monoid by a congruence relation `c` are equal if their
compositions with `c.mk'` are equal. -/
@[to_additive (attr := ext) /-- Homomorphisms on the quotient of an `AddMonoid` by an additive
congruence relation `c` are equal if their compositions with `c.mk'` are equal. -/]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {f g : c.Quotient ->* P} (h : f.comp c.mk' = g.comp c.mk')
  statement: f = g
  proof: by
  rw [← lift_apply_mk' f]; rw [← lift_apply_mk' g]
  congr 1

中文:
引理 hom_ext
  条件: {f g : c.商 ->* P} (h : f.comp c.mk' = g.comp c.mk')
  结论: f = g
  证明: by
  rw [← lift_apply_mk' f]; rw [← lift_apply_mk' g]
  congr 1

Depends on / 依赖: Finset, Finset.sum_congr, LinearEquiv, LinearEquiv.coe_symm_mk, coe_symm_mk, lift_apply_mk, smul_comm, sum_congr
-/
lemma hom_ext {f g : c.Quotient ->* P} (h : f.comp c.mk' = g.comp c.mk') : f = g := by
  rw [← lift_apply_mk' f]; rw [← lift_apply_mk' g]
  congr 1

/-- Homomorphisms on the quotient of a monoid by a congruence relation are equal if they
are equal on elements that are coercions from the monoid. -/
@[to_additive /-- Homomorphisms on the quotient of an `AddMonoid` by an additive congruence relation
are equal if they are equal on elements that are coercions from the `AddMonoid`. -/]
/--
theorem `lift_funext` / 定理 `lift_funext`

English:
theorem lift_funext
  given: (f g : c.Quotient ->* P) (h : forall a : M, f a = g a)
  statement: f = g
  proof: hom_ext DFunLike.ext _ _ h

中文:
定理 lift_funext
  条件: (f g : c.商 ->* P) (h : 对任意 a : M, f a = g a)
  结论: f = g
  证明: hom_ext DFunLike.ext _ _ h

Depends on / 依赖: DFunLike, DFunLike.ext, Finset, Finset.sum_congr, RingHom, RingHom.id_apply, hom_ext, id_apply, smul_comm, sum_congr
-/
theorem lift_funext (f g : c.Quotient ->* P) (h : forall a : M, f a = g a) : f = g :=
hom_ext DFunLike.ext _ _ h

/-- The uniqueness part of the universal property for quotients of monoids. -/
@[to_additive /-- The uniqueness part of the universal property for quotients of `AddMonoid`s. -/]
/--
theorem `lift_unique` / 定理 `lift_unique`

English:
theorem lift_unique
  given: (H : c <= ker f) (g : c.Quotient ->* P) (Hg : g.comp c.mk' = f)
  proof: hom_ext Hg

中文:
定理 lift_unique
  条件: (H : c <= ker f) (g : c.商 ->* P) (Hg : g.comp c.mk' = f)
  证明: hom_ext Hg

Depends on / 依赖: Finset, Finset.mul_sum, Finset.sum_congr, Matrix, Matrix.mulVec, Matrix.toLinearMap, _apply, dotProduct, hom_ext, mulVec, mul_assoc, mul_comm, mul_sum, simp_rw, smul_eq_mul, sum_congr
-/
theorem lift_unique (H : c <= ker f) (g : c.Quotient ->* P) (Hg : g.comp c.mk' = f) :
    g = c.lift f H :=
  hom_ext Hg

/-- Surjective monoid homomorphisms constant on a congruence relation `c`'s equivalence classes
induce a surjective homomorphism on `c`'s quotient. -/
@[to_additive /-- Surjective `AddMonoid` homomorphisms constant on an additive congruence
relation `c`'s equivalence classes induce a surjective homomorphism on `c`'s quotient. -/]
/--
theorem `lift_surjective_of_surjective` / 定理 `lift_surjective_of_surjective`

English:
theorem lift_surjective_of_surjective
  given: (h : c <= ker f) (hf : Surjective f)
  proof: fun y =>
  (Exists.elim (hf y)) fun w hw => ⟨w, (lift_mk' h w).symm ▸ hw⟩

中文:
定理 lift_surjective_of_surjective
  条件: (h : c <= ker f) (hf : 满射 f)
  证明: fun y =>
  (Exists.elim (hf y)) fun w hw => ⟨w, (lift_mk' h w).symm ▸ hw⟩

Depends on / 依赖: Aux_single, Matrix, Matrix.toLinearMap
-/
theorem lift_surjective_of_surjective (h : c <= ker f) (hf : Surjective f) :
    Surjective (c.lift f h) := fun y =>
  (Exists.elim (hf y)) fun w hw => ⟨w, (lift_mk' h w).symm ▸ hw⟩

variable (c f)

/-- Given a monoid homomorphism `f` from `M` to `P`, the kernel of `f` is the unique congruence
relation on `M` whose induced map from the quotient of `M` to `P` is injective. -/
@[to_additive /-- Given an `AddMonoid` homomorphism `f` from `M` to `P`, the kernel of `f`
is the unique additive congruence relation on `M` whose induced map from the quotient of `M`
to `P` is injective. -/]
/--
theorem `ker_eq_lift_of_injective` / 定理 `ker_eq_lift_of_injective`

English:
theorem ker_eq_lift_of_injective
  given: (H : c <= ker f) (h : Injective (c.lift f H))
  statement: ker f = c
  proof: toSetoid_injective Setoid.ker_eq_lift_of_injective f H h

中文:
定理 ker_eq_lift_of_injective
  条件: (H : c <= ker f) (h : 单射 (c.lift f H))
  结论: ker f = c
  证明: toSetoid_injective Setoid.ker_eq_lift_of_injective f H h

Depends on / 依赖: Aux_single, Matrix, Matrix.toLinearMap, Setoid, Setoid.ker_eq_lift_of_injective, ker_eq_lift_of_injective, toSetoid_injective
-/
theorem ker_eq_lift_of_injective (H : c <= ker f) (h : Injective (c.lift f H)) : ker f = c :=
toSetoid_injective Setoid.ker_eq_lift_of_injective f H h

variable {c}

/-- The homomorphism induced on the quotient of a monoid by the kernel of a monoid homomorphism. -/
@[to_additive /-- The homomorphism induced on the quotient of an `AddMonoid` by the kernel
of an `AddMonoid` homomorphism. -/]
/--
Definition of `kerLift` / `kerLift` 的定义

English:
definition kerLift
  signature: : (ker f).Quotient ->* P
  body: ((ker f).lift f) fun _ _ => id

中文:
定义 kerLift
  签名: : (ker f).商 ->* P
  定义体: ((ker f).lift f) fun _ _ => id
-/
def kerLift : (ker f).Quotient ->* P :=
  ((ker f).lift f) fun _ _ => id

variable {f}

/-- The diagram described by the universal property for quotients of monoids, when the congruence
relation is the kernel of the homomorphism, commutes. -/
@[to_additive (attr := simp) /-- The diagram described by the universal property for quotients
of `AddMonoid`s, when the additive congruence relation is the kernel of the homomorphism,
commutes. -/]
/--
theorem `kerLift_mk` / 定理 `kerLift_mk`

English:
theorem kerLift_mk
  given: (x : M)
  statement: kerLift f x = f x
  proof: rfl

中文:
定理 kerLift_mk
  条件: (x : M)
  结论: kerLift f x = f x
  证明: rfl

Depends on / 依赖: LinearMap, LinearMap.toMatrix, symm_symm
-/
theorem kerLift_mk (x : M) : kerLift f x = f x :=
  rfl

/-- A monoid homomorphism `f` induces an injective homomorphism on the quotient by `f`'s kernel. -/
@[to_additive /-- An `AddMonoid` homomorphism `f` induces an injective homomorphism on the quotient
by `f`'s kernel. -/]
/--
theorem `kerLift_injective` / 定理 `kerLift_injective`

English:
theorem kerLift_injective
  given: (f : M ->* P)
  statement: Injective (kerLift f)
  proof: fun x y =>
  Quotient.inductionOn₂' x y fun _ _ => (ker f).eq.2

中文:
定理 kerLift_injective
  条件: (f : M ->* P)
  结论: 单射 (kerLift f)
  证明: fun x y =>
  Quotient.inductionOn₂' x y fun _ _ => (ker f).eq.2

Depends on / 依赖: Matrix, Matrix.toLinearMap, apply_symm_apply
-/
theorem kerLift_injective (f : M ->* P) : Injective (kerLift f) := fun x y =>
  Quotient.inductionOn₂' x y fun _ _ => (ker f).eq.2

/-- Given congruence relations `c, d` on a monoid such that `d` contains `c`, `d`'s quotient
map induces a homomorphism from the quotient by `c` to the quotient by `d`. -/
@[to_additive /-- Given additive congruence relations `c, d` on an `AddMonoid` such that `d`
contains `c`, `d`'s quotient map induces a homomorphism from the quotient by `c` to the quotient
by `d`. -/]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (c d : Con M) (h : c <= d)
  body: (c.lift d.mk') fun x y hc => show (ker d.mk') x y from (mk'_ker d).symm ▸ h hc

中文:
定义 map
  签名: (c d : Con M) (h : c <= d)
  定义体: (c.lift d.mk') fun x y hc => show (ker d.mk') x y from (mk'_ker d).symm ▸ h hc

Depends on / 依赖: Matrix, Matrix.toLinearMap, _ker, apply_symm_apply, c.lift, d.mk
-/
def map (c d : Con M) (h : c <= d) : c.Quotient ->* d.Quotient :=
  (c.lift d.mk') fun x y hc => show (ker d.mk') x y from (mk'_ker d).symm ▸ h hc

/-- Given congruence relations `c, d` on a monoid such that `d` contains `c`, the definition of
the homomorphism from the quotient by `c` to the quotient by `d` induced by `d`'s quotient map. -/
@[to_additive /-- Given additive congruence relations `c, d` on an `AddMonoid` such that `d`
contains `c`, the definition of the homomorphism from the quotient by `c` to the quotient by `d`
induced by `d`'s quotient map. -/]
/--
theorem `map_apply` / 定理 `map_apply`

English:
theorem map_apply
  given: {c d : Con M} (h : c <= d) (x)
  proof: rfl

中文:
定理 map_apply
  条件: {c d : Con M} (h : c <= d) (x)
  证明: rfl

Depends on / 依赖: LinearMap, LinearMap.toMatrix, apply_symm_apply
-/
theorem map_apply {c d : Con M} (h : c <= d) (x) :
    c.map d h x = c.lift d.mk' (fun _ _ hc => d.eq.2 <| h hc) x :=
  rfl

end MulOneClass

end Con
