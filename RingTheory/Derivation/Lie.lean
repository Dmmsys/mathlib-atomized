/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Andrew Yang
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Algebra.Lie.Prod

/-!
# Lie Algebra Structure on Derivations

## Main statements

- `Derivation.instLieAlgebra`: The `R`-derivations from `A` to `A` form a Lie algebra over `R`.

-/

@[expose] public section


namespace Derivation

variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [Algebra R A]
variable {D1 D2 : Derivation R A A} (a : A)

section LieStructures

/-! ### Lie structures -/


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bracket (Derivation R A A) (Derivation R A A)
  body: ⟨fun D1 D2 =>
    mk' ⁅(D1 : Module.End R A), (D2 : Module.End R A)⁆ fun a b => by
      simp only [Ring.lie_def, map_add, smul_eq_mul, Module.End.mul_apply, leibniz,
        coeFn_coe, LinearMap.sub_apply]
      ring⟩

@[simp]

中文:
实例 :
  签名: Bracket (Derivation R A A) (Derivation R A A)
  定义体: ⟨fun D1 D2 =>
    mk' ⁅(D1 : Module.End R A), (D2 : Module.End R A)⁆ fun a b => by
      simp only [Ring.lie_def, map_add, smul_eq_mul, Module.End.mul_apply, leibniz,
        coeFn_coe, LinearMap.sub_apply]
      ring⟩

@[simp]

Depends on / 依赖: LinearMap, LinearMap.sub_apply, Module, Module.End, Module.End.mul_apply, Ring.lie_def, coeFn_coe, leibniz, lie_def, map_add, mul_apply, smul_eq_mul, sub_apply
-/
instance : Bracket (Derivation R A A) (Derivation R A A) :=
  ⟨fun D1 D2 =>
    mk' ⁅(D1 : Module.End R A), (D2 : Module.End R A)⁆ fun a b => by
      simp only [Ring.lie_def, map_add, smul_eq_mul, Module.End.mul_apply, leibniz,
        coeFn_coe, LinearMap.sub_apply]
      ring⟩

@[simp]
/--
theorem `commutator_coe_linear_map` / 定理 `commutator_coe_linear_map`

English:
theorem commutator_coe_linear_map
  statement: ↑⁅D1, D2⁆ = ⁅(D1 : Module.End R A), (D2 : Module.End R A)⁆
  proof: rfl

中文:
定理 commutator_coe_linear_map
  结论: ↑⁅D1, D2⁆ = ⁅(D1 : Module.End R A), (D2 : Module.End R A)⁆
  证明: rfl
-/
theorem commutator_coe_linear_map : ↑⁅D1, D2⁆ = ⁅(D1 : Module.End R A), (D2 : Module.End R A)⁆ :=
  rfl

/--
theorem `commutator_apply` / 定理 `commutator_apply`

English:
theorem commutator_apply
  statement: ⁅D1, D2⁆ a = D1 (D2 a) - D2 (D1 a)
  proof: rfl

中文:
定理 commutator_apply
  结论: ⁅D1, D2⁆ a = D1 (D2 a) - D2 (D1 a)
  证明: rfl
-/
theorem commutator_apply : ⁅D1, D2⁆ a = D1 (D2 a) - D2 (D1 a) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LieRing (Derivation R A A)
  body: by ext a; simp only [commutator_apply, add_apply, map_add]; ring
  lie_add d e f := by ext a; simp only [commutator_apply, add_apply, map_add]; ring
  lie_self d := by ext a; simp only [commutator_apply]; ring_nf; simp
  leibniz_lie d e f := by ext a; simp only [commutator_apply, add_apply, map_sub]

中文:
实例 :
  签名: LieRing (Derivation R A A)
  定义体: by ext a; simp only [commutator_apply, add_apply, map_add]; ring
  lie_add d e f := by ext a; simp only [commutator_apply, add_apply, map_add]; ring
  lie_self d := by ext a; simp only [commutator_apply]; ring_nf; simp
  leibniz_lie d e f := by ext a; simp only [commutator_apply, add_apply, map_sub]

Depends on / 依赖: add_apply, commutator_apply, leibniz_lie, lie_add, lie_self, map_add, map_sub, ring_nf
-/
instance : LieRing (Derivation R A A) where
  add_lie d e f := by ext a; simp only [commutator_apply, add_apply, map_add]; ring
  lie_add d e f := by ext a; simp only [commutator_apply, add_apply, map_add]; ring
  lie_self d := by ext a; simp only [commutator_apply]; ring_nf; simp
  leibniz_lie d e f := by ext a; simp only [commutator_apply, add_apply, map_sub]; ring

/--
Instance `instLieAlgebra` / 实例 `instLieAlgebra`

English:
instance instLieAlgebra
  signature: : LieAlgebra R (Derivation R A A)
  body: { Derivation.instModule with
    lie_smul := fun r d e => by
      ext a; simp only [commutator_apply, map_smul, smul_sub, smul_apply] }

中文:
实例 instLieAlgebra
  签名: : LieAlgebra R (Derivation R A A)
  定义体: { Derivation.instModule with
    lie_smul := fun r d e => by
      ext a; simp only [commutator_apply, map_smul, smul_sub, smul_apply] }

Depends on / 依赖: Derivation, Derivation.instModule, commutator_apply, instModule, lie_smul, map_smul, smul_apply, smul_sub
-/
instance instLieAlgebra : LieAlgebra R (Derivation R A A) :=
  { Derivation.instModule with
    lie_smul := fun r d e => by
      ext a; simp only [commutator_apply, map_smul, smul_sub, smul_apply] }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LieRingModule (Derivation R A A) A
  body: X a
  add_lie _ _ m := add_apply m
  lie_add _ _ _ := Derivation.map_add _ _ _
  leibniz_lie _ _ _ := by rw [commutator_apply]; abel

中文:
实例 :
  签名: LieRingModule (Derivation R A A) A
  定义体: X a
  add_lie _ _ m := add_apply m
  lie_add _ _ _ := Derivation.map_add _ _ _
  leibniz_lie _ _ _ := by rw [commutator_apply]; abel
-/
instance : LieRingModule (Derivation R A A) A where
  bracket X a := X a
  add_lie _ _ m := add_apply m
  lie_add _ _ _ := Derivation.map_add _ _ _
  leibniz_lie _ _ _ := by rw [commutator_apply]; abel

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LieModule R (Derivation R A A) A
  body: rfl
  lie_smul _ _ _ := Derivation.map_smul_of_tower _ _ _

@[simp]

中文:
实例 :
  签名: LieModule R (Derivation R A A) A
  定义体: rfl
  lie_smul _ _ _ := Derivation.map_smul_of_tower _ _ _

@[simp]
-/
instance : LieModule R (Derivation R A A) A where
  smul_lie _ _ _ := rfl
  lie_smul _ _ _ := Derivation.map_smul_of_tower _ _ _

@[simp]
/--
lemma `bracket_eq_fun` / 引理 `bracket_eq_fun`

English:
lemma bracket_eq_fun
  given: (X : Derivation R A A) (a : A)
  statement: ⁅X, a⁆ = X a
  proof: rfl

中文:
引理 bracket_eq_fun
  条件: (X : Derivation R A A) (a : A)
  结论: ⁅X, a⁆ = X a
  证明: rfl
-/
lemma bracket_eq_fun (X : Derivation R A A) (a : A) : ⁅X, a⁆ = X a := rfl

section CompatibleDerivations
variable {A' : Type*} [CommRing A'] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']
attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false in
variable (R A A') in
/--
Definition of `couple` / `couple` 的定义

English:
definition couple
  signature: : LieSubalgebra R (Derivation R A' A' × Derivation R A A) where
  body: { x | x.fst.compAlgebraMapL R A A' A' = (Algebra.ofId A A').toLinearMap.compDer x.snd }
  add_mem' := by simp_all
  zero_mem' := by simp
  smul_mem' := by simp_all
  lie_mem' {x y} hx hy := by
    have hxx (a : A) := congrArg (fun f => f a) hx
    have hyy (a : A) := congrArg (fun f => f a) hy
    e

中文:
定义 couple
  签名: : LieSubalgebra R (Derivation R A' A' × Derivation R A A) where
  定义体: { x | x.fst.compAlgebraMapL R A A' A' = (Algebra.ofId A A').toLinearMap.compDer x.snd }
  add_mem' := by simp_all
  zero_mem' := by simp
  smul_mem' := by simp_all
  lie_mem' {x y} hx hy := by
    have hxx (a : A) := congrArg (fun f => f a) hx
    have hyy (a : A) := congrArg (fun f => f a) hy
    e

Depends on / 依赖: Algebra, Algebra.ofId, compAlgebraMapL, compDer, toLinearMap, toLinearMap.compDer, x.fst.compAlgebraMapL, x.snd
-/
def couple : LieSubalgebra R (Derivation R A' A' × Derivation R A A) where
  carrier := { x | x.fst.compAlgebraMapL R A A' A' = (Algebra.ofId A A').toLinearMap.compDer x.snd }
  add_mem' := by simp_all
  zero_mem' := by simp
  smul_mem' := by simp_all
  lie_mem' {x y} hx hy := by
    have hxx (a : A) := congrArg (fun f => f a) hx
    have hyy (a : A) := congrArg (fun f => f a) hy
    ext z
    simp at hxx hyy
    simp [Derivation.commutator_apply, hxx, hyy]

namespace Compatible
/--
lemma `mem` / 引理 `mem`

English:
lemma mem
  given: (x : (Derivation R A' A') × (Derivation R A A))
  proof: by
  constructor
  · intro hx; ext a; exact congrArg (· a) hx
  · intro hx; ext a; exact congrArg (· a) hx

中文:
引理 mem
  条件: (x : (Derivation R A' A') × (Derivation R A A))
  证明: by
  constructor
  · intro hx; ext a; exact congrArg (· a) hx
  · intro hx; ext a; exact congrArg (· a) hx
-/
lemma mem (x : (Derivation R A' A') × (Derivation R A A)) :
    x in couple R A A' ↔ x.1 ∘ Algebra.ofId A A' = Algebra.ofId A A' ∘ x.2 := by
  constructor
  · intro hx; ext a; exact congrArg (· a) hx
  · intro hx; ext a; exact congrArg (· a) hx

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (x : Derivation R A' A') (y : Derivation R A A)
  body: ⟨(x, y), (Compatible.mem _).mpr h⟩

中文:
定义 mk
  签名: (x : Derivation R A' A') (y : Derivation R A A)
  定义体: ⟨(x, y), (Compatible.mem _).mpr h⟩

Depends on / 依赖: Compatible, Compatible.mem, Inhabited, y.Type
-/
def mk (x : Derivation R A' A') (y : Derivation R A A)
  (h : x ∘ (Algebra.ofId A A') = (Algebra.ofId A A') ∘ y) : couple R A A' :=
⟨(x, y), (Compatible.mem _).mpr h⟩

/--
lemma `mk_left` / 引理 `mk_left`

English:
lemma mk_left
  statement: (x : Derivation R A' A') (y : Derivation R A A)
  proof: rfl

中文:
引理 mk_left
  结论: (x : Derivation R A' A') (y : Derivation R A A)
  证明: rfl
-/
lemma mk_left (x : Derivation R A' A') (y : Derivation R A A)
    (h : x ∘ (Algebra.ofId A A') = (Algebra.ofId A A') ∘ y) : (mk x y h).1.1 = x := rfl

/--
lemma `mk_right` / 引理 `mk_right`

English:
lemma mk_right
  statement: (x : Derivation R A' A') (y : Derivation R A A)
  proof: rfl

中文:
引理 mk_right
  结论: (x : Derivation R A' A') (y : Derivation R A A)
  证明: rfl
-/
lemma mk_right (x : Derivation R A' A') (y : Derivation R A A)
    (h : x ∘ (Algebra.ofId A A') = (Algebra.ofId A A') ∘ y) : (mk x y h).1.2 = y := rfl

/--
lemma `apply` / 引理 `apply`

English:
lemma apply
  given: (x : couple R A A') (a : A)
  proof: by
  exact congrArg (· a) x.2

中文:
引理 apply
  条件: (x : couple R A A') (a : A)
  证明: by
  exact congrArg (· a) x.2
-/
lemma apply (x : couple R A A') (a : A) :
    x.1.1 (Algebra.ofId A A' a) = (Algebra.ofId A A') (x.1.2 a) := by
  exact congrArg (· a) x.2

end Compatible

end CompatibleDerivations

end LieStructures

end Derivation
