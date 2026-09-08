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


/-- The commutator of derivations is again a derivation. -/
/-
**Derivation.** 是 Mathlib 中的一个实例，位于命名空间 `Derivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The commutator of derivations is again a derivation.
-/
instance : Bracket (Derivation R A A) (Derivation R A A) :=
  ⟨fun D1 D2 =>
    mk' ⁅(D1 : Module.End R A), (D2 : Module.End R A)⁆ fun a b => by
      simp only [Ring.lie_def, map_add, smul_eq_mul, Module.End.mul_apply, leibniz,
        coeFn_coe, LinearMap.sub_apply]
      ring⟩

@[simp]
/-
**Derivation.commutator_coe_linear_map** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：commutator_coe_linear_map : ↑⁅D1, D2⁆ = ⁅(D1 : Module.End R A), (D2 : Modu
le.End R A)⁆
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem commutator_coe_linear_map : ↑⁅D1, D2⁆ = ⁅(D1 : Module.End R A), (D2 : Module.End R A)⁆ :=
  rfl
/-
**Derivation.commutator_apply** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：commutator_apply : ⁅D1, D2⁆ a = D1 (D2 a) - D2 (D1 a)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem commutator_apply : ⁅D1, D2⁆ a = D1 (D2 a) - D2 (D1 a) :=
  rfl
/-
**Derivation.** 是 Mathlib 中的一个实例，位于命名空间 `Derivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LieRing (Derivation R A A) where
  add_lie d e f := by ext a; simp only [commutator_apply, add_apply, map_add]; ring
  lie_add d e f := by ext a; simp only [commutator_apply, add_apply, map_add]; ring
  lie_self d := by ext a; simp only [commutator_apply]; ring_nf; simp
  leibniz_lie d e f := by ext a; simp only [commutator_apply, add_apply, map_sub]; ring
/-
**Derivation.instLieAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `Derivation`。
形式化陈述：instLieAlgebra : LieAlgebra R (Derivation R A A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLieAlgebra : LieAlgebra R (Derivation R A A) :=
  { Derivation.instModule with
    lie_smul := fun r d e => by
      ext a; simp only [commutator_apply, map_smul, smul_sub, smul_apply] }
/-
**Derivation.** 是 Mathlib 中的一个实例，位于命名空间 `Derivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LieRingModule (Derivation R A A) A where
  bracket X a := X a
  add_lie _ _ m := add_apply m
  lie_add _ _ _ := Derivation.map_add _ _ _
  leibniz_lie _ _ _ := by rw [commutator_apply]; abel
/-
**Derivation.** 是 Mathlib 中的一个实例，位于命名空间 `Derivation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LieModule R (Derivation R A A) A where
  smul_lie _ _ _ := rfl
  lie_smul _ _ _ := Derivation.map_smul_of_tower _ _ _

@[simp]
/-
**Derivation.bracket_eq_fun** 是 Mathlib 中的一个引理，位于命名空间 `Derivation`。
形式化陈述：bracket_eq_fun (X : Derivation R A A) (a : A) : ⁅X, a⁆ = X a
参数：X : Derivation R A A；a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma bracket_eq_fun (X : Derivation R A A) (a : A) : ⁅X, a⁆ = X a := rfl

section CompatibleDerivations
variable {A' : Type*} [CommRing A'] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']
attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false in
variable (R A A') in
/-- Let `σ : A → A'` be a an homomorphism. A derivation `d : A → A` and a derivation
`d' : A' → A'` are called compatible if `d' ∘ σ = σ ∘ d`. Couples of derivations
with this property form a Lie subalgebra of all couples of derivations. -/
/-
**Derivation.couple** 是 Mathlib 中的一个定义，位于命名空间 `Derivation`。
形式化陈述：couple : LieSubalgebra R (Derivation R A' A' × Derivation R A A) where car
rier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `σ : A → A'` be a an homomorphism. A derivation `d : A → A` and a derivation
`d' : A' → A'` are called compatible if `d' ∘ σ = σ ∘ d`. Couples of derivations
with this property form a Lie subalgebra of all couples of derivations.
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
/-
**Derivation.Compatible.mem** 是 Mathlib 中的一个引理，位于命名空间 `Derivation.Compatible`。
形式化陈述：mem (x : (Derivation R A' A') × (Derivation R A A)) : x in couple R A A' ↔
 x.1 ∘ Algebra.ofId A A' = Algebra.ofId A A' ∘ x.2
参数：x : (Derivation R A' A') × (Derivation R A A)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Derivation.ext`：ext (H : forall a, D1 a = D2 a) : D1 = D2
-/
lemma mem (x : (Derivation R A' A') × (Derivation R A A)) :
    x ∈ couple R A A' ↔ x.1 ∘ Algebra.ofId A A' = Algebra.ofId A A' ∘ x.2 := by
  constructor
  · intro hx; ext a; exact congrArg (· a) hx
  · intro hx; ext a; exact congrArg (· a) hx

/-- Generate an element of `couple` from `x y` satisfying the compatibility equation. -/
/-
**Derivation.Compatible.mk** 是 Mathlib 中的一个定义，位于命名空间 `Derivation.Compatible`。
形式化陈述：mk (x : Derivation R A' A') (y : Derivation R A A) (h : x ∘ (Algebra.ofId 
A A') = (Algebra.ofId A A') ∘ y) : couple R A A'
参数：x : Derivation R A' A'；y : Derivation R A A；h : x ∘ (Algebra.ofId A A') = (Al
gebra.ofId A A') ∘ y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Generate an element of `couple` from `x y` satisfying the compatibility equation
.
-/
def mk (x : Derivation R A' A') (y : Derivation R A A)
  (h : x ∘ (Algebra.ofId A A') = (Algebra.ofId A A') ∘ y) : couple R A A' :=
⟨(x, y), (Compatible.mem _).mpr h⟩
/-
**Derivation.Compatible.mk_left** 是 Mathlib 中的一个引理，位于命名空间 `Derivation.Compatible
`。
形式化陈述：mk_left (x : Derivation R A' A') (y : Derivation R A A) (h : x ∘ (Algebra.
ofId A A') = (Algebra.ofId A A') ∘ y) : (mk x y h).1.1 = x
参数：x : Derivation R A' A'；y : Derivation R A A；h : x ∘ (Algebra.ofId A A') = (Al
gebra.ofId A A') ∘ y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_left (x : Derivation R A' A') (y : Derivation R A A)
    (h : x ∘ (Algebra.ofId A A') = (Algebra.ofId A A') ∘ y) : (mk x y h).1.1 = x := rfl
/-
**Derivation.Compatible.mk_right** 是 Mathlib 中的一个引理，位于命名空间 `Derivation.Compatibl
e`。
形式化陈述：mk_right (x : Derivation R A' A') (y : Derivation R A A) (h : x ∘ (Algebra
.ofId A A') = (Algebra.ofId A A') ∘ y) : (mk x y h).1.2 = y
参数：x : Derivation R A' A'；y : Derivation R A A；h : x ∘ (Algebra.ofId A A') = (Al
gebra.ofId A A') ∘ y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_right (x : Derivation R A' A') (y : Derivation R A A)
    (h : x ∘ (Algebra.ofId A A') = (Algebra.ofId A A') ∘ y) : (mk x y h).1.2 = y := rfl
/-
**Derivation.Compatible.apply** 是 Mathlib 中的一个引理，位于命名空间 `Derivation.Compatible`。
形式化陈述：apply (x : couple R A A') (a : A) : x.1.1 (Algebra.ofId A A' a) = (Algebra
.ofId A A') (x.1.2 a)
参数：x : couple R A A'；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma apply (x : couple R A A') (a : A) :
    x.1.1 (Algebra.ofId A A' a) = (Algebra.ofId A A') (x.1.2 a) := by
  exact congrArg (· a) x.2

end Compatible

end CompatibleDerivations

end LieStructures

end Derivation

