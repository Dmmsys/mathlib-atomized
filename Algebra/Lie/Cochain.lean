/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Lie.Abelian

/-!
# Lie algebra cohomology in low degree

This file defines low degree cochains of Lie algebras with coefficients given by a module. They are
useful in the construction of central extensions, so we treat these easier cases separately from the
general theory of Lie algebra cohomology.

## Main definitions
* `LieAlgebra.oneCochain`: an abbreviation for a linear map.
* `LieAlgebra.twoCochain`: a submodule of bilinear maps, giving 2-cochains.
* `LieAlgebra.d₁₂`: The coboundary map taking 1-cochains to 2-cochains.
* `LieAlgebra.d₂₃`: A coboundary map taking 2-cochains to a space containing 3-cochains.
* `LieAlgebra.twoCocycle`: The submodule of 2-cocycles.

## TODO
* coboundaries, cohomology
* comparison to the Chevalley-Eilenberg complex.
* construction and classification of central extensions

## References
* [H. Cartan, S. Eilenberg, *Homological Algebra*](cartan-eilenberg-1956)

-/

@[expose] public section

namespace LieModule.Cohomology

variable (R : Type*) [CommRing R]
variable (L : Type*) [LieRing L] [LieAlgebra R L]
variable (M : Type*) [AddCommGroup M] [Module R M]

/-- Lie algebra 1-cochains over `L` with coefficients in the module `M`. -/
/-
**LieModule.Cohomology.oneCochain** 是 Mathlib 中的一个缩写定义，位于命名空间 `LieModule.Cohomol
ogy`。
形式化陈述：oneCochain
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lie algebra 1-cochains over `L` with coefficients in the module `M`.
-/
abbrev oneCochain := L →ₗ[R] M

/-- Lie algebra 2-cochains over `L` with coefficients in the module `M`. -/
/-
**LieModule.Cohomology.twoCochain** 是 Mathlib 中的一个定义，位于命名空间 `LieModule.Cohomolog
y`。
形式化陈述：twoCochain : Submodule R (L ->ₗ[R] L ->ₗ[R] M) where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lie algebra 2-cochains over `L` with coefficients in the module `M`.
-/
def twoCochain : Submodule R (L →ₗ[R] L →ₗ[R] M) where
  carrier := {c | ∀ x, c x x = 0}
  add_mem' {a b} ha hb x := by simp [ha x, hb x]
  zero_mem' := by simp
  smul_mem' t {c} hc x := by simp [hc x]

section

variable {R L M}

/-
**LieModule.Cohomology.** 是 Mathlib 中的一个实例，位于命名空间 `LieModule.Cohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (twoCochain R L M) L (L →ₗ[R] M) where
  coe := fun a x ↦ a.1 x
  coe_injective _ _ h := by
    ext
    exact congrFun (congrArg DFunLike.coe (congrFun h _)) _
/-
**LieModule.Cohomology.** 是 Mathlib 中的一个实例，位于命名空间 `LieModule.Cohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LinearMapClass (twoCochain R L M) R L (L →ₗ[R] M) where
  map_add a := a.1.map_add
  map_smulₛₗ a := a.1.map_smul

@[simp]
/-
**LieModule.Cohomology.mem_twoCochain_iff** 是 Mathlib 中的一个引理，位于命名空间 `LieModule.C
ohomology`。
形式化陈述：mem_twoCochain_iff {c : L ->ₗ[R] L ->ₗ[R] M} : c in twoCochain R L M ↔ for
all x, c x x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
lemma mem_twoCochain_iff {c : L →ₗ[R] L →ₗ[R] M} : c ∈ twoCochain R L M ↔ ∀ x, c x x = 0 := Iff.rfl

@[simp]
/-
**LieModule.Cohomology.twoCochain_alt** 是 Mathlib 中的一个引理，位于命名空间 `LieModule.Cohom
ology`。
形式化陈述：twoCochain_alt (a : twoCochain R L M) (x : L) : a x x = 0
参数：a : twoCochain R L M；x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma twoCochain_alt (a : twoCochain R L M) (x : L) :
    a x x = 0 :=
  a.2 x
/-
**LieModule.Cohomology.twoCochain_skew** 是 Mathlib 中的一个引理，位于命名空间 `LieModule.Coho
mology`。
形式化陈述：twoCochain_skew (a : twoCochain R L M) (x y : L) : - a x y = a y x
参数：a : twoCochain R L M；x y : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_eq_iff_add_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
-a = b ↔ a + b = 0
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `LieModule.Cohomology.instLinearMapClassSubtypeLinearMapIdMemSubmoduleTwo
Cochain`：∀ {R : Type u_1} [inst : CommRing R] {L : Type u_2} [inst_1 : LieRing L
] [inst_2 : LieAlgebra R L] {M : Type u_3}   [inst_3 : AddCommGroup M…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `LieModule.Cohomology.twoCochain_alt`：twoCochain_alt (a : twoCochain R L 
M) (x : L) : a x x = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma twoCochain_skew (a : twoCochain R L M) (x y : L) : - a x y = a y x := by
  rw [neg_eq_iff_add_eq_zero, add_comm]
  simpa [map_add, twoCochain_alt a x, twoCochain_alt a y] using twoCochain_alt a (x + y)

@[simp]
/-
**LieModule.Cohomology.twoCochain_val_apply** 是 Mathlib 中的一个引理，位于命名空间 `LieModule
.Cohomology`。
形式化陈述：twoCochain_val_apply (a : twoCochain R L M) (x : L) : a.val x = a x
参数：a : twoCochain R L M；x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
lemma twoCochain_val_apply (a : twoCochain R L M) (x : L) :
    a.val x = a x :=
  rfl

@[simp]
/-
**LieModule.Cohomology.add_apply_apply** 是 Mathlib 中的一个引理，位于命名空间 `LieModule.Coho
mology`。
形式化陈述：add_apply_apply (a b : twoCochain R L M) (x y : L) : (a + b) x y = a x y +
 b x y
参数：a b : twoCochain R L M；x y : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
lemma add_apply_apply (a b : twoCochain R L M) (x y : L) :
    (a + b) x y = a x y + b x y := by
  rfl


@[simp]
/-
**LieModule.Cohomology.smul_apply_apply** 是 Mathlib 中的一个引理，位于命名空间 `LieModule.Coh
omology`。
形式化陈述：smul_apply_apply (r : R) (a : twoCochain R L M) (x y : L) : (r • a) x y = 
r • (a x y)
参数：r : R；a : twoCochain R L M；x y : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
lemma smul_apply_apply (r : R) (a : twoCochain R L M) (x y : L) :
    (r • a) x y = r • (a x y) := by
  rfl

end

variable [LieRingModule L M] [LieModule R L M]

/-- The coboundary operator taking degree 1 cochains to degree 2 cochains. -/
@[simps]
/-
**LieModule.Cohomology.d** 是 Mathlib 中的一个定义，位于命名空间 `LieModule.Cohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coboundary operator taking degree 1 cochains to degree 2 cochains.
-/
def d₁₂ : oneCochain R L M →ₗ[R] twoCochain R L M where
  toFun f :=
    { val :=
      { toFun x :=
          { toFun y := ⁅x, f y⁆ - ⁅y, f x⁆ - f ⁅x, y⁆
            map_add' _ _ := by simp; abel
            map_smul' _ _ := by simp [smul_sub] }
        map_add' _ _ := by ext; simp; abel
        map_smul' _ _ := by ext; simp [smul_sub] }
      property x := by simp }
  map_add' _ _ := by ext; simp; abel
  map_smul' _ _ := by ext; simp [smul_sub]

@[simp]
/-
**LieModule.Cohomology.d** 是 Mathlib 中的一个引理，位于命名空间 `LieModule.Cohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma d₁₂_apply_apply (f : oneCochain R L M) (x y : L) :
    d₁₂ R L M f x y = ⁅x, f y⁆ - ⁅y, f x⁆ - f ⁅x, y⁆ := rfl
/-
**LieModule.Cohomology.d** 是 Mathlib 中的一个引理，位于命名空间 `LieModule.Cohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma d₁₂_apply_apply_ofTrivial [LieModule.IsTrivial L M] (f : oneCochain R L M) (x y : L) :
    d₁₂ R L M f x y = - f ⁅x, y⁆ := by
  simp [trivial_lie_zero]

/-- The coboundary operator taking degree 2 cochains to a space containing degree 3 cochains. -/
/-
**LieModule.Cohomology.d** 是 Mathlib 中的一个定义，位于命名空间 `LieModule.Cohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coboundary operator taking degree 2 cochains to a space containing degree 3 
cochains.
-/
def d₂₃ : twoCochain R L M →ₗ[R] L →ₗ[R] L →ₗ[R] L →ₗ[R] M where
  toFun a := {
    toFun x := {
      toFun y := {
        toFun z := ⁅x, a y z⁆ - ⁅y, a x z⁆ + ⁅z, a x y⁆ - a ⁅x, y⁆ z + a ⁅x, z⁆ y - a ⁅y, z⁆ x
        map_add' _ _ := by simp; abel
        map_smul' _ _ := by simp; abel_nf; simp }
      map_add' _ _ := by ext; simp; abel
      map_smul' _ _ := by ext; simp; abel_nf; simp }
    map_add' _ _ := by ext; simp; abel
    map_smul' _ _ := by ext; simp; abel_nf; simp }
  map_add' _ _ := by ext; simp; abel
  map_smul' _ _ := by ext; simp; abel_nf; simp

@[simp]
/-
**LieModule.Cohomology.d** 是 Mathlib 中的一个引理，位于命名空间 `LieModule.Cohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma d₂₃_apply (a : twoCochain R L M) (x y z : L) :
    d₂₃ R L M a x y z =
      ⁅x, a y z⁆ - ⁅y, a x z⁆ + ⁅z, a x y⁆ - a ⁅x, y⁆ z + a ⁅x, z⁆ y - a ⁅y, z⁆ x :=
  rfl
/-
**LieModule.Cohomology.d** 是 Mathlib 中的一个引理，位于命名空间 `LieModule.Cohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma d₂₃_comp_d₁₂ : (d₂₃ R L M) ∘ₗ (d₁₂ R L M) = 0 := by
  ext a x y z
  have (a : oneCochain R L M) (x : L) : d₁₂ R L M a x = (d₁₂ R L M a).val x := rfl
  simp only [LinearMap.comp_apply, d₂₃_apply, LinearMap.zero_apply, this,
    d₁₂_apply_coe_apply_apply R L M, lie_sub, lie_lie]
  rw [leibniz_lie y x, leibniz_lie z x, leibniz_lie z y]
  have : a ⁅y, ⁅z, x⁆⁆ = a ⁅x, ⁅z, y⁆⁆ + a ⁅z, ⁅y, x⁆⁆ := by
    rw [congr_arg a (leibniz_lie y z x), ← lie_skew, ← lie_skew z y, lie_neg, map_add]
  simp only [lie_lie, sub_add_cancel, map_sub, ← lie_skew x y, ← lie_skew x z, ← lie_skew y z,
    lie_neg, map_neg, this]
  abel

/-- A Lie 2-cocycle is a 2-cochain that is annihilated by the coboundary map. -/
/-
**LieModule.Cohomology.twoCocycle** 是 Mathlib 中的一个定义，位于命名空间 `LieModule.Cohomolog
y`。
形式化陈述：twoCocycle : Submodule R (twoCochain R L M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Lie 2-cocycle is a 2-cochain that is annihilated by the coboundary map.
-/
def twoCocycle : Submodule R (twoCochain R L M) := LinearMap.ker (d₂₃ R L M)
/-
**LieModule.Cohomology.mem_twoCocycle_iff** 是 Mathlib 中的一个引理，位于命名空间 `LieModule.C
ohomology`。
形式化陈述：mem_twoCocycle_iff (a : twoCochain R L M) : a in twoCocycle R L M ↔ d₂₃ R 
L M a = 0
参数：a : twoCochain R L M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_twoCocycle_iff (a : twoCochain R L M) : a ∈ twoCocycle R L M ↔ d₂₃ R L M a = 0 := by
  simp [twoCocycle]
/-
**LieModule.Cohomology.mem_twoCocycle_iff_of_trivial** 是 Mathlib 中的一个引理，位于命名空间 `
LieModule.Cohomology`。
形式化陈述：mem_twoCocycle_iff_of_trivial [LieModule.IsTrivial L M] (a : twoCochain R 
L M) : a in twoCocycle R L M ↔ forall (x y z : L), a x ⁅y, z⁆ = a ⁅x, y⁆ z + a y
 ⁅x, z⁆
参数：a : twoCochain R L M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieModule.Cohomology.mem_twoCocycle_iff`：mem_twoCocycle_iff (a : twoCoch
ain R L M) : a in twoCocycle R L M ↔ d₂₃ R L M a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LieModule.Cohomology.twoCochain_skew`：twoCochain_skew (a : twoCochain R 
L M) (x y : L) : - a x y = a y x
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `trivial_lie_zero`：trivial_lie_zero (L : Type v) (M : Type w) [Bracket L 
M] [Zero M] [LieModule.IsTrivial L M] (x : L) (m : M) : ⁅x, m⁆ = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `_private.Mathlib.Algebra.Lie.Cochain.0.LieModule.Cohomology.mem_twoCocyc
le_iff_of_trivial._abel_1_2`：∀ (R : Type u_3) [inst : CommRing R] (L : Type u_2)
 [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] (M : Type u_1)   [inst_3 : AddCo
mmGroup M…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `_private.Mathlib.Algebra.Lie.Cochain.0.LieModule.Cohomology.mem_twoCocyc
le_iff_of_trivial._abel_1_3`：∀ (R : Type u_3) [inst : CommRing R] (L : Type u_2)
 [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] (M : Type u_1)   [inst_3 : AddCo
mmGroup M…
-/
lemma mem_twoCocycle_iff_of_trivial [LieModule.IsTrivial L M] (a : twoCochain R L M) :
    a ∈ twoCocycle R L M ↔
      ∀ (x y z : L), a x ⁅y, z⁆ = a ⁅x, y⁆ z + a y ⁅x, z⁆ := by
  constructor
  · intro h x y z
    rw [mem_twoCocycle_iff] at h
    have : (d₂₃ R L M) a x y z = 0 := (congrArg (fun b ↦ b x y z = 0) h).mpr rfl
    simp only [d₂₃_apply, trivial_lie_zero, sub_self, add_zero, zero_sub] at this
    rw [sub_eq_zero] at this
    rw [← twoCochain_skew a _ x, ← twoCochain_skew a _ y, ← this]
    abel
  · intro h
    ext x y z
    simp only [d₂₃_apply, trivial_lie_zero, sub_self, add_zero, zero_sub, LinearMap.zero_apply]
    rw [← twoCochain_skew a x, ← twoCochain_skew a y, h x y z]
    abel

end LieModule.Cohomology

