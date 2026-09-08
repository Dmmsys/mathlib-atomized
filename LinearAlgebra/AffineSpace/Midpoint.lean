/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Module.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv

/-!
# Midpoint of a segment

## Main definitions

* `midpoint R x y`: midpoint of the segment `[x, y]`. We define it for `x` and `y`
  in a module over a ring `R` with invertible `2`.
* `AddMonoidHom.ofMapMidpoint`: construct an `AddMonoidHom` given a map `f` such that
  `f` sends zero to zero and midpoints to midpoints.

## Main theorems

* `midpoint_eq_iff`: `z` is the midpoint of `[x, y]` if and only if `x + y = z + z`,
* `midpoint_unique`: `midpoint R x y` does not depend on `R`;
* `midpoint x y` is linear both in `x` and `y`;
* `pointReflection_midpoint_left`, `pointReflection_midpoint_right`:
  `Equiv.pointReflection (midpoint R x y)` swaps `x` and `y`.

We do not mark most lemmas as `@[simp]` because it is hard to tell which side is simpler.

## Tags

midpoint, AddMonoidHom
-/

@[expose] public section

open AffineMap AffineEquiv

section

variable (R : Type*) {V V' P P' : Type*} [Ring R] [Invertible (2 : R)] [AddCommGroup V]
  [Module R V] [AddTorsor V P] [AddCommGroup V'] [Module R V'] [AddTorsor V' P']

set_option backward.isDefEq.respectTransparency false in
/-- `midpoint x y` is the midpoint of the segment `[x, y]`. -/
/-
**midpoint** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：midpoint (x y : P) : P
参数：x y : P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`midpoint x y` is the midpoint of the segment `[x, y]`.
-/
def midpoint (x y : P) : P :=
  lineMap x y (⅟2 : R)

variable {R} {x y z : P}

@[simp]
/-
**AffineMap.map_midpoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineMap.map_midpoint (f : P ->ᵃ[R] P') (a b : P) : f (midpoint R a b) = 
midpoint R (f a) (f b)
参数：f : P ->ᵃ[R] P'；a b : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `AffineMap.apply_lineMap`：apply_lineMap (f : P1 ->ᵃ[k] P2) (p₀ p₁ : P1) (
c : k) : f (lineMap p₀ p₁ c) = lineMap (f p₀) (f p₁) c
-/
theorem AffineMap.map_midpoint (f : P →ᵃ[R] P') (a b : P) :
    f (midpoint R a b) = midpoint R (f a) (f b) :=
  f.apply_lineMap a b _

@[simp]
/-
**AffineEquiv.map_midpoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineEquiv.map_midpoint (f : P ≃ᵃ[R] P') (a b : P) : f (midpoint R a b) =
 midpoint R (f a) (f b)
参数：f : P ≃ᵃ[R] P'；a b : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `AffineEquiv.apply_lineMap`：apply_lineMap (e : P₁ ≃ᵃ[k] P₂) (a b : P₁) (c
 : k) : e (AffineMap.lineMap a b c) = AffineMap.lineMap (e a) (e b) c
-/
theorem AffineEquiv.map_midpoint (f : P ≃ᵃ[R] P') (a b : P) :
    f (midpoint R a b) = midpoint R (f a) (f b) :=
  f.apply_lineMap a b _
/-
**AffineEquiv.pointReflection_midpoint_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineEquiv.pointReflection_midpoint_left (x y : P) : pointReflection R (m
idpoint R x y) x = y
参数：x y : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `midpoint.eq_1`：∀ (R : Type u_1) {V : Type u_2} {P : Type u_4} [inst : Ri
ng R] [inst_1 : Invertible 2] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Modul
e R…
· 使用定理 `AffineEquiv.pointReflection_apply`：pointReflection_apply (x y : P₁) : po
intReflection k x y = (x -ᵥ y) +ᵥ x
· 使用定理 `AffineMap.lineMap_apply`：lineMap_apply (p₀ p₁ : P1) (c : k) : lineMap p₀
 p₁ c = c • (p₁ -ᵥ p₀) +ᵥ p₀
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用定理 `vadd_vadd`：∀ {M : Type u_1} {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (a₁ a₂ : M) (b : α),   a₁ +ᵥ a₂ +ᵥ b = (a₁ + a₂) +ᵥ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `mul_invOf_self`：mul_invOf_self [Mul α] [One α] (a : α) [Invertible a] : 
a * ⅟a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
-/
theorem AffineEquiv.pointReflection_midpoint_left (x y : P) :
    pointReflection R (midpoint R x y) x = y := by
  rw [midpoint, pointReflection_apply, lineMap_apply, vadd_vsub, vadd_vadd, ← add_smul, ← two_mul,
    mul_invOf_self, one_smul, vsub_vadd]

@[simp]
/-
**Equiv.pointReflection_midpoint_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.pointReflection_midpoint_left (x y : P) : (Equiv.pointReflection (mi
dpoint R x y)) x = y
参数：x y : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `midpoint.eq_1`：∀ (R : Type u_1) {V : Type u_2} {P : Type u_4} [inst : Ri
ng R] [inst_1 : Invertible 2] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Modul
e R…
· 使用定理 `Equiv.pointReflection_apply`：pointReflection_apply (x y : P) : pointRefl
ection x y = (x -ᵥ y) +ᵥ x
· 使用定理 `AffineMap.lineMap_apply`：lineMap_apply (p₀ p₁ : P1) (c : k) : lineMap p₀
 p₁ c = c • (p₁ -ᵥ p₀) +ᵥ p₀
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用定理 `vadd_vadd`：∀ {M : Type u_1} {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (a₁ a₂ : M) (b : α),   a₁ +ᵥ a₂ +ᵥ b = (a₁ + a₂) +ᵥ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `mul_invOf_self`：mul_invOf_self [Mul α] [One α] (a : α) [Invertible a] : 
a * ⅟a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
-/
theorem Equiv.pointReflection_midpoint_left (x y : P) :
    (Equiv.pointReflection (midpoint R x y)) x = y := by
  rw [midpoint, pointReflection_apply, lineMap_apply, vadd_vsub, vadd_vadd, ← add_smul, ← two_mul,
    mul_invOf_self, one_smul, vsub_vadd]
/-
**midpoint_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：midpoint_comm (x y : P) : midpoint R x y = midpoint R y x
参数：x y : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `midpoint.eq_1`：∀ (R : Type u_1) {V : Type u_2} {P : Type u_4} [inst : Ri
ng R] [inst_1 : Invertible 2] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Modul
e R…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineMap.lineMap_apply_one_sub`：lineMap_apply_one_sub (p₀ p₁ : P1) (c :
 k) : lineMap p₀ p₁ (1 - c) = lineMap p₁ p₀ c
· 使用定理 `one_sub_invOf_two`：one_sub_invOf_two [Ring R] [Invertible (2 : R)] : 1 -
 (⅟2 : R) = ⅟2
-/
theorem midpoint_comm (x y : P) : midpoint R x y = midpoint R y x := by
  rw [midpoint, ← lineMap_apply_one_sub, one_sub_invOf_two, midpoint]
/-
**AffineEquiv.pointReflection_midpoint_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineEquiv.pointReflection_midpoint_right (x y : P) : pointReflection R (
midpoint R x y) y = x
参数：x y : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `midpoint_comm`：midpoint_comm (x y : P) : midpoint R x y = midpoint R y x
· 使用定理 `AffineEquiv.pointReflection_midpoint_left`：AffineEquiv.pointReflection_m
idpoint_left (x y : P) : pointReflection R (midpoint R x y) x = y
-/
theorem AffineEquiv.pointReflection_midpoint_right (x y : P) :
    pointReflection R (midpoint R x y) y = x := by
  rw [midpoint_comm, AffineEquiv.pointReflection_midpoint_left]

@[simp]
/-
**Equiv.pointReflection_midpoint_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.pointReflection_midpoint_right (x y : P) : (Equiv.pointReflection (m
idpoint R x y)) y = x
参数：x y : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `midpoint_comm`：midpoint_comm (x y : P) : midpoint R x y = midpoint R y x
· 使用定理 `Equiv.pointReflection_midpoint_left`：Equiv.pointReflection_midpoint_left
 (x y : P) : (Equiv.pointReflection (midpoint R x y)) x = y
-/
theorem Equiv.pointReflection_midpoint_right (x y : P) :
    (Equiv.pointReflection (midpoint R x y)) y = x := by
  rw [midpoint_comm, Equiv.pointReflection_midpoint_left]
/-
**midpoint_vsub_midpoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：midpoint_vsub_midpoint (p₁ p₂ p₃ p₄ : P) : midpoint R p₁ p₂ -ᵥ midpoint R 
p₃ p₄ = midpoint R (p₁ -ᵥ p₃) (p₂ -ᵥ p₄)
参数：p₁ p₂ p₃ p₄ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `AffineMap.lineMap_vsub_lineMap`：lineMap_vsub_lineMap (p₁ p₂ p₃ p₄ : P1) 
(c : k) : lineMap p₁ p₂ c -ᵥ lineMap p₃ p₄ c = lineMap (p₁ -ᵥ p₃) (p₂ -ᵥ p₄) c
-/
theorem midpoint_vsub_midpoint (p₁ p₂ p₃ p₄ : P) :
    midpoint R p₁ p₂ -ᵥ midpoint R p₃ p₄ = midpoint R (p₁ -ᵥ p₃) (p₂ -ᵥ p₄) :=
  lineMap_vsub_lineMap _ _ _ _ _
/-
**midpoint_vadd_midpoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：midpoint_vadd_midpoint (v v' : V) (p p' : P) : midpoint R v v' +ᵥ midpoint
 R p p' = midpoint R (v +ᵥ p) (v' +ᵥ p')
参数：v v' : V；p p' : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `AffineMap.lineMap_vadd_lineMap`：lineMap_vadd_lineMap (v₁ v₂ : V1) (p₁ p₂
 : P1) (c : k) : lineMap v₁ v₂ c +ᵥ lineMap p₁ p₂ c = lineMap (v₁ +ᵥ p₁) (v₂ +ᵥ 
p₂) c
-/
theorem midpoint_vadd_midpoint (v v' : V) (p p' : P) :
    midpoint R v v' +ᵥ midpoint R p p' = midpoint R (v +ᵥ p) (v' +ᵥ p') :=
  lineMap_vadd_lineMap _ _ _ _ _
/-
**midpoint_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：midpoint_eq_iff {x y z : P} : midpoint R x y = z ↔ pointReflection R z x =
 y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `AffineEquiv.injective_pointReflection_left_of_module`：injective_pointRef
lection_left_of_module [Invertible (2 : k)] : forall y, Injective fun x : P₁ => 
pointReflection k x y
· 使用定理 `AffineEquiv.pointReflection_midpoint_left`：AffineEquiv.pointReflection_m
idpoint_left (x y : P) : pointReflection R (midpoint R x y) x = y
-/
theorem midpoint_eq_iff {x y z : P} : midpoint R x y = z ↔ pointReflection R z x = y :=
  eq_comm.trans
    ((injective_pointReflection_left_of_module R x).eq_iff'
        (AffineEquiv.pointReflection_midpoint_left x y)).symm

@[simp]
/-
**midpoint_pointReflection_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：midpoint_pointReflection_left (x y : P) : midpoint R (Equiv.pointReflectio
n x y) y = x
参数：x y : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `midpoint_eq_iff`：midpoint_eq_iff {x y z : P} : midpoint R x y = z ↔ poin
tReflection R z x = y
· 使用定理 `Equiv.pointReflection_involutive`：pointReflection_involutive (x : P) : I
nvolutive (pointReflection x : P -> P)
-/
theorem midpoint_pointReflection_left (x y : P) :
    midpoint R (Equiv.pointReflection x y) y = x :=
  midpoint_eq_iff.2 <| Equiv.pointReflection_involutive _ _

@[simp]
/-
**midpoint_pointReflection_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：midpoint_pointReflection_right (x y : P) : midpoint R y (Equiv.pointReflec
tion x y) = x
参数：x y : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `midpoint_eq_iff`：midpoint_eq_iff {x y z : P} : midpoint R x y = z ↔ poin
tReflection R z x = y
-/
theorem midpoint_pointReflection_right (x y : P) :
    midpoint R y (Equiv.pointReflection x y) = x :=
  midpoint_eq_iff.2 rfl

nonrec lemma AffineEquiv.midpoint_pointReflection_left (x y : P) :
    midpoint R (pointReflection R x y) y = x :=
  midpoint_pointReflection_left x y

nonrec lemma AffineEquiv.midpoint_pointReflection_right (x y : P) :
    midpoint R y (pointReflection R x y) = x :=
  midpoint_pointReflection_right x y

@[simp]
/-
**midpoint_vsub_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：midpoint_vsub_left (p₁ p₂ : P) : midpoint R p₁ p₂ -ᵥ p₁ = (⅟2 : R) • (p₂ -
ᵥ p₁)
参数：p₁ p₂ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `AffineMap.lineMap_vsub_left`：lineMap_vsub_left (p₀ p₁ : P1) (c : k) : li
neMap p₀ p₁ c -ᵥ p₀ = c • (p₁ -ᵥ p₀)
-/
theorem midpoint_vsub_left (p₁ p₂ : P) : midpoint R p₁ p₂ -ᵥ p₁ = (⅟2 : R) • (p₂ -ᵥ p₁) :=
  lineMap_vsub_left _ _ _

@[simp]
/-
**midpoint_vsub_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：midpoint_vsub_right (p₁ p₂ : P) : midpoint R p₁ p₂ -ᵥ p₂ = (⅟2 : R) • (p₁ 
-ᵥ p₂)
参数：p₁ p₂ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `midpoint_comm`：midpoint_comm (x y : P) : midpoint R x y = midpoint R y x
· 使用定理 `midpoint_vsub_left`：midpoint_vsub_left (p₁ p₂ : P) : midpoint R p₁ p₂ -ᵥ
 p₁ = (⅟2 : R) • (p₂ -ᵥ p₁)
-/
theorem midpoint_vsub_right (p₁ p₂ : P) : midpoint R p₁ p₂ -ᵥ p₂ = (⅟2 : R) • (p₁ -ᵥ p₂) := by
  rw [midpoint_comm, midpoint_vsub_left]

@[simp]
/-
**left_vsub_midpoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：left_vsub_midpoint (p₁ p₂ : P) : p₁ -ᵥ midpoint R p₁ p₂ = (⅟2 : R) • (p₁ -
ᵥ p₂)
参数：p₁ p₂ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `AffineMap.left_vsub_lineMap`：left_vsub_lineMap (p₀ p₁ : P1) (c : k) : p₀
 -ᵥ lineMap p₀ p₁ c = c • (p₀ -ᵥ p₁)
-/
theorem left_vsub_midpoint (p₁ p₂ : P) : p₁ -ᵥ midpoint R p₁ p₂ = (⅟2 : R) • (p₁ -ᵥ p₂) :=
  left_vsub_lineMap _ _ _

@[simp]
/-
**right_vsub_midpoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：right_vsub_midpoint (p₁ p₂ : P) : p₂ -ᵥ midpoint R p₁ p₂ = (⅟2 : R) • (p₂ 
-ᵥ p₁)
参数：p₁ p₂ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `midpoint_comm`：midpoint_comm (x y : P) : midpoint R x y = midpoint R y x
· 使用定理 `left_vsub_midpoint`：left_vsub_midpoint (p₁ p₂ : P) : p₁ -ᵥ midpoint R p₁
 p₂ = (⅟2 : R) • (p₁ -ᵥ p₂)
-/
theorem right_vsub_midpoint (p₁ p₂ : P) : p₂ -ᵥ midpoint R p₁ p₂ = (⅟2 : R) • (p₂ -ᵥ p₁) := by
  rw [midpoint_comm, left_vsub_midpoint]
/-
**midpoint_vsub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：midpoint_vsub (p₁ p₂ p : P) : midpoint R p₁ p₂ -ᵥ p = (⅟2 : R) • (p₁ -ᵥ p)
 + (⅟2 : R) • (p₂ -ᵥ p)
参数：p₁ p₂ p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_sub_vsub_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : AddG
roup G] [T : AddTorsor G P] (p₁ p₂ p₃ : P), p₁ -ᵥ p₃ - (p₂ -ᵥ p₃) = p₁ -ᵥ p₂
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `invOf_two_smul_add_invOf_two_smul`：invOf_two_smul_add_invOf_two_smul (R)
 [Semiring R] [AddCommMonoid M] [Module R M] [Invertible (2 : R)] (x : M) : (⅟2 
: R) • x + (⅟2 : R) • x…
· 使用定理 `vadd_vsub_assoc`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T 
: AddTorsor G P] (g : G) (p₁ p₂ : P),   (g +ᵥ p₁) -ᵥ p₂ = g + (p₁ -ᵥ p₂)
· 使用定理 `midpoint_comm`：midpoint_comm (x y : P) : midpoint R x y = midpoint R y x
· 使用定理 `midpoint.eq_1`：∀ (R : Type u_1) {V : Type u_2} {P : Type u_4} [inst : Ri
ng R] [inst_1 : Invertible 2] [inst_2 : AddCommGroup V]   [inst_3 : _root_.Modul
e R…
· 使用定理 `AffineMap.lineMap_apply`：lineMap_apply (p₀ p₁ : P1) (c : k) : lineMap p₀
 p₁ c = c • (p₁ -ᵥ p₀) +ᵥ p₀
-/
theorem midpoint_vsub (p₁ p₂ p : P) :
    midpoint R p₁ p₂ -ᵥ p = (⅟2 : R) • (p₁ -ᵥ p) + (⅟2 : R) • (p₂ -ᵥ p) := by
  rw [← vsub_sub_vsub_cancel_right p₁ p p₂, smul_sub, sub_eq_add_neg, ← smul_neg,
    neg_vsub_eq_vsub_rev, add_assoc, invOf_two_smul_add_invOf_two_smul, ← vadd_vsub_assoc,
    midpoint_comm, midpoint, lineMap_apply]
/-
**vsub_midpoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：vsub_midpoint (p₁ p₂ p : P) : p -ᵥ midpoint R p₁ p₂ = (⅟2 : R) • (p -ᵥ p₁)
 + (⅟2 : R) • (p -ᵥ p₂)
参数：p₁ p₂ p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `midpoint_vsub`：midpoint_vsub (p₁ p₂ p : P) : midpoint R p₁ p₂ -ᵥ p = (⅟2
 : R) • (p₁ -ᵥ p) + (⅟2 : R) • (p₂ -ᵥ p)
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
-/
theorem vsub_midpoint (p₁ p₂ p : P) :
    p -ᵥ midpoint R p₁ p₂ = (⅟2 : R) • (p -ᵥ p₁) + (⅟2 : R) • (p -ᵥ p₂) := by
  rw [← neg_vsub_eq_vsub_rev, midpoint_vsub, neg_add, ← smul_neg, ← smul_neg, neg_vsub_eq_vsub_rev,
    neg_vsub_eq_vsub_rev]

@[simp]
/-
**midpoint_sub_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：midpoint_sub_left (v₁ v₂ : V) : midpoint R v₁ v₂ - v₁ = (⅟2 : R) • (v₂ - v
₁)
参数：v₁ v₂ : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `midpoint_vsub_left`：midpoint_vsub_left (p₁ p₂ : P) : midpoint R p₁ p₂ -ᵥ
 p₁ = (⅟2 : R) • (p₂ -ᵥ p₁)
-/
theorem midpoint_sub_left (v₁ v₂ : V) : midpoint R v₁ v₂ - v₁ = (⅟2 : R) • (v₂ - v₁) :=
  midpoint_vsub_left v₁ v₂

@[simp]
/-
**midpoint_sub_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：midpoint_sub_right (v₁ v₂ : V) : midpoint R v₁ v₂ - v₂ = (⅟2 : R) • (v₁ - 
v₂)
参数：v₁ v₂ : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `midpoint_vsub_right`：midpoint_vsub_right (p₁ p₂ : P) : midpoint R p₁ p₂ 
-ᵥ p₂ = (⅟2 : R) • (p₁ -ᵥ p₂)
-/
theorem midpoint_sub_right (v₁ v₂ : V) : midpoint R v₁ v₂ - v₂ = (⅟2 : R) • (v₁ - v₂) :=
  midpoint_vsub_right v₁ v₂

@[simp]
/-
**left_sub_midpoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：left_sub_midpoint (v₁ v₂ : V) : v₁ - midpoint R v₁ v₂ = (⅟2 : R) • (v₁ - v
₂)
参数：v₁ v₂ : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `left_vsub_midpoint`：left_vsub_midpoint (p₁ p₂ : P) : p₁ -ᵥ midpoint R p₁
 p₂ = (⅟2 : R) • (p₁ -ᵥ p₂)
-/
theorem left_sub_midpoint (v₁ v₂ : V) : v₁ - midpoint R v₁ v₂ = (⅟2 : R) • (v₁ - v₂) :=
  left_vsub_midpoint v₁ v₂

@[simp]
/-
**right_sub_midpoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：right_sub_midpoint (v₁ v₂ : V) : v₂ - midpoint R v₁ v₂ = (⅟2 : R) • (v₂ - 
v₁)
参数：v₁ v₂ : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `right_vsub_midpoint`：right_vsub_midpoint (p₁ p₂ : P) : p₂ -ᵥ midpoint R 
p₁ p₂ = (⅟2 : R) • (p₂ -ᵥ p₁)
-/
theorem right_sub_midpoint (v₁ v₂ : V) : v₂ - midpoint R v₁ v₂ = (⅟2 : R) • (v₂ - v₁) :=
  right_vsub_midpoint v₁ v₂

variable (R)

@[simp]
/-
**midpoint_eq_left_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：midpoint_eq_left_iff {x y : P} : midpoint R x y = x ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `midpoint_eq_iff`：midpoint_eq_iff {x y z : P} : midpoint R x y = z ↔ poin
tReflection R z x = y
· 使用定理 `AffineEquiv.pointReflection_self`：pointReflection_self (x : P₁) : pointR
eflection k x x = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem midpoint_eq_left_iff {x y : P} : midpoint R x y = x ↔ x = y := by
  rw [midpoint_eq_iff, pointReflection_self]

@[simp]
/-
**left_eq_midpoint_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：left_eq_midpoint_iff {x y : P} : x = midpoint R x y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `midpoint_eq_left_iff`：midpoint_eq_left_iff {x y : P} : midpoint R x y = 
x ↔ x = y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem left_eq_midpoint_iff {x y : P} : x = midpoint R x y ↔ x = y := by
  rw [eq_comm, midpoint_eq_left_iff]

@[simp]
/-
**midpoint_eq_right_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：midpoint_eq_right_iff {x y : P} : midpoint R x y = y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `midpoint_comm`：midpoint_comm (x y : P) : midpoint R x y = midpoint R y x
· 使用定理 `midpoint_eq_left_iff`：midpoint_eq_left_iff {x y : P} : midpoint R x y = 
x ↔ x = y
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem midpoint_eq_right_iff {x y : P} : midpoint R x y = y ↔ x = y := by
  rw [midpoint_comm, midpoint_eq_left_iff, eq_comm]

@[simp]
/-
**right_eq_midpoint_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：right_eq_midpoint_iff {x y : P} : y = midpoint R x y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `midpoint_eq_right_iff`：midpoint_eq_right_iff {x y : P} : midpoint R x y 
= y ↔ x = y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem right_eq_midpoint_iff {x y : P} : y = midpoint R x y ↔ x = y := by
  rw [eq_comm, midpoint_eq_right_iff]
/-
**midpoint_eq_midpoint_iff_vsub_eq_vsub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：midpoint_eq_midpoint_iff_vsub_eq_vsub {x x' y y' : P} : midpoint R x y = m
idpoint R x' y' ↔ x -ᵥ x' = y' -ᵥ y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂
· 使用定理 `midpoint_vsub_midpoint`：midpoint_vsub_midpoint (p₁ p₂ p₃ p₄ : P) : midpo
int R p₁ p₂ -ᵥ midpoint R p₃ p₄ = midpoint R (p₁ -ᵥ p₃) (p₂ -ᵥ p₄)
· 使用定理 `midpoint_eq_iff`：midpoint_eq_iff {x y z : P} : midpoint R x y = z ↔ poin
tReflection R z x = y
· 使用定理 `AffineEquiv.pointReflection_apply`：pointReflection_apply (x y : P₁) : po
intReflection k x y = (x -ᵥ y) +ᵥ x
· 使用定理 `vsub_eq_sub`：∀ {G : Type u_1} [inst : AddGroup G] (g₁ g₂ : G), g₁ -ᵥ g₂ 
= g₁ - g₂
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `vadd_eq_add`：∀ {α : Type u_9} [inst : Add α] (a b : α), a +ᵥ b = a + b
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem midpoint_eq_midpoint_iff_vsub_eq_vsub {x x' y y' : P} :
    midpoint R x y = midpoint R x' y' ↔ x -ᵥ x' = y' -ᵥ y := by
  rw [← @vsub_eq_zero_iff_eq V, midpoint_vsub_midpoint, midpoint_eq_iff, pointReflection_apply,
    vsub_eq_sub, zero_sub, vadd_eq_add, add_zero, neg_eq_iff_eq_neg, neg_vsub_eq_vsub_rev]
/-
**midpoint_eq_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：midpoint_eq_iff' {x y z : P} : midpoint R x y = z ↔ Equiv.pointReflection 
z x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `midpoint_eq_iff`：midpoint_eq_iff {x y z : P} : midpoint R x y = z ↔ poin
tReflection R z x = y
-/
theorem midpoint_eq_iff' {x y z : P} : midpoint R x y = z ↔ Equiv.pointReflection z x = y :=
  midpoint_eq_iff

/-- `midpoint` does not depend on the ring `R`. -/
/-
**midpoint_unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：midpoint_unique (R' : Type*) [Ring R'] [Invertible (2 : R')] [Module R' V]
 (x y : P) : midpoint R x y = midpoint R' x y
参数：R' : Type*；2 : R'；x y : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `midpoint_eq_iff'`：midpoint_eq_iff' {x y z : P} : midpoint R x y = z ↔ Eq
uiv.pointReflection z x = y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b

--- 原说明 ---
`midpoint` does not depend on the ring `R`.
-/
theorem midpoint_unique (R' : Type*) [Ring R'] [Invertible (2 : R')] [Module R' V] (x y : P) :
    midpoint R x y = midpoint R' x y :=
  (midpoint_eq_iff' R).2 <| (midpoint_eq_iff' R').1 rfl

@[simp]
/-
**midpoint_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：midpoint_self (x : P) : midpoint R x x = x
参数：x : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `AffineMap.lineMap_same_apply`：lineMap_same_apply (p : P1) (c : k) : line
Map p p c = p
-/
theorem midpoint_self (x : P) : midpoint R x x = x :=
  lineMap_same_apply _ _

@[simp]
/-
**midpoint_add_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：midpoint_add_self (x y : V) : midpoint R x y + midpoint R x y = x + y
参数：x y : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `midpoint_comm`：midpoint_comm (x y : P) : midpoint R x y = midpoint R y x
· 使用定理 `midpoint_vadd_midpoint`：midpoint_vadd_midpoint (v v' : V) (p p' : P) : m
idpoint R v v' +ᵥ midpoint R p p' = midpoint R (v +ᵥ p) (v' +ᵥ p')
· 使用定理 `vadd_eq_add`：∀ {α : Type u_9} [inst : Add α] (a b : α), a +ᵥ b = a + b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `midpoint_self`：midpoint_self (x : P) : midpoint R x x = x
-/
theorem midpoint_add_self (x y : V) : midpoint R x y + midpoint R x y = x + y :=
  calc
    midpoint R x y +ᵥ midpoint R x y = midpoint R x y +ᵥ midpoint R y x := by rw [midpoint_comm]
    _ = x + y := by rw [midpoint_vadd_midpoint, vadd_eq_add, vadd_eq_add, add_comm, midpoint_self]
/-
**midpoint_zero_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：midpoint_zero_add (x y : V) : midpoint R 0 (x + y) = midpoint R x y
参数：x y : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `midpoint_eq_midpoint_iff_vsub_eq_vsub`：midpoint_eq_midpoint_iff_vsub_eq_
vsub {x x' y y' : P} : midpoint R x y = midpoint R x' y' ↔ x -ᵥ x' = y' -ᵥ y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `sub_add_cancel_right`：∀ {G : Type u_3} [inst : AddGroup G] (a b : G), a 
- (b + a) = -b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem midpoint_zero_add (x y : V) : midpoint R 0 (x + y) = midpoint R x y :=
  (midpoint_eq_midpoint_iff_vsub_eq_vsub R).2 <| by simp
/-
**midpoint_eq_smul_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：midpoint_eq_smul_add (x y : V) : midpoint R x y = (⅟2 : R) • (x + y)
参数：x y : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `midpoint_eq_iff`：midpoint_eq_iff {x y z : P} : midpoint R x y = z ↔ poin
tReflection R z x = y
· 使用定理 `AffineEquiv.pointReflection_apply`：pointReflection_apply (x y : P₁) : po
intReflection k x y = (x -ᵥ y) +ᵥ x
· 使用定理 `vsub_eq_sub`：∀ {G : Type u_1} [inst : AddGroup G] (g₁ g₂ : G), g₁ -ᵥ g₂ 
= g₁ - g₂
· 使用定理 `vadd_eq_add`：∀ {α : Type u_9} [inst : Add α] (a b : α), a +ᵥ b = a + b
· 使用定理 `sub_add_eq_add_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a
 b c : α), a - b + c = a + c - b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `mul_invOf_self`：mul_invOf_self [Mul α] [One α] (a : α) [Invertible a] : 
a * ⅟a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
-/
theorem midpoint_eq_smul_add (x y : V) : midpoint R x y = (⅟2 : R) • (x + y) := by
  rw [midpoint_eq_iff, pointReflection_apply, vsub_eq_sub, vadd_eq_add, sub_add_eq_add_sub, ←
    two_smul R, smul_smul, mul_invOf_self, one_smul, add_sub_cancel_left]

@[simp]
/-
**midpoint_self_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：midpoint_self_neg (x : V) : midpoint R x (-x) = 0
参数：x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `midpoint_eq_smul_add`：midpoint_eq_smul_add (x y : V) : midpoint R x y = 
(⅟2 : R) • (x + y)
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem midpoint_self_neg (x : V) : midpoint R x (-x) = 0 := by
  rw [midpoint_eq_smul_add, add_neg_cancel, smul_zero]

@[simp]
/-
**midpoint_neg_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：midpoint_neg_self (x : V) : midpoint R (-x) x = 0
参数：x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `midpoint_self_neg`：midpoint_self_neg (x : V) : midpoint R x (-x) = 0
-/
theorem midpoint_neg_self (x : V) : midpoint R (-x) x = 0 := by simpa using midpoint_self_neg R (-x)

@[simp]
/-
**midpoint_sub_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：midpoint_sub_add (x y : V) : midpoint R (x - y) (x + y) = x
参数：x y : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vadd_eq_add`：∀ {α : Type u_9} [inst : Add α] (a b : α), a +ᵥ b = a + b
· 使用定理 `midpoint_vadd_midpoint`：midpoint_vadd_midpoint (v v' : V) (p p' : P) : m
idpoint R v v' +ᵥ midpoint R p p' = midpoint R (v +ᵥ p) (v' +ᵥ p')
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `midpoint_self`：midpoint_self (x : P) : midpoint R x x = x
· 使用定理 `midpoint_neg_self`：midpoint_neg_self (x : V) : midpoint R (-x) x = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem midpoint_sub_add (x y : V) : midpoint R (x - y) (x + y) = x := by
  rw [sub_eq_add_neg, ← vadd_eq_add, ← vadd_eq_add, ← midpoint_vadd_midpoint]; simp

@[simp]
/-
**midpoint_add_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：midpoint_add_sub (x y : V) : midpoint R (x + y) (x - y) = x
参数：x y : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `midpoint_comm`：midpoint_comm (x y : P) : midpoint R x y = midpoint R y x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `midpoint_sub_add`：midpoint_sub_add (x y : V) : midpoint R (x - y) (x + y
) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem midpoint_add_sub (x y : V) : midpoint R (x + y) (x - y) = x := by
  rw [midpoint_comm]; simp
/-
**midpoint_vsub_midpoint_same_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：midpoint_vsub_midpoint_same_left (p₁ p₂ p₃ : P) : midpoint R p₁ p₂ -ᵥ midp
oint R p₁ p₃ = (⅟2 : R) • (p₂ -ᵥ p₃)
参数：p₁ p₂ p₃ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `midpoint_vsub_midpoint`：midpoint_vsub_midpoint (p₁ p₂ p₃ p₄ : P) : midpo
int R p₁ p₂ -ᵥ midpoint R p₃ p₄ = midpoint R (p₁ -ᵥ p₃) (p₂ -ᵥ p₄)
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `midpoint_eq_smul_add`：midpoint_eq_smul_add (x y : V) : midpoint R x y = 
(⅟2 : R) • (x + y)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem midpoint_vsub_midpoint_same_left (p₁ p₂ p₃ : P) :
    midpoint R p₁ p₂ -ᵥ midpoint R p₁ p₃ = (⅟2 : R) • (p₂ -ᵥ p₃) := by
  rw [midpoint_vsub_midpoint, vsub_self, midpoint_eq_smul_add, zero_add]
/-
**midpoint_vsub_midpoint_same_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：midpoint_vsub_midpoint_same_right (p₁ p₂ p₃ : P) : midpoint R p₁ p₃ -ᵥ mid
point R p₂ p₃ = (⅟2 : R) • (p₁ -ᵥ p₂)
参数：p₁ p₂ p₃ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `midpoint_vsub_midpoint`：midpoint_vsub_midpoint (p₁ p₂ p₃ p₄ : P) : midpo
int R p₁ p₂ -ᵥ midpoint R p₃ p₄ = midpoint R (p₁ -ᵥ p₃) (p₂ -ᵥ p₄)
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `midpoint_eq_smul_add`：midpoint_eq_smul_add (x y : V) : midpoint R x y = 
(⅟2 : R) • (x + y)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem midpoint_vsub_midpoint_same_right (p₁ p₂ p₃ : P) :
    midpoint R p₁ p₃ -ᵥ midpoint R p₂ p₃ = (⅟2 : R) • (p₁ -ᵥ p₂) := by
  rw [midpoint_vsub_midpoint, vsub_self, midpoint_eq_smul_add, add_zero]

end

namespace AddMonoidHom

variable (R R' : Type*) {E F : Type*} [Ring R] [Invertible (2 : R)] [AddCommGroup E] [Module R E]
  [Ring R'] [Invertible (2 : R')] [AddCommGroup F] [Module R' F]

/-- A map `f : E → F` sending zero to zero and midpoints to midpoints is an `AddMonoidHom`. -/
/-
**AddMonoidHom.ofMapMidpoint** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoidHom`。
形式化陈述：ofMapMidpoint (f : E -> F) (h0 : f 0 = 0) (hm : forall x y, f (midpoint R 
x y) = midpoint R' (f x) (f y)) : E ->+ F where toFun
参数：f : E -> F；h0 : f 0 = 0；hm : forall x y, f (midpoint R x y) = midpoint R' (f 
x) (f y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A map `f : E → F` sending zero to zero and midpoints to midpoints is an `AddMono
idHom`.
-/
def ofMapMidpoint (f : E → F) (h0 : f 0 = 0)
    (hm : ∀ x y, f (midpoint R x y) = midpoint R' (f x) (f y)) : E →+ F where
  toFun := f
  map_zero' := h0
  map_add' x y :=
    calc
      f (x + y) = f 0 + f (x + y) := by rw [h0, zero_add]
      _ = midpoint R' (f 0) (f (x + y)) + midpoint R' (f 0) (f (x + y)) :=
        (midpoint_add_self _ _ _).symm
      _ = f (midpoint R x y) + f (midpoint R x y) := by rw [← hm, midpoint_zero_add]
      _ = f x + f y := by rw [hm, midpoint_add_self]

@[simp]
/-
**AddMonoidHom.coe_ofMapMidpoint** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidHom`。
形式化陈述：coe_ofMapMidpoint (f : E -> F) (h0 : f 0 = 0) (hm : forall x y, f (midpoin
t R x y) = midpoint R' (f x) (f y)) : ⇑(ofMapMidpoint R R' f h0 hm) = f
参数：f : E -> F；h0 : f 0 = 0；hm : forall x y, f (midpoint R x y) = midpoint R' (f 
x) (f y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem coe_ofMapMidpoint (f : E → F) (h0 : f 0 = 0)
    (hm : ∀ x y, f (midpoint R x y) = midpoint R' (f x) (f y)) :
    ⇑(ofMapMidpoint R R' f h0 hm) = f :=
  rfl

end AddMonoidHom

