/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Submodule
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.Topology.Algebra.Group.Torsor
public import Mathlib.Topology.MetricSpace.IsometricSMul

/-!
# Torsors of additive normed group actions.

This file defines torsors of additive normed group actions, with a
metric space structure.  The motivating case is Euclidean affine
spaces.
-/

@[expose] public section


noncomputable section

open NNReal Topology

open Filter

/-- A `NormedAddTorsor V P` is a torsor of an additive seminormed group
action by a `SeminormedAddCommGroup V` on points `P`. We bundle the pseudometric space
structure and require the distance to be the same as results from the
norm (which in fact implies the distance yields a pseudometric space, but
bundling just the distance and using an instance for the pseudometric space
results in type class problems). -/
/-
**NormedAddTorsor** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(V : outParam (Type u_1)) → (P : Type u_2) → [SeminormedAddCommGroup V] → 
[PseudoMetricSpace P] → Type (max u_1 u_2)
参数：Type u_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `NormedAddTorsor V P` is a torsor of an additive seminormed group
action by a `SeminormedAddCommGroup V` on points `P`. We bundle the pseudometric
 space
structure and require the distance to be the same as results from the
norm (which in fact implies the distance yields a pseudometric space, but
bundling just the distance and using an instance for the pseudometric space
results in type class problems).
-/
class NormedAddTorsor (V : outParam Type*) (P : Type*) [SeminormedAddCommGroup V]
  [PseudoMetricSpace P] extends AddTorsor V P where
  dist_eq_norm' : ∀ x y : P, dist x y = ‖(x -ᵥ y : V)‖

/-- Shortcut instance to help typeclass inference out. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Shortcut instance to help typeclass inference out.
-/
instance (priority := 100) NormedAddTorsor.toAddTorsor' {V P : Type*} [NormedAddCommGroup V]
    [MetricSpace P] [NormedAddTorsor V P] : AddTorsor V P :=
  NormedAddTorsor.toAddTorsor

variable {α V P W Q : Type*} [SeminormedAddCommGroup V] [PseudoMetricSpace P] [NormedAddTorsor V P]
  [SeminormedAddCommGroup W] [PseudoMetricSpace Q] [NormedAddTorsor W Q]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) NormedAddTorsor.to_isIsIsometricVAdd : IsIsometricVAdd V P :=
  ⟨fun c => Isometry.of_dist_eq fun x y => by
    simp [NormedAddTorsor.dist_eq_norm']⟩

/-- A `SeminormedAddCommGroup` is a `NormedAddTorsor` over itself. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `SeminormedAddCommGroup` is a `NormedAddTorsor` over itself.
-/
instance (priority := 100) SeminormedAddCommGroup.toNormedAddTorsor : NormedAddTorsor V V where
  dist_eq_norm' := dist_eq_norm

-- Because of the AddTorsor.nonempty instance.
/-- A nonempty affine subspace of a `NormedAddTorsor` is itself a `NormedAddTorsor`. -/
/-
**AffineSubspace.toNormedAddTorsor** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AffineSubspace.toNormedAddTorsor {R : Type*} [Ring R] [Module R V] (s : Af
fineSubspace R P) [Nonempty s] : NormedAddTorsor s.direction s
参数：s : AffineSubspace R P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A nonempty affine subspace of a `NormedAddTorsor` is itself a `NormedAddTorsor`.
-/
instance AffineSubspace.toNormedAddTorsor {R : Type*} [Ring R] [Module R V]
    (s : AffineSubspace R P) [Nonempty s] : NormedAddTorsor s.direction s :=
  { AffineSubspace.toAddTorsor s with
    dist_eq_norm' := fun x y => NormedAddTorsor.dist_eq_norm' x.val y.val }
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NormedAddTorsor (V × W) (P × Q) where
  dist_eq_norm' x y := by
    simp only [Prod.dist_eq, NormedAddTorsor.dist_eq_norm', Prod.norm_def, Prod.fst_vsub,
      Prod.snd_vsub]

section

variable (V W)

/-- The distance equals the norm of subtracting two points. In this
lemma, it is necessary to have `V` as an explicit argument; otherwise
`rw dist_eq_norm_vsub` sometimes doesn't work. -/
/-
**dist_eq_norm_vsub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
参数：x y : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddTorsor.dist_eq_norm'`：∀ {V : outParam (Type u_1)} {P : Type u_2
} {inst : SeminormedAddCommGroup V} {inst_1 : PseudoMetricSpace P}   [self : Nor
medAddTorsor V P] (…

--- 原说明 ---
The distance equals the norm of subtracting two points. In this
lemma, it is necessary to have `V` as an explicit argument; otherwise
`rw dist_eq_norm_vsub` sometimes doesn't work.
-/
theorem dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖ :=
  NormedAddTorsor.dist_eq_norm' x y
/-
**nndist_eq_nnnorm_vsub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_eq_nnnorm_vsub (x y : P) : nndist x y = ‖x -ᵥ y‖₊
参数：x y : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
-/
theorem nndist_eq_nnnorm_vsub (x y : P) : nndist x y = ‖x -ᵥ y‖₊ :=
  NNReal.eq <| dist_eq_norm_vsub V x y


/-- The distance equals the norm of subtracting two points. In this
lemma, it is necessary to have `V` as an explicit argument; otherwise
`rw dist_eq_norm_vsub'` sometimes doesn't work. -/
/-
**dist_eq_norm_vsub'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_eq_norm_vsub' (x y : P) : dist x y = ‖y -ᵥ x‖
参数：x y : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖

--- 原说明 ---
The distance equals the norm of subtracting two points. In this
lemma, it is necessary to have `V` as an explicit argument; otherwise
`rw dist_eq_norm_vsub'` sometimes doesn't work.
-/
theorem dist_eq_norm_vsub' (x y : P) : dist x y = ‖y -ᵥ x‖ :=
  (dist_comm _ _).trans (dist_eq_norm_vsub _ _ _)
/-
**nndist_eq_nnnorm_vsub'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_eq_nnnorm_vsub' (x y : P) : nndist x y = ‖y -ᵥ x‖₊
参数：x y : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `dist_eq_norm_vsub'`：dist_eq_norm_vsub' (x y : P) : dist x y = ‖y -ᵥ x‖
-/
theorem nndist_eq_nnnorm_vsub' (x y : P) : nndist x y = ‖y -ᵥ x‖₊ :=
  NNReal.eq <| dist_eq_norm_vsub' V x y

end

/-
**dist_vadd_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_vadd_cancel_left (v : V) (x y : P) : dist (v +ᵥ x) (v +ᵥ y) = dist x 
y
参数：v : V；x y : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dist_vadd`：∀ {M : Type u} {X : Type w} [inst : PseudoMetricSpace X] [ins
t_1 : VAdd M X] [IsIsometricVAdd M X] (c : M) (x y : X),   dist (c +ᵥ x) (c +ᵥ …
· 使用定理 `NormedAddTorsor.to_isIsIsometricVAdd`：∀ {V : Type u_2} {P : Type u_3} [i
nst : SeminormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : Norme
dAddTorsor V P], IsIsometr…
-/
theorem dist_vadd_cancel_left (v : V) (x y : P) : dist (v +ᵥ x) (v +ᵥ y) = dist x y :=
  dist_vadd _ _ _
/-
**nndist_vadd_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_vadd_cancel_left (v : V) (x y : P) : nndist (v +ᵥ x) (v +ᵥ y) = nnd
ist x y
参数：v : V；x y : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `dist_vadd_cancel_left`：dist_vadd_cancel_left (v : V) (x y : P) : dist (v
 +ᵥ x) (v +ᵥ y) = dist x y
-/
theorem nndist_vadd_cancel_left (v : V) (x y : P) : nndist (v +ᵥ x) (v +ᵥ y) = nndist x y :=
  NNReal.eq <| dist_vadd_cancel_left _ _ _

@[simp]
/-
**dist_vadd_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_vadd_cancel_right (v₁ v₂ : V) (x : P) : dist (v₁ +ᵥ x) (v₂ +ᵥ x) = di
st v₁ v₂
参数：v₁ v₂ : V；x : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `vadd_vsub_vadd_cancel_right`：∀ {G : Type u_1} {P : Type u_2} [inst : Add
Group G] [T : AddTorsor G P] (v₁ v₂ : G) (p : P),   (v₁ +ᵥ p) -ᵥ (v₂ +ᵥ p) = v₁ 
- v₂
-/
theorem dist_vadd_cancel_right (v₁ v₂ : V) (x : P) : dist (v₁ +ᵥ x) (v₂ +ᵥ x) = dist v₁ v₂ := by
  rw [dist_eq_norm_vsub V, dist_eq_norm, vadd_vsub_vadd_cancel_right]

@[simp]
/-
**nndist_vadd_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_vadd_cancel_right (v₁ v₂ : V) (x : P) : nndist (v₁ +ᵥ x) (v₂ +ᵥ x) 
= nndist v₁ v₂
参数：v₁ v₂ : V；x : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `dist_vadd_cancel_right`：dist_vadd_cancel_right (v₁ v₂ : V) (x : P) : dis
t (v₁ +ᵥ x) (v₂ +ᵥ x) = dist v₁ v₂
-/
theorem nndist_vadd_cancel_right (v₁ v₂ : V) (x : P) : nndist (v₁ +ᵥ x) (v₂ +ᵥ x) = nndist v₁ v₂ :=
  NNReal.eq <| dist_vadd_cancel_right _ _ _

@[simp]
/-
**dist_vadd_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_vadd_left (v : V) (x : P) : dist (v +ᵥ x) x = ‖v‖
参数：v : V；x : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dist_vadd_left (v : V) (x : P) : dist (v +ᵥ x) x = ‖v‖ := by
  simp [dist_eq_norm_vsub V _ x]

@[simp]
/-
**nndist_vadd_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_vadd_left (v : V) (x : P) : nndist (v +ᵥ x) x = ‖v‖₊
参数：v : V；x : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `dist_vadd_left`：dist_vadd_left (v : V) (x : P) : dist (v +ᵥ x) x = ‖v‖
-/
theorem nndist_vadd_left (v : V) (x : P) : nndist (v +ᵥ x) x = ‖v‖₊ :=
  NNReal.eq <| dist_vadd_left _ _

@[simp]
/-
**dist_vadd_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_vadd_right (v : V) (x : P) : dist x (v +ᵥ x) = ‖v‖
参数：v : V；x : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `dist_vadd_left`：dist_vadd_left (v : V) (x : P) : dist (v +ᵥ x) x = ‖v‖
-/
theorem dist_vadd_right (v : V) (x : P) : dist x (v +ᵥ x) = ‖v‖ := by rw [dist_comm, dist_vadd_left]

@[simp]
/-
**nndist_vadd_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_vadd_right (v : V) (x : P) : nndist x (v +ᵥ x) = ‖v‖₊
参数：v : V；x : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `dist_vadd_right`：dist_vadd_right (v : V) (x : P) : dist x (v +ᵥ x) = ‖v‖
-/
theorem nndist_vadd_right (v : V) (x : P) : nndist x (v +ᵥ x) = ‖v‖₊ :=
  NNReal.eq <| dist_vadd_right _ _

/-- Isometry between the tangent space `V` of a (semi)normed add torsor `P` and `P` given by
addition/subtraction of `x : P`. -/
@[simps!]
/-
**IsometryEquiv.vaddConst** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsometryEquiv.vaddConst (x : P) : V ≃ᵢ P where toEquiv
参数：x : P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Isometry between the tangent space `V` of a (semi)normed add torsor `P` and `P` 
given by
addition/subtraction of `x : P`.
-/
def IsometryEquiv.vaddConst (x : P) : V ≃ᵢ P where
  toEquiv := Equiv.vaddConst x
  isometry_toFun := Isometry.of_dist_eq fun _ _ => dist_vadd_cancel_right _ _ _

@[simp]
/-
**dist_vsub_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_vsub_cancel_left (x y z : P) : dist (x -ᵥ y) (x -ᵥ z) = dist y z
参数：x y z : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `vsub_sub_vsub_cancel_left`：∀ {G : Type u_1} {P : Type u_2} [inst : AddCo
mmGroup G] [inst_1 : AddTorsor G P] (p₁ p₂ p₃ : P),   p₃ -ᵥ p₂ - (p₃ -ᵥ p₁) = p₁
 -ᵥ p₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
-/
theorem dist_vsub_cancel_left (x y z : P) : dist (x -ᵥ y) (x -ᵥ z) = dist y z := by
  rw [dist_eq_norm, vsub_sub_vsub_cancel_left, dist_comm, dist_eq_norm_vsub V]

@[simp]
/-
**nndist_vsub_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_vsub_cancel_left (x y z : P) : nndist (x -ᵥ y) (x -ᵥ z) = nndist y 
z
参数：x y z : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `dist_vsub_cancel_left`：dist_vsub_cancel_left (x y z : P) : dist (x -ᵥ y)
 (x -ᵥ z) = dist y z
-/
theorem nndist_vsub_cancel_left (x y z : P) : nndist (x -ᵥ y) (x -ᵥ z) = nndist y z :=
  NNReal.eq <| dist_vsub_cancel_left _ _ _

/-- Isometry between the tangent space `V` of a (semi)normed add torsor `P` and `P` given by
subtraction from `x : P`. -/
@[simps!]
/-
**IsometryEquiv.constVSub** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsometryEquiv.constVSub (x : P) : P ≃ᵢ V where toEquiv
参数：x : P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Isometry between the tangent space `V` of a (semi)normed add torsor `P` and `P` 
given by
subtraction from `x : P`.
-/
def IsometryEquiv.constVSub (x : P) : P ≃ᵢ V where
  toEquiv := Equiv.constVSub x
  isometry_toFun := Isometry.of_dist_eq fun _ _ => dist_vsub_cancel_left _ _ _

@[simp]
/-
**dist_vsub_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_vsub_cancel_right (x y z : P) : dist (x -ᵥ z) (y -ᵥ z) = dist x y
参数：x y z : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsometryEquiv.dist_eq`：∀ {α : Type u_3} {β : Type u_4} [inst : PseudoMet
ricSpace α] [inst_1 : PseudoMetricSpace β] (h : α ≃ᵢ β) (x y : α),   dist (h x) 
(h y) = dis…
-/
theorem dist_vsub_cancel_right (x y z : P) : dist (x -ᵥ z) (y -ᵥ z) = dist x y :=
  (IsometryEquiv.vaddConst z).symm.dist_eq x y

@[simp]
/-
**nndist_vsub_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_vsub_cancel_right (x y z : P) : nndist (x -ᵥ z) (y -ᵥ z) = nndist x
 y
参数：x y z : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `dist_vsub_cancel_right`：dist_vsub_cancel_right (x y z : P) : dist (x -ᵥ 
z) (y -ᵥ z) = dist x y
-/
theorem nndist_vsub_cancel_right (x y z : P) : nndist (x -ᵥ z) (y -ᵥ z) = nndist x y :=
  NNReal.eq <| dist_vsub_cancel_right _ _ _
/-
**dist_vadd_vadd_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_vadd_vadd_le (v v' : V) (p p' : P) : dist (v +ᵥ p) (v' +ᵥ p') <= dist
 v v' + dist p p'
参数：v v' : V；p p' : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dist_vadd_cancel_right`：dist_vadd_cancel_right (v₁ v₂ : V) (x : P) : dis
t (v₁ +ᵥ x) (v₂ +ᵥ x) = dist v₁ v₂
· 使用定理 `dist_vadd`：∀ {M : Type u} {X : Type w} [inst : PseudoMetricSpace X] [ins
t_1 : VAdd M X] [IsIsometricVAdd M X] (c : M) (x y : X),   dist (c +ᵥ x) (c +ᵥ …
· 使用定理 `NormedAddTorsor.to_isIsIsometricVAdd`：∀ {V : Type u_2} {P : Type u_3} [i
nst : SeminormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : Norme
dAddTorsor V P], IsIsometr…
· 使用定理 `dist_triangle`：dist_triangle (x y z : α) : dist x z <= dist x y + dist y
 z
-/
theorem dist_vadd_vadd_le (v v' : V) (p p' : P) :
    dist (v +ᵥ p) (v' +ᵥ p') ≤ dist v v' + dist p p' := by
  simpa using dist_triangle (v +ᵥ p) (v' +ᵥ p) (v' +ᵥ p')
/-
**nndist_vadd_vadd_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_vadd_vadd_le (v v' : V) (p p' : P) : nndist (v +ᵥ p) (v' +ᵥ p') <= 
nndist v v' + nndist p p'
参数：v v' : V；p p' : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dist_vadd_vadd_le`：dist_vadd_vadd_le (v v' : V) (p p' : P) : dist (v +ᵥ 
p) (v' +ᵥ p') <= dist v v' + dist p p'
-/
theorem nndist_vadd_vadd_le (v v' : V) (p p' : P) :
    nndist (v +ᵥ p) (v' +ᵥ p') ≤ nndist v v' + nndist p p' :=
  dist_vadd_vadd_le _ _ _ _
/-
**dist_vsub_vsub_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_vsub_vsub_le (p₁ p₂ p₃ p₄ : P) : dist (p₁ -ᵥ p₂) (p₃ -ᵥ p₄) <= dist p
₁ p₃ + dist p₂ p₄
参数：p₁ p₂ p₃ p₄ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `vsub_sub_vsub_comm`：∀ {G : Type u_1} {P : Type u_2} [inst : AddCommGroup
 G] [inst_1 : AddTorsor G P] (p₁ p₂ p₃ p₄ : P),   p₁ -ᵥ p₂ - (p₃ -ᵥ p₄) = p₁ -ᵥ 
p₃ - (p₂…
· 使用定理 `dist_eq_norm_vsub`：dist_eq_norm_vsub (x y : P) : dist x y = ‖x -ᵥ y‖
· 使用定理 `norm_sub_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a - b‖ ≤ ‖a‖ + ‖b‖
-/
theorem dist_vsub_vsub_le (p₁ p₂ p₃ p₄ : P) :
    dist (p₁ -ᵥ p₂) (p₃ -ᵥ p₄) ≤ dist p₁ p₃ + dist p₂ p₄ := by
  rw [dist_eq_norm, vsub_sub_vsub_comm, dist_eq_norm_vsub V, dist_eq_norm_vsub V]
  exact norm_sub_le _ _
/-
**nndist_vsub_vsub_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nndist_vsub_vsub_le (p₁ p₂ p₃ p₄ : P) : nndist (p₁ -ᵥ p₂) (p₃ -ᵥ p₄) <= nn
dist p₁ p₃ + nndist p₂ p₄
参数：p₁ p₂ p₃ p₄ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem nndist_vsub_vsub_le (p₁ p₂ p₃ p₄ : P) :
    nndist (p₁ -ᵥ p₂) (p₃ -ᵥ p₄) ≤ nndist p₁ p₃ + nndist p₂ p₄ := by
  simp only [← NNReal.coe_le_coe, NNReal.coe_add, ← dist_nndist, dist_vsub_vsub_le]
/-
**edist_vadd_vadd_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_vadd_vadd_le (v v' : V) (p p' : P) : edist (v +ᵥ p) (v' +ᵥ p') <= ed
ist v v' + edist p p'
参数：v v' : V；p p' : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_nndist`：edist_nndist (x y : α) : edist x y = nndist x y
· 使用定理 `dist_vadd_vadd_le`：dist_vadd_vadd_le (v v' : V) (p p' : P) : dist (v +ᵥ 
p) (v' +ᵥ p') <= dist v v' + dist p p'
-/
theorem edist_vadd_vadd_le (v v' : V) (p p' : P) :
    edist (v +ᵥ p) (v' +ᵥ p') ≤ edist v v' + edist p p' := by
  simp only [edist_nndist]
  norm_cast
  apply dist_vadd_vadd_le
/-
**edist_vsub_vsub_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_vsub_vsub_le (p₁ p₂ p₃ p₄ : P) : edist (p₁ -ᵥ p₂) (p₃ -ᵥ p₄) <= edis
t p₁ p₃ + edist p₂ p₄
参数：p₁ p₂ p₃ p₄ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_nndist`：edist_nndist (x y : α) : edist x y = nndist x y
· 使用定理 `dist_vsub_vsub_le`：dist_vsub_vsub_le (p₁ p₂ p₃ p₄ : P) : dist (p₁ -ᵥ p₂)
 (p₃ -ᵥ p₄) <= dist p₁ p₃ + dist p₂ p₄
-/
theorem edist_vsub_vsub_le (p₁ p₂ p₃ p₄ : P) :
    edist (p₁ -ᵥ p₂) (p₃ -ᵥ p₄) ≤ edist p₁ p₃ + edist p₂ p₄ := by
  simp only [edist_nndist]
  norm_cast
  apply dist_vsub_vsub_le

/-- The pseudodistance defines a pseudometric space structure on the torsor. This
is not an instance because it depends on `V` to define a `MetricSpace P`. -/
@[instance_reducible]
/-
**pseudoMetricSpaceOfNormedAddCommGroupOfAddTorsor** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：pseudoMetricSpaceOfNormedAddCommGroupOfAddTorsor (V P : Type*) [Seminormed
AddCommGroup V] [AddTorsor V P] : PseudoMetricSpace P where dist x y
参数：V P : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pseudodistance defines a pseudometric space structure on the torsor. This
is not an instance because it depends on `V` to define a `MetricSpace P`.
-/
def pseudoMetricSpaceOfNormedAddCommGroupOfAddTorsor (V P : Type*) [SeminormedAddCommGroup V]
    [AddTorsor V P] : PseudoMetricSpace P where
  dist x y := ‖(x -ᵥ y : V)‖
  dist_self x := by simp
  dist_comm x y := by simp only [← neg_vsub_eq_vsub_rev y x, norm_neg]
  dist_triangle x y z := by
    rw [← vsub_add_vsub_cancel]
    apply norm_add_le

/-- The distance defines a metric space structure on the torsor. This
is not an instance because it depends on `V` to define a `MetricSpace P`. -/
@[instance_reducible]
/-
**metricSpaceOfNormedAddCommGroupOfAddTorsor** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：metricSpaceOfNormedAddCommGroupOfAddTorsor (V P : Type*) [NormedAddCommGro
up V] [AddTorsor V P] : MetricSpace P where dist x y
参数：V P : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The distance defines a metric space structure on the torsor. This
is not an instance because it depends on `V` to define a `MetricSpace P`.
-/
def metricSpaceOfNormedAddCommGroupOfAddTorsor (V P : Type*) [NormedAddCommGroup V]
    [AddTorsor V P] : MetricSpace P where
  dist x y := ‖(x -ᵥ y : V)‖
  dist_self x := by simp
  eq_of_dist_eq_zero h := by simpa using h
  dist_comm x y := by simp only [← neg_vsub_eq_vsub_rev y x, norm_neg]
  dist_triangle x y z := by
    rw [← vsub_add_vsub_cancel]
    apply norm_add_le
/-
**LipschitzWith.vadd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LipschitzWith.vadd [PseudoEMetricSpace α] {f : α -> V} {g : α -> P} {Kf Kg
 : Real>=0} (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) : LipschitzWith 
(Kf + Kg) (f +ᵥ g)
参数：hf : LipschitzWith Kf f；hg : LipschitzWith Kg g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `edist_vadd_vadd_le`：edist_vadd_vadd_le (v v' : V) (p p' : P) : edist (v 
+ᵥ p) (v' +ᵥ p') <= edist v v' + edist p p'
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
-/
theorem LipschitzWith.vadd [PseudoEMetricSpace α] {f : α → V} {g : α → P} {Kf Kg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) : LipschitzWith (Kf + Kg) (f +ᵥ g) :=
  fun x y =>
  calc
    edist (f x +ᵥ g x) (f y +ᵥ g y) ≤ edist (f x) (f y) + edist (g x) (g y) :=
      edist_vadd_vadd_le _ _ _ _
    _ ≤ Kf * edist x y + Kg * edist x y := add_le_add (hf x y) (hg x y)
    _ = (Kf + Kg) * edist x y := (add_mul _ _ _).symm
/-
**LipschitzWith.vsub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LipschitzWith.vsub [PseudoEMetricSpace α] {f g : α -> P} {Kf Kg : Real>=0}
 (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) : LipschitzWith (Kf + Kg) (
f -ᵥ g)
参数：hf : LipschitzWith Kf f；hg : LipschitzWith Kg g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `edist_vsub_vsub_le`：edist_vsub_vsub_le (p₁ p₂ p₃ p₄ : P) : edist (p₁ -ᵥ 
p₂) (p₃ -ᵥ p₄) <= edist p₁ p₃ + edist p₂ p₄
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
-/
theorem LipschitzWith.vsub [PseudoEMetricSpace α] {f g : α → P} {Kf Kg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) : LipschitzWith (Kf + Kg) (f -ᵥ g) :=
  fun x y =>
  calc
    edist (f x -ᵥ g x) (f y -ᵥ g y) ≤ edist (f x) (f y) + edist (g x) (g y) :=
      edist_vsub_vsub_le _ _ _ _
    _ ≤ Kf * edist x y + Kg * edist x y := add_le_add (hf x y) (hg x y)
    _ = (Kf + Kg) * edist x y := (add_mul _ _ _).symm

@[fun_prop]
/-
**uniformContinuous_vadd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_vadd : UniformContinuous fun x : V × P => x.1 +ᵥ x.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.uniformContinuous`：∀ {α : Type u} {β : Type v} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   L
ipschitzWith K f → Un…
· 使用定理 `LipschitzWith.vadd`：LipschitzWith.vadd [PseudoEMetricSpace α] {f : α -> 
V} {g : α -> P} {Kf Kg : Real>=0} (hf : LipschitzWith Kf f) (hg : LipschitzWith 
Kg g) : …
· 使用定理 `LipschitzWith.prod_fst`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetri
cSpace α] [inst_1 : PseudoEMetricSpace β], LipschitzWith 1 Prod.fst
· 使用定理 `LipschitzWith.prod_snd`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetri
cSpace α] [inst_1 : PseudoEMetricSpace β], LipschitzWith 1 Prod.snd
-/
theorem uniformContinuous_vadd : UniformContinuous fun x : V × P => x.1 +ᵥ x.2 :=
  (LipschitzWith.prod_fst.vadd LipschitzWith.prod_snd).uniformContinuous

@[fun_prop]
/-
**uniformContinuous_vsub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformContinuous_vsub : UniformContinuous fun x : P × P => x.1 -ᵥ x.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.uniformContinuous`：∀ {α : Type u} {β : Type v} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   L
ipschitzWith K f → Un…
· 使用定理 `LipschitzWith.vsub`：LipschitzWith.vsub [PseudoEMetricSpace α] {f g : α -
> P} {Kf Kg : Real>=0} (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) : Lip
schitzWi…
· 使用定理 `LipschitzWith.prod_fst`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetri
cSpace α] [inst_1 : PseudoEMetricSpace β], LipschitzWith 1 Prod.fst
· 使用定理 `LipschitzWith.prod_snd`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetri
cSpace α] [inst_1 : PseudoEMetricSpace β], LipschitzWith 1 Prod.snd
-/
theorem uniformContinuous_vsub : UniformContinuous fun x : P × P => x.1 -ᵥ x.2 :=
  (LipschitzWith.prod_fst.vsub LipschitzWith.prod_snd).uniformContinuous
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTopologicalAddTorsor P where
  continuous_vadd := uniformContinuous_vadd.continuous
  continuous_vsub := uniformContinuous_vsub.continuous

/-- Pullback of a normed add torsor along an injective map. -/
/-
**Function.Injective.normedAddTorsor** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Function.Injective.normedAddTorsor {Q : Type*} [VAdd V Q] [VSub V Q] [None
mpty Q] [PseudoMetricSpace Q] (f : Q -> P) (hf : Function.Injective f) (vadd : f
orall (c : V) (x : Q), f (c +ᵥ x) = c +ᵥ f x) (vsub : forall (x y : Q), x -ᵥ y =
 f x -ᵥ f y) (norm : forall (x y : Q), dist x y = dist (f x) (f y)) : NormedAddT
orsor V Q where __
参数：f : Q -> P；hf : Function.Injective f；vadd : forall (c : V) (x : Q), f (c +ᵥ x
) = c +ᵥ f x；vsub : forall (x y : Q), x -ᵥ y = f x -ᵥ f y；norm : forall (x y : Q
), dist x y = dist (f x) (f y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pullback of a normed add torsor along an injective map.
-/
abbrev Function.Injective.normedAddTorsor {Q : Type*} [VAdd V Q] [VSub V Q]
    [Nonempty Q] [PseudoMetricSpace Q] (f : Q → P) (hf : Function.Injective f)
    (vadd : ∀ (c : V) (x : Q), f (c +ᵥ x) = c +ᵥ f x)
    (vsub : ∀ (x y : Q), x -ᵥ y = f x -ᵥ f y)
    (norm : ∀ (x y : Q), dist x y = dist (f x) (f y)) : NormedAddTorsor V Q where
  __ := hf.addTorsor f vadd vsub
  dist_eq_norm' x y := by simp [norm, NormedAddTorsor.dist_eq_norm', vsub]

/-- Pushforward of a normed add torsor along a surjective map. -/
/-
**Function.Surjective.normedAddTorsor** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Function.Surjective.normedAddTorsor {Q : Type*} [VAdd V Q] [VSub V Q] [Pse
udoMetricSpace Q] (f : P -> Q) (hf : Surjective f) (vadd : forall (c : V) (x : P
), f (c +ᵥ x) = c +ᵥ f x) (vsub : forall (x y : P), x -ᵥ y = f x -ᵥ f y) (norm :
 forall (x y : P), dist x y = dist (f x) (f y)) : NormedAddTorsor V Q where __
参数：f : P -> Q；hf : Surjective f；vadd : forall (c : V) (x : P), f (c +ᵥ x) = c +ᵥ
 f x；vsub : forall (x y : P), x -ᵥ y = f x -ᵥ f y；norm : forall (x y : P), dist 
x y = dist (f x) (f y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pushforward of a normed add torsor along a surjective map.
-/
abbrev Function.Surjective.normedAddTorsor
    {Q : Type*} [VAdd V Q] [VSub V Q] [PseudoMetricSpace Q]
    (f : P → Q) (hf : Surjective f)
    (vadd : ∀ (c : V) (x : P), f (c +ᵥ x) = c +ᵥ f x)
    (vsub : ∀ (x y : P), x -ᵥ y = f x -ᵥ f y)
    (norm : ∀ (x y : P), dist x y = dist (f x) (f y)) : NormedAddTorsor V Q where
  __ := hf.addTorsor f vadd vsub
  dist_eq_norm' := by simp [hf.forall, ← norm, NormedAddTorsor.dist_eq_norm', ← vsub]
