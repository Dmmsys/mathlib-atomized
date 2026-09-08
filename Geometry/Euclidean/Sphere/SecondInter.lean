/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Analysis.Convex.Side
public import Mathlib.Analysis.Convex.StrictCombination
public import Mathlib.Geometry.Euclidean.Sphere.Basic

/-!
# Second intersection of a sphere and a line

This file defines and proves basic results about the second intersection of a sphere with a line
through a point on that sphere.

## Main definitions

* `EuclideanGeometry.Sphere.secondInter` is the second intersection of a sphere with a line
  through a point on that sphere.

-/

@[expose] public section


noncomputable section

open RealInnerProductSpace

namespace EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]
variable {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [MetricSpace P₂]
variable [NormedAddTorsor V₂ P₂]

/-- The second intersection of a sphere with a line through a point on that sphere; that point
if it is the only point of intersection of the line with the sphere. The intended use of this
definition is when `p ∈ s`; the definition does not use `s.radius`, so in general it returns
the second intersection with the sphere through `p` and with center `s.center`. -/
/-
**EuclideanGeometry.Sphere.secondInter** 是 Mathlib 中的一个定义，位于命名空间 `EuclideanGeome
try.Sphere`。
形式化陈述：{V : Type u_1} →   {P : Type u_2} →     [inst : NormedAddCommGroup V] →   
    [InnerProductSpace ℝ V] →         [inst_2 : MetricSpace P] → [NormedAddTorso
r V P] → EuclideanGeometry.Sphere P → P → V → P
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second intersection of a sphere with a line through a point on that sphere; 
that point
if it is the only point of intersection of the line with the sphere. The intende
d use of this
definition is when `p ∈ s`; the definition does not use `s.radius`, so in genera
l it returns
the second intersection with the sphere through `p` and with center `s.center`.
-/
def Sphere.secondInter (s : Sphere P) (p : P) (v : V) : P :=
  (-2 * ⟪v, p -ᵥ s.center⟫ / ⟪v, v⟫) • v +ᵥ p

set_option backward.isDefEq.respectTransparency false in
/-
**EuclideanGeometry.Sphere.secondInter_map** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanG
eometry.Sphere`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
V₂ : Type u_3} {P₂ : Type u_4} [inst_4 : NormedAddCommGroup V₂]   [inst_5 : Inne
rProductSpace ℝ V₂] [inst_6 : MetricSpace P₂] [inst_7 : NormedAddTorsor V₂ P₂]  
 (s : EuclideanGeometry.Sphere P) (p : P) (v : V) (f : P →ᵃⁱ[ℝ] P₂),   { center 
:= f s.center, radius := s.radius }.secondInter (f p) (f.linearIsometry v) = f (
s.secondInter p v)
参数：s : EuclideanGeometry.Sphere P；p : P；v : V；f : P →ᵃⁱ[ℝ] P₂；f p；f.linearIsomet
ry v；s.secondInter p v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearIsometry.inner_map_map`：LinearIsometry.inner_map_map (f : E ->ₗᵢ[𝕜
] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `norm_map`：∀ {𝓕 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : Seminor
medAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst_2 : FunLike 𝓕 E F] [Iso…
· 使用定理 `SemilinearIsometryClass.toIsometryClass`：∀ {R : Type u_1} {R₂ : Type u_2
} {E : Type u_5} {E₂ : Type u_6} {𝓕 : Type u_10} [inst : Semiring R]   [inst_1 :
 Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `AffineIsometry.map_vadd`：map_vadd (p : P) (v : V) : f (v +ᵥ p) = f.linea
rIsometry v +ᵥ f p
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma Sphere.secondInter_map (s : Sphere P) (p : P) (v : V) (f : P →ᵃⁱ[ℝ] P₂) :
    Sphere.secondInter ⟨f s.center, s.radius⟩ (f p) (f.linearIsometry v) =
      f (s.secondInter p v) := by
  simp [secondInter, ← AffineIsometry.map_vsub]
/-
**EuclideanGeometry.Sphere.coe_secondInter** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanG
eometry.Sphere`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] (
as : AffineSubspace ℝ P) [inst_4 : Nonempty ↥as] (s : EuclideanGeometry.Sphere ↥
as)   (p : ↥as) (v : ↥as.direction), ↑(s.secondInter p v) = { center := ↑s.cente
r, radius := s.radius }.secondInter ↑p ↑v
参数：as : AffineSubspace ℝ P；s : EuclideanGeometry.Sphere ↥as；p : ↥as；v : ↥as.dire
ction；s.secondInter p v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Sphere.coe_secondInter (as : AffineSubspace ℝ P) [Nonempty as] (s : Sphere as)
    (p : as) (v : as.direction) :
    s.secondInter p v = Sphere.secondInter ⟨(s.center : P), s.radius⟩ (p : P) (v : V) :=
  rfl

/-- The distance between `secondInter` and the center equals the distance between the original
point and the center. -/
@[simp]
/-
**EuclideanGeometry.Sphere.secondInter_dist** 是 Mathlib 中的一个定理，位于命名空间 `Euclidean
Geometry.Sphere`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] (
s : EuclideanGeometry.Sphere P) (p : P) (v : V),   dist (s.secondInter p v) s.ce
nter = dist p s.center
参数：s : EuclideanGeometry.Sphere P；p : P；v : V；s.secondInter p v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.Sphere.secondInter.eq_1`：∀ {V : Type u_1} {P : Type u_
2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Metr
icSpace P]   [inst_3 : NormedAd…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `zero_vadd`：∀ (M : Type u_1) {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (b : α), 0 +ᵥ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `EuclideanGeometry.dist_smul_vadd_eq_dist`：dist_smul_vadd_eq_dist {v : V}
 (p₁ p₂ : P) (hv : v != 0) (r : Real) : dist (r • v +ᵥ p₁) p₂ = dist p₁ p₂ ↔ r =
 0 ∨ r = -2 * ⟪v, p₁ -ᵥ p₂⟫ / …

--- 原说明 ---
The distance between `secondInter` and the center equals the distance between th
e original
point and the center.
-/
theorem Sphere.secondInter_dist (s : Sphere P) (p : P) (v : V) :
    dist (s.secondInter p v) s.center = dist p s.center := by
  rw [Sphere.secondInter]
  by_cases hv : v = 0; · simp [hv]
  rw [dist_smul_vadd_eq_dist _ _ hv]
  exact Or.inr rfl

/-- The point given by `secondInter` lies on the sphere. -/
@[simp]
/-
**EuclideanGeometry.Sphere.secondInter_mem** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanG
eometry.Sphere`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s : EuclideanGeometry.Sphere P} {p : P} (v : V), s.secondInter p v ∈ s ↔ p ∈ s
参数：v : V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `EuclideanGeometry.Sphere.secondInter_dist`：∀ {V : Type u_1} {P : Type u_
2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Metr
icSpace P]   [inst_3 : NormedAd…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The point given by `secondInter` lies on the sphere.
-/
theorem Sphere.secondInter_mem {s : Sphere P} {p : P} (v : V) : s.secondInter p v ∈ s ↔ p ∈ s := by
  simp_rw [mem_sphere, Sphere.secondInter_dist]

variable (V) in
/-- If the vector is zero, `secondInter` gives the original point. -/
@[simp]
/-
**EuclideanGeometry.Sphere.secondInter_zero** 是 Mathlib 中的一个定理，位于命名空间 `Euclidean
Geometry.Sphere`。
形式化陈述：∀ (V : Type u_1) {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] (
s : EuclideanGeometry.Sphere P) (p : P), s.secondInter p 0 = p
参数：V : Type u_1；s : EuclideanGeometry.Sphere P；p : P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `zero_vadd`：∀ (M : Type u_1) {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (b : α), 0 +ᵥ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If the vector is zero, `secondInter` gives the original point.
-/
theorem Sphere.secondInter_zero (s : Sphere P) (p : P) : s.secondInter p (0 : V) = p := by
  simp [Sphere.secondInter]

/-- The point given by `secondInter` equals the original point if and only if the line is
orthogonal to the radius vector. -/
/-
**EuclideanGeometry.Sphere.secondInter_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Eu
clideanGeometry.Sphere`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s : EuclideanGeometry.Sphere P} {p : P} {v : V},   s.secondInter p v = p ↔ inner
 ℝ v (p -ᵥ s.center) = 0
参数：p -ᵥ s.center。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `or_iff_right`：∀ {a b : Prop}, ¬a → (a ∨ b ↔ b)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `or_iff_left`：∀ {b a : Prop}, ¬b → (a ∨ b ↔ a)
· 使用定理 `inner_self_eq_zero`：inner_self_eq_zero {x : E} : ⟪x, x⟫ = 0 ↔ x = 0
· 使用定理 `div_eq_zero_iff`：div_eq_zero_iff : a / b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `smul_eq_zero`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_
1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {r : R}   {m : M} [Module.IsTo
rs…
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `eq_vadd_iff_vsub_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] (p₁ : P) (g : G) (p₂ : P),   p₁ = g +ᵥ p₂ ↔ p₁ -ᵥ p₂ = g
· 使用定理 `EuclideanGeometry.Sphere.secondInter.eq_1`：∀ {V : Type u_1} {P : Type u_
2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Metr
icSpace P]   [inst_3 : NormedAd…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `zero_vadd`：∀ (M : Type u_1) {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (b : α), 0 +ᵥ b = b

--- 原说明 ---
The point given by `secondInter` equals the original point if and only if the li
ne is
orthogonal to the radius vector.
-/
theorem Sphere.secondInter_eq_self_iff {s : Sphere P} {p : P} {v : V} :
    s.secondInter p v = p ↔ ⟪v, p -ᵥ s.center⟫ = 0 := by
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · by_cases hv : v = 0
    · simp [hv]
    rwa [Sphere.secondInter, eq_comm, eq_vadd_iff_vsub_eq, vsub_self, eq_comm, smul_eq_zero,
      or_iff_left hv, div_eq_zero_iff, inner_self_eq_zero, or_iff_left hv, mul_eq_zero,
      or_iff_right (by simp : (-2 : ℝ) ≠ 0)] at hp
  · rw [Sphere.secondInter, hp, mul_zero, zero_div, zero_smul, zero_vadd]

/-- A point on a line through a point on a sphere equals that point or `secondInter`. -/
/-
**EuclideanGeometry.Sphere.eq_or_eq_secondInter_of_mem_mk'_span_singleton_iff_me
m** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s : EuclideanGeometry.Sphere P} {p : P},   p ∈ s → ∀ {v : V} {p' : P}, p' ∈ Affi
neSubspace.mk' p (ℝ ∙ v) → (p' = p ∨ p' = s.secondInter p v ↔ p' ∈ s)
参数：ℝ ∙ v；p' = p ∨ p' = s.secondInter p v ↔ p' ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.Sphere.secondInter_mem`：∀ {V : Type u_1} {P : Type u_2
} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Metri
cSpace P]   [inst_3 : NormedAd…
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用定理 `AffineSubspace.mem_mk'`：mem_mk' {p q : P} {direction : Submodule k V} : 
q in mk' p direction ↔ q -ᵥ p in direction
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `zero_vadd`：∀ (M : Type u_1) {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (b : α), 0 +ᵥ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `EuclideanGeometry.Sphere.secondInter_zero`：∀ (V : Type u_1) {P : Type u_
2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Metr
icSpace P]   [inst_3 : NormedAd…
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `EuclideanGeometry.Sphere.secondInter.eq_1`：∀ {V : Type u_1} {P : Type u_
2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Metr
icSpace P]   [inst_3 : NormedAd…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `EuclideanGeometry.dist_smul_vadd_eq_dist`：dist_smul_vadd_eq_dist {v : V}
 (p₁ p₂ : P) (hv : v != 0) (r : Real) : dist (r • v +ᵥ p₁) p₂ = dist p₁ p₂ ↔ r =
 0 ∨ r = -2 * ⟪v, p₁ -ᵥ p₂⟫ / …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EuclideanGeometry.mem_sphere`：mem_sphere {p : P} {s : Sphere P} : p in s
 ↔ dist p s.center = s.radius
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `eq_vadd_iff_vsub_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] (p₁ : P) (g : G) (p₂ : P),   p₁ = g +ᵥ p₂ ↔ p₁ -ᵥ p₂ = g
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a

--- 原说明 ---
A point on a line through a point on a sphere equals that point or `secondInter`
.
-/
theorem Sphere.eq_or_eq_secondInter_of_mem_mk'_span_singleton_iff_mem {s : Sphere P} {p : P}
    (hp : p ∈ s) {v : V} {p' : P} (hp' : p' ∈ AffineSubspace.mk' p (ℝ ∙ v)) :
    p' = p ∨ p' = s.secondInter p v ↔ p' ∈ s := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with (h | h)
    · rwa [h]
    · rwa [h, Sphere.secondInter_mem]
  · rw [AffineSubspace.mem_mk', Submodule.mem_span_singleton] at hp'
    rcases hp' with ⟨r, hr⟩
    rw [eq_comm, ← eq_vadd_iff_vsub_eq] at hr
    subst hr
    by_cases hv : v = 0
    · simp [hv]
    rw [Sphere.secondInter]
    rw [mem_sphere] at h hp
    rw [← hp, dist_smul_vadd_eq_dist _ _ hv] at h
    rcases h with (h | h) <;> simp [h]

/-- A point on a line through a point on a sphere and a second point equals that point or
`secondInter`. -/
/-
**EuclideanGeometry.Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair**
 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s : EuclideanGeometry.Sphere P} {p q : P},   p ∈ s → ∀ {p' : P}, p' ∈ line[ℝ, p,
 q] → (p' = p ∨ p' = s.secondInter p (q -ᵥ p) ↔ p' ∈ s)
参数：p' = p ∨ p' = s.secondInter p (q -ᵥ p) ↔ p' ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Sphere.eq_or_eq_secondInter_of_mem_mk'_span_singleton_
iff_mem`：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 :
 InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.eq_iff_direction_eq_of_mem`：eq_iff_direction_eq_of_mem {s
₁ s₂ : AffineSubspace k P} {p : P} (h₁ : p in s₁) (h₂ : p in s₂) : s₁ = s₂ ↔ s₁.
direction = s₂.direction
· 使用定理 `AffineSubspace.self_mem_mk'`：self_mem_mk' (p : P) (direction : Submodule
 k V) : p in mk' p direction
· 使用定理 `left_mem_affineSpan_pair`：left_mem_affineSpan_pair (p₁ p₂ : P) : p₁ in l
ine[k, p₁, p₂]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AffineSubspace.direction_mk'`：direction_mk' (p : P) (direction : Submodu
le k V) : (mk' p direction).direction = direction
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用定理 `vectorSpan_pair_rev`：vectorSpan_pair_rev (p₁ p₂ : P) : vectorSpan k ({p₁
, p₂} : Set P) = k ∙ (p₂ -ᵥ p₁)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A point on a line through a point on a sphere and a second point equals that poi
nt or
`secondInter`.
-/
lemma Sphere.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair {s : Sphere P} {p q : P}
    (hp : p ∈ s) {p' : P} (hp' : p' ∈ line[ℝ, p, q]) :
    p' = p ∨ p' = s.secondInter p (q -ᵥ p) ↔ p' ∈ s := by
  convert! s.eq_or_eq_secondInter_of_mem_mk'_span_singleton_iff_mem hp ?_
  convert! hp'
  rw [AffineSubspace.eq_iff_direction_eq_of_mem (AffineSubspace.self_mem_mk' p _)
    (left_mem_affineSpan_pair _ _ _)]
  simp [direction_affineSpan, vectorSpan_pair_rev]

/-- `secondInter` is unchanged by multiplying the vector by a nonzero real. -/
@[simp]
/-
**EuclideanGeometry.Sphere.secondInter_smul** 是 Mathlib 中的一个定理，位于命名空间 `Euclidean
Geometry.Sphere`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] (
s : EuclideanGeometry.Sphere P) (p : P) (v : V) {r : ℝ},   r ≠ 0 → s.secondInter
 p (r • v) = s.secondInter p v
参数：s : EuclideanGeometry.Sphere P；p : P；v : V；r • v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `real_inner_smul_left`：real_inner_smul_left (x y : F) (r : Real) : ⟪r • x
, y⟫_Real = r * ⟪x, y⟫_Real
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `div_mul_eq_div_div`：div_mul_eq_div_div : a / (b * c) = a / b / c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)

--- 原说明 ---
`secondInter` is unchanged by multiplying the vector by a nonzero real.
-/
theorem Sphere.secondInter_smul (s : Sphere P) (p : P) (v : V) {r : ℝ} (hr : r ≠ 0) :
    s.secondInter p (r • v) = s.secondInter p v := by
  simp_rw [Sphere.secondInter, real_inner_smul_left, inner_smul_right, smul_smul,
    div_mul_eq_div_div]
  rw [mul_comm, ← mul_div_assoc, ← mul_div_assoc, mul_div_cancel_left₀ _ hr, mul_comm, mul_assoc,
    mul_div_cancel_left₀ _ hr, mul_comm]

/-- `secondInter` is unchanged by negating the vector. -/
@[simp]
/-
**EuclideanGeometry.Sphere.secondInter_neg** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanG
eometry.Sphere`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] (
s : EuclideanGeometry.Sphere P) (p : P) (v : V),   s.secondInter p (-v) = s.seco
ndInter p v
参数：s : EuclideanGeometry.Sphere P；p : P；v : V；-v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_one_smul`：neg_one_smul (x : M) : (-1 : R) • x = -x
· 使用定理 `EuclideanGeometry.Sphere.secondInter_smul`：∀ {V : Type u_1} {P : Type u_
2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Metr
icSpace P]   [inst_3 : NormedAd…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
`secondInter` is unchanged by negating the vector.
-/
theorem Sphere.secondInter_neg (s : Sphere P) (p : P) (v : V) :
    s.secondInter p (-v) = s.secondInter p v := by
  rw [← neg_one_smul ℝ v, s.secondInter_smul p v (by simp : (-1 : ℝ) ≠ 0)]

/-- Applying `secondInter` twice returns the original point. -/
@[simp]
/-
**EuclideanGeometry.Sphere.secondInter_secondInter** 是 Mathlib 中的一个定理，位于命名空间 `Eu
clideanGeometry.Sphere`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] (
s : EuclideanGeometry.Sphere P) (p : P) (v : V),   s.secondInter (s.secondInter 
p v) v = p
参数：s : EuclideanGeometry.Sphere P；p : P；v : V；s.secondInter p v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `EuclideanGeometry.Sphere.secondInter_zero`：∀ (V : Type u_1) {P : Type u_
2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Metr
icSpace P]   [inst_3 : NormedAd…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inner_self_ne_zero`：inner_self_ne_zero {x : E} : ⟪x, x⟫ != 0 ↔ x != 0
· 使用定理 `vadd_vsub_assoc`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T 
: AddTorsor G P] (g : G) (p₁ p₂ : P),   (g +ᵥ p₁) -ᵥ p₂ = g + (p₁ -ᵥ p₂)
· 使用定理 `inner_add_right`：inner_add_right (x y z : E) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x,
 z⟫
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `vadd_vadd`：∀ {M : Type u_1} {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (a₁ a₂ : M) (b : α),   a₁ +ᵥ a₂ +ᵥ b = (a₁ + a₂) +ᵥ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
（共 54 条，此处仅展示前 30 条）

--- 原说明 ---
Applying `secondInter` twice returns the original point.
-/
theorem Sphere.secondInter_secondInter (s : Sphere P) (p : P) (v : V) :
    s.secondInter (s.secondInter p v) v = p := by
  by_cases hv : v = 0; · simp [hv]
  have hv' : ⟪v, v⟫ ≠ 0 := inner_self_ne_zero.2 hv
  simp only [Sphere.secondInter, vadd_vsub_assoc, vadd_vadd, inner_add_right, inner_smul_right,
    div_mul_cancel₀ _ hv']
  rw [← @vsub_eq_zero_iff_eq V, vadd_vsub, ← add_smul, ← add_div]
  convert! zero_smul ℝ _
  convert! zero_div (G₀ := ℝ) _
  ring

set_option backward.isDefEq.respectTransparency false in
/-- If the vector passed to `secondInter` is given by a subtraction involving the point in
`secondInter`, the result of `secondInter` may be expressed using `lineMap`. -/
/-
**EuclideanGeometry.Sphere.secondInter_eq_lineMap** 是 Mathlib 中的一个定理，位于命名空间 `Euc
lideanGeometry.Sphere`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] (
s : EuclideanGeometry.Sphere P) (p p' : P),   s.secondInter p (p' -ᵥ p) =     (A
ffineMap.lineMap p p') (-2 * inner ℝ (p' -ᵥ p) (p -ᵥ s.center) / inner ℝ (p' -ᵥ 
p) (p' -ᵥ p))
参数：s : EuclideanGeometry.Sphere P；p p' : P；p' -ᵥ p；AffineMap.lineMap p p'；-2 * i
nner ℝ (p' -ᵥ p) (p -ᵥ s.center) / inner ℝ (p' -ᵥ p) (p' -ᵥ p)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the vector passed to `secondInter` is given by a subtraction involving the po
int in
`secondInter`, the result of `secondInter` may be expressed using `lineMap`.
-/
theorem Sphere.secondInter_eq_lineMap (s : Sphere P) (p p' : P) :
    s.secondInter p (p' -ᵥ p) =
      AffineMap.lineMap p p' (-2 * ⟪p' -ᵥ p, p -ᵥ s.center⟫ / ⟪p' -ᵥ p, p' -ᵥ p⟫) :=
  rfl

/-- If the vector passed to `secondInter` is given by a subtraction involving the point in
`secondInter`, the result lies in the span of the two points. -/
/-
**EuclideanGeometry.Sphere.secondInter_vsub_mem_affineSpan** 是 Mathlib 中的一个定理，位于
命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] (
s : EuclideanGeometry.Sphere P) (p₁ p₂ : P),   s.secondInter p₁ (p₂ -ᵥ p₁) ∈ lin
e[ℝ, p₁, p₂]
参数：s : EuclideanGeometry.Sphere P；p₁ p₂ : P；p₂ -ᵥ p₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_vsub_vadd_mem_affineSpan_pair`：smul_vsub_vadd_mem_affineSpan_pair (
r : k) (p₁ p₂ : P) : r • (p₂ -ᵥ p₁) +ᵥ p₁ in line[k, p₁, p₂]

--- 原说明 ---
If the vector passed to `secondInter` is given by a subtraction involving the po
int in
`secondInter`, the result lies in the span of the two points.
-/
theorem Sphere.secondInter_vsub_mem_affineSpan (s : Sphere P) (p₁ p₂ : P) :
    s.secondInter p₁ (p₂ -ᵥ p₁) ∈ line[ℝ, p₁, p₂] :=
  smul_vsub_vadd_mem_affineSpan_pair _ _ _

/-- If the vector passed to `secondInter` is given by a subtraction involving the point in
`secondInter`, the three points are collinear. -/
/-
**EuclideanGeometry.Sphere.secondInter_collinear** 是 Mathlib 中的一个定理，位于命名空间 `Eucl
ideanGeometry.Sphere`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] (
s : EuclideanGeometry.Sphere P) (p p' : P),   Collinear ℝ {p, p', s.secondInter 
p (p' -ᵥ p)}
参数：s : EuclideanGeometry.Sphere P；p p' : P；p' -ᵥ p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.pair_comm`：pair_comm (a b : α) : ({a, b} : Set α) = {b, a}
· 使用定理 `Set.insert_comm`：insert_comm (a b : α) (s : Set α) : insert a (insert b 
s) = insert b (insert a s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `collinear_insert_iff_of_mem_affineSpan`：collinear_insert_iff_of_mem_affi
neSpan {s : Set P} {p : P} (h : p in affineSpan k s) : Collinear k (insert p s) 
↔ Collinear k s
· 使用定理 `EuclideanGeometry.Sphere.secondInter_vsub_mem_affineSpan`：∀ {V : Type u_
1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V]
 [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `collinear_pair`：collinear_pair (p₁ p₂ : P) : Collinear k ({p₁, p₂} : Set
 P)

--- 原说明 ---
If the vector passed to `secondInter` is given by a subtraction involving the po
int in
`secondInter`, the three points are collinear.
-/
theorem Sphere.secondInter_collinear (s : Sphere P) (p p' : P) :
    Collinear ℝ ({p, p', s.secondInter p (p' -ᵥ p)} : Set P) := by
  rw [Set.pair_comm, Set.insert_comm]
  exact
    (collinear_insert_iff_of_mem_affineSpan (s.secondInter_vsub_mem_affineSpan _ _)).2
      (collinear_pair ℝ _ _)

/-- If the vector passed to `secondInter` is given by a subtraction involving the point in
`secondInter`, and the second point is not outside the sphere, the second point is weakly
between the first point and the result of `secondInter`. -/
/-
**EuclideanGeometry.Sphere.wbtw_secondInter** 是 Mathlib 中的一个定理，位于命名空间 `Euclidean
Geometry.Sphere`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s : EuclideanGeometry.Sphere P} {p p' : P},   p ∈ s → dist p' s.center ≤ s.radiu
s → Wbtw ℝ p p' (s.secondInter p (p' -ᵥ p))
参数：s.secondInter p (p' -ᵥ p)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `EuclideanGeometry.Sphere.secondInter_zero`：∀ (V : Type u_1) {P : Type u_
2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Metr
icSpace P]   [inst_3 : NormedAd…
· 使用定理 `EuclideanGeometry.wbtw_of_collinear_of_dist_center_le_radius`：wbtw_of_co
llinear_of_dist_center_le_radius {s : Sphere P} {p₁ p₂ p₃ : P} (h : Collinear Re
al ({p₁, p₂, p₃} : Set P)) (hp₁ : p₁ in s) (hp₂ : …
· 使用定理 `EuclideanGeometry.Sphere.secondInter_collinear`：∀ {V : Type u_1} {P : Ty
pe u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 :
 MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EuclideanGeometry.Sphere.secondInter_mem`：∀ {V : Type u_1} {P : Type u_2
} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Metri
cSpace P]   [inst_3 : NormedAd…
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `EuclideanGeometry.inner_pos_or_eq_of_dist_le_radius`：inner_pos_or_eq_of_
dist_le_radius {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ in s) (hp₂ : dist p₂ s.cente
r <= s.radius) : 0 < ⟪p₁ -ᵥ p₂, p₁ -ᵥ s.c…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `neg_vsub_eq_vsub_rev`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G
] [T : AddTorsor G P] (p₁ p₂ : P), -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁
· 使用定理 `inner_neg_left`：inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `EuclideanGeometry.Sphere.secondInter_eq_self_iff`：∀ {V : Type u_1} {P : 
Type u_2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2
 : MetricSpace P]   [inst_3 : NormedAd…

--- 原说明 ---
If the vector passed to `secondInter` is given by a subtraction involving the po
int in
`secondInter`, and the second point is not outside the sphere, the second point 
is weakly
between the first point and the result of `secondInter`.
-/
theorem Sphere.wbtw_secondInter {s : Sphere P} {p p' : P} (hp : p ∈ s)
    (hp' : dist p' s.center ≤ s.radius) : Wbtw ℝ p p' (s.secondInter p (p' -ᵥ p)) := by
  by_cases h : p' = p; · simp [h]
  refine
    wbtw_of_collinear_of_dist_center_le_radius (s.secondInter_collinear p p') hp hp'
      ((Sphere.secondInter_mem _).2 hp) ?_
  intro he
  rw [eq_comm, Sphere.secondInter_eq_self_iff, ← neg_neg (p' -ᵥ p), inner_neg_left,
    neg_vsub_eq_vsub_rev, neg_eq_zero, eq_comm] at he
  exact ((inner_pos_or_eq_of_dist_le_radius hp hp').resolve_right (Ne.symm h)).ne he

/-- If the vector passed to `secondInter` is given by a subtraction involving the point in
`secondInter`, and the second point is inside the sphere, the second point is strictly between
the first point and the result of `secondInter`. -/
/-
**EuclideanGeometry.Sphere.sbtw_secondInter** 是 Mathlib 中的一个定理，位于命名空间 `Euclidean
Geometry.Sphere`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s : EuclideanGeometry.Sphere P} {p p' : P},   p ∈ s → dist p' s.center < s.radiu
s → Sbtw ℝ p p' (s.secondInter p (p' -ᵥ p))
参数：s.secondInter p (p' -ᵥ p)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanGeometry.Sphere.wbtw_secondInter`：∀ {V : Type u_1} {P : Type u_
2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Metr
icSpace P]   [inst_3 : NormedAd…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanGeometry.mem_sphere`：mem_sphere {p : P} {s : Sphere P} : p in s
 ↔ dist p s.center = s.radius
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EuclideanGeometry.Sphere.secondInter_mem`：∀ {V : Type u_1} {P : Type u_2
} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Metri
cSpace P]   [inst_3 : NormedAd…

--- 原说明 ---
If the vector passed to `secondInter` is given by a subtraction involving the po
int in
`secondInter`, and the second point is inside the sphere, the second point is st
rictly between
the first point and the result of `secondInter`.
-/
theorem Sphere.sbtw_secondInter {s : Sphere P} {p p' : P} (hp : p ∈ s)
    (hp' : dist p' s.center < s.radius) : Sbtw ℝ p p' (s.secondInter p (p' -ᵥ p)) := by
  refine ⟨Sphere.wbtw_secondInter hp hp'.le, ?_, ?_⟩
  · rintro rfl
    rw [mem_sphere] at hp
    simp [hp] at hp'
  · rintro h
    rw [h, mem_sphere.1 ((Sphere.secondInter_mem _).2 hp)] at hp'
    exact lt_irrefl _ hp'

/-- If the point passed to `secondInter` is a vertex of a simplex, lying on the sphere, and all
vertices lie on or inside the sphere, and the vector passed to `secondInter` is given by a
subtraction involving that vertex and a point in the interior of the opposite face, the given
vertex and the result of `secondInter` are on opposite sides of that face. -/
/-
**EuclideanGeometry.Sphere.sOppSide_faceOpposite_secondInter_of_mem_interior_fac
eOpposite** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s : EuclideanGeometry.Sphere P} {n : ℕ} [inst_4 : NeZero n]   {sx : Affine.Simpl
ex ℝ P n} {i : Fin (n + 1)},   sx.points i ∈ s →     (∀ (j : Fin (n + 1)), dist 
(sx.points j) s.center ≤ s.radius) →       ∀ {p : P},         p ∈ (sx.faceOpposi
te i).interior →           (affineSpan ℝ (Set.range (sx.faceOpposite i).points))
.SOppSide (sx.points i)             (s.secondInter (sx.points i) (p -ᵥ sx.points
 i))
参数：n + 1；∀ (j : Fin (n + 1)), dist (sx.points j) s.center ≤ s.radius；sx.faceOppo
site i；affineSpan ℝ (Set.range (sx.faceOpposite i).points)；sx.points i；s.secondI
nter (sx.points i) (p -ᵥ sx.points i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sbtw.sOppSide_of_notMem_of_mem`：∀ {R : Type u_1} {V : Type u_2} {P : Typ
e u_4} [inst : Field R] [inst_1 : LinearOrder R]   [inst_2 : IsStrictOrderedRing
 R] [inst_3 : AddCom…
· 使用定理 `EuclideanGeometry.Sphere.sbtw_secondInter`：∀ {V : Type u_1} {P : Type u_
2} [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : Metr
icSpace P]   [inst_3 : NormedAd…
· 使用引理 `Affine.Simplex.dist_lt_of_mem_interior_of_strictConvexSpace`：dist_lt_of_
mem_interior_of_strictConvexSpace {n : Nat} (s : Simplex Real P n) {r : Real} {p
₀ p : P} (hp : p in s.interior) (hr : forall i, d…
· 使用定理 `UniformConvexSpace.toStrictConvexSpace`：∀ {E : Type u_1} [inst : NormedA
ddCommGroup E] [inst_1 : NormedSpace ℝ E] [UniformConvexSpace E], StrictConvexSp
ace ℝ E
· 使用定理 `InnerProductSpace.toUniformConvexSpace`：∀ {F : Type u_3} [inst : Seminor
medAddCommGroup F] [InnerProductSpace ℝ F], UniformConvexSpace F
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Affine.Simplex.range_faceOpposite_points`：∀ {k : Type u_1} {V : Type u_2
} {P : Type u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Modu
le k V]   [inst_3 : AddTorsor …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.mem_of_mem_of_subset`：mem_of_mem_of_subset {x : α} {s t : Set α} (hx
 : x in s) (h : s subseteq t) : x in t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Affine.Simplex.interior_subset_closedInterior`：interior_subset_closedInt
erior {n : Nat} (s : Simplex k P n) : s.interior subseteq s.closedInterior
· 使用引理 `Affine.Simplex.closedInterior_subset_affineSpan`：closedInterior_subset_a
ffineSpan {n : Nat} {s : Simplex k P n} : s.closedInterior subseteq affineSpan k
 (Set.range s.points)

--- 原说明 ---
If the point passed to `secondInter` is a vertex of a simplex, lying on the sphe
re, and all
vertices lie on or inside the sphere, and the vector passed to `secondInter` is 
given by a
subtraction involving that vertex and a point in the interior of the opposite fa
ce, the given
vertex and the result of `secondInter` are on opposite sides of that face.
-/
lemma Sphere.sOppSide_faceOpposite_secondInter_of_mem_interior_faceOpposite {s : Sphere P}
    {n : ℕ} [NeZero n] {sx : Affine.Simplex ℝ P n} {i : Fin (n + 1)} (hi : sx.points i ∈ s)
    (hsx : ∀ j, dist (sx.points j) s.center ≤ s.radius) {p : P}
    (hp : p ∈ (sx.faceOpposite i).interior) :
    (affineSpan ℝ (Set.range (sx.faceOpposite i).points)).SOppSide (sx.points i)
      (s.secondInter (sx.points i) (p -ᵥ (sx.points i))) :=
  Sbtw.sOppSide_of_notMem_of_mem
    (s.sbtw_secondInter hi ((sx.faceOpposite i).dist_lt_of_mem_interior_of_strictConvexSpace hp
      (fun j ↦ hsx _)))
    (by simp)
    (Set.mem_of_mem_of_subset hp ((sx.faceOpposite i).interior_subset_closedInterior.trans
      (sx.faceOpposite i).closedInterior_subset_affineSpan))

attribute [local instance] Nat.AtLeastTwo.neZero_sub_one

set_option backward.isDefEq.respectTransparency false in
/-- If the point passed to `secondInter` is a vertex of a simplex, lying on the sphere, and all
vertices lie on or inside the sphere, and the vector passed to `secondInter` is given by a
subtraction involving that vertex and a point in the interior of the simplex, the given vertex
and the result of `secondInter` are on opposite sides of the face opposite that vertex. -/
/-
**EuclideanGeometry.Sphere.sOppSide_faceOpposite_secondInter_of_mem_interior** 是
 Mathlib 中的一个定理，位于命名空间 `EuclideanGeometry.Sphere`。
形式化陈述：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [inst_1 : In
nerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAddTorsor V P] {
s : EuclideanGeometry.Sphere P} {n : ℕ} [inst_4 : n.AtLeastTwo]   {sx : Affine.S
implex ℝ P n} {i : Fin (n + 1)},   sx.points i ∈ s →     (∀ (j : Fin (n + 1)), d
ist (sx.points j) s.center ≤ s.radius) →       ∀ {p : P},         p ∈ sx.interio
r →           (affineSpan ℝ (Set.range (sx.faceOpposite i).points)).SOppSide (sx
.points i)             (s.secondInter (sx.points i) (p -ᵥ sx.points i))
参数：n + 1；∀ (j : Fin (n + 1)), dist (sx.points j) s.center ≤ s.radius；affineSpan 
ℝ (Set.range (sx.faceOpposite i).points)；sx.points i；s.secondInter (sx.points i)
 (p -ᵥ sx.points i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.AtLeastTwo.toNeZero`：∀ (n : ℕ) [n.AtLeastTwo], NeZero n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineMap.lineMap_vsub_left`：lineMap_vsub_left (p₀ p₁ : P1) (c : k) : li
neMap p₀ p₁ c -ᵥ p₀ = c • (p₁ -ᵥ p₀)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `EuclideanGeometry.Sphere.sOppSide_faceOpposite_secondInter_of_mem_interi
or_faceOpposite`：∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] [
inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P]   [inst_3 : NormedAd…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.affineCombination_piSingle`：affineCombination_piSingle [Decidable
Eq ι] (p : ι -> P) {i : ι} (hi : i in s) : s.affineCombination k p (Pi.single i 
1) = p i
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Finset.affineCombination_vsub`：affineCombination_vsub (w₁ w₂ : ι -> k) (
p : ι -> P) : s.affineCombination k p w₁ -ᵥ s.affineCombination k p w₂ = s.weigh
tedVSub p (w₁ - w₂)
· 使用定理 `Finset.weightedVSub_vadd_affineCombination`：weightedVSub_vadd_affineComb
ination (w₁ w₂ : ι -> k) (p : ι -> P) : s.weightedVSub p w₁ +ᵥ s.affineCombinati
on k p w₂ = s.affineCombination …
· 使用引理 `Affine.Simplex.affineCombination_mem_interior_face_iff_pos`：affineCombin
ation_mem_interior_face_iff_pos [IsOrderedAddMonoid k] {n : Nat} (s : Simplex k 
P n) {fs : Finset (Fin (n + 1))} {m : Nat} [NeZe…
· 使用引理 `Nat.AtLeastTwo.neZero_sub_one`：neZero_sub_one : NeZero (n - 1)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
If the point passed to `secondInter` is a vertex of a simplex, lying on the sphe
re, and all
vertices lie on or inside the sphere, and the vector passed to `secondInter` is 
given by a
subtraction involving that vertex and a point in the interior of the simplex, th
e given vertex
and the result of `secondInter` are on opposite sides of the face opposite that 
vertex.
-/
lemma Sphere.sOppSide_faceOpposite_secondInter_of_mem_interior {s : Sphere P}
    {n : ℕ} [Nat.AtLeastTwo n] {sx : Affine.Simplex ℝ P n} {i : Fin (n + 1)} (hi : sx.points i ∈ s)
    (hsx : ∀ j, dist (sx.points j) s.center ≤ s.radius) {p : P}
    (hp : p ∈ sx.interior) :
    (affineSpan ℝ (Set.range (sx.faceOpposite i).points)).SOppSide (sx.points i)
      (s.secondInter (sx.points i) (p -ᵥ (sx.points i))) := by
  obtain ⟨w, hw, hw01, rfl⟩ := hp
  let r : ℝ := (1 - w i)⁻¹
  have hrpos : 0 < r := by simp [inv_pos, sub_pos, r, (hw01 i).2]
  let p' : P := AffineMap.lineMap (sx.points i) (Finset.univ.affineCombination ℝ sx.points w) r
  have hp' : (p' -ᵥ (sx.points i)) =
      r • (Finset.univ.affineCombination ℝ sx.points w -ᵥ (sx.points i)) := by simp [p']
  suffices (affineSpan ℝ (Set.range (sx.faceOpposite i).points)).SOppSide (sx.points i)
      (s.secondInter (sx.points i) (p' -ᵥ (sx.points i))) by
    rwa [hp', s.secondInter_smul _ _ hrpos.ne'] at this
  refine s.sOppSide_faceOpposite_secondInter_of_mem_interior_faceOpposite hi hsx ?_
  simp_rw [p', ← Finset.univ.affineCombination_piSingle ℝ (sx.points)
    (Finset.mem_univ i), AffineMap.lineMap_apply, Finset.affineCombination_vsub,
    ← LinearMap.map_smul, Finset.weightedVSub_vadd_affineCombination,
    Affine.Simplex.faceOpposite]
  rw [Affine.Simplex.affineCombination_mem_interior_face_iff_pos]
  · simp only [Finset.mem_compl, Finset.mem_singleton, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul, Decidable.not_not, forall_eq, Pi.single_eq_same]
    refine ⟨fun j hj ↦ ?_, by grind⟩
    simp [hj, hrpos, (hw01 j).1]
  · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hw]

end EuclideanGeometry

