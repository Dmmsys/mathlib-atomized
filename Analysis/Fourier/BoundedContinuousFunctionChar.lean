/-
Copyright (c) 2025 Jakob Stiefel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Stiefel
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Star

/-!
# Definition of BoundedContinuousFunction.char

Definition and basic properties of `BoundedContinuousFunction.char he hL w := fun v ↦ e (L v w)`,
where `e` is a continuous additive character and `L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ` is a continuous bilinear
map.

In the special case `e = Circle.exp`, this is used to define the characteristic function of a
measure.

## Main definitions

- `char he hL w : V →ᵇ ℂ`: Bounded continuous mapping `fun v ↦ e (L v w)` from `V` to `ℂ`, where
  `e` is a continuous additive character and `L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ` is a continuous bilinear map.
- `charPoly he hL : W → ℂ`: The `StarSubalgebra ℂ (V →ᵇ ℂ)` consisting of `ℂ`-linear combinations of
  `char he hL w`, where `w : W`.

## Main statements

- `ext_of_char_eq`: If `e` and `L` are non-trivial, then `char he hL w, w : W` separates
  points in `V`.
- `star_mem_range_charAlgHom`: The family of `ℂ`-linear combinations of `char he hL w, w : W`, is
  closed under `star`.
- `separatesPoints_charPoly`: The family `charPoly he hL w, w : W` separates points in `V`.

-/

@[expose] public section

open Filter BoundedContinuousFunction Complex

namespace BoundedContinuousFunction

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
    {e : AddChar ℝ Circle} {L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ}
    {he : Continuous e} {hL : Continuous fun p : V × W ↦ L p.1 p.2}

set_option backward.isDefEq.respectTransparency false in
/-- The bounded continuous mapping `fun v ↦ e (L v w)` from `V` to `ℂ`. -/
/-
**BoundedContinuousFunction.char** 是 Mathlib 中的一个定义，位于命名空间 `BoundedContinuousFun
ction`。
形式化陈述：char (he : Continuous e) (hL : Continuous fun p : V × W => L p.1 p.2) (w :
 W) : V ->ᵇ Complex where toFun
参数：he : Continuous e；hL : Continuous fun p : V × W => L p.1 p.2；w : W。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bounded continuous mapping `fun v ↦ e (L v w)` from `V` to `ℂ`.
-/
noncomputable def char (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2) (w : W) :
    V →ᵇ ℂ where
  toFun := fun v ↦ e (L v w)
  continuous_toFun :=
    continuous_induced_dom.comp (he.comp (hL.comp (Continuous.prodMk_left w)))
  map_bounded' := by
    refine ⟨2, fun x y ↦ ?_⟩
    calc dist _ _
      ≤ (‖_‖ : ℝ) + ‖_‖ := dist_le_norm_add_norm _ _
    _ ≤ 1 + 1 := add_le_add (by simp) (by simp)
    _ = 2 := by ring

@[simp]
/-
**BoundedContinuousFunction.char_apply** 是 Mathlib 中的一个引理，位于命名空间 `BoundedContinu
ousFunction`。
形式化陈述：char_apply (w : W) (v : V) : char he hL w v = e (L v w)
参数：w : W；v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
lemma char_apply (w : W) (v : V) :
    char he hL w v = e (L v w) := rfl

@[simp]
/-
**BoundedContinuousFunction.char_zero_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `BoundedC
ontinuousFunction`。
形式化陈述：char_zero_eq_one : char he hL 0 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `BoundedContinuousFunction.ext`：ext (h : forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `AddChar.map_zero_eq_one`：∀ {A : Type u_1} {M : Type u_3} [inst : AddMono
id A] [inst_1 : Monoid M] (ψ : AddChar A M), ψ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma char_zero_eq_one : char he hL 0 = 1 := by ext; simp
/-
**BoundedContinuousFunction.char_add_eq_mul** 是 Mathlib 中的一个引理，位于命名空间 `BoundedCo
ntinuousFunction`。
形式化陈述：char_add_eq_mul (x y : W) : char he hL (x + y) = char he hL x * char he hL
 y
参数：x y : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `BoundedContinuousFunction.ext`：ext (h : forall x, f x = g x) : f = g
· 使用定理 `instBoundedMul`：∀ {R : Type u_1} [inst : NonUnitalSeminormedRing R], Bou
ndedMul R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用引理 `AddChar.map_add_eq_mul`：map_add_eq_mul (ψ : AddChar A M) (x y : A) : ψ (
x + y) = ψ x * ψ y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma char_add_eq_mul (x y : W) :
    char he hL (x + y) = char he hL x * char he hL y := by
  ext
  simp [e.map_add_eq_mul]
/-
**BoundedContinuousFunction.char_neg** 是 Mathlib 中的一个引理，位于命名空间 `BoundedContinuou
sFunction`。
形式化陈述：char_neg (w : W) : char he hL (-w) = star (char he hL w)
参数：w : W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `BoundedContinuousFunction.ext`：ext (h : forall x, f x = g x) : f = g
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `RCLike.instCStarRing`：∀ {K : Type u_1} [inst : RCLike K], CStarRing K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用引理 `Circle.star_addChar`：star_addChar (x : Real) : star ((e x) : Complex) = 
e (-x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma char_neg (w : W) :
    char he hL (-w) = star (char he hL w) := by ext; simp

set_option backward.isDefEq.respectTransparency false in
/-- If `e` and `L` are non-trivial, then `char he hL w, w : W` separates points in `V`. -/
/-
**BoundedContinuousFunction.ext_of_char_eq** 是 Mathlib 中的一个定理，位于命名空间 `BoundedCon
tinuousFunction`。
形式化陈述：ext_of_char_eq (he : Continuous e) (he' : e != 1) (hL : Continuous fun p :
 V × W => L p.1 p.2) (hL' : forall v != 0, L v != 0) {v v' : V} (h : forall w, c
har he hL w v = char he hL w v') : v = v'
参数：he : Continuous e；he' : e != 1；hL : Continuous fun p : V × W => L p.1 p.2；hL'
 : forall v != 0, L v != 0；h : forall w, char he hL w v = char he hL w v'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ne_iff`：ne_iff {f g : F} : f != g ↔ exists a, f a != g a
· 使用定理 `sub_ne_zero_of_ne`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a b : 
α}, a ≠ b → a - b ≠ 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `BoundedContinuousFunction.char.congr_simp`：∀ {V : Type u_1} {W : Type u_
2} [inst : AddCommGroup V] [inst_1 : _root_.Module ℝ V] [inst_2 : TopologicalSpa
ce V]   [inst_3 : AddCommGroup …
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `div_eq_one_iff_eq`：div_eq_one_iff_eq (hb : b != 0) : a / b = 1 ↔ a = b
· 使用定理 `Circle.coe_ne_zero`：∀ (z : Circle), ↑z ≠ 0
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `Metric.unitSphere.coe_inv`：Metric.unitSphere.coe_inv [NormedDivisionRing
 𝕜] (x : sphere (0 : 𝕜) 1) : ↑x⁻¹ = (x⁻¹ : 𝕜)
· 使用引理 `AddChar.map_neg_eq_inv`：map_neg_eq_inv (ψ : AddChar A M) (a : A) : ψ (-a
) = (ψ a)⁻¹
· 使用定理 `Submonoid.coe_mul`：coe_mul (x y : S) : (↑(x * y) : M) = ↑x * ↑y
· 使用引理 `AddChar.map_add_eq_mul`：map_add_eq_mul (ψ : AddChar A M) (x y : A) : ψ (
x + y) = ψ x * ψ y
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `OneMemClass.coe_eq_one`：coe_eq_one {x : S'} : (↑x : M₁) = 1 ↔ x = 1
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
（共 85 条，此处仅展示前 30 条）

--- 原说明 ---
If `e` and `L` are non-trivial, then `char he hL w, w : W` separates points in `
V`.
-/
theorem ext_of_char_eq (he : Continuous e) (he' : e ≠ 1)
    (hL : Continuous fun p : V × W ↦ L p.1 p.2) (hL' : ∀ v ≠ 0, L v ≠ 0) {v v' : V}
    (h : ∀ w, char he hL w v = char he hL w v') :
    v = v' := by
  contrapose! h
  obtain ⟨w, hw⟩ := DFunLike.ne_iff.mp (hL' (v - v') (sub_ne_zero_of_ne h))
  obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp he'
  use (a / (L (v - v') w)) • w
  simp only [map_sub, LinearMap.sub_apply, char_apply, ne_eq]
  rw [← div_eq_one_iff_eq (Circle.coe_ne_zero _), div_eq_inv_mul, ← Metric.unitSphere.coe_inv,
    ← e.map_neg_eq_inv, ← Submonoid.coe_mul, ← e.map_add_eq_mul, OneMemClass.coe_eq_one]
  simp only [map_sub, LinearMap.sub_apply, LinearMap.zero_apply, AddChar.one_apply,
    map_smul, smul_eq_mul] at ha hw ⊢
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
  It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
  canonicalizer; a minimization would help. The original proof was: `grind` -/
  ring_nf
  field_simp
  assumption

/-- Monoid homomorphism mapping `w` to `fun v ↦ e (L v w)`. -/
/-
**BoundedContinuousFunction.charMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `BoundedCont
inuousFunction`。
形式化陈述：charMonoidHom (he : Continuous e) (hL : Continuous fun p : V × W => L p.1 
p.2) : Multiplicative W ->* (V ->ᵇ Complex) where toFun w
参数：he : Continuous e；hL : Continuous fun p : V × W => L p.1 p.2。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `BoundedContinuousFunction.char_zero_eq_one`：char_zero_eq_one : char he h
L 0 = 1
· 使用引理 `BoundedContinuousFunction.char_add_eq_mul`：char_add_eq_mul (x y : W) : c
har he hL (x + y) = char he hL x * char he hL y

--- 原说明 ---
Monoid homomorphism mapping `w` to `fun v ↦ e (L v w)`.
-/
noncomputable def charMonoidHom (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2) :
    Multiplicative W →* (V →ᵇ ℂ) where
  toFun w := char he hL w.toAdd
  map_one' := char_zero_eq_one
  map_mul' := char_add_eq_mul (he := he) (hL := hL)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**BoundedContinuousFunction.charMonoidHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `Bound
edContinuousFunction`。
形式化陈述：charMonoidHom_apply (w : Multiplicative W) (v : V) : charMonoidHom he hL w
 v = e (L v w.toAdd)
参数：w : Multiplicative W；v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma charMonoidHom_apply (w : Multiplicative W) (v : V) :
    charMonoidHom he hL w v = e (L v w.toAdd) := by simp [charMonoidHom]

/-- Algebra homomorphism mapping `w` to `fun v ↦ e (L v w)`. -/
noncomputable
/-
**BoundedContinuousFunction.charAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `BoundedContinu
ousFunction`。
形式化陈述：charAlgHom (he : Continuous e) (hL : Continuous fun p : V × W => L p.1 p.2
) : AddMonoidAlgebra Complex W ->ₐ[Complex] (V ->ᵇ Complex)
参数：he : Continuous e；hL : Continuous fun p : V × W => L p.1 p.2。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def charAlgHom (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2) :
    AddMonoidAlgebra ℂ W →ₐ[ℂ] (V →ᵇ ℂ) :=
  AddMonoidAlgebra.lift ℂ (V →ᵇ ℂ) W (charMonoidHom he hL)

@[simp]
/-
**BoundedContinuousFunction.charAlgHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `BoundedC
ontinuousFunction`。
形式化陈述：charAlgHom_apply (w : AddMonoidAlgebra Complex W) (v : V) : charAlgHom he 
hL w v = w.coeff.sum (fun a z => z • (e (L v a) : Complex))
参数：w : AddMonoidAlgebra Complex W；v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `instBoundedMul`：∀ {R : Type u_1} [inst : NonUnitalSeminormedRing R], Bou
ndedMul R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.lift_apply`：lift_apply (F : Multiplicative M ->* A) (f 
: R[M]) : lift R A M F f = f.coeff.sum fun a b => b • F (.ofAdd a)
· 使用引理 `BoundedContinuousFunction.char_zero_eq_one`：char_zero_eq_one : char he h
L 0 = 1
· 使用引理 `BoundedContinuousFunction.char_add_eq_mul`：char_add_eq_mul (x y : W) : c
har he hL (x + y) = char he hL x * char he hL y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `BoundedContinuousFunction.coe_sum`：∀ {α : Type u} {R : Type u_2} [inst :
 TopologicalSpace α] [inst_1 : PseudoMetricSpace R] {ι : Type u_3} (s : Finset ι
)   [inst_2 : AddCommMo…
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma charAlgHom_apply (w : AddMonoidAlgebra ℂ W) (v : V) :
    charAlgHom he hL w v = w.coeff.sum (fun a z ↦ z • (e (L v a) : ℂ)) := by
  simp [charAlgHom, charMonoidHom, char, AddMonoidAlgebra.lift_apply]
  simp [Finsupp.sum]

set_option backward.isDefEq.respectTransparency false in
/-- The family of `ℂ`-linear combinations of `char he hL w, w : W`, is closed under `star`. -/
/-
**BoundedContinuousFunction.star_mem_range_charAlgHom** 是 Mathlib 中的一个引理，位于命名空间 
`BoundedContinuousFunction`。
形式化陈述：star_mem_range_charAlgHom (he : Continuous e) (hL : Continuous fun p : V ×
 W => L p.1 p.2) {x : V ->ᵇ Complex} (hx : x in (charAlgHom he hL).range) : star
 x in (charAlgHom he hL).range
参数：he : Continuous e；hL : Continuous fun p : V × W => L p.1 p.2；hx : x in (charA
lgHom he hL).range。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `instBoundedMul`：∀ {R : Type u_1} [inst : NonUnitalSeminormedRing R], Bou
ndedMul R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `RCLike.instCStarRing`：∀ {K : Type u_1} [inst : RCLike K], CStarRing K
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `BoundedContinuousFunction.ext`：ext (h : forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `AddMonoidHom.map_zero`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M
] [inst_1 : AddZero N] (f : M →+ N), f 0 = 0
· 使用引理 `BoundedContinuousFunction.charAlgHom_apply`：charAlgHom_apply (w : AddMon
oidAlgebra Complex W) (v : V) : charAlgHom he hL w v = w.coeff.sum (fun a z => z
 • (e (L v a) : Complex))
· 使用定理 `Finsupp.sum_embDomain`：∀ {α : Type u_1} {β : Type u_7} {M : Type u_8} {N
 : Type u_10} [inst : Zero M] [inst_1 : AddCommMonoid N] {v : α →₀ M}   {f : α ↪
 β} {g : β …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
The family of `ℂ`-linear combinations of `char he hL w, w : W`, is closed under 
`star`.
-/
lemma star_mem_range_charAlgHom (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    {x : V →ᵇ ℂ} (hx : x ∈ (charAlgHom he hL).range) :
    star x ∈ (charAlgHom he hL).range := by
  simp only [AlgHom.mem_range] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  let z := y.map (starRingEnd _).toAddMonoidHom
  let f : W ↪ W := ⟨fun x ↦ -x, (fun _ _ ↦ neg_inj.mp)⟩
  refine ⟨.ofCoeff <| z.coeff.embDomain f, ?_⟩
  ext
  simp [charAlgHom_apply, Finsupp.sum_embDomain, z, Finsupp.sum_mapRange_index, f]

/-- The star-subalgebra of polynomials. -/
noncomputable
/-
**BoundedContinuousFunction.charPoly** 是 Mathlib 中的一个定义，位于命名空间 `BoundedContinuou
sFunction`。
形式化陈述：charPoly (he : Continuous e) (hL : Continuous fun p : V × W => L p.1 p.2) 
: StarSubalgebra Complex (V ->ᵇ Complex) where toSubalgebra
参数：he : Continuous e；hL : Continuous fun p : V × W => L p.1 p.2。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `BoundedContinuousFunction.star_mem_range_charAlgHom`：star_mem_range_char
AlgHom (he : Continuous e) (hL : Continuous fun p : V × W => L p.1 p.2) {x : V -
>ᵇ Complex} (hx : x in (charAlgHom he hL)…
-/
def charPoly (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2) :
    StarSubalgebra ℂ (V →ᵇ ℂ) where
  toSubalgebra := (charAlgHom he hL).range
  star_mem' hx := star_mem_range_charAlgHom he hL hx
/-
**BoundedContinuousFunction.mem_charPoly** 是 Mathlib 中的一个引理，位于命名空间 `BoundedConti
nuousFunction`。
形式化陈述：mem_charPoly (f : V ->ᵇ Complex) : f in charPoly he hL ↔ exists w : AddMon
oidAlgebra Complex W, f = fun x => w.coeff.sum (fun a z => z * (e (L x a) : Comp
lex))
参数：f : V ->ᵇ Complex。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `instBoundedMul`：∀ {R : Type u_1} [inst : NonUnitalSeminormedRing R], Bou
ndedMul R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `RCLike.instCStarRing`：∀ {K : Type u_1} [inst : RCLike K], CStarRing K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `BoundedContinuousFunction.charAlgHom_apply`：charAlgHom_apply (w : AddMon
oidAlgebra Complex W) (v : V) : charAlgHom he hL w v = w.coeff.sum (fun a z => z
 • (e (L v a) : Complex))
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_charPoly (f : V →ᵇ ℂ) :
    f ∈ charPoly he hL
      ↔ ∃ w : AddMonoidAlgebra ℂ W, f = fun x ↦ w.coeff.sum (fun a z ↦ z * (e (L x a) : ℂ)) := by
  change f ∈ (charAlgHom he hL).range ↔ _
  simp [BoundedContinuousFunction.ext_iff, funext_iff, eq_comm]
/-
**BoundedContinuousFunction.char_mem_charPoly** 是 Mathlib 中的一个引理，位于命名空间 `Bounded
ContinuousFunction`。
形式化陈述：char_mem_charPoly (w : W) : char he hL w in charPoly he hL
参数：w : W。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `BoundedContinuousFunction.ext`：ext (h : forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instBoundedMul`：∀ {R : Type u_1} [inst : NonUnitalSeminormedRing R], Bou
ndedMul R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用引理 `BoundedContinuousFunction.charAlgHom_apply`：charAlgHom_apply (w : AddMon
oidAlgebra Complex W) (v : V) : charAlgHom he hL w v = w.coeff.sum (fun a z => z
 • (e (L v a) : Complex))
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma char_mem_charPoly (w : W) : char he hL w ∈ charPoly he hL := ⟨.single w 1, by ext; simp⟩

/-- The family `charPoly he hL w, w : W` separates points in `V`. -/
/-
**BoundedContinuousFunction.separatesPoints_charPoly** 是 Mathlib 中的一个引理，位于命名空间 `
BoundedContinuousFunction`。
形式化陈述：separatesPoints_charPoly (he : Continuous e) (he' : e != 1) (hL : Continuo
us fun p : V × W => L p.1 p.2) (hL' : forall v != 0, L v != 0) : ((charPoly he h
L).map (toContinuousMapStarₐ Complex)).SeparatesPoints
参数：he : Continuous e；he' : e != 1；hL : Continuous fun p : V × W => L p.1 p.2；hL'
 : forall v != 0, L v != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `ContinuousMap.instStarModule`：∀ {R : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2 : Star 
R] [inst_3 : Star …
· 使用定理 `instBoundedMul`：∀ {R : Type u_1} [inst : NonUnitalSeminormedRing R], Bou
ndedMul R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `RCLike.instCStarRing`：∀ {K : Type u_1} [inst : RCLike K], CStarRing K
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `BoundedContinuousFunction.ext_of_char_eq`：ext_of_char_eq (he : Continuou
s e) (he' : e != 1) (hL : Continuous fun p : V × W => L p.1 p.2) (hL' : forall v
 != 0, L v != 0) {v v' : V} (h…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `BoundedContinuousFunction.char_mem_charPoly`：char_mem_charPoly (w : W) :
 char he hL w in charPoly he hL

--- 原说明 ---
The family `charPoly he hL w, w : W` separates points in `V`.
-/
lemma separatesPoints_charPoly (he : Continuous e) (he' : e ≠ 1)
    (hL : Continuous fun p : V × W ↦ L p.1 p.2) (hL' : ∀ v ≠ 0, L v ≠ 0) :
    ((charPoly he hL).map (toContinuousMapStarₐ ℂ)).SeparatesPoints := by
  intro v v' hvv'
  obtain ⟨w, hw⟩ : ∃ w, char he hL w v ≠ char he hL w v' := by
    contrapose! hvv'
    exact ext_of_char_eq he he' hL hL' hvv'
  use char he hL w
  simp only [StarSubalgebra.coe_toSubalgebra, StarSubalgebra.coe_map, Set.mem_image,
    SetLike.mem_coe, exists_exists_and_eq_and, ne_eq]
  exact ⟨⟨char he hL w, char_mem_charPoly w, rfl⟩, hw⟩

end BoundedContinuousFunction

