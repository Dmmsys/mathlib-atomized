/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Topology.Algebra.ContinuousAffineMap
public import Mathlib.Topology.MetricSpace.TransferInstance
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Group.AddTorsor

/-!
# Norm on the continuous affine maps between normed vector spaces.

We define a norm on the space of continuous affine maps between normed vector spaces by defining the
norm of `f : V →ᴬ[𝕜] W` to be `‖f‖ = max ‖f 0‖ ‖f.cont_linear‖`. This is chosen so that we have a
linear isometry: `(V →ᴬ[𝕜] W) ≃ₗᵢ[𝕜] W × (V →L[𝕜] W)`.

The abstract picture is that for an affine space `P` modelled on a vector space `V`, together with
a vector space `W`, there is an exact sequence of `𝕜`-modules: `0 → C → A → L → 0` where `C`, `A`
are the spaces of constant and affine maps `P → W` and `L` is the space of linear maps `V → W`.

Any choice of a base point in `P` corresponds to a splitting of this sequence so in particular if we
take `P = V`, using `0 : V` as the base point provides a splitting, and we prove this is an
isometric decomposition.

On the other hand, choosing a base point breaks the affine invariance so the norm fails to be
submultiplicative: for a composition of maps, we have only `‖f.comp g‖ ≤ ‖f‖ * ‖g‖ + ‖f 0‖`.

## Main definitions:

* `ContinuousAffineMap.hasNorm`
* `ContinuousAffineMap.norm_comp_le`
* `ContinuousAffineMap.toConstProdContinuousLinearMap`

-/

@[expose] public section


namespace ContinuousAffineMap

variable {𝕜 R V W W₂ Q : Type*}

section Seminormed

variable [SeminormedAddCommGroup V] [SeminormedAddCommGroup W] [SeminormedAddCommGroup W₂]
variable [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 V] [NormedSpace 𝕜 W] [NormedSpace 𝕜 W₂]
variable [PseudoMetricSpace Q] [NormedAddTorsor W Q]

variable (f : V →ᴬ[𝕜] W)

/-- Note that unlike the operator norm for linear maps, this norm is _not_ submultiplicative:
we do _not_ necessarily have `‖f.comp g‖ ≤ ‖f‖ * ‖g‖`. See `norm_comp_le` for what we can say. -/
/-
**ContinuousAffineMap.hasNorm** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAffineMap`。
形式化陈述：hasNorm : Norm (V ->ᴬ[𝕜] W)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note that unlike the operator norm for linear maps, this norm is _not_ submultip
licative:
we do _not_ necessarily have `‖f.comp g‖ ≤ ‖f‖ * ‖g‖`. See `norm_comp_le` for wh
at we can say.
-/
noncomputable instance hasNorm : Norm (V →ᴬ[𝕜] W) :=
  ⟨fun f => max ‖f 0‖ ‖f.contLinear‖⟩
/-
**ContinuousAffineMap.norm_def** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineMap`。
形式化陈述：norm_def : ‖f‖ = max ‖f 0‖ ‖f.contLinear‖
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_def : ‖f‖ = max ‖f 0‖ ‖f.contLinear‖ :=
  rfl
/-
**ContinuousAffineMap.norm_contLinear_le** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAf
fineMap`。
形式化陈述：norm_contLinear_le : ‖f.contLinear‖ <= ‖f‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
-/
theorem norm_contLinear_le : ‖f.contLinear‖ ≤ ‖f‖ :=
  le_max_right _ _
/-
**ContinuousAffineMap.norm_image_zero_le** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAf
fineMap`。
形式化陈述：norm_image_zero_le : ‖f 0‖ <= ‖f‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
-/
theorem norm_image_zero_le : ‖f 0‖ ≤ ‖f‖ :=
  le_max_left _ _

@[simp]
/-
**ContinuousAffineMap.norm_eq** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineMap`。
形式化陈述：norm_eq (h : f 0 = 0) : ‖f‖ = ‖f.contLinear‖
参数：h : f 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAffineMap.norm_def`：norm_def : ‖f‖ = max ‖f 0‖ ‖f.contLinear‖
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem norm_eq (h : f 0 = 0) : ‖f‖ = ‖f.contLinear‖ :=
  calc
    ‖f‖ = max ‖f 0‖ ‖f.contLinear‖ := by rw [norm_def]
    _ = max 0 ‖f.contLinear‖ := by rw [h, norm_zero]
    _ = ‖f.contLinear‖ := max_eq_right (norm_nonneg _)
/-
**ContinuousAffineMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PseudoMetricSpace (V →ᴬ[𝕜] Q) :=
  (decompEquiv 𝕜 V Q).pseudometricSpace
/-
**ContinuousAffineMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : SeminormedAddCommGroup (V →ᴬ[𝕜] W) where
  dist_eq _ _ := dist_eq_norm_neg_add (E := W × (V →L[𝕜] W)) _ _
/-
**ContinuousAffineMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : NormedAddTorsor (V →ᴬ[𝕜] W) (V →ᴬ[𝕜] Q) where
  dist_eq_norm' _ _ := dist_eq_norm_vsub (P := Q × (V →L[𝕜] W)) _ _ _
/-
**ContinuousAffineMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : NormedSpace 𝕜 (V →ᴬ[𝕜] W) where
  norm_smul_le t f := norm_smul_le t (f 0, f.contLinear)
/-
**ContinuousAffineMap.norm_comp_le** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAffineMa
p`。
形式化陈述：norm_comp_le (g : W₂ ->ᴬ[𝕜] V) : ‖f.comp g‖ <= ‖f‖ * ‖g‖ + ‖f 0‖
参数：g : W₂ ->ᴬ[𝕜] V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAffineMap.norm_def`：norm_def : ‖f‖ = max ‖f 0‖ ‖f.contLinear‖
· 使用定理 `max_le_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, max a b ≤
 c ↔ a ≤ c ∧ b ≤ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instIsTopologicalAddTorsor`：∀ {G : Type u_1} [inst : AddGroup G] [inst_1
 : TopologicalSpace G] [IsTopologicalAddGroup G], IsTopologicalAddTorsor G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousAffineMap.decomp`：∀ {R : Type u_1} {V : Type u_2} {W : Type u_
3} [inst : Ring R] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module R V]   [ins
t_3 : Topologica…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `norm_add_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a + b‖ ≤ ‖a‖ + ‖b‖
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `ContinuousAffineMap.norm_contLinear_le`：norm_contLinear_le : ‖f.contLine
ar‖ <= ‖f‖
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `ContinuousAffineMap.norm_image_zero_le`：norm_image_zero_le : ‖f 0‖ <= ‖f
‖
（共 37 条，此处仅展示前 30 条）
-/
theorem norm_comp_le (g : W₂ →ᴬ[𝕜] V) : ‖f.comp g‖ ≤ ‖f‖ * ‖g‖ + ‖f 0‖ := by
  rw [norm_def, max_le_iff]
  constructor
  · calc
      ‖f.comp g 0‖ = ‖f (g 0)‖ := by simp
      _ = ‖f.contLinear (g 0) + f 0‖ := by rw [f.decomp]; simp
      _ ≤ ‖f.contLinear‖ * ‖g 0‖ + ‖f 0‖ := by grw [norm_add_le, f.contLinear.le_opNorm]
      _ ≤ ‖f‖ * ‖g‖ + ‖f 0‖ := by grw [f.norm_contLinear_le, g.norm_image_zero_le]
  · calc
      ‖(f.comp g).contLinear‖ ≤ ‖f.contLinear‖ * ‖g.contLinear‖ :=
        (g.comp_contLinear f).symm ▸ f.contLinear.opNorm_comp_le _
      _ ≤ ‖f‖ * ‖g‖ := by grw [f.norm_contLinear_le, g.norm_contLinear_le]
      _ ≤ ‖f‖ * ‖g‖ + ‖f 0‖ := by rw [le_add_iff_nonneg_right]; apply norm_nonneg

variable (𝕜 R V W) [Ring R] [Module R W] [ContinuousConstSMul R W] [SMulCommClass 𝕜 R W]

/-- The space of affine maps between two normed spaces is linearly isometric to the product of the
codomain with the space of linear maps, by taking the value of the affine map at `(0 : V)` and the
linear part. -/
/-
**ContinuousAffineMap.decompLinearIsometryEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Conti
nuousAffineMap`。
形式化陈述：decompLinearIsometryEquiv : (V ->ᴬ[𝕜] W) ≃ₗᵢ[R] W × (V ->L[𝕜] W) where __
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
The space of affine maps between two normed spaces is linearly isometric to the 
product of the
codomain with the space of linear maps, by taking the value of the affine map at
 `(0 : V)` and the
linear part.
-/
def decompLinearIsometryEquiv : (V →ᴬ[𝕜] W) ≃ₗᵢ[R] W × (V →L[𝕜] W) where
  __ := decompLinearEquiv 𝕜 R V W
  norm_map' _ := rfl

@[simp]
/-
**ContinuousAffineMap.fst_decompLinearIsometryEquiv** 是 Mathlib 中的一个定理，位于命名空间 `C
ontinuousAffineMap`。
形式化陈述：fst_decompLinearIsometryEquiv (f : V ->ᴬ[𝕜] W) : (decompLinearIsometryEqui
v 𝕜 R V W f).1 = f 0
参数：f : V ->ᴬ[𝕜] W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
theorem fst_decompLinearIsometryEquiv (f : V →ᴬ[𝕜] W) :
    (decompLinearIsometryEquiv 𝕜 R V W f).1 = f 0 :=
  rfl

@[simp]
/-
**ContinuousAffineMap.snd_decompLinearIsometryEquiv** 是 Mathlib 中的一个定理，位于命名空间 `C
ontinuousAffineMap`。
形式化陈述：snd_decompLinearIsometryEquiv (f : V ->ᴬ[𝕜] W) : (decompLinearIsometryEqui
v 𝕜 R V W f).2 = f.contLinear
参数：f : V ->ᴬ[𝕜] W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
theorem snd_decompLinearIsometryEquiv (f : V →ᴬ[𝕜] W) :
    (decompLinearIsometryEquiv 𝕜 R V W f).2 = f.contLinear :=
  rfl

@[simp]
/-
**ContinuousAffineMap.decompLinearIsometryEquiv_symm_apply** 是 Mathlib 中的一个定理，位于
命名空间 `ContinuousAffineMap`。
形式化陈述：decompLinearIsometryEquiv_symm_apply (p : W × (V ->L[𝕜] W)) (x : V) : (dec
ompLinearIsometryEquiv 𝕜 R V W).symm p x = p.2 x + p.1
参数：p : W × (V ->L[𝕜] W)；x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem decompLinearIsometryEquiv_symm_apply (p : W × (V →L[𝕜] W)) (x : V) :
    (decompLinearIsometryEquiv 𝕜 R V W).symm p x = p.2 x + p.1 :=
  rfl

@[simp]
/-
**ContinuousAffineMap.decompLinearIsometryEquiv_symm_contLinear** 是 Mathlib 中的一个
定理，位于命名空间 `ContinuousAffineMap`。
形式化陈述：decompLinearIsometryEquiv_symm_contLinear (p : W × (V ->L[𝕜] W)) : ((decom
pLinearIsometryEquiv 𝕜 R V W).symm p).contLinear = p.2
参数：p : W × (V ->L[𝕜] W)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAffineMap.decompLinearIsometryEquiv.eq_1`：∀ (𝕜 : Type u_1) (R 
: Type u_2) (V : Type u_3) (W : Type u_4) [inst : SeminormedAddCommGroup V]   [i
nst_1 : SeminormedAddCommGroup W] [inst_…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearIsometryEquiv.coe_symm_toLinearEquiv`：coe_symm_toLinearEquiv : ⇑e.
toLinearEquiv.symm = e.symm
· 使用定理 `instIsTopologicalAddTorsor`：∀ {G : Type u_1} [inst : AddGroup G] [inst_1
 : TopologicalSpace G] [IsTopologicalAddGroup G], IsTopologicalAddTorsor G
· 使用定理 `ContinuousAffineMap.decompLinearEquiv_symm_contLinear`：decompLinearEquiv
_symm_contLinear (p : W × (V ->L[R] W)) : ((decompLinearEquiv R S V W).symm p).c
ontLinear = p.2
-/
theorem decompLinearIsometryEquiv_symm_contLinear (p : W × (V →L[𝕜] W)) :
    ((decompLinearIsometryEquiv 𝕜 R V W).symm p).contLinear = p.2 := by
  rw [decompLinearIsometryEquiv, ← LinearIsometryEquiv.coe_symm_toLinearEquiv,
    decompLinearEquiv_symm_contLinear]

@[deprecated decompLinearIsometryEquiv (since := "2026-03-03"),
  inherit_doc decompLinearIsometryEquiv]
/-
**ContinuousAffineMap.toConstProdContinuousLinearMap** 是 Mathlib 中的一个缩写定义，位于命名空间
 `ContinuousAffineMap`。
形式化陈述：toConstProdContinuousLinearMap
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev toConstProdContinuousLinearMap := decompLinearIsometryEquiv 𝕜 𝕜 V W

@[deprecated fst_decompLinearIsometryEquiv (since := "2026-03-03")]
/-
**ContinuousAffineMap.toConstProdContinuousLinearMap_fst** 是 Mathlib 中的一个定理，位于命名
空间 `ContinuousAffineMap`。
形式化陈述：toConstProdContinuousLinearMap_fst (f : V ->ᴬ[𝕜] W) : (toConstProdContinuo
usLinearMap 𝕜 V W f).fst = f 0
参数：f : V ->ᴬ[𝕜] W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
theorem toConstProdContinuousLinearMap_fst (f : V →ᴬ[𝕜] W) :
    (toConstProdContinuousLinearMap 𝕜 V W f).fst = f 0 :=
  rfl

@[deprecated snd_decompLinearIsometryEquiv (since := "2026-03-03")]
/-
**ContinuousAffineMap.toConstProdContinuousLinearMap_snd** 是 Mathlib 中的一个定理，位于命名
空间 `ContinuousAffineMap`。
形式化陈述：toConstProdContinuousLinearMap_snd (f : V ->ᴬ[𝕜] W) : (toConstProdContinuo
usLinearMap 𝕜 V W f).snd = f.contLinear
参数：f : V ->ᴬ[𝕜] W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
-/
theorem toConstProdContinuousLinearMap_snd (f : V →ᴬ[𝕜] W) :
    (toConstProdContinuousLinearMap 𝕜 V W f).snd = f.contLinear :=
  rfl

end Seminormed

section Normed

variable [NormedAddCommGroup V] [NormedAddCommGroup W]
variable [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 V] [NormedSpace 𝕜 W]
variable [MetricSpace Q] [NormedAddTorsor W Q]

/-
**ContinuousAffineMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : MetricSpace (V →ᴬ[𝕜] Q) :=
  (decompEquiv 𝕜 V Q).metricSpace
/-
**ContinuousAffineMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousAffineMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : NormedAddCommGroup (V →ᴬ[𝕜] W) where
  __ : SeminormedAddCommGroup (V →ᴬ[𝕜] W) := inferInstance
  __ : MetricSpace (V →ᴬ[𝕜] W) := inferInstance

end Normed

end ContinuousAffineMap

