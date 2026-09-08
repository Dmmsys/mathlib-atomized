/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Topology.ContinuousMap.Units

/-! # Mapping `C(X, ℝ)` to `C(X, 𝕜)` and back

This file contains the definitions for `ContinuousMap.realToRCLike` and
`ContinuousMap.rclikeToReal`, which map `C(X, ℝ)` to `C(X, 𝕜)` and back for any `RCLike 𝕜`. -/

@[expose] public section

namespace ContinuousMap
variable {X : Type*} (𝕜 : Type*) [TopologicalSpace X] [RCLike 𝕜]

/-- Lifting `C(X, ℝ)` to `C(X, 𝕜)` using `RCLike.ofReal`. -/
/-
**ContinuousMap.realToRCLike** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：{X : Type u_1} → (𝕜 : Type u_2) → [inst : TopologicalSpace X] → [inst_1 : 
RCLike 𝕜] → C(X, ℝ) → C(X, 𝕜)
参数：𝕜 : Type u_2；X, ℝ；X, 𝕜。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lifting `C(X, ℝ)` to `C(X, 𝕜)` using `RCLike.ofReal`.
-/
@[simps] def realToRCLike (f : C(X, ℝ)) : C(X, 𝕜) where toFun x := RCLike.ofReal (f x)
/-
**ContinuousMap.isSelfAdjoint_realToRCLike** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
Map`。
形式化陈述：∀ {X : Type u_1} (𝕜 : Type u_2) [inst : TopologicalSpace X] [inst_1 : RCLi
ke 𝕜] {f : C(X, ℝ)},   IsSelfAdjoint (ContinuousMap.realToRCLike 𝕜 f)
参数：𝕜 : Type u_2；X, ℝ；ContinuousMap.realToRCLike 𝕜 f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.realToRCLike_apply`：∀ {X : Type u_1} (𝕜 : Type u_2) [inst 
: TopologicalSpace X] [inst_1 : RCLike 𝕜] (f : C(X, ℝ)) (x : X),   (ContinuousMa
p.realToRCLike 𝕜 f) x …
· 使用定理 `RCLike.conj_ofReal`：conj_ofReal (r : Real) : conj (r : K) = (r : K)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Lifting `C(X, ℝ)` to `C(X, 𝕜)` using `RCLike.ofReal`.
-/
@[simp, grind .] lemma isSelfAdjoint_realToRCLike {f : C(X, ℝ)} :
    IsSelfAdjoint (f.realToRCLike 𝕜) := by ext; simp
/-
**ContinuousMap.spectrum_realToRCLike** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：∀ {X : Type u_1} (𝕜 : Type u_2) [inst : TopologicalSpace X] [inst_1 : RCLi
ke 𝕜] (f : C(X, ℝ)),   spectrum ℝ (ContinuousMap.realToRCLike 𝕜 f) = spectrum ℝ 
f
参数：𝕜 : Type u_2；f : C(X, ℝ)；ContinuousMap.realToRCLike 𝕜 f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `algebraMap_apply`：algebraMap_apply (k : R) (a : α) : algebraMap R C(α, A
) k a = k • (1 : A)
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `ContinuousMap.realToRCLike_apply`：∀ {X : Type u_1} (𝕜 : Type u_2) [inst 
: TopologicalSpace X] [inst_1 : RCLike 𝕜] (f : C(X, ℝ)) (x : X),   (ContinuousMa
p.realToRCLike 𝕜 f) x …
· 使用定理 `RCLike.ext_iff`：ext_iff {z w : K} : z = w ↔ re z = re w ∧ im z = im w
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `RCLike.ofReal_im`：ofReal_im : forall r : Real, im (r : K) = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma spectrum_realToRCLike (f : C(X, ℝ)) :
    spectrum ℝ (f.realToRCLike 𝕜) = spectrum ℝ f := by
  ext; simp [spectrum.mem_iff, isUnit_iff_forall_isUnit, RCLike.ext_iff (K := 𝕜), Algebra.smul_def]

open ComplexOrder

set_option backward.isDefEq.respectTransparency.types false in
variable (X) in
/-- `ContinuousMap.realToRCLike` as an order embedding. -/
/-
**ContinuousMap.realToRCLikeOrderEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Continuous
Map`。
形式化陈述：(X : Type u_1) → (𝕜 : Type u_2) → [inst : TopologicalSpace X] → [inst_1 : 
RCLike 𝕜] → C(X, ℝ) ↪o C(X, 𝕜)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContinuousMap.realToRCLike` as an order embedding.
-/
@[simps] def realToRCLikeOrderEmbedding : C(X, ℝ) ↪o C(X, 𝕜) where
  toFun := realToRCLike 𝕜
  inj' f g hfg := by ext x; simpa using congr($hfg x)
  map_rel_iff' := by simp [le_def]

variable (X) in
/-
**ContinuousMap.realToRCLike_monotone** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：realToRCLike_monotone : Monotone (realToRCLike (X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorde
r α] [inst_1 : Preorder β] (f : α ↪o β), Monotone ⇑f
-/
lemma realToRCLike_monotone : Monotone (realToRCLike (X := X) 𝕜) :=
  realToRCLikeOrderEmbedding X 𝕜 |>.monotone

variable (X) in
/-
**ContinuousMap.realToRCLike_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap
`。
形式化陈述：realToRCLike_strictMono : StrictMono (realToRCLike (X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preor
der α] [inst_1 : Preorder β] (f : α ↪o β), StrictMono ⇑f
-/
lemma realToRCLike_strictMono : StrictMono (realToRCLike (X := X) 𝕜) :=
  realToRCLikeOrderEmbedding X 𝕜 |>.strictMono

variable (X) in
/-
**ContinuousMap.realToRCLike_injective** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`
。
形式化陈述：∀ (X : Type u_1) (𝕜 : Type u_2) [inst : TopologicalSpace X] [inst_1 : RCLi
ke 𝕜],   Function.Injective (ContinuousMap.realToRCLike 𝕜)
参数：X : Type u_1；𝕜 : Type u_2；ContinuousMap.realToRCLike 𝕜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.injective`：injective (f : r ↪r s) : Injective f
-/
@[simp] lemma realToRCLike_injective : (realToRCLike (X := X) 𝕜).Injective :=
  realToRCLikeOrderEmbedding X 𝕜 |>.injective
/-
**ContinuousMap.realToRCLike_inj** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：∀ {X : Type u_1} (𝕜 : Type u_2) [inst : TopologicalSpace X] [inst_1 : RCLi
ke 𝕜] {f g : C(X, ℝ)},   ContinuousMap.realToRCLike 𝕜 f = ContinuousMap.realToRC
Like 𝕜 g ↔ f = g
参数：𝕜 : Type u_2；X, ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.eq_iff_eq`：eq_iff_eq {a b} : f a = f b ↔ a = b
-/
@[simp] lemma realToRCLike_inj {f g : C(X, ℝ)} :
    realToRCLike 𝕜 f = realToRCLike 𝕜 g ↔ f = g :=
  realToRCLikeOrderEmbedding X 𝕜 |>.eq_iff_eq
/-
**ContinuousMap.realToRCLike_le_realToRCLike_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cont
inuousMap`。
形式化陈述：∀ {X : Type u_1} (𝕜 : Type u_2) [inst : TopologicalSpace X] [inst_1 : RCLi
ke 𝕜] {f g : C(X, ℝ)},   ContinuousMap.realToRCLike 𝕜 f ≤ ContinuousMap.realToRC
Like 𝕜 g ↔ f ≤ g
参数：𝕜 : Type u_2；X, ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.le_iff_le`：le_iff_le {a b} : f a <= f b ↔ a <= b
-/
@[simp] lemma realToRCLike_le_realToRCLike_iff {f g : C(X, ℝ)} :
    realToRCLike 𝕜 f ≤ realToRCLike 𝕜 g ↔ f ≤ g :=
  realToRCLikeOrderEmbedding X 𝕜 |>.le_iff_le
/-
**ContinuousMap.realToRCLike_lt_realToRCLike_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cont
inuousMap`。
形式化陈述：∀ {X : Type u_1} (𝕜 : Type u_2) [inst : TopologicalSpace X] [inst_1 : RCLi
ke 𝕜] {f g : C(X, ℝ)},   ContinuousMap.realToRCLike 𝕜 f < ContinuousMap.realToRC
Like 𝕜 g ↔ f < g
参数：𝕜 : Type u_2；X, ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.lt_iff_lt`：lt_iff_lt {a b} : f a < f b ↔ a < b
-/
@[simp] lemma realToRCLike_lt_realToRCLike_iff {f g : C(X, ℝ)} :
    realToRCLike 𝕜 f < realToRCLike 𝕜 g ↔ f < g :=
  realToRCLikeOrderEmbedding X 𝕜 |>.lt_iff_lt

variable (X) in
/-
**ContinuousMap.isometry_realToRCLike** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：∀ (X : Type u_1) (𝕜 : Type u_2) [inst : TopologicalSpace X] [inst_1 : RCLi
ke 𝕜] [inst_2 : CompactSpace X],   Isometry (ContinuousMap.realToRCLike 𝕜)
参数：X : Type u_1；𝕜 : Type u_2；ContinuousMap.realToRCLike 𝕜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.of_dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpa
ce α] [inst_1 : PseudoMetricSpace β] {f : α → β},   (∀ (x y : α), dist (f x) (f 
y) = dist…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `ContinuousMap.norm_eq_iSup_norm`：norm_eq_iSup_norm : ‖f‖ = ⨆ x : α, ‖f x
‖
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousMap.realToRCLike_apply`：∀ {X : Type u_1} (𝕜 : Type u_2) [inst 
: TopologicalSpace X] [inst_1 : RCLike 𝕜] (f : C(X, ℝ)) (x : X),   (ContinuousMa
p.realToRCLike 𝕜 f) x …
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
· 使用定理 `norm_algebraMap'`：norm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraM
ap 𝕜 𝕜' x‖ = ‖x‖
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem isometry_realToRCLike [CompactSpace X] : Isometry (realToRCLike 𝕜 (X := X)) :=
  .of_dist_eq fun f g ↦ by simp [dist_eq_norm, norm_eq_iSup_norm, ← map_sub]

variable (X) in
/-
**ContinuousMap.continuous_realToRCLike** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap
`。
形式化陈述：∀ (X : Type u_1) (𝕜 : Type u_2) [inst : TopologicalSpace X] [inst_1 : RCLi
ke 𝕜],   Continuous (ContinuousMap.realToRCLike 𝕜)
参数：X : Type u_1；𝕜 : Type u_2；ContinuousMap.realToRCLike 𝕜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.continuous_postcomp`：continuous_postcomp (g : C(Y, Z)) : C
ontinuous (ContinuousMap.comp g : C(X, Y) -> C(X, Z))
· 使用定理 `continuous_algebraMap`：continuous_algebraMap [ContinuousSMul R A] : Cont
inuous (algebraMap R A)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
@[simp, fun_prop] lemma continuous_realToRCLike : Continuous (realToRCLike 𝕜 (X := X)) :=
  continuous_postcomp { toFun x := RCLike.ofReal x }

variable (X) in
/-- `ContinuousMap.realToRCLike` as a ⋆-algebra map. -/
/-
**ContinuousMap.realToRCLikeStarAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`
。
形式化陈述：realToRCLikeStarAlgHom : C(X, Real) ->⋆ₐ[Real] C(X, 𝕜)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `RCLike.continuous_ofReal`：continuous_ofReal : Continuous (ofReal : Real 
-> K)

--- 原说明 ---
`ContinuousMap.realToRCLike` as a ⋆-algebra map.
-/
noncomputable def realToRCLikeStarAlgHom : C(X, ℝ) →⋆ₐ[ℝ] C(X, 𝕜) :=
  compStarAlgHom X (RCLike.ofRealStarAlgHom 𝕜) RCLike.continuous_ofReal
/-
**ContinuousMap.realToRCLikeStarAlgHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Continuo
usMap`。
形式化陈述：∀ {X : Type u_1} (𝕜 : Type u_2) [inst : TopologicalSpace X] [inst_1 : RCLi
ke 𝕜] (f : C(X, ℝ)),   (ContinuousMap.realToRCLikeStarAlgHom X 𝕜) f = Continuous
Map.realToRCLike 𝕜 f
参数：𝕜 : Type u_2；f : C(X, ℝ)；ContinuousMap.realToRCLikeStarAlgHom X 𝕜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
-/
@[simp] lemma realToRCLikeStarAlgHom_apply (f : C(X, ℝ)) :
    realToRCLikeStarAlgHom X 𝕜 f = f.realToRCLike 𝕜 := rfl
/-
**ContinuousMap.realToRCLike_star** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：realToRCLike_star (f : C(X, Real)) : (star f).realToRCLike 𝕜 = star (f.rea
lToRCLike 𝕜)
参数：f : C(X, Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarHomClass.map_star`：∀ {F : Type u_1} {R : outParam (Type u_2)} {S : o
utParam (Type u_3)} {inst : Star R} {inst_1 : Star S}   {inst_2 : FunLike F R S}
 [self : St…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `StarAlgHom.instStarHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u
_4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst
_3 : Star A] [ins…
-/
lemma realToRCLike_star (f : C(X, ℝ)) : (star f).realToRCLike 𝕜 = star (f.realToRCLike 𝕜) :=
  map_star (realToRCLikeStarAlgHom X 𝕜) f
/-
**ContinuousMap.realToRCLike_mul** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：∀ {X : Type u_1} (𝕜 : Type u_2) [inst : TopologicalSpace X] [inst_1 : RCLi
ke 𝕜] (f g : C(X, ℝ)),   ContinuousMap.realToRCLike 𝕜 (f * g) = ContinuousMap.re
alToRCLike 𝕜 f * ContinuousMap.realToRCLike 𝕜 g
参数：𝕜 : Type u_2；f g : C(X, ℝ)；f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…
-/
@[simp] lemma realToRCLike_mul (f g : C(X, ℝ)) :
    (f * g).realToRCLike 𝕜 = f.realToRCLike 𝕜 * g.realToRCLike 𝕜 :=
  map_mul (realToRCLikeStarAlgHom X 𝕜) f g

variable {𝕜} in
/-- Mapping `C(X, 𝕜)` to `C(X, ℝ)` using `RCLike.re`. -/
/-
**ContinuousMap.rclikeToReal** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：{X : Type u_1} → {𝕜 : Type u_2} → [inst : TopologicalSpace X] → [inst_1 : 
RCLike 𝕜] → C(X, 𝕜) → C(X, ℝ)
参数：X, 𝕜；X, ℝ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Mapping `C(X, 𝕜)` to `C(X, ℝ)` using `RCLike.re`.
-/
@[simps] def rclikeToReal (f : C(X, 𝕜)) : C(X, ℝ) where toFun x := RCLike.re (f x)

variable (X) in
/-
**ContinuousMap.rclikeToReal_monotone** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMap`。
形式化陈述：rclikeToReal_monotone : Monotone (rclikeToReal (X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `RCLike.le_iff_re_im`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K] {
z w : K},   z ≤ w ↔ RCLike.re z ≤ RCLike.re w ∧ RCLike.im z = RCLike.im w
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.rclikeToReal_apply`：∀ {X : Type u_1} {𝕜 : Type u_2} [inst 
: TopologicalSpace X] [inst_1 : RCLike 𝕜] (f : C(X, 𝕜)) (x : X),   f.rclikeToRea
l x = RCLike.re (f x)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma rclikeToReal_monotone : Monotone (rclikeToReal (X := X) (𝕜 := 𝕜)) := by
  intro a b; simp_all [le_def, RCLike.le_iff_re_im (K := 𝕜)]

variable (X) in
/-
**ContinuousMap.continuous_rclikeToReal** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap
`。
形式化陈述：∀ (X : Type u_1) (𝕜 : Type u_2) [inst : TopologicalSpace X] [inst_1 : RCLi
ke 𝕜], Continuous ContinuousMap.rclikeToReal
参数：X : Type u_1；𝕜 : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.continuous_postcomp`：continuous_postcomp (g : C(Y, Z)) : C
ontinuous (ContinuousMap.comp g : C(X, Y) -> C(X, Z))
· 使用定理 `RCLike.continuous_re`：continuous_re : Continuous (re : K -> Real)
-/
@[simp, fun_prop] lemma continuous_rclikeToReal : Continuous (rclikeToReal (X := X) (𝕜 := 𝕜)) :=
  continuous_postcomp { toFun x := RCLike.re x }
/-
**ContinuousMap.rclikeToReal_realToRCLike** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousM
ap`。
形式化陈述：∀ {X : Type u_1} (𝕜 : Type u_2) [inst : TopologicalSpace X] [inst_1 : RCLi
ke 𝕜] (f : C(X, ℝ)),   (ContinuousMap.realToRCLike 𝕜 f).rclikeToReal = f
参数：𝕜 : Type u_2；f : C(X, ℝ)；ContinuousMap.realToRCLike 𝕜 f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.rclikeToReal_apply`：∀ {X : Type u_1} {𝕜 : Type u_2} [inst 
: TopologicalSpace X] [inst_1 : RCLike 𝕜] (f : C(X, 𝕜)) (x : X),   f.rclikeToRea
l x = RCLike.re (f x)
· 使用定理 `ContinuousMap.realToRCLike_apply`：∀ {X : Type u_1} (𝕜 : Type u_2) [inst 
: TopologicalSpace X] [inst_1 : RCLike 𝕜] (f : C(X, ℝ)) (x : X),   (ContinuousMa
p.realToRCLike 𝕜 f) x …
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem rclikeToReal_realToRCLike (f : C(X, ℝ)) :
    (f.realToRCLike 𝕜).rclikeToReal = f := by ext; simp

variable {𝕜} in
@[aesop safe apply, grind =]
/-
**ContinuousMap.IsSelfAdjoint.realToRCLike_rclikeToReal** 是 Mathlib 中的一个定理，位于命名空
间 `ContinuousMap.IsSelfAdjoint`。
形式化陈述：∀ {X : Type u_1} {𝕜 : Type u_2} [inst : TopologicalSpace X] [inst_1 : RCLi
ke 𝕜] {f : C(X, 𝕜)},   IsSelfAdjoint f → ContinuousMap.realToRCLike 𝕜 f.rclikeTo
Real = f
参数：X, 𝕜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.realToRCLike_apply`：∀ {X : Type u_1} (𝕜 : Type u_2) [inst 
: TopologicalSpace X] [inst_1 : RCLike 𝕜] (f : C(X, ℝ)) (x : X),   (ContinuousMa
p.realToRCLike 𝕜 f) x …
· 使用定理 `ContinuousMap.rclikeToReal_apply`：∀ {X : Type u_1} {𝕜 : Type u_2} [inst 
: TopologicalSpace X] [inst_1 : RCLike 𝕜] (f : C(X, 𝕜)) (x : X),   f.rclikeToRea
l x = RCLike.re (f x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsSelfAdjoint.realToRCLike_rclikeToReal {f : C(X, 𝕜)} (hf : IsSelfAdjoint f) :
    f.rclikeToReal.realToRCLike 𝕜 = f := by
  ext
  simp only [realToRCLike_apply, rclikeToReal_apply, ← RCLike.conj_eq_iff_re]
  conv_rhs => rw [← hf.star_eq]
  simp

variable (X) in
open ContinuousMap in
/-
**ContinuousMap.range_realToRCLike_eq_isSelfAdjoint** 是 Mathlib 中的一个定理，位于命名空间 `C
ontinuousMap`。
形式化陈述：range_realToRCLike_eq_isSelfAdjoint : .range (realToRCLike 𝕜) = {f : C(X, 
𝕜) | IsSelfAdjoint f}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousMap.IsSelfAdjoint.realToRCLike_rclikeToReal`：∀ {X : Type u_1} 
{𝕜 : Type u_2} [inst : TopologicalSpace X] [inst_1 : RCLike 𝕜] {f : C(X, 𝕜)},   
IsSelfAdjoint f → ContinuousMap.realToRCLik…
-/
theorem range_realToRCLike_eq_isSelfAdjoint :
    .range (realToRCLike 𝕜) = {f : C(X, 𝕜) | IsSelfAdjoint f} :=
  le_antisymm (fun _ ⟨_, h⟩ ↦ by simp [← h]) fun f hf ↦
    ⟨f.rclikeToReal, hf.realToRCLike_rclikeToReal⟩

end ContinuousMap

