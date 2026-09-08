/-
Copyright (c) 2024 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
module

public import Mathlib.Analysis.Normed.Group.Hom
public import Mathlib.Topology.Algebra.SeparationQuotient.Hom

/-!
# Lifts of maps to separation quotients of seminormed groups

For any `SeminormedAddCommGroup M`, a `NormedAddCommGroup` instance has been defined in
`Mathlib/Analysis/Normed/Group/Uniform.lean`.

## Main definitions

We use `M` and `N` to denote seminormed groups.
All the following definitions are in the `SeparationQuotient` namespace. Hence we can access
`SeparationQuotient.normedMk` as `normedMk`.

* `normedMk` : the normed group hom from `M` to `SeparationQuotient M`.

* `liftNormedAddGroupHom` : any bounded group hom `f : M → N` such that `∀ x, ‖x‖ = 0 → f x = 0`
  descends to a bounded group hom `SeparationQuotient M → N`.
  Here, `(f : NormedAddGroupHom M N)`, `(hf : ∀ x : M, ‖x‖ = 0 → f x = 0)`
  and `liftNormedAddGroupHom f hf : NormedAddGroupHom (SeparationQuotient M) N` such that
  `liftNormedAddGroupHom f hf (mk x) = f x`.

## Main results

* `norm_normedMk_eq_one` : the operator norm of the projection is `1` if the subspace is not `⊤`.

* `norm_liftNormedAddGroupHom_le` : `‖liftNormedAddGroupHom f hf‖ ≤ ‖f‖`.
-/

@[expose] public section

section

open SeparationQuotient NNReal

variable {M N : Type*} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]

namespace SeparationQuotient

open NormedAddGroupHom

/-- The morphism from a seminormed group to the quotient by the inseparable setoid. -/
@[simps]
/-
**SeparationQuotient.normedMk** 是 Mathlib 中的一个定义，位于命名空间 `SeparationQuotient`。
形式化陈述：normedMk : NormedAddGroupHom M (SeparationQuotient M) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism from a seminormed group to the quotient by the inseparable setoid.
-/
noncomputable def normedMk : NormedAddGroupHom M (SeparationQuotient M) where
  __ := mkAddMonoidHom
  bound' := ⟨1, by simp⟩

/-- The operator norm of the projection is at most `1`. -/
/-
**SeparationQuotient.norm_normedMk_le** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuoti
ent`。
形式化陈述：norm_normedMk_le : ‖normedMk (M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.opNorm_le_bound`：opNorm_le_bound {M : Real} (hMp : 0 <
= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeparationQuotient.normedMk_apply`：∀ {M : Type u_1} [inst : SeminormedAd
dCommGroup M] (a : M),   SeparationQuotient.normedMk a = (↑SeparationQuotient.mk
AddMonoidHom).toFun a
· 使用定理 `SeparationQuotient.mkAddMonoidHom_apply`：∀ {M : Type u_1} [inst : Topolo
gicalSpace M] [inst_1 : AddZeroClass M] [inst_2 : ContinuousAdd M] (a : M),   Se
parationQuotient.mkAddMonoidH…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
The operator norm of the projection is at most `1`.
-/
theorem norm_normedMk_le : ‖normedMk (M := M)‖ ≤ 1 :=
  NormedAddGroupHom.opNorm_le_bound _ zero_le_one fun m => by simp
/-
**SeparationQuotient.apply_eq_apply_of_inseparable** 是 Mathlib 中的一个引理，位于命名空间 `Se
parationQuotient`。
形式化陈述：apply_eq_apply_of_inseparable {F : Type*} [FunLike F M N] [AddMonoidHomCla
ss F M N] (f : F) (hf : forall x, ‖x‖ = 0 -> f x = 0) : forall x y, Inseparable 
x y -> f x = f y
参数：f : F；hf : forall x, ‖x‖ = 0 -> f x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_sub_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a b : 
α}, a - b = 0 → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `Metric.inseparable_iff`：Metric.inseparable_iff {x y : α} : Inseparable x
 y ↔ dist x y = 0
-/
lemma apply_eq_apply_of_inseparable {F : Type*} [FunLike F M N] [AddMonoidHomClass F M N] (f : F)
    (hf : ∀ x, ‖x‖ = 0 → f x = 0) : ∀ x y, Inseparable x y → f x = f y :=
  fun x y h ↦ eq_of_sub_eq_zero <| by
    rw [← map_sub]
    rw [Metric.inseparable_iff, dist_eq_norm] at h
    exact hf (x - y) h

/-- The lift of a group hom to the separation quotient as a group hom. -/
@[simps]
/-
**SeparationQuotient.liftNormedAddGroupHom** 是 Mathlib 中的一个定义，位于命名空间 `Separation
Quotient`。
形式化陈述：liftNormedAddGroupHom (f : NormedAddGroupHom M N) (hf : forall x, ‖x‖ = 0 
-> f x = 0) : NormedAddGroupHom (SeparationQuotient M) N where toFun
参数：f : NormedAddGroupHom M N；hf : forall x, ‖x‖ = 0 -> f x = 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.instContinuousMapClass`：∀ {V₁ : Type u_2} {V₂ : Type u
_3} [inst : SeminormedAddCommGroup V₁] [inst_1 : SeminormedAddCommGroup V₂],   C
ontinuousMapClass (NormedAddGr…

--- 原说明 ---
The lift of a group hom to the separation quotient as a group hom.
-/
noncomputable def liftNormedAddGroupHom (f : NormedAddGroupHom M N)
    (hf : ∀ x, ‖x‖ = 0 → f x = 0) : NormedAddGroupHom (SeparationQuotient M) N where
  toFun := SeparationQuotient.liftContinuousAddMonoidHom f <| apply_eq_apply_of_inseparable f hf
  map_add' v₁ v₂ := map_add ..
  bound' := by
    refine ⟨‖f‖, fun v ↦ ?_⟩
    obtain ⟨v, rfl⟩ := surjective_mk v
    exact le_opNorm f v
/-
**SeparationQuotient.norm_liftNormedAddGroupHom_apply_le** 是 Mathlib 中的一个定理，位于命名
空间 `SeparationQuotient`。
形式化陈述：norm_liftNormedAddGroupHom_apply_le (f : NormedAddGroupHom M N) (hf : fora
ll x, ‖x‖ = 0 -> f x = 0) (x : SeparationQuotient M) : ‖liftNormedAddGroupHom f 
hf x‖ <= ‖f‖ * ‖x‖
参数：f : NormedAddGroupHom M N；hf : forall x, ‖x‖ = 0 -> f x = 0；x : SeparationQuo
tient M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeparationQuotient.surjective_mk`：surjective_mk : Surjective (mk : X -> 
SeparationQuotient X)
· 使用定理 `NormedAddGroupHom.le_opNorm`：le_opNorm (x : V₁) : ‖f x‖ <= ‖f‖ * ‖x‖
-/
theorem norm_liftNormedAddGroupHom_apply_le (f : NormedAddGroupHom M N)
    (hf : ∀ x, ‖x‖ = 0 → f x = 0) (x : SeparationQuotient M) :
    ‖liftNormedAddGroupHom f hf x‖ ≤ ‖f‖ * ‖x‖ := by
  obtain ⟨x, rfl⟩ := surjective_mk x
  exact le_opNorm f x

/-- The equivalence between `NormedAddGroupHom M N` vanishing on the inseparable setoid and
`NormedAddGroupHom (SeparationQuotient M) N`. -/
@[simps]
/-
**SeparationQuotient.liftNormedAddGroupHomEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Separ
ationQuotient`。
形式化陈述：liftNormedAddGroupHomEquiv {N : Type*} [SeminormedAddCommGroup N] : {f : N
ormedAddGroupHom M N // forall x, ‖x‖ = 0 -> f x = 0} ≃ NormedAddGroupHom (Separ
ationQuotient M) N where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `NormedAddGroupHom M N` vanishing on the inseparable set
oid and
`NormedAddGroupHom (SeparationQuotient M) N`.
-/
noncomputable def liftNormedAddGroupHomEquiv {N : Type*} [SeminormedAddCommGroup N] :
    {f : NormedAddGroupHom M N // ∀ x, ‖x‖ = 0 → f x = 0} ≃
    NormedAddGroupHom (SeparationQuotient M) N where
  toFun f := liftNormedAddGroupHom f f.prop
  invFun g := ⟨g.comp normedMk, by
    intro x hx
    rw [← norm_mk, norm_eq_zero] at hx
    simp [hx]⟩
  right_inv _ := by
    ext x
    obtain ⟨x, rfl⟩ := surjective_mk x
    rfl

/-- For a norm-continuous group homomorphism `f`, its lift to the separation quotient
is bounded by the norm of `f`. -/
/-
**SeparationQuotient.norm_liftNormedAddGroupHom_le** 是 Mathlib 中的一个定理，位于命名空间 `Se
parationQuotient`。
形式化陈述：norm_liftNormedAddGroupHom_le {N : Type*} [SeminormedAddCommGroup N] (f : 
NormedAddGroupHom M N) (hf : forall s, ‖s‖ = 0 -> f s = 0) : ‖liftNormedAddGroup
Hom f hf‖ <= ‖f‖
参数：f : NormedAddGroupHom M N；hf : forall s, ‖s‖ = 0 -> f s = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.opNorm_le_bound`：opNorm_le_bound {M : Real} (hMp : 0 <
= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `SeparationQuotient.norm_liftNormedAddGroupHom_apply_le`：norm_liftNormedA
ddGroupHom_apply_le (f : NormedAddGroupHom M N) (hf : forall x, ‖x‖ = 0 -> f x =
 0) (x : SeparationQuotient M) : ‖liftNormed…

--- 原说明 ---
For a norm-continuous group homomorphism `f`, its lift to the separation quotien
t
is bounded by the norm of `f`.
-/
theorem norm_liftNormedAddGroupHom_le {N : Type*} [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) (hf : ∀ s, ‖s‖ = 0 → f s = 0) :
    ‖liftNormedAddGroupHom f hf‖ ≤ ‖f‖ :=
  NormedAddGroupHom.opNorm_le_bound _ (norm_nonneg f) (norm_liftNormedAddGroupHom_apply_le f hf)
/-
**SeparationQuotient.liftNormedAddGroupHom_norm_le** 是 Mathlib 中的一个定理，位于命名空间 `Se
parationQuotient`。
形式化陈述：liftNormedAddGroupHom_norm_le {N : Type*} [SeminormedAddCommGroup N] (f : 
NormedAddGroupHom M N) (hf : forall s, ‖s‖ = 0 -> f s = 0) {c : Real>=0} (fb : ‖
f‖ <= c) : ‖liftNormedAddGroupHom f hf‖ <= c
参数：f : NormedAddGroupHom M N；hf : forall s, ‖s‖ = 0 -> f s = 0；fb : ‖f‖ <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `SeparationQuotient.norm_liftNormedAddGroupHom_le`：norm_liftNormedAddGrou
pHom_le {N : Type*} [SeminormedAddCommGroup N] (f : NormedAddGroupHom M N) (hf :
 forall s, ‖s‖ = 0 -> f s = 0) : ‖lift…
-/
theorem liftNormedAddGroupHom_norm_le {N : Type*} [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) (hf : ∀ s, ‖s‖ = 0 → f s = 0) {c : ℝ≥0} (fb : ‖f‖ ≤ c) :
    ‖liftNormedAddGroupHom f hf‖ ≤ c :=
  (norm_liftNormedAddGroupHom_le f hf).trans fb
/-
**SeparationQuotient.liftNormedAddGroupHom_normNoninc** 是 Mathlib 中的一个定理，位于命名空间 
`SeparationQuotient`。
形式化陈述：liftNormedAddGroupHom_normNoninc {N : Type*} [SeminormedAddCommGroup N] (f
 : NormedAddGroupHom M N) (hf : forall s, ‖s‖ = 0 -> f s = 0) (fb : f.NormNoninc
) : (liftNormedAddGroupHom f hf).NormNoninc
参数：f : NormedAddGroupHom M N；hf : forall s, ‖s‖ = 0 -> f s = 0；fb : f.NormNoninc
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one`：normNoninc_iff_
norm_le_one : f.NormNoninc ↔ ‖f‖ <= 1
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `SeparationQuotient.norm_liftNormedAddGroupHom_apply_le`：norm_liftNormedA
ddGroupHom_apply_le (f : NormedAddGroupHom M N) (hf : forall x, ‖x‖ = 0 -> f x =
 0) (x : SeparationQuotient M) : ‖liftNormed…
· 使用定理 `mul_le_of_le_one_left`：mul_le_of_le_one_left [MulPosMono α] (hb : 0 <= b
) (h : a <= 1) : a * b <= b
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem liftNormedAddGroupHom_normNoninc {N : Type*} [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) (hf : ∀ s, ‖s‖ = 0 → f s = 0) (fb : f.NormNoninc) :
    (liftNormedAddGroupHom f hf).NormNoninc := fun x => by
  have fb' : ‖f‖ ≤ 1 := NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.mp fb
  exact le_trans (norm_liftNormedAddGroupHom_apply_le f hf x)
    (mul_le_of_le_one_left (norm_nonneg x) fb')

/-- The operator norm of the projection is `1` if there is an element whose norm is different from
`0`. -/
/-
**SeparationQuotient.norm_normedMk_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQ
uotient`。
形式化陈述：norm_normedMk_eq_one [NontrivialTopology M] : ‖normedMk (M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedAddGroupHom.opNorm_eq_of_bounds`：opNorm_eq_of_bounds {M : Real} (M
_nonneg : 0 <= M) (h_above : forall x, ‖f x‖ <= M * ‖x‖) (h_below : forall N >= 
0, (forall x, ‖f x‖ <= N * …
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeparationQuotient.normedMk_apply`：∀ {M : Type u_1} [inst : SeminormedAd
dCommGroup M] (a : M),   SeparationQuotient.normedMk a = (↑SeparationQuotient.mk
AddMonoidHom).toFun a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `exists_norm_ne_zero`：∀ (E : Type u_5) [inst : SeminormedAddGroup E] [Non
trivialTopology E], ∃ x, ‖x‖ ≠ 0
· 使用引理 `one_le_of_le_mul_right₀`：one_le_of_le_mul_right₀ [MulPosReflectLE α] (hb
 : 0 < b) (h : b <= a * b) : 1 <= a
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖

--- 原说明 ---
The operator norm of the projection is `1` if there is an element whose norm is 
different from
`0`.
-/
theorem norm_normedMk_eq_one [NontrivialTopology M] :
    ‖normedMk (M := M)‖ = 1 := by
  apply NormedAddGroupHom.opNorm_eq_of_bounds _ zero_le_one
  · simpa only [normedMk_apply, one_mul] using! fun _ ↦ le_rfl
  · intro N _ hle
    obtain ⟨x, _⟩ := exists_norm_ne_zero M
    exact one_le_of_le_mul_right₀ (by positivity) (hle x)

/-- The projection is `0` if and only if all the elements have norm `0`. -/
/-
**SeparationQuotient.normedMk_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQ
uotient`。
形式化陈述：normedMk_eq_zero_iff : normedMk (M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SeparationQuotient.mk_eq_zero_iff`：∀ {E : Type u_2} [inst : SeminormedAd
dCommGroup E] {p : E}, SeparationQuotient.mk p = 0 ↔ ‖p‖ = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SeparationQuotient.normedMk_apply`：∀ {M : Type u_1} [inst : SeminormedAd
dCommGroup M] (a : M),   SeparationQuotient.normedMk a = (↑SeparationQuotient.mk
AddMonoidHom).toFun a
· 使用定理 `SeparationQuotient.mkAddMonoidHom_apply`：∀ {M : Type u_1} [inst : Topolo
gicalSpace M] [inst_1 : AddZeroClass M] [inst_2 : ContinuousAdd M] (a : M),   Se
parationQuotient.mkAddMonoidH…
· 使用定理 `NormedAddGroupHom.ext`：ext (H : forall x, f x = g x) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖

--- 原说明 ---
The projection is `0` if and only if all the elements have norm `0`.
-/
theorem normedMk_eq_zero_iff : normedMk (M := M) = 0 ↔ ∀ (x : M), ‖x‖ = 0 := by
  constructor
  · intro h x
    rw [SeparationQuotient.mk_eq_zero_iff.mp]
    have : normedMk x = 0 := by
      rw [h]
      simp only [NormedAddGroupHom.zero_apply]
    rw [← this]
    simp
  · intro h
    ext x
    simpa [← norm_eq_zero] using h x

end SeparationQuotient

end

