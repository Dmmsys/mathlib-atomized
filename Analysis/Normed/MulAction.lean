/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.ENNReal.Action
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.MetricSpace.Algebra

/-!
# Lemmas for `IsBoundedSMul` over normed additive groups

Lemmas which hold only in `NormedSpace α β` are provided in another file.

Notably we prove that `NonUnitalSeminormedRing`s have bounded actions by left- and right-
multiplication. This allows downstream files to write general results about `IsBoundedSMul`, and
then deduce `const_mul` and `mul_const` results as an immediate corollary.
-/

public section


variable {α β : Type*}

section SeminormedAddGroup

variable [SeminormedAddGroup α] [SeminormedAddGroup β] [SMulZeroClass α β]
variable [IsBoundedSMul α β] {r : α} {x : β}

@[bound]
/--
theorem `norm_smul_le` / 定理 `norm_smul_le`

English:
theorem norm_smul_le
  given: (r : α) (x : β)
  statement: ‖r • x‖ <= ‖r‖ * ‖x‖
  proof: by
  simpa [smul_zero] using dist_smul_pair r 0 x

@[bound]

中文:
定理 norm_smul_le
  条件: (r : α) (x : β)
  结论: ‖r • x‖ <= ‖r‖ * ‖x‖
  证明: by
  simpa [smul_zero] using dist_smul_pair r 0 x

@[bound]

Depends on / 依赖: dist_smul_pair, smul_zero
-/
theorem norm_smul_le (r : α) (x : β) : ‖r • x‖ <= ‖r‖ * ‖x‖ := by
  simpa [smul_zero] using dist_smul_pair r 0 x

@[bound]
/--
theorem `nnnorm_smul_le` / 定理 `nnnorm_smul_le`

English:
theorem nnnorm_smul_le
  given: (r : α) (x : β)
  statement: ‖r • x‖₊ <= ‖r‖₊ * ‖x‖₊
  proof: norm_smul_le _ _

@[bound]

中文:
定理 nnnorm_smul_le
  条件: (r : α) (x : β)
  结论: ‖r • x‖₊ <= ‖r‖₊ * ‖x‖₊
  证明: norm_smul_le _ _

@[bound]

Depends on / 依赖: norm_smul_le
-/
theorem nnnorm_smul_le (r : α) (x : β) : ‖r • x‖₊ <= ‖r‖₊ * ‖x‖₊ :=
  norm_smul_le _ _

@[bound]
/--
lemma `enorm_smul_le` / 引理 `enorm_smul_le`

English:
lemma enorm_smul_le
  statement: ‖r • x‖ₑ <= ‖r‖ₑ * ‖x‖ₑ
  proof: by
  simpa [enorm, ← ENNReal.coe_mul] using nnnorm_smul_le ..

中文:
引理 enorm_smul_le
  结论: ‖r • x‖ₑ <= ‖r‖ₑ * ‖x‖ₑ
  证明: by
  simpa [enorm, ← ENNReal.coe_mul] using nnnorm_smul_le ..

Depends on / 依赖: ENNReal, ENNReal.coe_mul, coe_mul, nnnorm_smul_le
-/
lemma enorm_smul_le : ‖r • x‖ₑ <= ‖r‖ₑ * ‖x‖ₑ := by
  simpa [enorm, ← ENNReal.coe_mul] using nnnorm_smul_le ..

/--
theorem `dist_smul_le` / 定理 `dist_smul_le`

English:
theorem dist_smul_le
  given: (s : α) (x y : β)
  statement: dist (s • x) (s • y) <= ‖s‖ * dist x y
  proof: by
  simpa only [dist_eq_norm_neg_add, add_zero, norm_neg] using dist_smul_pair s x y

中文:
定理 dist_smul_le
  条件: (s : α) (x y : β)
  结论: dist (s • x) (s • y) <= ‖s‖ * dist x y
  证明: by
  simpa only [dist_eq_norm_neg_add, add_zero, norm_neg] using dist_smul_pair s x y

Depends on / 依赖: add_zero, dist_eq_norm_neg_add, dist_smul_pair, norm_neg
-/
theorem dist_smul_le (s : α) (x y : β) : dist (s • x) (s • y) <= ‖s‖ * dist x y := by
  simpa only [dist_eq_norm_neg_add, add_zero, norm_neg] using dist_smul_pair s x y

/--
theorem `nndist_smul_le` / 定理 `nndist_smul_le`

English:
theorem nndist_smul_le
  given: (s : α) (x y : β)
  statement: nndist (s • x) (s • y) <= ‖s‖₊ * nndist x y
  proof: dist_smul_le s x y

中文:
定理 nndist_smul_le
  条件: (s : α) (x y : β)
  结论: nndist (s • x) (s • y) <= ‖s‖₊ * nndist x y
  证明: dist_smul_le s x y

Depends on / 依赖: dist_smul_le
-/
theorem nndist_smul_le (s : α) (x y : β) : nndist (s • x) (s • y) <= ‖s‖₊ * nndist x y :=
  dist_smul_le s x y

/--
theorem `lipschitzWith_smul` / 定理 `lipschitzWith_smul`

English:
theorem lipschitzWith_smul
  given: (s : α)
  statement: LipschitzWith ‖s‖₊ (s • · : β -> β)
  proof: lipschitzWith_iff_dist_le_mul.2 dist_smul_le _

中文:
定理 lipschitzWith_smul
  条件: (s : α)
  结论: LipschitzWith ‖s‖₊ (s • · : β -> β)
  证明: lipschitzWith_iff_dist_le_mul.2 dist_smul_le _

Depends on / 依赖: dist_smul_le, lipschitzWith_iff_dist_le_mul
-/
theorem lipschitzWith_smul (s : α) : LipschitzWith ‖s‖₊ (s • · : β -> β) :=
lipschitzWith_iff_dist_le_mul.2 dist_smul_le _

/--
theorem `edist_smul_le` / 定理 `edist_smul_le`

English:
theorem edist_smul_le
  given: (s : α) (x y : β)
  statement: edist (s • x) (s • y) <= ‖s‖₊ • edist x y
  proof: lipschitzWith_smul s x y

中文:
定理 edist_smul_le
  条件: (s : α) (x y : β)
  结论: edist (s • x) (s • y) <= ‖s‖₊ • edist x y
  证明: lipschitzWith_smul s x y

Depends on / 依赖: lipschitzWith_smul
-/
theorem edist_smul_le (s : α) (x y : β) : edist (s • x) (s • y) <= ‖s‖₊ • edist x y :=
  lipschitzWith_smul s x y

end SeminormedAddGroup

/--
Instance `NonUnitalSeminormedRing.isBoundedSMul` / 实例 `NonUnitalSeminormedRing.isBoundedSMul`

English:
instance NonUnitalSeminormedRing.isBoundedSMul
  signature: [NonUnitalSeminormedRing α]
  body: by simpa [mul_sub, dist_eq_norm] using norm_mul_le x (y₁ - y₂)
  dist_pair_smul' x₁ x₂ y := by simpa [sub_mul, dist_eq_norm] using norm_mul_le (x₁ - x₂) y

中文:
实例 NonUnitalSeminormedRing.isBoundedSMul
  签名: [NonUnitalSeminormedRing α]
  定义体: by simpa [mul_sub, dist_eq_norm] using norm_mul_le x (y₁ - y₂)
  dist_pair_smul' x₁ x₂ y := by simpa [sub_mul, dist_eq_norm] using norm_mul_le (x₁ - x₂) y

Depends on / 依赖: dist_eq_norm, dist_pair_smul, mul_sub, norm_mul_le, sub_mul
-/
instance NonUnitalSeminormedRing.isBoundedSMul [NonUnitalSeminormedRing α] :
    IsBoundedSMul α α where
  dist_smul_pair' x y₁ y₂ := by simpa [mul_sub, dist_eq_norm] using norm_mul_le x (y₁ - y₂)
  dist_pair_smul' x₁ x₂ y := by simpa [sub_mul, dist_eq_norm] using norm_mul_le (x₁ - x₂) y

/--
Instance `NonUnitalSeminormedRing.isBoundedSMulOpposite` / 实例 `NonUnitalSeminormedRing.isBoundedSMulOpposite`

English:
instance NonUnitalSeminormedRing.isBoundedSMulOpposite
  signature: [NonUnitalSeminormedRing α]
  body: by
    simpa [sub_mul, dist_eq_norm, mul_comm] using! norm_mul_le (y₁ - y₂) x.unop
  dist_pair_smul' x₁ x₂ y := by
    simpa [mul_sub, dist_eq_norm, mul_comm] using! norm_mul_le y (x₁ - x₂).unop

中文:
实例 NonUnitalSeminormedRing.isBoundedSMulOpposite
  签名: [NonUnitalSeminormedRing α]
  定义体: by
    simpa [sub_mul, dist_eq_norm, mul_comm] using! norm_mul_le (y₁ - y₂) x.unop
  dist_pair_smul' x₁ x₂ y := by
    simpa [mul_sub, dist_eq_norm, mul_comm] using! norm_mul_le y (x₁ - x₂).unop

Depends on / 依赖: dist_eq_norm, dist_pair_smul, mul_comm, mul_sub, norm_mul_le, sub_mul, x.unop
-/
instance NonUnitalSeminormedRing.isBoundedSMulOpposite [NonUnitalSeminormedRing α] :
    IsBoundedSMul αᵐᵒᵖ α where
  dist_smul_pair' x y₁ y₂ := by
    simpa [sub_mul, dist_eq_norm, mul_comm] using! norm_mul_le (y₁ - y₂) x.unop
  dist_pair_smul' x₁ x₂ y := by
    simpa [mul_sub, dist_eq_norm, mul_comm] using! norm_mul_le y (x₁ - x₂).unop

section SeminormedRing

variable [SeminormedRing α] [SeminormedAddCommGroup β] [Module α β]

/--
theorem `IsBoundedSMul.of_norm_smul_le` / 定理 `IsBoundedSMul.of_norm_smul_le`

English:
theorem IsBoundedSMul.of_norm_smul_le
  given: (h : forall (r : α) (x : β), ‖r • x‖ <= ‖r‖ * ‖x‖)
  proof: { dist_smul_pair' := fun a b₁ b₂ => by simpa [smul_sub, dist_eq_norm] using h a (b₁ - b₂)
    dist_pair_smul' := fun a₁ a₂ b => by simpa [sub_smul, dist_eq_norm] using h (a₁ - a₂) b }

中文:
定理 IsBoundedSMul.of_norm_smul_le
  条件: (h : 对任意 (r : α) (x : β), ‖r • x‖ <= ‖r‖ * ‖x‖)
  证明: { dist_smul_pair' := fun a b₁ b₂ => by simpa [smul_sub, dist_eq_norm] using h a (b₁ - b₂)
    dist_pair_smul' := fun a₁ a₂ b => by simpa [sub_smul, dist_eq_norm] using h (a₁ - a₂) b }

Depends on / 依赖: dist_eq_norm, dist_pair_smul, dist_smul_pair, smul_sub, sub_smul
-/
theorem IsBoundedSMul.of_norm_smul_le (h : forall (r : α) (x : β), ‖r • x‖ <= ‖r‖ * ‖x‖) :
    IsBoundedSMul α β :=
  { dist_smul_pair' := fun a b₁ b₂ => by simpa [smul_sub, dist_eq_norm] using h a (b₁ - b₂)
    dist_pair_smul' := fun a₁ a₂ b => by simpa [sub_smul, dist_eq_norm] using h (a₁ - a₂) b }

/--
theorem `IsBoundedSMul.of_enorm_smul_le` / 定理 `IsBoundedSMul.of_enorm_smul_le`

English:
theorem IsBoundedSMul.of_enorm_smul_le
  given: (h : forall (r : α) (x : β), ‖r • x‖ₑ <= ‖r‖ₑ * ‖x‖ₑ)
  proof: .of_norm_smul_le (by simpa [enorm_eq_nnnorm, ← ENNReal.coe_mul, ENNReal.coe_le_coe] using! h)

中文:
定理 IsBoundedSMul.of_enorm_smul_le
  条件: (h : 对任意 (r : α) (x : β), ‖r • x‖ₑ <= ‖r‖ₑ * ‖x‖ₑ)
  证明: .of_norm_smul_le (by simpa [enorm_eq_nnnorm, ← ENNReal.coe_mul, ENNReal.coe_le_coe] using! h)

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe, ENNReal.coe_mul, coe_le_coe, coe_mul, enorm_eq_nnnorm, of_norm_smul_le
-/
theorem IsBoundedSMul.of_enorm_smul_le (h : forall (r : α) (x : β), ‖r • x‖ₑ <= ‖r‖ₑ * ‖x‖ₑ) :
    IsBoundedSMul α β :=
  .of_norm_smul_le (by simpa [enorm_eq_nnnorm, ← ENNReal.coe_mul, ENNReal.coe_le_coe] using! h)

/--
theorem `IsBoundedSMul.of_nnnorm_smul_le` / 定理 `IsBoundedSMul.of_nnnorm_smul_le`

English:
theorem IsBoundedSMul.of_nnnorm_smul_le
  given: (h : forall (r : α) (x : β), ‖r • x‖₊ <= ‖r‖₊ * ‖x‖₊)
  proof: .of_norm_smul_le h

中文:
定理 IsBoundedSMul.of_nnnorm_smul_le
  条件: (h : 对任意 (r : α) (x : β), ‖r • x‖₊ <= ‖r‖₊ * ‖x‖₊)
  证明: .of_norm_smul_le h

Depends on / 依赖: of_norm_smul_le
-/
theorem IsBoundedSMul.of_nnnorm_smul_le (h : forall (r : α) (x : β), ‖r • x‖₊ <= ‖r‖₊ * ‖x‖₊) :
    IsBoundedSMul α β := .of_norm_smul_le h

end SeminormedRing

section NormSMulClass

/--
Definition of `NormSMulClass` / `NormSMulClass` 的定义

English:
class NormSMulClass
  parameters: (α β : Type*) [Norm α] [Norm β] [SMul α β]
  axioms and operations (1):
    - norm_smul((r : α) (x : β)) : ‖r • x‖ = ‖r‖ * ‖x‖

中文:
类 NormSMulClass
  参数: (α β : 类型) [Norm α] [Norm β] [SMul α β]
  公理与运算 (1 个):
    - norm_smul((r : α) (x : β)) : ‖r • x‖ = ‖r‖ * ‖x‖
-/
class NormSMulClass (α β : Type*) [Norm α] [Norm β] [SMul α β] : Prop where
  protected norm_smul (r : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖

/--
lemma `norm_smul` / 引理 `norm_smul`

English:
lemma norm_smul
  given: [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r : α) (x : β)
  proof: NormSMulClass.norm_smul r x

中文:
引理 norm_smul
  条件: [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r : α) (x : β)
  证明: NormSMulClass.norm_smul r x

Depends on / 依赖: NormSMulClass, NormSMulClass.norm_smul, norm_smul
-/
lemma norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r : α) (x : β) :
    ‖r • x‖ = ‖r‖ * ‖x‖ :=
  NormSMulClass.norm_smul r x

instance (priority := 100) NormMulClass.toNormSMulClass [Norm α] [Mul α] [NormMulClass α] :
    NormSMulClass α α where
  norm_smul := norm_mul

instance (priority := 100) NormMulClass.toNormSMulClass_op [SeminormedRing α] [NormMulClass α] :
    NormSMulClass αᵐᵒᵖ α where
  norm_smul a b := mul_comm ‖b‖ ‖a‖ ▸ norm_mul b a.unop

/--
Definition of `ENormSMulClass` / `ENormSMulClass` 的定义

English:
class ENormSMulClass
  parameters: (α β : Type*) [ENorm α] [ENorm β] [SMul α β]
  axioms and operations (1):
    - enorm_smul((r : α) (x : β)) : ‖r • x‖ₑ = ‖r‖ₑ * ‖x‖ₑ

中文:
类 ENormSMulClass
  参数: (α β : 类型) [ENorm α] [ENorm β] [SMul α β]
  公理与运算 (1 个):
    - enorm_smul((r : α) (x : β)) : ‖r • x‖ₑ = ‖r‖ₑ * ‖x‖ₑ
-/
class ENormSMulClass (α β : Type*) [ENorm α] [ENorm β] [SMul α β] : Prop where
  protected enorm_smul (r : α) (x : β) : ‖r • x‖ₑ = ‖r‖ₑ * ‖x‖ₑ

/--
lemma `enorm_smul` / 引理 `enorm_smul`

English:
lemma enorm_smul
  given: [ENorm α] [ENorm β] [SMul α β] [ENormSMulClass α β] (r : α) (x : β)
  proof: ENormSMulClass.enorm_smul r x

中文:
引理 enorm_smul
  条件: [ENorm α] [ENorm β] [SMul α β] [ENormSMulClass α β] (r : α) (x : β)
  证明: ENormSMulClass.enorm_smul r x

Depends on / 依赖: ENormSMulClass, ENormSMulClass.enorm_smul, enorm_smul
-/
lemma enorm_smul [ENorm α] [ENorm β] [SMul α β] [ENormSMulClass α β] (r : α) (x : β) :
    ‖r • x‖ₑ = ‖r‖ₑ * ‖x‖ₑ :=
  ENormSMulClass.enorm_smul r x

variable [SeminormedRing α] [SeminormedAddGroup β] [SMul α β]

/--
theorem `NormSMulClass.of_nnnorm_smul` / 定理 `NormSMulClass.of_nnnorm_smul`

English:
theorem NormSMulClass.of_nnnorm_smul
  given: (h : forall (r : α) (x : β), ‖r • x‖₊ = ‖r‖₊ * ‖x‖₊)
  proof: congr_arg NNReal.toReal (h r b)

中文:
定理 NormSMulClass.of_nnnorm_smul
  条件: (h : 对任意 (r : α) (x : β), ‖r • x‖₊ = ‖r‖₊ * ‖x‖₊)
  证明: congr_arg NNReal.toReal (h r b)

Depends on / 依赖: NNReal, NNReal.toReal, congr_arg, toReal
-/
theorem NormSMulClass.of_nnnorm_smul (h : forall (r : α) (x : β), ‖r • x‖₊ = ‖r‖₊ * ‖x‖₊) :
    NormSMulClass α β where
  norm_smul r b := congr_arg NNReal.toReal (h r b)

variable [NormSMulClass α β]

/--
theorem `nnnorm_smul` / 定理 `nnnorm_smul`

English:
theorem nnnorm_smul
  given: (r : α) (x : β)
  statement: ‖r • x‖₊ = ‖r‖₊ * ‖x‖₊
  proof: NNReal.eq norm_smul r x

中文:
定理 nnnorm_smul
  条件: (r : α) (x : β)
  结论: ‖r • x‖₊ = ‖r‖₊ * ‖x‖₊
  证明: NNReal.eq norm_smul r x

Depends on / 依赖: NNReal, NNReal.eq, norm_smul
-/
theorem nnnorm_smul (r : α) (x : β) : ‖r • x‖₊ = ‖r‖₊ * ‖x‖₊ :=
NNReal.eq norm_smul r x

instance (priority := 100) : ENormSMulClass α β where
  enorm_smul r x := by simp [enorm, nnnorm_smul]

/--
Instance `Pi.instNormSMulClass` / 实例 `Pi.instNormSMulClass`

English:
instance Pi.instNormSMulClass
  signature: {ι : Type*} {β : ι -> Type*} [Fintype ι]
  body: by
    simp [nnnorm_def, ← coe_nnnorm, nnnorm_smul, ← NNReal.coe_mul, NNReal.mul_finset_sup]

中文:
实例 Pi.instNormSMulClass
  签名: {ι : 类型} {β : ι -> 类型} [Fintype ι]
  定义体: by
    simp [nnnorm_def, ← coe_nnnorm, nnnorm_smul, ← NNReal.coe_mul, NNReal.mul_finset_sup]

Depends on / 依赖: NNReal, NNReal.coe_mul, NNReal.mul_finset_sup, coe_mul, coe_nnnorm, mul_finset_sup, nnnorm_def, nnnorm_smul
-/
instance Pi.instNormSMulClass {ι : Type*} {β : ι -> Type*} [Fintype ι]
    [forall i, SeminormedAddGroup (β i)] [forall i, SMul α (β i)] [forall i, NormSMulClass α (β i)] :
    NormSMulClass α (Π i, β i) where
  norm_smul r x := by
    simp [nnnorm_def, ← coe_nnnorm, nnnorm_smul, ← NNReal.coe_mul, NNReal.mul_finset_sup]

/--
Instance `Prod.instNormSMulClass` / 实例 `Prod.instNormSMulClass`

English:
instance Prod.instNormSMulClass
  signature: {γ : Type*} [SeminormedAddGroup γ] [SMul α γ] [NormSMulClass α γ]
  body: fun r ⟨v₁, v₂⟩ => by simp only [smul_def, ← coe_nnnorm, nnnorm_def,
    nnnorm_smul r, ← NNReal.coe_mul, NNReal.mul_sup]

中文:
实例 Prod.instNormSMulClass
  签名: {γ : 类型} [SeminormedAddGroup γ] [SMul α γ] [NormSMulClass α γ]
  定义体: fun r ⟨v₁, v₂⟩ => by simp only [smul_def, ← coe_nnnorm, nnnorm_def,
    nnnorm_smul r, ← NNReal.coe_mul, NNReal.mul_sup]

Depends on / 依赖: coe_nnnorm, nnnorm_def, smul_def
-/
instance Prod.instNormSMulClass {γ : Type*} [SeminormedAddGroup γ] [SMul α γ] [NormSMulClass α γ] :
    NormSMulClass α (β × γ) where
  norm_smul := fun r ⟨v₁, v₂⟩ => by simp only [smul_def, ← coe_nnnorm, nnnorm_def,
    nnnorm_smul r, ← NNReal.coe_mul, NNReal.mul_sup]

/--
Instance `ULift.instNormSMulClass` / 实例 `ULift.instNormSMulClass`

English:
instance ULift.instNormSMulClass
  signature: : NormSMulClass α (ULift β) where
  body: norm_smul r v.down

中文:
实例 ULift.instNormSMulClass
  签名: : NormSMulClass α (ULift β) where
  定义体: norm_smul r v.down

Depends on / 依赖: norm_smul, v.down
-/
instance ULift.instNormSMulClass : NormSMulClass α (ULift β) where
  norm_smul r v := norm_smul r v.down

end NormSMulClass

section NormSMulClassModule

variable [SeminormedRing α] [SeminormedAddCommGroup β] [Module α β] [NormSMulClass α β]

/--
theorem `dist_smul₀` / 定理 `dist_smul₀`

English:
theorem dist_smul₀
  given: (s : α) (x y : β)
  statement: dist (s • x) (s • y) = ‖s‖ * dist x y
  proof: by
  simp_rw [dist_eq_norm, (norm_smul s (x - y)).symm, smul_sub]

中文:
定理 dist_smul₀
  条件: (s : α) (x y : β)
  结论: dist (s • x) (s • y) = ‖s‖ * dist x y
  证明: by
  simp_rw [dist_eq_norm, (norm_smul s (x - y)).symm, smul_sub]

Depends on / 依赖: dist_eq_norm, norm_smul, simp_rw, smul_sub
-/
theorem dist_smul₀ (s : α) (x y : β) : dist (s • x) (s • y) = ‖s‖ * dist x y := by
  simp_rw [dist_eq_norm, (norm_smul s (x - y)).symm, smul_sub]

/--
theorem `nndist_smul₀` / 定理 `nndist_smul₀`

English:
theorem nndist_smul₀
  given: (s : α) (x y : β)
  statement: nndist (s • x) (s • y) = ‖s‖₊ * nndist x y
  proof: NNReal.eq dist_smul₀ s x y

中文:
定理 nndist_smul₀
  条件: (s : α) (x y : β)
  结论: nndist (s • x) (s • y) = ‖s‖₊ * nndist x y
  证明: NNReal.eq dist_smul₀ s x y

Depends on / 依赖: NNReal, NNReal.eq
-/
theorem nndist_smul₀ (s : α) (x y : β) : nndist (s • x) (s • y) = ‖s‖₊ * nndist x y :=
NNReal.eq dist_smul₀ s x y

/--
theorem `edist_smul₀` / 定理 `edist_smul₀`

English:
theorem edist_smul₀
  given: (s : α) (x y : β)
  statement: edist (s • x) (s • y) = ‖s‖₊ • edist x y
  proof: by
  simp only [edist_nndist, nndist_smul₀, ENNReal.coe_mul, ENNReal.smul_def, smul_eq_mul]

中文:
定理 edist_smul₀
  条件: (s : α) (x y : β)
  结论: edist (s • x) (s • y) = ‖s‖₊ • edist x y
  证明: by
  simp only [edist_nndist, nndist_smul₀, ENNReal.coe_mul, ENNReal.smul_def, smul_eq_mul]

Depends on / 依赖: ENNReal, ENNReal.coe_mul, ENNReal.smul_def, coe_mul, edist_nndist, smul_def, smul_eq_mul
-/
theorem edist_smul₀ (s : α) (x y : β) : edist (s • x) (s • y) = ‖s‖₊ • edist x y := by
  simp only [edist_nndist, nndist_smul₀, ENNReal.coe_mul, ENNReal.smul_def, smul_eq_mul]

/--
Instance `NormSMulClass.toIsBoundedSMul` / 实例 `NormSMulClass.toIsBoundedSMul`

English:
instance NormSMulClass.toIsBoundedSMul
  signature: : IsBoundedSMul α β
  body: .of_norm_smul_le fun r x => (norm_smul r x).le

中文:
实例 NormSMulClass.toIsBoundedSMul
  签名: : IsBoundedSMul α β
  定义体: .of_norm_smul_le fun r x => (norm_smul r x).le

Depends on / 依赖: norm_smul, of_norm_smul_le
-/
instance NormSMulClass.toIsBoundedSMul : IsBoundedSMul α β :=
  .of_norm_smul_le fun r x => (norm_smul r x).le

end NormSMulClassModule

section NormedDivisionRing

variable [NormedDivisionRing α] [SeminormedAddGroup β]
variable [MulActionWithZero α β] [IsBoundedSMul α β]

/--
lemma `NormedDivisionRing.toNormSMulClass` / 引理 `NormedDivisionRing.toNormSMulClass`

English:
lemma NormedDivisionRing.toNormSMulClass
  statement: NormSMulClass α β where
  proof: by
    by_cases h : r = 0
    · simp [h, zero_smul α x]
    · refine le_antisymm (norm_smul_le r x) ?_
      calc
      ‖r‖ * ‖x‖ = ‖r‖ * ‖r⁻¹ • r • x‖ := by rw [inv_smul_smul₀ h]
      _ <= ‖r‖ * (‖r⁻¹‖ * ‖r • x‖) := by gcongr; apply norm_smul_le
      _ = ‖r • x‖ := by rw [norm_inv, ← mul_assoc, m

中文:
引理 NormedDivisionRing.toNormSMulClass
  结论: NormSMulClass α β where
  证明: by
    by_cases h : r = 0
    · simp [h, zero_smul α x]
    · refine le_antisymm (norm_smul_le r x) ?_
      calc
      ‖r‖ * ‖x‖ = ‖r‖ * ‖r⁻¹ • r • x‖ := by rw [inv_smul_smul₀ h]
      _ <= ‖r‖ * (‖r⁻¹‖ * ‖r • x‖) := by gcongr; apply norm_smul_le
      _ = ‖r • x‖ := by rw [norm_inv, ← mul_assoc, m

Depends on / 依赖: le_antisymm, mul_assoc, norm_eq_zero, norm_inv, norm_smul_le, one_mul, zero_smul
-/
lemma NormedDivisionRing.toNormSMulClass : NormSMulClass α β where
  norm_smul r x := by
    by_cases h : r = 0
    · simp [h, zero_smul α x]
    · refine le_antisymm (norm_smul_le r x) ?_
      calc
      ‖r‖ * ‖x‖ = ‖r‖ * ‖r⁻¹ • r • x‖ := by rw [inv_smul_smul₀ h]
      _ <= ‖r‖ * (‖r⁻¹‖ * ‖r • x‖) := by gcongr; apply norm_smul_le
      _ = ‖r • x‖ := by rw [norm_inv, ← mul_assoc, mul_inv_cancel₀ (mt norm_eq_zero.1 h), one_mul]

end NormedDivisionRing

section NormedDivisionRingModule
variable [NormedDivisionRing α] [SeminormedAddCommGroup β] [Module α β] [NormSMulClass α β]

/--
theorem `Metric.smul_image_ball` / 定理 `Metric.smul_image_ball`

English:
theorem Metric.smul_image_ball
  given: {s : α} (hs : s != 0) (x : β) (ε : Real)
  proof: by
  ext p
  simp_rw [Set.mem_image, mem_ball]
  constructor
  · rintro ⟨y, h1, rfl⟩
    simpa [dist_smul₀] using mul_lt_mul_of_pos_left h1 (norm_pos_iff.mpr hs)
  · refine fun h => ⟨s⁻¹ • p, ?_, by simp [smul_smul, hs]⟩
    refine lt_of_mul_lt_mul_of_nonneg_left ?_ (norm_nonneg s)
    rw [← dist_sm

中文:
定理 Metric.smul_image_ball
  条件: {s : α} (hs : s != 0) (x : β) (ε : 实数)
  证明: by
  ext p
  simp_rw [Set.mem_image, mem_ball]
  constructor
  · rintro ⟨y, h1, rfl⟩
    simpa [dist_smul₀] using mul_lt_mul_of_pos_left h1 (norm_pos_iff.mpr hs)
  · refine fun h => ⟨s⁻¹ • p, ?_, by simp [smul_smul, hs]⟩
    refine lt_of_mul_lt_mul_of_nonneg_left ?_ (norm_nonneg s)
    rw [← dist_sm

Depends on / 依赖: Set.mem_image, lt_of_mul_lt_mul_of_nonneg_left, mem_ball, mem_image, mul_lt_mul_of_pos_left, norm_nonneg, norm_pos_iff, norm_pos_iff.mpr, simp_rw, smul_smul
-/
theorem Metric.smul_image_ball {s : α} (hs : s != 0) (x : β) (ε : Real) :
    (s • ·) '' ball x ε = ball (s • x) (‖s‖ * ε) := by
  ext p
  simp_rw [Set.mem_image, mem_ball]
  constructor
  · rintro ⟨y, h1, rfl⟩
    simpa [dist_smul₀] using mul_lt_mul_of_pos_left h1 (norm_pos_iff.mpr hs)
  · refine fun h => ⟨s⁻¹ • p, ?_, by simp [smul_smul, hs]⟩
    refine lt_of_mul_lt_mul_of_nonneg_left ?_ (norm_nonneg s)
    rw [← dist_smul₀]
    simpa [smul_smul, hs] using h

/--
theorem `Metric.smul_image_closedBall` / 定理 `Metric.smul_image_closedBall`

English:
theorem Metric.smul_image_closedBall
  given: {s : α} (hs : s != 0) (x : β) (ε : Real)
  proof: by
  ext p
  simp_rw [Set.mem_image, mem_closedBall]
  constructor
  · rintro ⟨y, h1, rfl⟩
    simpa [dist_smul₀] using mul_le_mul_of_nonneg_left h1 (norm_nonneg s)
  · refine fun h => ⟨s⁻¹ • p, ?_, by simp [smul_smul, hs]⟩
    refine le_of_mul_le_mul_of_pos_left ?_ (norm_pos_iff.mpr hs)
    rw [← d

中文:
定理 Metric.smul_image_closedBall
  条件: {s : α} (hs : s != 0) (x : β) (ε : 实数)
  证明: by
  ext p
  simp_rw [Set.mem_image, mem_closedBall]
  constructor
  · rintro ⟨y, h1, rfl⟩
    simpa [dist_smul₀] using mul_le_mul_of_nonneg_left h1 (norm_nonneg s)
  · refine fun h => ⟨s⁻¹ • p, ?_, by simp [smul_smul, hs]⟩
    refine le_of_mul_le_mul_of_pos_left ?_ (norm_pos_iff.mpr hs)
    rw [← d

Depends on / 依赖: Set.mem_image, le_of_mul_le_mul_of_pos_left, mem_closedBall, mem_image, mul_le_mul_of_nonneg_left, norm_nonneg, norm_pos_iff, norm_pos_iff.mpr, simp_rw, smul_smul
-/
theorem Metric.smul_image_closedBall {s : α} (hs : s != 0) (x : β) (ε : Real) :
    (s • ·) '' closedBall x ε = closedBall (s • x) (‖s‖ * ε) := by
  ext p
  simp_rw [Set.mem_image, mem_closedBall]
  constructor
  · rintro ⟨y, h1, rfl⟩
    simpa [dist_smul₀] using mul_le_mul_of_nonneg_left h1 (norm_nonneg s)
  · refine fun h => ⟨s⁻¹ • p, ?_, by simp [smul_smul, hs]⟩
    refine le_of_mul_le_mul_of_pos_left ?_ (norm_pos_iff.mpr hs)
    rw [← dist_smul₀]
    simpa [smul_smul, hs] using h

/--
theorem `Metric.smul_image_sphere` / 定理 `Metric.smul_image_sphere`

English:
theorem Metric.smul_image_sphere
  given: {s : α} (hs : s != 0) (x : β) (ε : Real)
  proof: by
  simp_rw [← Metric.closedBall_sdiff_ball, Set.image_sdiff (smul_right_injective β hs),
    smul_image_ball hs, smul_image_closedBall hs]

中文:
定理 Metric.smul_image_sphere
  条件: {s : α} (hs : s != 0) (x : β) (ε : 实数)
  证明: by
  simp_rw [← Metric.closedBall_sdiff_ball, Set.image_sdiff (smul_right_injective β hs),
    smul_image_ball hs, smul_image_closedBall hs]

Depends on / 依赖: Metric, Metric.closedBall_sdiff_ball, Set.image_sdiff, closedBall_sdiff_ball, image_sdiff, simp_rw, smul_image_ball, smul_image_closedBall, smul_right_injective
-/
theorem Metric.smul_image_sphere {s : α} (hs : s != 0) (x : β) (ε : Real) :
    (s • ·) '' sphere x ε = sphere (s • x) (‖s‖ * ε) := by
  simp_rw [← Metric.closedBall_sdiff_ball, Set.image_sdiff (smul_right_injective β hs),
    smul_image_ball hs, smul_image_closedBall hs]

end NormedDivisionRingModule
