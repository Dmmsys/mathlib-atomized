/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth
-/
module

public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Multiplicative actions of/on balls and spheres

Let `E` be a normed vector space over a normed field `𝕜`. In this file we define the following
multiplicative actions.

- The closed unit ball in `𝕜` acts on open balls and closed balls centered at `0` in `E`.
- The unit sphere in `𝕜` acts on open balls, closed balls, and spheres centered at `0` in `E`.
-/

public section


open Metric Set

variable {𝕜 𝕜' E : Type*} [NormedField 𝕜] [NormedField 𝕜'] [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜' E] {r : ℝ}

section ClosedBall

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul (closedBall (0 : 𝕜) 1) (ball (0 : E) r) where
  smul c x :=
    ⟨(c : 𝕜) • ↑x,
      mem_ball_zero_iff.2 <| by
        simpa only [norm_smul, one_mul] using
          mul_lt_mul' (mem_closedBall_zero_iff.1 c.2) (mem_ball_zero_iff.1 x.2) (norm_nonneg _)
            one_pos⟩
/-
**mulActionClosedBallBall** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：mulActionClosedBallBall : MulAction (closedBall (0 : 𝕜) 1) (ball (0 : E) r
) where one_smul _c₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulActionClosedBallBall : MulAction (closedBall (0 : 𝕜) 1) (ball (0 : E) r) where
  one_smul _c₂ := Subtype.ext <| one_smul 𝕜 _
  mul_smul _ _ _ := Subtype.ext <| mul_smul _ _ _
/-
**continuousSMul_closedBall_ball** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：continuousSMul_closedBall_ball : ContinuousSMul (closedBall (0 : 𝕜) 1) (ba
ll (0 : E) r)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
-/
instance continuousSMul_closedBall_ball : ContinuousSMul (closedBall (0 : 𝕜) 1) (ball (0 : E) r) :=
  ⟨Continuous.subtype_mk (by fun_prop) _⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul (closedBall (0 : 𝕜) 1) (closedBall (0 : E) r) where
  smul c x :=
    ⟨(c : 𝕜) • ↑x,
      mem_closedBall_zero_iff.2 <| by
        simpa only [norm_smul, one_mul] using
          mul_le_mul (mem_closedBall_zero_iff.1 c.2) (mem_closedBall_zero_iff.1 x.2) (norm_nonneg _)
            zero_le_one⟩
/-
**mulActionClosedBallClosedBall** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：mulActionClosedBallClosedBall : MulAction (closedBall (0 : 𝕜) 1) (closedBa
ll (0 : E) r) where one_smul _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulActionClosedBallClosedBall :
    MulAction (closedBall (0 : 𝕜) 1) (closedBall (0 : E) r) where
  one_smul _ := Subtype.ext <| one_smul 𝕜 _
  mul_smul _ _ _ := Subtype.ext <| mul_smul _ _ _
/-
**continuousSMul_closedBall_closedBall** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：continuousSMul_closedBall_closedBall : ContinuousSMul (closedBall (0 : 𝕜) 
1) (closedBall (0 : E) r)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
-/
instance continuousSMul_closedBall_closedBall :
    ContinuousSMul (closedBall (0 : 𝕜) 1) (closedBall (0 : E) r) :=
  ⟨Continuous.subtype_mk (by fun_prop) _⟩

end ClosedBall

section Sphere

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul (sphere (0 : 𝕜) 1) (ball (0 : E) r) where
  smul c x := inclusion sphere_subset_closedBall c • x
/-
**mulActionSphereBall** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：mulActionSphereBall : MulAction (sphere (0 : 𝕜) 1) (ball (0 : E) r) where 
one_smul _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulActionSphereBall : MulAction (sphere (0 : 𝕜) 1) (ball (0 : E) r) where
  one_smul _ := Subtype.ext <| one_smul _ _
  mul_smul _ _ _ := Subtype.ext <| mul_smul _ _ _
/-
**continuousSMul_sphere_ball** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：continuousSMul_sphere_ball : ContinuousSMul (sphere (0 : 𝕜) 1) (ball (0 : 
E) r)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
-/
instance continuousSMul_sphere_ball : ContinuousSMul (sphere (0 : 𝕜) 1) (ball (0 : E) r) :=
  ⟨Continuous.subtype_mk (by fun_prop) _⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul (sphere (0 : 𝕜) 1) (closedBall (0 : E) r) where
  smul c x := inclusion sphere_subset_closedBall c • x
/-
**mulActionSphereClosedBall** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：mulActionSphereClosedBall : MulAction (sphere (0 : 𝕜) 1) (closedBall (0 : 
E) r) where one_smul _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulActionSphereClosedBall : MulAction (sphere (0 : 𝕜) 1) (closedBall (0 : E) r) where
  one_smul _ := Subtype.ext <| one_smul _ _
  mul_smul _ _ _ := Subtype.ext <| mul_smul _ _ _
/-
**continuousSMul_sphere_closedBall** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：continuousSMul_sphere_closedBall : ContinuousSMul (sphere (0 : 𝕜) 1) (clos
edBall (0 : E) r)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
-/
instance continuousSMul_sphere_closedBall :
    ContinuousSMul (sphere (0 : 𝕜) 1) (closedBall (0 : E) r) :=
  ⟨Continuous.subtype_mk (by fun_prop) _⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul (sphere (0 : 𝕜) 1) (sphere (0 : E) r) where
  smul c x :=
    ⟨(c : 𝕜) • ↑x,
      mem_sphere_zero_iff_norm.2 <| by
        rw [norm_smul, mem_sphere_zero_iff_norm.1 c.coe_prop, mem_sphere_zero_iff_norm.1 x.coe_prop,
          one_mul]⟩
/-
**mulActionSphereSphere** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：mulActionSphereSphere : MulAction (sphere (0 : 𝕜) 1) (sphere (0 : E) r) wh
ere one_smul _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulActionSphereSphere : MulAction (sphere (0 : 𝕜) 1) (sphere (0 : E) r) where
  one_smul _ := Subtype.ext <| one_smul _ _
  mul_smul _ _ _ := Subtype.ext <| mul_smul _ _ _
/-
**continuousSMul_sphere_sphere** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：continuousSMul_sphere_sphere : ContinuousSMul (sphere (0 : 𝕜) 1) (sphere (
0 : E) r)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
-/
instance continuousSMul_sphere_sphere : ContinuousSMul (sphere (0 : 𝕜) 1) (sphere (0 : E) r) :=
  ⟨Continuous.subtype_mk (by fun_prop) _⟩

end Sphere

section IsScalarTower

variable [NormedAlgebra 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' E]

/-
**isScalarTower_closedBall_closedBall_closedBall** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isScalarTower_closedBall_closedBall_closedBall : IsScalarTower (closedBall
 (0 : 𝕜) 1) (closedBall (0 : 𝕜') 1) (closedBall (0 : E) r)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
instance isScalarTower_closedBall_closedBall_closedBall :
    IsScalarTower (closedBall (0 : 𝕜) 1) (closedBall (0 : 𝕜') 1) (closedBall (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩
/-
**isScalarTower_closedBall_closedBall_ball** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isScalarTower_closedBall_closedBall_ball : IsScalarTower (closedBall (0 : 
𝕜) 1) (closedBall (0 : 𝕜') 1) (ball (0 : E) r)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
instance isScalarTower_closedBall_closedBall_ball :
    IsScalarTower (closedBall (0 : 𝕜) 1) (closedBall (0 : 𝕜') 1) (ball (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩
/-
**isScalarTower_sphere_closedBall_closedBall** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isScalarTower_sphere_closedBall_closedBall : IsScalarTower (sphere (0 : 𝕜)
 1) (closedBall (0 : 𝕜') 1) (closedBall (0 : E) r)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
instance isScalarTower_sphere_closedBall_closedBall :
    IsScalarTower (sphere (0 : 𝕜) 1) (closedBall (0 : 𝕜') 1) (closedBall (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩
/-
**isScalarTower_sphere_closedBall_ball** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isScalarTower_sphere_closedBall_ball : IsScalarTower (sphere (0 : 𝕜) 1) (c
losedBall (0 : 𝕜') 1) (ball (0 : E) r)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
instance isScalarTower_sphere_closedBall_ball :
    IsScalarTower (sphere (0 : 𝕜) 1) (closedBall (0 : 𝕜') 1) (ball (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩
/-
**isScalarTower_sphere_sphere_closedBall** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isScalarTower_sphere_sphere_closedBall : IsScalarTower (sphere (0 : 𝕜) 1) 
(sphere (0 : 𝕜') 1) (closedBall (0 : E) r)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
instance isScalarTower_sphere_sphere_closedBall :
    IsScalarTower (sphere (0 : 𝕜) 1) (sphere (0 : 𝕜') 1) (closedBall (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩
/-
**isScalarTower_sphere_sphere_ball** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isScalarTower_sphere_sphere_ball : IsScalarTower (sphere (0 : 𝕜) 1) (spher
e (0 : 𝕜') 1) (ball (0 : E) r)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
instance isScalarTower_sphere_sphere_ball :
    IsScalarTower (sphere (0 : 𝕜) 1) (sphere (0 : 𝕜') 1) (ball (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩
/-
**isScalarTower_sphere_sphere_sphere** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isScalarTower_sphere_sphere_sphere : IsScalarTower (sphere (0 : 𝕜) 1) (sph
ere (0 : 𝕜') 1) (sphere (0 : E) r)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
instance isScalarTower_sphere_sphere_sphere :
    IsScalarTower (sphere (0 : 𝕜) 1) (sphere (0 : 𝕜') 1) (sphere (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩
/-
**isScalarTower_sphere_ball_ball** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isScalarTower_sphere_ball_ball : IsScalarTower (sphere (0 : 𝕜) 1) (ball (0
 : 𝕜') 1) (ball (0 : 𝕜') 1)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
instance isScalarTower_sphere_ball_ball :
    IsScalarTower (sphere (0 : 𝕜) 1) (ball (0 : 𝕜') 1) (ball (0 : 𝕜') 1) :=
  ⟨fun a b c => Subtype.ext <| smul_assoc (a : 𝕜) (b : 𝕜') (c : 𝕜')⟩
/-
**isScalarTower_closedBall_ball_ball** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isScalarTower_closedBall_ball_ball : IsScalarTower (closedBall (0 : 𝕜) 1) 
(ball (0 : 𝕜') 1) (ball (0 : 𝕜') 1)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
instance isScalarTower_closedBall_ball_ball :
    IsScalarTower (closedBall (0 : 𝕜) 1) (ball (0 : 𝕜') 1) (ball (0 : 𝕜') 1) :=
  ⟨fun a b c => Subtype.ext <| smul_assoc (a : 𝕜) (b : 𝕜') (c : 𝕜')⟩

end IsScalarTower

section SMulCommClass

variable [SMulCommClass 𝕜 𝕜' E]

/-
**instSMulCommClass_closedBall_closedBall_closedBall** 是 Mathlib 中的一个实例，位于命名空间 `
`。
形式化陈述：instSMulCommClass_closedBall_closedBall_closedBall : SMulCommClass (closed
Ball (0 : 𝕜) 1) (closedBall (0 : 𝕜') 1) (closedBall (0 : E) r)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance instSMulCommClass_closedBall_closedBall_closedBall :
    SMulCommClass (closedBall (0 : 𝕜) 1) (closedBall (0 : 𝕜') 1) (closedBall (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩
/-
**instSMulCommClass_closedBall_closedBall_ball** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instSMulCommClass_closedBall_closedBall_ball : SMulCommClass (closedBall (
0 : 𝕜) 1) (closedBall (0 : 𝕜') 1) (ball (0 : E) r)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance instSMulCommClass_closedBall_closedBall_ball :
    SMulCommClass (closedBall (0 : 𝕜) 1) (closedBall (0 : 𝕜') 1) (ball (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩
/-
**instSMulCommClass_sphere_closedBall_closedBall** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instSMulCommClass_sphere_closedBall_closedBall : SMulCommClass (sphere (0 
: 𝕜) 1) (closedBall (0 : 𝕜') 1) (closedBall (0 : E) r)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance instSMulCommClass_sphere_closedBall_closedBall :
    SMulCommClass (sphere (0 : 𝕜) 1) (closedBall (0 : 𝕜') 1) (closedBall (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩
/-
**instSMulCommClass_sphere_closedBall_ball** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instSMulCommClass_sphere_closedBall_ball : SMulCommClass (sphere (0 : 𝕜) 1
) (closedBall (0 : 𝕜') 1) (ball (0 : E) r)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance instSMulCommClass_sphere_closedBall_ball :
    SMulCommClass (sphere (0 : 𝕜) 1) (closedBall (0 : 𝕜') 1) (ball (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩
/-
**instSMulCommClass_sphere_ball_ball** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instSMulCommClass_sphere_ball_ball [NormedAlgebra 𝕜 𝕜'] : SMulCommClass (s
phere (0 : 𝕜) 1) (ball (0 : 𝕜') 1) (ball (0 : 𝕜') 1)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
instance instSMulCommClass_sphere_ball_ball [NormedAlgebra 𝕜 𝕜'] :
    SMulCommClass (sphere (0 : 𝕜) 1) (ball (0 : 𝕜') 1) (ball (0 : 𝕜') 1) :=
  ⟨fun a b c => Subtype.ext <| smul_comm (a : 𝕜) (b : 𝕜') (c : 𝕜')⟩
/-
**instSMulCommClass_sphere_sphere_closedBall** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instSMulCommClass_sphere_sphere_closedBall : SMulCommClass (sphere (0 : 𝕜)
 1) (sphere (0 : 𝕜') 1) (closedBall (0 : E) r)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance instSMulCommClass_sphere_sphere_closedBall :
    SMulCommClass (sphere (0 : 𝕜) 1) (sphere (0 : 𝕜') 1) (closedBall (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩
/-
**instSMulCommClass_sphere_sphere_ball** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instSMulCommClass_sphere_sphere_ball : SMulCommClass (sphere (0 : 𝕜) 1) (s
phere (0 : 𝕜') 1) (ball (0 : E) r)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance instSMulCommClass_sphere_sphere_ball :
    SMulCommClass (sphere (0 : 𝕜) 1) (sphere (0 : 𝕜') 1) (ball (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩
/-
**instSMulCommClass_sphere_sphere_sphere** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instSMulCommClass_sphere_sphere_sphere : SMulCommClass (sphere (0 : 𝕜) 1) 
(sphere (0 : 𝕜') 1) (sphere (0 : E) r)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance instSMulCommClass_sphere_sphere_sphere :
    SMulCommClass (sphere (0 : 𝕜) 1) (sphere (0 : 𝕜') 1) (sphere (0 : E) r) :=
  ⟨fun a b c => Subtype.ext <| smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

end SMulCommClass

variable (𝕜)
variable [CharZero 𝕜]

include 𝕜 in
/-
**ne_neg_of_mem_sphere** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ne_neg_of_mem_sphere {r : Real} (hr : r != 0) (x : sphere (0 : E) r) : x !
= -x
参数：hr : r != 0；x : sphere (0 : E) r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsAddTorsionFree.of_isTorsionFree`：IsAddTorsionFree.of_isTorsionFree : I
sAddTorsionFree M where nsmul_right_injective n hn
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `ne_zero_of_mem_sphere`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {r
 : ℝ}, r ≠ 0 → ∀ (x : ↑(Metric.sphere 0 r)), ↑x ≠ 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `self_eq_neg`：∀ {G : Type u_2} [inst : AddGroup G] [IsAddTorsionFree G] {
a : G}, a = -a ↔ a = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem ne_neg_of_mem_sphere {r : ℝ} (hr : r ≠ 0) (x : sphere (0 : E) r) : x ≠ -x :=
  have : IsAddTorsionFree E := .of_isTorsionFree 𝕜 E
  fun h => ne_zero_of_mem_sphere hr x (self_eq_neg.mp (by (conv_lhs => rw [h]); rfl))

include 𝕜 in
/-
**ne_neg_of_mem_unit_sphere** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ne_neg_of_mem_unit_sphere (x : sphere (0 : E) 1) : x != -x
参数：x : sphere (0 : E) 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_neg_of_mem_sphere`：ne_neg_of_mem_sphere {r : Real} (hr : r != 0) (x :
 sphere (0 : E) r) : x != -x
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem ne_neg_of_mem_unit_sphere (x : sphere (0 : E) 1) : x ≠ -x :=
  ne_neg_of_mem_sphere 𝕜 one_ne_zero x
