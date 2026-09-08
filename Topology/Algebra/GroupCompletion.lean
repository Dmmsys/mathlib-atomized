/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
module

public import Mathlib.Topology.Algebra.UniformMulAction

/-!
# Completion of topological groups:

This file endows the completion of a topological abelian group with a group structure.
More precisely the instance `UniformSpace.Completion.addGroup` builds an abelian group structure
on the completion of an abelian group endowed with a compatible uniform structure.
Then the instance `UniformSpace.Completion.isUniformAddGroup` proves this group structure is
compatible with the completed uniform structure. The compatibility condition is `IsUniformAddGroup`.

## Main declarations:

Beyond the instances explained above (that don't have to be explicitly invoked),
the main constructions deal with continuous group morphisms.

* `AddMonoidHom.extension`: extends a continuous group morphism from `G`
  to a complete separated group `H` to `Completion G`.
* `AddMonoidHom.completion`: promotes a continuous group morphism
  from `G` to `H` into a continuous group morphism
  from `Completion G` to `Completion H`.
-/

@[expose] public section


noncomputable section

variable {M R α β : Type*}

section Group

open UniformSpace CauchyFilter Filter Set

variable [UniformSpace α]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Zero α] : Zero (Completion α) :=
  ⟨(0 : α)⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Neg α] : Neg (Completion α) :=
  ⟨Completion.map (fun a ↦ -a : α → α)⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Add α] : Add (Completion α) :=
  ⟨Completion.map₂ (· + ·)⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Sub α] : Sub (Completion α) :=
  ⟨Completion.map₂ Sub.sub⟩

@[norm_cast]
/-
**UniformSpace.Completion.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformSpace.Completion.coe_zero [Zero α] : ((0 : α) : Completion α) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem UniformSpace.Completion.coe_zero [Zero α] : ((0 : α) : Completion α) = 0 :=
  rfl
/-
**UniformSpace.Completion.coe_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpac
e.Completion`。
形式化陈述：∀ {α : Type u_3} [inst : UniformSpace α] [inst_1 : Zero α] [T0Space α] {x 
: α}, ↑x = 0 ↔ x = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `UniformSpace.Completion.coe_inj`：coe_inj [T0Space α] {a b : α} : (a : Co
mpletion α) = b ↔ a = b
-/
@[simp] lemma UniformSpace.Completion.coe_eq_zero_iff [Zero α] [T0Space α] {x : α} :
    (x : Completion α) = 0 ↔ x = 0 :=
  Completion.coe_inj

end Group

namespace UniformSpace.Completion

open UniformSpace

section Zero

/-
**UniformSpace.Completion.** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpace.Completion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [UniformSpace α] [MonoidWithZero M] [Zero α] [MulActionWithZero M α]
    [UniformContinuousConstSMul M α] : MulActionWithZero M (Completion α) where
  smul_zero := fun r ↦ by rw [← coe_zero, ← coe_smul, MulActionWithZero.smul_zero r]
  zero_smul :=
    ext' (continuous_const_smul _) continuous_const fun a ↦ by
      rw [← coe_smul, zero_smul, coe_zero]

end Zero

section IsUniformAddGroup

variable [UniformSpace α] [AddGroup α] [IsUniformAddGroup α]

@[norm_cast]
/-
**UniformSpace.Completion.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace.Comple
tion`。
形式化陈述：coe_neg (a : α) : ((-a : α) : Completion α) = -a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UniformSpace.Completion.map_coe`：map_coe (hf : UniformContinuous f) (a :
 α) : (Completion.map f) a = f a
· 使用定理 `uniformContinuous_neg`：∀ {α : Type u_1} [inst : UniformSpace α] [inst_1 
: AddGroup α] [IsUniformAddGroup α], UniformContinuous fun x => -x
-/
theorem coe_neg (a : α) : ((-a : α) : Completion α) = -a :=
  (map_coe uniformContinuous_neg a).symm

@[norm_cast]
/-
**UniformSpace.Completion.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace.Comple
tion`。
形式化陈述：coe_sub (a b : α) : ((a - b : α) : Completion α) = a - b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UniformSpace.Completion.map₂_coe_coe`：map₂_coe_coe (a : α) (b : β) (f : 
α -> β -> γ) (hf : UniformContinuous₂ f) : Completion.map₂ f (a : Completion α) 
(b : Completion β) = f a b
· 使用定理 `uniformContinuous_sub`：∀ {α : Type u_1} [inst : UniformSpace α] [inst_1 
: AddGroup α] [IsUniformAddGroup α],   UniformContinuous fun p => p.1 - p.2
-/
theorem coe_sub (a b : α) : ((a - b : α) : Completion α) = a - b :=
  (map₂_coe_coe a b Sub.sub uniformContinuous_sub).symm

@[norm_cast]
/-
**UniformSpace.Completion.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace.Comple
tion`。
形式化陈述：coe_add (a b : α) : ((a + b : α) : Completion α) = a + b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UniformSpace.Completion.map₂_coe_coe`：map₂_coe_coe (a : α) (b : β) (f : 
α -> β -> γ) (hf : UniformContinuous₂ f) : Completion.map₂ f (a : Completion α) 
(b : Completion β) = f a b
· 使用定理 `uniformContinuous_add`：∀ {α : Type u_1} [inst : UniformSpace α] [inst_1 
: AddGroup α] [IsUniformAddGroup α],   UniformContinuous fun p => p.1 + p.2
-/
theorem coe_add (a b : α) : ((a + b : α) : Completion α) = a + b :=
  (map₂_coe_coe a b (· + ·) uniformContinuous_add).symm
/-
**UniformSpace.Completion.** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpace.Completion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddMonoid (Completion α) where
  zero_add a :=
    Completion.induction_on a
      (isClosed_eq (continuous_map₂ continuous_const continuous_id) continuous_id) fun a ↦
      show 0 + (a : Completion α) = a by rw [← coe_zero, ← coe_add, zero_add]
  add_zero a :=
    Completion.induction_on a
      (isClosed_eq (continuous_map₂ continuous_id continuous_const) continuous_id) fun a ↦
      show (a : Completion α) + 0 = a by rw [← coe_zero, ← coe_add, add_zero]
  add_assoc := fun a b c ↦
    Completion.induction_on₃ a b c
      (isClosed_eq
        (continuous_map₂ (continuous_map₂ continuous_fst (by fun_prop)) (by fun_prop))
        (continuous_map₂ continuous_fst (continuous_map₂ (by fun_prop) (by fun_prop))))
      fun a b c ↦
      show (a : Completion α) + b + c = a + (b + c) by repeat' rw_mod_cast [add_assoc]
  nsmul_zero a :=
    Completion.induction_on a (isClosed_eq continuous_map continuous_const) fun a ↦
      show 0 • (a : Completion α) = 0 by rw [← coe_smul, ← coe_zero, zero_smul]
  nsmul_succ n a :=
    Completion.induction_on a
      (isClosed_eq continuous_map <| continuous_map₂ continuous_map continuous_id) fun a ↦
      show (n + 1) • (a : Completion α) = n • (a : Completion α) + (a : Completion α) by
        rw [← coe_smul, succ_nsmul, coe_add, coe_smul]
/-
**UniformSpace.Completion.** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpace.Completion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SubNegMonoid (Completion α) where
  sub_eq_add_neg a b :=
    Completion.induction_on₂ a b
      (isClosed_eq (continuous_map₂ continuous_fst continuous_snd)
        (continuous_map₂ continuous_fst (Completion.continuous_map.comp continuous_snd)))
      fun a b ↦ mod_cast congr_arg ((↑) : α → Completion α) (sub_eq_add_neg a b)
  zsmul_zero' a :=
    Completion.induction_on a (isClosed_eq continuous_map continuous_const) fun a ↦
      show (0 : ℤ) • (a : Completion α) = 0 by rw [← coe_smul, ← coe_zero, zero_smul]
  zsmul_succ' n a :=
    Completion.induction_on a
      (isClosed_eq continuous_map <| continuous_map₂ continuous_map continuous_id) fun a ↦
        show (n.succ : ℤ) • (a : Completion α) = _ by
          rw [← coe_smul, show (n.succ : ℤ) • a = (n : ℤ) • a + a from
            SubNegMonoid.zsmul_succ' n a, coe_add, coe_smul]
  zsmul_neg' n a :=
    Completion.induction_on a
      (isClosed_eq continuous_map <| Completion.continuous_map.comp continuous_map) fun a ↦
        show (Int.negSucc n) • (a : Completion α) = _ by
          rw [← coe_smul, show (Int.negSucc n) • a = -((n.succ : ℤ) • a) from
            SubNegMonoid.zsmul_neg' n a, coe_neg, coe_smul]
/-
**UniformSpace.Completion.addGroup** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpace.Compl
etion`。
形式化陈述：addGroup : AddGroup (Completion α) where neg_add_cancel a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addGroup : AddGroup (Completion α) where
  neg_add_cancel a :=
    Completion.induction_on a
      (isClosed_eq (continuous_map₂ Completion.continuous_map continuous_id) continuous_const)
      fun a ↦
      show -(a : Completion α) + a = 0 by
        rw_mod_cast [neg_add_cancel]
        rfl
/-
**UniformSpace.Completion.isUniformAddGroup** 是 Mathlib 中的一个实例，位于命名空间 `UniformSp
ace.Completion`。
形式化陈述：isUniformAddGroup : IsUniformAddGroup (Completion α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.Completion.uniformContinuous_map₂`：uniformContinuous_map₂ (
f : α -> β -> γ) : UniformContinuous₂ (Completion.map₂ f)
-/
instance isUniformAddGroup : IsUniformAddGroup (Completion α) :=
  ⟨uniformContinuous_map₂ Sub.sub⟩
/-
**UniformSpace.Completion.** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpace.Completion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M} [Monoid M] [DistribMulAction M α] [UniformContinuousConstSMul M α] :
    DistribMulAction M (Completion α) where
  smul_add r x y :=
    induction_on₂ x y
      (isClosed_eq ((continuous_fst.fun_add continuous_snd).fun_const_smul _)
        ((continuous_fst.fun_const_smul _).fun_add (continuous_snd.fun_const_smul _)))
      fun a b ↦ by simp only [← coe_add, ← coe_smul, smul_add]
  smul_zero := fun r ↦ by rw [← coe_zero, ← coe_smul, smul_zero r]

/-- The map from a group to its completion as a group hom. -/
@[simps]
/-
**UniformSpace.Completion.toCompl** 是 Mathlib 中的一个定义，位于命名空间 `UniformSpace.Comple
tion`。
形式化陈述：toCompl : α ->+ Completion α where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.Completion.coe_add`：coe_add (a b : α) : ((a + b : α) : Comp
letion α) = a + b

--- 原说明 ---
The map from a group to its completion as a group hom.
-/
def toCompl : α →+ Completion α where
  toFun := (↑)
  map_add' := coe_add
  map_zero' := coe_zero
/-
**UniformSpace.Completion.continuous_toCompl** 是 Mathlib 中的一个定理，位于命名空间 `UniformS
pace.Completion`。
形式化陈述：continuous_toCompl : Continuous (toCompl : α -> Completion α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.Completion.continuous_coe`：continuous_coe : Continuous ((↑)
 : α -> Completion α)
-/
theorem continuous_toCompl : Continuous (toCompl : α → Completion α) :=
  continuous_coe α

variable (α) in
/-
**UniformSpace.Completion.isDenseInducing_toCompl** 是 Mathlib 中的一个定理，位于命名空间 `Uni
formSpace.Completion`。
形式化陈述：isDenseInducing_toCompl : IsDenseInducing (toCompl : α -> Completion α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.Completion.isDenseInducing_coe`：isDenseInducing_coe : IsDen
seInducing ((↑) : α -> Completion α)
-/
theorem isDenseInducing_toCompl : IsDenseInducing (toCompl : α → Completion α) :=
  isDenseInducing_coe

end IsUniformAddGroup

section UniformAddCommGroup

variable [UniformSpace α] [AddCommGroup α] [IsUniformAddGroup α]

/-
**UniformSpace.Completion.instAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpa
ce.Completion`。
形式化陈述：instAddCommGroup : AddCommGroup (Completion α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommGroup : AddCommGroup (Completion α) :=
  { (inferInstance : AddGroup <| Completion α) with
    add_comm a b :=
      Completion.induction_on₂ a b
        (isClosed_eq (by fun_prop) (by fun_prop))
        fun x y ↦ by
        change (x : Completion α) + ↑y = ↑y + ↑x
        rw [← coe_add, ← coe_add, add_comm] }
/-
**UniformSpace.Completion.instModule** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpace.Com
pletion`。
形式化陈述：instModule [Semiring R] [Module R α] [UniformContinuousConstSMul R α] : Mo
dule R (Completion α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instModule [Semiring R] [Module R α] [UniformContinuousConstSMul R α] :
    Module R (Completion α) :=
  { (inferInstance : DistribMulAction R <| Completion α),
    (inferInstance : MulActionWithZero R <| Completion α) with
    add_smul := fun a b ↦
      ext' (continuous_const_smul _) ((continuous_const_smul _).add (continuous_const_smul _))
        fun x ↦ by
          rw [← coe_smul, add_smul, coe_add, coe_smul, coe_smul] }

end UniformAddCommGroup

end UniformSpace.Completion

section AddMonoidHom

variable [UniformSpace α] [AddGroup α] [IsUniformAddGroup α] [UniformSpace β] [AddGroup β]
  [IsUniformAddGroup β]

open UniformSpace UniformSpace.Completion

/-- Extension to the completion of a continuous group hom. -/
/-
**AddMonoidHom.extension** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddMonoidHom.extension [CompleteSpace β] [T0Space β] (f : α ->+ β) (hf : C
ontinuous f) : Completion α ->+ β
参数：f : α ->+ β；hf : Continuous f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extension to the completion of a continuous group hom.
-/
def AddMonoidHom.extension [CompleteSpace β] [T0Space β] (f : α →+ β) (hf : Continuous f) :
    Completion α →+ β :=
  have hf : UniformContinuous f := uniformContinuous_addMonoidHom_of_continuous hf
  { toFun := Completion.extension f
    map_zero' := by rw [← coe_zero, extension_coe hf, f.map_zero]
    map_add' a b :=
      Completion.induction_on₂ a b
        (isClosed_eq (by fun_prop) (by fun_prop))
        fun a b ↦
        show Completion.extension f _ = Completion.extension f _ + Completion.extension f _ by
        rw_mod_cast [extension_coe hf, extension_coe hf, extension_coe hf, f.map_add] }
/-
**AddMonoidHom.extension_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddMonoidHom.extension_coe [CompleteSpace β] [T0Space β] (f : α ->+ β) (hf
 : Continuous f) (a : α) : f.extension hf a = f a
参数：f : α ->+ β；hf : Continuous f；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.Completion.extension_coe`：extension_coe [T0Space β] (hf : U
niformContinuous f) (a : α) : (Completion.extension f) a = f a
· 使用定理 `uniformContinuous_addMonoidHom_of_continuous`：∀ {α : Type u_1} {β : Type
 u_2} [inst : UniformSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α] {hom :
 Type u_3}   [inst_3 : UniformSpac…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem AddMonoidHom.extension_coe [CompleteSpace β] [T0Space β] (f : α →+ β)
    (hf : Continuous f) (a : α) : f.extension hf a = f a :=
  UniformSpace.Completion.extension_coe (uniformContinuous_addMonoidHom_of_continuous hf) a

@[continuity, fun_prop]
/-
**AddMonoidHom.continuous_extension** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddMonoidHom.continuous_extension [CompleteSpace β] [T0Space β] (f : α ->+
 β) (hf : Continuous f) : Continuous (f.extension hf)
参数：f : α ->+ β；hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.Completion.continuous_extension`：continuous_extension : Con
tinuous (Completion.extension f)
-/
theorem AddMonoidHom.continuous_extension [CompleteSpace β] [T0Space β] (f : α →+ β)
    (hf : Continuous f) : Continuous (f.extension hf) :=
  UniformSpace.Completion.continuous_extension

/-- Completion of a continuous group hom, as a group hom. -/
/-
**AddMonoidHom.completion** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddMonoidHom.completion (f : α ->+ β) (hf : Continuous f) : Completion α -
>+ Completion β
参数：f : α ->+ β；hf : Continuous f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Completion of a continuous group hom, as a group hom.
-/
def AddMonoidHom.completion (f : α →+ β) (hf : Continuous f) : Completion α →+ Completion β :=
  (toCompl.comp f).extension (continuous_toCompl.comp hf)

@[continuity, fun_prop]
/-
**AddMonoidHom.continuous_completion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddMonoidHom.continuous_completion (f : α ->+ β) (hf : Continuous f) : Con
tinuous (AddMonoidHom.completion f hf : Completion α -> Completion β)
参数：f : α ->+ β；hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.Completion.continuous_map`：continuous_map : Continuous (Com
pletion.map f)
-/
theorem AddMonoidHom.continuous_completion (f : α →+ β) (hf : Continuous f) :
    Continuous (AddMonoidHom.completion f hf : Completion α → Completion β) :=
  continuous_map

@[simp]
/-
**AddMonoidHom.completion_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddMonoidHom.completion_coe (f : α ->+ β) (hf : Continuous f) (a : α) : Ad
dMonoidHom.completion f hf a = f a
参数：f : α ->+ β；hf : Continuous f；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.Completion.map_coe`：map_coe (hf : UniformContinuous f) (a :
 α) : (Completion.map f) a = f a
· 使用定理 `uniformContinuous_addMonoidHom_of_continuous`：∀ {α : Type u_1} {β : Type
 u_2} [inst : UniformSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α] {hom :
 Type u_3}   [inst_3 : UniformSpac…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem AddMonoidHom.completion_coe (f : α →+ β) (hf : Continuous f) (a : α) :
    AddMonoidHom.completion f hf a = f a :=
  map_coe (uniformContinuous_addMonoidHom_of_continuous hf) a
/-
**AddMonoidHom.completion_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddMonoidHom.completion_zero : AddMonoidHom.completion (0 : α ->+ β) conti
nuous_const = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `UniformSpace.Completion.induction_on`：induction_on {p : Completion α -> 
Prop} (a : Completion α) (hp : IsClosed { a | p a }) (ih : forall a : α, p a) : 
p a
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `AddMonoidHom.continuous_completion`：AddMonoidHom.continuous_completion (
f : α ->+ β) (hf : Continuous f) : Continuous (AddMonoidHom.completion f hf : Co
mpletion α -> Completion…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidHom.completion_coe`：AddMonoidHom.completion_coe (f : α ->+ β) (
hf : Continuous f) (a : α) : AddMonoidHom.completion f hf a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem AddMonoidHom.completion_zero :
    AddMonoidHom.completion (0 : α →+ β) continuous_const = 0 := by
  ext x
  refine Completion.induction_on x ?_ ?_
  · apply isClosed_eq (AddMonoidHom.continuous_completion (0 : α →+ β) continuous_const)
    exact continuous_const
  · simp [(0 : α →+ β).completion_coe continuous_const, coe_zero]
/-
**AddMonoidHom.completion_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddMonoidHom.completion_add {γ : Type*} [AddCommGroup γ] [UniformSpace γ] 
[IsUniformAddGroup γ] (f g : α ->+ γ) (hf : Continuous f) (hg : Continuous g) : 
AddMonoidHom.completion (f + g) (hf.add hg) = AddMonoidHom.completion f hf + Add
MonoidHom.completion g hg
参数：f g : α ->+ γ；hf : Continuous f；hg : Continuous g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1 : A
dd M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f g : X 
→ M}…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `UniformSpace.Completion.induction_on`：induction_on {p : Completion α -> 
Prop} (a : Completion α) (hp : IsClosed { a | p a }) (ih : forall a : α, p a) : 
p a
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `AddMonoidHom.continuous_completion`：AddMonoidHom.continuous_completion (
f : α ->+ β) (hf : Continuous f) : Continuous (AddMonoidHom.completion f hf : Co
mpletion α -> Completion…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidHom.completion_coe`：AddMonoidHom.completion_coe (f : α ->+ β) (
hf : Continuous f) (a : α) : AddMonoidHom.completion f hf a = f a
· 使用定理 `UniformSpace.Completion.coe_add`：coe_add (a b : α) : ((a + b : α) : Comp
letion α) = a + b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem AddMonoidHom.completion_add {γ : Type*} [AddCommGroup γ] [UniformSpace γ]
    [IsUniformAddGroup γ] (f g : α →+ γ) (hf : Continuous f) (hg : Continuous g) :
    AddMonoidHom.completion (f + g) (hf.add hg) =
    AddMonoidHom.completion f hf + AddMonoidHom.completion g hg := by
  have hfg := hf.add hg
  ext x
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_eq ((f + g).continuous_completion hfg)
      ((f.continuous_completion hf).add (g.continuous_completion hg))
  · simp [(f + g).completion_coe hfg, coe_add, f.completion_coe hf, g.completion_coe hg]

end AddMonoidHom

