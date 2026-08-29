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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: α] : Zero (Completion α)
  body: ⟨(0 : α)⟩

中文:
实例 [零
  签名: α] : 零 (完备化 α)
  定义体: ⟨(0 : α)⟩
-/
instance [Zero α] : Zero (Completion α) :=
  ⟨(0 : α)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Neg
  signature: α] : Neg (Completion α)
  body: ⟨Completion.map (fun a => -a : α -> α)⟩

中文:
实例 [取负
  签名: α] : 取负 (完备化 α)
  定义体: ⟨Completion.map (fun a => -a : α -> α)⟩

Depends on / 依赖: Completion, Completion.map
-/
instance [Neg α] : Neg (Completion α) :=
  ⟨Completion.map (fun a => -a : α -> α)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Add
  signature: α] : Add (Completion α)
  body: ⟨Completion.map₂ (· + ·)⟩

中文:
实例 [加法
  签名: α] : 加法 (完备化 α)
  定义体: ⟨Completion.map₂ (· + ·)⟩

Depends on / 依赖: Completion, Completion.map
-/
instance [Add α] : Add (Completion α) :=
  ⟨Completion.map₂ (· + ·)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Sub
  signature: α] : Sub (Completion α)
  body: ⟨Completion.map₂ Sub.sub⟩

@[norm_cast]

中文:
实例 [减法
  签名: α] : 减法 (完备化 α)
  定义体: ⟨Completion.map₂ Sub.sub⟩

@[norm_cast]

Depends on / 依赖: Completion, Completion.map, Sub.sub
-/
instance [Sub α] : Sub (Completion α) :=
  ⟨Completion.map₂ Sub.sub⟩

@[norm_cast]
/--
theorem `UniformSpace.Completion.coe_zero` / 定理 `UniformSpace.Completion.coe_zero`

English:
theorem UniformSpace.Completion.coe_zero
  given: [Zero α]
  statement: ((0 : α) : Completion α) = 0
  proof: rfl

中文:
定理 一致空间.完备化.coe_zero
  条件: [零 α]
  结论: ((0 : α) : 完备化 α) = 0
  证明: rfl
-/
theorem UniformSpace.Completion.coe_zero [Zero α] : ((0 : α) : Completion α) = 0 :=
  rfl

/--
lemma `UniformSpace.Completion.coe_eq_zero_iff` / 引理 `UniformSpace.Completion.coe_eq_zero_iff`

English:
lemma UniformSpace.Completion.coe_eq_zero_iff
  given: [Zero α] [T0Space α] {x : α}
  proof: Completion.coe_inj

中文:
引理 一致空间.完备化.coe_eq_zero_iff
  条件: [零 α] [T0空间 α] {x : α}
  证明: Completion.coe_inj
-/
@[simp] lemma UniformSpace.Completion.coe_eq_zero_iff [Zero α] [T0Space α] {x : α} :
    (x : Completion α) = 0 ↔ x = 0 :=
  Completion.coe_inj

end Group

namespace UniformSpace.Completion

open UniformSpace

section Zero

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [UniformSpace
  signature: α] [MonoidWithZero M] [Zero α] [MulActionWithZero M α]
  body: fun r => by rw [← coe_zero, ← coe_smul, MulActionWithZero.smul_zero r]
  zero_smul :=
    ext' (continuous_const_smul _) continuous_const fun a => by
      rw [← coe_smul]; rw [zero_smul]; rw [coe_zero]

中文:
实例 [一致空间
  签名: α] [带零幺半群 M] [零 α] [带零乘法作用 M α]
  定义体: fun r => by rw [← coe_zero, ← coe_smul, MulActionWithZero.smul_zero r]
  zero_smul :=
    ext' (continuous_const_smul _) continuous_const fun a => by
      rw [← coe_smul]; rw [zero_smul]; rw [coe_zero]

Depends on / 依赖: MulActionWithZero, MulActionWithZero.smul_zero, coe_smul, coe_zero, smul_zero
-/
instance [UniformSpace α] [MonoidWithZero M] [Zero α] [MulActionWithZero M α]
    [UniformContinuousConstSMul M α] : MulActionWithZero M (Completion α) where
  smul_zero := fun r => by rw [← coe_zero, ← coe_smul, MulActionWithZero.smul_zero r]
  zero_smul :=
    ext' (continuous_const_smul _) continuous_const fun a => by
      rw [← coe_smul]; rw [zero_smul]; rw [coe_zero]

end Zero

section IsUniformAddGroup

variable [UniformSpace α] [AddGroup α] [IsUniformAddGroup α]

@[norm_cast]
/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  given: (a : α)
  statement: ((-a : α) : Completion α) = -a
  proof: (map_coe uniformContinuous_neg a).symm

@[norm_cast]

中文:
定理 coe_neg
  条件: (a : α)
  结论: ((-a : α) : 完备化 α) = -a
  证明: (map_coe uniformContinuous_neg a).symm

@[norm_cast]

Depends on / 依赖: map_coe, uniformContinuous_neg
-/
theorem coe_neg (a : α) : ((-a : α) : Completion α) = -a :=
  (map_coe uniformContinuous_neg a).symm

@[norm_cast]
/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  given: (a b : α)
  statement: ((a - b : α) : Completion α) = a - b
  proof: (map₂_coe_coe a b Sub.sub uniformContinuous_sub).symm

@[norm_cast]

中文:
定理 coe_sub
  条件: (a b : α)
  结论: ((a - b : α) : 完备化 α) = a - b
  证明: (map₂_coe_coe a b Sub.sub uniformContinuous_sub).symm

@[norm_cast]

Depends on / 依赖: Sub.sub, uniformContinuous_sub
-/
theorem coe_sub (a b : α) : ((a - b : α) : Completion α) = a - b :=
  (map₂_coe_coe a b Sub.sub uniformContinuous_sub).symm

@[norm_cast]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: (a b : α)
  statement: ((a + b : α) : Completion α) = a + b
  proof: (map₂_coe_coe a b (· + ·) uniformContinuous_add).symm

中文:
定理 coe_add
  条件: (a b : α)
  结论: ((a + b : α) : 完备化 α) = a + b
  证明: (map₂_coe_coe a b (· + ·) uniformContinuous_add).symm

Depends on / 依赖: uniformContinuous_add
-/
theorem coe_add (a b : α) : ((a + b : α) : Completion α) = a + b :=
  (map₂_coe_coe a b (· + ·) uniformContinuous_add).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddMonoid (Completion α)
  body: Completion.induction_on a
      (isClosed_eq (continuous_map₂ continuous_const continuous_id) continuous_id) fun a =>
      show 0 + (a : Completion α) = a by rw [← coe_zero, ← coe_add, zero_add]
  add_zero a :=
    Completion.induction_on a
      (isClosed_eq (continuous_map₂ continuous_id continuo

中文:
实例 :
  签名: 加法幺半群 (完备化 α)
  定义体: Completion.induction_on a
      (isClosed_eq (continuous_map₂ continuous_const continuous_id) continuous_id) fun a =>
      show 0 + (a : Completion α) = a by rw [← coe_zero, ← coe_add, zero_add]
  add_zero a :=
    Completion.induction_on a
      (isClosed_eq (continuous_map₂ continuous_id continuo

Depends on / 依赖: Completion, Completion.induction_on, add_assoc, add_zero, coe_add, coe_zero, continuous_const, continuous_fst, continuous_id, induction_on, isClosed_eq, trivialVectorBundleCore, zero_add
-/
instance : AddMonoid (Completion α) where
  zero_add a :=
    Completion.induction_on a
      (isClosed_eq (continuous_map₂ continuous_const continuous_id) continuous_id) fun a =>
      show 0 + (a : Completion α) = a by rw [← coe_zero, ← coe_add, zero_add]
  add_zero a :=
    Completion.induction_on a
      (isClosed_eq (continuous_map₂ continuous_id continuous_const) continuous_id) fun a =>
      show (a : Completion α) + 0 = a by rw [← coe_zero, ← coe_add, add_zero]
  add_assoc := fun a b c =>
    Completion.induction_on₃ a b c
      (isClosed_eq
        (continuous_map₂ (continuous_map₂ continuous_fst (by fun_prop)) (by fun_prop))
        (continuous_map₂ continuous_fst (continuous_map₂ (by fun_prop) (by fun_prop))))
      fun a b c =>
      show (a : Completion α) + b + c = a + (b + c) by repeat' rw_mod_cast [add_assoc]
  nsmul_zero a :=
    Completion.induction_on a (isClosed_eq continuous_map continuous_const) fun a =>
      show 0 • (a : Completion α) = 0 by rw [← coe_smul, ← coe_zero, zero_smul]
  nsmul_succ n a :=
    Completion.induction_on a
      (isClosed_eq continuous_map <| continuous_map₂ continuous_map continuous_id) fun a =>
      show (n + 1) • (a : Completion α) = n • (a : Completion α) + (a : Completion α) by
        rw [← coe_smul]; rw [succ_nsmul]; rw [coe_add]; rw [coe_smul]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SubNegMonoid (Completion α)
  body: Completion.induction_on₂ a b
      (isClosed_eq (continuous_map₂ continuous_fst continuous_snd)
        (continuous_map₂ continuous_fst (Completion.continuous_map.comp continuous_snd)))
      fun a b => mod_cast congr_arg ((↑) : α -> Completion α) (sub_eq_add_neg a b)
  zsmul_zero' a :=
    Completi

中文:
实例 :
  签名: SubNeg幺半群 (完备化 α)
  定义体: Completion.induction_on₂ a b
      (isClosed_eq (continuous_map₂ continuous_fst continuous_snd)
        (continuous_map₂ continuous_fst (Completion.continuous_map.comp continuous_snd)))
      fun a b => mod_cast congr_arg ((↑) : α -> Completion α) (sub_eq_add_neg a b)
  zsmul_zero' a :=
    Completi

Depends on / 依赖: Completion, Completion.continuous_map.comp, Completion.induction_on, coe_smul, coe_zero, congr_arg, continuous_const, continuous_fst, continuous_ma, continuous_map, continuous_snd, induction_on, isClosed_eq, mod_cast, sub_eq_add_neg, zero_smul, zsmul_succ, zsmul_zero
-/
instance : SubNegMonoid (Completion α) where
  sub_eq_add_neg a b :=
    Completion.induction_on₂ a b
      (isClosed_eq (continuous_map₂ continuous_fst continuous_snd)
        (continuous_map₂ continuous_fst (Completion.continuous_map.comp continuous_snd)))
      fun a b => mod_cast congr_arg ((↑) : α -> Completion α) (sub_eq_add_neg a b)
  zsmul_zero' a :=
    Completion.induction_on a (isClosed_eq continuous_map continuous_const) fun a =>
      show (0 : Int) • (a : Completion α) = 0 by rw [← coe_smul, ← coe_zero, zero_smul]
  zsmul_succ' n a :=
    Completion.induction_on a
      (isClosed_eq continuous_map <| continuous_map₂ continuous_map continuous_id) fun a =>
        show (n.succ : Int) • (a : Completion α) = _ by
          rw [← coe_smul]; rw [show (n.succ : Int) • a = (n : Int) • a + a from
            SubNegMonoid.zsmul_succ' n a]; rw [coe_add]; rw [coe_smul]
  zsmul_neg' n a :=
    Completion.induction_on a
      (isClosed_eq continuous_map <| Completion.continuous_map.comp continuous_map) fun a =>
        show (Int.negSucc n) • (a : Completion α) = _ by
          rw [← coe_smul]; rw [show (Int.negSucc n) • a = -((n.succ : Int) • a) from
            SubNegMonoid.zsmul_neg' n a]; rw [coe_neg]; rw [coe_smul]

/--
Instance `addGroup` / 实例 `addGroup`

English:
instance addGroup
  signature: : AddGroup (Completion α) where
  body: Completion.induction_on a
      (isClosed_eq (continuous_map₂ Completion.continuous_map continuous_id) continuous_const)
      fun a =>
      show -(a : Completion α) + a = 0 by
        rw_mod_cast [neg_add_cancel]
        rfl

中文:
实例 addGroup
  签名: : 加法群 (完备化 α) where
  定义体: Completion.induction_on a
      (isClosed_eq (continuous_map₂ Completion.continuous_map continuous_id) continuous_const)
      fun a =>
      show -(a : Completion α) + a = 0 by
        rw_mod_cast [neg_add_cancel]
        rfl

Depends on / 依赖: Completion, Completion.continuous_map, Completion.induction_on, continuous_const, continuous_id, continuous_map, induction_on, isClosed_eq, neg_add_cancel, rw_mod_cast
-/
instance addGroup : AddGroup (Completion α) where
  neg_add_cancel a :=
    Completion.induction_on a
      (isClosed_eq (continuous_map₂ Completion.continuous_map continuous_id) continuous_const)
      fun a =>
      show -(a : Completion α) + a = 0 by
        rw_mod_cast [neg_add_cancel]
        rfl

/--
Instance `isUniformAddGroup` / 实例 `isUniformAddGroup`

English:
instance isUniformAddGroup
  signature: : IsUniformAddGroup (Completion α)
  body: ⟨uniformContinuous_map₂ Sub.sub⟩

中文:
实例 isUniformAddGroup
  签名: : 是UniformAdd群 (完备化 α)
  定义体: ⟨uniformContinuous_map₂ Sub.sub⟩

Depends on / 依赖: Sub.sub
-/
instance isUniformAddGroup : IsUniformAddGroup (Completion α) :=
  ⟨uniformContinuous_map₂ Sub.sub⟩

instance {M} [Monoid M] [DistribMulAction M α] [UniformContinuousConstSMul M α] :
    DistribMulAction M (Completion α) where
  smul_add r x y :=
    induction_on₂ x y
      (isClosed_eq ((continuous_fst.fun_add continuous_snd).fun_const_smul _)
        ((continuous_fst.fun_const_smul _).fun_add (continuous_snd.fun_const_smul _)))
      fun a b => by simp only [← coe_add, ← coe_smul, smul_add]
  smul_zero := fun r => by rw [← coe_zero, ← coe_smul, smul_zero r]

/-- The map from a group to its completion as a group hom. -/
@[simps]
/--
Definition of `toCompl` / `toCompl` 的定义

English:
definition toCompl
  signature: : α ->+ Completion α where
  body: (↑)
  map_add' := coe_add
  map_zero' := coe_zero

中文:
定义 toCompl
  签名: : α ->+ 完备化 α where
  定义体: (↑)
  map_add' := coe_add
  map_zero' := coe_zero
-/
def toCompl : α ->+ Completion α where
  toFun := (↑)
  map_add' := coe_add
  map_zero' := coe_zero

/--
theorem `continuous_toCompl` / 定理 `continuous_toCompl`

English:
theorem continuous_toCompl
  statement: Continuous (toCompl : α -> Completion α)
  proof: continuous_coe α

中文:
定理 continuous_toCompl
  结论: 连续 (toCompl : α -> 完备化 α)
  证明: continuous_coe α

Depends on / 依赖: continuous_coe
-/
theorem continuous_toCompl : Continuous (toCompl : α -> Completion α) :=
  continuous_coe α

variable (α) in
/--
theorem `isDenseInducing_toCompl` / 定理 `isDenseInducing_toCompl`

English:
theorem isDenseInducing_toCompl
  statement: IsDenseInducing (toCompl : α -> Completion α)
  proof: isDenseInducing_coe

中文:
定理 isDenseInducing_toCompl
  结论: 是DenseInducing (toCompl : α -> 完备化 α)
  证明: isDenseInducing_coe

Depends on / 依赖: isDenseInducing_coe
-/
theorem isDenseInducing_toCompl : IsDenseInducing (toCompl : α -> Completion α) :=
  isDenseInducing_coe

end IsUniformAddGroup

section UniformAddCommGroup

variable [UniformSpace α] [AddCommGroup α] [IsUniformAddGroup α]

/--
Instance `instAddCommGroup` / 实例 `instAddCommGroup`

English:
instance instAddCommGroup
  signature: : AddCommGroup (Completion α)
  body: { (inferInstance : AddGroup <| Completion α) with
    add_comm a b :=
      Completion.induction_on₂ a b
        (isClosed_eq (by fun_prop) (by fun_prop))
        fun x y => by
        change (x : Completion α) + ↑y = ↑y + ↑x
        rw [← coe_add]; rw [← coe_add]; rw [add_comm] }

中文:
实例 instAddCommGroup
  签名: : 加法交换群 (完备化 α)
  定义体: { (inferInstance : AddGroup <| Completion α) with
    add_comm a b :=
      Completion.induction_on₂ a b
        (isClosed_eq (by fun_prop) (by fun_prop))
        fun x y => by
        change (x : Completion α) + ↑y = ↑y + ↑x
        rw [← coe_add]; rw [← coe_add]; rw [add_comm] }

Depends on / 依赖: AddGroup, Completion, Completion.induction_on, add_comm, coe_add, fun_prop, isClosed_eq
-/
instance instAddCommGroup : AddCommGroup (Completion α) :=
  { (inferInstance : AddGroup <| Completion α) with
    add_comm a b :=
      Completion.induction_on₂ a b
        (isClosed_eq (by fun_prop) (by fun_prop))
        fun x y => by
        change (x : Completion α) + ↑y = ↑y + ↑x
        rw [← coe_add]; rw [← coe_add]; rw [add_comm] }

/--
Instance `instModule` / 实例 `instModule`

English:
instance instModule
  signature: [Semiring R] [Module R α] [UniformContinuousConstSMul R α]
  body: { (inferInstance : DistribMulAction R <| Completion α),
    (inferInstance : MulActionWithZero R <| Completion α) with
    add_smul := fun a b =>
      ext' (continuous_const_smul _) ((continuous_const_smul _).add (continuous_const_smul _))
        fun x => by
          rw [← coe_smul]; rw [add_smul

中文:
实例 instModule
  签名: [半环 R] [模 R α] [一致连续常数标量乘法 R α]
  定义体: { (inferInstance : DistribMulAction R <| Completion α),
    (inferInstance : MulActionWithZero R <| Completion α) with
    add_smul := fun a b =>
      ext' (continuous_const_smul _) ((continuous_const_smul _).add (continuous_const_smul _))
        fun x => by
          rw [← coe_smul]; rw [add_smul

Depends on / 依赖: Completion, DistribMulAction, MulActionWithZero, add_smul, coe_add, coe_smul, continuous_const_smul
-/
instance instModule [Semiring R] [Module R α] [UniformContinuousConstSMul R α] :
    Module R (Completion α) :=
  { (inferInstance : DistribMulAction R <| Completion α),
    (inferInstance : MulActionWithZero R <| Completion α) with
    add_smul := fun a b =>
      ext' (continuous_const_smul _) ((continuous_const_smul _).add (continuous_const_smul _))
        fun x => by
          rw [← coe_smul]; rw [add_smul]; rw [coe_add]; rw [coe_smul]; rw [coe_smul] }

end UniformAddCommGroup

end UniformSpace.Completion

section AddMonoidHom

variable [UniformSpace α] [AddGroup α] [IsUniformAddGroup α] [UniformSpace β] [AddGroup β]
  [IsUniformAddGroup β]

open UniformSpace UniformSpace.Completion

/--
Definition of `AddMonoidHom.extension` / `AddMonoidHom.extension` 的定义

English:
definition AddMonoidHom.extension
  signature: [CompleteSpace β] [T0Space β] (f : α ->+ β) (hf : Continuous f)
  body: have hf : UniformContinuous f := uniformContinuous_addMonoidHom_of_continuous hf
  { toFun := Completion.extension f
    map_zero' := by rw [← coe_zero, extension_coe hf, f.map_zero]
    map_add' a b :=
      Completion.induction_on₂ a b
        (isClosed_eq (by fun_prop) (by fun_prop))
        fun 

中文:
定义 加法幺半群态射.extension
  签名: [完备空间 β] [T0空间 β] (f : α ->+ β) (hf : 连续 f)
  定义体: have hf : UniformContinuous f := uniformContinuous_addMonoidHom_of_continuous hf
  { toFun := Completion.extension f
    map_zero' := by rw [← coe_zero, extension_coe hf, f.map_zero]
    map_add' a b :=
      Completion.induction_on₂ a b
        (isClosed_eq (by fun_prop) (by fun_prop))
        fun 

Depends on / 依赖: Completion, Completion.extension, Completion.induction_on, UniformContinuous, coe_zero, extension, extension_coe, f.map_add, f.map_zero, fun_prop, isClosed_eq, map_add, map_zero, rw_mod_cast, uniformContinuous_addMonoidHom_of_continuous
-/
def AddMonoidHom.extension [CompleteSpace β] [T0Space β] (f : α ->+ β) (hf : Continuous f) :
    Completion α ->+ β :=
  have hf : UniformContinuous f := uniformContinuous_addMonoidHom_of_continuous hf
  { toFun := Completion.extension f
    map_zero' := by rw [← coe_zero, extension_coe hf, f.map_zero]
    map_add' a b :=
      Completion.induction_on₂ a b
        (isClosed_eq (by fun_prop) (by fun_prop))
        fun a b =>
        show Completion.extension f _ = Completion.extension f _ + Completion.extension f _ by
        rw_mod_cast [extension_coe hf, extension_coe hf, extension_coe hf, f.map_add] }

/--
theorem `AddMonoidHom.extension_coe` / 定理 `AddMonoidHom.extension_coe`

English:
theorem AddMonoidHom.extension_coe
  statement: [CompleteSpace β] [T0Space β] (f : α ->+ β)
  proof: UniformSpace.Completion.extension_coe (uniformContinuous_addMonoidHom_of_continuous hf) a

@[continuity, fun_prop]

中文:
定理 加法幺半群态射.extension_coe
  结论: [完备空间 β] [T0空间 β] (f : α ->+ β)
  证明: UniformSpace.Completion.extension_coe (uniformContinuous_addMonoidHom_of_continuous hf) a

@[continuity, fun_prop]

Depends on / 依赖: Completion, UniformSpace, UniformSpace.Completion.extension_coe, extension_coe, uniformContinuous_addMonoidHom_of_continuous
-/
theorem AddMonoidHom.extension_coe [CompleteSpace β] [T0Space β] (f : α ->+ β)
    (hf : Continuous f) (a : α) : f.extension hf a = f a :=
  UniformSpace.Completion.extension_coe (uniformContinuous_addMonoidHom_of_continuous hf) a

@[continuity, fun_prop]
/--
theorem `AddMonoidHom.continuous_extension` / 定理 `AddMonoidHom.continuous_extension`

English:
theorem AddMonoidHom.continuous_extension
  statement: [CompleteSpace β] [T0Space β] (f : α ->+ β)
  proof: UniformSpace.Completion.continuous_extension

中文:
定理 加法幺半群态射.continuous_extension
  结论: [完备空间 β] [T0空间 β] (f : α ->+ β)
  证明: UniformSpace.Completion.continuous_extension

Depends on / 依赖: Completion, UniformSpace, UniformSpace.Completion.continuous_extension, continuous_extension
-/
theorem AddMonoidHom.continuous_extension [CompleteSpace β] [T0Space β] (f : α ->+ β)
    (hf : Continuous f) : Continuous (f.extension hf) :=
  UniformSpace.Completion.continuous_extension

/--
Definition of `AddMonoidHom.completion` / `AddMonoidHom.completion` 的定义

English:
definition AddMonoidHom.completion
  signature: (f : α ->+ β) (hf : Continuous f)
  body: (toCompl.comp f).extension (continuous_toCompl.comp hf)

@[continuity, fun_prop]

中文:
定义 加法幺半群态射.completion
  签名: (f : α ->+ β) (hf : 连续 f)
  定义体: (toCompl.comp f).extension (continuous_toCompl.comp hf)

@[continuity, fun_prop]

Depends on / 依赖: continuous_toCompl, continuous_toCompl.comp, extension, toCompl, toCompl.comp
-/
def AddMonoidHom.completion (f : α ->+ β) (hf : Continuous f) : Completion α ->+ Completion β :=
  (toCompl.comp f).extension (continuous_toCompl.comp hf)

@[continuity, fun_prop]
/--
theorem `AddMonoidHom.continuous_completion` / 定理 `AddMonoidHom.continuous_completion`

English:
theorem AddMonoidHom.continuous_completion
  given: (f : α ->+ β) (hf : Continuous f)
  proof: continuous_map

@[simp]

中文:
定理 加法幺半群态射.continuous_completion
  条件: (f : α ->+ β) (hf : 连续 f)
  证明: continuous_map

@[simp]

Depends on / 依赖: continuous_map
-/
theorem AddMonoidHom.continuous_completion (f : α ->+ β) (hf : Continuous f) :
    Continuous (AddMonoidHom.completion f hf : Completion α -> Completion β) :=
  continuous_map

@[simp]
/--
theorem `AddMonoidHom.completion_coe` / 定理 `AddMonoidHom.completion_coe`

English:
theorem AddMonoidHom.completion_coe
  given: (f : α ->+ β) (hf : Continuous f) (a : α)
  proof: map_coe (uniformContinuous_addMonoidHom_of_continuous hf) a

中文:
定理 加法幺半群态射.completion_coe
  条件: (f : α ->+ β) (hf : 连续 f) (a : α)
  证明: map_coe (uniformContinuous_addMonoidHom_of_continuous hf) a

Depends on / 依赖: map_coe, uniformContinuous_addMonoidHom_of_continuous
-/
theorem AddMonoidHom.completion_coe (f : α ->+ β) (hf : Continuous f) (a : α) :
    AddMonoidHom.completion f hf a = f a :=
  map_coe (uniformContinuous_addMonoidHom_of_continuous hf) a

/--
theorem `AddMonoidHom.completion_zero` / 定理 `AddMonoidHom.completion_zero`

English:
theorem AddMonoidHom.completion_zero
  proof: by
  ext x
  refine Completion.induction_on x ?_ ?_
  · apply isClosed_eq (AddMonoidHom.continuous_completion (0 : α ->+ β) continuous_const)
    exact continuous_const
  · simp [(0 : α ->+ β).completion_coe continuous_const, coe_zero]

中文:
定理 加法幺半群态射.completion_zero
  证明: by
  ext x
  refine Completion.induction_on x ?_ ?_
  · apply isClosed_eq (AddMonoidHom.continuous_completion (0 : α ->+ β) continuous_const)
    exact continuous_const
  · simp [(0 : α ->+ β).completion_coe continuous_const, coe_zero]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.continuous_completion, Completion, Completion.induction_on, coe_zero, completion_coe, continuous_completion, continuous_const, induction_on, isClosed_eq
-/
theorem AddMonoidHom.completion_zero :
    AddMonoidHom.completion (0 : α ->+ β) continuous_const = 0 := by
  ext x
  refine Completion.induction_on x ?_ ?_
  · apply isClosed_eq (AddMonoidHom.continuous_completion (0 : α ->+ β) continuous_const)
    exact continuous_const
  · simp [(0 : α ->+ β).completion_coe continuous_const, coe_zero]

/--
theorem `AddMonoidHom.completion_add` / 定理 `AddMonoidHom.completion_add`

English:
theorem AddMonoidHom.completion_add
  statement: {γ : Type*} [AddCommGroup γ] [UniformSpace γ]
  proof: by
  have hfg := hf.add hg
  ext x
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_eq ((f + g).continuous_completion hfg)
      ((f.continuous_completion hf).add (g.continuous_completion hg))
  · simp [(f + g).completion_coe hfg, coe_add, f.completion_coe hf, g.completion_coe hg]

中文:
定理 加法幺半群态射.completion_add
  结论: {γ : 类型} [加法交换群 γ] [一致空间 γ]
  证明: by
  have hfg := hf.add hg
  ext x
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_eq ((f + g).continuous_completion hfg)
      ((f.continuous_completion hf).add (g.continuous_completion hg))
  · simp [(f + g).completion_coe hfg, coe_add, f.completion_coe hf, g.completion_coe hg]

Depends on / 依赖: Completion, Completion.induction_on, coe_add, completion_coe, continuous_completion, f.completion_coe, f.continuous_completion, g.completion_coe, g.continuous_completion, hf.add, induction_on, isClosed_eq
-/
theorem AddMonoidHom.completion_add {γ : Type*} [AddCommGroup γ] [UniformSpace γ]
    [IsUniformAddGroup γ] (f g : α ->+ γ) (hf : Continuous f) (hg : Continuous g) :
    AddMonoidHom.completion (f + g) (hf.add hg) =
    AddMonoidHom.completion f hf + AddMonoidHom.completion g hg := by
  have hfg := hf.add hg
  ext x
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_eq ((f + g).continuous_completion hfg)
      ((f.continuous_completion hf).add (g.continuous_completion hg))
  · simp [(f + g).completion_coe hfg, coe_add, f.completion_coe hf, g.completion_coe hg]

end AddMonoidHom
