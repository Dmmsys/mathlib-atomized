/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.TransferInstance
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Algebra.SeparationQuotient.Basic

/-!
# Completion of topological rings:

This file endows the completion of a topological ring with a ring structure.
More precisely, the instance `UniformSpace.Completion.ring` builds a ring structure
on the completion of a ring endowed with a compatible uniform structure in the sense of
`IsUniformAddGroup`. There is also a commutative version when the original ring is commutative.
Moreover, if a topological ring is an algebra over a commutative semiring, then so is its
`UniformSpace.Completion`.

The last part of the file builds a ring structure on the biggest separated quotient of a ring.

## Main declarations:

Beyond the instances explained above (that don't have to be explicitly invoked),
the main constructions deal with continuous ring morphisms.

* `UniformSpace.Completion.extensionHom`: extends a continuous ring morphism from `R`
  to a complete separated group `S` to `Completion R`.
* `UniformSpace.Completion.mapRingHom`: promotes a continuous ring morphism
  from `R` to `S` into a continuous ring morphism from `Completion R` to `Completion S`.

TODO: Generalise the results here from the concrete `Completion` to any `AbstractCompletion`.
-/

@[expose] public section

noncomputable section

universe u
namespace UniformSpace.Completion

open IsDenseInducing UniformSpace Function

section one_and_mul
variable (α : Type*) [Ring α] [UniformSpace α]

/-
**UniformSpace.Completion.one** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpace.Completion
`。
形式化陈述：one : One (Completion α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance one : One (Completion α) :=
  ⟨(1 : α)⟩
/-
**UniformSpace.Completion.mul** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpace.Completion
`。
形式化陈述：mul : Mul (Completion α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mul : Mul (Completion α) :=
  ⟨curry <| (isDenseInducing_coe.prodMap isDenseInducing_coe).extend ((↑) ∘ uncurry (· * ·))⟩

@[norm_cast]
/-
**UniformSpace.Completion.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace.Comple
tion`。
形式化陈述：coe_one : ((1 : α) : Completion α) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ((1 : α) : Completion α) = 1 :=
  rfl
/-
**UniformSpace.Completion.coe_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace
.Completion`。
形式化陈述：∀ (α : Type u_1) [inst : Ring α] [inst_1 : UniformSpace α] [T0Space α] {x 
: α}, ↑x = 1 ↔ x = 1
参数：α : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `UniformSpace.Completion.coe_inj`：coe_inj [T0Space α] {a b : α} : (a : Co
mpletion α) = b ↔ a = b
-/
@[simp] lemma coe_eq_one_iff [T0Space α] {x : α} : (x : Completion α) = 1 ↔ x = 1 :=
  Completion.coe_inj

end one_and_mul

variable {α : Type*} [Ring α] [UniformSpace α] [IsTopologicalRing α]

@[norm_cast]
/-
**UniformSpace.Completion.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace.Comple
tion`。
形式化陈述：coe_mul (a b : α) : ((a * b : α) : Completion α) = a * b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsDenseInducing.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{δ : Type u_4} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst
_2 : Topologi…
· 使用定理 `UniformSpace.Completion.isDenseInducing_coe`：isDenseInducing_coe : IsDen
seInducing ((↑) : α -> Completion α)
· 使用定理 `IsDenseInducing.extend_eq`：extend_eq [T2Space γ] (di : IsDenseInducing i
) {f : α -> γ} (hf : Continuous f) (a : α) : di.extend f (i a) = f a
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `UniformSpace.Completion.continuous_coe`：continuous_coe : Continuous ((↑)
 : α -> Completion α)
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
-/
theorem coe_mul (a b : α) : ((a * b : α) : Completion α) = a * b :=
  ((isDenseInducing_coe.prodMap isDenseInducing_coe).extend_eq
      ((continuous_coe α).comp (@continuous_mul α _ _ _)) (a, b)).symm

variable [IsUniformAddGroup α]
/-
**UniformSpace.Completion.** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpace.Completion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ContinuousMul (Completion α) where
  continuous_mul := by
    let m := (AddMonoidHom.mul : α →+ α →+ α).compr₂ toCompl
    have : Continuous fun p : α × α => m p.1 p.2 := (continuous_coe α).comp continuous_mul
    have di : IsDenseInducing (toCompl : α → Completion α) := isDenseInducing_coe
    exact (di.extend_Z_bilin di this :)
/-
**UniformSpace.Completion.ring** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpace.Completio
n`。
形式化陈述：ring : Ring (Completion α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ring : Ring (Completion α) :=
  { AddMonoidWithOne.unary, ((inferInstance : AddCommGroup (Completion α))),
      ((inferInstance : Mul (Completion α))), ((inferInstance : One (Completion α))) with
    zero_mul a :=
      Completion.induction_on a (isClosed_eq (by fun_prop) continuous_const)
        fun a => by rw [← coe_zero, ← coe_mul, zero_mul]
    mul_zero a :=
      Completion.induction_on a (isClosed_eq (by fun_prop) continuous_const)
        fun a ↦ by rw [← coe_zero, ← coe_mul, mul_zero]
    one_mul a :=
      Completion.induction_on a
        (isClosed_eq (by fun_prop) continuous_id)
        fun a => by rw [← coe_one, ← coe_mul, one_mul]
    mul_one a :=
      Completion.induction_on a
        (isClosed_eq (by fun_prop) continuous_id)
        fun a => by rw [← coe_one, ← coe_mul, mul_one]
    mul_assoc a b c :=
      Completion.induction_on₃ a b c
        (isClosed_eq (by fun_prop) (by fun_prop))
        fun a b c => by rw [← coe_mul, ← coe_mul, ← coe_mul, ← coe_mul, mul_assoc]
    left_distrib a b c :=
      Completion.induction_on₃ a b c
        (isClosed_eq (by fun_prop) (by fun_prop))
        fun a b c => by rw [← coe_add, ← coe_mul, ← coe_mul, ← coe_mul, ← coe_add, mul_add]
    right_distrib a b c :=
      Completion.induction_on₃ a b c
        (isClosed_eq (by fun_prop) (by fun_prop))
        fun a b c => by rw [← coe_add, ← coe_mul, ← coe_mul, ← coe_mul, ← coe_add, add_mul] }

/-- The map from a uniform ring to its completion, as a ring homomorphism. -/
/-
**UniformSpace.Completion.coeRingHom** 是 Mathlib 中的一个定义，位于命名空间 `UniformSpace.Com
pletion`。
形式化陈述：coeRingHom : α ->+* Completion α where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.Completion.coe_one`：coe_one : ((1 : α) : Completion α) = 1
· 使用定理 `UniformSpace.Completion.coe_mul`：coe_mul (a b : α) : ((a * b : α) : Comp
letion α) = a * b

--- 原说明 ---
The map from a uniform ring to its completion, as a ring homomorphism.
-/
def coeRingHom : α →+* Completion α where
  toFun := (↑)
  map_one' := coe_one α
  map_zero' := coe_zero
  map_add' := coe_add
  map_mul' := coe_mul
/-
**UniformSpace.Completion.continuous_coeRingHom** 是 Mathlib 中的一个定理，位于命名空间 `Unifo
rmSpace.Completion`。
形式化陈述：continuous_coeRingHom : Continuous (coeRingHom : α -> Completion α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.Completion.continuous_coe`：continuous_coe : Continuous ((↑)
 : α -> Completion α)
-/
theorem continuous_coeRingHom : Continuous (coeRingHom : α → Completion α) :=
  continuous_coe α

variable {β : Type u} [UniformSpace β] [Ring β] [IsUniformAddGroup β] [IsTopologicalRing β]
  (f : α →+* β) (hf : Continuous f)

/-- The completion extension as a ring morphism. -/
/-
**UniformSpace.Completion.extensionHom** 是 Mathlib 中的一个定义，位于命名空间 `UniformSpace.C
ompletion`。
形式化陈述：extensionHom [CompleteSpace β] [T0Space β] : Completion α ->+* β
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The completion extension as a ring morphism.
-/
def extensionHom [CompleteSpace β] [T0Space β] : Completion α →+* β :=
  have hf' : Continuous (f : α →+ β) := hf
  -- helping the elaborator
  have hf : UniformContinuous f := uniformContinuous_addMonoidHom_of_continuous hf'
  { toFun := Completion.extension f
    map_zero' := by simp_rw [← coe_zero, extension_coe hf, f.map_zero]
    map_add' a b :=
      Completion.induction_on₂ a b
        (isClosed_eq (by fun_prop) (by fun_prop))
        fun a b => by simp_rw [← coe_add, extension_coe hf, f.map_add]
    map_one' := by rw [← coe_one, extension_coe hf, f.map_one]
    map_mul' a b :=
      Completion.induction_on₂ a b
        (isClosed_eq (by fun_prop) (by fun_prop))
        fun a b => by simp_rw [← coe_mul, extension_coe hf, f.map_mul] }
/-
**UniformSpace.Completion.extensionHom_coe** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpa
ce.Completion`。
形式化陈述：extensionHom_coe [CompleteSpace β] [T0Space β] (a : α) : Completion.extens
ionHom f hf a = f a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformSpace.Completion.extension_coe`：extension_coe [T0Space β] (hf : U
niformContinuous f) (a : α) : (Completion.extension f) a = f a
· 使用定理 `uniformContinuous_addMonoidHom_of_continuous`：∀ {α : Type u_1} {β : Type
 u_2} [inst : UniformSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α] {hom :
 Type u_3}   [inst_3 : UniformSpac…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem extensionHom_coe [CompleteSpace β] [T0Space β] (a : α) :
    Completion.extensionHom f hf a = f a := by
  simp only [Completion.extensionHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    UniformSpace.Completion.extension_coe <| uniformContinuous_addMonoidHom_of_continuous hf]
/-
**UniformSpace.Completion.topologicalRing** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpac
e.Completion`。
形式化陈述：topologicalRing : IsTopologicalRing (Completion α) where continuous_add
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_add`：continuous_add : Continuous (fun x : X × X ↦ x.1 + x.2)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
· 使用定理 `UniformSpace.Completion.instContinuousMul`：∀ {α : Type u_1} [inst : Ring
 α] [inst_1 : UniformSpace α] [IsTopologicalRing α] [IsUniformAddGroup α],   Con
tinuousMul (UniformSpace.Comple…
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
-/
instance topologicalRing : IsTopologicalRing (Completion α) where
  continuous_add := continuous_add
  continuous_mul := continuous_mul

/-- The completion map as a ring morphism. -/
/-
**UniformSpace.Completion.mapRingHom** 是 Mathlib 中的一个定义，位于命名空间 `UniformSpace.Com
pletion`。
形式化陈述：mapRingHom (hf : Continuous f) : Completion α ->+* Completion β
参数：hf : Continuous f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The completion map as a ring morphism.
-/
def mapRingHom (hf : Continuous f) : Completion α →+* Completion β :=
  extensionHom (coeRingHom.comp f) (continuous_coeRingHom.comp hf)
/-
**UniformSpace.Completion.mapRingHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpa
ce.Completion`。
形式化陈述：∀ {α : Type u_1} [inst : Ring α] [inst_1 : UniformSpace α] [inst_2 : IsTop
ologicalRing α] [inst_3 : IsUniformAddGroup α]   {β : Type u} [inst_4 : UniformS
pace β] [inst_5 : Ring β] [inst_6 : IsUniformAddGroup β] [inst_7 : IsTopological
Ring β]   (f : α →+* β) (hf : Continuous ⇑f) {x : UniformSpace.Completion α},   
(UniformSpace.Completion.mapRingHom f hf) x = UniformSpace.Completion.map (⇑f) x
参数：f : α →+* β；hf : Continuous ⇑f；UniformSpace.Completion.mapRingHom f hf；⇑f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem mapRingHom_apply {x : Completion α} : mapRingHom f hf x = .map f x := rfl
/-
**UniformSpace.Completion.coe_mapRingHom** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace
.Completion`。
形式化陈述：coe_mapRingHom : mapRingHom f hf = Completion.map f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mapRingHom : mapRingHom f hf = Completion.map f := rfl

variable {f}
/-
**UniformSpace.Completion.mapRingHom_coe** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace
.Completion`。
形式化陈述：mapRingHom_coe (hf : Continuous f) (a : α) : mapRingHom f hf a = f a
参数：hf : Continuous f；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformSpace.Completion.mapRingHom_apply`：∀ {α : Type u_1} [inst : Ring 
α] [inst_1 : UniformSpace α] [inst_2 : IsTopologicalRing α] [inst_3 : IsUniformA
ddGroup α]   {β : Type u} [ins…
· 使用定理 `UniformSpace.Completion.map_coe`：map_coe (hf : UniformContinuous f) (a :
 α) : (Completion.map f) a = f a
· 使用定理 `uniformContinuous_addMonoidHom_of_continuous`：∀ {α : Type u_1} {β : Type
 u_2} [inst : UniformSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α] {hom :
 Type u_3}   [inst_3 : UniformSpac…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
theorem mapRingHom_coe (hf : Continuous f) (a : α) : mapRingHom f hf a = f a := by
  rw [mapRingHom_apply, map_coe (uniformContinuous_addMonoidHom_of_continuous hf)]
/-
**UniformSpace.Completion.mapRingHom_comp** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpac
e.Completion`。
形式化陈述：mapRingHom_comp {γ : Type*} [UniformSpace γ] [Ring γ] [IsUniformAddGroup γ
] [IsTopologicalRing γ] {g : β ->+* γ} (hg : Continuous g) (hf : Continuous f) :
 (mapRingHom g hg).comp (mapRingHom f hf) = mapRingHom (g.comp f) (hg.comp hf)
参数：hg : Continuous g；hf : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `UniformSpace.Completion.map_comp`：map_comp {g : β -> γ} {f : α -> β} (hg
 : UniformContinuous g) (hf : UniformContinuous f) : Completion.map g ∘ Completi
on.map f = Completion.…
· 使用定理 `uniformContinuous_addMonoidHom_of_continuous`：∀ {α : Type u_1} {β : Type
 u_2} [inst : UniformSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α] {hom :
 Type u_3}   [inst_3 : UniformSpac…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
theorem mapRingHom_comp {γ : Type*} [UniformSpace γ] [Ring γ] [IsUniformAddGroup γ]
    [IsTopologicalRing γ] {g : β →+* γ} (hg : Continuous g) (hf : Continuous f) :
    (mapRingHom g hg).comp (mapRingHom f hf) = mapRingHom (g.comp f) (hg.comp hf) :=
  DFunLike.ext' <| map_comp
    (uniformContinuous_addMonoidHom_of_continuous hg)
    (uniformContinuous_addMonoidHom_of_continuous hf)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**UniformSpace.Completion.mapRingHom_id** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace.
Completion`。
形式化陈述：mapRingHom_id : mapRingHom (.id α) continuous_id = .id (Completion α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `UniformSpace.Completion.map_id`：map_id : Completion.map (@id α) = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem mapRingHom_id : mapRingHom (.id α) continuous_id = .id (Completion α) := by
  simp [RingHom.ext_iff, mapRingHom_apply]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- A ring isomorphism `α ≃+* β` between uniform rings, uniformly continuous in both directions,
lifts to a ring isomorphism between corresponding uniform space completions. -/
@[simps!]
/-
**UniformSpace.Completion.mapRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `UniformSpace.C
ompletion`。
形式化陈述：mapRingEquiv (f : α ≃+* β) (hf : Continuous f) (hf' : Continuous f.symm) :
 Completion α ≃+* Completion β
参数：f : α ≃+* β；hf : Continuous f；hf' : Continuous f.symm。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring isomorphism `α ≃+* β` between uniform rings, uniformly continuous in both
 directions,
lifts to a ring isomorphism between corresponding uniform space completions.
-/
def mapRingEquiv (f : α ≃+* β) (hf : Continuous f) (hf' : Continuous f.symm) :
    Completion α ≃+* Completion β :=
  .ofRingHom (mapRingHom f.toRingHom hf) (mapRingHom f.symm.toRingHom hf')
    (by simp [mapRingHom_comp]) (by simp [mapRingHom_comp])

section Algebra

variable (A : Type*) [Ring A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  (R : Type*) [CommSemiring R] [Algebra R A] [UniformContinuousConstSMul R A]

@[simp]
/-
**UniformSpace.Completion.map_smul_eq_mul_coe** 是 Mathlib 中的一个定理，位于命名空间 `Uniform
Space.Completion`。
形式化陈述：map_smul_eq_mul_coe (r : R) : Completion.map (r • ·) = ((algebraMap R A r 
: Completion A) * ·)
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
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
· 使用定理 `IsTopologicalAddGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSp
ace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], RegularSpace G
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `UniformSpace.Completion.continuous_map`：continuous_map : Continuous (Com
pletion.map f)
· 使用定理 `continuous_const_mul`：continuous_const_mul (m : M) : Continuous (m * ·)
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformSpace.Completion.map_coe`：map_coe (hf : UniformContinuous f) (a :
 α) : (Completion.map f) a = f a
· 使用定理 `UniformContinuousConstSMul.uniformContinuous_const_smul`：∀ {M : Type v} 
{X : Type x} {inst : UniformSpace X} {inst_1 : SMul M X} [self : UniformContinuo
usConstSMul M X] (c : M),   UniformContinuous…
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `UniformSpace.Completion.coe_mul`：coe_mul (a b : α) : ((a * b : α) : Comp
letion α) = a * b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_smul_eq_mul_coe (r : R) :
    Completion.map (r • ·) = ((algebraMap R A r : Completion A) * ·) := by
  ext x
  refine Completion.induction_on x ?_ fun a => ?_
  · exact isClosed_eq Completion.continuous_map (continuous_const_mul _)
  · simp_rw [map_coe (uniformContinuous_const_smul r) a, Algebra.smul_def, coe_mul]
/-
**UniformSpace.Completion.algebra** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpace.Comple
tion`。
形式化陈述：algebra : Algebra R (Completion A) where algebraMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance algebra : Algebra R (Completion A) where
  algebraMap := (UniformSpace.Completion.coeRingHom : A →+* Completion A).comp (algebraMap R A)
  commutes' := fun r x =>
    Completion.induction_on x (isClosed_eq (continuous_const_mul _) (continuous_mul_const _))
      fun a => by
      simpa only [coe_mul] using! congr_arg ((↑) : A → Completion A) (Algebra.commutes r a)
  smul_def' := fun r x => congr_fun (map_smul_eq_mul_coe A R r) x
/-
**UniformSpace.Completion.algebraMap_def** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace
.Completion`。
形式化陈述：algebraMap_def (r : R) : algebraMap R (Completion A) r = (algebraMap R A r
 : Completion A)
参数：r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_def (r : R) :
    algebraMap R (Completion A) r = (algebraMap R A r : Completion A) :=
  rfl

end Algebra

section CommRing

variable (R : Type*) [CommRing R] [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]

/-
**UniformSpace.Completion.commRing** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpace.Compl
etion`。
形式化陈述：commRing : CommRing (Completion R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commRing : CommRing (Completion R) :=
  { Completion.ring with
    mul_comm a b :=
      Completion.induction_on₂ a b
        (isClosed_eq (by fun_prop) (by fun_prop))
        fun a b => by rw [← coe_mul, ← coe_mul, mul_comm] }

/-- A shortcut instance for the common case -/
/-
**UniformSpace.Completion.algebra'** 是 Mathlib 中的一个实例，位于命名空间 `UniformSpace.Compl
etion`。
形式化陈述：algebra' : Algebra R (Completion R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A shortcut instance for the common case
-/
instance algebra' : Algebra R (Completion R) := by infer_instance

end CommRing

end UniformSpace.Completion

namespace UniformSpace

variable {α : Type*}

-- TODO: move (some of) these results to the file about topological rings
/-
**UniformSpace.inseparableSetoid_ring** 是 Mathlib 中的一个定理，位于命名空间 `UniformSpace`。
形式化陈述：inseparableSetoid_ring (α) [Ring α] [TopologicalSpace α] [IsTopologicalRin
g α] : inseparableSetoid α = Submodule.quotientRel (Ideal.closure ⊥)
参数：α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.ext`：ext {α : Sort*} : forall {s t : Setoid α}, (forall a b, s a 
b ↔ t a b) -> s = t | ⟨r, _⟩, ⟨p, _⟩, Eq => by have : r = p
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `addGroup_inseparable_iff`：∀ {G : Type w} [inst : TopologicalSpace G] [in
st_1 : AddGroup G] [IsTopologicalAddGroup G] {x y : G},   Inseparable x y ↔ x - 
y ∈ closure 0
· 使用定理 `IsSemitopologicalRing.toIsTopologicalAddGroup`：∀ {R : Type u_1} [inst : 
NonUnitalNonAssocRing R] [inst_1 : TopologicalSpace R] [IsSemitopologicalRing R]
,   IsTopologicalAddGroup R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Submodule.quotientRel_def`：quotientRel_def {x y : M} : p.quotientRel x y
 ↔ x - y in p
-/
theorem inseparableSetoid_ring (α) [Ring α] [TopologicalSpace α] [IsTopologicalRing α] :
    inseparableSetoid α = Submodule.quotientRel (Ideal.closure ⊥) :=
  Setoid.ext fun x y =>
    addGroup_inseparable_iff.trans <| .trans (by rfl) (Submodule.quotientRel_def _).symm

/-- Given a topological ring `α` equipped with a uniform structure that makes subtraction uniformly
continuous, get a homeomorphism between the separated quotient of `α` and the quotient ring
corresponding to the closure of zero. -/
/-
**UniformSpace.sepQuotHomeomorphRingQuot** 是 Mathlib 中的一个定义，位于命名空间 `UniformSpace
`。
形式化陈述：sepQuotHomeomorphRingQuot (α) [Ring α] [TopologicalSpace α] [IsTopological
Ring α] : SeparationQuotient α ≃ₜ α ⧸ (⊥ : Ideal α).closure where toEquiv
参数：α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a topological ring `α` equipped with a uniform structure that makes subtra
ction uniformly
continuous, get a homeomorphism between the separated quotient of `α` and the qu
otient ring
corresponding to the closure of zero.
-/
def sepQuotHomeomorphRingQuot (α) [Ring α] [TopologicalSpace α] [IsTopologicalRing α] :
    SeparationQuotient α ≃ₜ α ⧸ (⊥ : Ideal α).closure where
  toEquiv := Quotient.congrRight fun x y => by rw [inseparableSetoid_ring]
  continuous_toFun := continuous_id.quotient_map' <| by
    rw [inseparableSetoid_ring]; exact fun _ _ ↦ id
  continuous_invFun := continuous_id.quotient_map' <| by
    rw [inseparableSetoid_ring]; exact fun _ _ ↦ id

/-- Given a topological ring `α` equipped with a uniform structure that makes subtraction uniformly
continuous, get an equivalence between the separated quotient of `α` and the quotient ring
corresponding to the closure of zero. -/
/-
**UniformSpace.sepQuotRingEquivRingQuot** 是 Mathlib 中的一个定义，位于命名空间 `UniformSpace`
。
形式化陈述：sepQuotRingEquivRingQuot (α) [CommRing α] [TopologicalSpace α] [IsTopologi
calRing α] : SeparationQuotient α ≃+* α ⧸ (⊥ : Ideal α).closure where __
参数：α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a topological ring `α` equipped with a uniform structure that makes subtra
ction uniformly
continuous, get an equivalence between the separated quotient of `α` and the quo
tient ring
corresponding to the closure of zero.
-/
def sepQuotRingEquivRingQuot (α) [CommRing α] [TopologicalSpace α] [IsTopologicalRing α] :
    SeparationQuotient α ≃+* α ⧸ (⊥ : Ideal α).closure where
  __ := sepQuotHomeomorphRingQuot α
  map_mul' := SeparationQuotient.surjective_mk.forall₂.2 (fun _ _ ↦ rfl)
  map_add' := SeparationQuotient.surjective_mk.forall₂.2 (fun _ _ ↦ rfl)

end UniformSpace

section UniformExtension

variable {α : Type*} [UniformSpace α] [Semiring α]
variable {β : Type*} [UniformSpace β] [Semiring β] [IsTopologicalSemiring β]
variable {γ : Type*} [UniformSpace γ] [Semiring γ] [IsTopologicalSemiring γ]
variable [T2Space γ] [CompleteSpace γ]

/-- The dense inducing extension as a ring homomorphism. -/
/-
**IsDenseInducing.extendRingHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsDenseInducing.extendRingHom {i : α ->+* β} {f : α ->+* γ} (ue : IsUnifor
mInducing i) (dr : DenseRange i) (hf : UniformContinuous f) : β ->+* γ where toF
un
参数：ue : IsUniformInducing i；dr : DenseRange i；hf : UniformContinuous f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The dense inducing extension as a ring homomorphism.
-/
noncomputable def IsDenseInducing.extendRingHom {i : α →+* β} {f : α →+* γ}
    (ue : IsUniformInducing i) (dr : DenseRange i) (hf : UniformContinuous f) : β →+* γ where
  toFun := (ue.isDenseInducing dr).extend f
  map_one' := by
    convert! IsDenseInducing.extend_eq (ue.isDenseInducing dr) hf.continuous 1
    exacts [i.map_one.symm, f.map_one.symm]
  map_zero' := by
    convert! IsDenseInducing.extend_eq (ue.isDenseInducing dr) hf.continuous 0 <;>
    simp only [map_zero]
  map_add' := by
    have h := (uniformContinuous_uniformly_extend ue dr hf).continuous
    refine fun x y => DenseRange.induction_on₂ dr ?_ (fun a b => ?_) x y
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · simp_rw [← i.map_add, IsDenseInducing.extend_eq (ue.isDenseInducing dr) hf.continuous _,
        ← f.map_add]
  map_mul' := by
    have h := (uniformContinuous_uniformly_extend ue dr hf).continuous
    refine fun x y => DenseRange.induction_on₂ dr ?_ (fun a b => ?_) x y
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · simp_rw [← i.map_mul, IsDenseInducing.extend_eq (ue.isDenseInducing dr) hf.continuous _,
        ← f.map_mul]

end UniformExtension

