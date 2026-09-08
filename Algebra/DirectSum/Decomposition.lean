/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jujian Zhang
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Module.Submodule.Basic

/-!
# Decompositions of additive monoids, groups, and modules into direct sums

## Main definitions

* `DirectSum.Decomposition ℳ`: A typeclass to provide a constructive decomposition from
  an additive monoid `M` into a family of additive submonoids `ℳ`
* `DirectSum.decompose ℳ`: The canonical equivalence provided by the above typeclass


## Main statements

* `DirectSum.Decomposition.isInternal`: The link to `DirectSum.IsInternal`.

## Implementation details

As we want to talk about different types of decomposition (additive monoids, modules, rings, ...),
we choose to avoid heavily bundling `DirectSum.decompose`, instead making copies for the
`AddEquiv`, `LinearEquiv`, etc. This means we have to repeat statements that follow from these
bundled homs, but means we don't have to repeat statements for different types of decomposition.
-/

@[expose] public section


variable {ι R M σ : Type*}

open DirectSum

namespace DirectSum

section AddCommMonoid

variable [DecidableEq ι] [AddCommMonoid M]
variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)

/-- A decomposition is an equivalence between an additive monoid `M` and a direct sum of additive
submonoids `ℳ i` of that `M`, such that the "recomposition" is canonical. This definition also
works for additive groups and modules.

This is a version of `DirectSum.IsInternal` which comes with a constructive inverse to the
canonical "recomposition" rather than just a proof that the "recomposition" is bijective.

Often it is easier to construct a term of this type via `Decomposition.ofAddHom` or
`Decomposition.ofLinearMap`. -/
/-
**DirectSum.Decomposition** 是 Mathlib 中的一个归纳类型，位于命名空间 `DirectSum`。
形式化陈述：{ι : Type u_1} →   {M : Type u_3} →     {σ : Type u_4} →       [DecidableE
q ι] →         [inst : AddCommMonoid M] → [inst_1 : SetLike σ M] → [AddSubmonoid
Class σ M] → (ι → σ) → Type (max u_1 u_3)
参数：ι → σ；max u_1 u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A decomposition is an equivalence between an additive monoid `M` and a direct su
m of additive
submonoids `ℳ i` of that `M`, such that the "recomposition" is canonical. This d
efinition also
works for additive groups and modules.

This is a version of `DirectSum.IsInternal` which comes with a constructive inve
rse to the
canonical "recomposition" rather than just a proof that the "recomposition" is b
ijective.

Often it is easier to construct a term of this type via `Decomposition.ofAddHom`
 or
`Decomposition.ofLinearMap`.
-/
class Decomposition where
  decompose' : M → ⨁ i, ℳ i
  left_inv : Function.LeftInverse (DirectSum.coeAddMonoidHom ℳ) decompose'
  right_inv : Function.RightInverse (DirectSum.coeAddMonoidHom ℳ) decompose'

/-- `DirectSum.Decomposition` instances, while carrying data, are always equal. -/
/-
**DirectSum.** 是 Mathlib 中的一个实例，位于命名空间 `DirectSum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`DirectSum.Decomposition` instances, while carrying data, are always equal.
-/
instance : Subsingleton (Decomposition ℳ) :=
  ⟨fun x y ↦ by
    obtain ⟨_, _, xr⟩ := x
    obtain ⟨_, yl, _⟩ := y
    congr
    exact Function.LeftInverse.eq_rightInverse xr yl⟩

/-- A convenience method to construct a decomposition from an `AddMonoidHom`, such that the proofs
of left and right inverse can be constructed via `ext`. -/
/-
**DirectSum.Decomposition.ofAddHom** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum.Decompos
ition`。
形式化陈述：{ι : Type u_1} →   {M : Type u_3} →     {σ : Type u_4} →       [inst : Dec
idableEq ι] →         [inst_1 : AddCommMonoid M] →           [inst_2 : SetLike σ
 M] →             [inst_3 : AddSubmonoidClass σ M] →               (ℳ : ι → σ) →
                 (decompose : M →+ DirectSum ι fun i => ↥(ℳ i)) →               
    (DirectSum.coeAddMonoidHom ℳ).comp decompose = AddMonoidHom.id M →          
           decompose.comp (DirectSum.coeAddMonoidHom ℳ) = AddMonoidHom.id (Direc
tSum ι fun i => ↥(ℳ i)) →                       DirectSum.Decomposition ℳ
参数：ℳ : ι → σ；decompose : M →+ DirectSum ι fun i => ↥(ℳ i)；DirectSum.coeAddMonoid
Hom ℳ；DirectSum.coeAddMonoidHom ℳ；DirectSum ι fun i => ↥(ℳ i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A convenience method to construct a decomposition from an `AddMonoidHom`, such t
hat the proofs
of left and right inverse can be constructed via `ext`.
-/
abbrev Decomposition.ofAddHom (decompose : M →+ ⨁ i, ℳ i)
    (h_left_inv : (DirectSum.coeAddMonoidHom ℳ).comp decompose = .id _)
    (h_right_inv : decompose.comp (DirectSum.coeAddMonoidHom ℳ) = .id _) : Decomposition ℳ where
  decompose' := decompose
  left_inv := DFunLike.congr_fun h_left_inv
  right_inv := DFunLike.congr_fun h_right_inv

/-- Noncomputably conjure a decomposition instance from a `DirectSum.IsInternal` proof. -/
@[instance_reducible]
/-
**DirectSum.IsInternal.chooseDecomposition** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum.
IsInternal`。
形式化陈述：{ι : Type u_1} →   {M : Type u_3} →     {σ : Type u_4} →       [inst : Dec
idableEq ι] →         [inst_1 : AddCommMonoid M] →           [inst_2 : SetLike σ
 M] →             [inst_3 : AddSubmonoidClass σ M] → (ℳ : ι → σ) → DirectSum.IsI
nternal ℳ → DirectSum.Decomposition ℳ
参数：ℳ : ι → σ。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Noncomputably conjure a decomposition instance from a `DirectSum.IsInternal` pro
of.
-/
noncomputable def IsInternal.chooseDecomposition (h : IsInternal ℳ) :
    DirectSum.Decomposition ℳ where
  decompose' := (Equiv.ofBijective _ h).symm
  left_inv := (Equiv.ofBijective _ h).right_inv
  right_inv := (Equiv.ofBijective _ h).left_inv

variable [Decomposition ℳ]
/-
**DirectSum.Decomposition.isInternal** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum.Decomp
osition`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_3} {σ : Type u_4} [inst : DecidableEq ι] [ins
t_1 : AddCommMonoid M] [inst_2 : SetLike σ M]   [inst_3 : AddSubmonoidClass σ M]
 (ℳ : ι → σ) [DirectSum.Decomposition ℳ], DirectSum.IsInternal ℳ
参数：ℳ : ι → σ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.RightInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.RightInverse f g → Function.Injective f
· 使用定理 `DirectSum.Decomposition.right_inv`：∀ {ι : Type u_1} {M : Type u_3} {σ : 
Type u_4} {inst : DecidableEq ι} {inst_1 : AddCommMonoid M} {inst_2 : SetLike σ 
M}   {inst_3 : AddSubmo…
· 使用定理 `Function.LeftInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.LeftInverse f g → Function.Surjective f
· 使用定理 `DirectSum.Decomposition.left_inv`：∀ {ι : Type u_1} {M : Type u_3} {σ : T
ype u_4} {inst : DecidableEq ι} {inst_1 : AddCommMonoid M} {inst_2 : SetLike σ M
}   {inst_3 : AddSubmo…
-/
protected theorem Decomposition.isInternal : DirectSum.IsInternal ℳ :=
  ⟨Decomposition.right_inv.injective, Decomposition.left_inv.surjective⟩

/-- If `M` is graded by `ι` with degree `i` component `ℳ i`, then it is isomorphic as
to a direct sum of components. This is the canonical spelling of the `decompose'` field. -/
/-
**DirectSum.decompose** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：decompose : M ≃ ⨁ i, ℳ i where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.Decomposition.left_inv`：∀ {ι : Type u_1} {M : Type u_3} {σ : T
ype u_4} {inst : DecidableEq ι} {inst_1 : AddCommMonoid M} {inst_2 : SetLike σ M
}   {inst_3 : AddSubmo…
· 使用定理 `DirectSum.Decomposition.right_inv`：∀ {ι : Type u_1} {M : Type u_3} {σ : 
Type u_4} {inst : DecidableEq ι} {inst_1 : AddCommMonoid M} {inst_2 : SetLike σ 
M}   {inst_3 : AddSubmo…

--- 原说明 ---
If `M` is graded by `ι` with degree `i` component `ℳ i`, then it is isomorphic a
s
to a direct sum of components. This is the canonical spelling of the `decompose'
` field.
-/
def decompose : M ≃ ⨁ i, ℳ i where
  toFun := Decomposition.decompose'
  invFun := DirectSum.coeAddMonoidHom ℳ
  left_inv := Decomposition.left_inv
  right_inv := Decomposition.right_inv

omit [AddSubmonoidClass σ M] in
/-- A substructure `p ⊆ M` is homogeneous if for every `m ∈ p`, all homogeneous components
  of `m` are in `p`. -/
/-
**DirectSum.SetLike.IsHomogeneous** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum.SetLike`。
形式化陈述：{ι : Type u_1} →   {M : Type u_3} →     {σ : Type u_4} →       [inst : Dec
idableEq ι] →         [inst_1 : AddCommMonoid M] →           [inst_2 : SetLike σ
 M] →             [inst_3 : AddSubmonoidClass σ M] →               (ℳ : ι → σ) →
 [DirectSum.Decomposition ℳ] → {P : Type u_5} → [SetLike P M] → P → Prop
参数：ℳ : ι → σ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A substructure `p ⊆ M` is homogeneous if for every `m ∈ p`, all homogeneous comp
onents
  of `m` are in `p`.
-/
def SetLike.IsHomogeneous {P : Type*} [SetLike P M] (p : P) : Prop :=
  ∀ (i : ι) ⦃m : M⦄, m ∈ p → (DirectSum.decompose ℳ m i : M) ∈ p

@[elab_as_elim]
/-
**DirectSum.Decomposition.inductionOn** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum.Decom
position`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_3} {σ : Type u_4} [inst : DecidableEq ι] [ins
t_1 : AddCommMonoid M] [inst_2 : SetLike σ M]   [inst_3 : AddSubmonoidClass σ M]
 (ℳ : ι → σ) [DirectSum.Decomposition ℳ] {motive : M → Prop},   motive 0 →     (
∀ {i : ι} (m : ↥(ℳ i)), motive ↑m) → (∀ (m m' : M), motive m → motive m' → motiv
e (m + m')) → ∀ (m : M), motive m
参数：ℳ : ι → σ；∀ {i : ι} (m : ↥(ℳ i)), motive ↑m；∀ (m m' : M), motive m → motive m
' → motive (m + m')；m : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubmonoid.instAddSubmonoidClass`：∀ {M : Type u_1} [inst : AddZeroClas
s M], AddSubmonoidClass (AddSubmonoid M) M
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
· 使用定理 `trivial`：True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DirectSum.IsInternal.addSubmonoid_iSup_eq_top`：∀ {ι : Type v} {M : Type 
u_1} [inst : DecidableEq ι] [inst_1 : AddCommMonoid M] (A : ι → AddSubmonoid M),
   DirectSum.IsInternal A → iSup A …
· 使用定理 `DirectSum.Decomposition.isInternal`：∀ {ι : Type u_1} {M : Type u_3} {σ :
 Type u_4} [inst : DecidableEq ι] [inst_1 : AddCommMonoid M] [inst_2 : SetLike σ
 M]   [inst_3 : AddSubmo…
· 使用定理 `AddSubmonoid.iSup_induction`：∀ {M : Type u_1} [inst : AddZeroClass M] {ι
 : Sort u_4} (S : ι → AddSubmonoid M) {motive : M → Prop} {x : M},   x ∈ ⨆ i, S 
i →     (∀ (i : ι…
-/
protected theorem Decomposition.inductionOn {motive : M → Prop} (zero : motive 0)
    (homogeneous : ∀ {i} (m : ℳ i), motive (m : M))
    (add : ∀ m m' : M, motive m → motive m' → motive (m + m')) : ∀ m, motive m := by
  let ℳ' : ι → AddSubmonoid M := fun i ↦
    (⟨⟨ℳ i, fun x y ↦ AddMemClass.add_mem x y⟩, (ZeroMemClass.zero_mem _)⟩ : AddSubmonoid M)
  have t : DirectSum.Decomposition ℳ' :=
    { decompose' := DirectSum.decompose ℳ
      left_inv := fun _ ↦ (decompose ℳ).left_inv _
      right_inv := fun _ ↦ (decompose ℳ).right_inv _ }
  have mem : ∀ m, m ∈ iSup ℳ' := fun _m ↦
    (DirectSum.IsInternal.addSubmonoid_iSup_eq_top ℳ' (Decomposition.isInternal ℳ')).symm ▸ trivial
  -- Porting note: needs to use @ even though no implicit argument is provided
  exact fun m ↦ @AddSubmonoid.iSup_induction _ _ _ ℳ' _ _ (mem m)
    (fun i m h ↦ homogeneous ⟨m, h⟩) zero add
--  exact fun m ↦
--    AddSubmonoid.iSup_induction ℳ' (mem m) (fun i m h ↦ h_homogeneous ⟨m, h⟩) h_zero h_add

@[simp]
/-
**DirectSum.Decomposition.decompose'_eq** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum.Dec
omposition`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_3} {σ : Type u_4} [inst : DecidableEq ι] [ins
t_1 : AddCommMonoid M] [inst_2 : SetLike σ M]   [inst_3 : AddSubmonoidClass σ M]
 (ℳ : ι → σ) [inst_4 : DirectSum.Decomposition ℳ],   DirectSum.Decomposition.dec
ompose' = ⇑(DirectSum.decompose ℳ)
参数：ℳ : ι → σ；DirectSum.decompose ℳ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Decomposition.decompose'_eq : Decomposition.decompose' = decompose ℳ := rfl

@[simp]
/-
**DirectSum.decompose_symm_of** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：decompose_symm_of {i : ι} (x : ℳ i) : (decompose ℳ).symm (DirectSum.of _ i
 x) = x
参数：x : ℳ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.coeAddMonoidHom_of`：coeAddMonoidHom_of {M S : Type*} [Decidabl
eEq ι] [AddCommMonoid M] [SetLike S M] [AddSubmonoidClass S M] (A : ι -> S) (i :
 ι) (x : A i) : Di…
-/
theorem decompose_symm_of {i : ι} (x : ℳ i) : (decompose ℳ).symm (DirectSum.of _ i x) = x :=
  DirectSum.coeAddMonoidHom_of ℳ _ _

@[simp]
/-
**DirectSum.decompose_coe** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：decompose_coe {i : ι} (x : ℳ i) : decompose ℳ (x : M) = DirectSum.of _ i x
参数：x : ℳ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DirectSum.decompose_symm_of`：decompose_symm_of {i : ι} (x : ℳ i) : (deco
mpose ℳ).symm (DirectSum.of _ i x) = x
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
theorem decompose_coe {i : ι} (x : ℳ i) : decompose ℳ (x : M) = DirectSum.of _ i x := by
  rw [← decompose_symm_of _, Equiv.apply_symm_apply]
/-
**DirectSum.decompose_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：decompose_of_mem {x : M} {i : ι} (hx : x in ℳ i) : decompose ℳ x = DirectS
um.of (fun i => ℳ i) i ⟨x, hx⟩
参数：hx : x in ℳ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.decompose_coe`：decompose_coe {i : ι} (x : ℳ i) : decompose ℳ (
x : M) = DirectSum.of _ i x
-/
theorem decompose_of_mem {x : M} {i : ι} (hx : x ∈ ℳ i) :
    decompose ℳ x = DirectSum.of (fun i ↦ ℳ i) i ⟨x, hx⟩ :=
  decompose_coe _ ⟨x, hx⟩
/-
**DirectSum.decompose_of_mem_same** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：decompose_of_mem_same {x : M} {i : ι} (hx : x in ℳ i) : (decompose ℳ x i :
 M) = x
参数：hx : x in ℳ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.decompose_of_mem`：decompose_of_mem {x : M} {i : ι} (hx : x in 
ℳ i) : decompose ℳ x = DirectSum.of (fun i => ℳ i) i ⟨x, hx⟩
· 使用定理 `DirectSum.of_eq_same`：of_eq_same (i : ι) (x : β i) : (of _ i x) i = x
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
-/
theorem decompose_of_mem_same {x : M} {i : ι} (hx : x ∈ ℳ i) : (decompose ℳ x i : M) = x := by
  rw [decompose_of_mem _ hx, DirectSum.of_eq_same, Subtype.coe_mk]
/-
**DirectSum.decompose_of_mem_ne** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：decompose_of_mem_ne {x : M} {i j : ι} (hx : x in ℳ i) (hij : i != j) : (de
compose ℳ x j : M) = 0
参数：hx : x in ℳ i；hij : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.decompose_of_mem`：decompose_of_mem {x : M} {i : ι} (hx : x in 
ℳ i) : decompose ℳ x = DirectSum.of (fun i => ℳ i) i ⟨x, hx⟩
· 使用定理 `DirectSum.of_eq_of_ne`：of_eq_of_ne (i j : ι) (x : β i) (h : j != i) : (o
f _ i x) j = 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ZeroMemClass.coe_zero`：∀ {A : Type u_3} {M₁ : Type u_4} [inst : SetLike 
A M₁] [inst_1 : Zero M₁] [hA : ZeroMemClass A M₁] (S' : A), ↑0 = 0
-/
theorem decompose_of_mem_ne {x : M} {i j : ι} (hx : x ∈ ℳ i) (hij : i ≠ j) :
    (decompose ℳ x j : M) = 0 := by
  rw [decompose_of_mem _ hx, DirectSum.of_eq_of_ne _ _ _ hij.symm, ZeroMemClass.coe_zero]
/-
**DirectSum.degree_eq_of_mem_mem** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：degree_eq_of_mem_mem {x : M} {i j : ι} (hxi : x in ℳ i) (hxj : x in ℳ j) (
hx : x != 0) : i = j
参数：hxi : x in ℳ i；hxj : x in ℳ j；hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DirectSum.decompose_of_mem_same`：decompose_of_mem_same {x : M} {i : ι} (
hx : x in ℳ i) : (decompose ℳ x i : M) = x
· 使用定理 `DirectSum.decompose_of_mem_ne`：decompose_of_mem_ne {x : M} {i j : ι} (hx
 : x in ℳ i) (hij : i != j) : (decompose ℳ x j : M) = 0
-/
theorem degree_eq_of_mem_mem {x : M} {i j : ι} (hxi : x ∈ ℳ i) (hxj : x ∈ ℳ j) (hx : x ≠ 0) :
    i = j := by
  contrapose! hx; rw [← decompose_of_mem_same ℳ hxj, decompose_of_mem_ne ℳ hxi hx]

#adaptation_note
/--
`simps!` won't apply `AddEquiv.symm_mk` without the `id <|` in `map_add'`.
`decompose` and `Equiv.symm` are not implicit-reducible, so the type of the proof doesn't match the
expected type up to implicit reducibility. If we remove `id`, we don't get an immediate error,
but some downstream declarations will break.
-/
/-- If `M` is graded by `ι` with degree `i` component `ℳ i`, then it is isomorphic as
an additive monoid to a direct sum of components. -/
@[simps!]
/-
**DirectSum.decomposeAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：decomposeAddEquiv : M ≃+ ⨁ i, ℳ i
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `M` is graded by `ι` with degree `i` component `ℳ i`, then it is isomorphic a
s
an additive monoid to a direct sum of components.
-/
def decomposeAddEquiv : M ≃+ ⨁ i, ℳ i :=
  AddEquiv.symm { (decompose ℳ).symm with
    map_add' := id <| map_add (DirectSum.coeAddMonoidHom ℳ) }

@[simp]
/-
**DirectSum.decompose_zero** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：decompose_zero : decompose ℳ (0 : M) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
theorem decompose_zero : decompose ℳ (0 : M) = 0 :=
  map_zero (decomposeAddEquiv ℳ)

@[simp]
/-
**DirectSum.decompose_symm_zero** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：decompose_symm_zero : (decompose ℳ).symm 0 = (0 : M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
theorem decompose_symm_zero : (decompose ℳ).symm 0 = (0 : M) :=
  map_zero (decomposeAddEquiv ℳ).symm

@[simp]
/-
**DirectSum.decompose_add** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：decompose_add (x y : M) : decompose ℳ (x + y) = decompose ℳ x + decompose 
ℳ y
参数：x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
theorem decompose_add (x y : M) : decompose ℳ (x + y) = decompose ℳ x + decompose ℳ y :=
  map_add (decomposeAddEquiv ℳ) x y

@[simp]
/-
**DirectSum.decompose_symm_add** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：decompose_symm_add (x y : ⨁ i, ℳ i) : (decompose ℳ).symm (x + y) = (decomp
ose ℳ).symm x + (decompose ℳ).symm y
参数：x y : ⨁ i, ℳ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
theorem decompose_symm_add (x y : ⨁ i, ℳ i) :
    (decompose ℳ).symm (x + y) = (decompose ℳ).symm x + (decompose ℳ).symm y :=
  map_add (decomposeAddEquiv ℳ).symm x y

@[simp]
/-
**DirectSum.decompose_sum** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：decompose_sum {ι'} (s : Finset ι') (f : ι' -> M) : decompose ℳ (∑ i in s, 
f i) = ∑ i in s, decompose ℳ (f i)
参数：s : Finset ι'；f : ι' -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
theorem decompose_sum {ι'} (s : Finset ι') (f : ι' → M) :
    decompose ℳ (∑ i ∈ s, f i) = ∑ i ∈ s, decompose ℳ (f i) :=
  map_sum (decomposeAddEquiv ℳ) f s

@[simp]
/-
**DirectSum.decompose_symm_sum** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：decompose_symm_sum {ι'} (s : Finset ι') (f : ι' -> ⨁ i, ℳ i) : (decompose 
ℳ).symm (∑ i in s, f i) = ∑ i in s, (decompose ℳ).symm (f i)
参数：s : Finset ι'；f : ι' -> ⨁ i, ℳ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
theorem decompose_symm_sum {ι'} (s : Finset ι') (f : ι' → ⨁ i, ℳ i) :
    (decompose ℳ).symm (∑ i ∈ s, f i) = ∑ i ∈ s, (decompose ℳ).symm (f i) :=
  map_sum (decomposeAddEquiv ℳ).symm f s
/-
**DirectSum.sum_support_decompose** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：sum_support_decompose [forall (i) (x : ℳ i), Decidable (x != 0)] (r : M) :
 (∑ i in (decompose ℳ r).support, (decompose ℳ r i : M)) = r
参数：i；x : ℳ i；x != 0；r : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `DirectSum.sum_support_of`：sum_support_of [forall (i : ι) (x : β i), Deci
dable (x != 0)] (x : ⨁ i, β i) : (∑ i in x.support, of β i (x i)) = x
· 使用定理 `DirectSum.decompose_symm_sum`：decompose_symm_sum {ι'} (s : Finset ι') (f
 : ι' -> ⨁ i, ℳ i) : (decompose ℳ).symm (∑ i in s, f i) = ∑ i in s, (decompose ℳ
).symm (f i)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `DirectSum.decompose_symm_of`：decompose_symm_of {i : ι} (x : ℳ i) : (deco
mpose ℳ).symm (DirectSum.of _ i x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_support_decompose [∀ (i) (x : ℳ i), Decidable (x ≠ 0)] (r : M) :
    (∑ i ∈ (decompose ℳ r).support, (decompose ℳ r i : M)) = r := by
  conv_rhs =>
    rw [← (decompose ℳ).symm_apply_apply r, ← sum_support_of (decompose ℳ r)]
  rw [decompose_symm_sum]
  simp_rw [decompose_symm_of]
/-
**DirectSum.AddSubmonoidClass.IsHomogeneous.mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `D
irectSum.AddSubmonoidClass.IsHomogeneous`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_3} {σ : Type u_4} [inst : DecidableEq ι] [ins
t_1 : AddCommMonoid M] [inst_2 : SetLike σ M]   [inst_3 : AddSubmonoidClass σ M]
 (ℳ : ι → σ) [inst_4 : DirectSum.Decomposition ℳ] {P : Type u_5}   [inst_5 : Set
Like P M] [AddSubmonoidClass P M] (p : P),   DirectSum.SetLike.IsHomogeneous ℳ p
 → ∀ {x : M}, x ∈ p ↔ ∀ (i : ι), ↑(((DirectSum.decompose ℳ) x) i) ∈ p
参数：ℳ : ι → σ；p : P；i : ι；((DirectSum.decompose ℳ) x) i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DirectSum.sum_support_decompose`：sum_support_decompose [forall (i) (x : 
ℳ i), Decidable (x != 0)] (r : M) : (∑ i in (decompose ℳ r).support, (decompose 
ℳ r i : M)) = r
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
-/
theorem AddSubmonoidClass.IsHomogeneous.mem_iff
    {P : Type*} [SetLike P M] [AddSubmonoidClass P M] (p : P)
    (hp : SetLike.IsHomogeneous ℳ p) {x} :
    x ∈ p ↔ ∀ i, (decompose ℳ x i : M) ∈ p := by
  classical
  refine ⟨fun hx i ↦ hp i hx, fun hx ↦ ?_⟩
  rw [← DirectSum.sum_support_decompose ℳ x]
  exact sum_mem (fun i _ ↦ hx i)
/-
**DirectSum.AddSubmonoidClass.IsHomogeneous.ext** 是 Mathlib 中的一个定理，位于命名空间 `Direc
tSum.AddSubmonoidClass.IsHomogeneous`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_3} {σ : Type u_4} [inst : DecidableEq ι] [ins
t_1 : AddCommMonoid M] [inst_2 : SetLike σ M]   [inst_3 : AddSubmonoidClass σ M]
 {ℳ : ι → σ} [inst_4 : DirectSum.Decomposition ℳ] {P : Type u_5}   [inst_5 : Set
Like P M] [AddSubmonoidClass P M] {p q : P},   DirectSum.SetLike.IsHomogeneous ℳ
 p →     DirectSum.SetLike.IsHomogeneous ℳ q → (∀ (i : ι), ∀ m ∈ ℳ i, m ∈ p ↔ m 
∈ q) → p = q
参数：∀ (i : ι), ∀ m ∈ ℳ i, m ∈ p ↔ m ∈ q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.AddSubmonoidClass.IsHomogeneous.mem_iff`：∀ {ι : Type u_1} {M :
 Type u_3} {σ : Type u_4} [inst : DecidableEq ι] [inst_1 : AddCommMonoid M] [ins
t_2 : SetLike σ M]   [inst_3 : AddSubmo…
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem AddSubmonoidClass.IsHomogeneous.ext
    {ℳ : ι → σ} [Decomposition ℳ] {P : Type*} [SetLike P M] [AddSubmonoidClass P M]
    {p q : P} (hp : SetLike.IsHomogeneous ℳ p) (hq : SetLike.IsHomogeneous ℳ q)
    (hpq : ∀ i, ∀ m ∈ ℳ i, m ∈ p ↔ m ∈ q) :
    p = q := by
  refine SetLike.ext fun m ↦ ?_
  rw [AddSubmonoidClass.IsHomogeneous.mem_iff ℳ p hp,
    AddSubmonoidClass.IsHomogeneous.mem_iff ℳ q hq]
  exact forall_congr' fun i ↦ hpq i _ (decompose ℳ _ i).2

end AddCommMonoid

section AddCommGroup

variable [DecidableEq ι] [AddCommGroup M]
variable [SetLike σ M] [AddSubgroupClass σ M] (ℳ : ι → σ)
variable [Decomposition ℳ]

@[simp]
/-
**DirectSum.decompose_neg** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：decompose_neg (x : M) : decompose ℳ (-x) = -decompose ℳ x
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
theorem decompose_neg (x : M) : decompose ℳ (-x) = -decompose ℳ x :=
  map_neg (decomposeAddEquiv ℳ) x

@[simp]
/-
**DirectSum.decompose_symm_neg** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：decompose_symm_neg (x : ⨁ i, ℳ i) : (decompose ℳ).symm (-x) = -(decompose 
ℳ).symm x
参数：x : ⨁ i, ℳ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
theorem decompose_symm_neg (x : ⨁ i, ℳ i) : (decompose ℳ).symm (-x) = -(decompose ℳ).symm x :=
  map_neg (decomposeAddEquiv ℳ).symm x

@[simp]
/-
**DirectSum.decompose_sub** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：decompose_sub (x y : M) : decompose ℳ (x - y) = decompose ℳ x - decompose 
ℳ y
参数：x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
theorem decompose_sub (x y : M) : decompose ℳ (x - y) = decompose ℳ x - decompose ℳ y :=
  map_sub (decomposeAddEquiv ℳ) x y

@[simp]
/-
**DirectSum.decompose_symm_sub** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：decompose_symm_sub (x y : ⨁ i, ℳ i) : (decompose ℳ).symm (x - y) = (decomp
ose ℳ).symm x - (decompose ℳ).symm y
参数：x y : ⨁ i, ℳ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
theorem decompose_symm_sub (x y : ⨁ i, ℳ i) :
    (decompose ℳ).symm (x - y) = (decompose ℳ).symm x - (decompose ℳ).symm y :=
  map_sub (decomposeAddEquiv ℳ).symm x y

end AddCommGroup

section Module

variable [DecidableEq ι] [Semiring R] [AddCommMonoid M] [Module R M]
variable (ℳ : ι → Submodule R M)

/-- A convenience method to construct a decomposition from an `LinearMap`, such that the proofs
of left and right inverse can be constructed via `ext`. -/
/-
**DirectSum.Decomposition.ofLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum.Decom
position`。
形式化陈述：{ι : Type u_1} →   {R : Type u_2} →     {M : Type u_3} →       [inst : Dec
idableEq ι] →         [inst_1 : Semiring R] →           [inst_2 : AddCommMonoid 
M] →             [inst_3 : _root_.Module R M] →               (ℳ : ι → Submodule
 R M) →                 (decompose : M →ₗ[R] DirectSum ι fun i => ↥(ℳ i)) →     
              DirectSum.coeLinearMap ℳ ∘ₗ decompose = LinearMap.id →            
         decompose ∘ₗ DirectSum.coeLinearMap ℳ = LinearMap.id → DirectSum.Decomp
osition ℳ
参数：ℳ : ι → Submodule R M；decompose : M →ₗ[R] DirectSum ι fun i => ↥(ℳ i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A convenience method to construct a decomposition from an `LinearMap`, such that
 the proofs
of left and right inverse can be constructed via `ext`.
-/
abbrev Decomposition.ofLinearMap (decompose : M →ₗ[R] ⨁ i, ℳ i)
    (h_left_inv : DirectSum.coeLinearMap ℳ ∘ₗ decompose = .id)
    (h_right_inv : decompose ∘ₗ DirectSum.coeLinearMap ℳ = .id) : Decomposition ℳ where
  decompose' := decompose
  left_inv := DFunLike.congr_fun h_left_inv
  right_inv := DFunLike.congr_fun h_right_inv

variable [Decomposition ℳ]

/-- If `M` is graded by `ι` with degree `i` component `ℳ i`, then it is isomorphic as
a module to a direct sum of components. -/
/-
**DirectSum.decomposeLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：decomposeLinearEquiv : M ≃ₗ[R] ⨁ i, ℳ i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M` is graded by `ι` with degree `i` component `ℳ i`, then it is isomorphic a
s
a module to a direct sum of components.
-/
def decomposeLinearEquiv : M ≃ₗ[R] ⨁ i, ℳ i :=
  LinearEquiv.symm
    { (decomposeAddEquiv ℳ).symm with map_smul' := map_smul (DirectSum.coeLinearMap ℳ) }
/-
**DirectSum.decomposeLinearEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：decomposeLinearEquiv_apply (m : M) : decomposeLinearEquiv ℳ m = decompose 
ℳ m
参数：m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem decomposeLinearEquiv_apply (m : M) :
    decomposeLinearEquiv ℳ m = decompose ℳ m := rfl
/-
**DirectSum.decomposeLinearEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum
`。
形式化陈述：decomposeLinearEquiv_symm_apply (m : ⨁ i, ℳ i) : (decomposeLinearEquiv ℳ).
symm m = (decompose ℳ).symm m
参数：m : ⨁ i, ℳ i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem decomposeLinearEquiv_symm_apply (m : ⨁ i, ℳ i) :
    (decomposeLinearEquiv ℳ).symm m = (decompose ℳ).symm m := rfl

@[simp]
/-
**DirectSum.decompose_smul** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：decompose_smul (r : R) (x : M) : decompose ℳ (r • x) = r • decompose ℳ x
参数：r : R；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
-/
theorem decompose_smul (r : R) (x : M) : decompose ℳ (r • x) = r • decompose ℳ x :=
  map_smul (decomposeLinearEquiv ℳ) r x
/-
**DirectSum.decomposeLinearEquiv_symm_comp_lof** 是 Mathlib 中的一个定理，位于命名空间 `Direct
Sum`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} [inst : DecidableEq ι] [ins
t_1 : Semiring R] [inst_2 : AddCommMonoid M]   [inst_3 : _root_.Module R M] (ℳ :
 ι → Submodule R M) [inst_4 : DirectSum.Decomposition ℳ] (i : ι),   ↑(DirectSum.
decomposeLinearEquiv ℳ).symm ∘ₗ DirectSum.lof R ι (fun x => ↥(ℳ x)) i = (ℳ i).su
btype
参数：ℳ : ι → Submodule R M；i : ι；DirectSum.decomposeLinearEquiv ℳ；fun x => ↥(ℳ x)；
ℳ i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `DirectSum.decompose_symm_of`：decompose_symm_of {i : ι} (x : ℳ i) : (deco
mpose ℳ).symm (DirectSum.of _ i x) = x
-/
@[simp] theorem decomposeLinearEquiv_symm_comp_lof (i : ι) :
    (decomposeLinearEquiv ℳ).symm ∘ₗ lof R ι (ℳ ·) i = (ℳ i).subtype :=
  LinearMap.ext <| decompose_symm_of _
/-
**DirectSum.decomposeLinearEquiv_symm_lof** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} [inst : DecidableEq ι] [ins
t_1 : Semiring R] [inst_2 : AddCommMonoid M]   [inst_3 : _root_.Module R M] (ℳ :
 ι → Submodule R M) [inst_4 : DirectSum.Decomposition ℳ] (i : ι) (x : ↥(ℳ i)),  
 (DirectSum.decomposeLinearEquiv ℳ).symm ((DirectSum.lof R ι (fun i => ↥(ℳ i)) i
) x) = ↑x
参数：ℳ : ι → Submodule R M；i : ι；x : ↥(ℳ i)；DirectSum.decomposeLinearEquiv ℳ；(Dire
ctSum.lof R ι (fun i => ↥(ℳ i)) i) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.decomposeLinearEquiv_symm_comp_lof`：∀ {ι : Type u_1} {R : Type
 u_2} {M : Type u_3} [inst : DecidableEq ι] [inst_1 : Semiring R] [inst_2 : AddC
ommMonoid M]   [inst_3 : _root_.Mo…
-/
@[simp] lemma decomposeLinearEquiv_symm_lof (i : ι) (x : ℳ i) :
    (decomposeLinearEquiv ℳ).symm (lof R _ _ i x) = x :=
  congr($(decomposeLinearEquiv_symm_comp_lof ℳ i) x)
/-
**DirectSum.decomposeLinearEquiv_apply_coe** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`
。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} [inst : DecidableEq ι] [ins
t_1 : Semiring R] [inst_2 : AddCommMonoid M]   [inst_3 : _root_.Module R M] (ℳ :
 ι → Submodule R M) [inst_4 : DirectSum.Decomposition ℳ] (i : ι) (x : ↥(ℳ i)),  
 (DirectSum.decomposeLinearEquiv ℳ) ↑x = (DirectSum.lof R ι (fun i => ↥(ℳ i)) i)
 x
参数：ℳ : ι → Submodule R M；i : ι；x : ↥(ℳ i)；DirectSum.decomposeLinearEquiv ℳ；Direc
tSum.lof R ι (fun i => ↥(ℳ i)) i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearEquiv.eq_symm_apply`：eq_symm_apply {x y} : y = e.symm x ↔ e y = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DirectSum.decomposeLinearEquiv_symm_lof`：∀ {ι : Type u_1} {R : Type u_2}
 {M : Type u_3} [inst : DecidableEq ι] [inst_1 : Semiring R] [inst_2 : AddCommMo
noid M]   [inst_3 : _root_.Mo…
-/
@[simp] lemma decomposeLinearEquiv_apply_coe (i : ι) (x : ℳ i) :
    decomposeLinearEquiv ℳ x = lof R _ _ i x :=
  (LinearEquiv.eq_symm_apply _).mp (decomposeLinearEquiv_symm_lof ..).symm

/-- Two linear maps from a module with a decomposition agree if they agree on every piece.

Note this cannot be `@[ext]` as `ℳ` cannot be inferred. -/
/-
**DirectSum.decompose_lhom_ext** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：decompose_lhom_ext {N} [AddCommMonoid N] [Module R N] ⦃f g : M ->ₗ[R] N⦄ (
h : forall i, f ∘ₗ (ℳ i).subtype = g ∘ₗ (ℳ i).subtype) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
· 使用定理 `DirectSum.linearMap_ext`：linearMap_ext ⦃ψ ψ' : (⨁ i, M i) ->ₗ[R] N⦄ (H :
 forall i, ψ.comp (lof R ι M i) = ψ'.comp (lof R ι M i)) : ψ = ψ'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `DirectSum.decomposeLinearEquiv_symm_comp_lof`：∀ {ι : Type u_1} {R : Type
 u_2} {M : Type u_3} [inst : DecidableEq ι] [inst_1 : Semiring R] [inst_2 : AddC
ommMonoid M]   [inst_3 : _root_.Mo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x

--- 原说明 ---
Two linear maps from a module with a decomposition agree if they agree on every 
piece.

Note this cannot be `@[ext]` as `ℳ` cannot be inferred.
-/
theorem decompose_lhom_ext {N} [AddCommMonoid N] [Module R N] ⦃f g : M →ₗ[R] N⦄
    (h : ∀ i, f ∘ₗ (ℳ i).subtype = g ∘ₗ (ℳ i).subtype) : f = g :=
  LinearMap.ext <| (decomposeLinearEquiv ℳ).symm.surjective.forall.mpr <|
    suffices f ∘ₗ (decomposeLinearEquiv ℳ).symm
           = (g ∘ₗ (decomposeLinearEquiv ℳ).symm : (⨁ i, ℳ i) →ₗ[R] N) from
      DFunLike.congr_fun this
    linearMap_ext _ fun i => by
      simp_rw [LinearMap.comp_assoc, decomposeLinearEquiv_symm_comp_lof ℳ i, h]

end Module

end DirectSum

