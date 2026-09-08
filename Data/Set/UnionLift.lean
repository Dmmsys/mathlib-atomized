/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Data.Set.Lattice
public import Mathlib.Order.Directed

/-!
# Union lift

This file defines `Set.iUnionLift` to glue together functions defined on each of a collection of
sets to make a function on the Union of those sets.

## Main definitions

* `Set.iUnionLift` -  Given a Union of sets `iUnion S`, define a function on any subset of the Union
  by defining it on each component, and proving that it agrees on the intersections.
* `Set.liftCover` - Version of `Set.iUnionLift` for the special case that the sets cover the
  entire type.

## Main statements

There are proofs of the obvious properties of `iUnionLift`, i.e. what it does to elements of
each of the sets in the `iUnion`, stated in different ways.

There are also three lemmas about `iUnionLift` intended to aid with proving that `iUnionLift` is a
homomorphism when defined on a Union of substructures. There is one lemma each to show that
constants, unary functions, or binary functions are preserved. These lemmas are:

* `Set.iUnionLift_const`
* `Set.iUnionLift_unary`
* `Set.iUnionLift_binary`

## Tags

directed union, directed supremum, glue, gluing
-/

@[expose] public section

variable {α : Type*} {ι β : Sort _}

namespace Set

section UnionLift

/- The unused argument is left in the definition so that the `simp` lemmas
`iUnionLift_inclusion` will work without the user having to provide it explicitly to
simplify terms involving `iUnionLift`. -/
/-- Given a union of sets `iUnion S`, define a function on the Union by defining
it on each component, and proving that it agrees on the intersections. -/
@[nolint unusedArguments]
/-
**Set.iUnionLift** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：iUnionLift (S : ι -> Set α) (f : forall i, S i -> β) (_ : forall (i j) (x 
: α) (hxi : x in S i) (hxj : x in S j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩) (T : Set α)
 (hT : T subseteq iUnion S) (x : T) : β
参数：S : ι -> Set α；f : forall i, S i -> β；_ : forall (i j) (x : α) (hxi : x in S 
i) (hxj : x in S j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩；T : Set α；hT : T subseteq iUnio
n S；x : T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a union of sets `iUnion S`, define a function on the Union by defining
it on each component, and proving that it agrees on the intersections.
-/
noncomputable def iUnionLift (S : ι → Set α) (f : ∀ i, S i → β)
    (_ : ∀ (i j) (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩) (T : Set α)
    (hT : T ⊆ iUnion S) (x : T) : β :=
  let i := Classical.indefiniteDescription _ (mem_iUnion.1 (hT x.prop))
  f i ⟨x, i.prop⟩

variable {S : ι → Set α} {f : ∀ i, S i → β}
  {hf : ∀ (i j) (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩} {T : Set α}
  {hT : T ⊆ iUnion S} (hT' : T = iUnion S)

@[simp]
/-
**Set.iUnionLift_mk** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnionLift_mk {i : ι} (x : S i) (hx : (x : α) in T) : iUnionLift S f hf T 
hT ⟨x, hx⟩ = f i x
参数：x : S i；hx : (x : α) in T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem iUnionLift_mk {i : ι} (x : S i) (hx : (x : α) ∈ T) :
    iUnionLift S f hf T hT ⟨x, hx⟩ = f i x := hf _ i x _ _
/-
**Set.iUnionLift_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnionLift_inclusion {i : ι} (x : S i) (h : S i subseteq T) : iUnionLift S
 f hf T hT (Set.inclusion h x) = f i x
参数：x : S i；h : S i subseteq T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iUnionLift_mk`：iUnionLift_mk {i : ι} (x : S i) (hx : (x : α) in T) :
 iUnionLift S f hf T hT ⟨x, hx⟩ = f i x
-/
theorem iUnionLift_inclusion {i : ι} (x : S i) (h : S i ⊆ T) :
    iUnionLift S f hf T hT (Set.inclusion h x) = f i x :=
  iUnionLift_mk x _
/-
**Set.iUnionLift_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnionLift_of_mem (x : T) {i : ι} (hx : (x : α) in S i) : iUnionLift S f h
f T hT x = f i ⟨x, hx⟩
参数：x : T；hx : (x : α) in S i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iUnionLift_of_mem (x : T) {i : ι} (hx : (x : α) ∈ S i) :
    iUnionLift S f hf T hT x = f i ⟨x, hx⟩ := by obtain ⟨x, hx⟩ := x; exact hf _ _ _ _ _
/-
**Set.preimage_iUnionLift** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_iUnionLift (t : Set β) : iUnionLift S f hf T hT ⁻¹' t = inclusion
 hT ⁻¹' (⋃ i, inclusion (subset_iUnion S i) '' f i ⁻¹' t)
参数：t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Set.iUnionLift_of_mem`：iUnionLift_of_mem (x : T) {i : ι} (hx : (x : α) i
n S i) : iUnionLift S f hf T hT x = f i ⟨x, hx⟩
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem preimage_iUnionLift (t : Set β) :
    iUnionLift S f hf T hT ⁻¹' t =
      inclusion hT ⁻¹' (⋃ i, inclusion (subset_iUnion S i) '' f i ⁻¹' t) := by
  ext x
  simp only [mem_preimage, mem_iUnion, mem_image]
  constructor
  · rcases mem_iUnion.1 (hT x.prop) with ⟨i, hi⟩
    refine fun h => ⟨i, ⟨x, hi⟩, ?_, rfl⟩
    rwa [iUnionLift_of_mem x hi] at h
  · rintro ⟨i, ⟨y, hi⟩, h, hxy⟩
    obtain rfl : y = x := congr_arg Subtype.val hxy
    rwa [iUnionLift_of_mem x hi]

/-- `iUnionLift_const` is useful for proving that `iUnionLift` is a homomorphism
  of algebraic structures when defined on the Union of algebraic subobjects.
  For example, it could be used to prove that the lift of a collection
  of group homomorphisms on a union of subgroups preserves `1`. -/
/-
**Set.iUnionLift_const** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnionLift_const (c : T) (ci : forall i, S i) (hci : forall i, (ci i : α) 
= c) (cβ : β) (h : forall i, f i (ci i) = cβ) : iUnionLift S f hf T hT c = cβ
参数：c : T；ci : forall i, S i；hci : forall i, (ci i : α) = c；cβ : β；h : forall i, 
f i (ci i) = cβ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnionLift_of_mem`：iUnionLift_of_mem (x : T) {i : ι} (hx : (x : α) i
n S i) : iUnionLift S f hf T hT x = f i ⟨x, hx⟩
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
`iUnionLift_const` is useful for proving that `iUnionLift` is a homomorphism
  of algebraic structures when defined on the Union of algebraic subobjects.
  For example, it could be used to prove that the lift of a collection
  of group homomorphisms on a union of subgroups preserves `1`.
-/
theorem iUnionLift_const (c : T) (ci : ∀ i, S i) (hci : ∀ i, (ci i : α) = c) (cβ : β)
    (h : ∀ i, f i (ci i) = cβ) : iUnionLift S f hf T hT c = cβ := by
  let ⟨i, hi⟩ := Set.mem_iUnion.1 (hT c.prop)
  have : ci i = ⟨c, hi⟩ := Subtype.ext (hci i)
  rw [iUnionLift_of_mem _ hi, ← this, h]

/-- `iUnionLift_unary` is useful for proving that `iUnionLift` is a homomorphism
  of algebraic structures when defined on the Union of algebraic subobjects.
  For example, it could be used to prove that the lift of a collection
  of `LinearMap`s on a union of submodules preserves scalar multiplication. -/
/-
**Set.iUnionLift_unary** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnionLift_unary (u : T -> T) (ui : forall i, S i -> S i) (hui : forall (i
) (x : S i), u (Set.inclusion (show S i subseteq T from hT'.symm ▸ Set.subset_iU
nion S i) x) = Set.inclusion (show S i subseteq T from hT'.symm ▸ Set.subset_iUn
ion S i) (ui i x)) (uβ : β -> β) (h : forall (i) (x : S i), f i (ui i x) = uβ (f
 i x)) (x : T) : iUnionLift S f hf T (le_of_eq hT') (u x) = uβ (iUnionLift S f h
f T (le_of_eq hT') x)
参数：u : T -> T；ui : forall i, S i -> S i；hui : forall (i) (x : S i), u (Set.inclu
sion (show S i subseteq T from hT'.symm ▸ Set.subset_iUnion S i) x) = Set.inclus
ion (show S i subseteq T from hT'.symm ▸ Set.subset_iUnion S i) (ui i x)；uβ : β 
-> β；h : forall (i) (x : S i), f i (ui i x) = uβ (f i x)；x : T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnionLift_of_mem`：iUnionLift_of_mem (x : T) {i : ι} (hx : (x : α) i
n S i) : iUnionLift S f hf T hT x = f i ⟨x, hx⟩
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iUnionLift_inclusion`：iUnionLift_inclusion {i : ι} (x : S i) (h : S 
i subseteq T) : iUnionLift S f hf T hT (Set.inclusion h x) = f i x

--- 原说明 ---
`iUnionLift_unary` is useful for proving that `iUnionLift` is a homomorphism
  of algebraic structures when defined on the Union of algebraic subobjects.
  For example, it could be used to prove that the lift of a collection
  of `LinearMap`s on a union of submodules preserves scalar multiplication.
-/
theorem iUnionLift_unary (u : T → T) (ui : ∀ i, S i → S i)
    (hui :
      ∀ (i) (x : S i),
        u (Set.inclusion (show S i ⊆ T from hT'.symm ▸ Set.subset_iUnion S i) x) =
          Set.inclusion (show S i ⊆ T from hT'.symm ▸ Set.subset_iUnion S i) (ui i x))
    (uβ : β → β) (h : ∀ (i) (x : S i), f i (ui i x) = uβ (f i x)) (x : T) :
    iUnionLift S f hf T (le_of_eq hT') (u x) = uβ (iUnionLift S f hf T (le_of_eq hT') x) := by
  subst hT'
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 x.prop
  rw [iUnionLift_of_mem x hi, ← h i]
  have : x = Set.inclusion (Set.subset_iUnion S i) ⟨x, hi⟩ := by
    cases x
    rfl
  conv_lhs => rw [this, hui, iUnionLift_inclusion]

/-- `iUnionLift_binary` is useful for proving that `iUnionLift` is a homomorphism
  of algebraic structures when defined on the Union of algebraic subobjects.
  For example, it could be used to prove that the lift of a collection
  of group homomorphisms on a union of subgroups preserves `*`. -/
/-
**Set.iUnionLift_binary** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnionLift_binary (dir : Directed (· <= ·) S) (op : T -> T -> T) (opi : fo
rall i, S i -> S i -> S i) (hopi : forall i x y, Set.inclusion (show S i subsete
q T from hT'.symm ▸ Set.subset_iUnion S i) (opi i x y) = op (Set.inclusion (show
 S i subseteq T from hT'.symm ▸ Set.subset_iUnion S i) x) (Set.inclusion (show S
 i subseteq T from hT'.symm ▸ Set.subset_iUnion S i) y)) (opβ : β -> β -> β) (h 
: forall (i) (x y : S i), f i (opi i x y) = opβ (f i x) (f i y)) (x y : T) : iUn
ionLift S f hf T (le_of_eq
参数：dir : Directed (· <= ·) S；op : T -> T -> T；opi : forall i, S i -> S i -> S i；
hopi : forall i x y, Set.inclusion (show S i subseteq T from hT'.symm ▸ Set.subs
et_iUnion S i) (opi i x y) = op (Set.inclusion (show S i subseteq T from hT'.sym
m ▸ Set.subset_iUnion S i) x) (Set.inclusion (show S i subseteq T from hT'.symm 
▸ Set.subset_iUnion S i) y)；opβ : β -> β -> β；h : forall (i) (x y : S i), f i (o
pi i x y) = opβ (f i x) (f i y)；x y : T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnionLift_of_mem`：iUnionLift_of_mem (x : T) {i : ι} (hx : (x : α) i
n S i) : iUnionLift S f hf T hT x = f i ⟨x, hx⟩
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c

--- 原说明 ---
`iUnionLift_binary` is useful for proving that `iUnionLift` is a homomorphism
  of algebraic structures when defined on the Union of algebraic subobjects.
  For example, it could be used to prove that the lift of a collection
  of group homomorphisms on a union of subgroups preserves `*`.
-/
theorem iUnionLift_binary (dir : Directed (· ≤ ·) S) (op : T → T → T) (opi : ∀ i, S i → S i → S i)
    (hopi :
      ∀ i x y,
        Set.inclusion (show S i ⊆ T from hT'.symm ▸ Set.subset_iUnion S i) (opi i x y) =
          op (Set.inclusion (show S i ⊆ T from hT'.symm ▸ Set.subset_iUnion S i) x)
            (Set.inclusion (show S i ⊆ T from hT'.symm ▸ Set.subset_iUnion S i) y))
    (opβ : β → β → β) (h : ∀ (i) (x y : S i), f i (opi i x y) = opβ (f i x) (f i y)) (x y : T) :
    iUnionLift S f hf T (le_of_eq hT') (op x y) =
      opβ (iUnionLift S f hf T (le_of_eq hT') x) (iUnionLift S f hf T (le_of_eq hT') y) := by
  subst hT'
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 x.prop
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 y.prop
  rcases dir i j with ⟨k, hik, hjk⟩
  rw [iUnionLift_of_mem x (hik hi), iUnionLift_of_mem y (hjk hj), ← h k]
  have hx : x = Set.inclusion (Set.subset_iUnion S k) ⟨x, hik hi⟩ := by
    cases x
    rfl
  have hy : y = Set.inclusion (Set.subset_iUnion S k) ⟨y, hjk hj⟩ := by
    cases y
    rfl
  have hxy : (Set.inclusion (Set.subset_iUnion S k) (opi k ⟨x, hik hi⟩ ⟨y, hjk hj⟩) : α) ∈ S k :=
    (opi k ⟨x, hik hi⟩ ⟨y, hjk hj⟩).prop
  conv_lhs => rw [hx, hy, ← hopi, iUnionLift_of_mem _ hxy]

end UnionLift

variable {S : ι → Set α} {f : ∀ i, S i → β}
  {hf : ∀ (i j) (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩}
  {hS : iUnion S = univ}

/-- Glue together functions defined on each of a collection `S` of sets that cover a type. See
also `Set.iUnionLift`. -/
/-
**Set.liftCover** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：liftCover (S : ι -> Set α) (f : forall i, S i -> β) (hf : forall (i j) (x 
: α) (hxi : x in S i) (hxj : x in S j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩) (hS : iUnio
n S = univ) (a : α) : β
参数：S : ι -> Set α；f : forall i, S i -> β；hf : forall (i j) (x : α) (hxi : x in S
 i) (hxj : x in S j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩；hS : iUnion S = univ；a : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True

--- 原说明 ---
Glue together functions defined on each of a collection `S` of sets that cover a
 type. See
also `Set.iUnionLift`.
-/
noncomputable def liftCover (S : ι → Set α) (f : ∀ i, S i → β)
    (hf : ∀ (i j) (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩)
    (hS : iUnion S = univ) (a : α) : β :=
  iUnionLift S f hf univ hS.symm.subset ⟨a, trivial⟩

@[simp]
/-
**Set.liftCover_coe** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：liftCover_coe {i : ι} (x : S i) : liftCover S f hf hS x = f i x
参数：x : S i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iUnionLift_mk`：iUnionLift_mk {i : ι} (x : S i) (hx : (x : α) in T) :
 iUnionLift S f hf T hT ⟨x, hx⟩ = f i x
· 使用定理 `trivial`：True
-/
theorem liftCover_coe {i : ι} (x : S i) : liftCover S f hf hS x = f i x :=
  iUnionLift_mk x _
/-
**Set.liftCover_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：liftCover_of_mem {i : ι} {x : α} (hx : (x : α) in S i) : liftCover S f hf 
hS x = f i ⟨x, hx⟩
参数：hx : (x : α) in S i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iUnionLift_of_mem`：iUnionLift_of_mem (x : T) {i : ι} (hx : (x : α) i
n S i) : iUnionLift S f hf T hT x = f i ⟨x, hx⟩
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem liftCover_of_mem {i : ι} {x : α} (hx : (x : α) ∈ S i) :
    liftCover S f hf hS x = f i ⟨x, hx⟩ :=
  iUnionLift_of_mem ⟨x, mem_univ x⟩ hx
/-
**Set.preimage_liftCover** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_liftCover (t : Set β) : liftCover S f hf hS ⁻¹' t = ⋃ i, (↑) '' f
 i ⁻¹' t
参数：t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用定理 `Set.preimage_iUnionLift`：preimage_iUnionLift (t : Set β) : iUnionLift S 
f hf T hT ⁻¹' t = inclusion hT ⁻¹' (⋃ i, inclusion (subset_iUnion S i) '' f i ⁻¹
' t)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem preimage_liftCover (t : Set β) : liftCover S f hf hS ⁻¹' t = ⋃ i, (↑) '' f i ⁻¹' t := by
  change (iUnionLift S f hf univ hS.symm.subset ∘ fun a => ⟨a, mem_univ a⟩) ⁻¹' t = _
  rw [preimage_comp, preimage_iUnionLift]
  ext; simp

end Set

